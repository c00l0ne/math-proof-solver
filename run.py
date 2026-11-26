"""One current library for solving; archived code is used only for old replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory,mkdtemp

from app import solve,solve_proofs,report
from library import Library
from search import Limits
from verify import verify
from tasks import COMPOSED_SCHEMAS


def requires_drawing(r):
    return r.get('status')=='SOLVED' and (r['schema']=='rational-graph-run/v1' or
        r['schema']=='planar-domain/v1' and 'drawing_of_domain' in r['task']['requested_output'] or
        r['schema']=='level-set-family/v1' and 'level_curve_drawing' in r['task']['requested_output'])


def save(result,out,stem,library):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    if not re.fullmatch(r'[A-Za-z_0-9-]+',stem):raise ValueError('Unsafe report name')
    if requires_drawing(result):
        (out/(stem+'.svg')).write_bytes(result['value']['drawing_svg'].encode('utf-8'))
    (out/(stem+'.json')).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    (out/(stem+'.txt')).write_text(report(result,library),encoding='utf-8')


def proofs(path,out,jobs=None,max_steps=None,shortest=False):
    task=json.loads(Path(path).read_text(encoding='utf-8-sig'))
    library=Library()
    limits=Limits(jobs=jobs,questions=None,term_nodes=None,depth=None)
    summary,results=solve_proofs(task,library,limits,max_steps,shortest)
    out=Path(out)
    out.mkdir(parents=True,exist_ok=True)
    # Publish the manifest only after every referenced certificate and explanation is ready.
    generation=Path(mkdtemp(prefix='proofs-',dir=out))
    summary['proofs']=[]
    for index,result in enumerate(results,1):
        stem=f'proof-{index:04d}'
        save(result,generation,stem,library)
        prefix=generation.name+'/'+stem
        summary['proofs'].append({'steps':len(result['proof']['nodes']),'json':prefix+'.json','explanation':prefix+'.txt'})
    message=f"Проверено доказательств: {len(results)}."
    if summary['complete']:message+=' Перебор всех допустимых ациклических доказательств завершён.'
    elif summary['complete_through_steps'] is not None:
        message+=f" Перебор завершён до {summary['complete_through_steps']} шагов включительно."
    if summary.get('reason'):message+=' '+summary['reason']
    if summary.get('stats',{}).get('cutoffs'):message+=' Поиск ограничен: '+', '.join(summary['stats']['cutoffs'])+'.'
    if results:
        minimum='Доказанный минимум' if summary['shortest_certified'] else 'Минимум среди найденных'
        message+=f" {minimum}: {summary['shortest_steps']}."
    summary['message']=message
    staging=generation/'inventory.tmp'
    staging.write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    staging.replace(out/'inventory.json')
    if not results:generation.rmdir()
    return summary


def batch(path,out,jobs=None,order=None):
    data=json.loads(Path(path).read_text(encoding='utf-8'))
    tasks=data['tasks'] if isinstance(data,dict) else data
    library=Library();rows=[]
    for index,task in enumerate(tasks,1):
        result=solve(task,library,Limits(jobs=jobs,questions=4000,term_nodes=4000,depth=48),order)
        stem=str(task.get('source_number',task.get('id',index)))
        if not re.fullmatch(r'[A-Za-z_0-9-]+',stem):stem=str(index)
        if any(row['file']==stem+'.json' for row in rows):stem=str(index)+'_'+stem
        save(result,out,stem,library)
        rows.append({'input_index':index,'source_number':task.get('source_number'),'task_id':task.get('id'),'file':stem+'.json',
                     'status':result['status'],'value':result.get('value'),
                     'verification':result.get('verification'),'seconds':result['elapsed_seconds']})
    complete={'SOLVED','SOLVED_CASES','DOMAIN_ERROR','DOES_NOT_EXIST','NO_FINITE_DERIVATIVE'}
    summary={'total':len(rows),'completed':sum(r['status'] in complete for r in rows),
             'role':'Runtime outputs, outside the knowledge library.','library_hash':library.hash,'cases':rows}
    Path(out).mkdir(parents=True,exist_ok=True)
    (Path(out)/'batch.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    return summary


def replay(path):
    artifact=json.loads(Path(path).read_text(encoding='utf-8'))
    if requires_drawing(artifact):
        if hashlib.sha256(Path(path).with_suffix('.svg').read_bytes()).hexdigest()!=artifact['value']['drawing_sha256']:
            raise ValueError('The stored drawing differs from the verified graph')
    archive=Path(__file__).parent/'archive'
    if artifact.get('schema') in ('unified-chain-search-run/v4','compiled-calculus-run/v1','global-chain-search-run/v1','point-derivative-chain-run/v1','integral-chain-run/v1','partial-derivative-bundle/v1','ordinary-kernel-derivatives/v1','original-table-derivative/v1','series-comparison-run/v1','euler-homogeneity-run/v1',*COMPOSED_SCHEMAS,'rational-graph-run/v1'):
        library=Library()
        if artifact.get('library_hash')==library.hash:return verify(artifact,library)
        revisions=json.loads((archive/'replay-revisions.json').read_text(encoding='utf-8'))
        pinned=revisions.get(artifact.get('library_hash'))
        if not pinned:raise ValueError('Unknown historical library revision')
        commit=pinned['commit']
        if not re.fullmatch('[0-9a-f]{40}',commit):raise ValueError('Invalid pinned commit')
        # Recover only the small, pinned mathematical runtime, never build scripts.
        with TemporaryDirectory(prefix='limit-replay-') as folder:
            root=Path(folder).resolve()
            for name,digest in pinned['files'].items():
                target=(root/name).resolve()
                if not target.is_relative_to(root):raise ValueError('Unsafe archive path')
                raw=subprocess.check_output(['git','show',commit+':'+name],cwd=Path(__file__).resolve().parents[2])
                if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Historical source changed: '+name)
                target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
            result=subprocess.run([sys.executable,'-B','-X','utf8',str(root/'semantic/chain-search/run.py'),
                                   'replay',str(Path(path).resolve())],capture_output=True,text=True,
                                  encoding='utf-8',timeout=60,check=True)
        return {**json.loads(result.stdout),'implementation':'pinned Git revision','commit':commit}
    if artifact.get('schema') not in {'chain-search-run/v0','general-chain-search-run/v2','extended-chain-search-run/v3'}:
        raise ValueError('Unknown proof format')
    inventory=json.loads((archive/'INVENTORY.json').read_text(encoding='utf-8'))
    code=archive/'2026-11-17-before-unification'
    for name,digest in inventory['files'].items():
        if hashlib.sha256((code/name).read_bytes()).hexdigest()!=digest:raise ValueError('Historical archive changed: '+name)
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(code/'run.py'),'replay',str(Path(path).resolve())],
                          capture_output=True,text=True,encoding='utf-8',timeout=60,check=True)
    return {**json.loads(result.stdout),'implementation':'verified historical archive'}


def differential_evidence(result):
    """Read mathematical conclusions and the specific derivative DAG replayed by these schemas."""
    import expressions as m
    from model import freeze
    if (result.get('compilation') or {}).get('method') in ('finite_harmonic_primitive','quadratic_radical_differential'):return
    schema=result.get('schema')
    if schema in COMPOSED_SCHEMAS:
        for child in result['children']:
            yield from differential_evidence(child['proof'])
        return
    if schema=='integral-chain-run/v1':
        head=(freeze(result['value']['representative']),freeze(result['compilation']['integrand_ast']))
        child=result['child_result']
    elif schema=='compiled-calculus-run/v1' and result['task']['kind']=='differentiate':
        task=result['task']
        params=[p if isinstance(p,str) else p['symbol'] for p in task.get('parameters',())]
        head=m.parse(task['function'],task['variable'],params),freeze(result['value'])
        child=result
    else:return
    facts=[head]
    if child.get('schema')=='compiled-calculus-run/v1':
        table=child['child_result']
        if table['schema']=='original-table-derivative/v1':
            facts.extend((freeze(n['goal'][1]),freeze(n['value'])) for n in table['proof']['nodes'] if n['goal'][0]=='derivative')
    yield result['task']['variable'],facts


def check_differential(template,library):
    """Prove H'(u)=K(u) with every scalar slot an independent real parameter."""
    from integrals import learned_nodes
    from model import freeze,instantiate
    from polynomial import ResourceBound
    from tasks import source,domain_conditions,guard_source
    from verify import same_value
    kernel,primitive=(freeze(template[k]) for k in ('kernel','primitive'))
    params=sorted({slot[1:] for slot in learned_nodes(kernel) if isinstance(slot,str) and slot.startswith('?c')})
    env={'?u':('v','u'),**{'?'+name:('s',name) for name in params}}
    H,K=instantiate(primitive,env),instantiate(kernel,env)
    guards=list(dict.fromkeys(domain_conditions(H,True)+domain_conditions(K)))
    task=dict(kind='differentiate',variable='u',parameters=params,function=source(H),method_requirement='table_and_rules')
    proof=solve(task,library)
    result=dict(status='unproved',smooth_domain=[guard_source(g) for g in guards])
    if proof.get('status') in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'):
        checked=verify(proof,library,task)
        try:equal=same_value(proof['value'],K)
        except (ResourceBound,ArithmeticError):return result
        result.update(status='passed' if equal else 'different_derivative',checked_nodes=checked['checked_nodes'])
    return result


def learn_differentials(verified_sources,library=None,checks=None):
    """Abstract a common coordinate, then common scalar slots in repeated checked differential pairs."""
    from collections import defaultdict
    import expressions as m
    from model import ONE,ZERO,canonical,digest,match
    from polynomial import ResourceBound
    def walk(e):
        yield e
        for c in e[1:]:
            if isinstance(c,tuple):yield from walk(c)
    def map_leaves(e,visit):
        if not isinstance(e,tuple):return e
        if e[0] in ('q','s','v','argument'):return visit(e)
        return (e[0],*(map_leaves(c,visit) for c in e[1:]))
    def named(pair):
        params={}
        def rename(e):
            if e[0]=='v':return ('v','x')
            if e[0]=='s':return ('s',params.setdefault(e,len(params)))
            return e
        return tuple(map_leaves(expr,rename) for expr in pair)
    argument=('argument',);observations=defaultdict(lambda:defaultdict(set))
    contexts=defaultdict(set)
    for label,artifact in verified_sources:
        for variable,facts in differential_evidence(artifact):
            # Repeated paths, renamings and duplicate copies of one mathematical source give one vote.
            origin=digest(named(facts[0]))
            derivatives={('v',variable):ONE}
            for f,d in facts:
                if not m.variable_in(f,variable) or max(m.tree_size(f),m.tree_size(d))>96:continue
                try:derivatives[m.simplify(f)]=m.simplify(d)
                except (ResourceBound,ArithmeticError):continue
            for f,d in derivatives.items():
                if d==ZERO:continue
                for u in set(walk(f))&derivatives.keys():
                    if f==u or derivatives[u]==ZERO:continue
                    h=m.substitute(f,{u:argument})
                    if m.variable_in(h) or m.tree_size(h)>23:continue
                    try:k=m.substitute(m.div(d,derivatives[u]),{u:argument})
                    except (ResourceBound,ArithmeticError):continue
                    if m.variable_in(k) or not m.contains(k,argument) or m.tree_size(k)>35:continue
                    if h[0]=='add' and h[2][0]=='q':h=h[1]
                    if h[0]=='mul' and h[1][0]=='q':
                        # Normalize scalar multiples without passing the template marker to the simplifier.
                        try:k=m.substitute(m.div(m.div(d,derivatives[u]),h[1]),{u:argument})
                        except (ResourceBound,ArithmeticError):continue
                        if m.variable_in(k) or not m.contains(k,argument):continue
                        h=h[2]
                    if h==argument:continue
                    pair=named((k,h))
                    observations[pair][origin].add(label)
                    contexts[pair].add(digest(named((m.substitute(h,{argument:u}),u))))
    groups=defaultdict(list)
    def shape(e):
        if e==argument:return '?u'
        if e[0]=='s' or e[0]=='q' and e not in (ZERO,ONE,m.q(-1)):return '#'
        return e
    for pair in sorted(observations,key=canonical):
        signature=tuple(map_leaves(e,shape) for e in pair)
        groups[signature].append(pair)
    discovered={};support=defaultdict(set)
    def induce(examples):
        votes=set().union(*(observations[e] for e in examples))
        if len(votes)<2 or len(set().union(*(contexts[e] for e in examples)))<2:return
        slots={}
        def term(column):
            a=column[0]
            if a==argument:return '?u'
            if not isinstance(a,tuple):return a
            if a[0]=='s' or a[0]=='q' and any(z!=a for z in column):
                return slots.setdefault(tuple(column),'?c'+str(len(slots)))
            return (a[0],*(term(col) for col in zip(*(z[1:] for z in column))))
        k=term([e[0] for e in examples]);bound=len(slots)
        h=term([e[1] for e in examples])
        if len(slots)!=bound:return
        item={'kernel':k,'primitive':h};key=digest(item)
        discovered[key]=item
        for e in examples:
            for labels in observations[e].values():support[key].update(labels)
    for examples in groups.values():
        for pair in examples:induce([pair])
        if len(examples)>1:induce(examples)
    library=library or Library()
    confirmed={}
    for key,item in sorted(discovered.items()):
        evidence=check_differential(item,library)
        if checks is not None:checks[key]=evidence
        if evidence['status']=='passed':confirmed[key]=item
    keys=[]
    for key,item in confirmed.items():
        # Retain the parameterized template when it accounts for a more specific one.
        def subsumes(other):
            env={'?u':'?u'}
            if not match((other['kernel'],other['primitive']),(item['kernel'],item['primitive']),env):return False
            constants=[v for k,v in env.items() if k!='?u']
            return (all(isinstance(v,str) and v.startswith('?c') or isinstance(v,tuple) and v[0]=='q' for v in constants)
                    and any(isinstance(v,tuple) for v in constants))
        if not any(subsumes(other) for other in confirmed.values()):keys.append(key)
    return [discovered[k] for k in keys],{k:sorted(support[k]) for k in keys}


def learn_methods(verified_sources,library=None):
    from integrals import induce_parts_roles
    sources=list(verified_sources)
    checks={}
    differentials,first=learn_differentials(sources,library,checks)
    roles,second=induce_parts_roles(sources)
    return {'learned_differentials':differentials,'learned_parts_roles':roles},{'differentials':first,'parts_roles':second,'symbolic_checks':checks}


def proof_plan(library,*,sequence=None,proof=None):
    """Generalize a verified DAG or parse a preorder list of rule names. Keep no instance terms."""
    from library import ProofPlan
    table=[];positions={}
    def add(rid,children):
        key=(rid,tuple(children))
        if key not in positions:
            positions[key]=len(table)
            table.append([rid,library.revisions[rid],children])
        return positions[key]
    if sequence is not None:
        if not isinstance(sequence,list):raise ValueError('A rule sequence must be a list')
        ready=[]
        for rid in reversed(sequence):
            if not isinstance(rid,str) or rid not in library.by_id:raise ValueError('Unknown rule in sequence')
            count=sum('ask' in s for s in library.by_id[rid]['steps'])
            if count>len(ready):raise ValueError('Missing premise in rule sequence')
            ready.append(add(rid,[ready.pop() for _ in range(count)]))
        if len(ready)!=1:raise ValueError('Rule sequence must describe one complete derivation')
    else:
        nodes={n['id']:n for n in proof['nodes']};indices={};active=set();stack=[(proof['root'],False)]
        while stack:
            key,finishing=stack.pop()
            if key in indices:continue
            node=nodes[key];rid=node['rule']
            if library.revisions.get(rid)!=node['revision']:return None
            children=[s['proof'] for s in node['steps'] if 'ask' in s]
            if finishing:
                active.remove(key)
                indices[key]=add(rid,[indices[k] for k in children])
            else:
                if key in active:raise ValueError('Circular source proof')
                active.add(key)
                stack.append((key,True));stack.extend((k,False) for k in children)
    if len(table)<2:return None
    ProofPlan(library,table)
    return table


def check_proof_plans(library,sources,sequences,transfers):
    """Approve a tactic only after it produces an ordinary verified proof on another compiled goal."""
    from model import digest,Unsupported
    from tasks import compile_global_task
    from app import solve_global
    candidates={};learned_on={};supported={}
    for label,artifact in sources:
        if artifact.get('schema')!='global-chain-search-run/v1':continue
        plan=proof_plan(library,proof=artifact['proof'])
        if plan:
            key=digest(plan);candidates[key]=plan
            learned_on.setdefault(key,{})[label]=digest(artifact['goal'])
    for sequence in sequences:
        plan=proof_plan(library,sequence=sequence)
        if plan:candidates[digest(plan)]=plan
    approved={}
    for key,plan in candidates.items():
        # Use the same publication payload and the same first-proof entry as an ordinary task.
        trial=Library({**library.data,'learned_proof_plans':[plan]})
        for task in transfers:
            try:query=compile_global_task(task,trial)['goal']
            except Unsupported:continue
            if query[0] not in trial.proof_plans:continue
            goal=digest(query)
            if goal in learned_on.get(key,{}).values():continue
            result=solve_global(task,trial,Limits(),plan_trial=True)
            if result.get('applied_proof_plan')==key and result.get('verification',{}).get('status')=='passed':
                supported.setdefault(key,{})[goal]=result['verification']['checked_nodes']
        # A handwritten list has no checked source application. Require two distinct successful goals.
        if len(supported.get(key,{})) >= (1 if key in learned_on else 2):approved[key]=plan
    return approved,{'candidates':candidates,'verified_sources':learned_on,'verified_transfers':supported}


def attach_proof_plans(patch,approved,library):
    from model import digest
    if not approved:return
    previous={digest(plan):plan for plan in library.data.get('learned_proof_plans',[])}
    patch['package_metadata']['learned_proof_plans']=list((previous|approved).values())
    ns=json.loads(Path(__file__).with_name('current.json').read_text(encoding='utf8'))['namespace']+':'
    for key,plan in approved.items():
        if key in previous:continue
        node='method.proof_plan.'+key;root=library.by_id[plan[-1][0]]
        record=dict(id=node,kind='mathematical_argument',title='Составной приём: '+root['label'],
            statement='Построение доказательства цели '+root['head'][0]+' по сохранённой схеме применения правил.',
            argument='В каждой позиции исходное правило заново связывает переменные на новой цели. Проверка раскрытого доказательства воспроизводит все исходные вычисления и предпосылки.',
            conditions=['Допустимы исходные правила в данном контексте. Каждое сопоставление, каждая операция и каждая запрошенная посылка должны завершиться с требуемым результатом.'],
            subjects=['ford:FORD101'],proof_plan_digest=key,assessment=dict(author='Обобщение цепочки правил',formal_verification=False,
                review='Схема проверена на перенос. Условия каждого конкретного применения обязан доказать исполнитель.'))
        patch.setdefault('records',[]).append(record)
        for source,target,role in [('runtime.package',node,'uses_learned_pattern'),
                *((node,'rule.'+rid,'uses_existing_rule') for rid in dict.fromkeys(r[0] for r in plan))]:
            patch.setdefault('links',[]).append(dict(source=ns+source,target=ns+target,role=role,metadata={}))


def learn(path,out):
    from model import digest
    path=Path(path);inputs=json.loads(path.read_text(encoding='utf8'))
    options=inputs if isinstance(inputs,dict) else {'proofs':inputs}
    files=options.get('proofs',[]);sequences=options.get('rule_sequences',[]);transfers=options.get('transfer_tasks',[])
    if not all(isinstance(x,list) for x in (files,sequences,transfers)) or not (files or sequences):
        raise ValueError('Supply verified proof paths or a list of complete rule sequences')
    sources={}
    def checked():
        for name in files:
            file=path.parent/name;raw=file.read_bytes();key=hashlib.sha256(raw).hexdigest()
            if key in sources:continue
            result=json.loads(raw)
            if result.get('status') not in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'):raise ValueError('Only complete source proofs can be mined')
            if replay(file)['status']!='passed' or file.read_bytes()!=raw:raise ValueError('Unverified or changed proof input')
            sources[key]=str(file.resolve())
            yield key,result
    library=Library();artifacts=list(checked())
    methods,support=learn_methods(artifacts,library)
    approved,details=check_proof_plans(library,artifacts,sequences,transfers)
    if details['candidates']:support['proof_plans']=details
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    patch={'title':'Общие методы, извлечённые из проверенных доказательств','package_metadata':methods}
    attach_proof_plans(patch,approved,library)
    provenance={'verified_proofs':sources,'support_by_method_hash':support,'patch_digest':digest(patch)}
    for name,obj in [('skill-patch',patch),('provenance',provenance)]:
        (out/(name+'.json')).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
    return {'verified_proofs':len(sources),**{name:len(items) for name,items in methods.items()}}


def main():
    parser=argparse.ArgumentParser(description='Единая рабочая библиотека общих навыков')
    sub=parser.add_subparsers(dest='command',required=True)
    s=sub.add_parser('solve');s.add_argument('expression');s.add_argument('--out',required=True)
    s.add_argument('--variable',default='x')
    position=s.add_mutually_exclusive_group()
    position.add_argument('--point',default='0');position.add_argument('--magnitude-infinity',action='store_true')
    s.add_argument('--side',choices=('right','left','both'))
    germ=s.add_mutually_exclusive_group()
    germ.add_argument('--expansion-degree',type=int,help='return finite power coefficients with a Peano remainder')
    germ.add_argument('--leading-term',action='store_true',help='return the first nonzero asymptotic monomial')
    s.add_argument('--parameters',nargs='*',default=[]);s.add_argument('--assume',action='append',default=[])
    s.add_argument('--variable-domain',choices=('real','positive_integers'),default='real')
    s.add_argument('--jobs',type=int);s.add_argument('--order',type=int)
    s.add_argument('--method',help='Required scalar-limit method, e.g. taylor_expansion')
    b=sub.add_parser('batch');b.add_argument('inputs');b.add_argument('--out',required=True)
    b.add_argument('--jobs',type=int);b.add_argument('--order',type=int)
    p=sub.add_parser('proofs',help='перебрать доказательства одной глобальной цели и сравнить их по длине')
    p.add_argument('input');p.add_argument('--out',required=True)
    p.add_argument('--max-steps',type=int,help='рассмотреть доказательства до указанной длины включительно')
    p.add_argument('--shortest',action='store_true',help='перебирать по длине до первого полностью проверенного слоя с решениями')
    p.add_argument('--jobs',type=int,help='ограничить суммарное число действий поиска')
    eq=sub.add_parser('equality',help='доказать равенство на заявленной действительной области')
    eq.add_argument('left');eq.add_argument('right');eq.add_argument('--out',required=True)
    eq.add_argument('--variable',default='x');eq.add_argument('--parameters',nargs='*',default=[])
    eq.add_argument('--assume',action='append',default=[]);eq.add_argument('--punctured-at')
    mode=eq.add_mutually_exclusive_group()
    mode.add_argument('--jobs',type=int);mode.add_argument('--exhaustive',action='store_true',
        help='перебирать разрешённые ходы без предела числа вопросов, размера формул и глубины очереди')
    d=sub.add_parser('differentiate');d.add_argument('function');d.add_argument('--out',required=True)
    d.add_argument('--variable',default='x');d.add_argument('--point');d.add_argument('--parameters',nargs='*',default=[])
    d.add_argument('--assume',action='append',default=[]);d.add_argument('--from-definition',action='store_true')
    d.add_argument('--jobs',type=int);d.add_argument('--order',type=int)
    v=sub.add_parser('replay');v.add_argument('file')
    l=sub.add_parser('learn');l.add_argument('proofs');l.add_argument('--out',required=True)
    args=parser.parse_args()
    if args.command=='replay':print(json.dumps(replay(args.file),ensure_ascii=False))
    elif args.command=='learn':print(json.dumps(learn(args.proofs,args.out),ensure_ascii=False))
    elif args.command=='proofs':
        if any(n is not None and n<0 for n in (args.jobs,args.max_steps)):
            parser.error('Ограничения поиска должны быть неотрицательными')
        summary=proofs(args.input,args.out,args.jobs,args.max_steps,args.shortest)
        print(summary['message'])
        if summary['status']=='UNSUPPORTED':raise SystemExit(1)
    elif args.command=='equality':
        task=dict(kind='prove_equality',variable=args.variable,left=args.left,right=args.right,
                  parameters=args.parameters,assumptions=args.assume)
        if args.punctured_at is not None:task['punctured_at']=args.punctured_at
        limits=Limits.exhaustive() if args.exhaustive else Limits(jobs=args.jobs,questions=4000,term_nodes=4000,depth=48)
        lib=Library();result=solve(task,lib,limits)
        save(result,args.out,'run',lib);print(report(result,lib))
        if result['status']!='SOLVED':raise SystemExit(1)
    elif args.command=='batch':
        result=batch(args.inputs,args.out,args.jobs,args.order)
        print(json.dumps({'completed':result['completed'],'total':result['total'],'output':str(Path(args.out).resolve())},ensure_ascii=False))
        if result['completed']!=result['total']:raise SystemExit(1)
    elif args.command=='differentiate':
        task={'kind':'differentiate' if args.point is None else 'derivative_at','function':args.function,
              'variable':args.variable,'parameters':args.parameters,'stated_conditions':args.assume}
        if args.point is not None:task['point']=args.point
        if args.from_definition:task['method_requirement']='from_definition'
        lib=Library();result=solve(task,lib,Limits(jobs=args.jobs,questions=4000,term_nodes=4000,depth=48),order=args.order)
        save(result,args.out,'run',lib);print(report(result,lib))
    else:
        side=args.side or ('both' if args.expansion_degree is not None or args.leading_term else 'right')
        task={'expression':args.expression,'variable':args.variable,'approach':{'point':args.point,'side':side},
              'parameters':args.parameters,'variable_domain':args.variable_domain,'parameter_conditions':args.assume}
        if args.magnitude_infinity:task['approach']={'point':'infinity','side':args.side or 'both','mode':'magnitude_infinity'}
        if args.expansion_degree is not None:task.update(kind='finite_expansion',degree=args.expansion_degree)
        if args.leading_term:task['kind']='leading_asymptotic_term'
        if args.method is not None:task['method_requirement']=args.method
        lib=Library();result=solve(task,lib,Limits(jobs=args.jobs,questions=4000,term_nodes=4000,depth=48),order=args.order)
        save(result,args.out,'run',lib);print(report(result,lib))


if __name__=='__main__':main()
