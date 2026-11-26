"""Load executable general methods. The data contains no input exercise set."""
from pathlib import Path
import json
import sqlite3
import intervals as real_intervals

from model import Unsupported, freeze, digest, match, instantiate, rational
import expressions as m
from operations import GERM_GOALS,WINDOW_SIDES,closed_function_interval,compute,expression_positions,unpack,version


def pattern_variables(term):
    if isinstance(term,str) and term.startswith('?'):return {term}
    if isinstance(term,(list,tuple)):return set().union(*(pattern_variables(x) for x in term))
    return set()


class Library:
    def __init__(self,data=None):
        manifest=json.loads((Path(__file__).parent/'current.json').read_text(encoding='utf-8'))
        self.origin={'kind':'explicit_data'}
        if data is None:
            source=(Path(__file__).parent/manifest['module']).resolve()
            packet=json.loads(source.read_text(encoding='utf-8'))
            records={r['id']:r for r in packet['records']}
            package=records['runtime.package']
            data={**package['package_metadata'],'rules':[records['rule.'+rid]['executable_rule'] for rid in package['rule_ids']]}
            if digest(data)!=manifest['library_hash']:raise ValueError('Изменился закреплённый рабочий набор правил')
            self.origin={'kind':'module_file','path':str(source)}
            atlas_data,origin=read_atlas_package(data,manifest['snapshot_key'])
            if atlas_data is not None:data,self.origin=atlas_data,origin
        self.data=data;self.rules=data['rules'];self.hash=digest(data)
        if self.data.get('operation_hash')!=version():raise ValueError('Вычислительная основа не совпадает с рабочим снимком')
        self.by_id={r['id']:r for r in self.rules}
        if len(self.by_id)!=len(self.rules):raise ValueError('Повтор идентификатора правила')
        self.revisions={r['id']:r['id']+'@sha256:'+digest(r) for r in self.rules}
        self.index={}
        for r in self.rules:
            if not all(k in r for k in ('id','label','head','steps','result','basis')):raise ValueError('Неполное правило')
            bound=pattern_variables(r['head'])
            for step in r['steps']:
                missing=pattern_variables(step.get('ask',step.get('args',[])))-bound
                if missing:
                    raise ValueError(f"Правилу {r['id']} нужен источник кандидатов для {', '.join(sorted(missing))}")
                bound.update(pattern_variables(step.get('bind')))
            if pattern_variables(r['result'])-bound:raise ValueError('Несвязанный результат правила '+r['id'])
            self.index.setdefault(r['head'][0],[]).append(r)
        self.proof_plans={}
        for plan in data.get('learned_proof_plans',[]):
            view=ProofPlan(self,plan)
            self.proof_plans.setdefault(view.root_predicate,[]).append(view)
        self.inverse_fragments={}
        for rule in self.index.get('real_identity_step',()):
            pattern,result=freeze(rule['head'][1]),freeze(rule['result'])
            variables,kept=pattern_variables(pattern),pattern_variables(result)
            if not kept<variables or not isinstance(pattern,tuple):continue
            for path,fragment in expression_positions(pattern):
                if path and variables<=kept|pattern_variables(fragment):
                    self.inverse_fragments.setdefault(fragment[0],[]).append((rule['id'],pattern,result,fragment))

    def rule_allowed(self,rid,ctx):
        domains=self.data.get('rule_context_scopes',{}).get(rid)
        if domains is not None and ctx.get('domain') not in domains:return False
        scope=self.data.get('context_rule_scopes',{}).get(ctx.get('domain'))
        return ctx.get('domain')!='pointwise_real' if scope is None else rid in scope

    def candidates(self, goal, ctx=None):
        for r in self.index.get(goal[0], []):
            if ctx is not None and not self.rule_allowed(r['id'],ctx):continue
            env = {}
            if match(r["head"], goal, env):
                yield r,env

    def compute(self,name,args,ctx):
        if name!='opposite_identity_instances':return compute(name,args,ctx)
        # Match a proper fragment of the law to the opposite side of the goal.
        # This proposes an expansion. The rule must prove it in the forward direction.
        start,target=freeze(args)
        fragments=self.inverse_fragments.get(target[0])
        if not fragments:return []
        positions=list(expression_positions(start))
        if any(actual==target for _,actual in positions):return []
        answers={}
        for rid,pattern,result,fragment in fragments:
            env={}
            if not self.rule_allowed(rid,ctx) or not match(fragment,target,env):continue
            for path,actual in positions:
                bindings=env.copy()
                if match(result,actual,bindings):
                    expanded=instantiate(pattern,bindings)
                    if expanded!=actual:answers[path,actual,expanded]=None
        return list(answers)

    def limit_context(self,task,assumptions,side,order):
        ctx=m.context(task,assumptions)
        ctx.update(order=order,evaluation_side=side)
        kind=task.get('kind',task.get('task_type'))
        if kind in GERM_GOALS:
            if ctx['variable_domain']!='real' or ctx['point'] not in ('+inf','-inf') and not m.constant_defined(freeze(ctx['point']),ctx):
                raise Unsupported('The germ needs a real approach and a defined center')
        if kind=='finite_expansion':
            degree=task.get('degree')
            if self.data.get('task_compilers',{}).get('finite_expansion')!='finite_peano_coefficients':
                raise Unsupported('Finite power expansions are not admitted')
            if type(degree) is not int or not 0<=degree<=24:
                raise Unsupported('The expansion degree must be an integer in 0..24')
            if task.get('requested_output',['finite_power_expansion'])!=['finite_power_expansion'] or task.get('remainder','peano')!='peano':
                raise Unsupported('Only the finite power coefficients with a Peano remainder are admitted')
            ctx['expansion_degree']=degree
        elif kind=='leading_asymptotic_term':
            if self.data.get('task_compilers',{}).get(kind)!='first_nonzero_germ_monomial':
                raise Unsupported('Leading terms are not admitted')
            if task.get('requested_output',['first_nonzero_asymptotic_monomial'])!=['first_nonzero_asymptotic_monomial'] or 'degree' in task or 'remainder' in task:
                raise Unsupported('Unsupported leading-term output or remainder')
            ctx['leading_asymptotic_term']=True
        method=None
        if 'method_requirement' in task:
            name=task['method_requirement']
            method=self.data.get('scalar_limit_methods',{}).get(name) if isinstance(name,str) else None
            if method is None:raise Unsupported('Unknown required scalar-limit method: '+str(name))
            if kind in GERM_GOALS:method={**method,'root_rule':None}
            ctx['limit_method_requirement']=name
        return ctx,method

    def validate(self,goal,ctx,output=None,check_output=False):
        spec=self.data['predicates'].get(goal[0])
        if not spec or len(goal)-1!=len(spec['inputs']):raise Unsupported('Неподдерживаемый вопрос')
        for kind,val in zip(spec['inputs'],goal[1:]):self.validate_value(kind,freeze(val),ctx)
        if check_output:self.validate_value(spec['output'],freeze(output),ctx)

    def validate_value(self,kind,val,ctx):
        if kind in ('power_weight','exponent_threshold'):
            if ctx.get('domain')!='integer_series' or not isinstance(val,tuple):raise Unsupported('Unbound power-series criterion')
            if kind=='power_weight':
                if len(val)!=6 or type(val[1]) is not int or val[1] not in (0,1):raise Unsupported('Invalid progression or phase')
                for term in (val[0],*val[2:5]):rational(term)
                self.validate_value('scalar',val[5],ctx)
            else:
                if len(val)!=2 or val[1] not in (m.ZERO,m.ONE,'all'):raise Unsupported('Invalid threshold')
                self.validate_value('scalar',val[0],ctx)
            return
        if kind in ('rational_sequence_order','parameter_convergence_sets'):
            if ctx.get('domain')!='integer_series':raise Unsupported('An integer-indexed series is required')
            if kind=='rational_sequence_order':
                if type(val) is not int:raise Unsupported('Expected an integral asymptotic exponent')
            elif not isinstance(val,dict) or not {'source_domain','absolute_convergence_set','conditional_convergence_set'}<=val.keys():
                raise Unsupported('Expected both parameter sets on the original domain')
            return
        if kind in ('sequence_bound','series_classification'):
            if ctx.get('domain')!='integer_series':raise Unsupported('A bound needs its original integer index')
            if kind=='series_classification':
                if isinstance(val,dict) and val.get('classification')=='by_parameter':
                    if val.get('criterion')!='power_progression_thresholds' or not all(isinstance(val.get(k),str) for k in ('absolute_convergence','conditional_convergence','divergence')):raise Unsupported('Incomplete parameter classification')
                    return
                if not isinstance(val,dict) or val.get('classification') not in ('convergent','divergent'):raise Unsupported('Missing series classification')
                return
            if not isinstance(val,(tuple,list)) or len(val)!=4:raise Unsupported('Expected a bound C n^d r^n from index N')
            c,d,r,first=val
            if type(d) is not int or type(first) is not int or first<ctx['sum_start']:raise Unsupported('Invalid degree or starting index')
            self.validate_value('scalar',c,ctx)
            self.validate_value('scalar',r,ctx)
            return
        if kind=='comparison_interval':
            if ctx.get('domain')!='ordered_interval' or val!=freeze(ctx.get('comparison_interval')):raise Unsupported('Unbound original comparison interval')
            return
        if kind=='upward_relation':
            if val not in ('>','>='):raise Unsupported('Expected a positive or nonnegative comparison')
            return
        if kind in ('cartesian_side','cartesian_polynomials'):
            if ctx.get('domain')!='cartesian_field_identity':raise Unsupported('Требуются декартовы поля')
            if kind=='cartesian_side':
                if val not in ('left','right'):raise Unsupported('Неизвестная сторона тождества')
            else:
                from cartesian_fields import valid_form
                if not valid_form(val,ctx):raise Unsupported('Неверное представление компонент поля')
            return
        if kind=='window_side':
            if val not in ('prefix','suffix'):raise Unsupported('Не определена движущаяся граница отрезка')
            return
        if kind=='real_relation':
            if val not in real_intervals.RELATIONS:raise Unsupported('Неизвестное действительное отношение')
            return
        if kind in ('real_partition','real_set'):
            if ctx.get('domain')!='global_real_line':raise Unsupported('Не установлена глобальная действительная область')
            try:
                if kind=='real_partition':real_intervals.validate_partition(val,ctx['variable'])
                else:real_intervals.validate_real_set(val)
            except real_intervals.Unsupported as exc:raise Unsupported(str(exc)) from exc
            return
        if kind=='truth':
            if val is not True:raise Unsupported('Нужно установленное свойство')
            return
        if kind in ('expr_list','real_function_list'):
            if not isinstance(val,tuple):raise Unsupported('Ожидался список выражений')
            for e in val:self.validate_value('real_function' if kind=='real_function_list' else 'expr',e,ctx)
            return
        if kind=='jet':
            terms,r=unpack(val)
            if len(terms)>64:raise Unsupported('Слишком большое разложение')
            for p,c in terms.items():self.validate_value('scalar',c,ctx)
            return
        if kind=='limit_value' and val in ('+inf','-inf'):return
        if not isinstance(val,tuple) or not val:raise Unsupported('Ожидалось выражение')
        op=val[0]
        if kind=='real_function':
            if ctx.get('domain')!='function_continuity' or ctx.get('source_domain') not in ('arbitrary_real_subset','closed_real_interval','closed_real_ray'):
                raise Unsupported('Ожидалась общая действительная область функций')
            if op in WINDOW_SIDES:
                if len(val)!=2 or not closed_function_interval(ctx):raise Unsupported('Для экстремума нужен исходный замкнутый отрезок')
                self.validate_value(kind,val[1],ctx)
                return
            if op=='q':rational(val);return
            if op=='function' and len(val)==2 and val[1] in ctx['functions']:return
            if op in ('function','v','s'):raise Unsupported('Необъявленная функция')
            if op in ('min','max') and len(val)==3:
                for arg in val[1:]:self.validate_value(kind,arg,ctx)
                return
        if op=='q':
            if len(val)!=3 or m.num(val) is None or val[2]<=0:raise Unsupported('Неверная рациональная константа')
        elif op=='pi':
            if len(val)!=1:raise Unsupported('Неверная константа pi')
        elif op=='s':
            if len(val)!=2 or val[1] not in ctx['parameters']:raise Unsupported('Необъявленный параметр')
        elif op=='v':
            if kind in ('scalar','limit_value') or len(val)!=2 or val[1]!=ctx['variable']:raise Unsupported('Неверная переменная или зависимость результата')
        elif op in ('add','mul','div','rpow'):
            if len(val)!=3:raise Unsupported('Неверная арность')
            for c in val[1:]:self.validate_value(kind,c,ctx)
        elif op=='pow':
            if len(val)!=3 or type(val[2]) is not int or abs(val[2])>256:raise Unsupported('Неверная степень')
            self.validate_value(kind,val[1],ctx)
        elif op in m.FUNCTIONS:
            if len(val)!=2:raise Unsupported('Неверная арность функции')
            self.validate_value(kind,val[1],ctx)
        else:raise Unsupported('Неподдерживаемая операция')


class ProofPlan:
    """A view of the ordinary rules for one proof skeleton. Each position has a local name."""
    def __init__(self,library,plan):
        if not isinstance(plan,list) or len(plan)<2:raise ValueError('A composed plan needs at least two rule positions')
        self.library,self.compute=library,library.compute
        self.by_id,self.revisions,self.original={}, {}, {}
        predicates={};used=set()
        for i,row in enumerate(plan):
            if not isinstance(row,(list,tuple)) or len(row)!=3:raise ValueError('Invalid proof plan position')
            rid,revision,children=row
            if not isinstance(rid,str) or rid not in library.by_id or revision!=library.revisions[rid]:
                raise ValueError('Unknown or changed rule in proof plan')
            rule=library.by_id[rid];steps=[];asks=[s['ask'] for s in rule['steps'] if 'ask' in s]
            if not isinstance(children,(list,tuple)) or len(children)!=len(asks):raise ValueError('All premises must be preserved')
            for premise,j in zip(asks,children):
                if type(j) is not int or not 0<=j<i or self.original[str(j)]['head'][0]!=premise[0]:
                    raise ValueError('Incompatible or circular proof plan premise')
            refs=iter(children)
            for s in rule['steps']:
                steps.append({**s,'ask':[str(next(refs)),*s['ask'][1:]]} if 'ask' in s else s)
            name=str(i)
            self.original[name]=rule
            self.by_id[name]={**rule,'id':name,'head':[name,*rule['head'][1:]],'steps':steps}
            self.revisions[name]=revision
            predicates[name]=library.data['predicates'][rule['head'][0]]
            used.update(children)
        if used!=set(range(len(plan)-1)):raise ValueError('Disconnected position in proof plan')
        self.data={'predicates':predicates}
        self.root=str(len(plan)-1);self.root_predicate=self.original[self.root]['head'][0]
        self.key=digest(plan)

    def candidates(self,goal,ctx):
        name=goal[0];rule=self.by_id[name];env={}
        if self.library.rule_allowed(self.original[name]['id'],ctx) and match(rule['head'],goal,env):
            yield rule,env

    def real_goal(self,goal):
        return (self.original[goal[0]]['head'][0],*goal[1:])

    def validate(self,goal,ctx,output=None,check_output=False):
        self.library.validate(self.real_goal(goal),ctx,output,check_output)

    def restore(self,proof):
        nodes=[]
        for node in proof['nodes']:
            steps=[{**s,'ask':self.real_goal(s['ask'])} if 'ask' in s else s for s in node['steps']]
            nodes.append({**node,'rule':self.original[node['rule']]['id'],'goal':self.real_goal(node['goal']),'steps':steps})
        return {**proof,'nodes':nodes}

    def describes(self,proof):
        """Bind the claimed tactic to the already replayed original proof, allowing shared nodes."""
        nodes={n['id']:n for n in proof['nodes']}
        todo=[(self.root,proof['root'])];seen=set()
        while todo:
            place,key=todo.pop()
            if (place,key) in seen:continue
            seen.add((place,key));node=nodes[key]
            if node['rule']!=self.original[place]['id']:return False
            for step,actual in zip(self.by_id[place]['steps'],node['steps']):
                if 'ask' in step:todo.append((step['ask'][0],actual['proof']))
        return True


def read_atlas_package(expected,snapshot_key,database=None):
    """Use declared executable contracts from the sealed common-library snapshot.

    The module is the single offline source. The current manifest pins one active
    snapshot. Mere prose records never become executable rules.
    """
    database=Path(database or Path(__file__).parent.parent/'science-atlas/data/atlas.sqlite').resolve()
    if not database.exists():return None,None
    with sqlite3.connect(database.as_uri()+'?mode=ro',uri=True) as con:
        con.execute('PRAGMA query_only=ON')
        snapshots=con.execute('SELECT s.id FROM atlas_snapshots s JOIN atlas_seals z ON z.snapshot=s.id '
                              'WHERE s.id LIKE ?',(snapshot_key+'@sha256:%',)).fetchall()
        if not snapshots:return None,None
        if len(snapshots)!=1:raise ValueError('Неоднозначная версия исполняемого снимка общей библиотеки')
        snapshot=snapshots[0][0]
        rows=con.execute('SELECT r.id,r.payload_json FROM revisions r JOIN atlas_members m ON m.revision=r.id '
                         'WHERE m.snapshot=?',(snapshot,)).fetchall()
    records={json.loads(raw)['id']:(revision,json.loads(raw)) for revision,raw in rows}
    revision,manifest=records['runtime.package']
    data={**manifest['package_metadata'],
          'rules':[records['rule.'+rid][1]['executable_rule'] for rid in manifest['rule_ids']]}
    if digest(data)!=digest(expected) or digest(data)!=manifest['library_hash'] or manifest['operation_hash']!=version():
        raise ValueError('Исполняемые записи общей библиотеки не совпадают с закреплённой версией пакета')
    return data,{'kind':'atlas_snapshot','path':str(database),'snapshot':snapshot,'package_revision':revision}
