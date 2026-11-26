"""Compare on a real ray with the shared rule agenda and replay the resulting proof DAG."""
from time import perf_counter
import expressions as m
import polynomial as poly
from fractions import Fraction as F
from model import Unsupported,freeze,canonical,digest,q
from operations import version
from search import Engine
from verify import require,replay_dag


def source_claims(t):
    from graphs import SET_TASK_FIELDS,comparison_inputs,interval_terms,order_source_method
    if t.get('kind',t.get('task_type'))=='monotonicity_proof':
        g=t['goal'];direction={'prove monotonic increasing':1,'prove monotonic decreasing':-1}.get(g.get('goal'))
        if (not direction or set(t)-SET_TASK_FIELDS-{'method_requirement'} or set(g)-{'expression','domain','goal','variable'}
                or t.get('assumptions') or t.get('transcription_notes')):raise Unsupported('Unbound monotonicity requirements')
        verb='возрастает' if direction==1 else 'убывает'
        printed=f'Доказать, что {g["expression"]} монотонно {verb} на {g["domain"]}.'
        order_source_method(t,printed,('derivative_sign','strict_by_derivative'))
        var=g.get('variable','x');ctx=m.context(dict(variable=var));f=m.parse(g['expression'],var)
        a,b,lc,rc=interval_terms(g['domain'],ctx)
        if compare_scalar(b,a)<=0:raise Unsupported('Strict monotonicity needs a nondegenerate interval')
        I=('comparison_interval',a,b,lc,rc);ctx.update(domain='ordered_interval',variable=var,comparison_interval=I)
        oriented=f if direction==1 else ('mul',q(-1),f)
        return ctx,{'claim1':('strictly_increasing_on_interval',oriented,I)},[g['goal']]
    claims,constraints,output=comparison_inputs(t)
    v=('v','x');a=None;b='+inf';lc=rc=False
    for lo,hi,strict in constraints:
        if hi==v and a is None and m.constant_defined(lo,m.context({})):a,lc=m.simplify(lo),not strict
        elif lo==v and b=='+inf' and m.constant_defined(hi,m.context({})):b,rc=m.simplify(hi),not strict
        else:raise Unsupported('A single original interval must be explicit')
    if a is None or b!='+inf' and compare_scalar(b,a)<=0:raise Unsupported('A nonempty interval with finite left endpoint is required')
    I=('comparison_interval',a,b,lc,rc)
    ctx=m.context(dict(variable='x'));ctx.update(domain='ordered_interval',variable='x',comparison_interval=I)
    roots={f'claim{i+1}':('interval_comparison',lo,hi,'>' if strict else '>=',I) for i,(lo,hi,strict) in enumerate(claims)}
    return ctx,roots,output


def compare_scalar(a,b):
    from quadrature import enclose
    if a==b:return 0
    if a=='+inf' or b=='-inf':return 1
    if a=='-inf' or b=='+inf':return -1
    e=m.simplify(m.add(a,m.neg(b)));sg=m.sign(e,m.context({}))
    if sg is not None:return sg
    l,r=enclose(e,None)
    if l>0 or r<0:return 1 if l>0 else -1
    raise Unsupported('An exact ordering of interval endpoints is required')


def order_tidy(e):
    from operations import expression_positions
    # On a regular tangent branch, retain its value as a polynomial generator.
    # Distinct private atoms are replaced before returning any certified expression.
    atoms={z for _,z in expression_positions(e) if z[0]=='tan' and m.variable_in(z)}
    if not atoms:return m.simplify(e)
    replacements={z:('s','@branch'+str(i)) for i,z in enumerate(sorted(atoms,key=canonical))}
    return m.substitute(m.simplify(m.substitute(e,replacements)),{v:k for k,v in replacements.items()})


def phase_interval(angle,var,left,right):
    "The two endpoint phases in units of pi for a nonconstant, defined affine function."
    from integrals import affine
    if isinstance(left,str) or isinstance(right,str):raise Unsupported('Finite phase endpoints are required')
    ctx=m.context(dict(variable=var));x=('v',var)
    slope,offset=affine(angle,var)
    if not m.constant_defined(slope,ctx) or m.sign(slope,ctx) not in (-1,1) or not m.constant_defined(offset,ctx):
        raise Unsupported('A regular affine phase is required')
    values=[m.substitute(angle,{x:z}) for z in (left,right)]
    if not all(m.constant_defined(z,ctx) for z in values):raise Unsupported('The original affine phase has a hole')
    turns=[m.pi_multiple(m.simplify(z)) for z in values]
    if None in turns or turns[0]==turns[1]:raise Unsupported('Unproved endpoint phases or constant phase')
    return tuple(turns)


def phase_zeros(tag,turns,lc,rc):
    "The first and last integer labels of zeros in the stated interval."
    from math import floor,ceil
    a,b=turns
    if a>b:a,b,lc,rc=b,a,rc,lc
    shift=F(1,2) if tag=='cos' else F(0)
    a,b=a-shift,b-shift
    return (ceil(a) if lc else floor(a)+1),(floor(b) if rc else ceil(b)-1)


def primitive(name,args,ctx):
    from graphs import domain_partition
    from tasks import domain_conditions
    if ctx.get('domain')!='ordered_interval':return []
    I=freeze(ctx['comparison_interval']);_,anchor,upper,lc,rc=I
    def supported(z):
        if z[0] in ('v','pi','q'):return True
        return z[0] in ('add','mul','div','pow','sin','cos','exp','ln','sqrt','atan','tan','cot') and all(
            supported(c) for c in z[1:] if isinstance(c,tuple))
    def covers(guards,left_closed,right_closed):
        rational=[]
        for relation,z in guards:
            if relation=='nonzero' and z[0]=='pow' and z[2]!=0:z=z[1]
            if relation=='nonzero' and z[0] in ('sin','cos') and m.variable_in(z):
                turns=phase_interval(z[1],ctx['variable'],anchor,upper)
                first,last=phase_zeros(z[0],turns,left_closed,right_closed)
                if first<=last:return False
            else:rational.append((relation,z))
        guards=rational
        if not guards:return True
        part=domain_partition(ctx['variable'],guards,simplify_guards=True)[0]
        cuts=[]
        for _,a,b,d in part['cuts']:cuts.append(m.simplify(m.add(a,m.mul(b,('sqrt',q(d))))))
        for i,z in enumerate(cuts):
            l=compare_scalar(z,anchor);r=compare_scalar(upper,z)
            if (l>0 or not l and left_closed) and (r>0 or not r and right_closed) and not part['point_membership'][i]:return False
        ends=['-inf',*cuts,'+inf']
        return all(ok or compare_scalar(right,anchor)<=0 or compare_scalar(left,upper)>=0
                   for left,right,ok in zip(ends,ends[1:],part['open_cells']))
    def tested(e,relation):return m.sign(e,ctx) in ((1,) if relation=='>' else (0,1))
    try:
        if name=='interval_everywhere_nonzero':
            e,=args;return [()] if covers(domain_conditions(e)+[('nonzero',e)],False,False) else []
        if name=='interval_difference':
            l,h=args;return [(order_tidy(('add',h,('mul',q(-1),l))),)]
        if name=='interval_constant_factor':
            term,domain=args
            if domain!=I or term[0]!='mul':return []
            for scalar,remainder in ((term[1],term[2]),(term[2],term[1])):
                if not m.variable_in(scalar) and m.variable_in(remainder) and m.constant_defined(scalar,ctx):
                    return [(scalar,remainder)]
            return []
        if name=='interval_scalar_positive':
            scalar,=args
            return [()] if not m.variable_in(scalar) and m.constant_defined(scalar,ctx) and m.sign(scalar,ctx)==1 else []
        if name=='interval_left':
            return [(anchor,)] if args==(I,) else []
        if name=='interval_source_endpoint':
            l,h,rel,domain=args
            if domain!=I:return []
            for p,closed in ((anchor,lc),(upper,rc)):
                if closed and not tested(m.add(m.substitute(h,{('v','x'):p}),m.neg(m.substitute(l,{('v','x'):p}))),rel):return []
            return [()]
        if name in ('interval_defined','interval_continuous_left','interval_continuous_source','interval_differentiable'):
            e,domain=args
            if domain!=I or not supported(e):return []
            smooth=name=='interval_differentiable';left=False if smooth else True if name=='interval_continuous_left' else lc
            return [()] if covers(domain_conditions(e,smooth),left,False if smooth else rc) else []
        if name=='interval_value':
            e,rel,point=args;at=m.substitute(e,{('v',ctx['variable']):point})
            return [()] if m.constant_defined(at,ctx) and tested(at,rel) else []
        e,rel,domain=args
        if domain!=I:return []
        if rel not in ('>','>='):return []
        if name=='interval_even_sum':
            if not covers(domain_conditions(e),False,False):return []
            n,d=m.rational_form(e)
            if not d or any(c<0 or any(k%2 for _,k in mon) for p in (n,d) for mon,c in p.items()):return []
            if not d.get(()) and not covers([('nonzero',m.poly_expr(d))],False,False):return []
            return [()] if rel=='>=' or n.get((),0)>0 else []
        if name=='interval_rational':
            poly.rf(e,ctx['variable'])
            return [()] if covers(domain_conditions(e)+[('positive' if rel=='>' else 'nonnegative',e)],False,False) else []
        if name=='interval_trigonometric_range':
            if not covers(domain_conditions(e),False,False):return []
            n,d=m.rational_form(e)
            if d!={():F(1)}:return []
            margin=n.get((),F(0));found=False
            for mon,k in n.items():
                if not mon:continue
                if len(mon)!=1 or mon[0][1]!=1 or mon[0][0][0] not in ('sin','cos'):return []
                found=True;margin-=abs(k)
            return [()] if found and (margin>0 or rel=='>=' and not margin) else []
    except (Unsupported,poly.NotRational,poly.Undefined,poly.ResourceBound,ArithmeticError,ValueError):return []
    return []


def comparison_value(roots,requested):
    from tasks import source
    goal=next(iter(roots.values()))
    if goal[0]=='strictly_increasing_on_interval':
        return dict(strict_monotonicity=requested[0].rsplit(' ',1)[1],interval=goal[2])
    claims=[dict(left=g[1],right=g[2],relation='<' if g[3]=='>' else '≤') for g in roots.values()]
    pictures=['На заданном промежутке график y = '+source(c['left'])+(' строго ниже' if c['relation']=='<' else ' лежит не выше')+
              ' графика y = '+source(c['right'])+'.' for c in claims] if 'geometric_interpretation' in requested else []
    return dict(claims=claims,geometric_interpretation=pictures)


def solve_comparison(task,lib,limits):
    try:ctx,goals,requested=source_claims(task)
    except (Unsupported,TypeError,ValueError,KeyError):return None
    start=perf_counter();engine=Engine(lib,ctx,limits,task_kind='ordered_interval',trace_rules=True)
    engine.run(goals.values(),lambda s:all(s.answers(g) for g in goals.values()))
    events=[]
    comparison_heads={rule['head'][0] for rid,rule in lib.by_id.items() if rid.startswith('comparison.')}
    for item in engine.questions.values():
        g=item['goal']
        if g[0] not in comparison_heads:continue
        completed={engine.proofs[a['proof']]['rule'] for a in item['answers']}
        events.append(dict(goal=g,matched=[r['id'] for r,_ in lib.candidates(g,ctx)],
                           tried=engine.rule_attempts.get(canonical(g),[]),completed=sorted(completed)))
    rejected=[r for r in engine.rejections if r['operation'].startswith(('interval_','chord_'))]
    r=dict(schema='comparison-rule-dag/v1',task=task,library_hash=lib.hash,operation_hash=version(),knowledge_source=lib.origin,context=ctx,
           status='OPEN',value=None,proof=None,search_events=dict(diagnostic_only=True,questions=events,rejected=rejected,stats=engine.stats()))
    if all(engine.answers(g) for g in goals.values()):
        ids={k:engine.answers(g)[0]['proof'] for k,g in goals.items()}
        r.update(status='SOLVED',proof={**ids,'nodes':engine.export_nodes(ids.values())},value=comparison_value(goals,requested))
        r['verification']=verify_comparison(r,lib,task)
    r['elapsed_seconds']=perf_counter()-start
    return r


def verify_comparison(r,lib,expected_task=None):
    require(expected_task is None or canonical(r['task'])==canonical(expected_task),'Other source comparison or ray')
    require(r['library_hash']==lib.hash and r['operation_hash']==version() and r['status']=='SOLVED','Incomplete or changed comparison basis')
    ctx,goals,out=source_claims(r['task'])
    require(canonical(ctx)==canonical(r['context']),'Changed source ray')
    proof=replay_dag(r['proof'],lib,ctx,goals)
    require(all(v is True for v in proof['values'].values()) and canonical(r['value'])==canonical(comparison_value(goals,out)),
            'Unproved comparison or missing geometric conclusion')
    return dict(status='passed',complete=True,checked_nodes=proof['checked_nodes'],scope='each printed comparison over the original real interval, its included endpoints, and the requested interpretation')


def comparison_report(r,lib):
    from tasks import source
    _,left,right,lc,rc=r['context']['comparison_interval']
    end=lambda t:('−∞' if t=='-inf' else '+∞' if t=='+inf' else source(t))
    lines=['Промежуток '+('[' if lc else '(')+end(left)+', '+end(right)+(']' if rc else ')')+'.']
    for node in r['proof']['nodes']:
        if node['goal'][0]=='nondecreasing_on_interval':
            lines.append(source(node['goal'][1])+' не убывает по теореме Лагранжа. Непрерывность, дифференцируемость внутри и знак производной установлены в цепочке.')
        if node['goal'][0]=='interval_sign':
            lines.append(lib.by_id[node['rule']]['label']+'. '+source(node['goal'][1])+' '+node['goal'][2]+' 0.')
    if 'strict_monotonicity' in r['value']:
        lines.append('По теореме Лагранжа функция строго '+('возрастает.' if r['value']['strict_monotonicity']=='increasing' else 'убывает.'))
        return '\n'.join(lines)
    for c in r['value']['claims']:lines.append(source(c['left'])+' '+c['relation']+' '+source(c['right'])+'.')
    return '\n'.join(lines+r['value']['geometric_interpretation'])
