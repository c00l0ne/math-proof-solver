"""Compose general methods on fresh inputs; retain proofs outside the library."""
from contextvars import ContextVar
from collections import Counter
from dataclasses import asdict,replace
from integrals import solve_integral
from time import perf_counter
from model import freeze,Unsupported
from search import Engine,Limits
from library import Library
from operations import GERM_GOALS,compute,version,unpack,germ_conclusion,expression_positions
import expressions as m
from verify import verify,same_value,different_value,expansion_witness_sources,same_side_answer
from polynomial import ResourceBound
from tasks import COMPOSED_SCHEMAS,COMPOSED_GOALS,composed_kind,compose_goal,integral_charts,sum_limit_strategies,compile_derivative,compile_point_derivative_side,derivative_conclusion,compile_global_task


def one_side(task,library,limits,assumptions,side,order):
    ctx,method=library.limit_context(task,assumptions,side,order)
    expr,normalization=m.normalized(task,ctx,side)
    kind=task.get('kind',task.get('task_type','limit'));expansion=kind in GERM_GOALS
    ug,dg,lg=('undefined',expr),('defined',expr),('germ' if expansion else 'limit',expr)
    witnesses=method.get('expansion_rules',()) if method else ()
    def witness_rule(rule,value,steps,known):
        if rule['head'][0] not in ('germ','limit'):return False
        direct,children=expansion_witness_sources(rule,value,steps,witnesses)
        return direct or any(child in known for child in children)
    engine=Engine(library,ctx,limits,operations=compute,required_rules={lg:method['root_rule']} if method else None,
                  task_kind=kind if expansion else 'limit',witness_rule=witness_rule if witnesses else None)
    start=perf_counter()
    for predicate in (() if expansion else library.data.get('initial_normalization_predicates',[])):
        initial=(predicate,expr)
        engine.run([initial],lambda e:bool(e.answers(initial)))
        if engine.answers(initial):break
    selected=None
    examined=0
    refine=False
    def complete(e):
        nonlocal selected,examined,refine
        if e.answers(ug) or selected is not None or refine:return True
        if not e.answers(dg):return False
        answers=e.answers(lg)
        while examined<len(answers):
            answer=answers[examined];examined+=1
            if witnesses and answer['proof'] not in e.witnessed:continue
            value=(germ_conclusion if expansion else m.scalar_limit_conclusion)(answer['value'],ctx)
            if value is not None:
                selected=answer['proof'],value
                return True
            if ctx.get('leading_asymptotic_term'):
                terms,remainder=unpack(answer['value'])
                if not terms and remainder is not None and remainder>=order:
                    refine=True  # This germ proves o(|Δ|^order), so try a higher precision.
                    return True
        return False
    engine.run([ug,dg,lg],complete)
    complete(engine)  # The final agenda job can publish an answer and empty the queue.
    result={'side':side,'context':ctx,'normalization':normalization,'normalized_expression':expr,
            'library_hash':library.hash,'operation_hash':version(),'order':order,'limits':asdict(limits),
            'status':'BUDGET_LIMIT' if engine.cutoffs else 'OPEN','value':None,'proof':None,
            'stats':engine.stats(),'elapsed_seconds':round(perf_counter()-start,6)}
    root,domain=None,None
    if engine.answers(ug):
        result['status']='DOMAIN_ERROR';root=engine.answers(ug)[0]['proof']
    elif engine.answers(dg) and engine.answers(lg):
        if refine:result['reason']='The germ vanishes through the current precision'
        elif selected is None:result['reason']='The available germ does not establish the requested result or method'
        else:
            root,value=selected
            domain=engine.answers(dg)[0]['proof']
            result.update(status='SOLVED',value=value)
    if root:result['proof']={'root':root,'domain':domain,'nodes':engine.export_nodes([root,domain])}
    questions=[r['goal'] for r in engine.questions.values() if not r['answers']]
    result['unresolved_constant_guards']=[g for g in questions if g[0] in ('nonzero_constant','positive_constant')][:30]
    result['open_questions']=questions[:60]
    return result


def unresolved_parameter(sides,ctx,extra_guards=()):
    used={a['symbol'] for a in ctx['assumptions']}
    def symbols(e):
        if not isinstance(e,tuple):return set()
        if e[0]=='s':return {e[1]}
        return set().union(*(symbols(c) for c in e[1:] if isinstance(c,tuple)))
    # Do not split away a parameter occurring in a compound assumption.
    # Such branches need a separate consistency proof, not a guessed domain.
    for guard in ctx.get('nonzero_expressions',[])+ctx.get('positive_expressions',[]):used.update(symbols(freeze(guard)))
    for guard in [q[1] for side in sides for q in side['unresolved_constant_guards']]+list(extra_guards):
        names=symbols(freeze(guard))-used
        if len(names)==1:return next(iter(names))
    return None


def residual_precisions(task,orders):
    """Prefer the denominator valuation for an explicit nonlinear Taylor residual."""
    from polynomial import rf,valuation,NotRational,Undefined
    from tasks import domain_conditions,known_guard
    if '/' not in str(task.get('expression','')):return orders
    try:
        ctx=m.context(task)
        if isinstance(ctx['point'],str):return orders
        raw,_=m.normalized(task,ctx,'right')
        if raw[0]!='div' or raw[1][0]!='add':return orders
        top,bottom=rf(raw[2],ctx['variable']);a,b=valuation(top),valuation(bottom)
        if a is None or b is None or not orders[0]<a-b<=orders[-1]:return orders
        k=a-b;t=('v',ctx['variable']);p,d=m.rational_form(raw[1])
        if set(d)!={()}:return orders
        atoms={u for mon in p for u,_ in mon if u!=t and m.variable_in(u)}
        if len(atoms)!=1:return orders
        atom=next(iter(atoms));at={t:m.ZERO}
        if atom[0] not in m.FUNCTIONS or ((atom,1),) not in p:return orders
        if any(any(u==atom for u,_ in mon) and mon!=((atom,1),) for mon in p):return orders
        if max((dict(mon).get(t,0) for mon in p),default=0)!=k-1:return orders
        if not all(known_guard((rel,m.substitute(e,at)),ctx) for rel,e in domain_conditions(atom,True)):return orders
        if m.simplify(m.substitute(m.poly_expr(p),at))!=m.ZERO:return orders
        preferred=next(n for n in orders if n>=k)
        return (preferred,*(n for n in orders if n!=preferred))
    except (NotRational,Undefined,Unsupported,ResourceBound,ArithmeticError,ValueError,TypeError,KeyError):
        return orders


def solve(task,library=None,limits=None,order=None,max_case_depth=2):
    library=library or Library()
    limits=limits or Limits(questions=4000,term_nodes=4000,depth=48)
    kind=task.get('kind',task.get('task_type','limit'))
    if (composed_kind(task)=='printed_inequality' or kind=='monotonicity_proof') and 'interval_sign' in library.data['predicates']:
        from ray_proofs import solve_comparison
        trial=solve_comparison(task,library,limits)
        if trial is not None and (trial['status']=='SOLVED' or kind=='monotonicity_proof'):return trial
    if kind=='construct_graph':
        if library.data.get('source_geometric_domains') and composed_kind(task)=='source_geometric_domains':
            return solve_composed(task,library,limits,order)
        from graphs import solve_graph
        return solve_graph(task,library)
    if kind!='integrate' and composed_kind(task) in COMPOSED_GOALS:
        if kind=='functional_series_convergence_set':
            prior=solve_global(task,library,limits)
            if prior['status']=='SOLVED' or not library.data.get('power_series_boundary'):return prior
        result=solve_composed(task,library,limits,order)
        if composed_kind(task)=='printed_inequality' and 'interval_sign' in library.data['predicates'] and trial is not None and result['status']!='SOLVED':
            result['alternative_search']=trial['search_events']
        if (kind=='proof_about_real_functions' or composed_kind(task)=='order_certificate') and result['status']!='SOLVED':
            prior=solve_global(task,library,limits)
            if prior['status']=='SOLVED':return prior
        if result['status']=='SOLVED' or 'branches' in task or kind not in ('differentiate','limit','series_convergence','finite_expansion'):return result
    if kind=='partial_derivatives':return solve_partial_bundle(task,library,limits,order)
    if kind=='series_convergence':
        result=solve_series_comparison(task,library,limits,order)
        if result['status']!='SOLVED' and 'series_classification' in library.data['predicates']:
            trial=solve_global(task,library,limits)
            if trial['status']=='SOLVED':return trial
        return result
    if kind=='euler_homogeneity':return solve_euler_homogeneity(task,library,limits,order)
    if kind=='integrate':return solve_integral(task,library,limits,order)
    if kind in ('real_inequality','solve_real_inequality','proof','prove','prove_equality','cartesian_field_operator',
                'proof_about_real_functions','prove_continuity','prove_boundedness','formal_vector_identity','functional_series_convergence_set'):
        return solve_global(task,library,limits)
    if kind in ('differentiate','derivative_at'):
        return solve_derivative(task,library,limits,order,max_case_depth)
    expansion=kind in GERM_GOALS
    if kind!='limit' and not expansion:
        return {'schema':'unsupported-goal-run/v1','task':task,'library_hash':library.hash,
                'operation_hash':version(),'status':'UNSUPPORTED','value':None,'elapsed_seconds':0,
                'reason':'Ещё не поддержан вид цели: '+str(kind),'verification':{'status':'incomplete'}}
    started=perf_counter()
    if order is None:
        attempts=[]
        degree=task.get('degree')
        orders=(2,4,6,8)
        if kind=='leading_asymptotic_term':orders=(2,4,8,16,24)
        elif expansion:
            start=max(1,degree) if type(degree) is int and 0<=degree<=24 else 1
            orders=tuple(dict.fromkeys(min(24,start+offset) for offset in (0,2,4,8,24)))
        elif library.data.get('prioritize_explicit_taylor_residual'):orders=residual_precisions(task,orders)
        for precision in orders:
            result=solve(task,library,limits,precision,max_case_depth)
            attempts.append({'order':precision,'status':result['status']})
            if result['status']=='BUDGET_LIMIT':
                attempts[-1]['cutoffs']=sorted({name for s in all_sides(result) for name in s['stats']['cutoffs']})
            if result['status'] in ('SOLVED','SOLVED_CASES','DOMAIN_ERROR','DOES_NOT_EXIST','UNSUPPORTED'):break
        result['precision_attempts']=attempts
        result['elapsed_seconds']=round(perf_counter()-started,6)
        return result
    base={'schema':'unified-chain-search-run/v4','task':task,'library_hash':library.hash,
          'knowledge_source':library.origin,
          'operation_hash':version(),'assessment':'Search and replay relative to admitted general rules; not formal certification.'}
    max_order=24 if expansion else 12
    if type(order) is not int or not 1<=order<=max_order:raise ValueError(f'Order must be in 1..{max_order}')

    def run(assumptions,depth):
        ctx,targets=m.limit_directions(task,assumptions,library.data.get('magnitude_infinity_contract'))
        sides=[one_side(target,library,limits,assumptions,side,order) for target,side in targets]
        comparison_guards=()
        node={'assumptions':assumptions,'sides':sides,'value':None}
        magnitude=task.get('approach',{}).get('mode')=='magnitude_infinity'
        live=[s for s in sides if s['status']!='DOMAIN_ERROR'] if magnitude else sides
        if magnitude and len(live)==1:
            node.update(status=live[0]['status'],value=live[0]['value'])
        elif any(s['status']=='DOMAIN_ERROR' for s in sides):
            # Keep the other side if solved; replay requires every retained side complete.
            node['status']='DOMAIN_ERROR'
            if any(s['status'] not in ('SOLVED','DOMAIN_ERROR') for s in sides):node['status']='OPEN'
        elif all(s['status']=='SOLVED' for s in sides):
            if all(same_side_answer(sides[0]['value'],s['value'],s['context']) for s in sides):
                node.update(status='SOLVED',value=sides[0]['value'])
            elif not expansion and len(sides)==2 and different_value(sides[0]['value'],sides[1]['value'],ctx):
                node['status']='DOES_NOT_EXIST'
            else:
                node['status']='OPEN'
                if magnitude:
                    comparison_guards=(m.add(sides[0]['value'],m.neg(sides[1]['value'])),)
        else:node['status']='BUDGET_LIMIT' if any(s['status']=='BUDGET_LIMIT' for s in sides) else 'OPEN'
        if node['status'] in ('OPEN','BUDGET_LIMIT') and depth<max_case_depth:
            symbol=unresolved_parameter(sides,ctx,comparison_guards)
            if symbol:
                children=[run(assumptions+[{'symbol':symbol,'relation':relation}],depth+1) for relation in ('zero','nonzero')]
                node={'assumptions':assumptions,'split_symbol':symbol,'cases':children,
                      'status':'SOLVED_CASES' if all(c['status'] in ('SOLVED','SOLVED_CASES','DOMAIN_ERROR','DOES_NOT_EXIST') for c in children) else 'PARTIAL_CASES',
                      'initial_attempt_stats':[s['stats'] for s in sides], 'value':None}
        return node

    try:
        base.update(run([],0))
        if base['status'] in ('SOLVED','SOLVED_CASES','DOMAIN_ERROR','DOES_NOT_EXIST'):
            base['verification']=verify(base,library,expected_task=task)
        else:base['verification']={'status':'incomplete'}
    except Unsupported as exc:
        base.update(status='UNSUPPORTED',value=None,reason=str(exc),assumptions=[],verification={'status':'incomplete'})
    base['elapsed_seconds']=round(perf_counter()-started,6)
    return base


def point_derivative_side(compilation,library,limits,side,order):
    compiled=compile_point_derivative_side(compilation,side,order)
    ctx,goal=compiled['context'],compiled['goal'];started=perf_counter()
    engine=Engine(library,ctx,limits,operations=compute)
    engine.run([goal],lambda e:bool(e.answers(goal)))
    result={**compiled,'library_hash':library.hash,'operation_hash':version(),'limits':asdict(limits),
            'status':'BUDGET_LIMIT' if engine.cutoffs else 'OPEN','value':None,
            'value_in_original_variable':None,'proof':None,'stats':engine.stats(),
            'elapsed_seconds':round(perf_counter()-started,6)}
    for answer in engine.answers(goal):
        if not compute('finite',[answer['value']],ctx):continue
        value=freeze(answer['value']);root=answer['proof']
        result.update(status='SOLVED',value=value,
            value_in_original_variable=('mul',m.q(-1),value) if side=='left' else value,
            proof={'root':root,'nodes':engine.export_nodes([root])})
        break
    return result


def solve_point_derivative(task,compilation,library,limits,order):
    """Use local derivative facts in the same graph through the finite MVT bridge."""
    if task.get('method_requirement')=='from_definition':raise Unsupported('Метод определения не допускает мост Лагранжа')
    started=perf_counter()
    if order is None:
        attempts=[]
        for precision in (2,4,6,8):
            result=solve_point_derivative(task,compilation,library,limits,precision)
            attempts.append({'order':precision,'status':result['status']})
            if result['status'] in ('SOLVED','DOES_NOT_EXIST'):break
        result['precision_attempts']=attempts;result['elapsed_seconds']=round(perf_counter()-started,6)
        return result
    result={'schema':'point-derivative-chain-run/v1','task':task,'compilation':compilation,
            'library_hash':library.hash,'operation_hash':version(),'knowledge_source':library.origin,
            'order':order,'limits':asdict(limits),'value':None,
            'sides':[point_derivative_side(compilation,library,limits,s,order) for s in ('right','left')]}
    sides=result['sides']
    if all(s['status']=='SOLVED' for s in sides):
        right,left=(s['value_in_original_variable'] for s in sides)
        if same_value(right,left):result.update(status='SOLVED',value=right)
        elif different_value(right,left,sides[0]['context']):result['status']='DOES_NOT_EXIST'
        else:result['status']='OPEN'
    else:result['status']='BUDGET_LIMIT' if any(s['status']=='BUDGET_LIMIT' for s in sides) else 'OPEN'
    result['verification']=verify(result,library,expected_task=task) if result['status'] in ('SOLVED','DOES_NOT_EXIST') else {'status':'incomplete'}
    result['elapsed_seconds']=round(perf_counter()-started,6)
    return result


def solve_derivative(task,library,limits,order,max_case_depth):
    started=perf_counter()
    result={'schema':'compiled-calculus-run/v1','task':task,'library_hash':library.hash,
            'operation_hash':version(),'knowledge_source':library.origin,'value':None,
            'assessment':'General calculus compilation and replay in the same graph; explicit sufficient-domain scope.'}
    try:
        method=library.data.get('task_compilers',{}).get(task['kind'])
        if method not in ('derivative_definition','derivative_definition_or_mvt'):
            raise Unsupported('В текущем снимке не объявлено построение производной')
        compilation=compile_derivative(task);result['compilation']=compilation
        if not compilation['point_defined']:
            result.update(status='POINT_DOMAIN_UNRESOLVED',verification={'status':'incomplete'})
        else:
            child=None
            if method=='derivative_definition_or_mvt' and task['kind']=='differentiate' and task.get('method_requirement')!='from_definition' and library.data.get('pointwise_table_contract')=='original_variable_then_arbitrary_fixed_point':
                attempt=solve_original_table(task,library,limits)
                if attempt['status'] in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'):child=attempt
            if child is None and method=='derivative_definition_or_mvt' and task.get('method_requirement')!='from_definition':
                attempt=solve_point_derivative(task,compilation,library,limits,order)
                if attempt['status'] in ('SOLVED','DOES_NOT_EXIST'):child=attempt
                else:
                    result['initial_point_derivative_attempt']={'diagnostic_only':True,'status':attempt['status'],
                        'elapsed_seconds':attempt['elapsed_seconds'],'precision_attempts':attempt.get('precision_attempts'),
                        'sides':[{'side':s['side'],'status':s['status'],'stats':s['stats']} for s in attempt['sides']]}
            if child is None:child=solve(compilation['compiled_limit_task'],library,limits,order,max_case_depth)
            result['child_result']=child;result.update(derivative_conclusion(task,compilation,child))
            if child['status'] in ('SOLVED','SOLVED_CASES','DOMAIN_ERROR','DOES_NOT_EXIST') or child.get('schema')=='original-table-derivative/v1' and child['status']=='FORMULA_ON_SUFFICIENT_DOMAIN':
                result['verification']=verify(result,library,expected_task=task)
            else:result['verification']={'status':'incomplete'}
    except (Unsupported,KeyError) as exc:
        result.update(status='UNSUPPORTED',reason=str(exc),verification={'status':'incomplete'})
    result['elapsed_seconds']=round(perf_counter()-started,6)
    return result


def expression_pair_priority(goal):
    left,right=(dict(expression_positions(e)) for e in goal[1:])
    common=sum((Counter(left.values())&Counter(right.values())).values())
    aligned=sum(right.get(path)==term for path,term in left.items())
    return -common,-aligned


def global_record(task,library):
    return {'schema':'global-chain-search-run/v1','task':task,'library_hash':library.hash,
            'operation_hash':version(),'knowledge_source':library.origin,'value':None}


def search_global(result,library,limits,*,all_proofs=False,max_steps=None,plan_trial=False):
    compilation=compile_global_task(result['task'],library)
    ctx,goal=compilation['context'],compilation['goal']
    ranked=library.data.get('prioritize_matching_expression_pairs',())
    priority=None
    if goal[0] in ranked:
        priority=lambda q:expression_pair_priority(q) if q[0] in ranked else (0,0)
    # A stored tactic tries only the selected original rules, with fresh bindings
    # on this input. An explicit work cap or an all-proofs request keeps its single agenda.
    attempts=[]
    for plan in library.proof_plans.get(goal[0],()) if not all_proofs and limits.jobs is None else ():
        query=(plan.root,*goal[1:])
        engine=Engine(plan,ctx,limits).run([query],lambda e:bool(e.answers(query)))
        attempts.append({'plan':plan.key,'jobs':engine.processed})
        if engine.answers(query):
            result['applied_proof_plan']=plan.key
            break
    else:
        if not (plan_trial and attempts):
            query=goal
            engine=Engine(library,ctx,limits,deferred_priority=priority,all_proofs=all_proofs,max_proof_steps=max_steps)
            engine.run([goal],None if all_proofs else lambda e:bool(e.answers(goal)))
    result.update(compilation=compilation,context=ctx,goal=goal,limits=asdict(limits),stats=engine.stats(),proof=None)
    if attempts:result['proof_plan_attempts']=attempts
    return engine,query


def verified_global(result,engine,proof,library):
    if result.get('applied_proof_plan'):proof=engine.library.restore(proof)
    result={**result,'status':'SOLVED','value':engine.proofs[proof['root']]['value'],'proof':proof}
    result['verification']=verify(result,library,expected_task=result['task'])
    return result


def solve_global(task,library,limits,*,plan_trial=False):
    started=perf_counter()
    result=global_record(task,library)
    try:
        engine,goal=search_global(result,library,limits,plan_trial=plan_trial)
        if engine.answers(goal):
            root=engine.answers(goal)[0]['proof']
            result=verified_global(result,engine,{'root':root,'nodes':engine.export_nodes([root])},library)
        else:
            result.update(status='BUDGET_LIMIT' if engine.cutoffs else 'OPEN',verification={'status':'incomplete'})
            if goal[0]=='finite_sum_identity':
                result['open_equalities']=[item['goal'] for item in engine.questions.values()
                                           if item['goal'][0]=='poly_equal' and not item['answers']]
    except ResourceBound as exc:result.update(status='BUDGET_LIMIT',reason=str(exc),verification={'status':'incomplete'})
    except (Unsupported,KeyError) as exc:result.update(status='UNSUPPORTED',reason=str(exc),verification={'status':'incomplete'})
    result['elapsed_seconds']=round(perf_counter()-started,6)
    return result


def solve_proofs(task,library=None,limits=None,max_steps=None,shortest=False):
    """Enumerate distinct acyclic derivations admitted by a global task compiler."""
    if max_steps is not None and (type(max_steps) is not int or max_steps<0):
        raise ValueError('Максимальная длина должна быть целым неотрицательным числом')
    started=perf_counter()
    library=library or Library()
    limits=limits or Limits.exhaustive()
    base=global_record(task,library)
    bound=1 if shortest and max_steps!=0 else max_steps
    summary={'schema':'global-proof-inventory/v1','task':task,'library_hash':library.hash,
             'operation_hash':base['operation_hash'],'limits':asdict(limits),'max_steps':max_steps,'shortest_only':shortest,
             'metric':'distinct_rule_applications_in_proof_dag','status':'PARTIAL','complete':False,
             'complete_through_steps':None,'shortest_steps':None,'shortest_certified':False}
    results=[]
    try:
        if not isinstance(task,dict):raise Unsupported('Ожидалось одно условие задачи в формате JSON')
        if not isinstance(task.get('kind',task.get('task_type')),str):
            raise Unsupported('Не указан поддерживаемый вид глобальной цели')
        jobs=0
        while True:
            available=limits if limits.jobs is None else replace(limits,jobs=limits.jobs-jobs)
            engine,_=search_global(base,library,available,all_proofs=True,max_steps=bound)
            jobs+=base['stats']['jobs']
            if engine.complete_through_steps is not None:
                summary['complete_through_steps']=engine.complete_through_steps
            if (not shortest or engine.answers(base['goal']) or engine.enumeration_complete
                    or engine.complete_through_steps is None or bound==max_steps):
                break
            bound+=1
    except ResourceBound as exc:summary['reason']=str(exc)
    except (Unsupported,KeyError) as exc:summary.update(status='UNSUPPORTED',reason=str(exc))
    else:
        for proof in engine.proof_variants(base['goal']):
            result=verified_global(base,engine,proof,library)
            result['elapsed_seconds']=round(perf_counter()-started,6)
            results.append(result)
        complete=engine.enumeration_complete
        through=summary['complete_through_steps']
        summary.update(stats=base['stats'],total_jobs=jobs,complete=complete,
                       status='COMPLETE' if complete else 'PARTIAL')
        if results:
            first=len(results[0]['proof']['nodes'])
            summary.update(shortest_steps=first,shortest_certified=complete or (through is not None and first<=through))
    summary.update(proof_count=len(results),elapsed_seconds=round(perf_counter()-started,6))
    return summary,results


def all_sides(result):
    if result.get('schema') in COMPOSED_SCHEMAS:
        for child in result.get('children',[]):yield from all_sides(child['proof'])
        return
    if result.get('schema')=='euler-homogeneity-run/v1':yield from all_sides(result.get('child_result',{}));return
    if result.get('schema')=='series-comparison-run/v1':yield from all_sides(result.get('child_result',{}));return
    if result.get('schema')=='original-table-derivative/v1':yield result;return
    if result.get('schema') in ('ordinary-kernel-derivatives/v1','partial-derivative-bundle/v1'):
        for child in result.get('children',[]):yield from all_sides(child)
        return
    if result.get('schema')=='compiled-calculus-run/v1':
        yield from all_sides(result.get('child_result',{}));return
    if 'cases' in result:
        for child in result['cases']:yield from all_sides(child)
    else:yield from result.get('sides',[])


def used_rules(result):
    if result.get('schema')=='global-chain-search-run/v1':return sorted({n['rule'] for n in (result.get('proof') or {}).get('nodes',[])})
    return sorted({n['rule'] for side in all_sides(result) for n in (side.get('proof') or {}).get('nodes',[])})


def pretty(expression,variable_label='τ',*,simplify=True):
    """Presentation only; the full unsimplified statement stays in the proof."""
    if expression in ('+inf','-inf'):return m.render(expression)
    expression=freeze(expression)
    if simplify:
        try:expression=m.simplify(expression)
        except (ResourceBound,ZeroDivisionError):pass
    def show(e,parent=0):
        tag=e[0];precedence=100
        if tag=='q':
            text=str(e[1]) if e[2]==1 else str(e[1])+'/'+str(e[2]);precedence=20 if e[2]!=1 else 100
        elif tag=='v':text=variable_label
        elif tag=='s':text=e[1]
        elif tag=='pi':text='π'
        elif tag=='joined_periodic_primitive':
            phase,local,jump,left=map(show,e[1:])
            text=f'при (2j−1)π < {phase} < (2j+1)π: {local} + j·({jump}); при {phase} = (2j+1)π: {left} + j·({jump}), j ∈ ℤ'
        elif tag=='logarithmic_integral':text='li('+show(e[1])+')'
        elif tag=='indexed_log_primitive':
            x,n,rho=map(show,e[1:])
            text=f'{x}^({rho}) Σ_(j=0)^{n} ((−1)^j · {n}! · (ln {x})^({n}−j))/(({n}−j)! · ({rho})^(j+1))'
        elif tag=='piecewise_primitive':
            pieces=e[1]; singletons={a for (a,b),_ in pieces if a is not None and a==b}
            rows=[]
            for (a,b),p in pieces:
                if a in singletons and a==b:rows.append(show(p)+' при '+variable_label+' = '+show(a));continue
                left='(' if a is None or a in singletons else '['
                right=')' if b is None or b in singletons else ']'
                rows.append(show(p)+' на '+left+(show(a) if a is not None else '−∞')+', '+(show(b) if b is not None else '+∞')+right)
            text='. '.join(rows)
        elif tag in m.FUNCTIONS:text=tag+'('+show(e[1])+')'
        elif tag=='pow':text=show(e[1],31)+'^'+str(e[2]);precedence=30
        elif tag in ('rpow','signed_integer_power'):text=show(e[1],31)+'^('+show(e[2])+')';precedence=30
        elif tag=='real_odd_root':text=str(e[1])+'-й корень из ('+show(e[2])+')'
        elif tag=='add':
            left,right=show(e[1],10),show(e[2],10)
            text=left+(' - '+right[1:] if right.startswith('-') else ' + '+right);precedence=10
        elif tag=='mul':
            text='-'+show(e[2],20) if e[1]==('q',-1,1) else show(e[1],20)+' · '+show(e[2],20);precedence=20
        elif tag=='div':text=show(e[1],20)+' / '+show(e[2],21);precedence=20
        else:return m.render(e)
        return '('+text+')' if precedence<parent else text
    return show(expression)


def short_expansion(value,max_terms=2):
    terms,r=unpack(freeze(value));items=sorted(terms.items())
    if len(items)>max_terms:
        items=items[:max_terms]
        # A finite omitted term of higher order is o(t^last_retained_order).
        r=items[-1][0] if r is None else min(r,items[-1][0])
    pieces=[]
    for p,c in items:
        if p==0:pieces.append(pretty(c))
        else:pieces.append('('+pretty(c)+') · '+('τ' if p==1 else 'τ^('+str(p)+')'))
    if r is not None:pieces.append('o(1)' if r==0 else 'o(τ^('+str(r)+'))')
    return ' + '.join(pieces) or '0'


def factor_parts_lines(result):
    recipe=(result.get('proposal') or {}).get('recipe',{})
    if recipe.get('method')!='factor_parts':return []
    x=result['compilation']['variable'];params=result['compilation']['source_parameters']
    def formula(text):
        return pretty(m.parse(text,x,params),x)
    v=pretty(recipe['primitive_v']['value']['representative'],x)
    du=pretty(recipe['derivative_u']['value'],x)
    remainder=recipe['primitive_remainder']
    g=pretty(remainder['value']['representative'],x)
    learned=['Выбор множителей взят из нескольких проверенных доказательств. Свойства оставшегося множителя и производной u проверены для этого интеграла.'] if 'learned_roles' in recipe else []
    return learned+['Выбраны u = '+formula(recipe['u'])+' и dv = ('+formula(recipe['dv'])+') d'+x+'.',
            'Из dv получено v = '+v+'. Производная u′ = '+du+'.',
            'Оставшийся интеграл ∫ ('+formula(remainder['task']['integrand'])+') d'+x+
            ' имеет первообразную G = '+g+'.',
            'По формуле интегрирования по частям F = u·v − G. Проверено F′ = f на исходной области.']


def equality_report(result,library):
    """Read the selected proof in order, keeping the actual intermediate expressions."""
    from tasks import source
    task=result['task']
    if not result.get('proof'):
        reason=result.get('reason')
        if not reason and result.get('stats',{}).get('cutoffs'):
            reason='Достигнут предел поиска ('+', '.join(result['stats']['cutoffs'])+').'
        return result['status']+'\n'+(reason or 'Из доступных правил доказательство пока не получено.')
    ctx=result['context'];variable=ctx['variable']
    conditions=[pretty(expr,variable,simplify=False)+(' ≠ 0' if relation=='nonzero' else ' > 0')
                for relation,expr in ctx['source_guards']]
    if ctx['punctured_at'] is not None:conditions.append(variable+' ≠ '+source(ctx['punctured_at']))
    plan=result['compilation']
    left=task.get('left') or pretty(plan['left'],variable,simplify=False)
    right=task.get('right') or pretty(plan['right'],variable,simplify=False)
    symbols=[variable,*(p for p in ctx['parameters'] if p!=ctx['point_symbol'])]
    lines=['Докажем '+left+' = '+right+' для действительных '+', '.join(symbols)+
           (' при '+', '.join(conditions) if conditions else '')+'.']
    proof=result['proof'];nodes={n['id']:n for n in proof['nodes']}
    pending=[(proof['root'],False)];visited=set()
    while pending:
        key,reverse=pending.pop()
        if key is None:
            lines.append(reverse)
            continue
        if (key,reverse) in visited:continue
        visited.add((key,reverse))
        node=nodes[key];rule=node['rule']
        if rule=='real_equal.reflexive':continue
        children=[nodes[s['proof']] for s in node['steps'] if 'ask' in s]
        subgoals=[n for n in children if n['goal'][0]=='real_equal']
        if rule=='real_equal.symmetry':
            pending.append((subgoals[0]['id'],not reverse))
            continue
        law=next((n for n in children if n['goal'][0]=='real_identity_step'),None)
        before=node['goal'][1];after=subgoals[0]['goal'][1] if law and subgoals else node['goal'][2]
        if reverse:before,after=after,before
        lhs,rhs=(pretty(e,variable,simplify=False) for e in (before,after))
        if lhs==rhs:lhs,rhs=map(source,(before,after))
        line=lhs+' = '+rhs+'. '+library.by_id[(law or node)['rule']]['label']+'.'
        for premise in (law or {}).get('steps',[]):
            condition=premise.get('ask',[])
            if condition and condition[0] in ('nonzero','positive'):
                suffix=' ≠ 0' if condition[0]=='nonzero' else ' > 0'
                line+=' На заявленной области '+pretty(condition[1],variable,simplify=False)+suffix+'.'
        following=[(n['id'],reverse) for n in subgoals]
        # Congruence concludes after its arguments; a forward rewrite comes before its tail.
        events=[(None,line),*following] if law and not reverse else [*following,(None,line)]
        if law:
            premises=[(s['proof'],False) for s in law['steps'] if s.get('ask',[None])[0]=='real_equal']
            events=premises+events
        pending.extend(reversed(events))
    return '\n'.join(lines+['Обе стороны и промежуточные выражения определены на всей указанной области.'])


def report(result,library=None):
    library=library or Library();task=result['task']
    if (result.get('schema')=='multivariate-operator-proof/v1'
            and 'argument' in result.get('compilation',{})
            and 'method' not in result['compilation']):
        shown={**result,'schema':'source-asymptotic-proof/v1'}
        return report(shown,library)
    plan=result.get('compilation') or {}
    if result.get('schema')=='implicit-graph-values/v1' and plan.get('argument'):
        return report({**result,'schema':'source-asymptotic-proof/v1'},library)
    steps_methods={'method.absolute_harmonic_cells','method.indexed_derivative_phase',
                   'method.monomial_exponential_sign','method.positive_axis_normalization',
                   'method.positive_logarithmic_curvature','method.cosine_coordinate_extrema',
                   'method.factorial_polynomial_series','method.termwise_integral_moments',
                   'method.linear_norm_modulus','method.distinct_radial_phases','method.oscillatory_axis_amplitude',
                   'method.coordinate_moduli_imply_joint_continuity','method.monotone_slice_sandwich',
                   'method.continuous_trace_composition','method.stationarity_of_weighted_affine_product',
                   'method.stationarity_on_radial_image'}
    if (result.get('schema') in ('derivative-sign-chart/v1','strict-extrema-run/v1',
                                 'telescoping-series/v1','termwise-integral/v1','joint-limit/v1','multivariate-extrema/v1') and
            result.get('status')=='SOLVED' and plan.get('argument') and
            (plan.get('theorem') in steps_methods or
             result['schema']=='telescoping-series/v1' and 'start' not in plan)):
        return report({**result,'schema':'source-asymptotic-proof/v1'},library)
    alternative_schema_fields={'fourier-expansion/v1':'angular_frequency','power-series-boundary/v1':'coefficient_profile'}
    schema=result.get('schema');field=alternative_schema_fields.get(schema);plan=result.get('compilation') or {}
    if (field and result.get('status')=='SOLVED' and plan.get('argument') and
            field not in (result['value'] if schema=='fourier-expansion/v1' else plan)):
        return report({**result,'schema':'source-asymptotic-proof/v1'},library)
    if result.get('schema') in ('scalar-source-proof/v1','interval-integral-proof/v1','primitive-recurrence/v1','plane-geometry/v1','exact-ordinary-order/v1','measurement-uncertainty/v1','source-asymptotic-proof/v1','real-function-proof/v1','derivative-proof/v1',
                                'source-series-algebra/v1','fourier-coefficient-transport/v1','abstract-series-theorem/v1','source-uniform-functional/v1',
                                'implicit-differential-identity/v1',
                                'cauchy-series-tails/v1','ordinary-series-proof/v1','certified-series-prefix/v1','functional-primitive/v1','defined-riemann-integral/v1','source-definite-trace/v1',
                                'elementary-proof/v1','source-surface-field/v1','source-geometric-domains/v1',
                                'inverse-definition-derivative/v1') or (
            result.get('schema') in ('structured-limit/v1','continuity-classification/v1','sequence-tail-bounds/v1','sequence-range-and-tail/v1')
            and 'family_reduction' in result.get('compilation',{})) or (
            result.get('schema')=='infinite-rational-product/v1' and 'argument' in result.get('compilation',{})) or (
            result.get('schema')=='linear-primitive/v1' and result.get('compilation',{}).get('chart') in
            {'regular_piecewise',*library.data.get('source_primitive_charts',())}):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'].get('family_reduction',result['compilation'])
        def show(value):
            if isinstance(value,dict):return '\n'.join(f'{key} = '+show(item) for key,item in value.items())
            if isinstance(value,(list,tuple)):
                value=freeze(value)
                if value and isinstance(value[0],str) and value[0] in m.FUNCTIONS|{'q','v','s','pi','add','mul','div','pow','rpow','piecewise_primitive','joined_periodic_primitive','signed_integer_power','real_odd_root'}:
                    try:return pretty(value,'x')
                    except (TypeError,IndexError,ValueError):pass  # A coefficient table row may start with a function name.
                return '['+', '.join(show(item) for item in value)+']'
            return str(value)
        labels={'method.radius_from_rational_poles':'Радиус определяет ближайший неустранимый полюс.',
                'method.reciprocal_series_convolution':'Приравниваем коэффициенты произведения двух рядов коэффициентам единицы.',
                'method.factorial_series_differential_coefficients':'Дифференцируем почленно и сводим одинаковые степени к общей факториальной дроби.',
                'method.exponential_cauchy_product':'Группируем абсолютно сходящееся произведение по общей степени и применяем формулу бинома.',
                'method.uniform_unbounded_polynomial_errors':'Отклонение каждого частичного многочлена от ограниченной функции неограниченно.',
                'method.fourier_coefficient_transport':'Переносим сдвиг или отражение в интегралы коэффициентов Фурье и проверяем нормировку.'}
        argument=p.get('argument') or labels[p['theorem']]
        if result['schema']=='derivative-proof/v1':
            details={k:p[k] for k in ('scope','smooth_domain','exceptional_points') if p.get(k)}
            if details.get('exceptional_points'):
                details['exceptional_points']=[
                    {**row,'traces':[{k:t[k] for k in ('direction','value','outer_slope')} for t in row['traces']]}
                    if 'traces' in row else row for row in details['exceptional_points']]
            return '\n'.join((*argument,show(result['value']),show(details)))
        return (argument if isinstance(argument,str) else '\n'.join(argument))+'\n'+show(result['value'])
    if result.get('schema')=='normalized-applied-extremum/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        plan=result['compilation']
        if 'argument' in plan:
            rows=list(plan['argument'])
            for branch in result['value']['branches']:
                relation=branch['condition']
                sign={'less':' < ','at_least':' ≥ '}[relation['relation']]
                header='При '+pretty(relation['lhs'])+sign+pretty(relation['rhs'])+': '
                if 'maximum' in branch:
                    text='максимум '+pretty(branch['maximum'])+', расстояние от центра большого шара '+pretty(branch['location']['distance_from_large_centre'])
                elif 'supremum' in branch:
                    text='недостижимая верхняя грань '+pretty(branch['supremum'])+' на внешнем луче со стороны меньшего шара'
                else:
                    text='устойчивый угол к горизонту '+pretty(branch['angle_to_horizontal'])
                rows.append(header+text+'.')
            if 'other_stationary_example' in result['value']:
                rows.append('Вертикальный стержень с нижним концом на дне тоже находится в равновесии, но оно неустойчиво.')
            return '\n'.join(rows)
        model=plan['model'];variable=model['scalar']
        text=[model['model_argument'],f'Для {variable} ∈ {model["domain"]} сравниваем профиль '+pretty(plan['profile'],variable)+'.',
              plan['calculus_argument']]
        for row in result['value']['branches']:
            condition='При '+row['condition']+' ' if row['condition'] else ''
            line=condition+f'{variable} = '+pretty(row['coordinate'],variable)+', значение '+pretty(row['bound'],variable)+'.'
            if not row['attained']:line+=' Это предельная грань при вырожденной конфигурации.'
            if row['configuration']:line+=' '+', '.join(k+' = '+pretty(z,variable) for k,z in row['configuration'].items())+'.'
            text.append(line)
        return '\n'.join(text)
    if result.get('schema')=='fourier-integral-representation/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        plan=result['compilation'];value=result['value'];lines=[]
        if plan.get('strategy')=='signed_harmonic_support':
            coeff=value['frequency_cases'][0]['sine_coefficient']
            return '\n'.join([*plan['steps'],'Синусный коэффициент вне резонанса равен '+pretty(coeff['regular'])+'.',
                             'При частоте '+pretty(coeff['at'])+' он равен '+pretty(coeff['resonant'])+'.'])
        if 'radius_cases' in value:
            radius=pretty(plan['radius'])
            lines.append(f'При {radius}<0 носитель пуст. При {radius}=0 обе плотности равны нулю, а исходное значение в нуле '+pretty(plan['zero_point_value'])+'.')
            lines.append(f'При {radius}>0 берём исходные гладкие части носителя.')
            plan=plan['positive'];value=value['radius_cases'][0]['result']
        else:
            entrances={'compact_smooth_pieces':'Разбиваем носитель в точках смены формулы и проверяем первообразные на всех частях.',
                       'decaying_half_axis_modes':'Учитываем ориентацию и знак синуса на отрицательной полуоси. На бесконечности все моды затухают.',
                       'cauchy_exponential_duality':'Берём пару преобразований для затухающей экспоненты. Для нечётной части дифференцируем косинусный момент при положительной частоте.',
                       'gaussian_whole_line':'На всей прямой применяем гауссовы моменты с проверенным квадратичным затуханием.'}
            lines.append(entrances[plan['strategy']])
        if value.get('continuation'):lines.append({'even':'Используем заданное чётное продолжение.','odd':'Используем заданное нечётное продолжение.'}[value['continuation']])
        for name in ('cosine','sine'):
            c=value[name+'_coefficient'];label='a' if name=='cosine' else 'b'
            lines.append(label+'('+value['frequency']+') = '+pretty(c['regular'] if isinstance(c,dict) else c)+'.')
            if isinstance(c,dict):
                for row in c['resonances']:
                    lines.append('К предыдущей формуле прибавляем '+pretty(row['then'])+' при '+pretty(row['if_zero'])+' = 0, иначе '+pretty(row['otherwise'])+'.')
        lines.append('Интеграл по положительным частотам воспроизводит функцию в точках непрерывности.')
        for jump in value['jump_values']:
            lines.append('При '+pretty(jump['point'])+' полусумма односторонних пределов равна '+pretty(jump['average'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='source-spatial-moment/v1':
        from plane_domains import source_spatial_moment_report
        return source_spatial_moment_report(result,pretty)
    if result.get('schema')=='source-integral-transform/v1' or (
            result.get('schema') in ('parameter-improper-evaluation/v1','source-parameter-integral/v1')
            and result.get('compilation',{}).get('theorem')=='method.gaussian_transform_normalization'):
        from quadrature import source_integral_transform_report
        return source_integral_transform_report(result,pretty)
    if result.get('schema')=='parameter-improper-evaluation/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        if 'parameter_cases' in result['value']:
            rows=list(result['compilation']['steps'])
            for case in result['value']['parameter_cases']:
                rows.append('При '+case['condition']+(' интеграл равен '+pretty(case['value'])
                            if 'value' in case else ' интеграл расходится к '+case['divergence'])+'.')
            return '\n'.join(rows)
        p=result['compilation'];v=result['value']['exact_integral']
        if 'strategy' not in p:
            lines=list(p['steps'])
            if isinstance(v,dict) and 'expression' in v:
                lines.append('Интеграл равен '+v['expression']+'.')
                lines.extend(str(k)+' = '+pretty(x)+'.' for k,x in v['parameters'].items())
                for definition in v['functions'].values():
                    lines.extend([definition] if isinstance(definition,str) else definition)
            elif isinstance(v,dict) and 'cases' in v:
                lines.extend('При '+case['condition']+' интеграл равен '+pretty(case['value'])+'.' for case in v['cases'])
            else:lines.append('Интеграл равен '+pretty(v)+'.')
            return '\n'.join(lines)
        if p['strategy']=='frullani_scaled_difference':
            a,b=(pretty(k) for k in p['dilations'])
            line=f'В формуле Фруллани масштабы {a} и {b}. На конечном нижнем срезе остаётся логарифм отношения, на бесконечности вычитаем предельный уровень профиля или применяем Дирихле.'
        elif p['strategy']=='positive_gaussian_moment':
            line='Квадратичный коэффициент затухания '+pretty(p['quadratic_scale'])+' положителен. При нулевой частоте применяем интеграл Эйлера–Пуассона. Интегрирование по частям даёт дифференциальное уравнение для частоты и рекурсию моментов.'
            if p['even_half_line']:line+=' Проверенная чётность даёт половину интеграла по прямой.'
        else:
            line='Разложение числителя в конечную сумму гармоник показывает, что у нуля обнуляются первые '+str(len(p['origin_derivatives']))+' коэффициентов. После '+str(p['integrations_by_parts'])+' интегрирований по частям остаются синусы и разности косинусов с весом 1/x. Формулы Дирихле и Фруллани определяют каждую моду, причём sgn(0)=0.'
            if p['power_substitution']!=1:line='Положительная замена t=x^'+str(p['power_substitution'])+' сохраняет полуось. '+line
        return line+'\nИнтеграл равен '+v+'.'
    if result.get('schema')=='order-certificate/v1' and result.get('status')=='SOLVED':
        return '\n'.join(result['compilation']['steps'])
    if result.get('schema') in ('bound-curve-integral/v1','source-green-integral/v1'):
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation']
        if result['schema']=='bound-curve-integral/v1':
            a,b=(pretty(freeze(e)) for e in plan['bounds'])
            header=f'По координате {plan["injective_coordinate"]+1} параметр {plan["parameter"]} однозначно определён: {a} в начальной точке и {b} в конечной. Подстановка проверена для каждой координаты.'
        elif plan.get('chart')=='direct_circle':header='Параметризация совершает один обход окружности в указанном направлении. Подставляем её в исходную форму.'
        else:header='Уравнение контура или его вершины задают границу области '+str(plan['region'])+'. Направление учтено при применении формулы Грина.'
        return header+'\n'+report(result['children'][0]['proof'],library)
    if result.get('schema')=='rectangular-grid-sums/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];value=result['value']
        lines=['Площадь одной ячейки равна '+pretty(freeze(plan['cell_area']),'n')+'.']
        if plan['derivative_ranges']:
            lines.append('Знаки частных производных постоянны на прямоугольнике. Минимум и максимум в каждой ячейке достигаются в вершинах '+str(plan['corners'])+' (0 — нижний конец координаты, 1 — верхний).')
        else:lines.append('Берём заданную вершину каждой ячейки.')
        lines.append('Для сумм степеней проверены нулевое начальное значение и разность соседних значений. Суммируем по обоим индексам.')
        for key,title in [('sum','Сумма'),('lower_sum','Нижняя сумма'),('upper_sum','Верхняя сумма')]:
            if key in value:lines.append(title+' '+pretty(freeze(value[key]),'n'))
        end=value['limit'] if 'limit' in value else value['limits'][0]
        return '\n'.join([*lines,'При n → ∞ предел равен '+pretty(freeze(end))+'.'])
    if result.get('schema')=='area-from-line-integral/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];c=p['coverage'];n=p['normalization']
        if c['kind']=='odd_coordinate_homeomorphisms':
            step=('Один полный оборот единичной окружности проходит все точки ровно один раз до замыкания. '
                  'Нечётные степени её координат строго возрастают и сохраняют простоту и ориентацию контура.')
        elif c['kind']=='positive_radial_loop':
            step=('Проводим луч v=t·u. На каждом положительном луче из уравнения получается ровно одна точка. '
                  'Доля w=v^p/(u^p+v^p) возрастает от 0 до 1, и оба конца дуги приходят в начало координат. '
                  'В нормализованных координатах произведение UV равно w(1−w), а разность логарифмических '
                  'производных V и U равна 1/[p·w(1−w)]. Поэтому U dV−V dU=dw/p, где p='+pretty(c['degree'])+'.')
        else:
            step=(f"Из квадрата аффинной формы получаем параметр {c['inverse_parameter']}. "
                  f"Пусть {c['parameter']} обозначает этот параметр. Нормализованная верхняя дуга задаётся координатами "
                  f"{c['parameter']}² и {c['normalized_height']}. С прямой она встречается при значениях 0 и 1. "
                  'Проходим отрезок вправо и возвращаемся по дуге над ним.')
        return (step+'\nИнтеграл формы (x dy−y dx)/2 по этой положительной границе равен '+pretty(n['unit_boundary_integral'])+
                '. Сдвиг добавляет интеграл полного дифференциала, равный нулю. Определитель масштабирования равен '+
                pretty(n['determinant'])+'. При отрицательном определителе направление обращается; при нулевом образ вырождается. Площадь равна '+
                pretty(result['value']['area'])+'.')
    if result.get('schema')=='plane-measure/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation']
        if plan['strategy']=='affine_disk':
            detail='Координаты '+', '.join(plan['coordinate_pair'])+' переводят область в круг. Определитель равен '+pretty(freeze(plan['determinant']))+'.'
        elif plan['strategy']=='polar_fibers':
            rad,phi=plan['coordinates']['radius'],plan['coordinates']['angle']
            detail=(f"При x={plan['cartesian_map']['x']} и y={plan['cartesian_map']['y']} угол {phi} проходит полный оборот. "
                    f"Радиус {rad} заключён между "+' и '.join(pretty(freeze(x)) for x in plan['radii'])+f". Множитель площади равен {rad}.")
        else:detail='Выделяем полные квадраты в исходном неравенстве и вычисляем момент по полученному эллипсу.'
        value=result['value']
        return '\n'.join([detail,*[report(c['proof'],library) for c in result['children']],str(value) if isinstance(value,dict) else pretty(freeze(value))])
    if result.get('schema')=='infinite-rational-product/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];v=result['value'];n=plan['index']
        if plan.get('theorem')=='method.wave_product_limit':
            lines=[report(result['children'][0]['proof'],library),
                   f"Перенумеруем множители от единицы. Начальный угол равен {plan['angle']}."]
            for branch in v['branches']:
                note=' Правая часть исходного равенства здесь не определена.' if branch.get('claimed_expression')=='undefined' else ''
                prefix='' if branch['condition']=='always' else f"При {branch['condition']} "
                lines.append(prefix+'получаем '+pretty(freeze(branch['value']))+'.'+note)
            return '\n'.join(lines)
        if 'normalized_prefix' in plan:
            detail=f"Пустое произведение равно 1. Умножение на исходный множитель переводит предыдущее произведение в P({n}) = {plan['normalized_prefix']}."
        elif 'zero_index' in plan:detail=f"При {n} = {plan['zero_index']} множитель равен нулю. Все дальнейшие конечные произведения равны нулю."
        else:detail=f"Множители положительны. По ведущему члену разности с единицей программа проверила сходимость суммы логарифмов. Порядок разности: {plan['difference_order']}."
        conclusion={'diverges_unbounded':'Расходится без конечного предела','diverges_to_zero':'Расходится к нулю без нулевого множителя','converges_nonzero':'Сходится к конечному ненулевому значению','converges_to_zero_by_zero_factor':'Сходится к нулю по соглашению книги'}[v['classification']]
        if 'partial_product_limit' in v:conclusion+=', предел '+pretty(freeze(v['partial_product_limit']))
        return detail+' '+conclusion+'.'
    if result.get('schema')=='function-sign-sets/v1':
        return '\n'.join([result['status'],result.get('reason','')]+[
            report(child['proof'],library) for child in result.get('children',[])])
    if result.get('schema')=='spatial-reduction/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        lines=['Масса по заданной плотности' if task['kind']=='solid_mass' else 'Интеграл по заданному телу']
        for child in result['children']:
            inner=child['proof']['task']
            lines.append('Пределы интегрирования от внешнего к внутреннему: '+', '.join(
                f"{b['lower']} ≤ {b['variable']} ≤ {b['upper']}" for b in inner['integration_order']))
            lines.append('Подынтегральная функция '+inner['integrand'])
        return '\n'.join(lines+['Значение '+pretty(result['value'])])
    if result.get('schema') in ('finite-interval-primitive/v1','continuous-riemann-limit/v1'):
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];p=lambda term:pretty(freeze(term))
        if result['schema']=='continuous-riemann-limit/v1':
            text=f'Шаг сетки {p(plan["mesh"])}, точка {p(plan["sample"])}. После подстановки исходное слагаемое равно шагу сетки, умноженному на {p(plan["integrand"])} в этой точке.'
            if plan['omitted_right_endpoint']:text+=' Вес пропущенного правого конца стремится к нулю.'
            return text+' Интеграл непрерывной функции по [0,1] даёт предел '+p(result['value'])+'.'
        if 'pulled_back_primitive' in plan:
            return 'В исходной переменной первообразная равна '+p(plan['pulled_back_primitive'])+'. Она непрерывна на всём промежутке. Разность значений на концах равна '+p(result['value'])+'.'
        text='Применяем формулу Ньютона–Лейбница на каждом участке постоянного знака.' if plan.get('pieces') else 'Вычисляем первообразную на исходном промежутке и подставляем концы.'
        return text+' Значение интеграла равно '+p(result['value'])+'.'
    if result.get('schema') in ('finite-product-limit/v1','finite-product-identity/v1',
                                'sequence-expression-limit/v1','sequence-expression-nonzero/v1'):
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];value=result['value'];schema=result['schema']
        if schema=='finite-product-identity/v1':
            return (f'Для граничной функции {plan["multiplier_wave"]} правило {plan["dilation_rule"]} даёт '
                    f'{pretty(freeze(plan["local_identity"][0]))} = {pretty(freeze(plan["local_identity"][1]))}. '
                    f'При добавлении следующего множителя величина {value["coefficient"]} · P остаётся равной '
                    f'{value["boundary"]}. Начальное значение произведения равно 1.')
        if schema=='finite-product-limit/v1':
            branches=value['branches']
            return '\n'.join([report(child['proof'],library) for child in result['children']]+[
                f'При {branches[0]["condition"]} каждый множитель равен 1. При {branches[1]["condition"]} '
                f'на хвосте можно разделить обе стороны тождества. Предел равен {pretty(freeze(branches[1]["value"]))}.'])
        if schema=='sequence-expression-limit/v1':
            if plan.get('argument'):
                return '\n'.join([*plan['argument'],'Предел равен '+pretty(freeze(value))+'.'])
            mesh=(f'Положим {plan["mesh_variable"]}=({plan["mesh_ratio"]})^{plan["variable"]}. '
                  'Эта величина положительна и стремится к нулю по неравенству Бернулли. '
                  if plan['strategy']=='geometric_mesh' else '')
            return mesh+'В исходной области получен предел '+pretty(freeze(value))+'.'
        if plan.get('strategy')=='nonzero_limit':
            return (report(result['children'][0]['proof'],library)+f' При L={plan["limit_expression"]} доказано L≠0. '
                    'При достаточно больших индексах |Dₙ−L|<|L|/2, следовательно |Dₙ|>|L|/2>0.')
        return f'Доказана ненулевость {plan["expression"]} на всей заявленной области.'
    if result.get('schema') in ('verified-interpolation/v1','bernstein-polynomials/v1',
                                'stirling-factorials/v1','product-approximation-proof/v1'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];v=result['value'];schema=result['schema']
        def describe(obj):
            if isinstance(obj,dict):return ', '.join(k+' = '+describe(z) for k,z in obj.items())
            if isinstance(obj,(list,tuple)):
                if obj and obj[0] in ('v','s','q','add','mul','div','pow','rpow','exp','ln','sin','cos','sqrt','pi'):
                    return pretty(freeze(obj))
                return '['+', '.join(map(describe,obj))+']'
            return str(obj)
        if schema=='verified-interpolation/v1':
            text='Точно проверены все исходные узлы. Коэффициенты по возрастанию степени '+describe(p['coefficients'])+'.'
        elif schema=='bernstein-polynomials/v1':
            text='Из исходного отрезка получена аффинная сетка. Использованы биномиальные веса порядка '+describe(p['degree'])+'.'
        elif schema=='stirling-factorials/v1':
            text='Точное сведение к факториалам выполнено. Проверены формула Стирлинга и направленные оценки логарифмического остатка.'
        else:text='\n'.join(p['steps'])
        return text+'\n'+describe(v)
    if result.get('schema')=='certified-root-iterations/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];roots=result['value']['roots']
        method={'newton':'методом Ньютона','false_position':'методом хорд','unspecified':'методом хорд'}[p['method']]
        cause={'sturm':'По знаковым вариациям последовательности Штурма',
               'global_monotonicity':'По строгой монотонности на всей прямой',
               'polynomial_dominates_bounded_remainder':'По оценке хвостов и знаку на всех участках оставшегося отрезка'}
        rows=[cause[p['global_root_coverage']['proof']]+f' доказано число корней {len(roots)}.']
        rows.extend(f'Корень {i+1} приближён {method}: {pretty(freeze(r["approximation"]))} '
                    f'с абсолютной погрешностью не больше {pretty(freeze(r["absolute_error"]))}.'
                    for i,r in enumerate(roots))
        return '\n'.join(rows)
    if result.get('schema')=='numeric-taylor-enclosure/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        plan=result['compilation'];value=result['value']
        steps=[f'{s["operation"]}: {s["terms"]} членов, остаток по модулю не больше {pretty(freeze(s["absolute_remainder"]))}'
               for s in plan['steps']]
        steps.append(f'Приближённое значение {pretty(freeze(value["approximate_value"]))}, '
                     f'полная абсолютная погрешность не больше {pretty(freeze(value["certified_absolute_error"]))}.')
        return '\n'.join(steps)
    if result.get('schema')=='isolated-real-roots/v1':
        v=result['value'];intervals=[pretty(freeze(a)) if a==b else '('+pretty(freeze(a))+', '+pretty(freeze(b))+')' for a,b in v['isolating_intervals']]
        return ('Число различных вещественных корней по теореме Штурма: '+str(v['distinct_real_roots'])+'. '+
                ('Изоляция каждого корня: '+', '.join(intervals)+'.' if intervals else ''))
    if result.get('schema')=='sequence-extremum/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];value=result['value'];ranges=value['all_attaining_indices']
        if not isinstance(ranges[0],(tuple,list)):ranges=[ranges]
        return ('Знаки изменения от индекса n к n+1 по всем участкам: '+str(p['integer_sign_runs'])+
                '. '+('Максимум' if value['extremum']=='maximum' else 'Минимум')+' равен '+pretty(freeze(value['value']))+
                '. Индексы достижения: '+', '.join(str(a)+('…'+str(b) if b!=a else '') for a,b in ranges)+'.')
    if result.get('schema') in ('sequence-tail-bounds/v1','sequence-range-and-tail/v1'):
        lines=[]
        if result['schema']=='sequence-range-and-tail/v1' and result.get('children'):
            lines.append(report(result['children'][0]['proof'],library))
        if result['status']!='SOLVED':
            return '\n'.join(lines+[result['status'],result.get('reason','Не доказаны все требуемые грани.')])
        plan=result['compilation'];values=result['value']
        if 'classes' in plan:
            if plan['period']==1:lines.append('Предел всей последовательности равен '+pretty(values['liminf'])+'.')
            else:
                for row in plan['classes']:
                    lines.append(f"На индексах от {row['first_index']} с шагом {plan['period']} предел равен {pretty(row['limit'])}.")
                lines.append(f"Нижний предел равен {pretty(values['liminf'])}, верхний — {pretty(values['limsup'])}.")
        else:
            period=result['children'][0]['proof']['compilation']['period']
            for branch in plan['monotone_classes']:
                for segment in branch['segments']:
                    a,b=segment['first_index'],segment['last_index']
                    va,vb=pretty(freeze(segment['first_value'])),pretty(freeze(segment['last_value']))
                    trend={-1:'убывают',0:'постоянны',1:'возрастают'}[segment['difference_sign']]
                    end=(f'до индекса {b}, где значение равно {vb}' if b is not None else f'на хвосте с пределом {vb}')
                    lines.append(f'С индекса {a} (значение {va}) члены с шагом {period} {trend} {end}.')
            lines.append(f"Нижняя грань всей последовательности равна {pretty(values['infimum'])}, верхняя — {pretty(values['supremum'])}.")
            for key,label in [('infimum','Нижняя'),('supremum','Верхняя')]:
                n=plan['attained_at'][key]
                lines.append(f'{label} грань впервые достигается при индексе {n}.' if n is not None else
                             f'{label} грань является предельным значением и не достигается.')
        return '\n'.join(lines)
    if result.get('schema')=='root-linearization/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];v=result['value']
        if 'geometric_factor' in p:
            return ('Пусть a>0, n≥1 — целое, yⁿ=aⁿ+x и y>0. Разность степеней раскладывается как x=(y−a)Sₙ. '
                    'При n=1 берём S₁=1. Умножение на y и прибавление aⁿ даёт Sₙ₊₁=ySₙ+aⁿ. '
                    'В частности Sₙ≥aⁿ⁻¹, поэтому |y−a|≤|x|/aⁿ⁻¹ и y→a. '
                    'По непрерывности полинома Sₙ→Sₙ(a,a)=naⁿ⁻¹. Следовательно, (y−a)/x→1/(naⁿ⁻¹) '
                    'и y=a+x/(naⁿ⁻¹)+o(x) при x→0 для фиксированных a,n.')
        if 'strict_comparison' in p:
            return ('При x>0 и a>0 имеем y=√(a²+x)>a и x=(y−a)(y+a). '
                    'Остаток a+x/(2a)−y=(y−a)²/(2a)=x²/[2a(y+a)²]. '
                    'Он строго положителен, а из y+a>2a следует r<x²/(8a³).')
        lines=[report(result['children'][0]['proof'],library),
               f"Для степени {task['degree']} исходное подкоренное число равно {p['center_radicand']} + ({p['increment']}). "
               f"В выбранном центре корень равен {p['center_root']}. Линеаризация даёт {pretty(v['linearized_value'])}."]
        if 'comparison' in v:
            lo,hi=v['comparison']['exact_value_interval'];err=v['comparison']['signed_approximation_error']
            lines.append(f"Проверка целых степеней заключает корень в [{pretty(lo)}, {pretty(hi)}], "
                         f"погрешность приближения — в [{pretty(err[0])}, {pretty(err[1])}].")
        return '\n'.join(lines)
    if result.get('schema')=='partial-sum-convergence/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Не удалось доказать критерий Коши.')
        plan=result['compilation'];n=plan['variable'];child=result['children'][0]['proof']
        waves=[f"|{w['function']}({w['phase']})| ≤ 1 при всех целых индексах от {w['valid_from']}." for w in plan.get('unit_waves',())]
        if 'later_index' not in plan:
            return '\n'.join([*waves,f"Разность двух частичных сумм содержит слагаемые начиная с {plan['first_tail_term']}.",
                              report(child,library),'Оценка равномерна по верхнему индексу. Последовательность сходится по критерию Коши.'])
        b=plan['later_index'];facts=child['compilation']['facts']
        return '\n'.join((*waves,f"Модуль слагаемого ограничен разностью соседних значений R(i) = {facts['potential']} с абсолютным весом |{facts['scalar']}|.",
                          f"Для любых двух верхних индексов {b} ≥ {n} ≥ 1 общие члены двух сумм сокращаются.",
                          'В хвосте разности складываются телескопически. Поскольку последняя величина неотрицательна,',
                          f"модуль разности сумм не превосходит {pretty(m.parse(plan['tail_bound'],n),n)}. Эта оценка не зависит от {b}.",
                          'Её предел равен нулю. Для каждого ε > 0 все достаточно поздние разности меньше ε по модулю.',
                          'По критерию Коши действительная последовательность сходится.'))
    if result.get('schema')=='sequence-term-at/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        original=task['sequence_task'];where=original.get('goal',original)
        assignments=[where['variable']+'='+str(task['index_value'])]
        assignments.extend(str(k)+'='+str(v) for k,v in task['parameter_values'].items())
        point=', '.join(assignments);value=result['value']
        if value['defined']:
            return f'При {point} исходное выражение определено. Его значение равно '+pretty(freeze(value['value']))+'.'
        return f'При {point} исходный делитель '+str(value['zero_divisor'])+' равен нулю. Значение выражения в этой точке не определено.'
    if result.get('schema')=='finite-sum-context/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Не завершена подстановка доказанных формул.')
        plan=result['compilation'];n=plan['variable']
        lines=[f'Для каждого целого {n} ≥ 1 установлены формулы вложенных сумм.']
        params=plan['rewritten_goal'].get('parameters',[])
        for item in plan['substitutions']:
            lines.append(item['sum']+' = '+pretty(m.parse(item['formula'],n,params),n)+'.')
        for child in result['children'][:-1]:
            if child['proof']['schema']=='contracting-expression-nonzero/v1':
                lines.append(report(child['proof'],library))
        if plan.get('domain_scope')=='eventually':
            lines.append('При фиксированных параметрах все исходные делители отличны от нуля для достаточно больших индексов.')
        else:lines.append('После подстановки проверены исходные знаменатели на всей области индекса.')
        lines.append(report(result['children'][-1]['proof'],library))
        return '\n'.join(lines)
    if result.get('schema') in ('contracting-integer-power-limit/v1','contracting-expression-nonzero/v1','contracting-power-expression-limit/v1'):
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];n=task['variable']
        if task['kind']=='contracting_integer_power_limit':
            p=task['base'];shift=task['offset'];exponent=n+(f'+{shift}' if shift else '')
            return (f'При {p}=0 каждая положительная степень равна нулю. При 0<|{p}|<1 положим d=1/|{p}|−1>0. '
                    f'По неравенству Бернулли |{p}|^({exponent}) ≤ 1/(1+({exponent})d) → 0.')
        def display(text):return pretty(m.parse(text,n,task['parameters']),n)
        if task['kind']=='contracting_expression_nonzero':
            sign='положителен' if plan['sign']>0 else 'отрицателен'
            if plan.get('strategy')=='nonzero_limit':
                limit=display(plan['limit_expression'])
                return (f'Для делителя {display(task["expression"])} проверка знака на всех индексах не дала доказательства. '
                        f'Его предел L = {limit} строго {sign}. Выбираем ε = |L|/2. По определению предела '
                        f'при всех {n} ≥ N делитель отличается от L меньше чем на ε, поэтому имеет тот же знак. '
                        'Для каждого набора фиксированных параметров существует своё такое N.')
            lines=[f'При каждом целом {n} ≥ 1 делитель {display(task["expression"])} строго {sign}.']
            for text,bound in plan['polynomial_bounds'].items():
                lines.append(f'Для {display(text)} отклонение от {bound["constant"]} по модулю меньше {bound["strict_error_bound"]}.')
            return '\n'.join(lines)
        lines=[report(c['proof'],library) for c in result['children'] if c['proof']['task']['kind']=='contracting_integer_power_limit']
        if any(c['role']=='nonzero limiting divisor' for c in result['children']):
            lines.append('Для каждого частного отдельно проверено, что предел знаменателя отличен от нуля.')
        return '\n'.join([*lines,'Предел равен '+pretty(freeze(result['value']),n)+'.'])
    if result.get('schema')=='finite-sum-bound/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Границы пока не доказаны.')
        facts=result['compilation']['facts'];value=result['value'];k=task['index']
        return '\n'.join([
            f'На целых {k} ≥ {facts["start"]} построена функция R({k}) = '+pretty(m.parse(facts['potential'],k),k)+'.',
            f'Модуль каждого слагаемого без внешнего множителя ограничен разностью R({k}) − R({k}+1).',
            'Проверены исходные делители и неотрицательность коэффициентов после переноса начала отсчёта.',
            'Сумма ограничивающих разностей равна R(первый индекс) − R(последний индекс + 1).',
            'С учётом внешнего множителя получено '+value['lower']+' ≤ S ≤ '+value['upper']+
            ' при целом '+task['variable']+' ≥ '+str(value['valid_from'])+'.'])
    if result.get('schema')=='finite-sum-formula/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Формула суммы пока не доказана.')
        identity=result['compilation'];k=identity['index'];n=identity['outer']
        if identity['construction']=='geometric_prefix_by_induction':
            p=identity['ratio'];s=pretty(m.parse(identity['prefix_formula'],n,task['parameters']),n)
            return (f'При |{p}|<1 величина 1−{p} положительна. Для пустой суммы формула даёт ноль. '
                    f'При увеличении верхней границы на единицу правая часть возрастает ровно на очередное слагаемое {p} в соответствующей степени. '
                    f'По индукции сумма равна {s} при всех целых {n} ≥ {identity["valid_from"]}.')
        def show(text,var):return pretty(m.parse(text,var),var)
        lines=[f'Ищем F({k}), для которой F({k}) − F({k}−1) равно слагаемому без общего множителя.',
               f'Получено F({k}) = '+show(identity['discrete_primitive'],k)+f'. Начальное значение F({identity["start"]-1}) = '+show(identity['initial_value'],k)+'.']
        if 'identity_task' in identity:lines.append('Доказана конечная формула '+identity['identity_task']['goal']['proposition']+'.')
        elif 'forward_potential' in identity:
            lines.append(f'Построена R({k}) = '+show(identity['forward_potential'],k)+f'. После проверки знаменателей исходное ядро равно R({k}) − R({k}+1).')
        else:lines.append('Подстановка коэффициентов в разность проверяет тождество при каждом целом индексе суммы.')
        lines.append('Сумма равна разности конечного и начального значений F с общим множителем '+show(identity['scalar'],n)+'.')
        for branch in result['value']['branches']:
            lines.append('Внешний индекс = '+branch['at_index']+'. Формула суммы: '+show(branch['expression'],n)+'.')
        return '\n'.join(lines)
    if result.get('schema')=='finite-sum-limit/v1':
        if result.get('compilation',{}).get('strategy')=='abstract_riemann_profile':
            return '\n'.join(result['compilation']['steps'])
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Предел пока не доказан.')
        names={'exact':'точная формула','bound':'оценка суммы','riemann':'интеграл по сетке'}
        states={'proved':'доказан','open':'остался открытым','not_tried':'не потребовался'}
        lines=['Рассмотренные ходы: '+', '.join(names[row['strategy']]+' ('+states[row['status']]+')' for row in result['search_attempts'])+'.',
               report(result['children'][0]['proof'],library)]
        plan=result['compilation'];n=plan['outer']
        labels={'all':'На натуральных индексах','even':'Для индекса 2j','odd':'Для индекса 2j+1',
                'lower':'Образ нижней границы','upper':'Образ верхней границы'}
        for branch in plan['endpoints']:
            variable='j' if branch['indices'] in ('even','odd') else n
            lines.append(labels[branch['indices']]+': '+pretty(m.parse(branch['expression'],n),variable)+' → '+pretty(branch['limit'],variable)+'.')
        if plan['strategy']=='bound':
            lines.append('Исходное выражение до внешнего модуля лежит между образами границ. Их общий предел даёт предел по теореме о сжатии.'
                         if plan['absolute'] else 'Исходное выражение лежит между образами границ. Их общий предел даёт предел по теореме о сжатии.')
        value=result['value']
        lines.append('Пределы подпоследовательностей различны.' if isinstance(value,dict) else 'Предел равен '+pretty(value,n)+'.')
        return '\n'.join(lines)
    if result.get('schema')=='relative-leading-term/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Главный член пока не установлен.')
        value=result['value']
        plan=result['compilation']
        if plan.get('theorem')=='method.affine_root_relative_magnitude':
            lines=list(plan['argument'])
            if value.get('printed_claim_holds') is False:
                lines.append('Для отрицательной величины сравнения вещественный главный член заданного вида отсутствует.')
            lines.append('Порядок относительно модуля равен '+pretty(value['order'])+
                         ', коэффициент равен '+pretty(value['coefficient'])+'.')
            return '\n'.join(lines)
        return (report(result['children'][0]['proof'],library)+'\nИсходная величина сравнения '+value['reference']+
                '. Порядок '+pretty(value['order'])+', коэффициент главного члена '+pretty(value['coefficient'])+'.')
    if result.get('schema')=='structured-limit/v1':
        plan=result.get('compilation',{})
        if 'growth_scale' in plan:
            p=plan['growth_scale'];c,(a,b,d)=p['steps'][-1][2:]
            return (f"Берём положительную величину y→∞. На исходной стороне получаем эквивалент "
                    f"{pretty(c)}·exp(({pretty(a)})·y)·y^({pretty(b)})·(ln y)^({pretty(d)}). "
                    f"Последовательно сравниваем показатели экспоненты, степени и логарифма. Предел равен {pretty(result['value'])}.")
        if 'analytic_reduction' in plan:
            from operations import leading
            proof=plan['analytic_reduction'];var=plan['scalar_task'].get('variable','x');value=result['value']
            if proof.get('argument'):
                return report({**result,'schema':'source-asymptotic-proof/v1','compilation':proof},library)
            if proof['theorem']=='method.logarithmic_monomial_phase':
                return ('На исходном положительном хвосте берём логарифм: '+pretty(proof['logarithmic_phase'],var)+
                        '. Порядок ведущего множителя '+str(list(proof['rate']))+', коэффициент '+
                        pretty(proof['coefficient'])+'. После экспоненцирования предел равен '+pretty(value)+'.')
            if proof['theorem']=='method.sine_power_common_increment':
                exponents=', '.join(pretty(e,var) for e in proof['exponents'])
                lines=['На каждой исходной стороне общая база положительна и стремится к единице через отличные от единицы значения.',
                       'Сокращаем общий малый множитель. Показатели '+exponents+'.']
            else:
                lines=['Разлагаем исходное выражение в малой координате отдельно на каждой допустимой стороне.']
                for case in proof.get('cases',[proof]):
                    if case.get('hypothesis'):
                        h=case['hypothesis'];lines.append(h['symbol']+(' = 0.' if h['relation']=='zero' else ' ≠ 0.'))
                    for row in case['sides']:
                        side={'left':'слева','right':'справа'}.get(row['side'],row['side'])
                        if 'jet' not in row:
                            lines.append('Подход '+side+' отсутствует в исходной области.');continue
                        power,coefficient=leading(freeze(row['jet']))
                        detail='Нулевое разложение' if coefficient is None else 'Ведущая степень '+str(power)+', коэффициент '+pretty(coefficient)
                        lines.append(detail+' при подходе '+side+'.')
            lines.append('Получаем '+(str(value) if isinstance(value,dict) else pretty(value,var))+'.')
            return '\n'.join(lines)
        if result['status']=='SOLVED':return report(result['children'][0]['proof'],library)
        return result['status']+'\n'+result.get('reason','Исходный предел пока не доказан.')
    if task.get('kind')=='cartesian_field_operator':
        if result['status']!='SOLVED':return result['status']
        from cartesian_fields import render_form
        return 'В декартовых координатах получаем '+render_form(result['value'])+'.'
    if result.get('schema')=='cartesian-flux/v1':
        if result['status']!='SOLVED':return result['status']+' '+result.get('reason','')
        v=result['value']
        if 'flux_formula' in v:return 'На противоположных гранях берём разность значений нормальной компоненты и умножаем на площадь грани. Поток равен '+v['flux_formula']+'.'
        if 'cartesian_integrand' in v:
            from cartesian_fields import render_form
            return 'По формуле Остроградского интегрируем по V дивергенцию '+render_form(v['cartesian_integrand'])+'.'
        p=result['compilation']
        s='Сумма трёх координатных производных равна '+pretty(p['divergence'])+'. По формуле Остроградского интегрируем её по V.'
        if 'flux' in v:
            if p['shape']=='lateral_cone':s+=' Замыкаем конус верхним диском и вычитаем поток через него.'
            s+=' Сверка с интегралом по ориентированной границе даёт поток '+pretty(v['flux'])+'.'
        return s
    if result.get('schema') in ('source-vector-calculus/v1','source-planar-composition/v1','source-geometric-application/v1'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from model import canonical
        return '\n'.join([*result['compilation']['argument'],canonical(result['value'])])
    if task.get('kind')=='formal_vector_identity':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','Обоснование пока не найдено.')
        from cartesian_fields import render_form
        value=next(n['value'] for n in result['proof']['nodes'] if n['goal'][0]=='cartesian_components')
        return '\n'.join((task.get('identity',task.get('claim',task.get('goal'))), 'В декартовых координатах раскрываем каждую сторону, применяя правило произведения к компонентам.',
                          'На общей области существования указанных компонентных производных обе стороны дают '+render_form(value)+'.',
                          'Порядок смешанных производных сохраняется, если требуемая непрерывная дифференцируемость явно не задана.'))
    if task.get('kind',task.get('task_type'))=='prove_equality' or (result.get('goal') or [None])[0]=='real_equal':
        return equality_report(result,library)
    if (result.get('goal') or [None])[0]=='bounded_on' or task.get('kind')=='prove_boundedness':
        if result['status']!='SOLVED':return result['status']+'\n'+(result.get('reason') or 'Доказательство ограниченности пока не найдено.')
        ctx=result['context'];end=ctx['ray_endpoint']
        ray='['+end+', +∞)' if ctx['ray_side']=='right' else '(−∞, '+end+']'
        symbol=result['goal'][1][1]
        lines=['Докажем ограниченность функции '+symbol+' на '+ray+'.']
        for node in result['proof']['nodes']:
            reason=library.by_id[node['rule']]['label'].replace('f(x)',symbol+'(x)').replace('|f|','|'+symbol+'|')
            lines.append(reason.rstrip('.')+'.')
        return '\n'.join(lines)
    if result.get('schema')=='global-chain-search-run/v1' and (result.get('goal') or [None])[0]=='parameter_series_sets':
        if result['status']!='SOLVED':return result['status']
        answer=result['value']
        return ('На области '+(', '.join(answer['source_domain']) or 'всех действительных параметров')+
                ' ряд сходится абсолютно при '+answer['absolute_convergence_set']+
                '. Множество условной сходимости: '+answer['conditional_convergence_set']+
                '. Проверены геометрический множитель, порядок рационального коэффициента и обе границы |B|=1.')
    if result.get('schema')=='global-chain-search-run/v1' and (result.get('goal') or [None])[0] in ('series_classification','cauchy_series_classification'):
        if result['status']!='SOLVED':return result['status']
        answer=result['value']
        if answer.get('criterion')=='power_progression_thresholds':
            nodes=result['proof']['nodes']
            c,phase,a,b,first,s=next(n['value'] for n in nodes if n['goal'][0]=='progression_weight')
            explanation=f"Исходное основание равно {pretty(a)}·{task['index']}+({pretty(b)}), с первого индекса положительно и растёт."
            if freeze(c)==m.ZERO:explanation+=' Множитель равен нулю на всей исходной области.'
            else:
                explanation+=f' Модуль сравним с {task["index"]} в степени −({pretty(s)}), поскольку предел отношения равен |{pretty(c)}|·({pretty(a)})^(−({pretty(s)})) > 0.'
                explanation+=(' Знаки чередуются. При положительном показателе убывающая амплитуда стремится к нулю. При неположительном общий член не стремится к нулю.' if phase else ' Знак постоянен, поэтому обычная сходимость равносильна абсолютной.')
            subset=', '.join(answer['domain_conditions']) or 'все исходные действительные параметры'
            def cells(s):return ('да' if s else 'нет') if isinstance(s,bool) else s.replace('empty','∅').replace('all','вся область').replace(' and ',' и ')
            return explanation+' Область — '+subset+'. Абсолютная сходимость — '+cells(answer['absolute_convergence'])+'. Условная — '+cells(answer['conditional_convergence'])+'. Расходимость — '+cells(answer['divergence'])+'.'
        proof=result['proof'];root=next(n for n in proof['nodes'] if n['id']==proof['root'])
        c,d,r,start=root['steps'][0]['value']
        lines=[f'При n ≥ {start} модуль члена не превосходит {pretty(c)} · n^({d}) · ({pretty(r)})^n. Каждый предшествующий член определён.']
        if root['rule']=='series_envelope.cauchy':
            mode,factor,rate,first=root['steps'][1]['outputs']
            tail=(pretty(factor)+' · ('+pretty(rate)+')^m' if mode=='geometric_tail' else pretty(factor)+'/(m−1)')
            lines.append(f'При l ≥ m ≥ {first} сумма модулей с m по l ограничена величиной {tail}, которая стремится к нулю. Выполнен критерий Коши.')
        elif freeze(r)==m.ONE:
            lines.append('Мажоранта ограничена константой, умноженной на 1/n².')
        else:
            lines.append('У ненулевой мажоранты отношение соседних членов стремится к основанию, меньшему единицы. Нулевая мажоранта даёт нулевой хвост.')
        return ' '.join(lines+['Ряд сходится абсолютно.'])
    if result.get('schema')=='comparison-rule-dag/v1':
        from ray_proofs import comparison_report
        return comparison_report(result,library)
    if task.get('kind',task.get('task_type')) in ('proof_about_real_functions','prove_continuity') and result.get('schema')!='printed-inequality/v1':
        if result.get('status')!='SOLVED':return result['status']+'\n'+result.get('reason','')
        ctx=result['context'];declared=', '.join(ctx['functions'])
        lines=['Пусть D — произвольное подмножество ℝ.']
        interval=ctx.get('interval_endpoints')
        if interval:
            left,right=map(str,interval)
            lines=[f'Рассмотрим замкнутый отрезок D=[{left},{right}], где {left}≤{right}.']
        if declared:lines.append('На D заданы действительные функции '+declared+'.')
        from operations import WINDOW_SIDES
        def display(term):
            if not isinstance(term,(tuple,list)):return term
            op,*args=term
            if op=='function':return ('s',args[0])
            if op in WINDOW_SIDES:
                side,extremum=op.split('_')
                bounds=f'[{left},ξ]' if side=='prefix' else f'[ξ,{right}]'
                return ('s',f'{extremum} на {bounds} от {formula(args[0])}')
            return (op,*(display(a) for a in args))
        def formula(term):return m.render(display(term))
        for node in result['proof']['nodes']:
            goal=node['goal']
            if goal[0]=='continuous_on':
                term=formula(goal[1]);reason=library.by_id[node['rule']]['label'].rstrip('.')
                if node['rule'] in ('continuous.min','continuous.max'):
                    equivalent=next(step['ask'][1] for step in node['steps'] if 'ask' in step)
                    lines.append(term+' = '+formula(equivalent)+'.')
                lines.append(term+' непрерывна на D. '+reason+'.')
            elif goal[0]=='attains_on_subintervals':
                lines.append(f'На каждом непустом замкнутом подотрезке D функция {formula(goal[1])} достигает конечных минимума и максимума.')
            elif goal[0]=='window_projection':
                clip='min(u,ξ)' if goal[1]=='prefix' else 'max(u,η)'
                lines.append(f'Пусть ξ≤η. Точка u большего подотрезка имеет в меньшем проекцию {clip} на расстоянии ≤η−ξ. Общие точки остаются на месте.')
            elif goal[0]=='oscillation_majorant':
                inner=formula(node['value'])
                lines.append(f'Для {formula(goal[1])} разность значений по модулю не превосходит модуля непрерывности {inner} при h=|η−ξ|. '
                             'Действительно, значение в точке экстремума и значение в её проекции отличаются не более чем на наибольшее колебание функции на расстоянии h. Сравнение в обоих направлениях даёт оценку.')
            elif goal[0]=='uniform_on':
                lines.append(formula(goal[1])+' равномерно непрерывна на D. '+library.by_id[node['rule']]['label'].rstrip('.')+'.')
        return '\n'.join(lines)
    if result.get('schema')=='substitution-validity/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];geo=plan['geometry'];v=plan['variable'];t=plan['new_variable']
        lines=[t+' = '+pretty(geo['forward'],v)+'. Исходная подынтегральная функция непрерывна на всём отрезке.']
        for point,kind in geo['cuts']:
            reason='замена имеет полюс' if kind=='pole' else 'меняется направление монотонности'
            lines.append('При '+v+' = '+pretty(point)+' '+reason+'.')
        def route(bounds):return ' → '.join(map(pretty,bounds))
        for branch in geo['branches']:
            lines.append(v+' проходит '+route(branch['source_bounds'])+', '+t+' проходит '+route(branch['image_bounds'])+
                         '. На этой ветви '+v+' = '+pretty(branch['inverse'],t)+', подынтегральное выражение равно '+
                         pretty(branch['integrand'],t)+' d'+t+'.')
        lines.append('Требуется сложить интегралы по указанным ветвям.' if geo['cuts'] else 'Достаточно одной обратной ветви.')
        lines.append('Односторонние пределы на границах существуют по непрерывности исходной функции и равенству интегралов на усечённых отрезках.')
        return '\n'.join(lines)
    if result.get('schema')=='global-chain-search-run/v1' and task.get('kind',task.get('task_type')) in ('proof','prove'):
        from finite_sums import proof_text
        return proof_text(result,pretty)
    if result.get('schema')=='continuous-least-squares/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from quadrature import continuous_projection_report
        return continuous_projection_report(result,pretty)
    if result.get('schema')=='source-global-extrema/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from level_sets import source_global_extrema_report
        return source_global_extrema_report(result,pretty)
    if result.get('schema') in ('source-parameter-integral/v1','improper-space-integral/v1'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from quadrature import parameter_certificate_report
        return parameter_certificate_report(result,pretty)
    if result.get('schema')=='multivariate-operator-proof/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from cartesian_fields import multivariate_operator_report
        return multivariate_operator_report(result,pretty)
    if result.get('schema')=='local-geometry/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        if result['compilation']['method'] in ('printed_taylor','field_weighted_shifts') and 'leading_degree' not in result['value']:
            return report(result['children'][0]['proof'],library)
        from cartesian_fields import local_geometry_report
        return local_geometry_report(result,pretty)
    if result.get('schema')=='multivariate-taylor/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        v=result['value'];lines=['Разложение '+task['expression']+' по приращениям '+', '.join(task['increments'])]
        lines.extend('Степень '+str(k)+': '+pretty(e) for k,e in enumerate(v['homogeneous_terms']) if freeze(e)!=m.ZERO)
        lines.extend('Производная в центре по '+', '.join(path)+': '+pretty(e) for path,e in zip(task.get('requested_partials',[]),v.get('specified_derivatives_at_center',[])))
        lines.append('Остаток тождественно равен нулю.' if v['remainder']=='identically_zero' else 'Остаток o(||Δ||^'+str(v['degree'])+').')
        return '\n'.join(lines)
    if result.get('schema') in ('pointwise-modulus/v1','neighborhood-quantifiers/v1'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];answer=result['value']
        if 'estimate' in p:
            bound=p['estimate'];a=p['center'];eps=p['epsilon']
            return (f'Пусть {a} и x лежат в области исходной функции. При |x−{a}| < 1 разность значений по модулю не превосходит '
                    +pretty(bound['constant'])+f' · |x−{a}|^('+pretty(bound['exponent'])+f'). Для каждого {eps} > 0 берём δ = '
                    +pretty(answer['delta'])+f'. Тогда при |x−{a}| < δ отклонение меньше {eps}.')
        if p['transition']=='cofinal_tolerances':
            c=pretty(p['numerator']);b=pretty(p['base'])
            return f'Для любого ε > 0 выбираем натуральное n > {c}/(ε·({b}−1)). По неравенству Бернулли {b}ⁿ ≥ 1+n·({b}−1), поэтому {c}/{b}ⁿ < ε. Радиус, данный для этого члена, годится для ε. Функция непрерывна в исходной точке.'
        if p['transition']=='positive_tolerance_floor':
            lower='минимуму семейства (для пустого берём 1)' if isinstance(p['lower'],str) else pretty(p['lower'])
            return f'Положим L равным {lower}. При t ≤ 0 зададим f(t)=0, при t > 0 — f(t)=L/2. В нуле любое из заданных ε больше скачка. Однако f(1/n)=L/2 для всех n, поэтому для ε=L/4 подходящего радиуса нет.'
        if p['transition']=='affine_floor_jumps':
            slope=pretty(p['slope']);jump=pretty(p['jump'])
            return (f'При расстоянии меньше 1 целые части аргументов различаются не более чем на 1. Для ε > {jump} подходит '
                    +f'δ = min(1,(ε−{jump})/({slope})). У целого k берём y=k−1/n, n≥2. Тогда f(k)−f(y) = {jump} + ({slope})/n. '
                    +'Это опровергает оценку и при равенстве ε величине скачка. Между соседними целыми функция аффинна. Разрывы составляют все целые точки.')
        descriptions={'continuity':'При любом желаемом отклонении можно сузить окрестность аргумента. Достаточно сколь угодно малых положительных допусков.',
            'locally_bounded_image':'Образ некоторой окрестности ограничен. Из условия достаточно взять один радиус, а в обратную сторону одна граница значений подходит для всех меньших радиусов.',
            'bounded_image_of_each_centered_ball':'Образ каждого конечного шара с центром в данной точке ограничен.',
            'bounded_preimage_of_some_output_ball':'Прообраз некоторой окрестности значения ограничен. Тот же радиус аргумента подходит для меньших окрестностей значения.',
            'bounded_preimage_of_each_centered_output_ball':'Прообраз каждого шара вокруг значения функции в данной точке ограничен.',
            'positive_image_separation_outside_each_input_ball':'Вне любой окрестности точки значения отделены от её значения положительным расстоянием. Это контрапозиция данного включения шаров.'}
        lines=[descriptions[answer['equivalent_property']]]
        if 'witness' in p:
            w=p['witness'];s=pretty(w['slope']);j=pretty(w['jump'])
            lines.append(f'В точке 0 рассмотрим f(t)={s}·t при t≤0 и f(t)={s}·t+{j} при t>0. '
                         +f'При r=|t| имеем {pretty(w["lower_absolute"])} ≤ |f(t)| ≤ {pretty(w["upper_absolute"])}. '
                         +f'Для заданного радиуса r берём {pretty(p["chosen_radius"])}. Между тем f(1/n) → {j}, а f(0)=0.')
        if 'example' in p:
            e=p['example'];lines.append('В печатном примере ветви лежат по разные стороны от '+pretty(e['separator'])+
                '. Обратные на образах равны tan(y) и '+pretty(e['upper_inverse'])+
                '. Внутри каждой из двух открытых полос обратная непрерывна. Рациональные и иррациональные аргументы плотны, а пределы ветвей в каждой точке различны.')
        return '\n'.join(lines)
    if result.get('schema')=='fourier-expansion/v1' and result.get('value') is not None:
        v=result['value'];p=result['compilation'];fmt=lambda e:pretty(freeze(e),'x')
        lines=['Период '+fmt(v['period'])+'. Частота '+fmt(v['angular_frequency'])+' при целом n ≥ 1.']
        for key,c in v['coefficients'].items():
            terms=[fmt(c['fixed'])] if freeze(c['fixed'])!=m.ZERO or not c['conditional'] else []
            for branch in c['conditional']:
                terms.append('('+fmt(branch['then'])+' при '+fmt(branch['if_zero'])+' = 0, иначе '+fmt(branch['otherwise'])+')')
            lines.append({'mean':'Постоянный член','cos':'Коэффициент косинуса','sin':'Коэффициент синуса'}[key]+' = '+' + '.join(terms)+'.')
        lines.append('Внутри гладких частей ряд сходится к исходной функции. В точках стыка его сумма равна полусумме односторонних пределов: '+
                     ', '.join(fmt(a)+' ↦ '+fmt(b) for a,b in v['junction_values'])+'.')
        for s,y in v.get('numeric_series_sums',{}).items():
            lines.append('Подстановка в ряд с общим порядком частичных сумм даёт '+s+' = '+fmt(y)+'.')
        return '\n'.join(lines)
    if result.get('schema')=='complex-series-disk/v1' and result.get('value') is not None:
        v=result['value'];p=result['compilation'];a,b=[m.render(freeze(c)) for c in v['center']]
        radius='∞' if v['radius']=='+inf' else m.render(freeze(v['radius']))
        return '\n'.join(['Для каждого множителя вычислено отношение квадратов модулей соседних коэффициентов.',
                          'После умножения его асимптотика равна '+m.render(freeze(p['leading_squared']))+' · n^'+str(p['squared_ratio_degree'])+'.',
                          'Центр ('+a+', '+b+'), радиус '+radius+'.',
                          {'center_only':'Ряд сходится только в центре.','whole_plane':'Ряд сходится на всей комплексной плоскости.',
                           'open_disk':'Внутри круга ряд сходится абсолютно, а вне замкнутого круга расходится.'}[v['disk']]])
    if result.get('schema')=='functional-characterization/v1' and result.get('value') is not None:
        return '\n'.join([*result['compilation']['steps'],'Все решения: '+', '.join(result['value']['solutions'])+'.',
                          'Параметры: '+result['value']['parameter_domain']+'.'])
    if result.get('schema')=='uniform-continuity/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        lines=[];answers=result['value']
        for interval,answer in zip(result['compilation']['intervals'],answers if isinstance(answers,list) else [answers]):
            lines.append('На промежутке '+interval['domain']+' проверена исходная область функции.')
            if 'estimate' in interval:
                bound=interval['estimate']
                lines.append('Разность значений по модулю не превосходит '+pretty(bound['constant'])+' · |u−v|^('+pretty(bound['exponent'])+').')
            elif 'finite_extensions' in interval:lines.append('Конечные значения на концах дают непрерывное продолжение на компактный отрезок.')
            elif 'divergent_limit' in interval:lines.append('При приближении к конечному концу значения не имеют конечного предела. Равномерная непрерывность потребовала бы такого предела.')
            elif 'sequences' in interval:
                witness=interval['sequences'];index='j'
                while index in task.get('parameters',[]):index+="'"
                u,v=(pretty(e,index) for e in witness['points'])
                lines.append(f'При целых {index} → ∞ берём u = {u} и v = {v}. Тогда |v−u| → 0, а f(v)−f(u) → '+pretty(witness['value_difference_limit'])+'.')
            if 'sufficient_delta_for_each_positive_epsilon' in answer:
                tolerance=answer['sufficient_delta_for_each_positive_epsilon'];eps=tolerance['variable']
                lines.append(f'Для каждого {eps} > 0 подходит δ = '+pretty(tolerance['delta'])+'.')
            if 'continuity' in answer:lines.append('Функция непрерывна.')
            if 'boundedness' in answer:lines.append('Функция ограничена.')
            if 'unboundedness' in answer:lines.append('Функция неограниченна.')
            if 'uniform_continuity' in answer:
                lines.append('Функция равномерно непрерывна.' if answer['uniform_continuity'] else 'Равномерная непрерывность отсутствует.')
        return '\n'.join(lines+[report(c['proof'],library) for c in result['children']])
    if result.get('schema')=='linear-approximation/v1':
        if not result.get('value'):return result.get('reason',result['status'])
        p=result['compilation']
        head='Для кругового сектора S=R²α/2, угол в радианах.' if 'sector_formula' in p else 'Выбираем центр '+pretty(p['center'])+' и вычисляем линейное приближение в заданной точке.'
        return head+'\n'+report(result['children'][0]['proof'],library)
    if result.get('schema')=='function-increment/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];value=result['value']
        if 'derivative' in p:lines=['Вычисляем производную в точке '+pretty(p['point'])+'.']
        else:lines=['В начальной точке значение равно '+pretty(p['value_before'])+', в конечной — '+pretty(p['value_after'])+'.']
        if p['natural_parameter_guards']:
            from tasks import guard_source
            lines.append('Из исходной формулы следуют условия '+', '.join(guard_source(g) for g in p['natural_parameter_guards'])+'.')
        labels={'argument_increment':'Приращение аргумента','function_increment':'Приращение функции','tangent_slope':'Угловой коэффициент касательной',
                'secant_slope':'Угловой коэффициент секущей','instantaneous_velocity':'Мгновенная скорость','mean_velocity':'Средняя скорость',
                'instantaneous_stretch_factor':'Коэффициент растяжения в точке','mean_stretch_factor':'Средний коэффициент растяжения','numerical_value':'Численное значение'}
        labels.update(differential='Дифференциал',linearized_value='Приближённое значение')
        for k,v in value.items():
            if k=='comparison':lines.append('Сравнение даёт Δf '+v['relation']+' df. Разность Δf − df = '+pretty(v['exact_minus_differential'])+'.')
            else:lines.append(labels[k]+' = '+pretty(v))
        return '\n'.join(lines)
    if result.get('schema')=='euler-integral/v1' or 'euler_reduction' in (result.get('compilation') or {}):
        if result.get('status')!='SOLVED':return result.get('reason',result['status'])
        from tasks import guard_source
        p=result['compilation'].get('euler_reduction',result['compilation']);value=result['value']
        change=p['substitution'];arg=list(map(pretty,p['shape']));params=list(map(pretty,p['kernel_parameters']))
        variable=task.get('variable','x')
        if change=='positive_binomial_odds':
            _,n,A,B,_=params;substitution=f's = ({B})/({A}) · {variable}^({n}), t = s/(1+s)'
        elif change=='finite_power_fraction':
            upper=task['limits'].split('..')[1] if 'limits' in task else task['upper']
            substitution=f't = ({variable}/({upper}))^({params[1]})'
        elif change=='scaled_power_gamma':substitution=f't = ({params[1]}) · {variable}^({params[0]})'
        elif change=='negative_logarithm':substitution=f't = −ln({variable})'
        else:substitution=f't = sin²({variable})'
        lines=['На открытом промежутке положим '+substitution+'.']
        if p['original_parameter_domain']:lines.append('Исходные ограничения выражения: '+', '.join(map(guard_source,p['original_parameter_domain']))+'.')
        if change in ('scaled_power_gamma','positive_binomial_odds'):
            lines.append('При отрицательной степени концы меняются местами, поэтому множитель в якобиане содержит модуль степени.')
        family=('B' if p['kernel']=='beta' else 'Γ')+'('+', '.join(arg)+')'
        lines.append('Для сходимости эйлерова интеграла требуются '+', '.join(map(guard_source,p['endpoint_conditions']))+'.')
        if p.get('logarithmic_order'):
            lines.append('Дифференцируем по показателю степени. Внутри строгой области сходимости соседние показатели дают интегрируемые мажоранты у обоих концов, включая логарифмические множители.')
        if value.get('converges') is False or value.get('convergence')=='divergent':
            lines.append('Одно из необходимых условий нарушено. Исходный интеграл расходится.')
        elif 'euler_reduction' in result['compilation']:lines.extend(['Эйлеров множитель имеет вид '+family+'.','Значение интеграла равно '+pretty(value['value'])+'.'])
        else:
            if not p.get('logarithmic_order'):lines.append('После подстановки получаем ('+pretty(value['factor'])+') · '+family+'.')
            special=value['special_value']
            if special and 'half_integer_gamma' in special:
                n=special['half_integer_gamma'];lines.append('По рекурсии гамма-функции результат равен ('+pretty(value['factor'])+f') · √π · (2{n})!/(4^{n} · {n}!).')
            elif special:
                terms=[f'({pretty(c)}) · Γ^({i})({arg[0]})' for i,c in enumerate(special['gamma_derivative_terms'])]
                lines.append('После дифференцирования получаем '+' + '.join(terms)+'.')
            if value['closed_value'] is not None:
                if p['kernel']=='beta':lines.append('Используем B(p,q) = Γ(p)Γ(q)/Γ(p+q), рекурсию и формулу отражения при дополнительных аргументах.')
                lines.append('Значение интеграла равно '+pretty(value['closed_value'])+'.')
            if value['conditions']:lines.append('Область сходимости при исходных ограничениях задаётся условиями '+', '.join(map(guard_source,value['conditions']))+'.')
        return '\n'.join(lines)
    if result.get('value') is not None and (result.get('schema')=='source-endpoint-limit/v1' or
            result.get('schema')=='improper-integral/v1' and result['compilation'].get('theorem')=='method.reciprocal_log_moment'):
        from quadrature import endpoint_estimate_report
        return endpoint_estimate_report(result,pretty)
    if result.get('schema')=='source-endpoint-limit/v1':return result.get('reason',result['status'])
    if result.get('schema')=='improper-integral/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];value=result['value'];lines=[]
        if 'ordinary_if' in value:
            lines.extend(p['steps'])
            for label,key in (('Обычная','ordinary_if'),('Абсолютная','absolute_if'),('Условная','conditional_if')):
                condition=value[key]
                text='всегда' if condition is True else 'никогда' if condition is False else str(condition)
                lines.append(label+' сходимость — '+text+'.')
            return '\n'.join(lines)
        if p.get('theorem')=='method.logarithmic_pole_traces':
            return '\n'.join((*p['argument'],str(value)))
        if p.get('theorem')=='method.separate_symbolic_improper_orders':
            return '\n'.join((*p['argument'],'Условия сходимости — '+' и '.join(value['if_and_only_if'])+'.'))
        if p.get('theorem')=='method.indexed_euler_integrals':
            return 'Конечная сумма Эйлера продолжается через изолированные нули знаменателя. Интегрируем каждую экспоненту между исходными концами. При нулевой частоте её вклад равен длине интервала.'
        if p.get('theorem')=='method.improper_harmonic_moments':
            return 'Каждая экспоненциально-полиномиальная мода абсолютно интегрируема по причине строгого затухания. Её первообразная исчезает на бесконечности. Значение интеграла равно '+pretty(value['value'])+'.'
        if 'absolute_majorant' in p:
            return 'На всём открытом промежутке аргумент определён. Модуль не превосходит 1, поэтому интеграл по промежутку конечной длины сходится абсолютно.'
        if 'endpoint_scales' in p or 'periodic_function' in p:
            def condition(c):
                if c is True:return 'всегда'
                if c is False:return 'никогда'
                if 'all' in c:return ' и '.join(condition(v) for v in c['all'])
                expr=pretty(c['expression'])
                text=expr+' '+c['relation']+' 0'
                if 'when_equal' in c:text+=' или ('+expr+' = 0 и '+condition(c['when_equal'])+')'
                return text
            if 'periodic_function' in p:
                lines.append('Используем фазу u = '+pretty(p['phase'],task['variable'])+'. При бесконечном u амплитуда сравнима с u^('+pretty(p['tail_power'])+')·(ln u)^('+pretty(p['tail_log_power'])+').')
                lines.append('На одинаковых участках каждого периода модуль синуса или косинуса отделён от нуля. Сравнение по этим участкам даёт условие абсолютной сходимости.')
                if p['periodic_power']%2:lines.append('У нечётной степени среднее за период равно нулю. Если амплитуда убывает к нулю, применяем признак Дирихле.')
                else:lines.append('Чётная степень сохраняет знак на всём промежутке.')
                for case in value['cases']:
                    label='Частота равна нулю. ' if case['frequency_zero'] else 'Частота отлична от нуля. '
                    lines.append(label+'Обычная сходимость — '+condition(case['ordinary'])+'. Абсолютная — '+condition(case['absolute'])+'. Условная — '+condition(case['conditional'])+'.')
                return '\n'.join(lines)
            for row in p['endpoint_scales']:
                at=pretty(row['endpoint']);left,right=map(pretty,row['interval'])
                factors=[base if freeze(p)==m.ONE else base+'^('+pretty(p)+')' for base,p in
                         zip(('exp(t)','t','|ln t|','|ln|ln t||'),row['profile']) if freeze(p)!=m.ZERO]
                lines.append('На ('+left+', '+right+') у конца '+at+' модуль выражения сравним с '+('·'.join(factors) or '1')+'.')
                lines.append('Здесь t '+('стремится к +∞.' if row['endpoint']=='+inf' else 'обозначает расстояние до конца.'))
                lines.append('Условие сходимости в этом конце — '+condition(row['condition'])+'.')
            lines.append('Для исходного интеграла все полученные условия должны выполняться одновременно.')
            return '\n'.join(lines)
        if 'principal_value_exists' in value:
            lines.append('Берём равные отсечения с обеих сторон каждой внутренней особой точки. Разные точки рассматриваем независимо.')
            for piece in p['symmetric_pairs_and_regular_pieces']:
                center=piece['reflection_center'];ends=pretty(piece['lower'])+' < t < '+pretty(piece['upper'])
                if center is None:lines.append('На промежутке '+ends+' сохраняем исходный интеграл.')
                else:lines.append('При отражении относительно '+pretty(center)+' сумма двух подынтегральных выражений равна '+pretty(piece['integrand'])+' для '+ends+'.')
            lines.append('Главное значение Коши равно '+pretty(value['principal_value'])+'.' if value['principal_value_exists']
                         else 'Хотя бы один из независимых пределов расходится. Конечного главного значения Коши нет.')
            return '\n'.join(lines)
        if 'primitive' in p:lines.append('Первообразная F = '+pretty(p['primitive']))
        for item in p.get('endpoint_comparisons',[]):
            end=pretty(item['point'])
            if 'power' in item:lines.append('У конца '+end+' сравним модуль с t^('+pretty(item['power'])+')·|ln t|^('+pretty(item['log_power'])+') при t → 0+.')
            else:lines.append('У конца '+end+' подынтегральная функция непрерывна.')
        for item in p.get('one_sided_evaluations',[]):
            left,right=item['primitive_limits']
            lines.append('На ('+pretty(item['lower'])+', '+pretty(item['upper'])+') пределы F равны '+pretty(left)+' и '+pretty(right)+'.')
        lines.append('Интеграл сходится.' if value['convergence']=='convergent' else 'Несобственный интеграл расходится.')
        if 'value' in value:lines.append('Значение интеграла = '+pretty(value['value']))
        return '\n'.join(lines)
    if result.get('schema')=='formal-composition/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];args='('+', '.join(pretty(a) for a in p['outer_evaluation_arguments'])+')';outer=p['outer_symbol']
        lines=['Пусть '+outer+' дважды дифференцируема в точке '+args+'.']
        if p['original_inner_domain']:
            from tasks import guard_source
            lines.append('Для внутренних аргументов требуется '+', '.join(guard_source(g) for g in p['original_inner_domain'])+'.')
        lines.append('Используем проверенные первые и вторые производные внутренних аргументов. Индексы внешней функции перечислены в порядке дифференцирования.')
        for label,terms in result['value'].items():
            parts=['('+pretty(t['coefficient'])+') · '+outer+'_'+','.join(str(i) for i in t['ordered_outer_partials'])+args for t in terms]
            lines.append(label+' = '+(' + '.join(parts) or '0'))
        return '\n'.join(lines)
    if result.get('schema')=='sampled-field-taylor/v1':
        v=result.get('value')
        if v is None:return result['status']+'\n'+result.get('reason','')
        field=v['field'];coords=v['variables'];lines=['Разложение линейной комбинации значений поля '+field+' по приращениям '+', '.join(v['increments'])+'.']
        if 'terms' in v:
            def partial(alpha):
                label=''.join(x+('^'+str(i) if i>1 else '') for x,i in zip(coords,alpha) if i)
                return field+'_{'+label+'}' if label else field
            lines.append(' + '.join('('+pretty(t['coefficient'])+')·'+partial(t['orders']) for t in v['terms']) or '0')
            lines.append('При непрерывных производных до порядка '+str(v['degree'])+' в окрестности центра остаток равен o(‖Δ‖^'+str(v['degree'])+').')
        elif 'circle_series' in v:
            lines.append('Коэффициент при r^(2j) равен Δ^j '+field+' / (4^j (j!)²), j ≥ 0. Коэффициенты нечётных степеней равны нулю. Здесь Δ обозначает лапласиан.')
        elif 'diagonal_support_weights' in v:
            lines.append('Для каждого мультииндекса α коэффициент равен D^α '+field+' / α!, умноженному на вес множества координат с αᵢ > 0.')
            for g in v['diagonal_support_weights']:lines.append('{'+', '.join(g['positive_coordinates'])+'} → '+pretty(g['weight']))
            lines.append('Остальные веса равны нулю.')
        elif v['coefficient_kernel']['method']=='weighted_products':
            lines.append('Коэффициент при D^α '+field+' равен Σⱼ wⱼ (δⱼ)^α / α!. Пары веса и вектора смещения даны ниже.')
            for w,d in v['coefficient_kernel']['nodes']:lines.append(pretty(w)+' · ('+', '.join(map(pretty,d))+')')
        else:
            period=v['coefficient_kernel']['frequency_multiple']
            lines.append('При α=(p,q) нечётный q даёт нулевой коэффициент. Для чётного q он равен r^(p+q)(−1)^(q/2)/(2^(p+q) p! q!), умноженному на сумму (−1)^j C(p,i) C(q,j) по 0≤i≤p и 0≤j≤q, для которых p+q−2i−2j кратно '+str(period)+'.')
        if 'convergence' in v:lines.append('При гладкости формула задаёт коэффициенты каждого конечного порядка. При аналитичности в окрестности центра ряд сходится к исходному выражению для достаточно малых приращений.')
        return '\n'.join(lines)
    if result.get('schema')=='series-numeric-bounds/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];values=result['value'] if isinstance(result['value'],list) else [result['value']]
        return '\n'.join([f"В разложении берём {p['terms']} членов."]+
                         ['Приближение '+pretty(v['approximation'])+', гарантированная ошибка не превосходит '+
                          pretty(v['certified_remainder'])+'.' for v in values])
    if result.get('schema') in ('termwise-integral/v1','power-series-quadrature/v1'):
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];v=result['value']
        if 'integrated_terms' in p:
            return f"Разложение {p['basis']} применяется с границей аргумента {pretty(p['argument_bound'])}. Слагаемые интегрируются по одному с сохранением концов. Взято {v['terms']} членов, приближение {pretty(v['approximation'])}, гарантированная ошибка не превосходит {pretty(v['certified_remainder'])}."
        return 'Раскрываем '+p['kernel']+' ряд под интегралом. Интегралы модулей членов мажорируются сходящимся рядом порядка '+str(p['decay_order'])+'. Сумма интегралов равна '+pretty(v)+'.'
    if result.get('schema')=='telescoping-series/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];n=task['index']
        if p.get('theorem')=='method.generating_series_operators':
            v=result['value'];lines=['Сопоставляем члены исходного ряда с коэффициентами производящей функции.']
            if 'recurrence' in p:lines.extend([p['recurrence'],p['differential_equation']])
            if 'differentiated_series_sum' in p:lines.append('Почленное дифференцирование даёт '+pretty(p['differentiated_series_sum'])+'. Восстанавливаем сумму с её значением при нуле.')
            if 'integrated_series_sum' in p:lines.append('Сумма после почленного интегрирования равна '+pretty(p['integrated_series_sum'])+'. Исходную сумму восстанавливаем дифференцированием.')
            lines.append('Внутри области сходимости сумма равна '+pretty(v['interior_sum'])+'.')
            for b in v['boundaries']:
                lines.append('Конец '+pretty(b['point'])+' — '+b.get('convergence',b.get('condition',''))+
                             (', сумма '+pretty(b['sum']) if b['sum'] is not None else '')+'.')
            return '\n'.join(lines)
        if p.get('theorem')=='method.abel_series_values':
            return 'Получаем производящую функцию внутри единичного интервала. Проверяем сходимость при предельном аргументе и применяем теорему Абеля. Сумма ряда '+pretty(result['value'])+'.'
        if p.get('theorem')=='method.geometric_antidifference':
            return 'Проверяем исходные знаменатели и представляем член разностью соседних значений '+pretty(p['kernel'])+' с множителем '+pretty(p['scale'])+'. Предельное значение краевого члена '+pretty(p['tail_limit'])+'. Сумма ряда '+pretty(result['value'])+'.'
        if p.get('theorem')=='method.harmonic_series_values':
            return 'Разлагаем исходный член по гармоникам. Для каждой частоты применяется геометрический, логарифмический или экспоненциальный ряд. Слагаемые оцениваются при одном верхнем индексе. Частоты в резонансе учитываются отдельно.'
        if p.get('theorem')=='method.translated_series_difference':
            return 'Находим граничное выражение '+pretty(p['witness'],n)+'. Разность его соседних значений равна исходному члену. В частичной сумме остаются только два края.\n'+report(result['children'][0]['proof'],library)+'\nСумма ряда '+pretty(result['value'])+'.'
        if p.get('theorem')=='method.geometric_series_tail':
            if 'cycle' in p:
                return 'Разобьём члены на полные периоды. Сумма первого блока '+pretty(p['block_sum'])+' для индекса 0 масштабируется начальной степенью. Отношение блоков '+pretty(p['block_ratio'])+'. Остаток неполного блока стремится к нулю. Сумма ряда '+pretty(result['value'])+'.'
            return 'Синус и косинус следующего угла получаются поворотом на '+pretty(p['angle_step'])+'. В конечной геометрической сумме после умножения на 1−z сокращаются внутренние члены. Модуль остатка стремится к нулю, поскольку |z|<1. Сумма равна '+pretty(result['value'])+'.'
        if p.get('theorem')=='method.factorial_polynomial_series':
            cs=', '.join(pretty(freeze(c)) for c in p['falling_coefficients'])
            return f"Коэффициенты полинома в базисе падающих факториалов равны {cs}. Сократив каждую падающую степень с факториалом индекса, суммируем сдвинутые экспоненциальные ряды и вычитаем начальные члены. Сумма равна "+pretty(result['value'])+'.'
        if 'linear_limits' in p:
            return '\n'.join([report(v['proof'],library) for v in result['children']]+['Предел суммы частичных сумм равен '+pretty(result['value'])+'.'])
        if 'finite_prefix_limit' in p:
            return report(result['children'][0]['proof'],library)+'\nПредел проверенной частичной суммы равен '+pretty(result['value'])+'. Это сумма ряда.'
        if 'partial_fractions' in p:
            lines=['Разложим рациональную часть по полюсам. Коэффициенты проверены приведением к общему знаменателю.']
            for term in p['partial_fractions']:
                lines.append('Полюс '+term['pole']+', степень '+str(term['order'])+', коэффициент '+term['weight']+'.')
            if p['phase']:lines.append('На целых индексах общий знак задаётся множителем (−1)^'+n+'.')
            lines.append('Суммируем все части до одного верхнего индекса. Каждый фиксированный сдвиг верхнего конца даёт исчезающий остаток.')
            if not p['phase']:lines.append('У обычных гармонических частей проверяем, что суммарный коэффициент при H_N равен нулю.')
            for term in p['common_cutoff_residues']:
                lines.append('После совмещения сумм с началом '+term['origin']+' и степенью '+str(term['order'])+' вклад равен '+term['coefficient']+' · ('+pretty(term['regular_part'])+').')
            lines.append('Поправка от конечных сдвигов равна '+p['finite_endpoint_adjustment']+'. Получаем '+pretty(result['value'])+'.')
            return '\n'.join(lines)
        if 'positive_integer_shift' in p:
            h=pretty(p['positive_integer_shift']);j=pretty(p['boundary_index'])
            return '\n'.join(['Введём K('+n+') = '+pretty(p['kernel'])+'. Тогда исходный член равен '+pretty(p['coefficient'])+'·(K('+n+')−K('+n+'+'+h+')).',
                'В конечной сумме сокращаются слагаемые со сдвигом на '+h+'. Остаются два блока, каждый длины '+h+'.',
                'Верхний блок стремится к нулю при фиксированном '+h+'. Ответ равен '+pretty(p['coefficient'])+' · Σ ('+pretty(p['lower_block_summand'])+'), где '+j+' пробегает целые от 0 до '+h+'−1.'])
        return '\n'.join(['Суммируем '+task['term']+' по целым '+n+' от '+str(p['start'])+' до +∞.',
             'R('+n+') = '+pretty(p['antidifference'])+'. Проверено тождество a('+n+') = R('+n+') − R('+n+'+1) на исходных индексах.',
             'Частичная сумма до '+n+' равна '+pretty(p['finite_partial_sum'])+'.',
             'Предел R('+n+'+1) равен '+pretty(p['limit'])+'. Сумма ряда равна '+pretty(result['value'])+'.'])
    if result.get('schema')=='implicit-derivative/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];equation=task['source_formula'] if 'requested_paths' in plan else task['relation']+' = 0'
        lines=['Неявное дифференцирование уравнения '+equation+'.',
               'Производная по зависимой переменной '+pretty(plan['pivot'])+' отлична от нуля на регулярной ветви.']
        labels=([label for label,_ in plan['requested_paths']] if 'requested_paths' in plan else
                [task['dependent']+'_'+''.join(p) for p in task['requested_partials']] if 'requested_partials' in task else
                ['d^'+str(k)+' '+task['dependent'] for k in task['differential_orders']])
        for label,v in zip(labels,result['value']):lines.append(label+' = '+pretty(v))
        return '\n'.join(lines)
    if result.get('schema')=='indexed-moment/v1':
        lines=['Формула понижения для '+task['integrand'],result['status']]
        if result.get('value') is None:return '\n'.join(lines+[result.get('reason','')])
        p=result['compilation'];v=result['value'];s=v['stride']
        if 'substitution' in p:
            lines.append('Подставим '+task['variable']+' = '+pretty(p['substitution'])+'. Внутри промежутка косинус положителен, а новый интегранд непрерывен вплоть до концов.')
            return '\n'.join(lines+[report(result['children'][-1]['proof'],library)])
        lines.append('Обозначим через J_p интеграл W·U^p. Здесь W = '+pretty(p['weight'])+', U = '+pretty(p['base'])+', V = '+pretty(p['multiplier'])+'.')
        lines.append('Для k = p−'+str(s)+'+1 дифференцируем V·U^k и интегрируем производную по исходному промежутку.')
        def coefficient(key):
            c,h=map(pretty,v['coefficients'][key]);return '('+c+' + k·('+h+'))'
        def boundary(item):
            if 'product_limit' in item:return pretty(item['product_limit'])
            return '('+pretty(item['multiplier'])+')·('+pretty(item['kernel'])+')^k'
        if 'decay_rate' in p:lines.append('В бесконечности произведение убывающей экспоненты на любую фиксированную неотрицательную степень линейной функции стремится к нулю.')
        ends=list(map(boundary,v['boundary']))
        lines.append('L = '+coefficient('leading')+', R = '+coefficient('lower')+', B = '+ends[1]+' − '+ends[0]+'.')
        lines.append('J_p = A_p·J_(p−'+str(s)+') + D_p, где A_p = −R/L, D_p = B/L.')
        lines.extend('J_'+str(row['degree'])+' = '+pretty(row['value']) for row in v['bases'])
        lines.append('При p = '+str(v['degree']['slope'])+'·'+task['index']+f"{v['degree']['intercept']:+d} положим s = "+str(s)+', r = p mod s, t = (p−r)/s.')
        lines.append('J_p = J_r·∏_{j=1}^t A_(r+js) + ∑_{i=1}^t D_(r+is)·∏_{j=i+1}^t A_(r+js). Пустое произведение равно 1.')
        return '\n'.join(lines)
    if result.get('schema')=='oriented-boundary/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')
        plan=result['compilation'];formula='Формула Грина' if len(task['variables'])==2 else 'Формула Гаусса'
        lines=[formula,'Ориентация границы: '+task['orientation'],'Подынтегральная функция с учётом ориентации: '+pretty(plan['density'])]
        if 'boundary_integral' in result['value']:lines.append('Интеграл по границе равен '+pretty(result['value']['boundary_integral'])+'.')
        if 'direct_integral' in result['value']:lines.append('Прямое интегрирование по контуру даёт '+pretty(result['value']['direct_integral'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='cartesian-slices/v1':
        if result.get('value') is None:return result['status']+'\n'+result.get('reason','')+'\n'
        lines=['Пределы интегрирования для '+task['integrand']]
        for key,strips in result['value'].items():
            x,y=result['compilation']['coordinates'];v,w=(x,y) if key==x+'_then_'+y else (y,x)
            lines.append('Внешняя переменная '+v+', внутренняя '+w)
            for s,a,b,l,h in strips:lines.append(('С вычитанием: ' if s<0 else '')+pretty(a)+' ≤ '+v+' ≤ '+pretty(b)+', '+pretty(l)+' ≤ '+w+' ≤ '+pretty(h))
            if not strips:lines.append('Интеграл равен нулю.')
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='integral-endpoint-derivative/v1':
        lines=['Производная интеграла с переменными пределами',result['status']]
        if result.get('value') is None:lines.append(result.get('reason',''))
        else:
            lines.append('Непрерывность подынтегральной функции позволяет применить формулу F(верхний предел) − F(нижний предел), где F′ = f.')
            for variable,value in zip(task['differentiation_variables'],result['value']):
                lines.append('Производная по '+variable+' = '+pretty(value))
        return '\n'.join(lines)
    if result.get('schema') in ('finite-integral-order/v1','finite-integral-mean/v1'):
        if result.get('value') is None:return result.get('reason',result['status'])
        p=result['compilation'];v=result['value']
        if p['theorem']=='method.finite_integral_mean':
            if 'argument' in p:
                labels={'mean_focal_radius':'Средний фокальный радиус', 'mean_velocity':'Средняя направленная скорость',
                        'mean_squared_current':'Средний квадрат силы тока'}
                return '\n'.join((*p['argument'],*(labels[k]+' равен '+pretty(v[k])+'.' for k in task['requested_output'])))
            return 'Интеграл по исходному отрезку равен '+pretty(p['integral'])+'. Деление на длину '+pretty(p['length'])+' даёт среднее '+pretty(v)+'.'
        conclusion=('Левый интеграл больше.' if v['left_larger'] else 'Правый интеграл больше.') if 'left_larger' in v else ('Интеграл положителен.' if v['sign']=='positive' else 'Интеграл отрицателен.')
        return 'После сведения к одному интервалу знак подынтегрального выражения '+pretty(p['ordered_kernel'])+' проверяется на открытом отрезке. '+conclusion
    if result.get('schema')=='weighted-integral-mean/v1':
        if result.get('value') is None:return result.get('reason',result['status'])
        p=result['compilation'];v=result['value'];low,high=p['factor_range']
        return ('Вес неотрицателен, его интеграл равен '+pretty(p['weight_integral'])+'. '
                'По первой теореме о среднем множитель в значении интеграла лежит между '+pretty(low)+' и '+pretty(high)+'. '
                'Получаем границы '+pretty(v['lower'])+' и '+pretty(v['upper'])+'.')
    if result.get('schema')=='ellipsoid-moment/v1':
        lines=[task['integrand'],result['status']];v=result.get('value')
        if v:
            plan=result['compilation']
            if plan['natural_parameter_guards']:lines.append('Условия на параметры: '+', '.join(plan['natural_parameter_guards']))
            lines+=['Замена координат по выделенным квадратам:']
            for x,p,shift in plan['completed_squares']:lines.append(pretty(x)+' = '+pretty(shift)+' + h_'+str(x[1])+', коэффициент квадрата '+pretty(p))
            show=lambda r:pretty(r['value']) if r['defined'] else 'не определено при нулевой мере'
            if 'when_positive' in v:lines+=['При '+pretty(v['size'])+' > 0: '+show(v['when_positive']),'В остальных случаях: '+show(v['otherwise'])]
            else:lines.append('Ответ: '+show(v))
        elif result.get('reason'):lines.append(result['reason'])
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='line-integral/v1':
        lines=['Криволинейный интеграл',result['status']]
        if (result.get('compilation') or {}).get('measure')=='exact_one_form':
            lines.append('Градиент функции '+pretty(result['compilation']['potential'])+' совпадает с коэффициентами формы. Интеграл равен разности значений функции на концах пути.')
        for p in (result.get('compilation') or {}).get('pieces',[]):
            lines.append('После подстановки на участке '+str(len(lines)-1)+' получаем '+pretty(p['pullback'],task['parameter'])+' и интеграл '+pretty(p['value'])+'.')
        lines.append('Сумма = '+pretty(result['value']) if result.get('value') is not None else result.get('reason',''))
        return '\n'.join(lines)
    if result.get('schema')=='iterated-integral/v1':
        lines=[task['integrand'],result['status']]
        plan=result.get('compilation') or {}
        if plan.get('theorem')=='method.finite_parameter_endpoint_profiles':
            return '\n'.join((*plan['argument'],pretty(freeze(result['value']))))
        if plan.get('chart')=='indexed_euler_expansion':
            return 'Формулы Эйлера и биномиальное разложение дают конечную сумму экспонент со всеми заявленными целыми показателями. Каждая мода вычисляется на исходных концах, а нулевая мода даёт длину интервала.'
        for s,child in zip(plan.get('stages',[]),result['children']):
            if plan.get('chart'):
                x=s['variable'];chart=s['method']
                if chart=='branched_rational_substitution':
                    t='t' if x!='t' else 'u'
                    discovery=s['discovery']
                    def leading_term(key):
                        coefficient,order=discovery[key]
                        return pretty(m.mul(freeze(coefficient),m.power(('v',x),order)),x)
                    lines.append(f"Ведущие члены при нуле и бесконечности равны {leading_term('at_zero')} и {leading_term('at_infinity')}. Сравнение коэффициентов для замены {x} + c/{x} даёт кандидат c = {pretty(discovery['scale'])}.")
                    lines.append(f"{t} = {pretty(s['forward'],x,simplify=False)}, d{t}/d{x} = {pretty(s['jacobian'],x)}.")
                    lines.append(f"Проверено равенство дифференциалов. После замены интегрируем {pretty(s['kernel'],t)} по {t}.")
                    for branch in s['branches']:
                        a,b=map(pretty,branch['source_bounds']);p,q=map(pretty,branch['image_bounds'])
                        lines.append(f"При {x} от {a} до {b} пределы по {t} идут от {p} до {q}. Интеграл на этой ветви равен {pretty(branch['value'])}.")
                elif chart=='endpoint_change_of_variable':
                    lines.extend([f"u = {pretty(s['u'],x)}, u′ = {pretty(s['du'],x)}.",
                                  f"На открытом интервале произведение знаменателя и u′ равно {pretty(s['scale_on_interval'])}.",
                                  f"Первообразная F = {pretty(s['primitive'],x)}."])
                    for edge in result['children']:
                        proof=edge['proof'];approach=proof['task'].get('approach')
                        if approach:
                            side='справа' if approach['side']=='right' else 'слева'
                            lines.append(f"Предел F в точке {approach['point']} {side} равен {pretty(proof['value'])}.")
                else:
                    if chart=='semicircle_chart':
                        t='θ';bounds=s['transformed_bounds'];kernel=s['transformed_integrand']
                        lines.extend([f"{x} = {pretty(s['substitution'],t)}.",
                                      f"На выбранном интервале корень равен {pretty(s['radical_image'],t)}."])
                    else:
                        t='u' if x!='u' else 't';bounds=s['substituted_bounds'];kernel=s['kernel']
                        lines.append(f"{t} = {pretty(s['forward'],x)}, {x} = {pretty(s['inverse'],t)}.")
                    lines.append(f"d{x}/d{t} = {pretty(s['jacobian'],t)}.")
                    lines.append(f"После замены интегрируем {pretty(kernel,t)} по {t} от {pretty(bounds[0])} до {pretty(bounds[1])}.")
                continue
            a,b=s['bounds'];parts=factor_parts_lines(child['proof']);lines.extend(parts)
            if parts:
                low,high=s['endpoint_values']
                lines.extend(['Первообразная F = '+pretty(s['primitive'])+'.',
                              'F('+pretty(a)+') = '+pretty(low)+', F('+pretty(b)+') = '+pretty(high)+'.'])
            else:
                lines.append('По '+s['variable']+' от '+pretty(a)+' до '+pretty(b)+': первообразная '+pretty(s['primitive'])+', значение '+pretty(s['difference'])+'.')
        if result.get('value') is not None:
            lines.append(('Среднее значение' if task['requested_output']==['area_mean'] else 'Интеграл')+' = '+pretty(result['value']))
        elif result.get('reason'):lines.append(result['reason'])
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='pointwise-limit-continuity/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        if 'maximum_of' in result['value']:
            v=result['value']
            return ('Сумма лежит между наибольшим слагаемым и этим слагаемым, умноженным на число членов. '
                    +'В пределе получаем max('+', '.join(map(pretty,v['maximum_of']))+') / '+pretty(v['divisor'])
                    +'. Максимум конечного числа непрерывных функций непрерывен.')
        v=result['value'];c=pretty(v['cut']);x=v['variable'];L,R=map(pretty,result['compilation']['one_sided_at_cut'])
        return (f"При {x} < {c} предел равен {pretty(v['left_formula'])}, при {x} > {c} равен {pretty(v['right_formula'])}. "
                f"В точке {c} значение {pretty(v['at_cut'])}, пределы слева и справа равны {L} и {R}. "
                +{'continuous':'Функция непрерывна на всей исходной области.','removable':'В этой точке устранимый разрыв.','jump':'В этой точке скачок.'}[v['classification']])
    if result.get('schema')=='continuity-classification/v1':
        value=result.get('value')
        if value is None:return result['status']+'\n'+result.get('reason','')
        lines=['На каждом оставшемся интервале исходной области функция непрерывна по композиции.']
        if 'jump_families' in value:
            var=task['variable'];lines=[]
            for f in value['jump_families']:
                lines.append(f"При {var} = {pretty(f['location'])} ({f['index']}) предел слева {pretty(f['left'])}, справа {pretty(f['right'])}, значение {pretty(f['value'])}.")
                if f['classification']=='continuous':lines.append('Оба предела совпадают со значением.')
                else:lines.append('Скачок в точности там, где '+pretty(f['jump_if_nonzero'])+' ≠ 0.')
            for point in value['other_points']:
                description={'continuous':'непрерывна на исходной области','removable':'устранимый разрыв',
                             'infinite_discontinuity':'бесконечный разрыв','oscillatory_discontinuity':'ни одного одностороннего предела нет'}[point['classification']]
                lines.append(f"В точке {pretty(point['point'])} функция имеет следующее поведение: {description}.")
                if 'left' in point and point['left']!='does_not_exist':
                    lines.append('Предел слева '+pretty(point['left'])+', справа '+pretty(point['right'])+'.')
            return '\n'.join(lines+['На остальных точках исходной области функция непрерывна.'])
        labels={'continuous':'непрерывна','removable':'устранимый разрыв','jump_discontinuity':'скачок',
                'infinite_discontinuity':'бесконечный разрыв','continuous_at_isolated_point':'изолированная точка непрерывности'}
        for p in value['points']:
            desc=labels.get(p['classification'])
            if desc is None:desc='непрерывна при значении '+pretty(p['required_value'])+'; иначе разрыв устраним'
            limits=', '.join(('слева ' if side=='left' else 'справа ')+pretty(v) for side,v in p['one_sided'].items())
            lines.append('При '+task['variable']+' = '+pretty(p['point'])+' '+desc+('. Пределы: '+limits if limits else ''))
        return '\n'.join(lines)
    if result.get('schema')=='continuous-extension/v1':
        value=result.get('value')
        lines=['Непрерывное доопределение в точке '+str(task.get('point')),result['status']]
        if value is None:lines.append(result.get('reason',''))
        elif value['exists']:lines.append('По пределу на исходной области f('+str(task['point'])+') = '+pretty(value['assigned_value']))
        elif 'infinite_limit' in value:lines.append('Конечного непрерывного доопределения нет. Предел равен '+pretty(value['infinite_limit']))
        else:lines.append('Односторонние пределы различны: '+', '.join(pretty(v) for v in value['unequal_limits']))
        return '\n'.join(lines)
    if result.get('schema')=='tangent-geometry/v1':
        val=result.get('value')
        if val is None:return result['status']+'\n'+result.get('reason','')+'\n'
        lines=[];vec=lambda a:'('+', '.join(pretty(v) for v in a)+')'
        if 'split_parameter' in val:
            s=val['split_parameter'];lines+=[s+' = 0: образ — точка '+vec(val['zero']['constant_image'])+', касательная не определяется.',s+' ≠ 0:']
            val=val['nonzero']
        n=vec(val['line_direction']);curve=result['compilation']['dimension']==1
        lines += [('Касательная прямая' if curve else 'Нормаль')+': r(t) = '+vec(val['through'])+' + t '+n,
                  ('Нормальная плоскость' if curve else 'Касательная плоскость')+': '+n+' · ('+', '.join(task['coordinates'])+') = '+pretty(val['plane_constant'])]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='scalar-field-geometry/v1':
        lines=[task['function'],result['status']]
        vec=lambda a:'('+', '.join(pretty(v) for v in a)+')'
        for name,p in (result.get('compilation') or {}).get('points',{}).items():
            if p['on_source_level']:lines.append('Точка '+name+' принадлежит поверхности '+task['function']+' = '+str(task['level'])+'.')
        for item,val in zip(task.get('requests',[]),result.get('value') or ()):
            op=item['op'];at=item['at']
            if op=='tangent_plane_and_normal':
                n=vec(val['normal']);p=vec(val['through'])
                lines+=['Касательная плоскость: '+n+' · ('+', '.join(task['variables'])+') = '+pretty(val['plane_constant']),
                        'Нормаль: r(t) = '+p+' + t '+n]
            elif op=='gradient_angle':lines.append('Угол между градиентами в '+at+' и '+item['other']+' = '+pretty(val))
            else:
                label={'gradient':'Градиент','gradient_norm':'Норма градиента','gradient_direction':'Единичный вектор градиента',
                       'directional_derivative':'Производная по направлению'}[op]
                lines.append(label+' в '+at+' = '+(vec(val) if op in ('gradient','gradient_direction') else pretty(val)))
        if result.get('reason'):lines.append(result['reason'])
        return '\n'.join(lines)+'\n'
    if result.get('schema') in ('derivative-sign-chart/v1','printed-inequality/v1'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        v=result['value']
        if 'claims' in v:return '\n'.join([r['relation']+'  '+r['explanation'] for r in v['claims']]+v['geometric_interpretation'])
        labels={'strictly_increasing':'Строго возрастает','strictly_decreasing':'Строго убывает',
                'flat':'Постоянна' if 'convex' not in v else 'Линейна','convex':'Выпукла вниз (касательные ниже графика)',
                'concave':'Выпукла вверх (касательные выше графика)'}
        def end(z):
            if isinstance(z,str):return z.replace('inf','∞')
            a,b,d=z[1:];return pretty(m.add(freeze(a),m.mul(freeze(b),('sqrt',m.q(d)))))
        lines=[]
        for k,label in labels.items():
            if k in v:
                parts=[('[' if lc else '(')+end(l)+', '+end(r)+(']' if rc else ')') for l,r,lc,rc in v[k][1]]
                lines.append(label+' на '+(' ∪ '.join(parts) if parts else '∅'))
        if 'inflections' in v:lines.append('Точки перегиба '+(', '.join('('+pretty(a)+', '+pretty(b)+')' for a,b in v['inflections']) or 'отсутствуют'))
        return '\n'.join(lines)
    if result.get('schema')=='curve-contact-geometry/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        value=result['value']
        def point(p):return '('+', '.join(pretty(z) for z in p)+')'
        def equation(p,v):return f'{pretty(v[0])}·(X − {pretty(p[0])}) + {pretty(v[1])}·(Y − {pretty(p[1])}) = 0'
        if 'through' in value:
            p=value['through'];return 'Точка '+point(p)+'.\nКасательная '+equation(p,value['tangent_coefficients'])+'.\nНормаль '+equation(p,value['normal_coefficients'])+'.'
        if 'solutions' in value:return 'Точки с требуемым направлением: '+', '.join(point(s['point']) for s in value['solutions'])+'.'
        if 'cosine' in value:return ('Косинус угла равен '+pretty(value['cosine'])+' при ненулевых нормах '+point(value['regular_when_both_nonzero'])+
              '. При нулевой норме соответствующее направление исчезает при всех значениях параметра.')
        if 'contact_order' in value:return f"Порядок касания {value['contact_order']}. Первые различные производные имеют порядок {value['first_discrepancy_degree']}."
        t=value['regular_tangent'];return ('В регулярной точке касательная '+equation(t['through'],t['coefficients'])+
              ('. Точка на оси Ox '+point(value['normal_foot']) if 'normal_foot' in value else '')+'. '+value['construction']+
              (' При нулевом масштабе вся кривая состоит из одной точки.' if 'collapsed' in value else ''))
    if result.get('schema')=='sided-derivative-cells/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        v=result['value'];lines=[]
        for cell in v['cells']:
            d=cell['derivative'];lines.append(f"({cell['left']}, {cell['right']}) — "+('вне области' if d is None else 'производная '+pretty(d)))
        for row in v['cuts']:
            lines.append('Точка '+pretty(row['point'])+'.')
            for side,z in row['sides'].items():
                side='Слева' if side=='left' else 'Справа'
                lines.append(side+' обычная производная '+('вне области' if z['ordinary'] is None else pretty(z['ordinary']))+
                             (', по значению одностороннего предела '+pretty(z['generalized']) if 'generalized' in z else '')+'.')
        if 'derivative_limit' in v:lines.append('Предел производной '+pretty(v['derivative_limit'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='power-series-boundary/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];v=result['value']
        labels={'absolute':'абсолютная сходимость','divergent':'расходимость','conditional':'условная сходимость'}
        def classification(c):
            if isinstance(c,str):return labels[c]
            if 'parameter' in c:
                return ', '.join(c['parameter']+op+'1 — '+classification(c[k]) for op,k in (('<','below_one'),('=','at_one'),('>','above_one')))
            return ', '.join(labels[k]+' при '+c[k+'_if'] for k in labels if c[k+'_if']!='never')
        h=pretty(p['coefficient_profile']['log_coefficient'])
        lines=[f"Выделяем степень с основанием {p['coordinate']}. Проверяем множители начиная с индекса {p['start_index']}.",
               'В положительной части коэффициентов отношение соседних членов после выделения квадратичной и корневой экспонент имеет главный член '+
               pretty(p['ratio_multiplier'])+' · n^('+pretty(p['coefficient_profile']['ratio_degree'])+'). Поправка в логарифме равна '+h+'/n с суммируемым остатком.']
        if p['source_guards']:lines.append('Область исходных членов требует '+', '.join(p['source_guards'])+'.')
        if 'open_interval' in v:
            interval=v['open_interval']
            region='('+', '.join(interval)+')' if interval else 'пуст'
            lines.append('Радиус '+v['radius']+', открытый интервал '+region+'.')
            lines.extend(w+' — '+classification(c)+'.' for w,c in v['endpoint_classifications'].items())
        if isinstance(v.get('convergence_set'),dict):
            c=v['convergence_set'];r=c['absolute_inside'];z=c['coordinate']
            lines.extend([f'При |{z}| < {r} ряд сходится абсолютно, при |{z}| > {r} расходится.',
                          f'При {z} = −({r}) — '+classification(c['at_negative_boundary'])+'.',
                          f'При {z} = {r} — '+classification(c['at_positive_boundary'])+'.'])
        elif 'convergence_set' in v:lines.append('Ряд сходится только при '+task['variable']+' = '+v['convergence_set']+'.')
        return '\n'.join(lines)
    if result.get('schema') in ('symbolic-order-coefficients/v1','analytic-power-series/v1'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from tasks import guard_source
        plan=result['compilation'];value=result['value']
        lines=[task['function']+', центр '+plan['center']+'.',value['formula']+'.',value['notation']]
        if result['schema']=='analytic-power-series/v1':
            if value['valid_on']=='all_real':
                lines.append('Ряд сходится к функции на всей вещественной прямой.')
            elif value['valid_on']=='certified_convergence_interval':
                lines.append('В сдвинутой координате применяется геометрический ряд со знаменателем '+pretty(plan['geometric_factor'])+'.')
                lines.extend(report(c['proof'],library) for c in result['children']
                             if c['role']=='prove convergence including both endpoints of the geometric expansion')
            else:lines.append('Ряд сходится к функции в открытой окрестности центра, где допустимы применённые разложения.')
            if plan['method']=='expand_derivative_then_integrate_termwise':lines.append('Раскладываем производную и интегрируем почленно, сохраняя значение функции в центре.')
            if 'partial_fractions' in plan:lines.append('Разложение на простейшие дроби: '+' + '.join(pretty(e) for e in plan['partial_fractions'])+'.')
            if 'derivative_at_center' in value:
                d=value['derivative_at_center'];lines.append(f"Производная порядка {d['factorial_order']} в центре равна {pretty(d['multiplier'])} · {d['factorial_order']}!.")
        else:lines.append('Порядок n принимает все целые значения от 1.')
        if plan['natural_domain']:lines.append('Исходная область '+', '.join(map(guard_source,plan['natural_domain']))+'.')
        for i,row in enumerate(value['coefficients']):
            args=', '.join('C['+str(j)+']' for j in row['operands'])
            lines.append(f"C[{i}](0) = {row['zero']}; C[{i}](k) = {row['positive_orders']}."+
                         (' (A, B по порядку: '+args+').' if args else '')+
                         (' b(j) = '+row['outer_coefficients']+'.' if 'outer_coefficients' in row else '')+
                         (' r='+row['exponent']+'.' if 'exponent' in row else '')+
                         (' Цикл '+str(row['cycle'])+'.' if 'cycle' in row else ''))
        return '\n'.join(lines)
    if result.get('schema')=='ordinary-differentiation/v1':
        if result.get('status')!='SOLVED':return result['status']+'\n'+result.get('reason','')
        from tasks import guard_source
        p=result['compilation'];n=p['order'];x=p['variable']
        lines=['Исходная функция '+task['function']+'.',
               'Область: '+(', '.join([*p['stated_conditions'],*map(guard_source,p['natural_domain'])]) or 'все вещественные '+x)+'.']
        if p.get('independent_increment'):
            lines.append(f'Координата {x} независима. d^{n}y = y^({n}) · ({p["independent_increment"]})^{n}.')
        lines.append('После последовательного дифференцирования получено '+pretty(result['value'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='successive-composition/v1':
        if result.get('status')!='SOLVED':return result['status']+'\n'+result.get('reason','')
        from tasks import guard_source
        p=result['compilation'];lines=['Подставим разложения внутренних функций по формуле Тейлора в исходное выражение.']
        guards=[*p['stated_conditions'],*map(guard_source,p['natural_domain'])]
        if guards:lines.append('Условия: '+', '.join(guards)+'.')
        for name,spec in p['symbols'].items():
            what=spec['function']+('('+spec['at']+')' if 'at' in spec else '')
            if spec['order']:what=('дифференциал' if spec.get('differential') else 'производная')+' порядка '+str(spec['order'])+' от '+what
            lines.append(name+' = '+what+'.')
        for k,v in zip(p['requested_orders'],result['value']):
            lines.append(f'Коэффициент при приращении степени {k}, умноженный на {k}!, даёт '+pretty(v)+'.')
        return '\n'.join(lines)
    if result.get('schema')=='exact-form/v1' and task.get('kind') in ('exact_differential_endpoints','potential_from_differential'):
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        plan=result['compilation'];value=result['value']
        if value.get('has_global_potential') is False:
            return '\n'.join(['Локальная первообразная F = '+pretty(value['potential']),
                              'Интеграл за положительный обход равен '+pretty(value['period'])+'.',
                              'Из ненулевого обхода следует, что на всей исходной области первообразной нет.'])
        lines=['Потенциал F = '+pretty(value['potential'])]
        for x,v in zip(plan['variables'],plan['gradient']):lines.append('∂F/∂'+x+' = '+pretty(v))
        lines.append('Градиент совпадает с коэффициентами заданной формы на исходной области.')
        if 'line_integral' in value:lines.append('Интеграл равен F(B) − F(A) = '+pretty(value['line_integral'])+'.')
        else:lines.append('На каждой связной компоненте можно прибавить произвольную постоянную.')
        return '\n'.join(lines)
    if result.get('schema')=='total-differentials/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        return 'df = '+pretty(result['value']['d1'])+'\nd²f = '+pretty(result['value']['d2'])+'\n'
    if result.get('schema')=='ordered-partial-equality/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation']
        return 'Обе производные вычислены в своих порядках '+', '.join(' затем '.join(row) for row in p['ordered_equality'])+'. Обе формулы равны '+pretty(result['value']['common_value'])+' на исходной области.'
    if result.get('schema')=='continuity-locus/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];v=result['value'];lines=['Все операции исходной формулы непрерывны на её области определения.']
        from tasks import guard_source
        for g in p['raw_domain']:lines.append('Проверяем '+guard_source(g)+'.')
        for loc in v['exceptional_points_in_closure']:
            text=' и '.join(pretty(e)+' = 0' for e in loc['forms']) if 'forms' in loc else pretty(loc['form'])+(' = kπ, k целое' if loc['kind']=='integer_pi' else ' = 0')
            lines.append('Исключённые точки в замыкании области задаются условием '+text+'.')
        for outside in v['outside_domain_closure']:lines.append('При '+pretty(outside['form'])+' < 0 точка лежит вне замыкания области.')
        return '\n'.join(lines)
    if result.get('schema')=='joint-limit/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from tasks import guard_source
        p=result['compilation'];value=result['value'];lines=[]
        if p['original_domain']:lines.append('На исходной области выполняются '+', '.join(map(guard_source,p['original_domain']))+'.')
        if 'successive_limits' in p:
            for trial,final in zip(p['successive_limits'],value['iterated_limits']):
                lines.append('Сначала по '+trial['first']+' получаем '+pretty(trial['inner_limit'])+', затем по '+trial['second']+' получаем '+pretty(final)+'.')
            lines.append('Ненулевые полиномы, дающие крайние коэффициенты, имеют лишь конечное число исключительных сечений.')
        if 'coordinate_sections' in p:lines.append('На обеих координатных осях предел совпадает со значением в начале. Вне начала исходная рациональная функция непрерывна.')
        if 'all_rays' in p:lines.append('На луче общего наклона сравниваем степени числителя и знаменателя. Отдельная проверка вертикального и всех исключительных наклонов даёт один предел '+pretty(value['all_directional_limits'])+'.')
        for path in p.get('distinct_paths',[]):
            lines.append('При (x, y) = ('+', '.join(map(pretty,path['curve']))+') и t → '+path['parameter_approach']+' ограничение есть ('+pretty(path['trace_numerator'])+')/('+pretty(path['trace_denominator'])+'). Его предел равен '+pretty(path['limit'])+'.')
        if 'distinct_paths' in p:lines.append('Разные пределы на допустимых путях исключают совместный предел.')
        if 'uniform_error_estimate' in p:
            u=p['uniform_error_estimate']
            lines.append('Положим s = '+u['scale']+'. В каждом из двух секторов однородный член знаменателя отделён от нуля. При 0 < s ≤ '+pretty(u['max_scale'])+' ошибка на всех направлениях не превосходит '+pretty(u['coefficient'])+' · s^'+str(u['power'])+'.')
        if 'outer_function' in p:
            lines.append('Приращение аргумента равно '+pretty(p['increment'])+'. Разностное отношение функции '+p['outer_function']+' в точке '+pretty(p['anchor'])+' имеет непрерывное продолжение со значением '+pretty(p['slope'])+'.')
            lines.append('Подставляем это значение вместо S в '+pretty(p['residual']).replace('__slope','S')+' и переходим к пределу.')
        if 'separated_terms' in p:lines.append('Раскрываем экспоненты сумм и разбиваем выражение на сумму произведений независимых функций. Пределы множителей: '+', '.join(pretty(a)+' → '+pretty(b) for a,b in p['factor_limits'])+'.')
        if 'upper_bound' in p:lines.append('На положительном квадранте основание положительно и не превосходит '+pretty(p['upper_bound'])+'. Это следует из неотрицательности квадратичной формы '+pretty(p['majorant_quadratic'])+'. Показатель стремится к +∞.')
        if 'positive_homogeneous_base' in p:lines.append('При r = max(|x|, |y|) основание сравнимо с r^'+str(p['positive_homogeneous_base'])+' во всех направлениях. Показатель ограничен по модулю величиной '+pretty(p['exponent_coefficient_bound'])+' · r^'+str(p['exponent_order'])+'. Произведение показателя на логарифм основания стремится к нулю.')
        if 'continuous_composition_at' in p:lines.append('Все операции непрерывны в исходной точке. Подставляем её координаты.')
        if p.get('rational_identity'):lines.append('После вычитания предполагаемого значения числитель тождественно равен нулю на исходной области.')
        if 'joint_limit' in value:lines.append('Совместный предел равен '+pretty(value['joint_limit'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='abstract-field-equation/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        from tasks import guard_source
        import re
        plan=result['compilation'];value=result['value'];lines=[]
        display=lambda expr:re.sub(r'Field(\d+)',r'F[\1]',pretty(expr))
        for slot,(name,args,indices) in plan['field_bindings'].items():
            args=', '.join(display(a) for a in args)
            signature='∂' + '∂'.join(str(i+1) for i in indices)+' ' if indices else ''
            lines.append(f'F[{slot[5:]}] = {signature}{name}({args}).')
        if plan['natural_domain']:lines.append('Исходные ограничения: '+', '.join(map(guard_source,plan['natural_domain']))+'.')
        lines.append('Применяем правило цепочки по каждой указанной независимой переменной.')
        for label,val in plan['derivative_values'].items():lines.append(label+' = '+display(val)+'.')
        if 'differential_relation' in value:
            if plan['elimination_search']['products_of_derivatives_needed']:lines.append('Линейные комбинации оставили неизвестные производные. Включаем попарные произведения и сравниваем коэффициенты при каждом неизвестном множителе.')
            lines.append('Исключаем значения произвольных функций и их производных. Подстановка найденных выражений проверяет уравнение '+pretty(value['differential_relation'])+' = 0.')
        elif 'simplified' in value:lines.append('После подстановки остаётся '+pretty(value['simplified'])+'.')
        else:lines.append('Подставляем эти выражения в исходное равенство. Разность левой и правой частей равна нулю.')
        for cut in plan['checked_exceptional_sets']:
            lines.append('При '+', '.join(s+' = 0' for s in cut['zero_coordinates'])+' коэффициенты уравнения обращаются в нуль. Равенство сохраняется всюду, где существуют указанные производные.')
        return '\n'.join(lines)
    if result.get('schema')=='implicit-system-differentiation/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        p=result['compilation'];lines=[]
        if p.get('theorem')=='method.incompatible_implicit_point':
            witness=result['value']['counterexample']
            return p['argument']+' В строке '+str(witness['equation'])+' получаем '+pretty(witness['left'])+' и '+pretty(witness['right'])+'.'
        if p.get('theorem')=='method.symbolic_implicit_jacobian_and_hessian':
            value=result['value'];return '\n'.join([p['argument'],'При det J = '+pretty(p['determinant'])+' ≠ 0 получаем',
                       *(label+' = '+pretty(v) for label,v in value['formulas'].items())])
        if p.get('theorem')=='method.symmetric_elimination_of_parametric_fibers':
            value=result['value'];return '\n'.join([p['argument'],'Область '+pretty(p['root_discriminant'])+' ≥ 0.',
                       *(label+' = '+pretty(value[label]) for label in ('graph','z_x','z_y'))])
        if 'parametric_graphs' in p:
            lines.extend(report(c['proof'],library) for c in result['children'])
        for base,chart in p.get('charts',{}).items():
            lines.append('Берём '+base+' за независимые координаты. Определитель по '+', '.join(chart['dependent'])+' равен '+pretty(chart['determinant'])+'. На регулярной ветви он отличен от нуля.')
            for slot,(_,_,value) in chart['first_derivative_bindings'].items():lines.append(slot+' = '+pretty(value))
        if p.get('vertical_tangencies'):
            lines.append('В обратной карте производная исходной независимой переменной равна нулю. Конечная производная обратной функции противоречила бы правилу цепочки.')
        for label,v in result['value'].items():lines.append(label+' = '+pretty(v) if not isinstance(v,dict) else label+' не существует как конечная производная.')
        return '\n'.join(lines)
    if result.get('schema')=='multivariate-extrema/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        plan=result['compilation']
        point=lambda xs:'('+', '.join(pretty(x) for x in xs)+')'
        if 'normal_form' in plan:
            lines=['Переходим к главным осям квадратичной формы. Коэффициенты квадратов равны '+
                   ', '.join(pretty(a['eigenvalue']) for a in plan['normal_form']['orthogonal_axes'])+'.']
            if freeze(plan['normal_form']['linear_residual'])!=m.ZERO:
                lines.append('В нулевом направлении остался ненулевой линейный член. В любой окрестности значение растёт и убывает.')
            elif plan.get('critical_affine_set',{}).get('saddle'):
                lines.append('Положительное и отрицательное направления дают седло в стационарном множестве.')
        elif 'elimination' in plan:
            lines=['В открытой области экстремум возможен лишь при нулевом градиенте. После удаления положительного множителя и проверки знаменателей решаем '+
                   ', '.join(pretty(e)+' = 0' for e in plan['stationary_polynomials'])+'.',
                   'Исключение одной координаты даёт '+pretty(plan['elimination']['projection'])+' = 0. Отдельно проверены нули коэффициента при исключённой координате.']
            for row in plan['critical_points']:
                if row['classification']=='outside_domain':lines.append('Точка '+point(row['point'])+' исключена исходной областью.')
                else:lines.append('В точке '+point(row['point'])+' определитель приведённой матрицы вторых производных равен '+pretty(row['determinant'])+
                                  ('. Приращения имеют разные знаки вдоль '+', '.join(str(w['direction']) for w in row['directions'])+'.' if row.get('directions') else
                                   '. Это седло.' if row['classification']=='saddle' else '.'))
        elif 'normal' in plan:
            lines=['Проецируем центр целевой формы на гиперплоскость вдоль нормали '+point(plan['normal'])+'. Изменение значения на плоскости пропорционально квадрату расстояния от проекции.']
        elif 'constant_value' in plan:
            lines=['Вычитание кратного уравнения сферы оставляет постоянную '+pretty(plan['constant_value'])+
                   '. Положительный радиус и точка '+point(plan['feasible_point'])+' подтверждают непустоту.']
        else:lines=['На сфере целевая функция сводится к линейной. Её крайние значения достигаются в двух противоположных направлениях '+point(plan['linear_direction'])+'.']
        if plan.get('parameter_guards'):
            from tasks import guard_source
            lines.append('Формулы действуют при '+', '.join(guard_source(g) for g in plan['parameter_guards'])+'.')
        for row in result['value']['extrema']:
            title=('Строгий' if row['strict'] else 'Нестрогий')+(' локальный ' if row.get('scope')=='local' else ' глобальный ')+('минимум' if row['kind']=='minimum' else 'максимум')
            if row.get('attaining_set'):
                lines.append(title+' '+pretty(row['value'])+' достигается в каждой точке исходной сферы.');continue
            lines.append(title+' '+pretty(row['value'])+' в точке '+point(row['point'])+('.' if not row['free_directions'] else ' и при любом смещении вдоль '+', '.join(point(d) for d in row['free_directions'])+'.'))
        if not result['value']['extrema']:lines.append('Локальных экстремумов нет.')
        return '\n'.join(lines)
    if result.get('schema')=='differential-coordinate-change/v1':
        if result['status']!='SOLVED':return result.get('reason',result['status'])
        plan=result['compilation']
        from tasks import guard_source
        theorem=plan.get('theorem','')
        argument=plan.get('argument',[])
        steps=[argument] if isinstance(argument,str) else list(argument)
        if theorem.startswith('method.ordinary_'):
            value=result['value'];lines=list(steps)
            for row in value.get('branches',()):
                signs={-1:'отрицательном',1:'положительном'}
                lines.append('При '+signs[row['argument_sign']]+' исходном аргументе x = '+pretty(row['old_abscissa'])+
                             ' и '+' = '.join(map(pretty,row['transformed_equation']))+'.')
                lines.append('Условия '+', '.join(guard_source(g) for g in row['source_and_chart_conditions'])+'.')
            if value.get('transformed_sides'):lines.append(' = '.join(map(pretty,value['transformed_sides'])))
            if value.get('coefficients'):lines.extend(n+' = '+s for n,s in value['coefficients'].items())
            if value.get('transformed_condition'):lines.append(value['transformed_condition'])
            if value.get('derivatives'):lines.extend(n+' = '+pretty(e) for n,e in value['derivatives'].items())
            return '\n'.join(lines)
        if plan.get('theorem')=='method.regular_graph_prolongation':
            conditions=', '.join(guard_source(g) for g in plan['chart_domain'])
            label=result['value'].get('expression_name');value=' = '.join(pretty(e) for e in result['value']['transformed_sides'])
            lines=[*steps,'Якобиан полной карты '+pretty(plan['ambient_jacobian'])+'.']
            if old:=plan.get('inverse_coordinate_description',{}).get('names'):
                lines.append('Коэффициенты '+', '.join(old.values())+' определяются обратной ветвью записанной карты.')
            if conditions:lines.append('Условия области '+conditions+'.')
            lines.append('Получаем '+((label+' = ') if label else '')+value+'.')
            return '\n'.join(lines)
        if 'argument' in plan:
            value=result['value'];lines=list(steps)
            if witness:=value.get('counterexample'):
                lines.extend(name+' = '+(pretty(val) if isinstance(val,(list,tuple)) else str(val)) for name,val in witness.items())
            if text:=value.get('identity'):lines.append(text)
            for n,text in value.get('identities',{}).items():lines.append(n+' = '+text)
            for n,e in value.get('equations',{}).items():lines.append(n+' = '+pretty(e))
            if value.get('transformed_sides'):
                lines.append(' = '.join(map(pretty,value['transformed_sides']))+'.')
            if isinstance(value.get('regular_when'),str):lines.append('Область карты — '+value['regular_when']+'.')
            if 'multiplier' in value:
                lines.append('Ненулевой множитель равен '+pretty(value['multiplier'])+'.')
            if solution:=value.get('general_solution'):
                if solution.get('form')=='sum_of_two_arbitrary_functions':
                    u,v=solution['arguments']
                    lines.append(f'Общее решение {solution["field"]} = F({u}) + G({v}).')
            for branch in value.get('branches',()):
                if 'coordinates' in branch and 'condition' in branch:
                    lines.append('При '+branch['condition']+' получаем '+', '.join(
                        name+' = '+pretty(expr) for name,expr in branch['coordinates'].items())+'.')
                if 'transformed_sides' in branch and 'condition' in branch:
                    lines.append('При '+branch['condition']+' получаем '+' = '.join(map(pretty,branch['transformed_sides']))+'.')
            return '\n'.join(lines)
        if 'forward_map' in plan:
            lines=['Подставляем прямую координатную карту '+', '.join(n+' = '+pretty(e) for n,e in plan['forward_map'].items())+'.',
                   'Определители преобразования пространства и проекции графика равны '+pretty(plan['ambient_jacobian'])+' и '+pretty(plan['graph_jacobian'])+'.']
            if plan['characteristic_field'] is not None:lines.append('Берём производную каждой новой координаты вдоль поля ('+', '.join(map(pretty,plan['characteristic_field']))+').')
            else:lines.append('Дважды применяем правило цепочки, сохраняя порядок смешанных производных.')
            lines.append('Обратная подстановка проверяет коэффициенты при каждой производной. Общий ненулевой множитель равен '+pretty(plan['nonzero_equation_factor'])+'.')
            lines.append('При '+', '.join(guard_source(g) for g in plan['source_domain'])+' получаем '+' = '.join(map(pretty,result['value']['transformed_sides']))+'.')
            solution=result['value'].get('general_solution')
            if solution:
                if solution['form']=='sum_of_two_arbitrary_functions':
                    u,v=solution['arguments'];rhs=f'F({u}) + G({v})'
                else:rhs=pretty(solution['offset'])+' + '+pretty(solution['multiplier'])+'·F('+solution['argument']+')'
                lines.append('Общее локальное решение в этих координатах: '+solution['field']+' = '+rhs+', где функции произвольны и имеют требуемые производные.')
            branch=result['value'].get('singular_parameter_branch')
            if branch:
                a,b=branch['active'],branch['free']
                lines.append(f"При {branch['parameter']} = 0 карта вырождается. В исходных координатах вторая производная по {a} равна нулю, откуда {branch['field']} = {a}·F({b}) + G({b}).")
            return '\n'.join(lines)
        if 'inverse_coordinate_differentials' in plan:
            p,q=plan['variables'];lines=['После перехода к '+p+', '+q+' якобиан равен '+pretty(plan['jacobian'])+'.']
            for v,(a,b) in plan['inverse_coordinate_differentials'].items():
                lines.append('∂/∂'+v+' = ('+pretty(a)+') ∂/∂'+p+' + ('+pretty(b)+') ∂/∂'+q+'.')
            lines.append('Применяем эти операторы в порядке исходных производных, включая производные их коэффициентов.')
            lines.append('Область: '+', '.join(guard_source(g) for g in plan['source_domain'])+'.')
            lines.append('После подстановки получаем '+' = '.join(pretty(e) for e in result['value']['transformed_sides'])+'.')
            return '\n'.join(lines)
        u,t=plan['new_dependent'],plan['new_independent']
        lines=[f'{u} считаем функцией {t}. Старые координаты заданы формулами x = '+pretty(plan['map'][0])+', y = '+pretty(plan['map'][1])+'.']
        lines.append('Производные по '+t+' обозначены '+', '.join(s+' = '+u+'′'*i for i,s in enumerate(plan['jet_symbols'],1))+'.')
        if 'speed_squared' in plan:
            lines.append('Квадрат скорости равен '+pretty(plan['speed_squared'])+'. В каждой точке с ненулевой скоростью хотя бы одна координата пригодна как параметр графика.')
            lines.append('Определитель скорости и ускорения равен '+pretty(plan['determinant'])+'. Модуль устраняет зависимость от ориентации.')
        else:
            lines.append('Правило цепочки даёт d/dx = (1/('+pretty(plan['dx_dt'])+')) d/d'+t+'.')
            for i,e in enumerate(plan['derivative_map'],1):lines.append('y'+"′"*i+' = '+pretty(e))
        lines.append('Область карты и исходного выражения: '+', '.join(guard_source(g) for g in plan['original_and_chart_guards'])+'.')
        lines.append('После подстановки получаем '+' = '.join(pretty(e) for e in result['value']['transformed_sides'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='differential-operator/v1':
        lines=['Действие операторов на '+str(task.get('function')),result['status']]
        plan=result.get('compilation',{})
        if 'printed_identity' in plan:
            lines.append(plan['printed_identity'])
            for coordinate,operand,value in plan['applications']:
                lines.append('d/d'+coordinate+' ('+pretty(operand)+') = '+pretty(value))
            lines.append('После подстановки левая часть равна '+pretty(result['value'][0])+'. Равенство доказано на исходной области.')
        elif result.get('value') is not None:
            for name,definition in task['operators'].items():lines.append(name+' = '+definition)
            for item,value in zip(task['requests'],result['value']):
                label=' ∘ '.join(reversed(item['apply']))
                lines.append(label+'('+task.get('field_symbol','u')+') = '+pretty(value))
                if 'equals' in item:lines.append('Проверено равенство с '+item['equals']+' на исходной области.')
        elif result.get('reason'):lines.append(result['reason'])
        return '\n'.join(lines)
    if result.get('schema')=='definite-quadrature/v1':
        lines=['ЧИСЛЕННОЕ ИНТЕГРИРОВАНИЕ',str(task.get('method_requirement'))+', число отрезков '+str(task.get('partition_count')),result['status']]
        if result.get('value'):
            v=result['value'];lines.append('Квадратурная сумма ≈ '+v['approximation'])
            if 'absolute_error_bound' in v:lines.append('Абсолютная погрешность с учётом округления ≤ '+pretty(v['absolute_error_bound']))
            if 'exact_integral' in v:lines.append('Точное значение интеграла = '+pretty(v['exact_integral']))
        elif result.get('reason'):lines.append(result['reason'])
        for c in result.get('children',[]):lines+=['',report(c['proof'],library)]
        return '\n'.join(lines)+'\n'
    if result.get('schema') in ('rational-graph-run/v1','strict-extrema-run/v1'):
        from graphs import graph_report
        return graph_report(result)
    if result.get('schema')=='partial-derivative-bundle/v1':
        from tasks import guard_source
        lines=['ЧАСТНЫЕ ПРОИЗВОДНЫЕ','Функция: '+task.get('function',''),'Статус: '+result['status'], 'Порядок индексов: последовательное дифференцирование слева направо.']
        if result.get('compilation'):lines.append('Исходная область: '+('; '.join(guard_source(g) for g in result['compilation']['natural_domain']) or 'все действительные координаты'))
        if task.get('stated_conditions'):lines.append('Исходные условия: '+'; '.join(task['stated_conditions']))
        for index,value in result.get('partial_values',[]):lines.append('D['+', '.join(index)+'] f = '+pretty(value))
        if result.get('pending'):lines.append('Незавершённая компонента: '+str(result['pending']['index'])+'; '+result['pending']['reason'])
        if result.get('reason'):lines.append(result['reason'])
        for child in result.get('children',[]):lines+=['',report(child,library)]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='ordinary-kernel-derivatives/v1':
        p=result['compilation'];lines=['Старшие производные функции '+task['function'],'Формула Лейбница применяется к многочлену и функции линейного аргумента.']
        for order,value in zip(p['orders'],result['value']):lines.append(f'Производная порядка {order} равна '+pretty(value)+'.')
        for child in result['children']:lines+=['',report(child,library)]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='original-table-derivative/v1':
        from tasks import guard_source
        comp=result['plan']['compilation']
        lines=['ПРОИЗВОДНАЯ ПО ТАБЛИЦЕ В ПРОИЗВОЛЬНОЙ ТОЧКЕ','Функция: '+task['function'],'Статус: '+result['status'],'Фиксированная точка: '+result['plan']['context']['point_symbol']]
        lines.append('Исходная область: '+('; '.join(guard_source(g) for g in comp['natural_domain']) or 'все действительные '+task.get('variable','x')))
        if task.get('stated_conditions'):lines.append('Исходные условия: '+'; '.join(task['stated_conditions']))
        lines.append('Достаточные условия: '+('; '.join(comp['display_sufficient_domain']) or 'без добавленных ограничений'))
        if result.get('value') is not None:lines+=['D(v) = '+pretty(result['formula'],task.get('variable','x')),'D(a) = '+pretty(result['value'])]
        lines+=['Общие правила: '+', '.join(library.by_id[r]['label'] for r in used_rules(result)),'Повторная проверка: '+str(result.get('verification'))]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='series-comparison-run/v1':
        lines=['СХОДИМОСТЬ РЯДА','Член: '+str(task.get('term','')),'Начальный индекс: '+str(task.get('start_index')),'Статус: '+result['status']]
        if result.get('value'):
            value=result['value'];lines.append('Классификация: '+value['classification'])
            plan=result['compilation']
            if plan.get('criterion')=='exceptional_comparison':
                p=lambda e:pretty(freeze(e))
                if plan['strategy']=='sparse_subseries':
                    lines.append(f"Квадратные индексы записываются как m². Проверенный конечный предел суммы квадратов двух масштабированных членов даёт оценку C/m^{plan['comparison_power']} для каждого. Обе мажоранты суммируемы.")
                else:
                    if plan['strategy']=='limiting_factor':
                        lines.append("На хвосте модули множителей ограничены числом "+p(value['tail_factor_bound'])+" < 1.")
                    else:
                        lines.append("Числитель по модулю не больше 1, знаменатель не меньше "+p(plan['lower_denominator'])+".")
                        if plan['zero_parameter']:lines.append(f"При {plan['zero_parameter']}=0 все члены равны нулю. На остальной области геометрическая оценка строга.")
                    lines.append(f"Модуль префикса конечен. По индукции хвостовое произведение ограничено геометрической прогрессией. Множитель n^{plan['degree']} сохраняет сходимость мажоранты по признаку Даламбера. Деление на множители произведения не требуется.")
                return '\n'.join(lines+[report(result['child_result'],library),'Ряд сходится абсолютно.'])
            if plan.get('criterion')=='product_ratio_expansion':
                text='Сокращаем соседние произведения после проверки положительности каждого исходного множителя. Логарифм модуля отношения равен ln(C)+G/√n+H/n+O(n^(−3/2)), где C='+pretty(plan['leading_ratio'])+', G='+pretty(plan['half_order'])+' и H='+pretty(plan['log_coefficient'])+'.'
                if plan.get('terminating_if'):text+=' При целом корне числителя, попадающем в диапазон произведения, хвост тождественно равен нулю. Остальные случаи исследуем после последней перемены знака.'
                if freeze(plan['leading_ratio'])==m.ONE and freeze(plan['half_order'])!=m.ZERO:
                    text+=' Знак G определяет бесконечный предел Раабе. При G<0 ряд сходится, при G>0 общий член не стремится к нулю.'
                elif freeze(plan['leading_ratio'])==m.ONE:text+=' Сумма остатков сходится. Поэтому общий член эквивалентен положительной константе, умноженной на n^H. Ряд сходится при H<−1 и расходится при H≥−1.'
                else:text+=' Отношение меньше единицы в пределе даёт сходимость, больше единицы — расходимость.'
                return text+'\n'+report(result['child_result'],library)
            if value.get('criterion')=='periodic_series':
                plan=result['compilation']
                if plan['argument']=='contiguous_nonnegative_integrals':lines.append('Члены ряда — интегралы неотрицательной функции по смежным промежуткам, которые покрывают всю полуось от начального предела.')
                else:
                    lines.append('Тригонометрический множитель имеет период '+str(plan['period'])+' на целых индексах. Сумма его значений за период определяет применимость признака Дирихле.')
                    lines.append('Для абсолютной сходимости сравниваем сумму положительной амплитуды с её интегралом. Ненулевой остаточный класс в каждом периоде даёт обратную оценку.')
                lines.append('Абсолютная сходимость — '+('да' if value['absolute_convergence'] else 'нет')+'. Условная сходимость — '+('да' if value['conditional_convergence'] else 'нет')+'.')
            elif value.get('criterion')=='alternating_rational':
                plan=result['compilation'];gap=plan['degree_gap'];c=pretty(plan['coefficient'])
                lines.append('На целых индексах член имеет вид (−1)^n · b(n), где b(n) = '+pretty(plan['amplitude'],plan['index'])+'.')
                lines.append(f'Предел n^({gap}) · b(n) равен {c}.')
                if freeze(plan['coefficient'])==m.ZERO:lines.append('Амплитуда тождественно равна нулю.')
                elif value['absolute_convergence']:lines.append(f'Сравнение модулей с 1/n^{gap} даёт абсолютную сходимость.')
                elif value['conditional_convergence']:
                    lines.append(f'При n≥{plan["threshold"]} знак b постоянен и |b| убывает к нулю. Признак Лейбница даёт сходимость, а сравнение модулей с 1/n исключает абсолютную сходимость.')
                else:lines.append('Модуль общего члена не стремится к нулю, поэтому ряд расходится.')
            elif 'log_limit' in value:lines+=['Признак: '+('Коши' if value['criterion']=='root_test' else 'Даламбера'),'Логарифмический предел: '+pretty(value['log_limit'])]
            else:lines+=['Степень сравнения p: '+pretty(value['comparison_power']),'Предел n^p a_n: '+pretty(value['scaled_limit'])]
        if result.get('reason'):lines.append(result['reason'])
        if result.get('value') and 'asymptotic_order' in result['value']:
            a=result['value']['asymptotic_order'];lines.append('Порядок относительно 1/n: '+pretty(a['power'])+'; коэффициент: '+pretty(a['equivalent_coefficient']) if a else 'Порядок относительно 1/n пока не установлен.')
        if result.get('child_result'):lines+=['Область исходного члена проверена для каждого N>=start.',report(result['child_result'],library)]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='euler-homogeneity-run/v1':
        lines=['ОДНОРОДНОСТЬ И ТОЖДЕСТВО ЭЙЛЕРА','Функция: '+str(task.get('function','')),'Статус: '+result['status']]
        if result.get('value'):lines+=['Степень: '+pretty(result['value']['homogeneity_degree']),'Масштабирование: t>0 на исходной области D','Левая часть: '+pretty(result['value']['euler_lhs']),'Правая часть: '+pretty(result['value']['euler_rhs'])]
        if result.get('reason'):lines.append(result['reason'])
        if result.get('child_result'):lines+=['ПРОВЕРКА ПЕРВЫХ ЧАСТНЫХ ПРОИЗВОДНЫХ',report(result['child_result'],library)]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='rational-primitive-part/v1':
        if result.get('value') is None:return result.get('reason','Редукция пока открыта')+'\n'
        plan=result['compilation'];v=task.get('variable','x')
        return ('Сравнение коэффициентов даёт рациональную часть H = '+pretty(plan['rational_part'],v)
                +'. На исходной области f − H′ = '+pretty(plan['remainder'],v)
                +'. У знаменателя остатка нет кратных корней.\n')
    if result.get('schema')=='rational-primitive-criterion/v1':
        if result.get('value') is None:return result.get('reason','Критерий пока не выведен')+'\n'
        lines=['Производная рациональной функции не содержит простых полюсов, в том числе комплексных.']
        if 'monomial_residuals' in plan:
            lines.append('Редукция Эрмита выделяет правильную дробь с бескратным знаменателем. Рациональная первообразная существует ровно тогда, когда её числитель тождественно равен нулю.')
        else:
            lines.append('Для квадрата квадратного знаменателя сопоставляем коэффициенты производной (u·x+v)/Q при двух разных корнях. В случаях кратного корня и падения степени проверяем коэффициент простой дроби отдельно.')
        for case in result['value']['cases']:
            assumptions=' и '.join(pretty(e)+(' = 0' if rel=='zero' else ' ≠ 0') for rel,e in case['when'])
            if case.get('undefined'):answer='знаменатель тождественно нулевой'
            else:answer=' и '.join(pretty(e)+' = 0' for e in case['zeros']) or 'дополнительных условий нет'
            lines.append(('При '+assumptions+' выполняется следующее. ' if assumptions else '')+answer+'.')
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='partial-fraction-symmetry/v1':
        return '\n'.join(plan['argument']) if result.get('value') is not None else result.get('reason',result['status'])
    if result.get('schema')=='quadratic-radical-primitive-proof/v1':
        if result.get('value') is None:return result.get('reason',result['status'])
        lines=list(plan['argument']); value=result['value']
        if 'primitive' in value:
            lines.append('Дискриминант равен '+pretty(value['nonempty_when'][1])+'. На исходной области первообразная равна '+pretty(value['primitive'],task['variable'])+'.')
        else:
            case=value['degree_two']
            lines.append('При '+pretty(case['leading_nonzero'])+' ≠ 0 и наличии действительного интервала условие имеет вид '+pretty(case['zero_residue'])+' = 0.')
        return '\n'.join(lines)
    if (result.get('compilation') or {}).get('method')=='quadratic_radical_differential':
        from radical_primitives import report as radical_report
        return radical_report(result)
    if (result.get('compilation') or {}).get('method')=='finite_harmonic_primitive':
        from integrals import harmonic_report
        return harmonic_report(result)
    if result.get('schema') in ('integral-chain-run/v1','linear-primitive/v1'):
        from tasks import guard_source
        lines=['ПЕРВООБРАЗНАЯ','Интеграл: '+task.get('integrand',''),'Статус: '+result['status']]
        if result.get('value') is not None:
            family=result['value'];domain=family['original_domain'][1]
            lines.append('D: '+('; '.join(guard_source(g) for g in domain) or 'все действительные '+task.get('variable','x')))
            if 'parameter_cases' in family:
                for case in family['parameter_cases']:
                    value=case.get('representative')
                    lines.append('При '+case['condition']+' получаем '+(pretty(value,task.get('variable','x'))+' + C_J'
                                 if value is not None else 'отсутствие открытого интервала первообразной')+'.')
            else:
                lines+=['На каждой максимальной связной открытой компоненте J области D:',
                        pretty(family['representative'],task.get('variable','x'))+' + C_J']
            lines.append('Константы на разных исходных компонентах независимы.')
        if plan.get('chart') in ('exponential_coordinate','tangent_half_angle_coordinate') and 'inner_coordinate' in plan:
            p=result['compilation']
            lines.append('Замена t = '+pretty(p['inner_coordinate'],task.get('variable','x'))+' приводит к интегралу от '+pretty(p['rational_differential'],'t')+'.')
            if p.get('seam',{}).get('kind')=='continuous_join':
                lines.append('На общей границе соседних карт пределы первообразной согласованы прибавлением постоянной. Производная там равна исходной функции по теореме Лагранжа.')
            elif p.get('seam'):lines.append('Каждая граница карты уже исключена из исходной области.')
        elif result.get('compilation',{}).get('theorem')=='method.real_radical_coordinate':
            p=result['compilation'];v=task.get('variable','x')
            lines.append('Замена '+pretty(p['coordinate'],v)+' даёт рациональный дифференциал '+pretty(p['rational_differential'])+'.')
            lines.append('Образ каждой допустимой ветви проверен по исходным корням и знаменателям.')
            lines.extend(p['argument'])
        elif result.get('compilation',{}).get('argument') and result.get('schema')=='linear-primitive/v1':
            lines.extend(result['compilation']['argument'])
        elif result.get('schema')=='linear-primitive/v1' and result.get('compilation'):
            for term in result['compilation']['terms']:
                lines.append('Постоянный множитель '+pretty(term['coefficient'])+'. Первообразная для '+pretty(term['kernel'],task.get('variable','x'))+' равна '+pretty(term['primitive'],task.get('variable','x'))+'.')
        if result.get('proposal'):
            from integrals import kernel_symbol
            recipe=result['proposal']['recipe'];names=result['compilation']['source_parameters'];variable=task.get('variable','x')
            if recipe.get('method')=='factor_parts':
                lines.extend(factor_parts_lines(result))
            elif recipe.get('method')=='ostrogradsky_reduction':
                lines.append('Сравнение коэффициентов выделяет производную рациональной функции H = '+pretty(recipe['rational_part'],variable)+'.')
                lines.append('Разность f − H′ равна '+pretty(recipe['remainder'],variable)+'. Знаменатель этой правильной дроби свободен от кратных корней.')
            elif recipe.get('method')=='rational_decomposition':
                lines.append('Разложение подынтегрального выражения по известным первообразным')
                for term in recipe['terms']:
                    w=freeze(term['weight'])
                    lines.append('∫ ('+pretty(m.mul(w,freeze(term['integrand'])),variable)+') d'+variable+
                                 ' = '+pretty(m.mul(w,freeze(term['primitive'])),variable)+' + C')
            elif recipe.get('method')=='product_to_sum':
                lines.append('По формулам произведения синусов и косинусов получаем '+recipe['expanded_integrand']+'.')
                lines.append('Интегрируем сумму по членам. При нулевой частоте соответствующее слагаемое постоянно.')
            elif recipe.get('method')=='quadratic_canonical_form':
                a,b,c=recipe['coefficients']
                lines.append('Берём u = '+recipe['coordinate']+' и Q = '+recipe['quadratic']+'.')
                lines.append('Выделение квадрата даёт 4·('+pretty(a)+')·Q = ('+recipe['centered_numerator']+')² + ('+pretty(recipe['discriminant_complement'])+').')
                lines.append('После замены числитель в дифференциале имеет вид ('+pretty(recipe['derivative_weight'])+')·dQ + ('+pretty(recipe['constant_weight'])+')·du.')
                lines.append('Применяем табличную первообразную для полученного квадрата. Производная результата равна исходному выражению на каждой компоненте.')
            elif recipe.get('method')=='trigonometric_power_reduction':
                a,b=recipe['sine_power'],recipe['cosine_power']
                lines.append(f"Положим t = {recipe['angle']}. Интегрируем sin(t)^{a} · cos(t)^{b} с множителем {recipe['coefficient']} / ({recipe['slope']}).")
                if recipe['rule']=='even_recurrence':
                    lines.append('Из производной sin(t)^(m−1) cos(t)^(n+1) следует (m+n) I(m,n) = (m−1) I(m−2,n) − sin(t)^(m−1) cos(t)^(n+1).')
                    lines.append('Для чистой степени косинуса n I(0,n) = (n−1) I(0,n−2) + sin(t) cos(t)^(n−1), с I(0,0) = t.')
                else:
                    lines.append('Подстановка u = '+recipe['substitution']+' использует sin²(t)+cos²(t)=1.')
                    if 'kernel_task' in recipe:lines.append('После подстановки раскладываем рациональное выражение '+recipe['kernel_task']['integrand']+'.')
                lines.append('Дифференцирование первообразной проверено на исходной области.')
            elif recipe.get('method')=='finite_polynomial_parts':
                lines+=['Метод: конечное интегрирование по частям','P = '+pretty(m.parse(recipe['raw_polynomial'],variable,names),variable),'Ядро: '+pretty(m.parse(recipe['kernel'],variable,names),variable),'Число слагаемых: '+str(len(recipe['terms']))]
                for k,term in enumerate(recipe['terms']):lines.append('T_'+str(k)+' = '+pretty(term,variable))
                if result['status']=='SOLVED':lines.append('Проверено F′ = f на всей исходной области D.')
            else:
                if recipe.get('method')=='learned_differential':
                    lines.append('Используем обобщённую пару функции и производной из проверенных доказательств.')
                lines+=['Подстановка ξ = '+pretty(m.parse(recipe['u'],variable,names),variable),
                        'Производная ξ′ = '+pretty(recipe['inner_derivative']['value'],variable),
                        'Множитель: '+pretty(m.parse(recipe['coefficient'],None,names)),
                        'K(ξ) = '+pretty(m.parse(recipe['kernel'],kernel_symbol(task),names),'ξ'),
                        ('Первообразная H(ξ) = ' if recipe.get('method')=='learned_differential' else 'Табличная первообразная H(ξ) = ')+pretty(m.parse(recipe['H'],kernel_symbol(task),names),'ξ'),
                        'Подынтегральное выражение = множитель · ξ′ · K(ξ).']
        if result.get('reason'):
            lines.append(result['reason'])
            lines.extend(a['method']+' / '+a['stage']+' — '+a['reason'] for a in result.get('plan_attempts',[]) if 'reason' in a)
        if 'child_result' in result:lines+=['','ПРОВЕРКА ПРОИЗВОДНОЙ',report(result['child_result'],library)]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='unsupported-goal-run/v1':
        return 'НЕЗАВЕРШЁННАЯ ЦЕЛЬ\nВид: '+str(task.get('kind'))+'\n'+result['reason']+'\n'
    if result.get('schema')=='parametric-curve-derivatives/v1':
        from tasks import guard_source
        lines=['Производные параметрической кривой',str(task.get('coordinates')),result['status']]
        v=result.get('value')
        if v is None:return '\n'.join(lines+[result.get('reason','')])
        if 'derivative_at_parameter_point' in v:
            lines.extend('При подходе '+('слева' if side=='left' else 'справа')+
                         ' параметрическая абсцисса имеет скорость '+pretty(slope)+'.'
                         for side,_,slope,_ in result['compilation']['horizontal_branches'])
            lines.append('Скорости различаются. Пределы разностного отношения по абсциссе совпадают и равны '+pretty(v['derivative_at_parameter_point'])+'.')
            return '\n'.join(lines)
        if v.get('zero_horizontal_velocity')=='polynomial_extension':
            plan=result['compilation']
            lines.append('Коэффициенты многочлена от абсциссы '+', '.join(map(pretty,plan['polynomial_in_horizontal_coordinate']))+'.')
            lines.extend('Производная порядка '+str(k)+' равна '+pretty(a)+'.' for k,a in zip(task['orders'],v['ordered_values']))
            lines.append('Нечётная степень в абсциссе сохраняет однозначность и в стационарной точке.')
            return '\n'.join(lines)
        while 'split_parameter' in v:
            a=v['split_parameter'];lines.append('При '+a+' = 0 абсцисса постоянна. Далее '+a+' ≠ 0.');v=v['nonzero']
        if v['regular_domain']=='empty':return '\n'.join(lines+['Абсцисса постоянна. Локальной ветви над интервалом x нет.'])
        lines.append('На ветвях, где '+', '.join(map(guard_source,v['regular_domain']))+', применяем d/dx = (1/x′(t)) d/dt.')
        lines.extend('Производная порядка '+str(k)+' равна '+pretty(a)+'.' for k,a in zip(task['orders'],v['ordered_values']))
        why={'nonzero_vertical_velocity':'при x′ = 0 вертикальная скорость отлична от нуля',
             'one_sided_branches_at_a_strict_coordinate_extremum':'при x′ = 0 абсцисса имеет строгий локальный экстремум. Каждая сторона параметра задаёт свою ветвь с односторонней производной по x',
             'vertical_displacement_of_lower_order_than_horizontal':'при x′ = 0 либо y′ ≠ 0, либо x″ = 0 и y″ ≠ 0'}
        lines.append('На исходной кривой '+why[v['zero_horizontal_velocity']]+'.')
        for k,a in zip(task['orders'],v.get('one_sided_at_turn',[])):
            lines.append('В точке разворота односторонняя производная порядка '+str(k)+(' отсутствует как конечная.' if a is None else ' равна '+pretty(a)+'.'))
        return '\n'.join(lines)
    if result.get('schema')=='implicit-graph-values/v1':
        lines=['Производные неявного графика',str(task['relation'])+' = 0',result['status']]
        if result.get('value') is None:return '\n'.join(lines+[result.get('reason','')])
        value=result['value']
        def describe(g):
            if 'split_parameter' in g:
                p=g['split_parameter']
                return ['При '+p+' = 0',*describe(g['zero']),'При '+p+' ≠ 0',*describe(g['nonzero'])]
            rows=[]
            if 'regular_condition' in g:rows.append('На исходных ветвях с ненулевой величиной '+pretty(g['regular_condition'][1])+' получаем следующие производные.')
            for order,d in zip(task['orders'],g['ordered_values']):rows.append('Производная порядка '+str(order)+' равна '+pretty(d)+'.')
            if g.get('on_zero_pivot'):rows.append('При нулевой производной по зависимой координате производная по абсциссе не существует как конечная.')
            return rows
        lines.extend(describe(value['graph']))
        for p in value['point_values']:
            lines.append('В точке '+', '.join(k+' = '+str(v) for k,v in p['point'].items())+' получаем '+', '.join(map(pretty,p['ordered_values']))+'.')
        return '\n'.join(lines)
    if result.get('schema')=='integer-step-derivative/v1':
        value=result.get('value')
        if value is None:return result['status']+'\n'+result.get('reason','')
        return ('Между целыми уровнями ступенчатый множитель постоянен. Производная равна '+pretty(value['elsewhere'])+
                '. В каждом целом уровне синусоидальный множитель убывает по крайней мере квадратично. Производная там равна нулю.\n')
    if result.get('schema')=='exact-form/v1':
        lines=['Полный дифференциал',result['status']]
        if result.get('value') is None:lines.append(result.get('reason',''))
        else:
            value=result['value'];lines.append('Потенциал F = '+pretty(value['potential'])+' + C')
            for v,g in zip(task['variables'],result['compilation']['verified_gradient']):lines.append('∂F/∂'+v+' = '+pretty(g))
            if 'line_integral' in value:lines.append('Интеграл по пути равен '+pretty(value['line_integral'])+'.')
        return '\n'.join(lines)
    if result.get('schema')=='uniform-series-majorant/v1':
        val=result.get('value');parts=['Функциональный ряд с членом '+str(task.get('term')),result['status']]
        if val is None:return '\n'.join(parts+[result.get('reason','')])+'\n'
        if argument:=result['compilation'].get('argument'):
            parts.extend([argument] if isinstance(argument,str) else argument)
            parts.append('Сходимость равномерная.' if val['uniform'] else 'Сходимость неравномерная.')
            if 'absolute_at_every_point' in val:
                parts.append('Во всех точках сходимость абсолютная.' if val['absolute_at_every_point'] else
                             'Условная сходимость при x = '+', '.join(pretty(e) for e in val['conditional_points'])+'.')
            return '\n'.join(parts)+'\n'
        if val.get('criterion')=='uniform_finite_prefix':
            witness=m.render(freeze(result['compilation']['potential']))
            return '\n'.join(parts+['На исходном промежутке члены неотрицательны. Ищем разность соседних значений '+witness+' и проверяем её равенство данному члену.',
                'Сокращение внутренних слагаемых даёт частичную сумму. Для неё проверяем поточечный предел и равномерную ошибку.',
                report(result['children'][0]['proof'],library)])
        if val.get('criterion')=='uniform_summation_by_parts':
            plan=result['compilation']
            return '\n'.join(parts+['За период длины '+str(plan['period'])+' сумма числителей равна нулю.',
                'Знаменатель положителен и возрастает по индексу. Суммирование по частям даёт для любого конечного хвоста с номера n верхнюю оценку модуля '+m.render(freeze(plan['uniform_tail_from_index']))+'.',
                'Эта оценка стремится к нулю одновременно во всех точках исходного промежутка.'])
        p=m.render(val['majorant_decay_power']);C=m.render(val['majorant_coefficient'])
        parts+=['Во всей исходной области |u_n(x)| ≤ ('+C+')/n^('+p+').',
                'При p = '+p+' > 1 числовой хвост после N ограничен интегралом C·N^(1−p)/(p−1).',
                'По признаку Вейерштрасса ряд сходится абсолютно и равномерно.']
        return '\n'.join(parts)+'\n'
    if result.get('schema')=='uniform-sequence/v1':
        from uniform import uniform_report
        return uniform_report(result)
    if result.get('schema')=='function-bounds/v1':
        goal=task.get('goal',task)
        lines=[str(goal.get('function',goal.get('expression','')))+' на '+str(goal.get('given_domain',goal.get('domain',goal.get('ambient_interval','')))),result['status']]
        labels={'infimum':'Нижняя грань','supremum':'Верхняя грань','minimum':'Минимум','maximum':'Максимум','oscillation':'Колебание'}
        for key,item in (result.get('value') or {}).items():
            lines.append(labels[key]+' = '+pretty(item['value']) if item['exists'] else labels[key]+' отсутствует')
        if result.get('reason'):lines.append(result['reason'])
        return '\n'.join(lines)
    if result.get('schema')=='level-set-family/v1':
        from level_sets import family_report
        return family_report(result)
    if (result.get('compilation') or {}).get('theorem')=='method.external_axis_centroid_sweep':
        p=result['compilation'];measure=next(iter(result['value'].values()))
        return '\n'.join(['Центр образующей окружности или круга лежит на расстоянии '+pretty(p['distance'])+' от оси.',
            'Радиус '+pretty(p['radius'])+' не превосходит этого расстояния, поэтому внутренность не пересекает ось.',
            'При полном обороте мера '+pretty(p['generator_measure'])+' умножается на длину пути центра. Получаем '+pretty(measure)+'.'])
    if result.get('schema')=='solid-sections/v1':
        from plane_domains import solid_sections_report
        return solid_sections_report(result)
    if result.get('schema')=='surface-metric-patch/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];w=result['value']
        return ('Касательная к параллели перпендикулярна касательной к меридиану. Скорость вдоль меридиана равна '+
                pretty(p['meridian_speed'])+', а по долготе — '+pretty(p['orbit_radius'])+'. Для интеграла по меридиану получаем первообразную '+
                pretty(p['primitive'])+'. Каждое угловое направление учитывается один раз; стянутая параллель имеет нулевую площадь.\n'+
                'Площадь участка = '+pretty(w.get('patch_area',w.get('surface_area')))+
                ('\nПлощадь всей поверхности = '+pretty(w['whole_torus_area']) if 'whole_torus_area' in w else ''))
    if result.get('schema')=='plane-curve-radius/v1':
        if result['status']!='SOLVED':return result['status']+'\n'+result.get('reason','')
        p=result['compilation'];w=result['value'];regular=w['finite_where']
        rho=pretty(w['radius']) if w['radius'] is not None else 'конечных значений нет'
        intro=('Берём касательную, перпендикулярную градиенту исходного уровня.' if p['representation']=='implicit' else
               'Дифференцируем радиус в подвижном полярном базисе.' if p['representation']=='polar' else
               'Дифференцируем обе координаты и вычисляем определитель скорости и ускорения.')
        return (intro+' Квадрат нормы равен '+pretty(regular['speed_squared_positive'])+
                ', ориентированный числитель кривизны равен '+pretty(regular['turning_nonzero'])+
                '. На регулярных точках с ненулевой кривизной радиус равен '+rho+
                '. При нулевой кривизне на регулярной ветви радиус бесконечен. '+{
                    'regular_everywhere':'Скорость всюду отлична от нуля.',
                    'ordinary_cusps_at_zero_speed':'При нулевой скорости в невырожденном масштабе вторая и третья производные подтверждают заострение.',
                    'globally_constant_turning':'Если постоянный определитель равен нулю, образ лежит на прямой либо является точкой.',
                    'degenerate_conic_if_turning_zero':'Ненулевой числитель гарантирует регулярность уровня; вырожденное уравнение обрабатывается отдельно.'
                }[w['singular']['type']])
    if result.get('schema')=='curve-metric/v1':
        name='Длина дуги' if task['kind']=='curve_arc_length' else 'Площадь поверхности вращения'
        if result.get('value') is None:return name+'\n'+result.get('reason','')
        plan=result['compilation'];lines=[name,'Промежуток интегрирования от '+str(plan['interval'][0])+' до '+str(plan['interval'][1])]
        for ordinate,value in plan.get('ordinate_definitions',{}).items():
            lines.append('Ордината конца дуги определяется графиком: '+ordinate+' = '+pretty(freeze(value))+'.')
        if plan['argument']=='monotone_radius_chart':
            lines.append('Каждый положительный радиус встречается один раз. С учётом dφ/dr элемент длины равен '+pretty(plan['radius_metric'])+' dr; на открытых концах интеграл имеет предел.')
        elif plan['argument']=='unbounded_radial_variation':
            lines.append('При приближении к углу '+pretty(plan['pole'])+' модуль радиуса неограничен. Длина превосходит изменение модуля радиуса.')
        for piece in plan['line_integral']:lines.append('Плотность по параметру равна '+pretty(piece['pullback']))
        return '\n'.join(lines+[name+' = '+pretty(next(iter(result['value'].values())))])
    if result.get('schema')=='bounded-section-measure/v1':
        label='Площадь' if task['kind']=='area_bounded_by_curves' else 'Объём вращения'
        lines=[label,result['status']]
        if result.get('value') is None:return '\n'.join(lines+[result.get('reason','')])
        p=result['compilation']
        if p.get('theorem')=='method.power_profile_rotation':
            lines.append(f"Подставляем x = {pretty(p['positive_intersection'])} · t^{p['substitution_power']}. Степени профилей определяют порядок радиусов на 0<t<1.")
            lines.append('Кратность после вращения равна '+str(p['half_profile_copies'])+'.')
        for piece in result['compilation']['sections']:
            a,b=piece['bounds']
            if 'lower' in piece and 'upper' in piece:
                lines.append('Сечение от '+pretty(a)+' до '+pretty(b)+' с границами '+pretty(piece['lower'])+' и '+pretty(piece['upper']))
            else:lines.append('Параметр контура меняется от '+pretty(a)+' до '+pretty(b)+'.')
            lines.append('Интеграл плотности '+pretty(piece['density'])+' равен '+pretty(piece['integral']))
        return '\n'.join(lines+[label+' = '+pretty(next(iter(result['value'].values())))])
    if result.get('schema')=='geometric-moments/v1':
        if result.get('value') is None:return result.get('reason',result['status'])
        p=result['compilation']
        lines=['Интегрируем расстояние, его квадрат или координату по исходной геометрической мере.']
        for c in p.get('computations',[]):
            lines.append('Интеграл '+pretty(c['density'])+' равен '+pretty(c['value'])+'.')
        for k,v in result['value'].items():
            if isinstance(v,(tuple,list)) and v and isinstance(v[0],(tuple,list)):
                lines.append(k+' = ('+', '.join(map(pretty,v))+')')
            else:lines.append(k+' = '+pretty(v))
        return '\n'.join(lines)
    if result.get('schema')=='planar-domain/v1':
        from plane_domains import region_report
        return region_report(result)
    if result.get('schema')=='function-image/v1':
        spec=task['goal'];lines=['Множество значений '+spec['expression'],result['status']]
        if result.get('value') is None:return '\n'.join(lines+[result.get('reason','')])
        def print_intervals(pieces,show):
            return ' ∪ '.join(('[' if lc else '(')+show(a)+', '+show(b)+(']' if rc else ')') for a,b,lc,rc in pieces) or '∅'
        def input_endpoint(z):
            if isinstance(z,str):return pretty(z)
            if z[0]!='quadratic_real':return pretty(z)
            _,a,b,d=freeze(z)
            return pretty(m.add(a,m.mul(b,('sqrt',m.q(d)))))
        lines.append('Допустимые аргументы '+print_intervals(result['value']['domain'][1],input_endpoint))
        lines.append('Множество значений '+print_intervals(result['value']['image_intervals'],pretty))
        return '\n'.join(lines)+'\n'
    if result.get('schema') in ('global-chain-search-run/v1','natural-real-domain/v1'):
        spec=task.get('goal',task);domain=result['schema']=='natural-real-domain/v1'
        lines=(['Область определения',str(spec.get('expression',''))] if domain else
               ['НЕРАВЕНСТВО НА ВСЕЙ ДЕЙСТВИТЕЛЬНОЙ ПРЯМОЙ','',spec['left']+' '+spec['relation']+' '+spec['right']])
        lines.append('Статус: '+result['status'])
        if domain and isinstance(result.get('value'),dict):
            from plane_domains import preimage_description
            return '\n'.join(lines+preimage_description(result['value']))+'\n'
        def endpoint(e):
            if isinstance(e,str):return pretty(e)
            _,a,b,d=freeze(e)
            return pretty(m.add(a,m.mul(b,('sqrt',m.q(d)))))
        if result.get('value') is not None:
            intervals=freeze(result['value'])[1]
            answer=' ∪ '.join(('[' if lc else '(')+endpoint(a)+', '+endpoint(b)+(']' if rc else ')') for a,b,lc,rc in intervals)
            lines.append('Множество решений: '+(answer or '∅'))
            if domain:
                plan=result['compilation']
                lines.append(f"Проверены исходные условия ({len(plan['raw_conditions'])}), открытые интервалы ({len(plan['open_cells'])}) и граничные точки ({len(plan['point_membership'])}).")
                return '\n'.join(lines)+'\n'
            certificate=next(n['value'] for n in result['proof']['nodes'] if n['goal'][0]=='real_partition')
            lines.append('Вся прямая разбита по '+str(len(certificate[4]))+' критическим точкам на '+str(len(certificate[5]))+' открытых ячеек.')
            lines.append('На каждой ячейке установлены ветвь модулей и знак; граничные точки проверены отдельно.')
        if result.get('reason'):lines.append(result['reason'])
        lines.append('Повторная проверка: '+str(result.get('verification')))
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='point-derivative-chain-run/v1':
        lines=['ПРОИЗВОДНАЯ ПО ТЕОРЕМЕ ЛАГРАНЖА','',
               'Функция: '+task['function'],'Статус: '+result['status'],
               'Для каждой стороны построена H(τ); τ стремится к 0 справа.']
        if result['status'] in ('SOLVED','DOES_NOT_EXIST'):
            lines.append('Непрерывность H в 0, локальная производная H′ и её конечный предел подтверждены общей цепочкой.')
        for side in result['sides']:
            lines+=['','Сторона исходной переменной: '+side['side'],
                    'H(τ) = '+pretty(side['normalized_expression'])]
            if side['status']=='SOLVED':
                lines+=['Предел H′(τ): '+pretty(side['value']),
                        'Производная по исходной переменной с учётом знака: '+pretty(side['value_in_original_variable']),
                        'Проверено узлов: '+str(len(side['proof']['nodes']))]
            else:lines.append('Обязательство не завершено: '+side['status'])
        lines+=['','Общие правила: '+', '.join(used_rules(result)),
                'Повторная проверка: '+str(result.get('verification'))]
        return '\n'.join(lines)+'\n'
    if result.get('schema')=='compiled-calculus-run/v1':
        lines=['ПРОИЗВОДНАЯ ПО ОБЩЕМУ ПРАВИЛУ','',
               'Функция: '+task['function'],'Вид цели: '+task['kind'],'Статус: '+result['status']]
        if result.get('value') is not None:lines.append('Получено: '+pretty(result['value'],task.get('variable','x')))
        compilation=result.get('compilation',{})
        if task['kind']=='differentiate':
            lines.append('Достаточная область формулы: '+('; '.join(compilation.get('display_sufficient_domain',[])) or 'дополнительных ограничений к исходным условиям нет'))
            lines.append('Граничные обязательства: '+str(result.get('boundary_obligations',compilation.get('boundary_obligations'))))
        lines.append('Область определения функции: '+('; '.join(compilation.get('display_natural_domain',[])) or 'без дополнительных синтаксических ограничений'))
        lines.append('Проверка требования метода: '+str(result.get('method_status')))
        lines.append('Повторная проверка: '+str(result.get('verification')))
        if result.get('reason'):lines.append(result['reason'])
        if 'child_result' in result:lines+=['','ПОСТРОЕННОЕ ОБОСНОВАНИЕ ПРОИЗВОДНОЙ','',report(result['child_result'],library)]
        return '\n'.join(lines)+'\n'
    lines=['АВТОМАТИЧЕСКОЕ СОСТАВЛЕНИЕ РЕШЕНИЯ','',
           'Выражение: '+task['expression'],f"Переменная: {task.get('variable','x')}; подход: {task.get('approach')}",
           'Статус: '+result['status'],'']
    if task.get('parameters'):
        lines.append('Фиксированные действительные параметры: '+', '.join(p if isinstance(p,str) else p['symbol'] for p in task['parameters']))
    if task.get('parameter_conditions'):
        lines.append('Исходные условия: '+'; '.join(task['parameter_conditions']))

    def walk(node):
        if node.get('assumptions'):
            lines.append('Условия: '+'; '.join(a['symbol']+(' = 0' if a['relation']=='zero' else ' != 0') for a in node['assumptions']))
        if 'cases' in node:
            lines.append('Разбиение на исчерпывающие случаи для постоянного параметра '+node['split_symbol']+'.')
            for child in node['cases']:walk(child)
            return
        kind=task.get('kind',task.get('task_type'))
        if node['status']=='SOLVED' and kind in GERM_GOALS:
            point=task.get('approach',{}).get('point','0');var=task.get('variable','x')
            coordinate='1/'+var if point in ('+inf','-inf') else var+' − ('+str(point)+')'
            if kind=='finite_expansion':
                degree=task['degree'];polynomial=m.ZERO
                for k,c in enumerate(node['value']):
                    if freeze(c)!=m.ZERO:polynomial=m.add(polynomial,m.mul(freeze(c),m.power(('v','delta'),k)))
                lines.append('При Δ = '+coordinate+' разложение равно '+pretty(polynomial,'Δ')+f' + o(|Δ|^{degree}).')
            elif node['value'][0]=='zero_germ':
                lines.append('Функция тождественно равна нулю в рассматриваемой проколотой окрестности.')
            else:
                _,p,c=node['value']
                lines.append('При Δ = '+coordinate+' функция эквивалентна ('+pretty(c)+') · Δ^('+pretty(p)+').')
        elif task.get('approach',{}).get('mode')=='magnitude_infinity' and node['status'] in ('SOLVED','DOES_NOT_EXIST'):
            for label,s in zip(('−∞','+∞'),node['sides']):
                lines.append('При подходе к '+label+' '+('исходная действительная область пуста в некоторой окрестности.' if s['status']=='DOMAIN_ERROR' else 'предел равен '+pretty(s['value'])+'.'))
            lines.append('Общего предела нет.' if node['status']=='DOES_NOT_EXIST' else 'Предел на исходной области равен '+pretty(node['value'])+'.')
        elif node['status']=='SOLVED':lines.append('Ответ: '+pretty(node['value']))
        else:lines.append('Результат ветви: '+node['status'])
        for side in node.get('sides',[]):
            side_label={'right':'справа','left':'слева'}[side['side']]
            if side['context']['point'] in ('+inf','-inf'):side_label='при подходе к '+str(side['context']['point'])
            lines.extend(['', 'Сторона: '+side_label,
                          'Замена: '+task.get('variable','x')+' = '+pretty(side['normalization']['substitution'])+', τ -> 0+.'])
            if side['normalization']['sequence_restriction']:
                lines.append('Предел функции ограничен на последовательность положительных целых аргументов.')
            proof=side.get('proof')
            if not proof:
                lines.append('Цепочка не завершена. Открытые постоянные условия: '+str(side['unresolved_constant_guards']));continue
            if side['status']=='SOLVED':lines.append('Исходная область и ненулевые делители выбранных преобразований подтверждены.')
            for n in proof['nodes']:
                if n['goal'][0]=='real_identity_step':
                    signs=[pretty(s['ask'][1])+' > 0' for s in n['steps'] if s.get('ask',[None])[0]=='positive']
                    condition=' при '+', '.join(signs) if signs else ''
                    lines.append('Применено тождество'+condition+'. '+pretty(n['goal'][1])+' = '+pretty(n['value'])+'.')
                if n['goal'][0] in ('rewrite','bound'):
                    before,after=pretty(n['goal'][1]),pretty(n['value'])
                    if n['goal'][0]=='bound':lines.append(library.by_id[n['rule']]['label']+': |'+before+'| <= '+after)
                    elif before!=after:lines.append(library.by_id[n['rule']]['label']+': '+before+' -> '+after)
            for n in proof['nodes']:
                if n['rule']=='limit.rational':
                    witness=next(s['outputs'] for s in n['steps'] if s.get('op')=='rational_leading')
                    power,coefficient=witness
                    if m.freeze(coefficient)==m.ZERO:
                        lines.append('Исходное рациональное выражение определено в проколотой окрестности и тождественно равно нулю.')
                    else:
                        lines.append('Младшие ненулевые члены исходного рационального выражения: '+
                                     pretty(n['goal'][1])+' ~ '+pretty(coefficient)+' · τ^('+pretty(power)+').')
                    lines.append('Отсюда предел: '+pretty(n['value']))
                if n['rule'] in ('germ.sin','germ.cos','germ.sqrt','germ.cbrt','germ.asin','germ.atan','germ.exp','germ.ln','germ.sinh','germ.cosh'):
                    lines.append(library.by_id[n['rule']]['label']+': '+pretty(n['goal'][1])+' = '+short_expansion(n['value']))
                if n['rule'] in ('slow_germ.log_power','slow_germ.ln'):
                    lines.append('При υ=-1/ln(τ)->0+: '+pretty(n['goal'][1])+' = '+short_expansion(n['value']).replace('τ','υ'))
            for n in proof['nodes']:
                if n['rule'] in ('limit.germ','limit.slow_germ'):
                    kind='slow_germ' if n['rule']=='limit.slow_germ' else 'germ'
                    expansion=next(s['value'] for s in n['steps'] if s.get('ask',[None])[0]==kind)
                    displayed=short_expansion(expansion,1)
                    if kind=='slow_germ':displayed=displayed.replace('τ','υ')
                    lines.append('Составлено: '+pretty(n['goal'][1])+' = '+displayed)
                    lines.append('Отсюда предел: '+pretty(n['value']))
            lines.append('Проверено узлов выбранного обоснования: '+str(len(proof['nodes'])))
            lines.append('Операций поиска: '+str(side['stats']['jobs']))
        lines.append('')

    if result['status']=='UNSUPPORTED':lines.append(result['reason'])
    else:walk(result)
    lines.extend(['Для краткости в тексте оставлены первые члены; полные коэффициенты, остатки и зависимости сохранены в JSON.',
                  'Использованные общие правила: '+', '.join(used_rules(result)),
                  'Повторная проверка: '+str(result.get('verification')),
                  'Библиотека: '+result['library_hash'],
                  'Источник правил: '+str(result.get('knowledge_source',library.origin)),
                  'Проверка относительна принятому математическому базису. В библиотеку задачи и ответы не добавлялись.'])
    return '\n'.join(lines)+'\n'


_retry_source_additions=ContextVar('retry_source_additions',default=True)


def solve_composed(task,library,limits,order,*,preferred_charts=()):
    from tasks import ADDITIVE_ORDER_CHARTS, additive_order_options
    kind=composed_kind(task);schema,pending=COMPOSED_GOALS[kind]
    start=perf_counter();base={'schema':schema,'task':task,'library_hash':library.hash,'operation_hash':version(),
        'status':pending,'value':None,'verification':{'status':'incomplete'}}
    is_sum=kind=='finite_sum_or_product_sequence_limit'
    def request(role,t,statuses=('SOLVED',)):
        child=solve(t,library,limits,order);r['children'].append({'role':role,'proof':child})
        if child.get('status') not in statuses:
            raise Unsupported(role+' remains '+child['status']+(': '+str(child['reason']) if is_sum and child.get('reason') else ''))
        verify(child,library,expected_task=t);return child
    exceptions=(Unsupported,ResourceBound,ArithmeticError,KeyError,TypeError,ValueError)
    try:
        if preferred_charts:options=preferred_charts
        elif is_sum:options=sum_limit_strategies(task,library)
        elif kind in ('sequence_liminf_limsup','sequence_range_and_envelopes') and library.data.get('elementary_proof_transitions'):
            options=(None,'exact_integer_phase')
        elif kind in ('plane_measure','uniform_continuity'):options=integral_charts(task,library)
        else:options=(None,*integral_charts(task,library))
        if not preferred_charts and not is_sum and _retry_source_additions.get():
            options=(*options,*additive_order_options(task,kind))
    except exceptions as exc:
        return dict(base,children=[],reason=str(exc),elapsed_seconds=round(perf_counter()-start,6))
    attempts=[dict(strategy=s,status='not_tried') for s in options] if is_sum else []
    initial=None;failures={};deferred=None
    prefer_local_chart=kind=='iterated_integral' and 'rationalizing_substitution' in options
    for i,chart in enumerate(options):
        if deferred is not None and chart!='rationalizing_substitution':continue
        r={**base,'children':[]}
        try:
            if chart in ADDITIVE_ORDER_CHARTS:
                mark=_retry_source_additions.set(False)
                try:plan,value=compose_goal(task,library,request,chart)
                finally:_retry_source_additions.reset(mark)
            else:plan,value=compose_goal(task,library,request,chart)
            r.update(compilation=plan,value=value,status='SOLVED')
            if is_sum:
                attempts[i]['status']='proved'
                r['search_attempts']=attempts
            r['verification']=verify(r,library,expected_task=task)
            if prefer_local_chart and chart is None and len(r['children'])==1:
                child=r['children'][0]['proof'].get('compilation',{})
                if child.get('chart')=='radical_conic' or (child.get('chart')=='lifted_scales' and 'inverse' in child):
                    # A bounded chart can certify the change of variable directly on the original fiber.
                    deferred=r
                    continue
            break
        except exceptions as exc:
            if is_sum:attempts[i].update(status='open',reason=str(exc))
            if initial is None:initial=dict(base,children=r['children'],reason=str(exc))
            elif not is_sum:failures[chart]=str(exc)
    else:
        if deferred is not None:r=deferred
        else:
            r=initial or dict(base,children=[],reason='Нет применимого перехода для этой цели и заданного метода')
            if is_sum:r['search_attempts']=attempts
            if failures:r['chart_attempts']=failures
    r['elapsed_seconds']=round(perf_counter()-start,6);return r


def solve_partial_bundle(task,library,limits,order):
    from tasks import compile_partial_bundle,partial_child_task,partial_component_value,ordinary_kernel_plan,ordinary_kernel_children,ordinary_kernel_values
    start = perf_counter(); result = {'schema':'partial-derivative-bundle/v1','task':task,
        'library_hash':library.hash,'operation_hash':version(),'knowledge_source':library.origin,
        'status':'PARTIAL_DERIVATIVES_PENDING','value':None,'children':[],'partial_values':(),
        'verification':{'status':'incomplete'}}
    try:
        if library.data.get('task_compilers',{}).get('partial_derivatives')!='coordinate_section_derivatives': raise Unsupported('Partial derivative bundle is not admitted')
        try:kernel=ordinary_kernel_plan(task,library.data['partial_bundle_contract'])
        except (Unsupported,KeyError,TypeError,ResourceBound):kernel=None
        if kernel:
            children=[solve(t,library,limits,order) for t in ordinary_kernel_children(kernel)]
            if all(c['status']=='SOLVED' for c in children):
                compact={**result,'schema':'ordinary-kernel-derivatives/v1','status':'SOLVED','compilation':kernel,
                         'children':children,'value':ordinary_kernel_values(kernel)}
                compact.pop('partial_values')
                try:compact['verification']=verify(compact,library,expected_task=task)
                except (ValueError,Unsupported,ResourceBound):pass
                else:
                    compact['elapsed_seconds']=round(perf_counter()-start,6)
                    return compact
        plan = compile_partial_bundle(task,library.data['partial_bundle_contract']); result['compilation'] = plan; values = {}
        for index in plan['indices']:
            child = None
            try:
                child = solve(partial_child_task(plan,index,values),library,limits,order)
                verify(child,library,expected_task=partial_child_task(plan,index,values))
                value = partial_component_value(plan,index,child)
            except (Unsupported,ValueError,KeyError,TypeError,ResourceBound) as exc:
                result['pending'] = {'index':index,'status':'COMPONENT_SCOPE_OR_PROOF_PENDING','child_status':child.get('status') if child else 'CHILD_REJECTED','reason':str(exc),'diagnostic_only':True,'child':child}; break
            result['children'].append(child); values[index] = value
        result['partial_values'] = tuple(values.items())
        if len(values)==len(plan['indices']): result.update(status='SOLVED',value=tuple(values[p] for p in plan.get('selected_paths',plan['indices'])))
        result['verification'] = verify(result,library,expected_task=task)
    except (Unsupported,KeyError,TypeError,ResourceBound) as exc: result['reason'] = str(exc)
    result['elapsed_seconds'] = round(perf_counter()-start,6)
    return result


def solve_original_table(task,library,limits):
    from tasks import compile_original_table
    from verify import verify_original_table
    start=perf_counter();plan=compile_original_table(task);ctx=plan['context'];goal=plan['goal']
    if library.data.get('pointwise_table_contract')!='original_variable_then_arbitrary_fixed_point':raise Unsupported('Pointwise table context not admitted')
    engine=Engine(library,ctx,limits).run([goal],lambda e:bool(e.answers(goal)))
    result={'schema':'original-table-derivative/v1','task':task,'library_hash':library.hash,
            'operation_hash':version(),'plan':plan,'status':'OPEN','value':None,'proof':None,'stats':engine.stats()}
    if engine.answers(goal):
        answer=engine.answers(goal)[0];formula=freeze(answer['value'])
        at=m.substitute(formula,{('v',ctx['variable']):('s',ctx['point_symbol'])})
        if m.constant_defined(at,ctx):
            result.update(status='FORMULA_ON_SUFFICIENT_DOMAIN' if plan['compilation']['boundary_obligations']=='pending' else 'SOLVED',
                formula=formula,value=at,proof={'root':answer['proof'],'nodes':engine.export_nodes([answer['proof']])})
            result['verification']=verify_original_table(result,library,task)
    result['elapsed_seconds']=round(perf_counter()-start,6)
    return result


def solve_series_comparison(task,library,limits,order):
    from tasks import series_candidates,compile_series_comparison,series_comparison_conclusion
    start=perf_counter();result={'schema':'series-comparison-run/v1','task':task,'library_hash':library.hash,'operation_hash':version(),
        'knowledge_source':library.origin,'status':'SERIES_PENDING','value':None,'attempts':[],'verification':{'status':'incomplete'}}
    try:
        if library.data.get('task_compilers',{}).get('series_convergence')!='positive_p_series_comparison':raise Unsupported('Series comparison is not admitted')
        for power in series_candidates(task,library):
            attempt={'criterion' if isinstance(power,str) else 'power':power,'diagnostic_only':True};result['attempts'].append(attempt)
            try:
                plan=compile_series_comparison(task,power)
                child=solve(plan['scaled_limit_task'],library,limits,order)
                attempt['status']=child['status']
                verify(child,library,expected_task=plan['scaled_limit_task']);conclusion=series_comparison_conclusion(plan,child)
            except (Unsupported,ValueError,KeyError,TypeError,ResourceBound) as exc:
                attempt.setdefault('status','INAPPLICABLE');attempt['reason']=str(exc);continue
            result.update(compilation=plan,child_result=child,**conclusion)
            result['verification']=verify(result,library,expected_task=task);break
        else:result['reason']='No admitted series test decided the requested classification'
    except (Unsupported,KeyError,TypeError,ValueError,ResourceBound) as exc:result['reason']=str(exc)
    result['elapsed_seconds']=round(perf_counter()-start,6)
    return result


def solve_euler_homogeneity(task,library,limits,order):
    from tasks import compile_euler_homogeneity,euler_conclusion
    start=perf_counter();result={'schema':'euler-homogeneity-run/v1','task':task,'library_hash':library.hash,'operation_hash':version(),
        'knowledge_source':library.origin,'status':'EULER_PENDING','value':None,'verification':{'status':'incomplete'}}
    try:
        if library.data.get('task_compilers',{}).get('euler_homogeneity')!='structural_scaling_and_euler_identity':raise Unsupported('Euler method is not admitted')
        plan=compile_euler_homogeneity(task);result['compilation']=plan
        child=solve(plan['partial_task'],library,limits,order);result['child_result']=child
        verify(child,library,expected_task=plan['partial_task']);result['value']=euler_conclusion(plan,child)
        result['status']='SOLVED';result['verification']=verify(result,library,expected_task=task)
    except (Unsupported,ValueError,TypeError,KeyError,ResourceBound) as exc:result.update(status='EULER_PENDING',value=None,reason=str(exc))
    result['elapsed_seconds']=round(perf_counter()-start,6)
    return result
