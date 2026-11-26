"""Replay the selected general-method proofs; never imports the search engine."""
from contextvars import ContextVar
from model import canonical,digest,freeze,match,instantiate,ZERO,Unsupported
from polynomial import ResourceBound
class VerificationError(ValueError): pass


def require(ok,message):
    if not ok:raise VerificationError(message)

import expressions as m
from operations import GERM_GOALS,compute,version,germ_conclusion
from tasks import COMPOSED_SCHEMAS,COMPOSED_GOALS,composed_kind,compose_goal,compile_derivative,compile_point_derivative_side,derivative_conclusion,compile_global_task


# Nested task compilers use the same verifier. A requesting reader can identify
# exactly which proof objects were replayed, including those of inner tasks.
_checked_dags = ContextVar('checked_dags', default=None)


def verify_with_dags(result, library):
    checked = {}
    token = _checked_dags.set(checked)
    try:
        return verify(result, library), checked
    finally:
        _checked_dags.reset(token)


def replay_dag(proof,library,ctx,root_goals):
    """Replay one shared DAG and bind named roots to exact expected goals.

    root_goals maps proof-role -> expected predicate tuple. Artifact/library,
    operation-version and task-compilation bindings remain the caller's job.
    """
    require(isinstance(proof,dict),'Неверный контейнер обоснования')
    require(isinstance(root_goals,dict) and bool(root_goals),'Нет объявленных корней обоснования')
    raw=proof.get('nodes')
    require(isinstance(raw,(list,tuple)),'Нет списка шагов обоснования')
    require(all(isinstance(n,dict) and type(n.get('id')) is str for n in raw),'Неверные идентификаторы шагов')
    nodes={n['id']:n for n in raw}
    require(len(nodes)==len(raw),'Повтор шага')
    require(all(k=='nodes' or k in root_goals or v is None for k,v in proof.items()),'Необъявленный корень обоснования')
    active,checked=set(),set()

    def check_steps(node):
        # Pause at a requested premise until its proof has been checked.
        goal,value=freeze(node['goal']),freeze(node['value'])
        try:library.validate(goal,ctx,value,True)
        except Unsupported as exc:raise VerificationError(str(exc)) from exc
        require(node['context']==digest(ctx),'Несовместимые предположения')
        require(node['rule'] in library.by_id,'Нет точной версии правила')
        require(library.rule_allowed(node['rule'],ctx),'Rule is not admitted in this context')
        rule=library.by_id[node['rule']]
        require(node['revision']==library.revisions[node['rule']],'Изменена версия правила')
        env={};require(match(rule['head'],goal,env),'Правило не подходит')
        require(len(rule['steps'])==len(node['steps']),'Изменены предпосылки')
        for expected,actual in zip(rule['steps'],node['steps']):
            if 'ask' in expected:
                question=instantiate(expected['ask'],env)
                require(canonical(question)==canonical(actual.get('ask')),'Подменена подзадача')
                child_id=actual['proof']
                yield child_id
                child=nodes[child_id]
                require(canonical(child['goal'])==canonical(question),'Чужое основание подзадачи')
                require(canonical(child['value'])==canonical(actual['value']),'Подменён ответ подзадачи')
                require(match(expected.get('bind',True),freeze(child['value']),env),'Несогласованная подстановка')
            else:
                inputs=instantiate(expected.get('args',[]),env)
                require(actual.get('op')==expected['op'],'Подменена операция')
                require(canonical(inputs)==canonical(actual['inputs']),'Изменены входы операции')
                output=freeze(actual['outputs'])
                require(any(canonical(output)==canonical(value) for value in library.compute(expected['op'],inputs,ctx)),
                        'Неверное вычисление или невыполненное условие')
                require(match(expected.get('bind',[]),output,env),'Несогласованный выход операции')
        require(canonical(instantiate(rule['result'],env))==canonical(value),'Подменено заключение')

    def replay(root):
        finished=object()
        stack=[(None, iter((root,)))]
        while stack:
            parent,steps=stack[-1]
            child=next(steps,finished)
            if child is finished:
                stack.pop()
                if parent is not None:
                    active.remove(parent)
                    checked.add(parent)
                continue
            require(type(child) is str and child in nodes,'Нет шага обоснования')
            require(child not in active,'Циклическое обоснование')
            if child not in checked:
                active.add(child)
                stack.append((child,check_steps(nodes[child])))
        return nodes[root]

    values,root_nodes={},{}
    for role,expected_goal in root_goals.items():
        require(type(role) is str and role in proof and proof[role] is not None,'Нет требуемого корня обоснования')
        root=replay(proof[role])
        require(canonical(root['goal'])==canonical(expected_goal),'Корень относится к другой исходной цели')
        values[role]=freeze(root['value']);root_nodes[role]=root['id']
    require(checked==set(nodes),'Посторонние шаги в обосновании')
    observed = _checked_dags.get()
    if observed is not None:
        observed[id(proof)] = (proof, ctx, root_nodes)
    return {'values':values,'root_nodes':root_nodes,'checked_nodes':len(checked)}


def expansion_witness_sources(rule,value,steps,witnesses):
    # Follow only germ premises supplying this value. Domain guards cannot certify the method.
    direct=rule['id'] in witnesses and value[2]!='exact'
    children=(actual['proof'] for template,actual in zip(rule['steps'],steps) if template.get('ask',[None])[0]=='germ')
    return direct,children


def matches_limit_method(library,method,root,nodes):
    if method['root_rule'] is not None and nodes[root]['rule']!=method['root_rule']:return False
    witnesses=method.get('expansion_rules',[])
    if not witnesses:return True
    # Only follow the germ values supplying the selected extraction, never domain guards.
    pending=[root];seen=set()
    while pending:
        key=pending.pop()
        if key in seen:continue
        seen.add(key);node=nodes[key]
        direct,children=expansion_witness_sources(library.by_id[node['rule']],node['value'],node['steps'],witnesses)
        if direct:return True
        pending.extend(children)
    return False


def verify_side(result,library,task,assumptions):
    require(result['library_hash']==library.hash,'Изменилась библиотека общих правил')
    require(result['operation_hash']==version(),'Изменились вычислительные операции')
    expansion=task.get('kind',task.get('task_type')) in GERM_GOALS
    require(type(result['order']) is int and 1<=result['order']<=(24 if expansion else 12),'Недопустимая точность')
    try:ctx,method=library.limit_context(task,assumptions,result['side'],result['order'])
    except Unsupported as exc:raise VerificationError(str(exc)) from exc
    expression,normalization=m.normalized(task,ctx,result['side'])
    require(canonical(ctx)==canonical(result['context']),'Подменён контекст')
    require(canonical(normalization)==canonical(result['normalization']),'Неверная замена переменной')
    require(canonical(expression)==canonical(result['normalized_expression']),'Подменено нормированное выражение')
    require(result['status'] in ('SOLVED','DOMAIN_ERROR'),'У незавершённого поиска нет полного обоснования')
    goals={'root':('germ' if expansion else 'limit',expression),'domain':('defined',expression)} if result['status']=='SOLVED' else {'root':('undefined',expression)}
    checked=replay_dag(result['proof'],library,ctx,goals)
    value=checked['values']['root']
    if result['status']=='SOLVED':
        if method:
            proof=result['proof']
            require(matches_limit_method(library,method,checked['root_nodes']['root'],{n['id']:n for n in proof['nodes']}),
                    'The selected answer does not demonstrate the required limit method')
        if expansion:
            value=germ_conclusion(value,ctx)
            require(value is not None,'The jet cannot certify the requested coefficients and remainder')
        else:require(m.scalar_limit_conclusion(value,ctx) is not None,'Неопределённый конечный ответ')
        require(canonical(value)==canonical(result['value']),'Подменён ответ')
        require(checked['values']['domain'] is True,'Не подтверждена исходная область')
    else:
        require(value is True and result.get('value') is None,'Нет основания нарушения области или заявлено значение на пустой стороне')
    return checked['checked_nodes']


def same_value(a,b):
    a,b=freeze(a),freeze(b)
    if a in ('+inf','-inf') or b in ('+inf','-inf'):return a==b
    difference=m.simplify(m.add(a,m.neg(b)))
    if difference==ZERO:return True
    if difference[0] not in ('add','div'):return False
    try:
        numerator,_=m.rational_form(difference)
        return not m.trig_reduce(numerator,complete=True)
    except ResourceBound:return False


def check_scalar_claim(value,ctx,library):
    value=freeze(value)
    try:library.validate_value('limit_value',value,ctx)
    except Unsupported as exc:raise VerificationError(str(exc)) from exc
    require(m.scalar_limit_conclusion(value,ctx) is not None,'Заявленный ответ не определён при исходных условиях')


def same_side_answer(a,b,ctx):
    if ctx.get('leading_asymptotic_term'):
        a,b=freeze(a),freeze(b)
        return a==b or isinstance(a,tuple) and isinstance(b,tuple) and len(a)==len(b)==3 and a[:2]==b[:2] and same_value(a[2],b[2])
    if 'expansion_degree' not in ctx:return same_value(a,b)
    return isinstance(b,(tuple,list)) and len(a)==len(b)==ctx['expansion_degree']+1 and all(
        same_value(x,y) for x,y in zip(a,b))


def different_value(a,b,ctx):
    a,b=freeze(a),freeze(b)
    if a in ('+inf','-inf') or b in ('+inf','-inf'):return a!=b
    return m.nonzero(m.add(a,m.neg(b)),ctx)


def derivative_compilation(task):
    try:return compile_derivative(task)
    except (Unsupported,KeyError,TypeError) as exc:
        raise VerificationError('Не поддержаны исходная производная или её ограничения') from exc


def verify(result,library,expected_task=None):
    if result.get('schema') in ('partial-derivative-bundle/v1','ordinary-kernel-derivatives/v1'):
        require(composed_kind(result['task']) not in ('differential_operator','higher_derivative'),'В доказательстве отсутствует печатный конечный вывод')
    if result.get('schema')=='comparison-rule-dag/v1':
        from ray_proofs import verify_comparison
        return verify_comparison(result,library,expected_task)
    if result.get('schema')=='rational-graph-run/v1':
        from graphs import verify_graph
        return verify_graph(result,library,expected_task)
    if result.get('schema')=='ordinary-kernel-derivatives/v1':return verify_ordinary_kernel(result,library,expected_task)
    if result.get('schema') in COMPOSED_SCHEMAS:return verify_composed(result,library,expected_task)
    if result.get('schema')=='partial-derivative-bundle/v1':return verify_partial_bundle(result,library,expected_task)
    if result.get('schema')=='original-table-derivative/v1':return verify_original_table(result,library,expected_task)
    if result.get('schema')=='series-comparison-run/v1':return verify_series_comparison(result,library,expected_task)
    if result.get('schema')=='euler-homogeneity-run/v1':return verify_euler_homogeneity(result,library,expected_task)
    if result.get('schema')=='integral-chain-run/v1':
        from integrals import verify_integral
        return verify_integral(result,library,expected_task)
    if result.get('schema')=='global-chain-search-run/v1':
        require(result['library_hash']==library.hash,'Изменилась глобальная библиотека')
        require(result['operation_hash']==version(),'Изменились глобальные операции')
        task=result['task']
        if expected_task is not None:require(canonical(task)==canonical(expected_task),'Подменена глобальная исходная задача')
        compilation=compile_global_task(task,library)
        require(canonical(compilation)==canonical(result['compilation']),'Подменена область или исходное утверждение')
        require(canonical(compilation['context'])==canonical(result['context']),'Подменён глобальный контекст')
        require(canonical(compilation['goal'])==canonical(result['goal']),'Подменена глобальная цель')
        require(result['status']=='SOLVED','Незавершённая глобальная цепочка')
        checked=replay_dag(result['proof'],library,compilation['context'],{'root':compilation['goal']})
        if 'applied_proof_plan' in result:
            plans=library.proof_plans.get(compilation['goal'][0],())
            require(any(p.key==result['applied_proof_plan'] and p.describes(result['proof']) for p in plans),
                    'Указанный составной приём не соответствует проверенной цепочке')
        require(canonical(checked['values']['root'])==canonical(result['value']),'Подменён глобальный вывод')
        scope='global_real_line_partition_and_complete_boundary_checks'
        if compilation['goal'][0] in ('series_classification','cauchy_series_classification'):scope='absolute convergence with a summable majorant under the printed method and every original term defined'
        if compilation['goal'][0]=='series_classification' and checked['values']['root'].get('criterion')=='power_progression_thresholds':
            scope='ordinary and absolute convergence thresholds on the original real parameter domain and integer indices'
        if compilation['goal'][0]=='parameter_series_sets':scope='parameter domain and absolute and conditional convergence, including both geometric endpoints'
        if compilation['goal'][0]=='cartesian_field_identity':scope='cartesian_component_identity_where_the_used_component_derivatives_exist'
        if compilation['goal'][0]=='cartesian_components':scope='all requested Cartesian components by ordered product and coordinate differentiation'
        if compilation['goal'][0]=='finite_sum_identity':scope='all_original_integer_indices_and_every_premise_of_the_selected_proof'
        if compilation['goal'][0]=='real_equal':scope='equality_at_every_point_of_the_declared_nonempty_real_domain'
        if compilation['goal'][0]=='bounded_on':scope='bounded_on_the_entire_original_closed_ray'
        if compilation['goal'][0] in ('continuous_on','all_continuous'):
            scope=('continuity_of_all_requested_functions_on_the_whole_declared_closed_interval'
                   if compilation['context']['source_domain']=='closed_real_interval'
                   else 'continuity_of_all_requested_functions_on_an_arbitrary_common_real_subset')
        return {'status':'passed','checked_nodes':checked['checked_nodes'],'scope':scope}
    if result.get('schema')=='point-derivative-chain-run/v1':
        require(result['library_hash']==library.hash,'Изменилась библиотека производной в точке')
        require(result['operation_hash']==version(),'Изменились операции производной в точке')
        task=result['task']
        if expected_task is not None:require(canonical(task)==canonical(expected_task),'Подменена исходная производная')
        require(task.get('method_requirement')!='from_definition','Мост Лагранжа не выполняет требование определения')
        require(library.data.get('task_compilers',{}).get(task.get('kind'))=='derivative_definition_or_mvt','Не объявлен метод Лагранжа')
        compilation=derivative_compilation(task)
        require(canonical(compilation)==canonical(result['compilation']),'Подменена функция или точка производной')
        require(compilation['point_defined'],'Не установлена исходная функция в точке')
        order=result['order'];require(type(order) is int and 1<=order<=12,'Недопустимая точность производной')
        require([s['side'] for s in result['sides']]==['right','left'],'Подменены стороны производной')
        total=0;values=[]
        for actual,side in zip(result['sides'],('right','left')):
            expected=compile_point_derivative_side(compilation,side,order)
            require(all(canonical(actual.get(k))==canonical(v) for k,v in expected.items()),'Подменена замена или цель стороны производной')
            require(actual['library_hash']==library.hash and actual['operation_hash']==version(),'Изменилась основа стороны производной')
            require(actual['status']=='SOLVED','Не доказана конечная производная с одной стороны')
            checked=replay_dag(actual['proof'],library,expected['context'],{'root':expected['goal']})
            value=checked['values']['root'];total+=checked['checked_nodes']
            require(canonical(value)==canonical(actual['value']),'Подменён предел производной H')
            require(bool(compute('finite',[value],expected['context'])),'Нет конечного определённого значения производной')
            signed=('mul',m.q(-1),value) if side=='left' else value
            require(canonical(signed)==canonical(actual['value_in_original_variable']),'Подменён знак левой производной')
            values.append(signed)
        if result['status']=='SOLVED':
            check_scalar_claim(result['value'],expected['context'],library)
            require(all(same_value(v,result['value']) for v in values),'Стороны не дают заявленную производную')
        else:
            require(result['status']=='DOES_NOT_EXIST' and result.get('value') is None and
                    different_value(values[0],values[1],result['sides'][0]['context']),
                    'Не доказано различие конечных односторонних производных')
        return {'status':'passed','checked_nodes':total,'scope':'two_sided_point_derivative_mvt_and_signed_local_derivative_limits'}
    if result.get('schema')=='compiled-calculus-run/v1':
        require(result['library_hash']==library.hash,'Изменилась библиотека общего метода')
        require(result['operation_hash']==version(),'Изменилось построение задачи')
        task=result['task']
        if expected_task is not None:require(canonical(task)==canonical(expected_task),'Подменена исходная цель')
        require(library.data.get('task_compilers',{}).get(task.get('kind')) in ('derivative_definition','derivative_definition_or_mvt'),'Нет объявленного общего метода')
        compilation=derivative_compilation(task)
        require(canonical(compilation)==canonical(result['compilation']),'Подменено определение или область производной')
        require(compilation['point_defined'],'Не установлена определённость функции в точке')
        child=result['child_result']
        child_task=task if child.get('schema') in ('point-derivative-chain-run/v1','original-table-derivative/v1') else compilation['compiled_limit_task']
        checked=verify(child,library,expected_task=child_task)
        conclusion=derivative_conclusion(task,compilation,child)
        require(all(canonical(result.get(k))==canonical(v) for k,v in conclusion.items()),'Подменены формула, условия или полнота решения')
        return {**checked,'scope':'compiled_calculus_and_selected_child_proof','method_status':conclusion['method_status']}
    require(result['schema']=='unified-chain-search-run/v4','Неверный формат результата')
    require(result['library_hash']==library.hash,'Изменилась библиотека общих правил')
    require(result['operation_hash']==version(),'Изменились вычислительные операции')
    task=result['task']
    if expected_task is not None:require(canonical(task)==canonical(expected_task),'Подменена исходная задача')
    require(task.get('kind',task.get('task_type','limit')) in ('limit',*GERM_GOALS),'Вид цели не соответствует цепочке предела')
    total=0
    def directions(assumptions):
        try:return m.limit_directions(task,assumptions,library.data.get('magnitude_infinity_contract'))
        except Unsupported as exc:raise VerificationError(str(exc)) from exc

    def walk(node,assumptions):
        nonlocal total
        require(canonical(node['assumptions'])==canonical(assumptions),'Подменены условия ветви')
        require(node['status']=='SOLVED' or node.get('value') is None,'Значение не доказано для всей этой ветви')
        if 'cases' in node:
            symbol=node['split_symbol'];ctx,_=directions(assumptions)
            require(symbol in ctx['parameters'],'Разбиение по недопустимому параметру')
            require(not any(a['symbol']==symbol for a in assumptions),'Повторное разбиение параметра')
            require(len(node['cases'])==2,'Неполное разбиение случаев')
            for child,relation in zip(node['cases'],('zero','nonzero')):
                walk(child,assumptions+[{'symbol':symbol,'relation':relation}])
            require(node['status']=='SOLVED_CASES' and all(c['status'] in ('SOLVED','SOLVED_CASES','DOMAIN_ERROR','DOES_NOT_EXIST') for c in node['cases']),
                    'Незавершённые случаи выданы за решение')
            return
        ctx,targets=directions(assumptions)
        require([s['side'] for s in node['sides']]==[side for _,side in targets],'Неполная или подменённая сторона подхода')
        for side,(target,_) in zip(node['sides'],targets):total+=verify_side(side,library,target,assumptions)
        live=node['sides']
        if task.get('approach',{}).get('mode')=='magnitude_infinity':
            live=[s for s in live if s['status']!='DOMAIN_ERROR']
            require(bool(live)==(node['status']!='DOMAIN_ERROR'),'Magnitude limit must use every unbounded end of the original domain')
        if node['status']=='DOMAIN_ERROR':
            require(any(s['status']=='DOMAIN_ERROR' for s in node['sides']),'Не обосновано нарушение области')
        else:
            require(all(s['status']=='SOLVED' for s in live),'Одна из сторон не решена')
            if node['status']=='SOLVED':
                if task.get('kind',task.get('task_type')) in GERM_GOALS:
                    require(canonical(node['sides'][0]['value'])==canonical(node['value']),'Substituted expansion coefficients')
                else:check_scalar_claim(node['value'],ctx,library)
                require(all(same_side_answer(s['value'],node['value'],s['context']) for s in live),'Стороны не дают заявленный ответ')
            else:
                require(node['status']=='DOES_NOT_EXIST' and len(live)==2 and task.get('kind',task.get('task_type')) not in GERM_GOALS and different_value(live[0]['value'],live[1]['value'],ctx),
                        'Не доказано различие односторонних пределов')

    walk(result,[])
    return {'status':'passed','checked_nodes':total,'scope':'applications_and_case_coverage_relative_to_admitted_general_basis'}


def verify_composed(r,lib,expected_task):
    kind=composed_kind(r['task'])
    require(COMPOSED_GOALS.get(kind,(None,None))[0]==r['schema'],'The task does not match its proof schema')
    is_sum=kind=='finite_sum_or_product_sequence_limit'
    extra={'search_attempts'} if is_sum else set()
    require(not set(r)-extra-{'schema','task','library_hash','operation_hash','children','status','value','verification','compilation','elapsed_seconds'},'Unknown composed claim')
    require(r['library_hash']==lib.hash and r['operation_hash']==version() and r['status']=='SOLVED','Incomplete or changed composition')
    require(expected_task is None or canonical(expected_task)==canonical(r['task']),'Source goal changed')
    children=iter(r['children']);count=0;child_check={}
    def request(role,t,statuses=('SOLVED',)):
        nonlocal count,child_check
        child=next(children,None);require(child is not None and set(child)=={'role','proof'} and child['role']==role,'Missing or changed child obligation')
        proof=child['proof'];require(proof['status'] in statuses,'Incomplete child claim')
        child_check=verify(proof,lib,expected_task=t)
        count+=child_check['checked_nodes'];return proof
    require(isinstance(r.get('compilation'),dict),'Missing composition plan')
    if order:=r['compilation'].get('source_addition_order'):
        from tasks import ADDITIVE_ORDER_CHARTS
        require(order in ADDITIVE_ORDER_CHARTS and not is_sum,'Unknown additive source rewrite')
        try:plan,value=compose_goal(r['task'],lib,request,order)
        except (Unsupported,ResourceBound,ArithmeticError,KeyError,TypeError,ValueError) as exc:raise VerificationError(str(exc)) from exc
        require(next(children,None) is None and canonical(plan)==canonical(r['compilation']) and canonical(value)==canonical(r['value']),
                'Additive source order or normalized conclusion changed')
        require(child_check.get('complete') is not False,'The normalized proof left conditions open')
        return {**child_check,'checked_nodes':count+1,'additive_order_checked':True}
    if kind=='source_parameter_integral' and r['task'].get('method_requirement')=='use_given_integral':
        from quadrature import check_given_integral_derivative
        require(r['children']==[],'Unexpected child in the parameter derivative proof')
        try:
            count=check_given_integral_derivative(r['task'],r['compilation'],r['value'])
        except (Unsupported,ResourceBound,ArithmeticError,KeyError,TypeError,ValueError) as exc:
            raise VerificationError(str(exc)) from exc
        return dict(status='passed',complete=True,checked_nodes=count,
                    scope='source identity, derivative recurrence, local endpoint domination and requested integral')
    chart=r['compilation'].get('chart') if kind in ('iterated_integral','potential_from_differential','exact_differential_endpoints','restricted_function_image','linear_primitive','greens_boundary_integral') else None
    try:
        if kind=='uniform_continuity':
            from tasks import integral_charts
            chart=r['compilation'].get('chart')
            require(chart in integral_charts(r['task'],lib),'Missing continuity transition')
        if kind=='plane_measure':
            from tasks import integral_charts
            chart=r['compilation'].get('strategy')
            require(chart in integral_charts(r['task'],lib),'The selected transition does not support this goal and method')
        if is_sum:
            from tasks import sum_limit_strategies
            chart=r['compilation']['strategy']; options=sum_limit_strategies(r['task'],lib)
            log=r['search_attempts'];selected=options.index(chart)
            require(isinstance(log,list) and len(log)==len(options),'Unbound search alternatives')
            for i,(s,row) in enumerate(zip(options,log)):
                status='open' if i<selected else 'proved' if i==selected else 'not_tried'
                require(isinstance(row,dict) and row.get('strategy')==s and row.get('status')==status
                        and set(row)==({'strategy','status','reason'} if status=='open' else {'strategy','status'})
                        and (status!='open' or isinstance(row['reason'],str)),'Invalid search log or selected strategy')
        plan,val=compose_goal(r['task'],lib,request,chart,saved=r['compilation'])
    except (Unsupported,ResourceBound,ArithmeticError,KeyError,TypeError,ValueError) as exc:raise VerificationError(str(exc)) from exc
    end=object()
    require(next(children,end) is end and canonical(plan)==canonical(r['compilation']) and canonical(val)==canonical(r['value']),'Plan, domain or conclusion changed')
    if kind=='inverse_definition_derivative':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan['verified_boundaries']),
                    scope='original difference quotient, defining inverse identity, and every source boundary')
    if kind=='elementary_taylor_limit':
        proof=plan['singular_series_proofs'];sides=sum(len(c['sides']) for c in proof.get('cases',[proof]))
        return dict(status='passed',complete=True,checked_nodes=count+sides,
                    scope='authorized elementary expansions on each original signed side')
    if kind in ('functional_primitive','defined_riemann_integral'):
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                    scope='original quantified conditions, partition or functional identity, and every requested conclusion')
    if kind=='source_definite_trace':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                    scope='whole original interval, signed endpoint traces, admissible joins and the requested convergence or value')
    if kind=='source_endpoint_limit' or kind=='improper_integral' and plan.get('theorem')=='method.reciprocal_log_moment':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                    scope='original one-sided domain, uniform remainder or endpoint estimates, and verified limit or integral')
    if kind in ('elementary_proof','source_integral_transform','source_surface_field','source_spatial_moment',
                'source_geometric_domains'):
        if kind=='source_geometric_domains' and plan.get('theorem')=='method.certified_graph_intersections':
            return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                        scope='source graph intersections, complete real branch coverage and exact interval brackets',
                        verified_mathematical_obligations=[plan['verified_method']])
        scopes={
            'elementary_proof':'original hypotheses, complete requested outputs and exact reductions',
            'source_integral_transform':'source kernel, transform normalization, convergence domain and verified child obligations',
            'source_surface_field':'original geometric coverage, orientation, and verified field or integral obligations',
            'source_spatial_moment':'original spatial bounds, chart or sections, and all requested moment obligations',
            'source_geometric_domains':'original geometric domain, all branches and requested analytical or numerical conclusions',
        }
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument'])+1,scope=scopes[kind])
    if kind=='indefinite_integral_recurrence':
        return dict(status='passed',complete=True,checked_nodes=len(plan['argument']),
                    scope='original index conditions, differential identity and real domain of the recurrence')
    if kind in ('explicit_cauchy_series','certified_series_prefix'):
        return dict(status='passed',complete=True,checked_nodes=count+2,
                    scope='original integer tail, exact bounds, stated method and sufficient cutoff or convergence class')
    if kind=='ordinary_series_proof':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                    scope='original integer lattice, domains, quantified parameter classes, stated method and full series conclusion')
    if kind=='abstract_series_theorem':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(val.get('majorants',())),
                    scope='given quantified sequences and separately checked comparison, cutoff or counterexample')
    if kind=='source_uniform_functional':
        return dict(status='passed',complete=True,checked_nodes=count+2,
                    scope='original interval and index, pointwise and uniform behavior or verified finite uniform error comparison')
    if kind=='source_series_algebra':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan.get('exact_coefficient_checks',())),
                    scope='integer index domain, analytic or uniform convergence, exact coefficient transformations and original method')
    if kind=='fourier_coefficient_relation':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan.get('phase_checks',())),
                    scope='original Fourier period and coefficient indices, transformation and normalization, zero mode and parameter domain')
    if kind=='interval_integral_proof':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                    scope='original integration interval, required cases and derived conditions of each transition')
    if kind=='source_vector_calculus':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument'])+1,
                    scope='source vector field, region or path, orientation and exact mathematical operator or stated theorem')
    if kind=='source_planar_composition':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument'])+1,
                    scope='source area, inverse chart, complete ordered fibers and every verified weight')
    if kind=='source_geometric_application':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument'])+1,
                    scope='source geometry, original domains and coverage, exact integration or fully specified physical model')
    if kind=='scalar_source_proof':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='complete scalar proof including original domains, directions, and symbolic cases')
    if kind=='polynomial_interpolation':
        return dict(status='passed',complete=True,checked_nodes=len(plan['nodes'])+1,
                    scope='all original nodes, degree or prescribed polynomial space, and requested evaluation or integral')
    if kind=='bernstein_approximation':
        return dict(status='passed',complete=True,checked_nodes=len(plan['rows'])+1,
                    scope='source sampling interval and integer order; verified finite binomial construction and requested simplification')
    if kind=='stirling_application':
        return dict(status='passed',complete=True,checked_nodes=len(plan['factorial_arguments'])+1,
                    scope='exact original reduction, positive factorial arguments, logarithmic Stirling terms and directed remainders')
    if kind=='product_and_approximation_claim':
        return dict(status='passed',complete=True,checked_nodes=len(plan['steps']),
                    scope='original mathematical hypotheses and complete proof or source-claim refutation')
    if kind=='local_geometry':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='the complete source domain and requested local geometric or Taylor obligations')
    if kind=='continuous_least_squares':
        from quadrature import verify_affine_gram
        try:verify_affine_gram(plan['bounds'],plan['gram'],plan['gram_form'])
        except Unsupported as exc:raise VerificationError(str(exc)) from exc
        return dict(status='passed',complete=True,checked_nodes=count+3,
                    scope='original interval and target, exact normal moments, positive Gram form and feasible global minimum')
    if kind=='source_global_extrema':
        return dict(status='passed',complete=True,checked_nodes=count+2,
                    scope='original objective and feasible set, exact global bounds and attainment')
    if kind=='source_parameter_integral':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['steps']),
                    scope='source integrand, every relevant improper end, original parameter region and permitted interchange')
    if kind=='improper_space_integrals':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['steps']),
                    scope='original multidimensional domains and all singular ends, independent exhaustion and required integral value')
    if kind=='multivariate_operator_proof':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='source-bound differential operator, regularity, and every printed mathematical result')
    if kind=='applied_extremum':
        return dict(status='passed',complete=True,checked_nodes=2+len(val['branches']),
                    scope='printed geometric condition, physical domain and global extremum with attained configurations or open boundary')
    if kind=='certified_numeric_approximation':
        return dict(status='passed',complete=True,checked_nodes=len(plan['steps'])+1,
                    scope='original real operations, rational Taylor remainder bounds, rounding error and requested absolute tolerance')
    if kind=='approximate_equation_roots':
        return dict(status='passed',complete=True,checked_nodes=count+1+sum(len(p['iterations']) for p in plan['brackets']),
                    scope='all original real roots, excluded poles, specified numerical method and certified absolute precision')
    if kind=='compute_limit' and 'growth_scale' in plan:
        return dict(status='passed',complete=True,checked_nodes=1+len(plan['growth_scale']['steps']),
                    scope='original expression, eventual domains and lexicographic growth scales')
    if kind=='solve_functional_equation':
        return dict(status='passed',complete=True,checked_nodes=len(plan['steps']),
                    scope='original group law, local regularity, all parameters, exceptional zero solution and converse')
    if kind=='fourier_expansion':
        if 'certificate' in plan:
            return dict(status='passed',complete=True,checked_nodes=len(plan['argument'])+1,
                        scope='source Fourier bounds, method, all harmonics and pointwise or integral interpretation')
        return dict(status='passed',complete=True,checked_nodes=sum(map(len,plan['primitives'].values()))+len(plan['pieces']),
                    scope='original Fourier interval, orthogonal basis, all coefficients and resonances, smooth pieces and one-sided limits')
    if kind=='complex_power_series_disk':
        return dict(status='passed',complete=True,checked_nodes=len(plan['factors'])+1,
                    scope='original positive integer indices, complex modulus of each coefficient factor, center, radius and open disk')
    if kind=='plane_measure':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='original bounded region, invertible chart on its interior, boundary measure, Jacobian and requested integral')
    if kind=='infinite_rational_product':
        if plan.get('theorem')=='method.wave_product_limit':
            return dict(status='passed',complete=True,checked_nodes=count+1,scope='original factor domain, finite induction without division, eventual division on nonzero angles, and both sides at zero')
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='original factor domain, zero factors, finite partial products or positive logarithmic comparison, and requested conclusion')
    if kind=='rectangular_grid_sums':
        return dict(status='passed',complete=True,checked_nodes=2+len(plan['power_prefixes'])+len(plan['corners']),
                    scope='source grid and prescribed tags or proven cell extrema, finite differences, sum and limit for positive integer mesh')
    if kind=='area_from_line_integral':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='simple positively oriented normalized boundary, affine pullback of the area form, full source trace and degeneracies')
    if kind=='function_sign_sets':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='three exact global relations of the same original expression on the same domain')
    if kind=='higher_derivative':
        return dict(status='passed',complete=True,checked_nodes=count,verified_order=plan['order'],
                    scope='successive ordinary derivative on the full original domain and every requested independent increment')
    if kind=='sided_derivatives':
        return dict(status='passed',complete=True,checked_nodes=count+len(val['cuts'])+len(val['cells']),
                    scope='full source domain and all requested ordinary, generalized and derivative limits on the specified sides')
    if kind=='power_series_boundary':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='all-index source domain, normalized coefficient growth, open region and each real endpoint')
    if kind=='parameter_improper_evaluation':
        steps=len(plan.get('terminal_frequencies',plan.get('modes',plan.get('dilations',[]))))
        return dict(status='passed',complete=True,checked_nodes=count+1+steps,scope='original finite and infinite ends, source restrictions, scale or moment identity, prescribed method and ordinary integral')
    if kind=='fourier_integral_representation':
        rows=plan.get('positive',plan)
        return dict(status='passed',complete=True,checked_nodes=2+sum(map(len,rows.get('primitives',{}).values())),
                    scope='original whole or reflected half-axis, both moments, every positive-frequency resonance, inversion and both jump traces')
    if kind=='infinite_power_series_expansion':
        return dict(status='passed',complete=True,checked_nodes=count+len(val['coefficients']),
                    scope='convergent analytic series equal to the source near its center, every coefficient and any requested full convergence set')
    if kind=='order_certificate':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['steps']),scope='original set or index assumptions, all endpoint or finite comparison steps')
    if kind in ('derivative_signs','printed_inequality'):
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['cells']) if kind=='derivative_signs' else count+len(val['claims']),
                    scope='full restricted real domain; sign of each open cell, endpoint coverage and every printed claim')
    if kind=='plane_geometry':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='original plane curves, source guards, coordinate jets, regular points and requested geometric conclusion')
    if kind=='derivative_proof':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument'])+len(plan.get('table_steps',())),
                    scope='original source method, domains, derivative rules, and exceptional point certificates')
    if kind=='real_function_proof':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                    scope='original real-function clauses, branch domains, and checked intermediate goals')
    if kind=='source_asymptotic_proof':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='full source parameters and original approaches, analytic or quantified proof replay and literal conclusion')
    if kind=='exact_ordinary_order':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['kernels'])+1,
                    scope='original real domain, finite affine derivative formulas and each requested ordinary order or differential')
    if kind=='measurement_uncertainty':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='initial measurement domain, exact endpoint error and first-order tolerance')
    if kind=='curve_contacts':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='source curve, point and all requested equations, contact orders or geometric constructions')
    if kind=='symbolic_order':
        return dict(status='passed',complete=True,checked_nodes=count+len(val['coefficients']),
                    scope='all positive integral orders on the original domain or at the requested center')
    if kind=='successive_composition':
        return dict(status='passed',complete=True,checked_nodes=count,verified_orders=plan['requested_orders'],
                    scope='source inner and outer smoothness and the requested coefficients of the Taylor composition')
    if kind=='discrete_global_extremum':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['integer_sign_runs']),
                    scope='exact sign of successive change on all positive integers and complete attaining index interval')
    if kind in ('finite_interval_integral','continuous_riemann_limit'):
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='continuous original finite interval, Newton–Leibniz primitives on each oriented component' if kind=='finite_interval_integral'
                    else 'original summand equals the uniform Riemann sample weight, continuous kernel, endpoint correction and exact integral')
    if kind=='real_root_count_isolation':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan['sturm_counts']),
                    scope='all distinct real roots; singleton exact roots, otherwise open rational isolating intervals')
    if kind in ('sequence_liminf_limsup','sequence_range_and_envelopes'):
        return {'status':'passed','complete':True,'checked_nodes':count+1+len(plan.get('family_reduction',{}).get('residue_proofs',())),
                'scope':'all original positive indices, exhaustive residue classes and their limits; requested global bounds from monotone branches'}
    if kind in ('potential_from_differential','exact_differential_endpoints'):
        if plan.get('period_obstruction'):
            return dict(status='passed',complete=True,checked_nodes=count+len(plan['argument']),
                        scope='local gradient, original punctured domain, and nonzero period')
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'entire gradient equals the given form on its source domain, including both endpoints when requested'}
    if kind=='first_and_second_total_differentials':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'C2 source function on its stated domain; contraction of every ordered derivative with independent coordinate increments'}
    if kind=='differential_coordinate_change':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='every prolongation on the regular coordinate chart; source domain and equivalent equation checked')
    if kind=='implicit_differential_identity':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='source flow invariants or vanishing stationary coefficients and every requested consequence')
    if kind in ('multivariate_extrema','constrained_extrema'):
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='all extrema on the original domain, including strictness and flat attained bounds')
    if kind=='implicitly_coupled_system':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='source equations, supplied point, regular implicit charts, every requested derivative and any proved inverse-graph obstruction')
    if kind in ('multivariable_limit','multivariate_continuity'):
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan.get('distinct_paths',[]))+len(plan.get('angular_denominator_certificates',[])),
                    scope='every requested joint, successive or directional assertion on the original domain with admissible paths and uniform bounds')
    if kind=='discontinuity_set':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan['guard_reductions']),
                    scope='every original definition condition, singular points in the closure, and exterior points')
    if kind=='compare_ordered_partials':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='equality of both independently differentiated ordered expressions on the source domain')
    if kind in ('formal_differential_identity','eliminate_arbitrary_functions'):
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan['checked_exceptional_sets']),
                    scope='printed operator or inferred differential relation, all function argument bindings, regular domain and each exceptional set')
    if kind=='euler_integral_evaluation':
        return dict(status='passed',complete=True,checked_nodes=count+1+len(plan['endpoint_conditions']),
                    scope='source integrand on the full open interval, substitution, both strict endpoint tests and requested Euler value')
    if kind=='sequence_term_at':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'original expression at the specified integer and parameter values, including its unsimplified divisors'}
    if kind in ('sequence_expression_limit','sequence_expression_nonzero','finite_product_identity','finite_product_limit'):
        scope={'sequence_expression_limit':'finite limit on a full tail of the original sequence',
               'sequence_expression_nonzero':plan.get('scope'),
               'finite_product_identity':'empty product and each original factor, before division',
               'finite_product_limit':'original factors, all real parameter branches and division only on the proved tail'}[kind]
        return {'status':'passed','complete':True,'checked_nodes':count+1,'scope':scope}
    if kind in ('finite_sum_context','contracting_power_expression_limit') and plan.get('domain_scope')=='eventually':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'for each fixed admissible parameter tuple, all sufficiently large integer indices; no assertion about earlier values'}
    if kind=='finite_sum_context':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'each sum on the original integer domain, raw outer divisors and the original final obligation and method'}
    if kind=='contracting_expression_nonzero' and plan.get('strategy')=='nonzero_limit':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'eventual strict sign of the original divisor for each fixed parameter tuple, from its finite nonzero limit'}
    if kind in ('contracting_integer_power_limit','contracting_expression_nonzero','contracting_power_expression_limit'):
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':{'contracting_integer_power_limit':'decay for each fixed real base of absolute value below one on the integer tail',
                         'contracting_expression_nonzero':'strict nonzero sign under the inherited parameter bounds for every original positive integer',
                         'contracting_power_expression_limit':'limits of the integer powers, validity of the original divisions and nonzero limiting divisors'}[kind]}
    if kind=='partial_sum_convergence':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'all pairs of sufficiently large original integer indices, absolute term comparison and vanishing uniform tail'}
    if kind=='finite_sum_bound':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'uncancelled domain and both coefficient inequalities for the supplied telescoping majorant'}
    if kind=='finite_sum_formula':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':'original domain and finite difference identity with its lower boundary and integer residue classes'}
    if kind=='finite_sum_or_product_sequence_limit':
        return {'status':'passed','complete':True,'checked_nodes':count+1,
                'scope':('original affine image between two proved envelopes with a common limit'
                         if chart=='bound' else 'verified original sample domain, reconstructed continuous kernel and integral'
                           if chart=='riemann' else 'original summation domain, verified finite difference, all integer residue classes and their endpoint limits')}
    if kind=='find_leading_term_and_order':
        return {'status':'passed','checked_nodes':count+1,'complete':True,
                'scope':'nonzero leading term with its remainder, relative order, and the original real approach'}
    if kind=='compute_limit':
        return {'status':'passed','complete':True,'checked_nodes':count+len(plan.get('family_reduction',{}).get('argument',())),
                'scope':'all source scalar limit directions, assumptions and returned parameter cases'}
    if kind=='integral_substitution_validity':
        return {'status':'passed','complete':True,'checked_nodes':count,'verified_branches':len(plan['geometry']['branches']),
                'scope':'original compact interval, oriented inverse branches, signed differentials and independent endpoint limits'}
    if kind=='root_linearization':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='universal positive-root difference quotient, source remainder or independently isolated numerical value')
    if kind=='linear_approximation':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='original requested argument, source domain and checked differential at the chosen center')
    if kind=='uniform_continuity':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='whole stated interval, original definition including endpoints, and every requested continuity property')
    if kind in ('quantifier_continuity','epsilon_delta_proof'):
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='original quantified neighborhood implication, its requested converse or local modulus, including declared example')
    if kind=='function_increment':
        return {'status':'passed','complete':True,'checked_nodes':count,'scope':'original endpoint values, finite displacement or checked instantaneous rate'}
    if kind=='exact_form':
        return {'status':'passed','complete':True,'checked_nodes':count,'verified_components':len(plan['verified_gradient']),
                'scope':'global gradient equality on the original domain and the endpoint theorem'}
    if kind=='improper_integral':
        if plan.get('theorem')=='method.indexed_euler_integrals':
            return dict(status='passed',complete=True,checked_nodes=len(plan['transformations']),
                        scope='original finite interval and integer domain, Euler expansion and removable singularities')
        if plan.get('theorem')=='method.improper_harmonic_moments':
            return dict(status='passed',complete=True,checked_nodes=1+len(plan['primitive']['modes']),
                        scope='original integrand, checked exponential-polynomial primitive and decay at infinity')
        scope=('independent symmetric cutoffs at each interior singularity and at the two infinities'
               if 'principal_value_exists' in val else 'ordinary one-sided integral on each component of the original real domain')
        return {'status':'passed','complete':True,'checked_nodes':count,'scope':scope}
    if kind in ('integral_reduction_family','oriented_boundary_integral'):
        scope=('integer-power recurrence, boundary terms and base integrals for every reachable residue'
               if kind=='integral_reduction_family' else 'signed boundary theorem on the full regular region and original smooth field')
        return {'status':'passed','checked_nodes':count,'complete':True,'scope':scope}
    if kind=='uniform_series_convergence':
        from uniform import UNIFORM_TAIL_THEOREMS
        if plan.get('theorem') in UNIFORM_TAIL_THEOREMS:
            return dict(status='passed',complete=True,checked_nodes=count+2,
                        scope='original index and domain, verified uniform tail bound or nonvanishing moving witness')
        if plan.get('theorem')=='method.uniform_rational_prefixes':
            return dict(status='passed',complete=True,checked_nodes=count+3+len(plan['source_sign_and_domain'])+len(plan['original_potential_domain']),
                        scope='all original abscissas and indices, nonnegative terms, telescoping identity, pointwise and uniform boundary errors')
        if plan.get('theorem')=='method.uniform_periodic_summation_by_parts':
            return dict(status='passed',complete=True,checked_nodes=count+len(plan['phase_values'])+4,
                        scope='original interval and start, periodic differences, positive decreasing amplitude, uniform Cauchy bound on every finite tail')
        return {'status':'passed','complete':True,'checked_nodes':count,'scope':'all original terms and a uniform numerical tail bound'}
    if kind=='uniform_sequence_convergence':
        return {'status':'passed','complete':True,'checked_nodes':count,'scope':'pointwise limit and limiting error supremum on the source interval'}
    if kind=='function_bounds':
        return {'status':'passed','checked_nodes':count,'complete':True,
                'scope':'extended bounds and endpoint attainment on the exact nonempty source image'}
    if kind=='implicit_derivative':
        return {'status':'passed','checked_nodes':count,'complete':True,
                'scope':'implicit function theorem, original source conditions and checked total derivatives on its regular graph'}
    if kind=='multivariate_taylor':
        return {'status':'passed','checked_nodes':count,'complete':True,
                'scope':'homogeneous components on the original multivariable neighborhood or exact global shifted identity'}
    if kind=='composite_function_differentiation':
        return {'status':'passed','checked_nodes':count,'complete':True,'scope':'ordered coordinate derivatives, original inner domain, and outer differentiability at the inner image'}
    if kind=='sampled_field_taylor':
        return {'status':'passed','complete':True,'checked_nodes':count,'scope':'all specified sampling weights and shifts, local smoothness, convergence only under analyticity'}
    if kind in ('integrate_by_series','power_series_quadrature'):
        return dict(status='passed',complete=True,checked_nodes=count+len(plan.get('integrated_terms',[]))+1,
                    scope='original integral, endpoint convergence, justified termwise integration and all requested error bounds')
    if kind=='series_numeric_approximation':
        return dict(status='passed',complete=True,checked_nodes=count+sum(map(len,plan['steps'])),
                    scope='original numerical target, fixed number of terms or prescribed reduction, rational enclosure and error')
    if kind=='series_sum':
        if plan.get('theorem') in ('method.generating_series_operators','method.abel_series_values',
                                  'method.geometric_antidifference','method.harmonic_series_values'):
            return dict(status='passed',complete=True,checked_nodes=count+1,
                        scope='original terms and integer start, certified coefficient identity and convergence on every stated branch')
        if plan.get('theorem')=='method.factorial_polynomial_series':
            return dict(status='passed',complete=True,checked_nodes=count+1,scope='original factorial indices, exact falling-factorial identity, absolutely convergent exponential series and omitted initial terms')
        if 'linear_limits' in plan:
            return dict(status='passed',complete=True,checked_nodes=count+1,scope='each summand has its own convergent infinite series with identical starting index and a common finite cutoff')
        if 'finite_prefix_limit' in plan:
            return {'status':'passed','checked_nodes':count,'complete':True,
                    'scope':'proved finite partial sum and common finite limit on every integer branch'}
        if 'partial_fractions' in plan:return {'status':'passed','checked_nodes':count,'complete':True,'scope':'original integer domain, exact partial fractions, and one common cutoff for every residue'}
        return {'status':'passed','checked_nodes':count,'complete':True,'scope':'original integer tail, exact antidifference identity, finite partial sums and endpoint limit'}
    if kind=='level_sets':
        return {'status':'passed','complete':True,'checked_nodes':count,'checked_level_cases':len(val['family']['families']),
                'checked_level_drawings':len(plan['drawn_levels']),'scope':'all real levels on the original domain'}
    if plan.get('theorem')=='method.external_axis_centroid_sweep':
        return dict(status='passed',complete=True,checked_nodes=count+1,theorem=plan['theorem'],scope='source circle, external or tangent axis, and one full sweep')
    if kind=='spatial_reduction':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='full source spatial domain, original density, required coordinates and ordered fiber integration')
    if kind=='cartesian_flux':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan['checks']),
                    scope=('continuous separable components and all six oriented box faces' if plan['theorem']=='method.opposite_face_flux'
                           else 'original field, boundary orientation and divergence theorem on the stated region'))
    if kind=='solid_sections':
        return dict(status='passed',complete=True,checked_nodes=count+1,theorem=plan['theorem'],
                    checked_scope='original solid, restrictions at each station and integrals of certified sections')
    if kind in ('bound_curve_integral','greens_boundary_integral'):
        return dict(status='passed',complete=True,checked_nodes=count+1,scope=(
            'unique affine coordinate inverse, both original geometric endpoints, oriented map and original field on the full arc'
            if kind=='bound_curve_integral' else 'single complete oriented circle traversal with the original field on the boundary'
            if chart=='direct_circle' else 'given region and its orientation, Green integral and each requested independent calculation'))
    if kind=='curve_metric':
        return dict(status='passed',complete=True,checked_nodes=count,scope='original curve domain, nonrepeating arc or swept surface and checked arc integral')
    if kind=='curve_curvature_radius':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='source level or parametrized branch, differential metric, absolute turning, zero curvature and certified singular cases')
    if kind=='surface_area':
        return dict(status='passed',complete=True,checked_nodes=count+1,scope='source meridian, metric and its primitive, multiplicity of the geometric patch including collapsed parallels and whole surface when required')
    if kind=='bounded_section_measure':
        return dict(status='passed',complete=True,checked_nodes=count,verified_sections=len(plan['sections']),
                    scope='original boundary, fiber order, rotation multiplicity and verified integrals')
    if kind=='geometric_moments':
        return dict(status='passed',complete=True,checked_nodes=count+1,
                    scope='original geometric chart and density, absolute or oriented distances, exact moments and positive normalizing measure')
    if kind=='planar_domain':
        region=val['domain_set']
        if 'intersection' in region:
            return dict(status='passed',complete=True,checked_nodes=count,checked_drawings=0,
                        checked_sign_preimages=len(region['intersection']))
        return {'status':'passed','complete':True,'checked_nodes':count,'checked_open_slabs':len(region['slabs']),
                'checked_vertical_sections':len(region['sections']),'checked_drawings':int('drawing_svg' in val)}
    if kind in ('restricted_function_image','real_function_domain_and_range'):
        return {'status':'passed','complete':True,'checked_nodes':count,'verified_intervals':len(val['image_intervals']),
                'scope':'maximal real input domain intersected with the stated set and exact image'}
    if kind=='parametric_curve_derivatives':
        return {'status':'passed','checked_nodes':count,'complete':True,'scope':'ordinary finite graph derivatives along the original local branches'}
    if kind=='implicit_graph_derivatives_and_values':
        return dict(status='passed',checked_nodes=count+1,complete=True,
                    scope='derivatives on original implicit graph fibers with all exceptional parameters and required points')
    if kind=='differentiate_floor_expression':
        return dict(status='passed',checked_nodes=count+1,complete=True,
                    scope='derivative on all original open cells and on every integer-level jump')
    if kind=='partial_fraction_symmetry':
        return dict(status='passed',complete=True,checked_nodes=len(plan['argument']),
                    scope='even rational function on the original symmetric domain and uniqueness of the decomposition over real and complex fields')
    if kind=='quadratic_radical_primitive_proof':
        return dict(status='passed',complete=True,checked_nodes=1+len(plan['argument']),
                    scope='exact quadratic coefficient identities, positive real radicals, original components and algebraic obstruction')
    if kind=='rational_primitive_criterion':
        return dict(status='passed',complete=True,checked_nodes=1+len(val['cases'])+len(plan.get('monomial_residuals',())),
                    scope='original nonzero polynomial denominator and all parameter branches; necessary and sufficient vanishing of the simple-pole part')
    if kind=='rational_primitive_algebraic_part':
        return dict(status='passed',complete=True,checked_nodes=count+2,
                    scope='exact rational derivative identity on the original domain and square-free proper remainder')
    if kind=='linear_primitive':
        if chart:
            return dict(status='passed',complete=True,checked_nodes=count+1,
                        scope='rational pullback on every original component with all regular chart boundaries joined')
        return {'status':'passed','checked_nodes':count,'complete':True,'verified_summands':len(plan['terms']),
                'scope':'linearity on every connected component of the original real integration domain'}
    if kind=='real_function_domain':
        if plan.get('method')=='sign_preimages':
            return dict(status='passed',checked_nodes=count,complete=True,checked_sign_preimages=len(val['intersection']),
                        checked_guards=len(plan['raw_conditions']))
        return {'status':'passed','checked_nodes':count,'complete':True,'checked_guards':len(plan['raw_conditions']),
                'checked_open_intervals':len(plan['open_cells']),'checked_points':len(plan['point_membership'])}
    if kind=='line_integral':
        if plan['measure']=='exact_one_form':
            return {'status':'passed','checked_nodes':count,'complete':True,
                    'scope':'endpoint evaluation of a global potential along the given piecewise smooth curve'}
        return {'status':'passed','checked_nodes':count,'complete':True,'verified_pieces':len(plan['pieces']),
                'scope':'original integrand on a continuous piecewise smooth path, pullback and integration on each piece'}
    if kind=='classify_extrema':
        return {'status':'passed','checked_nodes':count,'complete':True,'checked_branches':len(plan['chart']['branches']),
                'scope':'all strict two-sided local extrema on the original real domain'}
    if r['schema']=='cartesian-slices/v1':
        return {'status':'passed','complete':True,'checked_nodes':sum(len(v) for v in val.values())+len(plan['pieces']),
                'scope':'complete original edge or sign partition and signed fibers in every requested order'}
    if r['task']['kind']=='variable_endpoint_integral_derivative':
        return {'status':'passed','checked_nodes':count,'complete':True,'scope':'all real coordinates, oriented continuous integral with independently verified endpoint derivatives'}
    if kind in ('definite_integral_sign','compare_definite_integrals','mean_function_value'):
        return dict(status='passed',checked_nodes=count+1,complete=True,
                    scope='original finite integrals, verified normalization or strict sign on the transformed interval')
    if kind=='weighted_mean_integral_estimate':
        return dict(status='passed',checked_nodes=count+len(plan['range_steps'])+1,complete=True,
                    scope='closed interval, nonnegative weight with exact integral, and first integral mean value theorem')
    if r['task']['kind']=='ellipsoid_moment':
        return {'status':'passed','complete':True,'checked_nodes':len(plan['completed_squares'])+len(plan['moment_steps']),
                'scope':'verified triangular square completions, normalized uniform-ball monomial recurrence and original source domain'}
    if r['task']['kind']=='iterated_integral':
        if chart=='indexed_euler_expansion':
            return dict(status='passed',complete=True,checked_nodes=len(plan['transformations']),
                        scope='original finite endpoints, all stated positive integer indices and evaluated Euler modes')
        scope='primitive identities and Newton–Leibniz on every closed integration fiber'
        if chart=='endpoint_change_of_variable':scope='original open domain, derivative identity and separate finite one-sided limits'
        elif chart=='branched_rational_substitution':scope='original domain, rational differential identity, complete monotone partition and each oriented branch integral'
        elif chart:scope='original domain, oriented substitution, endpoints and checked integral in the new variable'
        return {'status':'passed','complete':True,'checked_nodes':count,'verified_fibers':len(plan['stages']),
                'scope':scope}
    if kind=='pointwise_limit_continuity':
        if plan.get('theorem')=='method.finite_maximum_envelope':
            return dict(status='passed',complete=True,checked_nodes=count+plan['number_of_terms']+2,
                        scope='positive terms bounded by a common maximum, vanishing squeeze error, denominator limit and continuity of a finite maximum')
        return dict(status='passed',checked_nodes=count+len(plan['scale_replacements'])+4,complete=True,
                    scope='common scale, source divisors, all relative open intervals, transition value and one-sided traces')
    if kind in ('discontinuity_classification','piecewise_continuity'):
        if 'family_reduction' in plan:
            return dict(status='passed',checked_nodes=count+len(plan['family_reduction']['argument']),complete=True,
                        scope='original relative domain, exceptional set and both admissible one-sided traces')
        if plan.get('theorem')=='method.step_level_continuity':
            return dict(status='passed',checked_nodes=count+len(val['jump_families'])+len(val['other_points'])+2,complete=True,
                        scope='original real domain, complete level preimages on each monotone branch, both traces and exceptional accumulation points')
        return dict(status='passed',checked_nodes=count+len(plan['open_cells']),complete=True,
                    scope='original real domain partition, continuity of elementary compositions and limits at every boundary or assigned point')
    if r['task']['kind']=='continuous_extension':
        return {'status':'passed','checked_nodes':count,'complete':True,'scope':'continuity at the adjoined point relative to the stated source neighborhood'}
    if r['task']['kind']=='tangent_geometry':
        return {'status':'passed','checked_nodes':count,'complete':True,
                'scope':'regular space tangent and orthogonal normal through the source point, including every returned rank case'}
    if r['task']['kind']=='scalar_field_geometry':
        return {'status':'passed','checked_nodes':count,'complete':True,'verified_points':len(plan['points']),
                'scope':'Euclidean differential on a smooth open neighborhood of every used source point'}
    if kind=='differential_operator':
        if 'printed_identity' in plan:
            return {'status':'passed','checked_nodes':count,'complete':True,'verified_identities':1,
                    'verified_applications':len(plan['applications']),
                    'scope':'printed ordinary differential equation, verified coordinate derivatives and equality on the full source domain'}
        return {'status':'passed','checked_nodes':count,'complete':True,'verified_applications':len(plan['applications']),
                'scope':'operator composition and verified coordinate derivatives on the original domain'}
    if kind=='definite_quadrature' and plan.get('theorem')=='method.target_quadrature':
        return dict(status='passed',complete=True,checked_nodes=count+len(plan.get('moments',[]))+2,
                    scope='original integrand, required normalization, finite and tail error estimates and total requested absolute error')
    return {'status':'passed','checked_nodes':count,'verified_samples':len(plan['samples']),'verified_domain_guards':len(plan['interval_domain']),
            'complete':True,'scope':'closed real interval, validated quadrature and requested obligations'}


def verify_ordinary_kernel(result,library,expected_task=None):
    from tasks import ordinary_kernel_plan,ordinary_kernel_children,ordinary_kernel_values
    require(not set(result)-{'schema','task','library_hash','operation_hash','knowledge_source','status','value','children','verification','compilation','elapsed_seconds'},'Unknown ordinary derivative claim')
    require(result['library_hash']==library.hash and result['operation_hash']==version() and result['status']=='SOLVED','Ordinary derivative basis changed')
    t=result['task']
    if expected_task is not None:require(canonical(t)==canonical(expected_task),'Ordinary derivative source changed')
    require(library.data.get('task_compilers',{}).get('partial_derivatives')=='coordinate_section_derivatives','Ordinary derivatives not admitted')
    try:p=ordinary_kernel_plan(t,library.data['partial_bundle_contract'])
    except (Unsupported,ValueError,KeyError,TypeError) as exc:raise VerificationError(str(exc)) from exc
    require(canonical(p)==canonical(result['compilation']),'Changed polynomial, kernel or original order')
    kids=ordinary_kernel_children(p);require(len(kids)==len(result['children']),'Missing elementary derivative witness')
    cycle=p['cycle'];total=0
    for i,(task,child) in enumerate(zip(kids,result['children'])):
        checked=verify(child,library,task);total+=checked['checked_nodes']
        tag,sign=cycle[i];other,s=cycle[(i+1)%len(cycle)]
        expected=m.mul(m.mul(m.q(sign*s),p['slope']),(other,p['kernel'][1]))
        require(child['status']=='SOLVED' and same_value(child['value'],expected),'Unproved elementary derivative transition')
    require(canonical(result['value'])==canonical(ordinary_kernel_values(p,replay=True)),'Differential recurrence does not reproduce the claimed formulas')
    return {'status':'passed','complete':True,'checked_nodes':total,'scope':'replayed elementary derivatives and polynomial product recurrence on the original real line'}




def verify_partial_bundle(result,library,expected_task=None):
    from tasks import compile_partial_bundle,partial_child_task,partial_component_value
    require(not set(result)-{'schema','task','library_hash','operation_hash','knowledge_source','status','value','children','partial_values','verification','compilation','pending','reason','elapsed_seconds'},'Unknown bundle claim')
    require(result['schema']=='partial-derivative-bundle/v1' and result['library_hash']==library.hash and result['operation_hash']==version(),'Partial bundle basis changed')
    task = result['task']
    if expected_task is not None: require(canonical(task)==canonical(expected_task),'Partial source changed')
    require(library.data.get('task_compilers',{}).get('partial_derivatives')=='coordinate_section_derivatives','Partial bundle not admitted')
    try: plan = compile_partial_bundle(task,library.data['partial_bundle_contract'])
    except (Unsupported,KeyError,TypeError) as exc: raise VerificationError(str(exc)) from exc
    require(canonical(plan)==canonical(result['compilation']),'Partial compilation or original domain changed')
    children = result['children']; require(isinstance(children,(list,tuple)) and len(children)<=len(plan['indices']),'Wrong component count')
    values = {}; total = 0
    for index,child in zip(plan['indices'],children):
        expected = partial_child_task(plan,index,values); total += verify(child,library,expected_task=expected)['checked_nodes']
        try: values[index] = partial_component_value(plan,index,child)
        except (Unsupported,KeyError,TypeError) as exc: raise VerificationError(str(exc)) from exc
    complete = len(values)==len(plan['indices'])
    require(canonical(result['partial_values'])==canonical(tuple(values.items())),'Partial coordinate value or order changed')
    answer = tuple(values[p] for p in plan.get('selected_paths',plan['indices'])) if complete else None
    require(result['status']==('SOLVED' if complete else 'PARTIAL_DERIVATIVES_PENDING') and canonical(result['value'])==canonical(answer),'Partial bundle completeness changed')
    if 'pending' in result: require(not complete and canonical(result['pending']['index'])==canonical(plan['indices'][len(values)]) and result['pending'].get('diagnostic_only') is True,'Pending coordinate changed')
    return {'status':'passed','checked_nodes':total,'scope':'ordered_coordinate_sections_on_original_domain_only','complete':complete}


def verify_original_table(result,library,expected_task=None):
    from tasks import compile_original_table
    require(result.get('schema')=='original-table-derivative/v1','Wrong pointwise proof schema')
    require(not set(result)-{'schema','task','library_hash','operation_hash','plan','status','value','proof','stats','formula','verification','elapsed_seconds'},'Unknown pointwise proof claim')
    require(result['library_hash']==library.hash and result['operation_hash']==version(),'Original-table basis changed')
    if expected_task is not None:require(canonical(result['task'])==canonical(expected_task),'Original-table source changed')
    require(library.data.get('pointwise_table_contract')=='original_variable_then_arbitrary_fixed_point','Pointwise context not admitted')
    require('pointwise_real' in library.data.get('context_rule_scopes',{}),'No pointwise rule scope')
    try:plan=compile_original_table(result['task'])
    except (Unsupported,KeyError,TypeError) as exc:raise VerificationError(str(exc)) from exc
    require(canonical(plan)==canonical(result['plan']),'Original-table context changed')
    checked=replay_dag(result['proof'],library,plan['context'],{'root':plan['goal']});formula=checked['values']['root']
    require(canonical(formula)==canonical(result['formula']),'Original derivative formula changed')
    at=m.substitute(formula,{('v',plan['context']['variable']):('s',plan['context']['point_symbol'])})
    require(m.constant_defined(at,plan['context']) and canonical(at)==canonical(result['value']),'Original point value or raw domain changed')
    expected='FORMULA_ON_SUFFICIENT_DOMAIN' if plan['compilation']['boundary_obligations']=='pending' else 'SOLVED'
    require(result['status']==expected,'Original-table source coverage changed')
    return {'status':'passed','checked_nodes':checked['checked_nodes'],'scope':'original_variable_table_at_arbitrary_fixed_point'}


def verify_series_comparison(result,library,expected_task=None):
    from tasks import compile_series_comparison,series_comparison_conclusion
    require(not set(result)-{'schema','task','library_hash','operation_hash','knowledge_source','status','value','attempts','verification','compilation','child_result','elapsed_seconds','reason'},'Unknown series claim')
    require(result.get('schema')=='series-comparison-run/v1' and result['library_hash']==library.hash and result['operation_hash']==version(),'Series comparison basis changed')
    task=result['task']
    if expected_task is not None:require(canonical(task)==canonical(expected_task),'Series source changed')
    require(library.data.get('task_compilers',{}).get('series_convergence')=='positive_p_series_comparison','Series comparison not admitted')
    choice=freeze(result['compilation'].get('criterion',result['compilation'].get('power')))
    require(not isinstance(choice,str) or choice in library.data.get('series_log_tests',())
            or choice=='product_ratio_expansion' and library.data.get('product_ratio_expansion')
            or choice=='exceptional_comparison' and library.data.get('exceptional_comparison')
            or choice=='factorial_ratio' and library.data.get('integer_factorial_ratio')
            or choice=='periodic_series' and library.data.get('periodic_integral_comparison')
            or choice=='alternating_rational' and library.data.get('alternating_rational_series'),'Series criterion is not admitted')
    try:plan=compile_series_comparison(task,choice)
    except (Unsupported,KeyError,TypeError,ValueError) as exc:raise VerificationError(str(exc)) from exc
    require(canonical(plan)==canonical(result['compilation']),'Scaled term or all-index source certificate changed')
    checked=verify(result['child_result'],library,expected_task=plan['scaled_limit_task'])
    try:conclusion=series_comparison_conclusion(plan,result['child_result'])
    except (Unsupported,KeyError,TypeError) as exc:raise VerificationError(str(exc)) from exc
    require(all(canonical(result.get(k))==canonical(v) for k,v in conclusion.items()),'Series classification or asymptotic-order scope changed')
    return {**checked,'scope':'series classification with all-index raw-domain certificate; no sum value','complete':result['status']=='SOLVED'}


def verify_euler_homogeneity(result,library,expected_task=None):
    from tasks import compile_euler_homogeneity,euler_conclusion
    require(not set(result)-{'schema','task','library_hash','operation_hash','knowledge_source','status','value','verification','compilation','child_result','elapsed_seconds','reason'},'Unknown Euler claim')
    require(result.get('schema')=='euler-homogeneity-run/v1' and result['library_hash']==library.hash and result['operation_hash']==version(),'Euler basis changed')
    if expected_task is not None:require(canonical(result['task'])==canonical(expected_task),'Euler source changed')
    require(library.data.get('task_compilers',{}).get('euler_homogeneity')=='structural_scaling_and_euler_identity','Euler method not admitted')
    try:plan=compile_euler_homogeneity(result['task'])
    except (Unsupported,KeyError,TypeError,ValueError) as exc:raise VerificationError(str(exc)) from exc
    require(canonical(plan)==canonical(result['compilation']),'Euler degree, cone or source domain changed')
    checked=verify(result['child_result'],library,expected_task=plan['partial_task'])
    try:value=euler_conclusion(plan,result['child_result'])
    except (Unsupported,KeyError,TypeError) as exc:raise VerificationError(str(exc)) from exc
    require(result['status']=='SOLVED' and canonical(value)==canonical(result['value']),'Euler identity or completeness changed')
    return {**checked,'scope':'positive scaling on original conic D and exact Euler identity; no joint differentiability claim'}
