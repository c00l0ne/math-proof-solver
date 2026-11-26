"""Find and check reductions for source limits with fixed parameters and finite binders."""
from fractions import Fraction
import re

import expressions as m
from model import ONE, ZERO, Unsupported, freeze, q


NAME=r'[A-Za-z_]\w*'
INNER_KINDS={
    'parameter_integer_power_limit','parameter_finite_scalar_limit','root_index_parameter_limit',
    'finite_product_integer_parameter_limit','finite_product_root_limit','variable_degree_root_product_limit',
    'integer_power_two_tail_limit','integer_parameter_limit','integer_parameter_trigonometric_limit',
    'parameter_domain_radical_limit','finite_sum_sequence_limit','area_via_inscribed_sum_limit',
    'limit_using_previous_array_theorem','integer_phase_sequence_limit','relative_domain_limit','floor_function_limit',
    'prove_directed_output_limit','difference_of_directional_limits','point_value_and_one_sided_limits',
    'iterated_function_limit','cauchy_increment_theorem_proof','cauchy_root_ratio_theorem_proof',
    'prove_sequence_identity','prove_exponential_series_limit','factorial_phase_limit','recursive_sequence_limit',
    'stable_recurrence_limit_theorem','function_recurrence_limit','cluster_value_sequence_construction',
    'liminf_limsup','Landau_power_algebra_proof','prove_no_power_order','prove_growth_comparison_family',
    'construct_and_prove_dominating_function','geometric_epsilon_delta','error_tolerance_interval',
    'propagate_measurement_error','maximal_error_neighborhood','epsilon_delta_proof_table','maximal_delta_and_uniformity',
    'quantifier_negation',
}
META={'id','kind','task_type','source','source_number','source_exercise_number','source_subpart','source_edition',
      'source_pdf_page','source_pdf_pages','transcription_notes','program_status','main_pass_status','deferred_reason'}


def family_route(task,kind):
    goal=task.get('goal')
    expression=goal.get('expression') if isinstance(goal,dict) else None
    if kind=='finite_sum_sequence_limit':return isinstance(expression,str) and 'sum_{' in expression
    if kind in INNER_KINDS-{'Landau_power_algebra_proof'}:return True
    if kind=='prove_limit_identity':return isinstance(task.get('goal'),dict) and 'expression' in task['goal']
    return (kind=='finite_sum_or_product_sequence_limit' and isinstance(expression,str)
            and goal.get('variable_domain')=='positive_integers'
            and (expression.startswith('sum_{') or re.match(r'product_\{.+?=0\}\^\w+\(1\+',expression)))


def require(ok,reason):
    if not ok:raise Unsupported(reason)


def ans(method,value,*argument,**evidence):
    return dict(theorem='method.'+method,argument=argument,**evidence),value


def sym(name):return ('s',name)


def times(*factors):
    out=ONE
    for x in factors:out=m.mul(out,x)
    return m.simplify(out)


def plus(*items):
    out=ZERO
    for x in items:out=m.add(out,x)
    return m.simplify(out)


def quotient(a,b):return m.simplify(m.div(a,b))


def subexpression(text,start):
    """Return one raw parenthesized operand, allowing nested source operands."""
    require(start<len(text) and text[start]=='(','The source operation needs a parenthesized operand')
    depth=1
    for p in range(start+1,len(text)):
        if text[p]=='(':depth+=1
        elif text[p]==')':
            depth-=1
            if not depth:return text[start+1:p],p+1
    raise Unsupported('Incomplete operand in the source expression')


def lower_functions(text,var,params,ctx,*,known_index=False):
    """Lower printed roots and indexed logarithms while exposing their source guards."""
    conditions=[];out=[];offset=0
    while offset<len(text):
        if text.startswith(('root_','root4(', 'log_'),offset):
            root=text.startswith('root',offset);literal_four=text.startswith('root4(',offset)
            begin=offset+5 if literal_four or root else offset+4
            if literal_four:label,end='4',begin
            elif text.startswith('(',begin):label,end=subexpression(text,begin)
            else:
                match=re.match(NAME,text[begin:]);require(match is not None,'Missing root index or logarithm base')
                label=match[0];end=begin+len(label)
            argument,end=subexpression(text,end)
            body,inner=lower_functions(argument,var,params,ctx,known_index=known_index);conditions.extend(inner)
            scale=m.parse(label,var,params)
            if root:
                if known_index and m.variable_in(scale):
                    from integrals import affine
                    a,b=map(m.num,affine(scale,var))
                    require(a is not None and b is not None and a>0 and a.denominator==b.denominator==1,
                            'The moving root index is not positive integer on a tail')
                conditions.append(dict(operator='root',base=body,nonzero_index=label))
                out.append('('+body+')^(1/('+label+'))')
            else:
                conditions.append(dict(operator='log',positive_argument=body,positive_base=label,exclude_unit_base=True))
                out.append('(ln('+body+')/ln('+label+'))')
            offset=end
        else:
            out.append(text[offset]);offset+=1
    return ''.join(out),conditions


def bound_packet(task,goal_fields,extra=(),allow_source_text=True):
    fields=META|{'goal','source_assumptions','assumptions','source_statement','derived_domain_conditions','derived_original_domain_conditions'}|set(extra)
    require(not set(task)-fields and not ('assumptions' in task and 'source_assumptions' in task),
            'An additional source condition or output must be bound')
    goal=task.get('goal');notes=task.get('source_statement');conditions=task.get('source_assumptions',task.get('assumptions',[]))
    require(isinstance(goal,dict) and set(goal)<=set(goal_fields) and isinstance(conditions,list) and all(isinstance(x,str) for x in conditions),
            'Invalid typed source statement, hypotheses, or requested goal')
    require(notes is None or allow_source_text and isinstance(notes,str) and notes.strip(),'No coherent source text')
    if notes is not None and 'expression' in goal:
        require(str(goal['expression']).replace(' ','') in notes.replace(' ',''),
                'Typed expression disagrees with the displayed source statement')
    return goal,conditions


def exact_neighborhood_limit(expression,variable,point,side,params,conditions,library):
    from limit_proofs import germ_limit
    child=dict(kind='limit',expression=expression,variable=variable,parameters=params,stated_conditions=conditions,
               approach=dict(point=point,side=side))
    return germ_limit(child,library,orders=(2,4,6),split=False)


def fixed_integer_local(task,kind,library):
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable','approach','parameters','point','side','parameter_n'})
    expr=g['expression'];var=g.get('variable','x');v=('v',var);approach=g.get('approach',{});point=approach.get('point',g.get('point'))
    side=approach.get('side',g.get('side'));params=g.get('parameters');domains={}
    require(side=='both' and point is not None and set(approach)<= {'point','side'},'The original local two-sided approach is not bound')
    if isinstance(params,dict):domains=dict(params)
    if kind=='root_index_parameter_limit':
        if not domains:
            require(g.get('parameter_n')=='integer as printed','A root index of known integer type is required');domains={'n':'integer'}
        require(set(domains.values())<= {'integer','real'} and not given,'An unsupported restriction on a root index remains')
        params=list(domains);conditions=[p+'!=0' for p,d in domains.items() if d=='integer'];ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conditions))
        lowered,guards=lower_functions(expr,var,params,ctx)
        require(guards and all(g['operator']=='root' and domains.get(g['nonzero_index'])=='integer' for g in guards),
                'The original fixed indices are not bound by the declared integer domains')
        proof,value=exact_neighborhood_limit(lowered,var,point,side,params,conditions,library)
        require(not isinstance(value,dict),'The finite limit or its original real domain remains unresolved')
        return ans('fixed_nonzero_integer_root_jet',dict(value=value,domain=conditions,otherwise='root index zero is undefined'),
                   'Сохраняем целые индексы как параметры. Нулевой индекс исключается, отрицательный означает обратный корень.',
                   'На положительной проколотой области исходный корень равен действительной степени. Строим её разложение на каждой запрошенной стороне.',
                   fixed_parameter_types=domains,root_obligations=guards,checked_local_germs=proof)

    if not domains:
        for c in given:
            match=re.fullmatch(r'('+NAME+r'(?:,'+NAME+r')*) positive integers?',c)
            if match:domains.update(dict.fromkeys(match[1].split(','),'positive integer'))
            else:
                match=re.fullmatch('('+NAME+') real',c);require(match is not None,'Unknown fixed integer assumption')
                domains[match[1]]='real'
    else:
        label=','.join(domains)+' positive integer'+('s' if len(domains)>1 else '')
        require(all(d=='positive integer' for d in domains.values()) and given==[label],
                'The fixed integer assumptions differ from the original statement')
    require(domains and any(t=='positive integer' for t in domains.values()),'No known positive degree')
    params=list(domains);conditions=[p+'>0' for p,d in domains.items() if d=='positive integer'];ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conditions))
    finite=re.fullmatch(r'\(sum_\{('+NAME+r')=(\d+)\}\^('+NAME+r') ([A-Za-z_]\w*)\^\1-(.+)\)/\('+re.escape(var)+r'-1\)',expr)
    if finite:
        j,lo,index,x,count=finite.groups();lo=int(lo)
        require(x==var and point=='1' and domains.get(index)=='positive integer' and j not in params+[var] and lo==1 and same_value(m.parse(count,None,params),sym(index)),
                'The number of subtracted constants differs from the original bound sum')
        upper=sym(index);value=times(q(1,2),upper,plus(upper,ONE))
        return ans('bound_integer_power_prefix_difference',value,
                   'Разносим вычитаемую константу по исходным членам. Каждую разность x^k−1 делим на x−1 конечной геометрической суммой.',
                   'При x→1 каждая такая сумма стремится к своему числу слагаемых k. Складываем все целые k из той же конечной области.',
                   binder=j,first_index=lo,last_index=index,fixed_parameter_types=domains)
    root=m.parse(expr,var,params);a=m.parse(str(point),None,params)
    if a[0]=='s' and domains.get(a[1])=='real' and root[0]=='div':
        h=plus(v,m.neg(a));n=next((sym(p) for p,d in domains.items() if d=='positive integer'),None)
        require(n is not None,'No positive integer exponent preserved')
        expected=plus(('rpow',v,n),m.neg(('rpow',a,n)),m.neg(times(n,('rpow',a,plus(n,q(-1))),h)))
        require(same_value(root[1],expected) and same_value(root[2],m.power(h,2)),'Not the first-order Taylor remainder of the checked integer monomial')
        value=dict(cases=[dict(condition=source(n)+'=1',value=ZERO),dict(condition=source(n)+'=2',value=ONE),
                          dict(condition=source(n)+'>=3',value=times(q(1,2),n,plus(n,q(-1)),('rpow',a,plus(n,q(-2)))))])
        return ans('integer_binomial_remainder_at_any_center',value,
                   'При целой положительной степени точное биномиальное тождество применимо также при отрицательном и нулевом центре.',
                   'После вычитания постоянной и линейной частей остаток делится на h². Отдельные степени 1 и 2 убирают отрицательные степени нулевого центра.',
                   polynomial=root,center=a,fixed_parameter_types=domains)
    proof,value=exact_neighborhood_limit(expr,var,point,side,params,conditions,library)
    require(not isinstance(value,dict),'The positive-base germ does not settle the full integer family')
    return ans('positive_base_jet_for_integer_family',value,
               'Проверяем исходные положительные целые параметры. В проколотой окрестности допустимы те же высокие степени положительных оснований.',
               'Собираем первые ненулевые коэффициенты числителя и знаменателя. Переход обоснован на обеих исходных сторонах.',
               fixed_parameter_types=domains,checked_local_germs=proof)


def reciprocal_limit(raw,var,params,conditions,library):
    from tasks import source
    t='limitReciprocal'
    while t in [var,*params]:t+='_'
    ast=m.substitute(raw,{('v',var):m.div(ONE,('v',t))})
    text=source(ast)
    proof,value=exact_neighborhood_limit(text,t,'0','right',params,conditions,library)
    require(not isinstance(value,dict),'The reciprocal germ does not cover the original positive tail')
    return dict(original=raw,reciprocal=ast,new_variable=t,germ=proof),value


def affine_denominators(expr,var,ctx):
    from integrals import affine
    from tasks import domain_conditions
    require(expr[0]=='rpow' and expr[2]==('v',var) and expr[1][0]=='div','No affine quotient with the running index as exponent')
    f,g=expr[1][1:]
    require(not domain_conditions(f) and not domain_conditions(g),'Original affine coefficient has its own unresolved denominator')
    a,b=affine(f,var);c,d=affine(g,var)
    require(all(m.constant_defined(y,ctx) for y in (a,b,c,d)) and all(m.sign(y,ctx)==1 for y in (a,c)),
            'Both leading coefficients must be proved strictly positive')
    return a,b,c,d


def nested_scalar_packet(task):
    g,conditions=bound_packet(task,{'variable','expression','approach','variable_domain','parameters','goal'})
    text=g['expression'];var=g['variable'];ad=g['approach'];mode=ad.get('mode','finite_point');point=ad['point'];side=ad.get('side','both')
    require(set(ad)<={'point','side','mode'} and side in ('both','left','right') and mode in ('finite_point','positive_integer_tail','positive_infinity','negative_infinity','magnitude_infinity'),
            'The source approach needs a different mathematical mode')
    expected='positive_integers' if mode=='positive_integer_tail' else 'real';require(g.get('variable_domain',expected)==expected,'The source variable domain is not preserved')
    claim=task.get('source_statement')
    allowed={f'Найти предел {text} при {var}→{point} ({side}; {mode}).',f'Найти/доказать предел {text} при {var}→{point}; {side}; {mode}.'}
    if side=='both' and mode=='finite_point':
        allowed.update(f'{verb} предел {text} при {var}->{point}.' for verb in ('Найти','Найти/доказать'))
    require(claim is None or claim in allowed,'The two source renderings disagree')
    origin=task.get('source',{})
    require(isinstance(origin,dict) and not set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','proof_reuse_only','reader_binding_ref'},
            'Unrepresented printed mathematical obligations in the source')
    notes=task.get('transcription_notes',[])
    require(not notes or all(isinstance(n,str) and (re.fullmatch(r'The enlarged source confirms numerator\d+ in BOTH fractions and point\d+\. One original goal contains both sides\.',n)
                                  or n=='The printed n>0 does not say integer here; the complete declared family permits a positive real exponent.') for n in notes),
            'An additional source annotation needs proof')
    supplied=g.get('parameters',[]);params=[]
    for s in supplied:
        if isinstance(s,str):params.append(s)
        else:
            require(set(s)=={'symbol','domain','independent_of'} and s['domain']=='real' and s['independent_of']==var,'A parameter may not vary with the running argument')
            params.append(s['symbol'])
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conditions))
    return text,var,point,side,mode,params,conditions,ctx


def candidate_divisor_guards(raw,var,point,side,params,conditions,ctx,library):
    from limit_proofs import local_coefficients
    from tasks import domain_conditions,source
    from verify import same_value
    def reduced(e):
        e=m.simplify(e)
        if e[0]=='mul':
            a,b=e[1:]
            if m.sign(a,ctx) in (-1,1):return reduced(b)
            if m.sign(b,ctx) in (-1,1):return reduced(a)
        if e[0]=='pow' and e[2]>0:return reduced(e[1])
        return e
    out=[]
    for rel,e in domain_conditions(raw):
        if rel!='nonzero':continue
        if m.variable_in(e):
            try:jet,_,_=local_coefficients(e,var,point,'right' if side=='both' else side,4,library,params,conditions)
            except (Unsupported,ArithmeticError):continue
            if not jet[1]:continue
            e=jet[1][0][1]
        w=reduced(e)
        if w!=ZERO and not m.variable_in(w) and m.sign(w,ctx) is None and not any(same_value(w,y) for y in out):out.append(w)
    return out


def guard_split_from_original_divisors(raw,guards,var,point,side,params,conditions,ctx,library):
    from limit_proofs import germ_limit
    from tasks import domain_conditions,source
    from verify import same_value
    require(len(guards)==1 and guards[0].endswith('!=0'),'Only a single necessary nonzero condition is admitted here')
    first=guards[0][:-3];w=m.simplify(m.parse(first,None,params));f=w;replace={}
    if f[0]=='s':replace={f:ZERO}
    else:
        for a in params:
            for b in params:
                if a!=b and same_value(f,plus(sym(a),m.neg(sym(b)))):replace={sym(a):sym(b)};break
            if replace:break
        if not replace and f[0]=='add':
            left,negative=f[1:];r=negative[2] if negative[0]=='mul' and negative[1]==q(-1) else None
            if r and left[0]==r[0]=='rpow' and left[2]==r[2] and left[1][0]==r[1][0]=='s' and left[1]!=r[1]:
                if all(m.constant_defined(t,ctx) and m.sign(t,ctx)==1 for t in (left[1],r[1],left[2])):
                    replace={left[1]:r[1]}  # On positive bases a fixed positive power is injective.
    source_divisors=[u for rel,u in domain_conditions(raw) if rel=='nonzero']
    require(any(same_value(u,w) or replace and m.simplify(m.substitute(u,replace))==ZERO for u in source_divisors),
            'The zero case has not been proved to invalidate the original denominator')
    gt=f'{source(w)}!=0';extra=[*conditions,gt];extra_ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=extra))
    at=m.substitute(raw,{('v',var):m.parse(point,None,params)})
    if m.constant_defined(at,extra_ctx):
        proof=dict(continuous_inside_original_domain=True);limit=m.simplify(at)
    else:
        transformed=('mul',raw[2],('ln',raw[1])) if raw[0]=='rpow' else raw
        proof,limit=exact_neighborhood_limit(source(transformed),var,point,side,params,extra,library)
        require(not isinstance(limit,dict),'The nonzero branch still has an unresolved approach')
        if raw[0]=='rpow':limit=ZERO if limit=='-inf' else '+inf' if limit=='+inf' else m.simplify(('exp',limit))
    return ans('necessary_parameter_guard_for_local_limit',dict(cases=[dict(condition=source(w)+'=0',value='no_original_approach'),dict(condition=gt,value=limit)]),
               'Сначала доказываем из исходного делителя, что при нулевом условии проколотая область отсутствует.',
               'В оставшейся ветви переносим доказанную ненулевость в локальное разложение или непрерывную подстановку.',
               original=raw,derived_zero_branch=tuple(replace.items()),necessary_guard=w,checked_local_branch=proof)


def constant_power_bases(raw,var,point,side,mode,params,conditions,library):
    from limit_proofs import local_coefficients,germ_limit
    from quadrature import enclose
    from tasks import source
    require(raw[0]=='rpow' and not params,'A fixed unequal-to-one base is necessary')
    base,exp=raw[1:];inverse=mode in ('positive_integer_tail','positive_infinity');v=('v',var);small='boundReciprocal'
    if inverse:
        swap={v:m.div(ONE,('v',small))};base=m.substitute(base,swap);exp=m.substitute(exp,swap);var,point,side=small,'0','right'
    def as_quotient(expr):
        if expr[0] not in ('tan','cot','sec','csc'):return expr
        sin,cos=('sin',expr[1]),('cos',expr[1])
        numerator,denominator={'tan':(sin,cos),'cot':(cos,sin),'sec':(ONE,cos),'csc':(ONE,sin)}[expr[0]]
        return 'div',numerator,denominator
    checked_base=as_quotient(base)
    try:
        a,b=exact_neighborhood_limit(source(checked_base),var,point,side,[],conditions,library)
        require(isinstance(b,tuple),'Base has no finite limit in the source domain')
        lo,hi=enclose(b,None)
    except Unsupported:
        require(mode=='finite_point','A local enclosure needs a finite original point')
        left,right=enclose(m.parse(point,None),None)
        for delta in (Fraction(1,32),Fraction(1,1024)):
            interval=left-delta,right+delta
            try:lo,hi=enclose(checked_base,interval)
            except Unsupported:continue
            if lo>0 and (hi<1 or lo>1):
                a=dict(method='interval_extension_on_original_base',variable_interval=tuple(map(q,interval)))
                break
        else:raise Unsupported('The original base is not separated throughout a checked neighborhood')
    require(lo>0 and (hi<1 or lo>1),'The original base is not strictly separated from 0 and 1')
    e,q0=exact_neighborhood_limit(source(as_quotient(exp)),var,point,side,[],conditions,library)
    require(q0 in ('+inf','-inf'),'Expected a bound divergent exponent on that same side')
    value=ZERO if (q0=='+inf')==(hi<1) else '+inf'
    return ans('power_limit_from_separated_base_and_exponent',value,
               'Доказываем, что исходное основание равномерно отделено и от нуля, и от единицы. Отсюда его логарифм имеет постоянный знак и отделён от нуля.',
               'Отдельно проверяем, что исходный показатель стремится к бесконечности с известным знаком. По пределу логарифма степени находим предел самой степени.',
               base_bound=(q(lo),q(hi)),base_proof=a,exponent_proof=e,source_reciprocal=inverse)


def tail_composition(raw,var,params,conditions,ctx,library):
    from operations import expression_positions
    from ordinary_series import logarithmic_monomial,guard_on_ray
    from tasks import domain_conditions,source
    from verify import same_value
    v=('v',var)
    if raw[0]=='add' and raw[1][0] in ('sin','cos','atan') and raw[2][0]=='mul' and raw[2][1]==q(-1) and raw[2][2][0]==raw[1][0]:
        a,b=raw[1][1],raw[2][2][1];error=plus(a,m.neg(b))
        if a[0]==b[0]=='ln':
            require(all(guard_on_ray(('positive',u),var,1,ctx) for u in (a[1],b[1])),'Both original logarithm arguments need positive tails')
            error=('ln',quotient(a[1],b[1]))
        proof,val=reciprocal_limit(error,var,params,conditions,library)
        require(val==ZERO,'The difference of the two source phases does not tend to zero')
        return ans('bounded_derivative_controls_phase_difference',ZERO,
                   'У внешней функции производная по модулю не больше единицы. Поэтому разность двух внешних значений ограничена модулем разности аргументов.',
                   'Внутреннюю разность строим как отдельную цель и проверяем её нулевой предел на исходной области.',
                   source_function=raw[1][0],phase_error=error,reduction=proof)
    if raw[0]=='div' and raw[1][0]==raw[2][0]=='ln' and not params:
        def monomials(e):
            if e[0]=='add':return monomials(e[1])+monomials(e[2])
            if e[0]=='cbrt':e=('rpow',e[1],q(1,3))
            c,r,_=logarithmic_monomial(e,v,ctx)
            require(len(r)==1 and m.num(r[0]) is not None and m.sign(c,ctx)==1,'The original log argument lacks a positive power sum')
            return [(r[0],c)]
        rows=[monomials(part[1]) for part in raw[1:]]
        degrees=[max(m.num(r) for r,_ in cell) for cell in rows]
        require(all(d>0 for d in degrees),'The logarithmic leading term must grow on both sides of the quotient')
        return ans('logarithm_of_positive_power_sum_growth',q(degrees[0]/degrees[1]),
                   'Из каждой положительной суммы выносим её наибольшую степень индекса. После логарифмирования остальные множители дают ограниченную поправку.',
                   'Ненулевой ведущий член обоих логарифмов пропорционален ln x. Отношение равно отношению наибольших показателей.',
                   power_sums=rows,leading_degrees=list(map(q,degrees)))
    raise Unsupported('No controlled outer phase or logarithmic growth comparison was found')


def extended_nested_limit(task,library):
    from limit_proofs import germ_limit
    from tasks import domain_conditions,source
    text,var,point,side,mode,params,conditions,ctx=nested_scalar_packet(task)
    lowered,guards=lower_functions(text,var,params,ctx,known_index=mode=='positive_integer_tail');v=('v',var)
    raw=m.parse(lowered,var,params)
    derived=task.get('derived_original_domain_conditions',task.get('derived_domain_conditions',[]))
    if mode=='finite_point' and params:
        from verify import same_value
        options=candidate_divisor_guards(raw,var,point,side,params,conditions,ctx,library)
        if derived:
            require(len(derived)==1 and derived[0].endswith('!=0'),'An unproved derived domain condition remains')
            condition=m.parse(derived[0][:-3],None,params)
            options=[w for w in options if same_value(w,condition) or same_value(w,m.neg(condition))]
        for w in options:
            try:return guard_split_from_original_divisors(raw,[source(w)+'!=0'],var,point,side,params,conditions,ctx,library)
            except Unsupported:pass
    require(not derived,'A reported domain condition has not been recovered from the original divisor')
    if mode=='positive_infinity' and raw[0]=='rpow' and raw[2]==v:
        try:a,b,c,d=affine_denominators(raw,var,ctx)
        except Unsupported:pass
        else:
            diff=plus(a,m.neg(c));equal=('exp',quotient(plus(b,m.neg(d)),a));name=source(diff)
            value=dict(cases=[dict(condition=name+'<0',value=ZERO),dict(condition=name+'=0',value=equal),dict(condition=name+'>0',value='+inf')])
            return ans('affine_power_limit_with_ratio_cases',value,
                       'Исходная база положительна на хвосте из её двух ведущих коэффициентов. Если их отношение отличается от единицы, показатель определяет нулевой или бесконечный предел.',
                       'В ветви равных коэффициентов выделяем поправку порядка 1/x, логарифмируем и вычисляем предел экспоненциального показателя.',
                       original=raw,leading=(a,c),offsets=(b,d))
    if mode in ('positive_integer_tail','positive_infinity'):
        require(point in ('infinity','+infinity','+inf') and side=='both','Wrong source direction of the reciprocal transformation')
        if not m.variable_in(raw):
            require(mode=='positive_integer_tail' and not guards,'The absent source index cannot be replaced by another variable')
            initial=domain_conditions(raw);value=dict(value=raw,available_under=[(s,source(e)) for s,e in initial])
            return ans('constant_expression_in_original_running_index',value,
                       'Вся исходная формула независима от напечатанного индекса. Предел постоянной последовательности равен её значению там, где определены все исходные операции.',
                       original=raw,index=var,source_domain=initial)
        if not params and raw[0]=='rpow':
            try:return constant_power_bases(raw,var,point,side,mode,params,conditions,library)
            except Unsupported:pass
        if raw[0]=='rpow':
            try:proof,exponent=reciprocal_limit(('mul',raw[2],('ln',raw[1])),var,params,conditions,library)
            except Unsupported:
                if mode=='positive_integer_tail' and raw[2][0]=='csc':return integer_phase_tail(task,'parity_power',library)
                raise
            value=ZERO if exponent=='-inf' else '+inf' if exponent=='+inf' else m.simplify(('exp',exponent))
        else:
            try:proof,value=reciprocal_limit(raw,var,params,conditions,library)
            except Unsupported:return tail_composition(raw,var,params,conditions,ctx,library)
        return ans('reciprocal_limit_jet_with_original_tail',value,
                   'Вводим 1/x или 1/n, который стремится к нулю справа на исходном хвосте. Для целого индекса это допустимая подпоследовательность положительного вещественного подхода.',
                   'Проверяем исходные корни и логарифмы через их определения. Вычисляем ведущий член в новой положительной координате.',
                   original_tail=mode,root_and_log_guards=guards,reduction=proof)
    if mode=='finite_point':
        if raw[0]=='rpow':
            from tasks import source
            if not params:
                try:return constant_power_bases(raw,var,point,side,mode,params,conditions,library)
                except Unsupported:pass
            logarithm=('mul',raw[2],('ln',raw[1]));proof,exponent=exact_neighborhood_limit(source(logarithm),var,point,side,params,conditions,library)
            require(not isinstance(exponent,dict),'The logarithmic characteristic differs across source approaches')
            value=ZERO if exponent=='-inf' else '+inf' if exponent=='+inf' else m.simplify(('exp',exponent))
            return ans('positive_base_logarithmic_characteristic',value,
                       'Доказываем положительность исходной базы в нужной проколотой области. Переходим к произведению показателя на логарифм базы.',
                       'Из проверенного предела логарифма получаем предел исходной степени.',
                       original=raw,original_guards=guards,logarithmic_limit=exponent,checked_local_germs=proof)
        proof,value=germ_limit(dict(kind='limit',expression=lowered,variable=var,parameters=params,
                                  stated_conditions=conditions,approach=dict(point=point,side=side)),library,orders=(2,4,6,8),split=True)
        return ans('elementary_source_notation_to_local_germs',value,
                   'Сохраняем напечатанную сторону и область корней и логарифмов. Для каждой допустимой ветви вычисляем локальные коэффициенты в исходной точке.',
                   original=raw,root_and_log_guards=guards,local_proof=proof)
    raise Unsupported('This signed infinity or discontinuity needs its own full source proof')


def lattice_monomial(e,n,k,ctx):
    """Factor one monomial in the running index and the bound counting index."""
    if e==n:return ONE,Fraction(1),Fraction(0)
    if e==k:return ONE,Fraction(0),Fraction(1)
    if m.constant_defined(e,ctx) and not m.contains(e,k):return e,Fraction(0),Fraction(0)
    op=e[0]
    if op in ('mul','div'):
        a,b,c=lattice_monomial(e[1],n,k,ctx);u,v,w=lattice_monomial(e[2],n,k,ctx)
        if op=='mul':return times(a,u),b+v,c+w
        require(m.sign(u,ctx) in (-1,1),'A fixed array scale divisor may vanish')
        return quotient(a,u),b-v,c-w
    if op=='sqrt' and e[1] in (n,k):return ONE,Fraction(e[1]==n,2),Fraction(e[1]==k,2)
    if op=='pow':
        a,b,c=lattice_monomial(e[1],n,k,ctx);p=e[2]
        require(p>0 or m.sign(a,ctx) in (-1,1),'An original array factor has unproved nonzero base')
        return m.simplify(m.power(a,p)),b*p,c*p
    raise Unsupported('No monomial array scale')


def previous_array_limit(task,library):
    from limit_proofs import local_coefficients
    from operations import expression_positions
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable_domain','fixed_parameters','method_requirement'})
    require(g.get('variable_domain')=='positive_integers' and re.fullmatch(r'use the previous uniform-array theorem\d*',g.get('method_requirement','')),
            'The original array domain and the required uniform comparison theorem must be bound')
    text=g['expression'];shape=re.fullmatch(r'(sum|product)_\{('+NAME+r')=1\}\^('+NAME+r')\s*(.+)',text)
    require(shape is not None,'Expected a complete initial segment of the integer lattice')
    kind,j,index,body=shape.groups();names=g['fixed_parameters'];n=('v',index);k=sym(j)
    require(j!=index and j not in names and index not in names,'The bound array index would capture an original parameter')
    ctx=m.context(dict(variable=index,parameters=names,parameter_conditions=given));f=m.parse(body,index,[*names,j])
    small='arraySmall'
    while small in [*names,index,j]:small+='_'
    t=('v',small);selected=None
    for _,x in expression_positions(f):
        if not m.contains(x,n) or not m.contains(x,k):continue
        try:c,degree,walk=lattice_monomial(x,n,k,ctx)
        except Unsupported:continue
        if not (walk>0 and degree < -walk):continue
        f0=m.substitute(f,{x:times(c,t)})
        if m.contains(f0,n) or m.contains(f0,k):continue
        selected=(x,c,degree,walk,f0);break
    require(selected is not None,'No shared shrinking lattice scale was found in the original term')
    x,c,degree,walk,f0=selected
    if kind=='product':f0=('ln',f0)
    jet,_,transport=local_coefficients(f0,small,'0','right',6,library,names,given)
    coeffs=[(m.num(r),b) for r,b in jet[1]];require(coeffs and coeffs[0][0] is not None and coeffs[0][0]>0,'No positive leading order for the array contribution')
    order,coefficient=coeffs[0];total_power=1+order*(degree+walk)
    require(total_power<=0 and m.num(jet[2])>order and all(p>order for p,_ in coeffs[1:]),
            'The selected leading term does not yet bound a finite aggregate limit')
    mass=ONE if walk*order==0 else q(1/(1+walk*order));reference=mass if total_power==0 else ZERO
    raw_value=times(coefficient,reference);value=('exp',raw_value) if kind=='product' else raw_value
    return ans('uniform_array_equivalence_after_detected_scale',m.simplify(value),
               'Ищем внутри исходного слагаемого общий степенной масштаб k^r n^s. На всех целых k от 1 до n он равномерно мал, поскольку r+s<0.',
               'Сравниваем вклад с его первым ненулевым мономом по теореме о равномерной малости массива. Для нулевого коэффициента вывод даёт та же оценка остатка.',
               'Сумму степеней k сравниваем через соседние интегралы, сохраняя все исходные границы. Для произведения применяем теорему к логарифмам положительных на хвосте множителей.',
               source_binder=(j,1,index),detected_scale=x,coefficient=c,degree_in_index=q(degree),degree_in_binder=q(walk),
               jet=jet,jet_transport=transport,power_sum_exponent=q(walk*order),reference_limit=reference,outer_operator=kind)


def finite_lattice_sums(task,kind,library,request):
    from finite_sums import polynomial_primitive
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable_domain','fixed_parameters','variable','goal','approach'},('printed_hint',))
    require(task.get('printed_hint') is None or re.fullmatch(r'См\. пример \d+\.',task['printed_hint']),'Additional source method on the finite sum')
    text=g['expression'];var=g.get('variable','n');n=('v',var);params=g.get('fixed_parameters',[])
    require(g.get('variable_domain','positive_integers')=='positive_integers' and given in ([],[var+' positive integer']),
            'The printed index and fixed parameters must be bound')
    pattern=r'sum_\{('+NAME+r')=(\d+)\}\^\{?(('+NAME+r')(?:-1)?)\}?'
    binders=list(re.finditer(pattern,text))
    require(binders and all(x[4]==var for x in binders),'No supported finite sum on the original index')
    from ordinary_series import polynomial_coefficients
    marker='finiteMass';names=[marker+'_'*i for i in range(len(binders))]
    require(not set(names)&{var,*params},'No free symbol for the bounded sum')
    formal_text='';cursor=0;sums=[]
    for binder,name in zip(binders,names):
        k,lo,hi=binder.groups()[:3];lo=int(lo)
        require(lo in (0,1) and k not in [var,*params],'An invalid first index or bound variable was introduced')
        require(binder.start()>=cursor,'Nested finite sums need a separate reduction')
        rest=text[binder.end():];pad=len(rest)-len(rest.lstrip());rest=rest.lstrip();leading=text[cursor:binder.start()]
        if rest.startswith('('):
            body,end=subexpression(rest,0)
            if end<len(rest) and re.match(r'\^\d+',rest[end:]):
                power_suffix=re.match(r'\^\d+',rest[end:])[0];body='('+body+')'+power_suffix;end+=len(power_suffix)
        else:
            plain=re.match(r'('+NAME+r')(?:\^(\d+))?',rest);require(plain and plain[1]==k,'A finite bound summand is missing')
            body=plain[0];end=plain.end();trailing=rest[end:]
            if len(binders)==1 and not leading and trailing.startswith('/'+var+'^'):
                normal=re.match(r'/'+re.escape(var)+r'\^(\d+)',trailing);require(normal,'Unknown sum scaling');end+=normal.end()
                leading='(1/'+var+'^'+normal[1]+')*'
        formal_text+=leading+name;cursor=binder.end()+pad+end
        body_raw=m.parse(body,k,[*params,var]);ks=('v',k)
        ctx=dict(variable=k,parameters=[*params,var],assumptions=[dict(symbol=var,relation='positive')])
        # The source is a polynomial in the bound index with fixed coefficients on each lattice.
        co=polynomial_coefficients(body_raw,ks,ctx);upper=m.parse(hi,var,params);total=ZERO;terms=[]
        for order,c in sorted(co.items()):
            require(0<=order<=8,'The needed elementary power-sum identity is out of scope')
            polynomial=polynomial_primitive(tuple(Fraction(i==order) for i in range(order+1)),Fraction(1),k)
            component=plus(m.substitute(polynomial,{ks:upper}),m.neg(m.substitute(polynomial,{ks:q(lo-1)})))
            c=m.substitute(c,{sym(var):n});total=plus(total,times(c,component));terms.append((order,c,component))
        sums.append(((k,lo,hi),terms,total))
    formal=m.parse(formal_text+text[cursor:],var,[*params,*names])
    reduced=m.substitute(formal,{sym(name):row[2] for name,row in zip(names,sums)})
    reduction,value=reciprocal_limit(reduced,var,params,[],library)
    (bounds,terms,total),more=sums[0],sums[1:]
    extra=dict(further_sums=more) if more else {}
    return ans('extract_finite_lattice_polynomial_coefficients',value,
               'Выделяем конечный сумматор внутри цели и сохраняем его нижнюю и верхнюю границы. Раскладываем слагаемое по степеням связанного индекса.',
               'Находим формулы конечных степенных сумм через проверенное конечное приращение. Подставляем их в исходное выражение до вычисления предела.',
               source_bounds=bounds,sum_terms=terms,exact_sum=total,reduction=reduction,**extra)


def directed_output_limit(task,library):
    import operations as op
    from limit_proofs import local_coefficients,germ_limit
    from tasks import source
    g,conditions=bound_packet(task,{'variable','expression','approach','parameters','goal','output_direction'})
    d=g['output_direction'];var=g['variable'];expr=g['expression'];params=g.get('parameters',[]);a=g['approach']
    require(d in ('from above','from below') and len(a)<=3 and a.get('side') in ('both','left','right'),'The exact output direction must be verified')
    point={'+infinity':'+inf','-infinity':'-inf'}.get(a['point'],a['point']);side=a['side']
    if a.get('mode') in ('positive_infinity','negative_infinity'):side=a['mode']
    kind=task.get('kind',task.get('task_type'));copy=dict(task)
    copy['goal']={k:v for k,v in g.items() if k!='output_direction'};nested_scalar_packet(copy)
    domain=dict(kind='limit',expression=expr,variable=var,parameters=params,stated_conditions=conditions,approach=dict(point=point,side=side))
    proof,limit=germ_limit(domain,library,split=False)
    require(isinstance(limit,tuple),'A strict output side needs an already established finite limit')
    residual=plus(m.parse(expr,var,params),m.neg(limit));sides=[]
    for scope in proof['sides']:
        local=scope['side'];jet,ctx,transport=local_coefficients(residual,var,point,local,max(4,scope['order']),library,params,conditions)
        sign=op.near_sign(jet,ctx)
        require(sign==(1 if d=='from above' else -1),'The claimed strict output side is not established')
        sides.append(dict(direction=local,transport=transport,residual=jet,strict_sign=sign))
    return ans('prove_side_of_limit_by_sign_of_residual',dict(limit=limit,output_direction=d),
               'Сначала вычисляем сам предел. Затем вычитаем его из исходной функции и устанавливаем строгий знак остатка на каждой указанной стороне.',
               limit_proof=proof,checked_error=sides)


def square_root_phase(e,n):
    from polynomial import NotRational,rf
    require(e[0]=='sqrt','Expected the radical phase')
    try:p,d=rf(e[1],n[1])
    except NotRational:raise Unsupported('The original inner polynomial is not bound') from None
    require(len(d)==1 and len(p)==3 and p[2]==d[0],'No monic square-root phase in the running index')
    return q(p[1]/d[0]),q(p[0]/d[0])


def integer_phase_tail(task,kind,library):
    from tasks import source
    g,given=bound_packet(task,{'expression','variable','variable_domain','approach','parameters','goal'})
    require(not given and g.get('variable_domain','positive_integers')=='positive_integers' and not g.get('parameters'),
            'A positive integer tail with fixed coefficients is required')
    var=g.get('variable','n');n=('v',var);raw=m.parse(g['expression'],var)
    if kind=='integer_phase_sequence_limit':
        require(g.get('approach','positive integer tail')=='positive integer tail','The proof needs the original integer lattice')
        core,p=(raw[1],raw[2]) if raw[0]=='pow' else (raw,1)
        require(core[0]=='sin' and type(p) is int and p>0,'Expected an integral power of a sine phase')
        phase=core[1];require(phase[0]=='mul' and m.PI in phase[1:],'The original phase does not contain π')
        radical=phase[2] if phase[1]==m.PI else phase[1];B,C=square_root_phase(radical,n)
        shift=times(q(1,2),B);harmonic=m.simplify(('sin',times(m.PI,shift)))
        val=m.simplify(m.power(harmonic,p))
        if p%2 and val!=ZERO:val=dict(status='does_not_exist',even_limit=val,odd_limit=m.neg(val))
        return ans('integer_phase_after_radical_rationalization',val,
                   'Вычитаем из корня целый индекс и рационализуем. Разность стремится к половине линейного коэффициента под корнем.',
                   'Снимаем прибавление nπ по чётности. Чётная степенная фаза сохраняется, нечётную проверяем на обоих классах.',
                   original_phase=phase,coefficients=(B,C),shift_limit=shift,integer_power=p)
    require(raw[0]=='rpow' and raw[1][0]=='add' and raw[1][1]==ONE and raw[1][2][0]=='div' and raw[1][2][2]==n and raw[2][0]=='csc',
            'No common alternating factor in the logarithmic characteristic')
    parity=raw[1][2][1];phase=raw[2][1]
    require(parity==('rpow',q(-1),n) and phase[0]=='mul' and m.PI in phase[1:],'The original parity, power, and phase do not match')
    radical=phase[2] if phase[1]==m.PI else phase[1];B,C=square_root_phase(radical,n)
    require(B==ZERO and C!=ZERO,'The matched first inverse power is not nonzero')
    scale=quotient(q(2),times(m.PI,C));value=m.simplify(('exp',scale))
    return ans('cancel_same_parity_in_power_characteristic',value,
               'На исходном целом хвосте логарифм базы содержит первым членом (−1)^n/n. Фаза синуса после рационализации равна nπ плюс πC/(2n) с меньшим остатком.',
               'В синусе появляется тот же знак (−1)^n. Делим после проверки ненулевости на хвосте, получаем общий предел логарифма и возвращаем экспоненту.',
               original_base=raw[1],original_exponent=raw[2],leading_correction=C,logarithmic_limit=scale)


def bounded_radical_oscillation(task):
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','point','side','original_domain'})
    require(g.get('point')=='0' and g.get('side')=='both' and not given,'Expected a relative approach to zero on both sides')
    raw=m.parse(g['expression'],'x');v=('v','x')
    require(raw[0]=='mul' and raw[1]==v and raw[2][0]=='sqrt' and raw[2][1][0] in ('cos','sin'),
            'No bounded radical multiplied by a vanishing factor')
    wave,phase=raw[2][1];numerator=phase[1] if phase[0]=='div' and phase[2]==v else None
    require(numerator is not None and m.num(numerator) not in (None,0),'Need a nonzero reciprocal phase scale')
    require(g.get('original_domain') in ('x!=0 and '+source(raw[2][1])+'>=0',f'x!=0 and {wave}({source(numerator)}/x)>=0'),
            'The relative domain must bind the original radicand')
    return ans('bounded_radical_squeeze_on_relative_domain',ZERO,
               'На исходной реальной области радикал заключён между нулём и единицей. Поэтому модуль всего выражения ограничен |x|.',
               'Для обеих сторон предъявляем точки с фазой, где радикал определён, на целых сдвигах этой фазы.',
               checked_domain=g['original_domain'],phase=phase,witness_phase=q(0) if wave=='cos' else times(q(1,2),m.PI))


def floor_limit_or_boundary(task,kind,library):
    from tasks import source
    g,given=bound_packet(task,{'expression','point','side','variable','requests','approach','domain'})
    var=g.get('variable','x');v=('v',var);text=g['expression'];token=re.escape(var)
    if kind=='floor_function_limit':
        require(not given and re.fullmatch(token+r'\*floor\(1/'+token+r'\)',text) and g.get('point','0')=='0',
                'The original floor expression is not the reciprocal normalization')
        return ans('floor_reciprocal_error_bound',ONE,
                   'В исходной проколотой окрестности разность между 1/x и его целой частью принадлежит [0,1). Умножение на x даёт модуль ошибки меньше |x| с обеих сторон.',
                   variable=var,two_sides=True)
    match=re.fullmatch(r'f\((-?\d+)\)',g['requests'][0]);require(match is not None,'Expected an integer cell boundary and full point query')
    point=int(match[1]);require(not given and g['requests']==[f'f({point})',f'left limit at{point}',f'right limit at{point}'],
                                  'Need the point value and both printed one-sided limits')
    label='floorValue';exact=text.replace('floor('+var+')',label);require(exact!=text,'No bound floor operation')
    raw=m.parse(exact,var,[label]);eval_at=lambda k:m.simplify(m.substitute(raw,{v:q(point),sym(label):q(k)}))
    ctx=dict(parameters=[],assumptions=[])
    a,b=(eval_at(k) for k in (point-1,point))
    require(all(m.constant_defined(x,ctx) for x in (a,b)) and not domain_operations(raw),
            'Another operation is not known continuous at both cell ends')
    return ans('integer_cell_boundary_traces',dict(value_at_point=b,left_limit=a,right_limit=b),
               'Заменяем целую часть постоянными значениями на двух соседних открытых клетках. Отдельно подставляем фактическое значение в самой границе.',
               integer_cell_boundary=point,cell_values=(point-1,point),continuous_piece=raw)


def domain_operations(raw):
    from tasks import domain_conditions
    return domain_conditions(raw)


def relative_radical_at_parameter(task,library):
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable','point','printed_side','parameters','goal'})
    var=g['variable'];v=('v',var);x=g['point'];params=g['parameters'];a=sym(x)
    require(g.get('printed_side')=='both/unspecified' and not given and params==[x],'Need the original unrestricted radical parameter')
    raw=m.parse(g['expression'],var,params);sqrt=lambda v:('sqrt',v);diff=plus(v,m.neg(a));D=plus(m.power(v,2),m.neg(m.power(a,2)))
    require(raw[0]=='div' and same_value(raw[1],plus(sqrt(v),m.neg(sqrt(a)),sqrt(diff))) and same_value(raw[2],sqrt(D)),
            'No common square-root scale in the original numerator and denominator')
    value=dict(cases=[dict(condition=x+'>0',value=quotient(ONE,sqrt(times(q(2),a))),side='right'),
                      dict(condition=x+'=0',value='+inf',side='right'),dict(condition=x+'<0',value='no_original_real_domain')])
    return ans('relative_radical_parameter_domain_cases',value,
               'При положительном параметре исходная область подходит только справа. Рационализуем первое приращение корня и выносим общий масштаб √(x−a).',
               'При нулевом параметре знаменатель меняет порядок, и отдельное точное выражение расходится. Отрицательный исходный параметр делает √a неопределённым.',
               original=raw,derived_shift=diff)


def directional_difference(task,library):
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable','approach','parameters','goal'})
    var=g['variable'];v=('v',var);params=g['parameters'];a=g['approach'];label=re.escape(var)
    body=re.fullmatch(r'(\w+)=limit_\{'+label+r'->\+infinity\}f\('+label+r'\)-limit_\{'+label+r'->-infinity\}f\('+label+r'\), f\('+label+r'\)=(.+)',g['expression'])
    require(body is not None and not given and len(params)==2 and a.get('point')=='two signed infinities',
            'The two original directional requirements are not both bound')
    raw=m.parse(body[2],var,params);terms=[]
    require(raw[0]=='ln' and raw[1][0]=='div','Expected a logarithm of two near-conjugate sums')
    for source_term in raw[1][1:]:
        require(source_term[0]=='add' and source_term[1]==v and source_term[2][0]=='sqrt','No matching radical conjugate')
        rad=source_term[2][1];choices=[p for p in params if same_value(rad,plus(m.power(v,2),m.power(sym(p),2)))]
        require(len(choices)==1,'Every quadratic coefficient must be checked against a fixed parameter');terms.append(choices[0])
    A,B=terms;required=[A+'!=0',B+'!=0']
    require(A!=B and set(task.get('derived_domain_conditions',[]))<=set(required),'The source positive-log domain does not bind both amplitudes')
    x,y=(m.power(sym(k),2) for k in (A,B));left=('ln',quotient(x,y))
    return ans('difference_of_checked_directional_radical_limits',dict(condition=required,positive_limit=ZERO,negative_limit=left,value=('ln',quotient(y,x)),
                                                                         otherwise='the original negative tail is not defined'),
               'На положительном хвосте обе суммы эквивалентны 2x. Для отрицательного направления умножаем каждую сумму на сопряжённое выражение.',
               'Обе исходные суммы на отрицательном хвосте положительны только при ненулевых квадратных коэффициентах. Их отношение стремится к отношению квадратов.',
               'Подставляем оба проверенных направленных предела в исходную разность.',original=raw,positive_direction='+inf',negative_direction='-inf')


def geometric_factorial_tails(task,kind,library):
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable','variable_domain','parameters','parameter','goal','source_hint','target'})
    text=g['expression'];n=g.get('variable','n');x=('v',n)
    if kind=='prove_sequence_identity':
        m0=re.fullmatch(r'\(1\+('+NAME+r')/'+re.escape(n)+r'\)\^'+re.escape(n),text)
        require(m0 is not None and not given and g.get('parameter')=='fixed real '+m0[1] and g.get('target')=='exp('+m0[1]+')'
                and g.get('variable_domain')=='positive_integers','The original exponential identity is not fully bound')
        p=sym(m0[1]);value=('exp',p)
        return ans('logarithm_of_integer_exponential_approximation',value,
                   'Для каждого фиксированного параметра основание положительно на целом хвосте. Логарифм степени равен n ln(1+x/n), его первый член равен x.',
                   'Экспоненцируем доказанный предел, включая нулевой параметр и все допустимые исходные ранние целые степени.',source_index=n,parameter=p)
    prefix=re.fullmatch(r'sum_\{('+NAME+r')=0\}\^('+NAME+r') ('+NAME+r')\^\1/\1!',text)
    if kind=='prove_exponential_series_limit' or prefix:
        require(prefix is not None and not given and g.get('parameter')=='fixed real '+prefix[3] and prefix[2]==n,
                'The original exponential coefficients or their finite index range differ')
        return ans('exponential_taylor_tail_from_factorial_ratio',('exp',sym(prefix[3])),
                   'Применяем формулу Тейлора к экспоненте до исходного конечного порядка. Модуль остатка не превышает exp(|x|)|x|^(n+1)/(n+1)!.',
                   'Отношение двух соседних мажорант стремится к нулю, значит остаток стремится к нулю.',
                   index=n,binder=prefix[1],fixed_argument=prefix[3],start=0)
    window=re.fullmatch(r'sum_\{('+NAME+r')=('+NAME+r')\+1\}\^\{(\d+)\*?\2\} ('+NAME+r')\^\1/\1!',text)
    if window:
        require(not given and int(window[3])>=2 and g.get('variable_domain')=='positive_integers' and g.get('parameter')=='fixed real '+window[4],
                'The factor range or source real parameter is unbound')
        return ans('finite_window_inside_absolute_factorial_tail',ZERO,
                   'Модуль конечного окна не превосходит всего абсолютного хвоста. Для фиксированного аргумента отношение |x|/(k+1) на хвосте строго меньше единицы.',
                   'Геометрическая мера хвоста стремится к нулю, и она ограничивает исходное окно.',bound_variable=window[1],source_index=window[2],end_multiplier=int(window[3]),parameter=window[4])
    product=re.fullmatch(r'product_\{('+NAME+r')=0\}\^('+NAME+r')\(1\+('+NAME+r')\^\(2\^\1\)\)',text)
    if product:
        k,n,p=product.groups()
        require(given==[f'abs({p})<1'] and g.get('variable_domain')=='positive_integers' and g.get('parameter')=='fixed real '+p,
                'The original product needs a strict geometric contraction')
        return ans('doubling_exponents_product_telescopes',quotient(ONE,plus(ONE,m.neg(sym(p)))),
                   'Проверяем тождество (1−u)(1+u)=1−u². Последовательно берём u=x^(2^k), поэтому умножение исходного произведения на 1−x оставляет 1−x^(2^(n+1)).',
                   'При |x|<1 последний член стремится к нулю, и исходный делитель 1−x ненулевой.',first=0,last=n,bound_variable=k,contraction=given[0])
    if kind=='factorial_phase_limit':
        require(not given and g.get('variable_domain')=='positive_integers' and ('source_hint' not in g or re.fullmatch(r'formula\(\*\) of example\d+',str(g['source_hint']))),
                'The factorial sequence or printed expansion reference is not bound')
        match=re.fullmatch(r'('+NAME+r')\*sin\((\d+)\*pi\*e\*factorial\(\1\)\)',text)
        require(match is not None and int(match[2])%2==0,'The phase must remove the integer exponential prefix by a full period')
        c=q(int(match[2]));v=times(c,m.PI)
        return ans('integer_factorial_prefix_in_periodic_phase',v,
                   'Представляем e экспоненциальным рядом. Умножение его конечной части на n! даёт целое, которое убирается полной периодичностью синуса.',
                   'Хвост после этого умножения равен 1/(n+1) плюс O(1/n²) по отношению соседних факториалов. Применяем sin t~t к оставшейся фазе.',
                   lattice=match[1],phase_scale=v,integer_prefix='sum n!/k!, k=0..n')
    raise Unsupported('No checked factorial tail or doubling product on the original lattice')


def fixed_bound_product(task,kind):
    from tasks import source
    from verify import same_value
    g,given=bound_packet(task,{'expression','variable','point','side','input_approach','parameters','parameter_n',
                               'numerator','denominator','required_directions','goal'})
    if kind=='finite_product_integer_parameter_limit':
        z=re.fullmatch(r'product_\{('+NAME+r')=1\}\^('+NAME+r')\(('+NAME+r')\^\1\+1\)',g['numerator'])
        require(z is not None and g.get('parameter_n')=='positive integer' and given==[z[2]+' positive integer']
                and g.get('input_approach')=='magnitude infinity; both admissible signed tails','The product degree or original unsigned approach is not bound')
        k,n,x=z.groups();den=g['denominator'];require(den==f'(({n}*{x})^{n}+1)^(({n}+1)/2)','The source outer exponent changes the leading degree')
        deg=times(q(1,2),sym(n),plus(sym(n),ONE));val=('rpow',sym(n),m.neg(deg))
        return ans('integer_product_degree_and_signed_tail_parity',dict(positive_limit=val,
                   negative_limit=dict(cases=[dict(condition=n+' ≡ 2 (mod 4)',value=m.neg(val)),dict(condition='otherwise positive integer',value=val)]),
                   two_tail_exists_when=n+' is not congruent to 2 modulo 4'),
                   'У каждого множителя сохраняем его ведущую целую степень. Общая степень равна сумме индексов от 1 до n.',
                   'На отрицательном хвосте при нечётном n целая степень знаменателя создаёт тот же знак, что и числитель. Для чётного n знаменатель положителен, и паритет суммы степеней даёт исключительный класс.',
                   degree=deg,index=k,upper=n,variable=x)
    if kind=='finite_product_root_limit':
        text=g.get('expression')
        if text is None:
            require(g.keys()=={'numerator','denominator','point','side','parameter_n'} and all(isinstance(v,str) for v in g.values())
                    and g['side']=='both' and g['parameter_n']=='positive integer product endpoint',
                    'The split source must declare its full approach and the integer product endpoint')
            text=g['numerator']+'/'+g['denominator']
        z=re.fullmatch(r'product_\{('+NAME+r')=2\}\^('+NAME+r')\(1-root_\1\(('+NAME+r')\)\)/\(1-\3\)\^\(\2-1\)',text)
        require(z is not None and len(set(z.groups()))==3 and g.get('point','1')=='1' and not given
                and g.get('side','both')=='both' and g.get('variable',z[3])==z[3],
                'The bound roots and exactly one common first difference per factor are required')
        k,n,x=z.groups();val=dict(value='1/factorial('+n+')',index_domain=n+' positive integer')
        if 'expression' not in g:
            require(task.get('source_statement')==f"Найти lim_{{{x}->{g['point']}}} {text}.",
                    'The split quotient disagrees with its source display')
        return ans('finite_product_of_first_root_differences',val,
                   'Сохраняем связанный индекс от 2 до n. Для каждого такого корня локальное отношение первого приращения к 1−x имеет предел 1/k.',
                   'Число множителей равно n−1, поэтому исходный знаменатель в точности распределяется на эти отношения. Произведение коэффициентов равно 1/n!.',
                   index=k,upper=n,variable=x,point=ONE)
    text=g['expression']
    if kind=='variable_degree_root_product_limit':
        z=re.fullmatch(r'root_('+NAME+r')\(product_\{('+NAME+r')=1\}\^\1\(('+NAME+r')\+('+NAME+r')\[\2\]\)\)-\3',text)
        require(z is not None and g.get('input_approach')=='positive_infinity' and g.get('parameters')==f'fixed real {z[4]}[{z[2]}], positive integer {z[1]}' and not given,
                'The variable product degree, fixed coefficients or positive tail are unbound')
        n,k,x,a=z.groups()
        return ans('root_of_finite_product_leading_average',dict(value=f'sum_{{{k}=1}}^{n} {a}[{k}] / {n}'),
                   'На положительном хвосте выносим x^n из произведения. Линейный коэффициент оставшегося произведения — сумма его исходных сдвигов.',
                   'Разложение корня степени n делит этот коэффициент на n. После вычитания x остаётся среднее исходных фиксированных сдвигов.',
                   variables=(n,k,x,a))
    if kind=='integer_power_two_tail_limit':
        n=sym('n');x=('v','x');raw=m.parse(text,'x',['n']);half=('sqrt',plus(m.power(x,2),q(-1)))
        expected=('div',plus(('rpow',plus(x,m.neg(half)),n),('rpow',plus(x,half),n)),('rpow',x,n))
        require(same_value(raw,expected) and given==['n positive integer'] and g.get('input_approach')=='positive_infinity' and g.get('required_directions')==['positive_infinity'],
                'The original two symmetric integer powers or right tail differ')
        return ans('symmetric_radical_power_normalization',('rpow',q(2),n),
                   'На исходном положительном хвосте делим каждое основание на x. Их пределы равны 0 и 2. Положительная целая степень непрерывна в обеих точках.',
                   original=raw,normalized_root=('sqrt',plus(ONE,m.neg(m.power(x,-2)))))
    raise Unsupported('No indexed product identity for the original bounds')


def local_error_and_quantifiers(task,kind):
    from math import isqrt
    from tasks import source
    val=lambda s:m.num(m.simplify(m.parse(str(s),None)))
    if kind=='error_tolerance_interval':
        require(not set(task)-META-{'side_cm','design_area_cm2','area','max_absolute_error_cm2'} and task['area']=='x^2',
                'The requested dimensional relation must be the square law')
        a,A=map(val,(task['side_cm'],task['design_area_cm2']));require(a is not None and A==a*a and a>0,'Nominal side and area do not match')
        text=task['max_absolute_error_cm2'];root=lambda x:m.simplify(('sqrt',x))
        if re.fullmatch(NAME,text):
            E=sym(text);lower=root(('max',ZERO,plus(q(A),m.neg(E))));upper=root(plus(q(A),E));scope=text+'>=0'
        else:
            E=val(text);require(E is not None and E>=0,'The area tolerance must be nonnegative')
            lower=root(q(max(0,A-E)));upper=root(q(A+E));scope='nonnegative edge lengths'
        return ans('invert_monotone_measure_for_error_interval',dict(edge_interval_cm=(lower,upper),unit='cm',conditions=scope),
                   'Погрешность площади задаёт два точных неравенства для квадрата ребра. На неотрицательной области обе границы можно обратить квадратным корнем.',
                   'Если нижняя граница площади отрицательна, действует естественная нижняя граница ребра.',nominal_area=q(A),nominal_edge=q(a))
    if kind=='propagate_measurement_error':
        require(not set(task)-META-{'edge_m','volume','max_absolute_error_m3'} and task['volume']=='x^3','The full dimensional propagation question is required')
        a,b=map(val,task['edge_m']);e=val(task['max_absolute_error_m3'])
        require(a is not None and b is not None and e is not None and 0<a<=b and 0<=e<(a+b)**3-b**3,'The required finite original measurement range is not bound')
        d=plus(('cbrt',q(b**3+e)),q(-b))
        return ans('sharp_worst_case_cubic_error_radius',dict(maximum_absolute_edge_error_m=d,volume_error_m3=q(e)),
                   'Для выпуклого возрастающего куба увеличение на фиксированную величину даёт больший модуль, чем уменьшение. Верхняя ошибка возрастает с исходным ребром.',
                   'Поэтому крайний объём задаётся наибольшим исходным ребром. Обращаем точное кубическое неравенство, сохраняя единицы и оба знака ошибки.',edge_range=(q(a),q(b)),sharp_edge=q(b))
    if kind=='maximal_error_neighborhood':
        require(not set(task)-META-{'expression','at','value','epsilon','n','instances'} and task['expression']=='sqrt(x)'
                and task['n']=='integer n>=0','The square-root neighborhood and original integer tolerance parameters are required')
        a,b=map(val,(task['at'],task['value']));require(a is not None and b is not None and a==b*b and b>1,'The center or value differs from the original root')
        match=re.fullmatch(r'(\d+)\^\(-n\)',task['epsilon']);instances=task['instances']
        require(match is not None and int(match[1])>=1 and isinstance(instances,list) and all(type(i) is int and 0<=i<=64 for i in instances),'The required tolerance instances are not bound')
        B=int(match[1]);e=('rpow',q(B),m.neg(sym('n')));left=plus(times(q(2*b),e),m.neg(m.power(e,2)))
        right=plus(times(q(2*b),e),m.power(e,2));rows=[]
        for i in instances:
            z=Fraction(1,B**i);rows.append(dict(n=i,delta=q(2*b*z-z*z),full_neighborhood=(q((b-z)**2),q((b+z)**2))))
        return ans('sharp_root_neighborhood_from_two_inverse_bounds',dict(maximal_symmetric_radius=left,distances=(left,right),instances=rows),
                   'Обращаем неравенства между двумя положительными границами для квадратного корня. Расстояния от центра до их образов различны.',
                   'Максимальная симметричная окрестность ограничена меньшим расстоянием. Подставляем все напечатанные значения параметра.',threshold_base=B,center=q(a))
    if kind=='epsilon_delta_proof_table':
        require(not set(task)-META-{'expression','at','epsilons'} and task['expression']=='x^2','Only the original smooth square law is checked here')
        a=val(task['at']);require(a is not None,'Unknown original center');L=2*(abs(a)+1)
        rows=[]
        for s in task['epsilons']:
            if s=='...':continue
            e=val(s);require(e is not None and e>0,'Every printed tolerance must be positive');rows.append(dict(epsilon=q(e),delta=q(min(1,e/L))))
        return ans('bounded_derivative_in_fixed_epsilon_delta_neighborhood',dict(table=rows,forall_epsilon='delta=min(1,epsilon/'+str(L)+')'),
                   'Фиксируем окрестность радиуса 1, где модуль производной квадрата ограничен. Применяем оценку по теореме о среднем.',
                   'Для любого ε выбираем меньшую из радиуса и отношения ε к границе производной. Заполняем все запрошенные строки.',center=q(a),lipschitz_bound=q(L))
    if kind=='maximal_delta_and_uniformity':
        require(not set(task)-META-{'expression','epsilon','base_points','uniformity_interval'} and task['expression']=='1/x',
                'A reciprocal source function with a full maximal-radius and uniformity request is needed')
        window=re.fullmatch(r'\(0,([^,]+)\)',task['uniformity_interval']);require(window is not None,'The interval must reach the singular endpoint')
        e,B=val(task['epsilon']),val(window[1]);require(e is not None and B is not None and e>0 and B>0 and e*B<1,'Both exact inverse thresholds must lie in their natural branch')
        point=[]
        for text in task['base_points'].split(','):
            if text.strip()=='...':continue
            x=val(text.strip());require(x is not None and 0<x<B,'A requested original base point is outside the interval');point.append(dict(at=q(x),delta=q(e*x*x/(1+e*x))))
        X=sym('x0');d=quotient(times(q(e),m.power(X,2)),plus(ONE,times(q(e),X)))
        return ans('sharp_reciprocal_neighborhood_and_uniform_failure',dict(maximal_delta=d,values=point,uniform_delta_exists=False),
                   'Обращаем два ограничения на 1/x отдельно. Ближайшая к x₀ недопустимая точка находится слева и задаёт острый радиус.',
                   'При приближении x₀ к нулю этот радиус стремится к нулю. Поэтому одного положительного δ для всего напечатанного интервала нет.',epsilon=q(e),window=task['uniformity_interval'])
    if kind=='quantifier_negation':
        require(not set(task)-META-{'given'} and task['given']=='f(x0) is defined','A specified original function value is needed')
        return ans('negate_continuity_neighborhood_quantifiers',dict(statement='exists epsilon0>0, for every delta>0, exists x in the original domain such that |x-x0|<delta and |f(x)-f(x0)|>=epsilon0'),
                   'Отрицаем кванторы определения непрерывности по очереди. Неравенство для аргумента остаётся строгим, а отрицание строгой оценки значения даёт знак больше или равно.',original_center='x0')
    require(kind=='geometric_epsilon_delta' and not set(task)-META-{'given','conclusion'} and task['given']=='graph y=f(x), continuous at a'
            and task['conclusion']=='abs(x-a)<delta implies abs(f(x)-f(a))<epsilon','The original geometric neighborhood statement is not bound')
    return ans('epsilon_strip_from_given_continuous_graph',dict(construction='choose a positive horizontal radius below the first exit from the open vertical epsilon strip; when no exit exists any available radius works'),
               'На данном графике берём открытую полосу между уровнями f(a)−ε и f(a)+ε. Непрерывность гарантирует положительную ширину участка возле a, полностью остающегося в полосе.',
               'Расстояние до ближайшего выхода из полосы снизу ограничивает допустимый горизонтальный радиус.',given_graph=True)


def recurrence_limit(task,kind):
    from integrals import affine
    from verify import same_value
    g,given=bound_packet(task,{'recurrence','parameter_domain','hypotheses','initial','printed_index','source_hint','goal'})
    r=g.get('recurrence','');name='iterState';Y=('v',name)
    if kind=='stable_recurrence_limit_theorem':
        h=g.get('hypotheses',[]);require(not given and len(h)==3,'The stable source loop requires precisely all three hypotheses')
        a=re.fullmatch(r'abs\(('+NAME+r')\)<1',h[0]);b=re.fullmatch(r'('+NAME+r')\[n\]->('+NAME+r')',h[2])
        require(a is not None and b is not None,'A contraction coefficient and a converging input are both required')
        match=re.fullmatch(re.escape(b[1])+r'\[n\]=('+NAME+r')\[n\]-'+re.escape(a[1])+r'\*\1\[n-1\]',h[1])
        require(match is not None,'The recurrence does not bind the original convergent input')
        alpha,B=sym(a[1]),sym(b[2]);value=quotient(B,plus(ONE,m.neg(alpha)))
        return ans('stable_affine_recurrence_with_vanishing_forcing',value,
                   'Вычитаем кандидат неподвижного уровня постоянной части. Полученная разность удовлетворяет той же линейной рекурсии с возмущением, стремящимся к нулю.',
                   'Конечный начальный вклад убывает геометрически. Позднее возмущение оценивается равномерной ошибкой, умноженной на сходящуюся геометрическую сумму.',
                   recurrence=h[1],contraction=h[0],forcing_limit=B)
    radical=re.fullmatch(r'('+NAME+r')\[1\]=sqrt\(('+NAME+r')\);\1\[n\+1\]=sqrt\(\2\+\1\[n\]\)',r)
    if radical:
        x,a=radical.groups();require(given==[a+'>0'],'The invariant positive-root interval requires the printed strict positivity')
        p=sym(a);root=times(q(1,2),plus(ONE,('sqrt',plus(ONE,times(q(4),p)))))
        return ans('monotone_square_root_iteration_on_invariant_interval',root,
                   'Решаем уравнение неподвижной точки и выбираем положительный корень. Отрезок от нуля до этого корня инвариантен.',
                   'Начальное значение не превосходит неподвижного. Возрастающее отображение и второй член запускают монотонную ограниченную последовательность. Её предел снова удовлетворяет уравнению.',
                   invariant_interval=(ZERO,root),parameter_positive=a,initial=('sqrt',p))
    one_step=re.fullmatch(r'('+NAME+r')\[n\]=(.+)',r)
    require(one_step is not None and not given,'The exact printed recurrence is needed')
    x=one_step[1];rest=one_step[2];first=g.get('initial');old=x+'[n-1]';older=x+'[n-2]'
    if isinstance(first,list) and older in rest:
        require(len(first)==2 and g.get('printed_index')=='n=2,3,...','Both initial data and the printed first index must remain')
        a=re.fullmatch(re.escape(x)+r'\[1\]=(.+)',first[0]);b=re.fullmatch(re.escape(x)+r'\[2\]=(.+)',first[1]);past='iterOlder'
        require(a is not None and b is not None,'Initial terms mismatch')
        F=m.parse(rest.replace(old,name).replace(older,past),name,[past]);A,R=affine(F,name)
        B,C=affine(m.substitute(R,{sym(past):('v',past)}),past);A,B=map(m.num,(A,B))
        require(A is not None and B is not None and C==ZERO and 0<B<1 and A+B==1,'No strict convex combination of consecutive terms')
        q0,q1=(m.simplify(m.parse(a[1],None)),m.simplify(m.parse(b[1],None)))
        require(all(m.num(z) is not None for z in (q0,q1)),'The initial values must be exact finite scalars')
        value=plus(q0,quotient(plus(q1,m.neg(q0)),q(1+B)))
        return ans('successive_difference_of_two_step_average',value,
                   'Вычитаем из рекурсии предыдущий член. Разность соседних членов умножается на минус вес более раннего члена.',
                   'Суммируем геометрическую последовательность разностей от заданного начала. Если напечатанная формула требует члена x₀, он определяется по n=2 и не меняет хвост.',
                   initial=(q0,q1),difference_ratio=q(-B),literal_previous_value=quotient(plus(q1,m.neg(times(q(A),q0))),q(B)))
    if isinstance(first,str) and 'parameter_domain' in g:
        d=re.fullmatch(r'0<=('+NAME+r')<=1',g['parameter_domain']);require(d is not None,'Both closed parameter endpoints are required')
        X=d[1];a=sym(X);text=rest.replace(old,name);f=m.parse(text,name,[X]);z=re.fullmatch(re.escape(x)+r'\[1\]=(.+)',first)
        require(z is not None and same_value(m.parse(z[1],None,[X]),quotient(a,q(2))),'The initial state differs from the source constant part')
        base=quotient(a,q(2));term=m.simplify(quotient(plus(f,m.neg(base)),m.power(Y,2)));c=m.num(term)
        require(c in (Fraction(-1,2),Fraction(1,2)),'A different quadratic iteration requires explicit interval construction')
        root=plus(q(1 if c>0 else -1),times(q(-1 if c>0 else 1),('sqrt',plus(ONE,times(q(-1 if c>0 else 1),a)))))
        return ans('quadratic_iteration_invariant_closed_parameter_range',root,
                   'На напечатанном замкнутом интервале параметра строим неотрицательную неподвижную точку из квадратного уравнения.',
                   'Для убывающей квадратичной карты исходный интервал инвариантен и есть строгое сжатие. Для возрастающей карты начальная точка ниже выбранной неподвижной, что даёт ограниченную монотонность также на граничном параметре.',
                   original_map=f,parameter=X,initial=base,quadratic_coefficient=q(c),closed_interval=(ZERO,ONE))
    if isinstance(first,str) and old in rest:
        z=re.fullmatch(re.escape(x)+r'\[0\]=(.+)',first);require(z is not None,'Original initial index must be zero')
        f=m.parse(rest.replace(old,name),name);t=m.num(m.simplify(m.parse(z[1],None)))
        require(f[0]=='div' and f[2]==('add',ONE,Y) and t is not None and t>0 and g.get('source_hint') in (None,'compare with fixed-point roots'),
                'Need the exact reciprocal map, positive start, and prescribed fixed-point comparison')
        c=m.num(f[1]);require(c is not None and 0<c<2,'Domain and strict contraction must hold for all original iterates')
        root=times(q(1,2),plus(('sqrt',q(1+4*c)),q(-1)))
        return ans('positive_reciprocal_iterates_contract_to_fixed_point',root,
                   'Все итерации положительны. Выбираем положительную неподвижную точку r и точно вычитаем её из следующего значения.',
                   'В модуле ошибка умножается на r/(1+y), строго не превосходящий заранее найденного r<1. Это доказывает сходимость по обоим знакам ошибки.',
                   initial=q(t),map_numerator=q(c),strict_ratio_bound=root)
    raise Unsupported('No invariant interval or lattice contraction has been derived')


def growth_relative_to_elementary_scale(task,kind,library):
    from tasks import source
    from verify import same_value
    if kind=='prove_no_power_order':
        require(not set(task)-META-{'schema','variable','approach','original_domain_policy','expression','parameters','given_infinitesimal_comparator','claim','requested_output'},
                'A complete relative-order source is required')
        var=task['variable']['symbol'];par=task['parameters'];name=par[0].get('symbol') if len(par)==1 else None
        require(name is not None and task['variable']=={'symbol':var,'domain':'real'} and par==[dict(symbol=name,domain='real',condition=name+'>0',quantifier='for_every')]
                and task.get('approach')==dict(point='0',direction='source_unqualified_finite') and task.get('given_infinitesimal_comparator')==var+'^'+name
                and task.get('requested_output')==['proof_for_all_positive_orders','natural_domain_qualification']
                and task.get('claim')==f'There is no {name}>0 for which lim(expression/{var}^{name})=k exists with finite k!=0.',
                'The positive-order quantifier, original comparator and requested conclusion must be preserved')
        v=('v',var);e=m.parse(task['expression'],var)
        if e==('div',ONE,('ln',v)):
            return ans('logarithmic_decay_not_comparable_to_any_power',dict(no_positive_power_order=True,comparison_limit='-inf',side='right'),
                       'На исходной правой области положим t=−ln x. Тогда отношение к любой x^p, p>0, равно −exp(p t)/t и уходит к минус бесконечности.',original=e)
        if e[0]=='exp' and same_value(e[1],m.neg(quotient(ONE,m.power(v,2)))):
            return ans('negative_exponential_below_every_algebraic_power',dict(no_positive_power_order=True,comparison_limit=ZERO,sides='each_original_real_side'),
                       'Выбираем t=1/x². Модуль отношения к любому положительному степенному масштабу равен t^(p/2) exp(−t), который стремится к нулю на обеих допустимых сторонах.',original=e)
        raise Unsupported('No proved relative logarithmic or exponential scale')
    text,var,point,side,mode,params,conditions,ctx=nested_scalar_packet(task)
    require(mode=='positive_infinity' and point in ('+inf','+infinity') and side=='both','An original positive tail is required')
    lowered,guards=lower_functions(text,var,params,ctx);v=('v',var);e=m.parse(lowered,var,params)
    require(e[0]=='div','No quotient for an exponential growth comparison')
    f,g=e[1:]
    if f[0]==g[0]=='rpow' and f[1]==v and g[2]==v and m.constant_defined(f[2],ctx) and m.constant_defined(g[1],ctx):
        require(m.sign(plus(g[1],q(-1)),ctx)==1 or g[1][0]=='s' and any(a['symbol']==g[1][1] and a['relation']=='greater_one' for a in ctx['assumptions']),
                'The source exponential base must be strictly greater than one')
        return ans('fixed_exponential_dominates_every_fixed_power',ZERO,
                   'На положительном хвосте логарифм отношения равен p ln x−x ln a. После деления на x его предел −ln a<0.',
                   'Поэтому исходный логарифм уходит к −∞, а отношение к нулю. Показатель p может быть любым фиксированным действительным.',log_power=f[2],exponential_base=g[1],source_conditions=conditions)
    if g[0]=='rpow' and g[1]==v and m.sign(g[2],ctx)==1:
        coefficient=ONE;an=f
        if f[0]=='div':an=f[1];coefficient=f[2]
        require(an==('ln',v) and m.constant_defined(coefficient,ctx) and m.nonzero(coefficient,ctx),'The original log base coefficient or positive power has not been proved')
        return ans('positive_power_dominates_logarithmic_scale',ZERO,
                   'Переходим к положительной бесконечной координате t=ln x. Числитель линейный по t, а знаменатель экспоненциальный с положительным фиксированным показателем.',
                   'Применяем сравнение экспоненты с линейным ростом. Постоянный коэффициент логарифмического основания определён и ненулевой.',source_power=g[2],log_base_factor=coefficient,original_guards=guards)
    raise Unsupported('No precise dominance claim for the original expression')


def quantified_growth_family(task,kind):
    common={'variable','original_domain_policy','approach','claim','requested_output','schema'}
    var=task['variable']['symbol'];v=('v',var)
    require(task['variable']==dict(symbol=var,domain='real'),'The original function variable is not an unrestricted real argument')
    if kind=='construct_and_prove_dominating_function':
        require(not set(task)-META-common-{'parameters','given'} and task['parameters']==[dict(symbol=var+'0',domain='real')]
                and task['given']==f'An arbitrary sequence of functions f_1({var}),f_2({var}),...,f_n({var}),... on {var}0<{var}<+inf.'
                and task['claim']==f'Construct f({var}) which as {var}->+inf grows faster than each f_n({var}), n=1,2,... .'
                and task['requested_output']==['function_construction','proof_for_every_fixed_index','domain_and_comparison_conditions'],
                'Need every member of the arbitrary source family and precise quantifiers')
        M=f'max(0,floor({var}-{var}0))';formula=f'(1+abs({var}))*(1+sum(abs(f_k({var})),k=1..M({var})))'
        return ans('diagonal_domination_by_finite_absolute_prefixes',dict(formula=formula,counter=M,comparison='abs(f_j)/f -> 0 for each fixed j'),
                   'Выбираем растущий целый счётчик. Вспомогательная положительная функция включает конечную сумму модулей всех уже охваченных функций.',
                   'Для каждого фиксированного j он входит в сумму начиная со своего хвоста. Тогда отношение ограничено 1/(1+|x|), которое стремится к нулю.',
                   source_domain=f'{var}>{var}0',requires_continuity=False)
    require(not set(task)-META-common-{'given_family'} and task['approach']==dict(point='+inf',direction='positive_infinity')
            and task['requested_output']==['proof','index_and_growth_comparison_conditions'],'The quantified growth claim is not fully bound')
    d=task['given_family'];family=d['f_n'];n='n';claim=task['claim']
    require(set(d)=={'f_n','index'} and d['index']=='n=1,2,...' and family in (var+'^n','root_n('+var+')'),'Unrecognized finite power family')
    if family==var+'^n' and claim==f'Every f_n({var})={family} grows faster than the preceding f_(n-1)({var}).':
        message='Делим предыдущую степень на следующую. Отношение равно 1/x и стремится к нулю на положительном хвосте.';domain='n>=2 (n=1 also with f_0=1)'
    elif family==var+'^n' and claim==f'exp({var}) grows faster than every f_n({var})={family}, n=1,2,... .':
        message='Логарифм отношения фиксированной степени к экспоненте равен n ln x−x и стремится к −∞.';domain='each fixed positive integer n'
    elif family=='root_n('+var+')' and claim==f'Every f_n({var})={family} grows more slowly than the preceding f_(n-1)({var}).':
        message='В отношении корней показатель равен −1/[n(n−1)]<0 при n≥2. На положительном хвосте отношение стремится к нулю.';domain='n>=2'
    elif family=='root_n('+var+')' and claim==f'ln({var}) grows more slowly than every f_n({var})={family}, n=1,2,... .':
        message='Полагаем t=ln x. Отношение логарифма к каждому фиксированному корню равно t exp(−t/n), предел нулевой.';domain='each fixed positive integer n'
    else:raise Unsupported('The claimed comparison does not match the original function family')
    return ans('quantified_comparison_of_power_and_exponential_scales',dict(proved=True,comparison_ratio_limit=ZERO,indices=domain),message,family=family,original_tail='positive_infinity')


def oscillation_and_continuity(task,kind,library):
    from integrals import affine
    from tasks import source,domain_conditions
    from verify import same_value
    if kind in ('cluster_value_sequence_construction','liminf_limsup','iterated_function_limit'):
        g,given=bound_packet(task,{'expression','parameter_domain','goals','approach','parameter','iteration','goal'})
        if kind=='iterated_function_limit':
            require(g==dict(iteration='sine composed n times',parameter='fixed real x',goal='limit for all fixed x') and not given,'Unknown original iterated map or starting domain')
            return ans('sine_iteration_monotone_absolute_radius',ZERO,
                       'Первая итерация помещает любую исходную точку в [−1,1]. Внутри отрезка модуль синуса строго меньше модуля ненулевого аргумента.',
                       'Модули убывают к неотрицательному пределу, который должен быть неподвижной точкой синуса на [0,1]. Такая точка только ноль.',map='sin',invariant_interval=(q(-1),ONE))
        var='x';x=('v',var);e=m.parse(g['expression'],var);recip=('div',ONE,x)
        if kind=='cluster_value_sequence_construction':
            require(not given and g.get('goals')==['construct a source-domain sequence','prove its convergence and image limit'] and e==('sin',recip),
                    'The original oscillating function does not have the checked reciprocal phase')
            match=re.fullmatch(r'-1<=('+NAME+r')<=1',g['parameter_domain']);require(match is not None,'The source parameter must fill the full sine range')
            a=match[1];term=quotient(ONE,plus(('asin',sym(a)),times(q(2),m.PI,sym('n'))))
            return ans('invert_periodic_phase_to_construct_cluster_sequence',dict(sequence=term,first_index=1,argument_limit=ZERO,image_limit=sym(a)),
                       'Выбираем фазу arcsin α, в которой исходный синус равен α. Прибавляем целое число полных периодов и решаем уравнение для исходного аргумента.',
                       'Знаменатель положителен при n≥1 и растёт без границы. Аргумент стремится к нулю, а образ равен α на каждом индексе.',phase_domain=g['parameter_domain'])
        require(g.get('goals')==['liminf','limsup'],'Both full oscillation bounds are requested')
        near=g['approach']=='x->0,both';far=g['approach']=='book unsigned infinity, both admissible tails';require(near or far,'Unknown source accumulation direction')
        phase=('cos',recip if near else x);sine=('sin',recip if near else x);phase_power=m.power(phase,2)
        if near and not given and e[0]=='add' and same_value(e[1],m.power(sine,2)):
            c=quotient(e[2],('atan',recip));C=m.mul(('abs',c),quotient(m.PI,q(2)))
            require(not m.variable_in(c) and m.constant_defined(c,dict(parameters=[],assumptions=[])),'The one-sided drift is not a fixed arctangent coefficient')
            limits=(m.neg(C),plus(ONE,C));kind0='bounded phase plus different one-sided drift'
        elif near and not given and e[0]=='mul' and phase in e[1:]:
            amplitude=e[2] if e[1]==phase else e[1];require(not domain_conditions(amplitude),'The finite amplitude may have separate singularities')
            proof,A=exact_neighborhood_limit(source(amplitude),var,'0','both',[],[],library);require(isinstance(A,tuple),'The amplitude does not have one finite limit')
            A=m.simplify(('abs',A));limits=(m.neg(A),A);kind0='bounded wave with a finite prefactor'
        elif (near and not given and e[0]=='rpow' and e[1] in (('add',ONE,('pow',phase,2)),plus(ONE,phase_power))
              and e[2] in (('pow',('sec',recip),2),m.power(('sec',recip),2))):
            limits=(q(2),('exp',ONE));kind0='monotone image of positive squared cosine'
        elif far and not given and e==sine:limits=(q(-1),ONE);kind0='unbounded affine phase reaches both sine extremes'
        elif far and not given and e[0]=='mul' and same_value(e[1],m.power(x,2)) and same_value(e[2],phase_power):
            limits=(ZERO,'+inf');kind0='nonnegative unbounded amplitude and exact zeros'
        elif far and not given and e[0]=='rpow' and e[2]==('sin',m.power(x,2)) and m.num(e[1]) is not None and m.num(e[1])>0:
            A=m.num(e[1]);ends=sorted((A,1/A));limits=tuple(map(q,ends));kind0='monotone exponential image of both sine extremes'
        elif far and given==['x>=0'] and e==('div',x,('add',ONE,('mul',m.power(x,2),m.power(sine,2)))):
            limits=(ZERO,'+inf');kind0='rational profile on the only admissible nonnegative tail'
        else:raise Unsupported('No full range and attaining phase witnesses were found')
        detail='Задаём диапазон исходной фазы и берём последовательности её экстремальных значений, сохраняя исходные исключения и знаки направления.'
        if kind0=='monotone image of positive squared cosine':detail+=' Для c=cos² фазы имеем c∈(0,1]. Производная ln(1+c)/c отрицательна, так как ln(1+c)>c/(1+c).'
        return ans('range_and_witnesses_of_oscillating_phase',dict(liminf=m.simplify(limits[0]) if isinstance(limits[0],tuple) else limits[0],
                   limsup=m.simplify(limits[1]) if isinstance(limits[1],tuple) else limits[1]),detail,
                   original=e,phase_profile=kind0,phase_witnesses='theta+2*pi*j on each admissible end or theta tending to an excluded endpoint')
    require(kind in ('piecewise_continuity','discontinuity_classification'),'Not a source continuity obligation')
    var=task['variable'];x=('v',var);rc=m.div(ONE,x);e=None
    if kind=='piecewise_continuity':
        require(not set(task)-META-{'variable','branches','requested_output'} and task.get('requested_output')==['classify continuity'],
                'Only the retained mathematical continuity question is in this proof')
        branch=task['branches'];require(set(branch)=={'except_point','point','point_value'} and branch['point_value']=='arbitrary','The original exceptional value is unbound')
        point=m.parse(branch['point'],None)
        require(m.constant_defined(point,m.context({'variable':var})),'The original assigned point must be a real scalar')
        e=m.parse(branch['except_point'],var)
    else:
        require(not set(task)-META-{'variable','expression','requested_output'} and task.get('requested_output')==[
                'all exceptional points on original real domain and its boundary','classification and one-sided behavior'],'The whole original real domain and both directions must be treated')
        e=m.parse(task['expression'],var,(),('sign',));point=None
    simple_oscillation=e==('sin',rc) or e==m.power(('cos',rc),2)
    if simple_oscillation and point in (None,ZERO):
        return ans('oscillatory_discontinuity_from_distinct_phase_witnesses',dict(exceptional_point=ZERO,kind='oscillatory_second_kind',elsewhere_continuous=True),
                   'На каждой проколотой стороне можно выбрать две последовательности, фиксирующие различные фазы. Их образы постоянны и различны, поэтому любого назначения значения в нуле недостаточно.',
                   original=e,excluded_point=ZERO)
    if e==('div',x,('sin',x)) and point is None:
        return ans('simple_poles_and_removable_zero_on_sine_lattice',dict(removable=dict(point=ZERO,limit=ONE),poles='k*pi for nonzero integer k',
                   pole_leading_coefficient='(-1)^k*k*pi',pole_sides='opposite infinite signs'),
                   'Исходные исключения — целые кратные π. В нуле также обращается в ноль числитель, и основной синусный предел даёт единицу.',
                   'На остальных исключениях знаменатель имеет простой ноль с производной (−1)^k. Ненулевой числитель даёт два противоположных бесконечных следа.',original=e)
    if e[0]=='div' and e[1]==e[2] and e[1]==('cos',m.div(m.PI,x)) and point is None:
        return ans('identity_on_original_domain_keeps_all_removable_holes',dict(removable='0 and 2/(2k+1) for integer k',limit=ONE),
                   'Функция единична в каждой точке исходной области. Не сокращаем ограничения знаменателя и взаимной координаты. На всех их исключениях остаются допустимые приближения и предел единица.',original=e)
    if e==('sign',('sin',m.div(m.PI,x))) and point is None:
        return ans('sign_of_oscillating_function_jumps_at_simple_zeros',dict(jumps='1/k for nonzero integer k',jump_sides='one-sided values ±1 with opposite sign',oscillatory_point=ZERO),
                   'В каждой ненулевой точке нуля внутренней функции производная отлична от нуля, значит исходный знак меняется. У нуля функции знака есть разные предельные фазы на обеих сторонах.',original=e)
    if e[0]=='sqrt' and e[1][0]=='div' and point is None:
        num,den=e[1][1:];C=plus(den,m.power(x,2));c=m.num(C)
        require(c is not None and c>0 and same_value(num,plus(ONE,m.neg(('cos',m.mul(m.PI,x))))),'The original bounded radical has unmatched walls or phase')
        R=m.simplify(('sqrt',C));rr=m.num(R);require(rr is not None and rr.denominator==1,'Exact wall phases are not resolved')
        even=int(rr)%2==0
        return ans('relative_discontinuity_of_radical_with_isolated_outer_points',dict(inner_interval=(m.neg(R),R),outer_points='even integers with absolute value > '+str(rr),
                     boundary_kind='removable' if even else 'unbounded from inside',relative_inner_limits=ZERO if even else '+inf'),
                   'Неотрицательный числитель делает открытый внутренний интервал допустимым. Снаружи отрицательный знаменатель оставляет только отдельные нули числителя.',
                   'На исходных концах выясняем порядок нуля или ненулевой предел числителя и простой ноль знаменателя. Изолированные внешние точки непрерывны относительно своей области.',original=e,wall=R)
    if e[0]=='div' and e[1]==ONE and e[2][0]=='add' and e[2][1]==ONE:
        a=e[2][2]
        if a[0]=='exp' and a[1][0]=='div' and a[1][1]==ONE and m.num(point) is not None:
            require(same_value(a[1][2],plus(x,m.neg(point))),'The bound step has a different singular center')
            return ans('bounded_logistic_jump_from_reciprocal_phase',dict(point=point,left_limit=ONE,right_limit=ZERO,kind='jump'),
                       'Слева и справа взаимный показатель расходится с противоположными знаками. Логистическая формула даёт следы единица и ноль при любом назначенном значении.',original=e)
        if a[0]=='mul' and a[1]==q(-1) and a[2][0]=='exp' and a[2][1][0]=='div' and point is None:
            z=a[2][1];require(z[1]==x and same_value(z[2],plus(ONE,m.neg(x))),'The source exponent has an unproved zero or pole')
            return ans('exponential_denominator_zero_and_reciprocal_phase_jump',dict(pole=dict(point=ZERO,left='+inf',right='-inf'),jump=dict(point=ONE,left=ZERO,right=ONE)),
                       'Знаменатель равен нулю только при нуле показателя. Его простое приращение создаёт полюс. В точке разрыва показателя проверяем два противоположных бесконечных следа, дающих конечный скачок.',original=e)
    raise Unsupported('No proved complete exceptional set and all one-sided traces')



def integer_phase_quotient(task):
    g,given=bound_packet(task,{'expression','point','side','parameters'})
    phases=re.fullmatch(r'sin\(('+NAME+r')\*('+NAME+r')\)/sin\(('+NAME+r')\*\2\)',g['expression'])
    require(phases is not None and len(set(phases.groups()))==3 and not given and g.get('side')=='both',
            'The original quotient needs two integer sine phases at the same two-sided approach')
    a,x,b=phases.groups();point=g['point'];source=task.get('source_statement')
    require(g.get('parameters')=={a:'integer',b:'integer'} and
            source in (None,f"Найти lim_{{{x}->{point}}}{g['expression']}, {a},{b} целые."),
            'The displayed phases, integer parameters, or approach differ')
    center=m.parse(point,None);k=m.num(quotient(center,m.PI))
    require(k is not None and k.denominator==1 and m.constant_defined(center,dict(parameters=[],assumptions=[])),
            'The center is not a defined integer multiple of pi')
    u,w=sym(a),sym(b);d=times(q(k),plus(u,m.neg(w)));ratio=quotient(u,w)
    value=dict(cases=[dict(condition=b+'=0',value=dict(status='no_original_approach'))])
    if k%2==0:value['cases'].append(dict(condition=b+'!=0',value=ratio))
    else:
        value['cases']+=[dict(condition=b+'!=0 and '+a+'-'+b+' '+parity,value=times(q(sign),ratio))
                         for parity,sign in [('even',1),('odd',-1)]]
    return ans('integer_phase_quotient_from_two_first_sine_terms',value,
               'Сдвигаем переменную на kπ. Для целых множителей обе фазы сдвигаются на целые кратные π, что даёт точные множители знака.',
               'При ненулевом множителе делителя его синус имеет простой ноль и ненулев в проколотой окрестности. Отношение первых членов даёт предел, включая нулевой числитель.',
               'Если множитель делителя равен нулю, тот тождественно нулевой на всей исходной области, и точек приближения нет.',
               center=center,phase_parity_exponent=d,original_parameters=g['parameters'])


def cauchy_growth(task,kind):
    g,given=bound_packet(task,{'domain','hypothesis','hypotheses','goal'})
    match=re.fullmatch(r'\(('+NAME+r'),infinity\)',g.get('domain',''))
    require(match is not None and not given,'The whole original right half-line is required')
    a=match[1];bound=f'bounded on each finite({a},b)';root=kind=='cauchy_root_ratio_theorem_proof'
    display=task.get('source_statement')
    if root:
        require(g==dict(domain=match[0],hypotheses=[bound,'f(x)>=C>0'],goal='general root-ratio theorem') and display in (
                None,'При тех же условиях и f(x)>=C>0 доказать lim_{x->+infinity}f(x)^(1/x)=lim_{x->+infinity}f(x+1)/f(x), если правый предел существует.'),
                'The original uniform positive lower bound and ratio claim are required')
    else:
        require(g==dict(domain=match[0],hypothesis=bound,goal='general increment-to-growth theorem') and display in (
                None,f'f определена на({a},infinity), ограничена на каждом конечном({a},b). Доказать lim_{{x->+infinity}}f(x)/x=lim_{{x->+infinity}}(f(x+1)-f(x)), если правый предел существует.'),
                'The original local boundedness and increment claim are required')
    argument=[
        'Фиксируем A правее начала области и представляем x=A+r+j, где j — целое и 0≤r<1. Стартовое значение равномерно ограничено на отрезке [A,A+1].',
        'Раскладываем прирост от A+r до x в телескопическую сумму j единичных приращений. Из определения предела каждое отклоняется от конечного L не больше заданного ε при достаточно большом A.',
        'Делим на x. Старт даёт ноль, j/x стремится к единице. Для бесконечного L заменяем ε произвольной нижней или верхней оценкой единичного приращения.'
    ]
    if root:
        argument.insert(0,'Переходим к ln f. Локальная ограниченность вместе с f≥C>0 ограничивает этот логарифм на опорном отрезке. Приращение логарифма — логарифм исходного отношения.')
        argument.append('Экспоненцируем результат, в том числе при бесконечном пределе. Нулевой предел отношения при f≥C>0 невозможен, поскольку дал бы ln f(x)/x→−∞.')
    return ans('unit_increment_telescoping_on_a_bounded_base_strip',dict(proved=True,mode='root-ratio' if root else 'increment-growth'),
               *argument,domain=match[0],base_strip='[A,A+1]',start_uniform_bound=True,requires_positive_lower_bound=root)


def family_goal(task,library,request):
    require(library.data.get('scalar_family_transitions'),'No admitted source-family limit transitions')
    kind=task.get('kind',task.get('task_type'))
    if kind in ('parameter_integer_power_limit','parameter_finite_scalar_limit','root_index_parameter_limit','integer_parameter_limit'):
        return fixed_integer_local(task,kind,library)
    if kind=='integer_parameter_trigonometric_limit' and library.data.get('tail_obligation_reductions'):
        return integer_phase_quotient(task)
    if kind in ('cauchy_increment_theorem_proof','cauchy_root_ratio_theorem_proof') and library.data.get('tail_obligation_reductions'):
        return cauchy_growth(task,kind)
    if kind=='limit_using_previous_array_theorem':return previous_array_limit(task,library)
    if kind in ('finite_sum_sequence_limit','finite_sum_or_product_sequence_limit'):
        if kind=='finite_sum_or_product_sequence_limit':return geometric_factorial_tails(task,kind,library)
        return finite_lattice_sums(task,kind,library,request)
    if kind=='prove_limit_identity':
        try:return growth_relative_to_elementary_scale(task,kind,library)
        except Unsupported:return extended_nested_limit(task,library)
    if kind=='prove_directed_output_limit':return directed_output_limit(task,library)
    if kind=='integer_phase_sequence_limit':return integer_phase_tail(task,kind,library)
    if kind=='relative_domain_limit':return bounded_radical_oscillation(task)
    if kind in ('floor_function_limit','point_value_and_one_sided_limits'):return floor_limit_or_boundary(task,kind,library)
    if kind=='parameter_domain_radical_limit':return relative_radical_at_parameter(task,library)
    if kind=='difference_of_directional_limits':return directional_difference(task,library)
    if kind in ('prove_sequence_identity','prove_exponential_series_limit','factorial_phase_limit'):
        return geometric_factorial_tails(task,kind,library)
    if kind in ('finite_product_integer_parameter_limit','finite_product_root_limit','variable_degree_root_product_limit','integer_power_two_tail_limit'):
        return fixed_bound_product(task,kind)
    if kind in ('error_tolerance_interval','propagate_measurement_error','maximal_error_neighborhood','epsilon_delta_proof_table',
                'maximal_delta_and_uniformity','quantifier_negation','geometric_epsilon_delta'):
        return local_error_and_quantifiers(task,kind)
    if kind in ('recursive_sequence_limit','function_recurrence_limit','stable_recurrence_limit_theorem'):
        return recurrence_limit(task,kind)
    if kind=='prove_no_power_order':return growth_relative_to_elementary_scale(task,kind,library)
    if kind in ('prove_growth_comparison_family','construct_and_prove_dominating_function'):return quantified_growth_family(task,kind)
    if kind in ('liminf_limsup','cluster_value_sequence_construction','iterated_function_limit'):
        return oscillation_and_continuity(task,kind,library)
    raise Unsupported('No complete mathematical transition for the source family')
