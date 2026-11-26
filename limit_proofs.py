"""Analytic germ calculations and explicit source limit obligations."""
from fractions import Fraction as F
from functools import lru_cache
import re

import expressions as m
import operations as op
import polynomial as poly
from model import ONE, ZERO, Unsupported, freeze, q


class EmptyGerm(Unsupported):
    """The original expression is undefined throughout the selected neighborhood."""


def elementary_jet(raw,ctx):
    """Compose the existing elementary jet rules on one positive local coordinate."""
    def inverse(j):
        if op.near_sign(j,ctx)==0 and op.unpack(j)[1] is None:
            raise EmptyGerm('An original denominator is identically zero')
        return op.jpower(j,F(-1),ctx)

    @lru_cache(maxsize=None)
    def visit(e):
        tag=e[0]
        if not m.variable_in(e):
            if not m.constant_defined(e,ctx):
                raise Unsupported('A fixed expression is not defined under the given conditions')
            return op.jc(m.simplify(e),ctx)
        if e==('v',ctx['variable']):
            return op.jet({1:ONE},order=ctx['order'])
        if tag=='ln' and e[1][0]=='exp':
            # The exponential is positive wherever its original argument is real.
            return visit(e[1][1])
        a=visit(e[1]);previous=op.unpack(a)
        if tag=='add':return op.jadd(a,visit(e[2]),ctx)
        if tag=='mul':return op.jmul(a,visit(e[2]),ctx)
        if tag=='div':return op.jmul(a,inverse(visit(e[2])),ctx)
        if tag=='pow':
            if e[2]<=0:inverse(a)
            return op.jpower(a,F(e[2]),ctx)
        if tag=='rpow':
            if op.near_sign(a,ctx)!=1:
                raise Unsupported('A real-power base has not been shown positive')
            power=m.num(m.simplify(e[2])) if m.constant_defined(e[2],ctx) else None
            if power is not None and op.leading(a)[0]!=0:return op.jpower(a,power,ctx)
            b=op.jmul(op.analytic(a,'ln',ctx),visit(e[2]),ctx)
            return op.analytic(b,'exp',ctx)
        if tag in ('sqrt','cbrt'):
            if not previous[0] and previous[1] is None:return op.jc(ZERO,ctx)
            if tag=='sqrt' and op.near_sign(a,ctx)==-1:
                raise EmptyGerm('The square-root argument is negative throughout the original side')
            return op.jpower(a,F(1,2 if tag=='sqrt' else 3),ctx)
        if tag=='abs':
            sign=op.near_sign(a,ctx)
            if sign not in (-1,0,1):raise Unsupported('The absolute-value branch is unresolved')
            return op.jscale(a,q(sign),ctx)
        if tag in ('tan','cot','tanh'):
            sn,cs=('sinh','cosh') if tag=='tanh' else ('sin','cos')
            if tag=='cot':sn,cs=cs,sn
            return op.jmul(op.analytic(a,sn,ctx),inverse(op.analytic(a,cs,ctx)),ctx)
        if tag in ('asin','acos'):
            if op.jet_limit(a,ctx) in ('+inf','-inf'):
                raise EmptyGerm('The inverse-trigonometric argument is unbounded on the original side')
            center=op.finite_center(a)
            if center in (ONE,q(-1)):
                sign=m.num(center)
                delta=op.jscale(op.jadd(op.jc(ONE,ctx),op.jscale(a,q(-sign),ctx),ctx),q(1,2),ctx)
                if op.near_sign(delta,ctx)==-1:
                    raise EmptyGerm('The inverse-trigonometric argument leaves its original real domain')
                radical=op.jc(ZERO,ctx) if op.near_sign(delta,ctx)==0 else op.jpower(delta,F(1,2),ctx)
                asin=op.jscale(op.jadd(op.jc(m.div(m.PI,q(2)),ctx),
                         op.jscale(op.analytic(radical,'asin',ctx),q(-2),ctx),ctx),q(sign),ctx)
            else:
                tested=m.sign(m.add(ONE,m.neg(m.power(center,2))),ctx)
                if tested==-1:raise EmptyGerm('The inverse-trigonometric argument stays outside the real interval')
                asin=op.analytic(a,'asin',ctx)
            return asin if tag=='asin' else op.jadd(op.jc(m.div(m.PI,q(2)),ctx),op.jscale(asin,q(-1),ctx),ctx)
        if tag=='exp' and op.jet_limit(a,ctx)=='-inf':
            # A negative-power phase bounds exp(a) by exp(-c/t^d) eventually.
            return op.jet({},F(ctx['order']),ctx['order'])
        if tag=='atan':
            value=op.jet_limit(a,ctx)
            if value in ('-inf','+inf'):
                endpoint=m.mul(q(1,2) if value=='+inf' else q(-1,2),m.PI)
                return op.jadd(op.jc(endpoint,ctx),op.jscale(op.analytic(inverse(a),'atan',ctx),q(-1),ctx),ctx)
        if tag in ('sin','cos','sinh','cosh','exp','ln','asin','atan'):
            return op.analytic(a,tag,ctx)
        raise Unsupported('No admitted elementary germ for '+tag)
    return visit(raw)


def germ_limit(task,library,*,orders=(2,4,6,8,12),split=True):
    """Find one common component-wise limit or an exhaustive real parameter split."""
    from verify import same_side_answer, different_value

    def side_result(target,side,assumptions):
        ctx,_=m.limit_directions(target,assumptions,library.data.get('magnitude_infinity_contract'))
        e,transport=m.normalized(target,ctx,side)
        for order in orders:
            current={**ctx,'order':order}
            try:
                jet=elementary_jet(e,current);value=op.jet_limit(jet,current)
                if isinstance(value,tuple) and not m.constant_defined(value,current):
                    raise Unsupported('The resulting finite coefficient is not real on the case domain')
            except EmptyGerm:
                return dict(side=side,transport=transport,case='no_original_approach',order=order)
            except (Unsupported,op.Unavailable,op.ResourceBound,TypeError,ZeroDivisionError):
                continue
            return dict(side=side,transport=transport,order=order,jet=jet,ctx=current,value=value)
        raise Unsupported('No sufficiently precise elementary germ has all its real domain conditions')

    def on_cases(assumptions):
        ctx,targets=m.limit_directions(task,assumptions,library.data.get('magnitude_infinity_contract'))
        rows=[side_result(t,s,assumptions) for t,s in targets]
        admitted=[r for r in rows if 'value' in r]
        if not admitted:return rows,dict(status='no_original_approach')
        if len(admitted)<len(rows) and task['approach'].get('mode')!='magnitude_infinity':
            raise Unsupported('The requested finite sides do not have the same source domain')
        first=admitted[0]['value']
        if all(same_side_answer(first,r['value'],r['ctx']) for r in admitted):
            return rows,first
        if len(admitted)==2 and different_value(first,admitted[1]['value'],ctx):
            return rows,dict(status='does_not_exist',one_sided_values=[r['value'] for r in admitted])
        raise Unsupported('The original directions have no common verified comparison')

    try:
        rows,value=on_cases([])
    except Unsupported as failure:
        if not split:raise
        for parameter in task.get('parameters',[]):
            cases=[]
            try:
                for relation in ('zero','nonzero'):
                    hypothesis=dict(symbol=parameter,relation=relation)
                    rows,value=on_cases([hypothesis])
                    cases.append(dict(hypothesis=hypothesis,sides=rows,value=value))
            except Unsupported:
                continue
            return dict(theorem='method.finite_analytic_germ',cases=cases),dict(cases=[
                dict(condition=c['hypothesis'],value=c['value']) for c in cases])
        raise failure
    return dict(theorem='method.finite_analytic_germ',sides=rows),value


def analytic_priority(task):
    """Prefer the direct series composition when the source exposes a simple normalized scale."""
    var=('v',task['variable'])
    e=m.parse(task['expression'],var[1],task.get('parameters',[]))
    if e[0]=='atan':return True
    if e[0]=='rpow' and e[1][0]=='div' and e[1][2]==var:
        return e[1][1][0] in ('sin','tan','asin','atan','ln')
    return task['approach'].get('mode')=='magnitude_infinity' and any(z[0]=='cbrt' for _,z in op.expression_positions(e))


def necessary_fixed_domain(raw,var,params,source):
    from tasks import domain_conditions,guard_source,known_guard
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=source))
    fixed=tuple(g for g in domain_conditions(raw) if not m.variable_in(g[1]))
    strict={g[1] for g in fixed if g[0]=='positive'}|({g[1] for g in fixed if g[0]=='nonnegative'} &
                                                       {g[1] for g in fixed if g[0]=='nonzero'})
    residual=tuple(dict.fromkeys([('positive',e) for e in sorted(strict,key=repr)]+
                                  [g for g in fixed if g[1] not in strict]))
    if any(g[0]=='nonnegative' for g in residual if not known_guard(g,ctx)):
        raise Unsupported('The source includes a parameter boundary requiring a further split')
    return fixed,list(dict.fromkeys(guard_source(g) for g in residual if not known_guard(g,ctx)))


def germ_with_fixed_domain(task,library):
    """Extract necessary fixed restrictions from the raw expression and prove the remaining local limit."""
    var=task['variable'];params=task.get('parameters',[]);source=task.get('stated_conditions',[])
    if task['approach']['point'] in ('infinity','-inf','+inf'):
        raise Unsupported('This transition requires a local endpoint')
    raw=m.parse(task['expression'],var,params)
    if not params and raw[0] not in ('div','rpow','add','mul'):
        raise Unsupported('There is no composed local expression')
    fixed,assumptions=necessary_fixed_domain(raw,var,params,source)
    if source and not assumptions:
        raise Unsupported('The routine child proof already carries these explicit source conditions')
    target=dict(task,stated_conditions=[*source,*assumptions])
    try:checked,value=germ_limit(target,library,orders=(2,4,6,8))
    except Unsupported:
        ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=target['stated_conditions']))
        names=[p for p in params if m.sign(('s',p),ctx) is None]
        if len(names)!=1:raise
        p=names[0];rows=[]
        for relation in ('<0','=0','>0'):
            condition=p+relation
            case=dict(target,stated_conditions=[*target['stated_conditions'],condition])
            proof,conclusion=germ_limit(case,library,orders=(2,4,6,8),split=False)
            rows.append(dict(condition=condition,analytic_proof=proof,value=conclusion))
        checked=dict(exhaustive_sign_cases=rows)
        value=dict(cases=[dict(condition=r['condition'],value=r['value']) for r in rows])
    if assumptions:value=dict(required_original_parameters=assumptions,value=value,otherwise='no_original_approach')
    return dict(theorem='method.local_germ_after_proving_fixed_source_domain',original=raw,raw_fixed_guards=fixed,
                required_on_original_domain=assumptions,analytic_proof=checked,
                argument=['Находим все ограничения действительных операций в исходной формуле.',
                          'Условие, которое зависит лишь от фиксированных параметров, обязательно при любом приближении. Из совместных неотрицательности и ненулевости выводим строгую положительность.',
                          'Строим локальные доказательства при этих условиях и проверяем каждую исходную сторону.']),value


def square_coordinate_limit(task,library):
    """Compose square-root germs in their common positive coordinate and keep parameter guards."""
    from tasks import domain_conditions,known_guard,source
    var=task['variable'];x=('v',var);params=task.get('parameters',[])
    condition=task.get('stated_conditions',[])
    if task['approach']['point']!='0' or task['approach']['side'] not in ('both','right') or 'sqrt' not in task['expression']:
        raise Unsupported('No right square-root neighborhood at the original point')
    raw=m.parse(task['expression'],var,params)
    if ('nonnegative',x) not in domain_conditions(raw):
        raise Unsupported('The original formula does not itself require a nonnegative variable')
    fixed,guards=necessary_fixed_domain(raw,var,params,condition);contexts=[*condition,*guards]
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=contexts))
    asymptotic='localRoot'
    while asymptotic in [var,*params]:asymptotic+='_'
    t=('v',asymptotic);replacement={('sqrt',x):t}
    for _,e in op.expression_positions(raw):
        if (e[0]!='sqrt' or e[1][0]!='div' or e[1][1]!=x or m.variable_in(e[1][2])):continue
        scale=e[1][2]
        if not known_guard(('positive',scale),ctx):raise Unsupported('The fixed scale of the root has not been shown positive')
        replacement[e]=('div',t,('sqrt',scale))
    if len(replacement)==1:raise Unsupported('No other scaled root shares the proved coordinate')
    reduced=m.substitute(raw,{**replacement,x:('pow',t,2)})
    mapping=dict(kind='limit',variable=asymptotic,parameters=params,expression=source(reduced),
                 stated_conditions=contexts,approach=dict(point='0',side='right'))
    checked,value=germ_limit(mapping,library,orders=(2,4,6,8))
    if guards:value=dict(required_original_parameters=guards,value=value,otherwise='no_original_approach')
    return dict(theorem='method.common_square_root_coordinate_in_local_germs',original=raw,
                raw_fixed_guards=fixed,derived_parameter_guards=guards,exact_square_root_replacements=tuple(replacement.items()),
                verified_reduction=checked,argument=['Из исходной области получаем x≥0 и выводим необходимые ограничения фиксированных делителей.',
                    'Вводим t=√x и переносим каждый исходный корень через его доказанный положительный масштаб.',
                    'В новой положительной координате находим конечные члены и проверяем полученный предел. Слева от нуля исходный корень запрещает приближение.']),value


def logarithms_of_vanishing_sine_phases(task,library):
    """Bind the sign of each phase before comparing its singular logarithm."""
    from integrals import affine
    from tasks import domain_conditions,source
    var=task['variable'];x=('v',var);params=task.get('parameters',[]);side=task['approach'].get('side')
    if task['approach']['point']!='0' or side not in ('both','left','right'):
        raise Unsupported('No directed neighborhood for a pair of vanishing sine phases')
    raw=m.parse(task['expression'],var,params)
    if raw[0]!='div' or any(z[0]!='ln' or z[1][0]!='sin' for z in raw[1:]):
        raise Unsupported('No quotient of two logarithms of sine phases')
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=task.get('stated_conditions',[])))
    rows=[]
    for atom in raw[1:]:
        if domain_conditions(atom[1][1]):raise Unsupported('The original phase has a separate exceptional domain')
        k,b=affine(atom[1][1],var)
        if b!=ZERO or not m.constant_defined(k,ctx) or k[0] not in ('q','s'):
            raise Unsupported('Only fixed linear sine phases with zero center are matched here')
        rows.append(k)
    cases=[]
    for direction,relation in (('right','>0'),('left','<0')):
        if side not in ('both',direction):continue
        signs=[m.sign(c,ctx) for c in rows]
        required=1 if direction=='right' else -1
        if any(s is not None and s!=required for s in signs):continue
        conditions=tuple(dict.fromkeys(source(c)+relation for c,s in zip(rows,signs) if s is None))
        cases.append(dict(conditions=conditions,admissible_side=direction,value=ONE))
    value=(dict(status='no_original_approach') if not cases else ONE if len(cases)==1 and not cases[0]['conditions']
           else dict(cases=cases,otherwise='no_original_approach'))
    return dict(theorem='method.leading_logarithm_on_shared_vanishing_sine_domain',original=raw,linear_coefficients=rows,
                domain_cases=cases,argument=['На выбранной проколотой стороне синус линейной фазы имеет знак её первого члена.',
                    'Сохраняем именно тот случай параметров, где оба исходных логарифма определены. Нулевой множитель тоже проверяется.',
                    'Выносим из каждого аргумента |x|. Остаются два положительных конечных множителя, а общий неограниченный логарифм даёт отношение 1.']),value


def logarithmic_divided_difference_of_roots(task,library):
    """Find the common logarithmic coordinate before comparing two fixed roots."""
    from scalar_families import subexpression
    from tasks import source
    text=task['expression'];names=task.get('parameters',[])
    if 'root_' not in text or not text.startswith('ln(') or task['approach']['point'] in ('+inf','-inf','infinity'):
        raise Unsupported('No local logarithm over a root difference')
    argument,end=subexpression(text,2);rest=text[end:]
    a=re.fullmatch(r'/\(root_([A-Za-z_]\w*)\('+re.escape(argument)+r'\)-root_([A-Za-z_]\w*)\('+re.escape(argument)+r'\)\)',rest)
    if not a or not set(a.groups())<=set(names):
        raise Unsupported('The numerator and both fixed root arguments differ')
    left,right=a.groups()
    if left==right:
        raise Unsupported('Equal root indices require an explicit proof of the empty domain')
    var=task['variable'];base=m.parse(argument,var,names)
    child=dict(task,expression=source(('add',base,q(-1))))
    for order in (2,4,6,8):
        try:checked,value=germ_limit(child,library,orders=(order,),split=False)
        except Unsupported:continue
        rows=[r for r in checked['sides'] if 'jet' in r]
        if value==ZERO and rows and all(op.unpack(r['jet'])[0] and m.nonzero(op.leading(r['jet'])[1],r['ctx']) for r in rows):break
    else:raise Unsupported('The common base must approach one through nonunit positive values')
    a,b=('s',left),('s',right)
    value=m.div(ONE,m.add(m.div(ONE,a),m.neg(m.div(ONE,b))))
    guards=[left+'!=0',right+'!=0',left+'!='+right]
    return dict(theorem='method.checked_logarithmic_coordinate_for_root_differences',
                common_base=base,original_positive_nonunit_base=checked,derived_index_guards=guards,
                argument=['Доказываем, что общий аргумент стремится к единице через отличные от единицы положительные значения.',
                          'Вводим его логарифм t. Разность корней становится exp(t/m)−exp(t/n), её первый коэффициент равен 1/m−1/n.',
                          'Нулевой индекс не задаёт исходного корня. При равных индексах делитель тождественно нулевой. В оставшейся области коэффициент ненулевой.']),dict(
                required_original_parameters=guards,value=value,otherwise='no_original_approach')


def exponential_over_high_power(task):
    """Compare a reciprocal exponential with an arbitrary fixed integer power of the same local scale."""
    if task.get('parameters') or task.get('stated_conditions') or task['approach']['point']!='0':
        raise Unsupported('A single unvarying real scale at zero is required')
    var=re.escape(task['variable']);text=task['expression'].replace(' ','')
    profile=re.fullmatch(r'exp\(-(\d+)/'+var+r'\^(\d+)\)/'+var+r'\^(\d+)',text)
    if profile is None:raise Unsupported('No reciprocal exponential and integer-power pair on the source scale')
    c,p,n=map(int,profile.groups());side=task['approach'].get('side')
    if c<=0 or p<=0 or side not in ('left','right','both'):
        raise Unsupported('The reciprocal scale or approach has not been bound')
    left=ZERO if p%2==0 else '+inf' if n%2==0 else '-inf'
    value=ZERO if side=='right' or left==ZERO else left if side=='left' else dict(status='does_not_exist',one_sided_values=[ZERO,left])
    return dict(theorem='method.reciprocal_exponential_dominates_fixed_power',
                coefficient=q(c),reciprocal_order=p,denominator_power=n,source_variable=task['variable'],
                original_two_sided_guard=task['variable']+'!=0',approach=task['approach'],
                argument=['Берём логарифм модуля исходного отношения. Степенной член в показателе растёт по модулю быстрее логарифма знаменателя.',
                          'Устанавливаем знак ведущего члена отдельно на каждой запрошенной стороне. Восстанавливаем знак исходной дроби по паритету целой степени.']),value


def logarithmically_controlled_power(task,library):
    """Use a bound on the logarithm of the base when the precise real-power germ is unnecessary."""
    if task.get('parameters') or '^' not in task['expression']:
        raise Unsupported('A parameter-free power is required for this logarithmic comparison')
    _,targets=m.limit_directions(task,[],library.data.get('magnitude_infinity_contract'))
    rows=[]
    for target,side in targets:
        ctx,_=m.limit_directions(target,[],library.data.get('magnitude_infinity_contract'))
        ctx['order']=6
        raw,transport=m.normalized(target,ctx,side)
        body=raw;offset=ZERO
        if raw[0]=='add' and raw[1][0]=='rpow' and m.constant_defined(raw[2],ctx) and m.num(m.simplify(raw[2])) is not None:
            body,offset=raw[1],m.simplify(raw[2])
        if body[0]!='rpow':raise Unsupported('The original expression is not a power plus a fixed offset')

        def leading(expr):
            jet=elementary_jet(expr,ctx);terms,tail=op.unpack(jet)
            if not terms:
                if tail is None:return 0,ZERO
                raise Unsupported('No resolved leading order for the local scale')
            power,coef=op.leading(jet)
            if m.sign(coef,ctx) not in (-1,1):raise Unsupported('The sign of the leading coefficient is unknown')
            return power,coef

        def log_bound(base):
            if base[0]=='ln':
                order,c=leading(base[1])
                if m.sign(c,ctx)!=1 or order>0:raise EmptyGerm('The logarithmic base stays nonpositive')
                if order<0:return 1,dict(positive_logarithmic_base=True,inner_order=q(order),inner_coefficient=c)
            order,c=leading(base)
            if m.sign(c,ctx)!=1:raise EmptyGerm('The original real-power base stays nonpositive')
            return (order<0)-(order>0),dict(base_order=q(order),base_coefficient=c)

        def behavior(exponent):
            inner=exponent;subtract_one=(exponent[0]=='add' and m.constant_defined(exponent[2],ctx)
                                        and m.simplify(exponent[2])==q(-1))
            if subtract_one:inner=exponent[1]
            if inner[0]=='rpow':
                _,bound=log_bound(inner[1]);inner_order,detail=behavior(inner[2])
                if inner_order=='small':
                    return ('small' if subtract_one else 1),dict(inner_base_bound=bound,inner_exponent=detail,
                        bound_on_increment='|exp(z)-1| <= 2|z| for sufficiently small z')
            order,c=leading(exponent)
            if order>0 or c==ZERO:return 'small',dict(exponent_order=q(order),exponent_coefficient=c)
            if order==0:return m.sign(c,ctx),dict(finite_exponent=c)
            raise Unsupported('The originally divergent exponent needs a different comparison')

        try:
            diverges,base=log_bound(body[1]);exponent,scale=behavior(body[2])
            if exponent=='small':value=m.add(ONE,offset);characteristic=ZERO
            elif diverges:
                grows=exponent*diverges>0
                value='+inf' if grows else offset;characteristic='+inf' if grows else '-inf'
            else:raise Unsupported('The bound does not determine the logarithmic characteristic')
        except EmptyGerm:
            rows.append(dict(side=side,original_domain='no_original_approach',transport=transport))
        else:rows.append(dict(side=side,original_base=base,exponent_scale=scale,characteristic=characteristic,
                              value=value,transport=transport))
    values=[r['value'] for r in rows if 'value' in r]
    value=(dict(status='no_original_approach') if not values else values[0] if len(set(values))==1
           else dict(status='does_not_exist',one_sided_values=values))
    return dict(theorem='method.power_limit_from_bounded_logarithmic_growth',sides=rows,
                argument=['На каждой допустимой стороне строим положительную малую координату и доказываем знак исходного основания.',
                          'Если основание эквивалентно положительному степенному члену, его логарифм имеет не более чем логарифмический рост. Для логарифмического основания используем ln u≤u при u≥1.',
                          'Проверяем, убывает ли показатель степенным порядком, допускающим конечную степень логарифма. При необходимости сначала ограничиваем вложенную степень через |exp(z)−1|.',
                          'Перемножаем оценки, либо используем доказанный ненулевой предел показателя и бесконечный знак логарифма. Возвращаемся к исходной степени.']),value


def elementary_taylor_limit(task,library):
    from tasks import domain_conditions,source
    permitted={'kind','id','source','expression','variable','approach','parameters','parameter_conditions','method_requirement'}
    origin=task.get('source',{})
    heading='Используя разложения I—V, найти следующие пределы'
    if (not library.data.get('atom_local_limit_proofs') or set(task)-permitted or
            task.get('method_requirement')!='use_elementary_taylor_expansions_I_V' or
            not isinstance(origin,dict) or set(origin)-{'exercise','printed_subpart','pdf_sha256','pdf_page','printed_page','method_heading','expansions_page'} or
            origin.get('method_heading',heading)!=heading):
        raise Unsupported('The source-required elementary expansions are not bound')
    raw=m.parse(task['expression'],task['variable'],task.get('parameters',[]))
    allowed={'q','v','s','pi','add','mul','div','pow','rpow','sqrt','cbrt','sin','cos','ln','exp'}
    if any(e[0] not in allowed for _,e in op.expression_positions(raw)):
        raise Unsupported('This original formula needs an expansion outside the admitted list')
    extracted=()
    try:proof,value=germ_limit(task,library,orders=(2,4,6,8))
    except Unsupported:
        if task['approach']!={'point':'+inf','side':'positive_infinity'} or task.get('parameters') or task.get('parameter_conditions'):
            raise
        x=('v',task['variable']);internal='reciprocalScale'
        if internal==x[1]:internal+='_'
        t=('v',internal);changes={}
        for _,node in op.expression_positions(raw):
            if node[0]=='sqrt':exponent=F(1,2)
            elif node[0]=='rpow' and m.constant_defined(node[2],dict(parameters=[],assumptions=[])):
                exponent=m.num(m.simplify(node[2]))
            else:continue
            if exponent is None or domain_conditions(node[1]):continue
            numerator,denominator=m.rational_form(node[1])
            if denominator!={():1} or any(mon and (len(mon)!=1 or mon[0][0]!=x or mon[0][1]<0) for mon in numerator):continue
            coefficients={mon[0][1] if mon else 0:c for mon,c in numerator.items()}
            degree=max(coefficients,default=0)
            if degree==0 or coefficients[degree]<=0:continue
            core=m.poly_expr({((t,degree-j),) if j!=degree else ():c for j,c in coefficients.items()})
            changes[node]=('mul',('rpow',t,q(-exponent*degree)),('rpow',core,q(exponent)))
        if not changes:raise
        extracted=tuple(changes.items());reduced=m.substitute(raw,{**changes,x:('div',ONE,t)})
        proof,value=germ_limit(dict(kind='limit',variable=internal,expression=source(reduced),approach=dict(point='0',side='right')),
                               library,orders=(2,4,6,8))
    return dict(theorem='method.elementary_taylor_list_after_coordinate_transport',
                original=raw,original_guards=domain_conditions(raw),permitted_expansions=tuple(sorted(allowed)),
                exact_extracted_scales=extracted,
                singular_series_proofs=proof,argument=['Переносим каждую допустимую сторону в положительное локальное приращение.',
                    'Собираем ведущие члены из указанных элементарных разложений. Для степеней и корней используем биномиальное разложение после выделения ведущего множителя.',
                    'Проверяем исходные ограничения и отдельно сравниваем результаты каждой запрошенной стороны.']),value


def sine_powers_at_integer_phase(task,library):
    """Cancel a shared positive-base germ before expanding fixed real powers."""
    from tasks import source
    variable=task['variable'];parameters=task.get('parameters',[])
    raw=m.parse(task['expression'],variable,parameters)
    if raw[0]!='div':raise Unsupported('A comparison of two sine phases is required')
    def decompose(e):
        if e[0]!='sin' or e[1][0]!='mul' or m.PI not in e[1][1:]:
            raise Unsupported('Each sine phase must approach the same integer multiple of π')
        power=e[1][2] if e[1][1]==m.PI else e[1][1]
        if power[0] not in ('rpow','pow'):
            raise Unsupported('A fixed real exponent of the common base is required')
        return power[1],power[2] if power[0]=='rpow' else q(power[2])
    (base,a),(check,b)=map(decompose,raw[1:])
    if base!=check or any(m.variable_in(v) for v in (a,b)):
        raise Unsupported('The two inner germs differ or the exponent varies with the approach')
    difference=dict(task,expression=source(('add',base,q(-1))))
    germ,_=germ_limit(difference,library,orders=(2,4,6),split=False)
    rows=germ.get('sides',[])
    if not rows or any(r.get('value')!=ZERO or
            not m.nonzero(op.leading(r['jet'])[1],r['ctx']) for r in rows):
        raise Unsupported('The common base must approach one through nonunit values')
    ctx=rows[0]['ctx']
    if not all(m.constant_defined(v,ctx) for v in (a,b)):
        raise Unsupported('The exponents are not fixed, defined real parameters')
    plan=dict(theorem='method.sine_power_common_increment',original=raw,base_increment=germ,
              exponents=(a,b),original_base_positive=True)
    if m.nonzero(b,ctx):
        return plan,m.div(a,b)
    if b==ZERO:
        return plan,dict(status='no_original_approach')
    if b[0]!='s' or b[1] not in parameters:
        raise Unsupported('The degenerate denominator branch cannot be expressed')
    cases=[dict(hypothesis=dict(symbol=b[1],relation='zero'),value=dict(status='no_original_approach')),
           dict(hypothesis=dict(symbol=b[1],relation='nonzero'),value=m.div(a,b))]
    return dict(plan,cases=cases),dict(cases=[dict(condition=c['hypothesis'],value=c['value']) for c in cases])


def logarithmic_monomial_tail(task):
    """Compare powers of x, ln x and ln ln x after transporting a positive expression through log."""
    if task['approach']['point']!='+inf' or task.get('parameters') or task.get('stated_conditions'):
        raise Unsupported('The strict positive logarithmic scale needs a parameter-free positive tail')
    x=('v',task['variable']);log=('ln',x);loglog=('ln',log);scales=(x,log,loglog)
    raw=m.parse(task['expression'],task['variable'])

    def positive_log(e):
        if e in scales:return ('ln',e)
        if m.num(e) is not None and m.num(e)>0:return m.simplify(('ln',e))
        if e[0]=='rpow':
            if any(z[0] not in ('q','v','pow','mul','add','ln') or z[0]=='ln' and z not in scales[1:]
                   for _,z in op.expression_positions(e[2])):
                raise Unsupported('The exponent contains an unproved positive-tail expression')
            return ('mul',e[2],positive_log(e[1]))
        if e[0]=='pow':return ('mul',q(e[2]),positive_log(e[1]))
        if e[0] in ('mul','div'):
            first,second=map(positive_log,e[1:])
            return ('add',first,second if e[0]=='mul' else ('mul',q(-1),second))
        raise Unsupported('An original positive base has not been proved on the tail')

    phase=positive_log(raw);n,d=m.rational_form(phase)
    def leading(p):
        frequencies={}
        for mon,c in p.items():
            if any(z not in scales for z,_ in mon):raise Unsupported('No comparable logarithmic monomial')
            powers=tuple(dict(mon).get(z,0) for z in scales)
            frequencies[powers]=frequencies.get(powers,0)+c
        keys=[k for k in frequencies if frequencies[k]]
        if not keys:raise Unsupported('The phase leading order vanishes')
        rate=max(keys)
        return rate,frequencies[rate]
    pn,cn=leading(n);pd,cd=leading(d)
    if pn<=pd:
        raise Unsupported('No divergent logarithmic phase on the original tail')
    return dict(theorem='method.logarithmic_monomial_phase',raw=raw,logarithmic_phase=phase,
        rate=tuple(a-b for a,b in zip(pn,pd)),coefficient=q(cn/cd),
        positivity='x, ln(x), and ln(ln(x)) are positive for x>e'), ZERO if cn*cd<0 else '+inf'


def power_domain_notes(task):
    conditions=task.get('derived_original_domain_conditions',[])+task.get('derived_domain_conditions',[])
    if len(conditions)!=1 or task.get('transcription_notes') or not conditions[0].endswith('!=0'):
        return ()
    goal=task['goal'];v=goal['variable'];params=goal.get('parameters',[])
    try:
        term=m.parse(conditions[0][:-3],v,params)
    except Unsupported:
        return ()
    return () if m.variable_in(term,v) else (term,)


def source_reader_notes(task):
    """Only admit notes whose mathematical content will be checked by the rebuilt branching proof."""
    derived=task.get('derived_original_domain_conditions',[])
    notes=task.get('transcription_notes',[])
    if not derived:
        goal=task['goal'];a=goal['approach']
        return (not task.get('derived_domain_conditions') and
            notes==['Independently visually checked: the source does not print1-0 in this subpart.']
            and a.get('point')=='0' and a.get('side')=='right')
    if len(derived)!=1 or task.get('derived_domain_conditions'):
        return False
    matched=re.fullmatch(r'([A-Za-z_]\w*)!=0',derived[0])
    if not matched or matched[1] not in task['goal'].get('parameters',[]):
        return False
    p=matched[1]
    return notes==[f'{p}=0 makes the original sine denominator identically0; negative/zero alpha is otherwise permitted.']


def derived_notes_hold(task,plan):
    required=task.get('derived_original_domain_conditions',[])
    if plan.get('theorem')=='method.power_divided_differences':
        if not required and not task.get('derived_domain_conditions'):return True
        from verify import same_value
        terms=power_domain_notes(task)
        implication=plan.get('nonzero_on_defined_branch')
        return bool(terms and implication and same_value(terms[0],implication))
    if task.get('derived_domain_conditions'):return False
    if not required:return True
    zero,nonzero=plan.get('cases',(None,None))
    return (zero is not None and zero['hypothesis']['symbol']+'!=0'==required[0]
            and zero['value']=={'status':'no_original_approach'}
            and isinstance(nonzero['value'],tuple))


KINDS={
    'general_polynomial_growth_proof','general_rational_degree_proof','possible_rational_limit_values',
    'general_polynomial_root_proof','parametric_right_limit','quadratic_root_asymptotic_analysis',
    'asymptotic_coefficient_identification','two_direction_asymptotic_coefficient_identification',
    'asymptote_criterion_proof','integer_parameter_point_and_sides','composition_limit_counterexample',
    'growth_theorem_source_review','polynomial_increment_growth_theorem','uniform_array_equivalence_sum_theorem',
    'reciprocal_newton_iteration_proof','square_root_newton_iteration_proof','kepler_fixed_point_existence_uniqueness',
    'all_infinite_directions_taylor_limit','geometric_limit_from_tangent_angle','prove_limit_under_geometric_bound',
    'prove_second_derivative_symmetric_difference_formula','classify_differentiability_at_point','find_curve_asymptote',
    'circular_segment_asymptotic','quantified_taylor_remainder','limit_under_asymptotic_hypothesis',
    'derivative_uniform_bound','uniform_approximation_error','approximation_validity_interval',
    'prove_taylor_remainder_inequality','fit_asymptotic_coefficients',
    'fit_asymptotic_coefficients_and_apply_to_geometry','geometric_asymptotic_error','lhopital_applicability',
}
META={'kind','task_type','id','source','source_number','source_exercise_number','source_subpart','source_edition',
    'source_pdf_page','source_pdf_pages','transcription_notes','program_status','main_pass_status',
    'deferred_reason','pending_obligations','original_obligations'}


def routing(task,kind):
    if kind in KINDS:return True
    from scalar_families import family_route
    if family_route(task,kind):return True
    if kind=='finite_expansion':
        return task.get('degree')=='n' or task.get('requested_output') in (
            ['finite_power_expansion','global_polynomial_identity'],['finite_power_expansion','fourth_derivative_at_zero'])
    if kind=='mathematical_question':
        return isinstance(task.get('goal'),dict) and task['goal'].get('goals')==['all asymptotes with correct directions']
    return (kind in (None,'limit') and isinstance(task.get('expression'),str)
            and 'tan(' in task['expression'] and 'sin(' in task['expression'])


def fields(task,allowed):
    if set(task)-META-set(allowed):
        raise Unsupported('A source requirement has not been carried to the proof')


def fact(method,value,argument,**plan):
    return dict(theorem='method.'+method,argument=argument,**plan),value


def claim_text(task,text,*with_optional_hint):
    if task.get('source_statement',text) not in (text,*with_optional_hint):
        raise Unsupported('The typed statement differs from the printed conditions')


def polynomial_family(task,kind):
    fields(task,{'source_statement','goal','assumptions'})
    g=task['goal']
    cases=[
        ('general_polynomial_growth_proof',{'family':'real polynomial of degree n>=1 with nonzero leading coefficient',
            'input_approach':'magnitude_infinity','target':'abs(P(x))->positive_infinity','goal':'general proof for the full family'},
         ['n positive integer','a0!=0','all coefficients real']),
        ('general_rational_degree_proof',{'family':'ratio of real polynomials with nonzero leading coefficients',
            'input_approach':'magnitude_infinity','literal_claim':{'n_greater_m':'unsigned infinity',
            'n_equal_m':'a0/b0','n_less_m':'0'},'left_side':'limit abs(R(x))',
            'goal':'prove all printed degree cases without silently changing conditions'},['a0!=0','b0!=0','real coefficients']),
        ('possible_rational_limit_values',{'family':'real polynomials P,Q with common zero a',
            'conditions':['P(a)=0','Q(a)=0'],'goal':'classify all possible limits including book magnitude-infinity convention'},[]),
        ('general_polynomial_root_proof',{'polynomial_family':'P has zero constant term and arbitrary finite degree',
            'root_index':'m integer as printed','goal':'general limit identity for the whole polynomial family'},[]),
    ]
    _,goal,assumptions=next(c for c in cases if c[0]==kind)
    if g!=goal or task.get('assumptions',[])!=assumptions:
        raise Unsupported('The declared polynomial family changes a leading term or a quantified case')
    if kind=='general_polynomial_growth_proof':
        claim_text(task,'P(x)=a0*x^n+a1*x^(n-1)+...+an, n>=1,a0!=0, вещественные коэффициенты. Доказать lim_{x->infinity}|P(x)|=+infinity.')
        return fact('polynomial_limit_orders',dict(proved=True,limit='+inf',directions=['-inf','+inf']),
            'После вынесения x^n каждый оставшийся младший член стремится к нулю на обеих бесконечностях. Модуль скобки не меньше половины |a₀| на достаточно далёком хвосте.')
    if kind=='general_rational_degree_proof':
        claim_text(task,'R(x)=(a0*x^n+...+an)/(b0*x^m+...+bm), a0!=0,b0!=0. Доказать напечатанное lim_{x->infinity}|R(x)|: infinity если n>m; a0/b0 если n=m;0 если n<m.')
        return fact('polynomial_limit_orders',dict(printed_claim_holds=False,
            counterexample=dict(n=1,m=1,P='-x',Q='x',literal_value=q(-1),actual_value=ONE),
            corrected_cases={'n>m':'+inf','n=m':'abs(a0/b0)','n<m':ZERO}),
            'Вынесение старших степеней оставляет |x|^(n−m)|a₀/b₀+o(1)|. При одинаковой степени в ответе остаётся модуль. У P=−x и Q=x левый предел равен 1, а напечатанная формула даёт −1.')
    if kind=='possible_rational_limit_values':
        claim_text(task,'Пусть R(x)=P(x)/Q(x), P,Q многочлены и P(a)=Q(a)=0. Какие возможны значения lim_{x->a}P(x)/Q(x)?')
        return fact('polynomial_limit_orders',dict(cases={
            'Q identically zero':'no original domain','P identically zero and Q nonzero':ZERO,
            'ord(P)>ord(Q)':ZERO,'ord(P)=ord(Q)':'ratio of first nonzero coefficients',
            'ord(P)<ord(Q)':'infinite magnitude with side signs given by the parity of the deficit'}),
            'Вынесем максимальные степени x−a из обоих многочленов. Частное оставшихся множителей сходится к отношению их ненулевых свободных членов, а степень x−a определяет нуль, конечный предел или полюс.')
    claim_text(task,'Пусть P(x)=a1*x+a2*x^2+...+an*x^n, m целое. Доказать lim_{x->0}(root_m(1+P(x))-1)/x=a1/m.')
    return fact('polynomial_limit_orders',dict(cases={'m nonzero integer':'a1/m','m=0':'root index and quotient undefined'}),
        'У P нет свободного члена, и P(x)/x→a₁. Положительность 1+P(x) установлена в окрестности нуля. Производная u^(1/m) в u=1 равна 1/m для каждого ненулевого целого m, что даёт требуемый предел.')


def nested_radical_right(task):
    from tasks import domain_conditions
    fields(task,{'expression','variable','approach','parameters','parameter_conditions','requested_output'})
    if (task['requested_output']!=['limit_by_parameter_case','right_accumulation_domain'] or task.get('parameter_conditions')
            or len(task['parameters'])!=1 or task['approach']!=dict(point=task['parameters'][0],side='right')):
        raise Unsupported('The full parameterized right limit and its accumulation domain are required')
    v=task['variable'];a=('s',task['parameters'][0]);raw=m.parse(task['expression'],v,task['parameters'])
    if raw[0]!='add' or raw[1][0]!='sqrt' or not (r:=op.negative_term(raw[2])) or r[0]!='sqrt':
        raise Unsupported('A difference of square roots is needed')
    left,right=raw[1][1],r[1]
    if left[0]!='add' or right[0]!='add':
        raise Unsupported('The two radicands have no common scale and opposite corrections')
    scale,inner=left[1:]
    if right!=('add',scale,('mul',q(-1),inner)) or inner!=('sqrt',('add',scale,('sqrt',scale))):
        raise Unsupported('The nested corrections are not on the conjugate square-root scale')
    if (scale[0]!='div' or m.variable_in(scale[1])
            or any(domain_conditions(z) for z in scale[1:])):
        raise Unsupported('The reciprocal scale contains further raw domain restrictions')
    pn,pd=poly.rf(scale,v)
    if len(pn)!=1 or len(pd)!=2 or pn[0]/pd[1]<=0:
        raise Unsupported('The positive reciprocal coordinate has not been proved')
    coefficient=q(pn[0]/pd[1]);center=q(-pd[0]/pd[1])
    name='rho'
    while name in (v,a[1]):name+='_'
    root=('s',name);end=m.add(center,m.div(coefficient,m.power(root,2)))
    return fact('nested_radical_relative_domain',dict(
        original_domain=dict(variable=v,lower=center,upper=end,lower_open=True,upper_closed=True),
        cases=[dict(condition=f'{a[1]}=lower',value=ONE),
               dict(condition=f'lower<{a[1]}<upper',value=m.substitute(raw,{('v',v):a})),
               dict(condition=f'{a[1]}<lower or {a[1]}>=upper',value='no_original_right_approach')]),
        'На положительной ветви положим t=√A, где A — общий обратный масштаб. Последний корень действителен при t³−t−1≥0. У этого полинома ровно один положительный корень больше единицы. При t→∞ домножение на сумму корней даёт предел 1, а внутри области действует непрерывность.',
        root_condition=dict(symbol=root,polynomial=(q(-1),q(-1),ZERO,ONE),unique_positive=True),
        original=raw,affine_reciprocal=(coefficient,center))


def quadratic_root_family(task):
    fields(task,{'source_statement','goal','assumptions'})
    g=task['goal']
    if (set(g)!={'equation','variable_parameter','approach','fixed_parameters','goals'}
            or g['approach']!=dict(point='0',side='both')
            or g['goals']!=['behavior of both roots with consistent labels','all relevant parameter/sign cases']
            or len(g['fixed_parameters'])!=2):
        raise Unsupported('The disappearing leading coefficient or both root branches are unbound')
    a=g['variable_parameter'];b,c=g['fixed_parameters']
    v='x';text=f'{a}*{v}^2+{b}*{v}+{c}=0'
    if len({a,b,c,v})!=4 or g['equation']!=text or task['assumptions']!=[b+'!=0',b+','+c+' real']:
        raise Unsupported('The nonzero linear coefficient is required')
    claim_text(task,f'Изучить поведение корней x1,x2 уравнения {text} при {a}->0; {b},{c} постоянны,{b}!=0.')
    A,B,C=(('s',p) for p in (a,b,c));disc=m.add(m.power(B,2),m.neg(m.mul(q(4),m.mul(A,C))))
    rows=[]
    for sign in (-1,1):
        u=m.div(m.mul(q(-2),C),m.add(B,m.mul(q(sign),('sqrt',disc))))
        rows.append(dict(condition=f'{b}'+('>0' if sign==1 else '<0'),finite_root=u,
            other_root=m.add(m.div(m.neg(B),A),m.neg(u)),finite_limit=m.div(m.neg(C),B),
            divergent_sign_by_side=dict(left=sign,right=-sign)))
    return fact('regular_root_branch',dict(branches=rows,zero_leading_coefficient=m.div(m.neg(C),B)),
        'Дискриминант стремится к положительному квадрату линейного коэффициента. Выбираем знак корня, при котором числитель стремится к нулю, и рационализуем его. Остальной корень следует из суммы корней, включая знаки двух бесконечных ветвей.',
        discriminant=disc,source_condition=b+'!=0')


def finite_source_limit(task,library,kind):
    from tasks import source
    if kind=='all_infinite_directions_taylor_limit':
        fields(task,{'expression','variable','requested_output'})
        meta=task.get('source',{})
        if (task['requested_output']!=['both_infinite_directions','expansion_method']
                or meta.get('printed_approach','x→∞')!='x→∞'
                or meta.get('method_heading','Используя разложения I—V, найти следующие пределы')!='Используя разложения I—V, найти следующие пределы'
                or set(meta)-{'exercise','pdf_page','printed_page','pdf_sha256','printed_approach','method_heading'}):
            raise Unsupported('The full Taylor method or two original directions are not preserved')
        raw=m.parse(task['expression'],task['variable'])
        if any(e[0] not in ('add','mul','div','pow','rpow','ln','sin','cos','exp','q','v','pi') for _,e in op.expression_positions(raw)):
            raise Unsupported('The printed expansions I–V do not cover an original operation')
        child=dict(kind='limit',expression=task['expression'],variable=task['variable'],
                   approach=dict(point='infinity',side='both',mode='magnitude_infinity'))
        argument='Подставляем 1/x на обеих бесконечностях и используем напечатанное разложение для малой координаты. Раздельные односторонние остатки дают общий предел.'
    else:
        fields(task,{'expression','variable','approach','parameters','parameter_conditions'})
        raw=m.parse(task['expression'],task.get('variable','x'),task.get('parameters',[]))
        if not op.trig_candidates(raw,'tan_minus_sin'):
            raise Unsupported('A constructible trigonometric cancellation is required for this source route')
        child={k:task[k] for k in ('expression','variable','approach','parameters','parameter_conditions') if k in task}
        child['kind']='limit'
        argument='Разложения синуса и косинуса строятся на каждой стороне, тангенс заменяется их частным при доказанном ненулевом косинусе. Ведущие члены берутся после сокращения совпавших порядков.'
    plan,value=germ_limit(child,library,orders=(4,6,8))
    return dict(plan,argument=argument,original_task=child),value


def integer_sine_trace(task):
    fields(task,{'source_statement','goal','source_assumptions'})
    g=task['goal']
    if (set(g)!={'expression','parameter_n','requests'} or g['parameter_n']!='integer'
            or g['requests']!=['f(n)','left limit at n','right limit at n'] or task.get('source_assumptions')):
        raise Unsupported('The integer parameter and both requested traces must be bound')
    e=g['expression'];matched=re.fullmatch(r'sgn\(sin\((?:(-?\d+)\*)?pi\*x\)\)',e)
    if not matched:
        raise Unsupported('An integral multiple of the basic sine phase is needed')
    k=int(matched[1] or '1')
    claim_text(task,f'Найти f(n),f(n-0),f(n+0), n=0,+/-1,..., если f(x)={e}.')
    if not k:
        value=dict(at=ZERO,left=ZERO,right=ZERO)
    else:
        s='1' if k%2==0 else '(-1)^n'
        value=dict(at=ZERO,left=('−' if k>0 else '')+s,right=('−' if k<0 else '')+s)
    return fact('integer_phase_traces',value,
        'Сдвиг на целый n переносит синус к фазе kπn. В самой точке он равен нулю, а на близких сторонах знак малой фазы противоположен. Чётность k n даёт общий множитель для обоих следов.',
        harmonic=k,index='any integer n')


def logical_limit_example(task,kind):
    fields(task,{'source_statement','goal','source_assumptions'})
    if task.get('source_assumptions'):
        raise Unsupported('A source premise cannot be dropped from the implication')
    g=task['goal']
    if kind=='composition_limit_counterexample':
        if g!=dict(goals=['decide the proposed implication','analyze the specified example'],
                example={'phi':'Thomae function1/q on reduced rationals,0 on irrationals',
                         'psi':'indicator(t!=0)','approach':'x->0'},
                hypotheses=['lim(phi(x),x->a)=A','lim(phi(x),x->A)=B'],
                conclusion='lim(psi(phi(x)),x->a)=B'):
            raise Unsupported('Both literal inner limits and the example must agree with the source')
        claim_text(task,'Если φ(x)→A при x→a и φ(x)→B при x→A, следует ли, что ψ(φ(x))→B при x→a? Рассмотреть φ(p/q)=1/q для несократимых дробей p/q, φ=0 на иррациональных, ψ(t)=1 при t≠0 и ψ(0)=0, x→0.')
        return fact('limit_support_and_counterexamples',dict(implication_holds=False,
            literal_limits=dict(A=ZERO,B=ZERO),possible_outer_function_reading=dict(A=ZERO,B=ONE),
            composition_limits=dict(rational=ONE,irrational=ZERO)),
            'У ненулевой несократимой дроби p/q имеем 1/q≤|p/q|. На иррациональных φ=0. Значит, предел φ в нуле равен 0, но композиция принимает 1 на 1/n и 0 на √2/n. Если во второй предпосылке читать ψ, внешний предел равен 1, и пример всё равно опровергает вывод.',
            phase_sequences=('1/n','sqrt(2)/n'),zero_input='psi(0)=0')
    if kind=='uniform_array_equivalence_sum_theorem':
        if g!=dict(hypotheses=['phi/psi->1 at0','psi>0',
                'for every epsilon>0, abs(alpha_mn)<epsilon for all positive integers m once n>N(epsilon)'],
                goal='general equivalence replacement for growing sums'):
            raise Unsupported('The exact quantified uniform-array statement is required')
        claim_text(task,'Если φ(x)/ψ(x)→1 при x→0, ψ(x)>0 и α_mn→0 равномерно по m=1,2,…, доказать равенство пределов ∑_{m=1}^n φ(α_mn) и ∑_{m=1}^n ψ(α_mn), предполагая существование правого предела.')
        return fact('limit_support_and_counterexamples',dict(printed_claim_holds=False,
            counterexample=dict(phi='abs(x) for x!=0, 2 at x=0',psi='abs(x) for x!=0, 1 at x=0',
                alpha='0 for m=1, 1/n^2 for every m>1',left_limit=q(2),right_limit=ONE),
            sufficient_addition='Nonzero array entries eventually, or phi(0)=psi(0)'),
            'Предел отношения относится к проколотой области, а в равномерно малом массиве допустимы нули. Один нуль в каждой колонке даёт вклад 2 слева и 1 справа. Остальные n−1 слагаемых порядка n⁻² не влияют на предел. При согласовании нулевого значения равномерная относительная оценка переносится на сумму ввиду положительности весов.',
            finite_sums=('2+(n−1)/n^2','1+(n−1)/n^2'),uniform_upper_bound='1/n^2')
    if kind=='growth_theorem_source_review':
        if g!=dict(hypotheses=['f defined for x>a','locally bounded on every finite(a,b)',
               'increments tend to book unsigned infinity'],conclusion='f(x)/x tends to unsigned infinity'):
            raise Unsupported('The sign of the printed divergent limit must be explicit')
        claim_text(task,'Если f определена при x>a, ограничена на каждом конечном(a,b), и f(x+1)-f(x)->infinity, доказать f(x)/x->infinity при x->+infinity.')
        degree=1
    else:
        if g!=dict(parameter_n='positive integer',hypotheses=['f defined on(a,infinity)',
                'bounded on every finite(a,b)','increment quotient has a finite or infinite limit l'],
                conclusion='f(x)/x^(n+1)->l/(n+1)',infinite_limit_convention='unsigned infinity as defined in the book'):
            raise Unsupported('The index, local bound and sign convention are all required')
        claim_text(task,'f определена при x>a и ограничена на конечных(a,b). Для некоторого натурального n существует конечный или бесконечный l=lim_{x->+infinity}(f(x+1)-f(x))/x^n. Доказать lim f(x)/x^(n+1)=l/(n+1).')
        degree=2
    x=('v','x')
    raw=m.power(x,degree)
    increment=m.add(m.power(m.add(x,ONE),degree),raw)
    scale=m.power(x,degree-1)
    p,d=poly.rf(m.div(increment,scale),'x')
    if len(p)!=len(d)+1 or p[-1]/d[-1]<=0:
        raise Unsupported('The proposed unsigned difference has not been shown divergent')
    return fact('limit_support_and_counterexamples',dict(printed_claim_holds=False,
        counterexample=dict(x_domain='x>0',n=degree-1 if degree>1 else None,
                            function=f'(-1)^floor(x)*x^{degree}',absolute_scaled_value=ONE),
        corrected_domain='finite signed limit or prescribed direction of infinite divergence'),
        'При сдвиге на единицу множитель (−1)^⌊x⌋ меняет знак. Поэтому модуль нормированного приращения растёт, а модуль нормированного значения функции постоянно равен 1. Для подписанного приращения телескопирование по x=t+N и ограниченность начального отрезка дают требуемый результат. Для степенной шкалы сумма (t+j)^n после нормировки стремится к 1/(n+1).',
        signed_scale=scale,absolute_increment=increment,leading_coefficient=q(p[-1]/d[-1]))


def contraction_iteration(task,kind):
    from verify import same_value
    fields(task,{'source_statement','goal','source_assumptions'})
    g=task['goal']
    if kind=='kepler_fixed_point_existence_uniqueness':
        if (set(g)!={'equation','initial','recurrence','goals'} or g['initial']!='x[0]=m'
                or g['goals']!=['prove convergence','identify its limit as a root','prove uniqueness']
                or task.get('source_assumptions')!=['0<epsilon<1','m real']):
            raise Unsupported('A strict global contraction and the original starting point are required')
        fun=re.fullmatch(r'x\[n\]=m\+epsilon\*(sin|cos)\(x\[n-1\]\)',g['recurrence'])
        if not fun or g['equation']!=f'x-epsilon*{fun[1]}(x)=m':
            raise Unsupported('The recurrence and fixed-point equation do not agree')
        if task.get('source_statement') and fun[1]!='sin':
            raise Unsupported('The printed Kepler equation uses the sine')
        claim_text(task,'Для x-epsilon*sin(x)=m,0<epsilon<1, положить x0=m,xn=m+epsilon*sin(x[n-1]). Доказать существование предела xi и его единственность как корня.')
        return fact('contracting_error_coordinate',dict(converges=True,unique_root=True,limit_equation=g['equation'],
             cauchy_error_bound='epsilon^n*abs(x[1]-x[0])/(1-epsilon)'),
            'Синус и косинус имеют производные модуля не больше единицы. Поэтому отображение сжимает расстояния с коэффициентом ε. Геометрическая оценка последовательных разностей даёт критерий Коши. Непрерывность переносит уравнение в предел, а строгое сжатие исключает второй корень.',
            rate=('s','epsilon'),initial=('s','m'),model=g['recurrence'])
    if task.get('source_assumptions'):
        raise Unsupported('The original positivity assumptions must stay attached to the iteration')
    expected='convergence and exact limit' if kind=='reciprocal_newton_iteration_proof' else 'full convergence proof'
    x,y=('s','x'),('s','y')
    term=g['recurrence']
    if not term.startswith('y[n]=') or g['goal']!=expected:
        raise Unsupported('The update and all convergence obligations must be specified')
    update=m.parse(term.removeprefix('y[n]=').replace('y[n-1]','y'),None,['x','y'])
    if kind=='reciprocal_newton_iteration_proof':
        if set(g)!={'hypotheses','recurrence','goal'} or g['hypotheses']!=['x>0','y[0]>0','y[1]>0']:
            raise Unsupported('Both positive initial iterates are required for reciprocal convergence')
        text='x>0,yn=y[n-1]*(2-x*y[n-1]). Доказать: если y0>0 и y1>0, то yn сходится к1/x.'
        claim_text(task,text,text+' Указание: изучить1/x-yn.')
        error=m.add(ONE,m.neg(m.mul(x,y)))
        target=m.div(ONE,x)
        explanation='Подставляем правило обновления в масштабированную ошибку 1−xy. Получается точный квадрат предыдущей ошибки. Положительность y₁ и равенство e₁=e₀² дают 0≤e₁<1, откуда eₙ→0 и положительность всех последующих yₙ.'
    else:
        if (set(g)-{'hypotheses','recurrence','goal','source_hint'} or g['hypotheses']!=['x>0','y[0]>0']
                or g.get('source_hint','the displayed cross-ratio is squared at each step')!='the displayed cross-ratio is squared at each step'):
            raise Unsupported('The positive square-root setting or optional displayed hint differs from the source')
        if not same_value(update,m.div(m.add(y,m.div(x,y)),q(2))):
            raise Unsupported('The proposed update does not preserve the verified positive domain')
        text='Для x>0,y0>0 произвольного,yn=(y[n-1]+x/y[n-1])/2 доказать yn->sqrt(x).'
        claim_text(task,text,text+' Указание: использовать квадрат отношения(yn-sqrt(x))/(yn+sqrt(x)).')
        target=('sqrt',x)
        error=m.div(m.add(y,m.neg(target)),m.add(y,target))
        explanation='Положительные x и y обеспечивают положительность следующей итерации. Подстановка показывает точное возведение в квадрат отношения ошибки к сумме y+√x. Его начальный модуль строго меньше единицы. Обращение дроби даёт предел √x.'
    changed=m.substitute(error,{y:update})
    if not same_value(changed,m.power(error,2)):
        raise Unsupported('The transformed error is not the square of the previous error')
    return fact('contracting_error_coordinate',dict(converges=True,limit=target,updated_error='square',
                 domain_preserved=True),explanation,recurrence=update,error_coordinate=error,
                 error_after_update=changed,source_conditions=g['hypotheses'])


def stable_germ_at(expression,var,point,side,library,parameters=(),conditions=()):
    """Use a scale-preserving rewrite only after verifying its witnesses."""
    from scalar_proofs import global_guard
    from tasks import source,domain_conditions
    from verify import same_value
    def compute(e):
        t=dict(kind='limit',expression=source(e),variable=var,parameters=list(parameters),
               stated_conditions=list(conditions),approach=dict(point=point,side=side))
        return germ_limit(t,library,orders=(2,4,6,8),split=False)
    try:return compute(expression)
    except Unsupported as original:
        if not any(e[0]=='exp' for _,e in op.expression_positions(expression)):
            raise original
        ctx=m.context(dict(variable=var,parameters=list(parameters),parameter_conditions=list(conditions)))
        guards=domain_conditions(expression)
        for relation,e in guards:
            if global_guard((relation,e),var,ctx):continue
            # exp(u)-1 has the same sign and the same zeros as u.
            phase=next((z[1] for _,z in op.expression_positions(e)
                        if z[0]=='exp' and same_value(e,m.add(z,q(-1)))),e)
            series,proof_ctx,_=local_coefficients(phase,var,point,side,4,library,parameters,conditions)
            sign=op.near_sign(series,proof_ctx)
            if not (sign==1 or sign==-1 and relation=='nonzero' or sign==0 and relation=='nonnegative'):
                raise Unsupported('A raw scale-transport guard is unresolved on the original approach')
        for logarithm in (True,False):
            for phase,changed in op.exponential_scale_candidates(expression,logarithm):
                try:
                    phase_plan,pl=compute(phase)
                    if pl!='+inf':continue
                    proof,value=compute(changed)
                    return dict(proof,scale_transport=dict(original=expression,transformed=changed,
                        exponential_phase=phase,phase_proof=phase_plan,original_guards=guards)),value
                except (Unsupported,op.Unavailable,op.ResourceBound):
                    continue
        raise original


def line_at_infinity(raw,v,point,library,parameters=(),conditions=()):
    var=('v',v);side='positive_infinity' if point=='+inf' else 'negative_infinity'
    first,k=stable_germ_at(('div',raw,var),v,point,side,library,parameters,conditions)
    if isinstance(k,dict) and k.get('status')=='no_original_approach':
        return dict(slope_proof=first),dict(approach=point,status='no_original_tail')
    if not isinstance(k,tuple):
        return dict(slope_proof=first),dict(approach=point,status='no_linear_asymptote')
    remainder=('add',raw,('mul',q(-1),('mul',k,var)))
    second,b=stable_germ_at(remainder,v,point,side,library,parameters,conditions)
    if not isinstance(b,tuple):
        return dict(slope_proof=first,intercept_proof=second),dict(approach=point,status='no_linear_asymptote')
    return dict(slope_proof=first,intercept_proof=second),dict(approach=point,slope=k,intercept=b)


def asymptotic_line_fitting(task,kind,library):
    from tasks import domain_conditions
    from verify import same_value
    fields(task,{'source_statement','goal','assumptions','source_assumptions'})
    if task.get('assumptions') or task.get('source_assumptions'):
        raise Unsupported('An extra fixed parameter hypothesis remains')
    g=task['goal'];x=('v','x')
    if kind=='asymptote_criterion_proof':
        if g!=dict(definition='common-line error tends to0',input_infinity='printed unsigned infinity, both admissible tails',
                  goal='derive necessary and sufficient conditions'):
            raise Unsupported('The original asymptote hypothesis refers to both admissible tails')
        claim_text(task,'Прямая y=k*x+b есть асимптота графика f, если lim_{x->infinity}(f(x)-(k*x+b))=0. Вывести необходимые и достаточные условия её существования.')
        return fact('successive_asymptote_coefficients',dict(necessary_and_sufficient=[
                    'k = limit of f(x)/x on both admissible tails','b = limit of f(x)-k*x on both admissible tails'],
                     unique_when_exists=True),
            'Если f−kx−b→0, то деление на x даёт k, а выделение остатка даёт b. Обратно, второй предел означает стремление расстояния до прямой к нулю. Для общей прямой коэффициенты на двух хвостах должны совпадать.')
    if kind=='asymptotic_coefficient_identification':
        if g!=dict(expression=g.get('expression'),input_approach='magnitude infinity',target='0',goal='determine every constant pair a,b'):
            raise Unsupported('Both infinite directions and every coefficient are required')
        claim_text(task,f"Найти a,b из lim_{{x->infinity}}({g['expression']})=0.")
        descriptions=[(g['expression'],('a','b'),p) for p in ('-inf','+inf')]
    else:
        if set(g)!={'goal','directional_conditions'} or g['goal']!='determine all four constants' or len(g['directional_conditions'])!=2:
            raise Unsupported('Both directional residuals are needed')
        entries=g['directional_conditions']
        for row,d in zip(entries,('negative_infinity','positive_infinity')):
            if set(row)!={'direction','expression','target'} or row['direction']!=d or row['target']!='0':
                raise Unsupported('The original directions or their required residuals differ')
        first,second=[r['expression'] for r in entries]
        claim_text(task,f'Найти a_i,b_i,i=1,2: {first}->0 при x->-infinity и {second}->0 при x->+infinity.')
        descriptions=[(first,('a1','b1'),'-inf'),(second,('a2','b2'),'+inf')]
    solutions={};proofs=[]
    for expression,(a,b),p in descriptions:
        symbols=[('s',a),('s',b)]
        full=m.parse(expression,'x',[a,b]);raw=m.substitute(full,dict.fromkeys(symbols,ZERO))
        line=('add',('mul',symbols[0],x),symbols[1])
        if (not same_value(full,m.add(raw,m.neg(line))) or
                any(any(m.contains(e,s) for s in symbols) for _,e in domain_conditions(full))):
            raise Unsupported('The unknown constants are not free affine correction terms')
        plan,values=line_at_infinity(raw,'x',p,library)
        if 'slope' not in values:raise Unsupported('The required finite directional line remains open')
        for name,value in zip((a,b),(values['slope'],values['intercept'])):
            if name in solutions and not same_value(solutions[name],value):
                raise Unsupported('The two original tails give different line coefficients')
            solutions[name]=value
        proofs.append(dict(original_residual=full,fit=plan,direction=p))
    return fact('successive_asymptote_coefficients',dict(coefficients=solutions),
        'Сначала делим на x и вычисляем коэффициент при x. Затем вычитаем найденный линейный член и вычисляем свободный коэффициент. Обе односторонние справки проверены с исходной областью.',
        directional_proofs=proofs)


def finite_domain_cuts(raw,v):
    from graphs import rational_roots
    from scalar_proofs import global_guard
    from tasks import domain_conditions
    from verify import same_value
    ctx=m.context(dict(variable=v));cuts=set()
    for r,e in domain_conditions(raw):
        if global_guard((r,e),v,ctx):continue
        exponentials=[z for _,z in op.expression_positions(e) if z[0]=='exp']
        for z in exponentials:
            if same_value(e,m.add(z,q(-1))):
                # exp(u)-1 has exactly the zero set of its original argument.
                e=z[1];break
        try:p,d=poly.rf(e,v)
        except (poly.Undefined,poly.NotRational) as ex:
            raise Unsupported('An original finite domain boundary is not isolated') from ex
        if not any(p):
            raise Unsupported('An entire original restriction is identically zero')
        for a in [*rational_roots(p),*rational_roots(d)]:
            cuts.add(q(a.a) if not a.b else m.add(q(a.a),m.mul(q(a.b),('sqrt',q(a.d)))))
    return sorted(cuts)


def curve_asymptotes(task,kind,library):
    from tasks import source
    from verify import same_value
    v='x';x=('v',v)
    if kind=='mathematical_question':
        fields(task,{'source_statement','goal','source_assumptions'})
        g=task['goal'];text=g['expression']
        if set(g)!={'expression','goals'} or task.get('source_assumptions'):
            raise Unsupported('The retained asymptote question changes the original domain')
        claim_text(task,'Найти асимптоты и построить кривую y='+text+'.')
        raw=m.parse(text,v);conditions=[];finite=finite_domain_cuts(raw,v)
        pairs=[]
        for cut in finite:
            branches=[]
            for side in ('left','right'):
                step,lim=stable_germ_at(raw,v,source(cut),side,library)
                branches.append(dict(side=side,result=lim,proof=step))
            pairs.append(dict(point=cut,vertical=any(b['result'] in ('+inf','-inf') for b in branches),branches=branches))
        tails=('-inf','+inf');tail_expression=raw
    else:
        fields(task,{'curve','source_assumptions','requested_output'})
        if task['source_assumptions']!=['x>0'] or task['requested_output']!=[
                'find_asymptote','justify_asymptotic_line','check_original_domain_ends']:
            raise Unsupported('The positive source domain or complete asymptote request is unbound')
        text=task['curve']
        if not text.startswith('y='):raise Unsupported('An explicit source graph is needed')
        raw=m.parse(text[2:],v)
        if raw[0]!='div' or any(z[0]!='rpow' for z in raw[1:]):
            raise Unsupported('No common varying exponent has been identified')
        numerator,denominator=raw[1:];difference=m.add(numerator[2],m.neg(denominator[2]))
        if numerator[1]!=x or not same_value(denominator[1],m.add(ONE,x)) or denominator[2]!=x or not m.num(difference) or m.num(difference)<=0:
            raise Unsupported('The common exponent and the small-end comparison were not proved')
        tail_expression=('mul',('rpow',x,difference),('rpow',('div',x,denominator[1]),x))
        tails=('+inf',);conditions=['x>0']
        pairs=[dict(point=ZERO,vertical=False,branches=[dict(side='right',result=ZERO,
            proof='The positive power of x tends to zero and (x/(1+x))^x stays in (0,1).')])]
    lines=[];plans=[]
    for point in tails:
        plan,value=line_at_infinity(tail_expression,v,point,library,conditions=conditions)
        plans.append(plan);lines.append(value)
    return fact('successive_asymptote_coefficients',dict(directional_lines=lines,finite_boundaries=pairs,
                vertical_asymptotes=[r['point'] for r in pairs if r['vertical']]),
        'Разбираем все исходные конечные границы и вычисляем подходы с доступных сторон. Для каждого бесконечного хвоста сначала определяем наклон по f(x)/x, затем свободный член по разности. Переносы выполняются на той же области.',
        original=raw,tail_expression=tail_expression,directional_proofs=plans)


def local_coefficients(raw,v,point,side,order,library,parameters=(),conditions=()):
    from tasks import source
    task=dict(kind='limit',expression=source(raw),variable=v,parameters=list(parameters),
              stated_conditions=list(conditions),approach=dict(point=point,side=side))
    ctx,targets=m.limit_directions(task,[],library.data.get('magnitude_infinity_contract'))
    t,oriented=targets[0]
    e,transport=m.normalized(t,ctx,oriented)
    ctx=dict(ctx,order=order)
    try:series=elementary_jet(e,ctx)
    except (op.Unavailable,op.ResourceBound,EmptyGerm) as exc:
        raise Unsupported('The local analytic terms or necessary branch are not admitted') from exc
    return series,ctx,transport


def source_expansion(task,library):
    from finite_sums import translated_coefficients
    from integrals import affine
    from math import factorial
    from tasks import domain_conditions,known_guard,source
    fields(task,{'expression','degree','variable','parameters','parameter_conditions','variable_domain','approach','requested_output'})
    v=task['variable'];degree=task['degree'];params=task['parameters'];conditions=task['parameter_conditions']
    approach=task['approach'];req=task['requested_output'];meta=task.get('source',{})
    if (set(approach)!={'point','side'} or approach['side']!='both' or task['variable_domain']!='real'
            or set(meta)-{'exercise','printed_page','pdf_page','pdf_sha256','literal_requirement','instruction',
                          'remainder_reference','additional_question'}):
        raise Unsupported('A complete real Taylor neighborhood is required')
    point=approach['point'];raw=m.parse(task['expression'],v,params)
    if degree=='n':
        if (raw[0]!='ln' or point!='0' or 'n' not in params or 'n>0' not in conditions
                or req!=['finite_power_expansion'] or meta.get('literal_requirement') not in (None,
                   'h — приращение, x>0; нужен общий коэффициент до h^n для каждого натурального n.')):
            raise Unsupported('The logarithmic family must keep the finite order n and the positive base')
        slope,base=affine(raw[1],v);ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=conditions))
        if not known_guard(('positive',base),ctx) or not m.constant_defined(slope,ctx) or m.contains(raw,('s','n')):
            raise Unsupported('The center and slope of the logarithm are not fixed real constants on this family')
        return fact('finite_taylor_obligations',dict(constant=('ln',base),
            coefficient=f'(-1)^(j+1)*({source(slope)}/{source(base)})^j/j for 1<=j<=n',
            order='n a positive integer',remainder='O(h^(n+1)) for fixed parameters'),
            'Раскладываем логарифм положительного центра и логарифм единицы плюс малое аффинное приращение. Коэффициент каждого j берётся из общей формулы для ln(1+u).',
            slope=slope,positive_base=base,original=raw)
    if params or conditions or type(degree)!=int or degree<0:
        raise Unsupported('An exact numeric expansion center and finite integer order are required')
    at=m.parse(point,None);ctx=m.context(dict(variable=v))
    if req==['finite_power_expansion','global_polynomial_identity']:
        p,d=poly.rf(raw,v)
        if (domain_conditions(raw) or len(d)!=1 or not d[0] or m.num(at) is None or len(p)>degree+1
                or meta.get('literal_requirement') not in (None,'Разложить данный многочлен по целым неотрицательным степеням x+1, как тождество.')
                or meta.get('literal_requirement') and at!=q(-1)):
            raise Unsupported('A global identity needs a polynomial with its correct printed shift')
        coefficients=tuple(q(c/d[0]) for c in translated_coefficients(p,m.num(at)))
        return fact('finite_taylor_obligations',dict(center=at,coefficients=coefficients,global_identity=True),
            'Заменяем x суммой центра и новой координаты. Все степени раскрываются конечной биномиальной формулой, поэтому остаток тождественно нулевой.',
            original=raw,degree=degree)
    if (req!=['finite_power_expansion','fourth_derivative_at_zero'] or at!=ZERO or degree!=4
            or meta.get('additional_question') not in (None,'Найти также четвёртую производную f в точке 0.')
            or meta.get('instruction') not in (None,'Целые неотрицательные степени x до указанной степени включительно.')
            or meta.get('remainder_reference') not in (None,'стр.132–133, §10, формулы (1),(2)')
            or any(not known_guard((r,m.substitute(e,{('v',v):at})),ctx) for r,e in domain_conditions(raw,True))):
        raise Unsupported('The extra derivative at the original expansion center is not bound')
    series,_,transport=local_coefficients(raw,v,point,'right',degree+2,library)
    c,rem=op.unpack(series)
    if rem is not None and rem<degree or any(p.denominator!=1 or p<0 for p in c):
        raise Unsupported('The coefficients have no complete integer-order remainder')
    coefficients=tuple(c.get(i,ZERO) for i in range(degree+1))
    return fact('finite_taylor_obligations',dict(center=at,coefficients=coefficients,
             fourth_derivative=m.mul(q(factorial(degree)),coefficients[degree])),
        'Формальное деление соседних степеней даёт коэффициенты полного разложения. Ненулевой знаменатель в центре обеспечивает аналитичность. Производная указанного порядка равна коэффициенту, умноженному на факториал.',
        original=raw,transport=transport,series=series)


def fit_coefficients(task,kind,library):
    from itertools import combinations
    from level_sets import solve_linear
    fields(task,{'variable','free_coefficients','approach','goal','requested_output','assumptions'})
    g=task['goal'];approximation=kind=='fit_asymptotic_coefficients_and_apply_to_geometry'
    v=task.get('variable','x')
    if approximation:
        if (g!=dict(formula='x ≈ alpha*sin(x)+beta*tan(x)',source_precision='с точностью до члена с x^5',
                 application='приближенное спрямление дуг малой угловой величины')
                or task['assumptions']!=['x is small in absolute value'] or task['requested_output']!=[
                    'determine_alpha_and_beta','justify_order_of_error','give_small_arc_rectification']):
            raise Unsupported('The prescribed order and the arc application must both be preserved')
        names=['alpha','beta'];residual='x-(alpha*sin(x)+beta*tan(x))';order=5;exact=False
        denominator=ONE
    else:
        if (task.get('approach')!=dict(point='0',side='both') or task.get('assumptions')
                or task['requested_output']!=['determine_all_coefficients','justify_order']):
            raise Unsupported('All free coefficients and the simultaneous orders on both sides are required')
        names=task['free_coefficients'];denominator=ONE
        exact_term=re.fullmatch(r'exactly (\d+|fifth) order relative to '+re.escape(v),g.get('order',''))
        exact=exact_term is not None
        if exact:
            if set(g)!={'residual','order'}:raise Unsupported('The given residual is not complete')
            residual=g['residual'];order=5 if exact_term[1]=='fifth' else int(exact_term[1])
        else:
            matched=re.fullmatch(r'(.+?)=(.+?)\+O\('+re.escape(v)+r'\^(\d+)\)',g.get('formula',''))
            if not matched or set(g)!={'formula','order'} or g['order']!='big_O_'+matched[3]:
                raise Unsupported('The remainder order is not bound by the formula')
            order=int(matched[3]);left=m.parse(matched[1],v,names);right=m.parse(matched[2],v,names)
            if right[0]=='div':numerator,denominator=right[1:]
            else:numerator=right
            residual=('add',('mul',denominator,left),('mul',q(-1),numerator))
    raw=m.parse(residual,v,names) if isinstance(residual,str) else residual
    if not names or len(names)!=len(set(names)) or order<=0:
        raise Unsupported('An unconstrained finite vector of real coefficients is required')
    symbols=[('s',p) for p in names];records=[]
    for side in ('right','left'):
        den,ctx,_=local_coefficients(denominator,v,'0',side,order+2,library,names)
        lead,coef=op.leading(den)
        if lead.denominator!=1 or lead<0 or not m.nonzero(coef,ctx):
            raise Unsupported('The rational denominator order changes with a free coefficient')
        cutoff=order+int(lead)
        series,ctx,transport=local_coefficients(raw,v,'0',side,cutoff+4,library,names)
        coeff,rem=op.unpack(series)
        if rem is not None and rem<cutoff:
            raise Unsupported('A needed cancellation lies beyond the verified remainder')
        records.append((side,cutoff,den,series,transport,coeff))
    equations=[e for side,cutoff,_,_,_,terms in records for p,e in terms.items() if p<cutoff]
    matrix=[]
    for e in equations:
        p,d=m.rational_form(e)
        if set(d)!={()} or any(mon and (len(mon)!=1 or mon[0][0] not in symbols or mon[0][1]!=1) for mon in p):
            raise Unsupported('Coefficient matching is not affine')
        matrix.append(([p.get(((s,1),),F(0))/d[()] for s in symbols],-p.get((),F(0))/d[()]))
    trial=None
    for rows in combinations(matrix,len(symbols)):
        trial=solve_linear([row for row,b in rows],[b for row,b in rows])
        if trial is not None:break
    if trial is None or any(sum(a*c for a,c in zip(row,trial))!=b for row,b in matrix):
        raise Unsupported('There is no certified unique matching family')
    env=dict(zip(symbols,map(q,trial)));leading=[]
    for side,cutoff,den,series,transport,terms in records:
        coefficient=m.simplify(m.substitute(terms.get(cutoff,ZERO),env))
        if exact and not m.nonzero(coefficient,m.context({})):
            raise Unsupported('The required exact leading coefficient vanishes')
        leading.append(dict(side=side,coefficient=m.div(coefficient,op.leading(den)[1])))
    result=dict(coefficients=dict(zip(names,map(q,trial))),remainder_order=order,exact_order=exact,
                first_allowed_coefficients=leading)
    if approximation:
        result.update(arc_formula='R*(alpha*sin(theta)+beta*tan(theta))',angle_unit='radians',
                      length_error='O(R*theta^5) at fixed R')
    return fact('asymptotic_linear_coefficient_matching',result,
        'Проверяем порядок знаменателя в обеих проколотых окрестностях, затем приводим задачу к исчезновению коэффициентов остатка. Решаем точную линейную систему и подставляем ответ. Для точного порядка первый оставшийся коэффициент проверяется на ненулевость.',
        original_residual=raw,denominator=denominator,side_witnesses=[r[:-1] for r in records],
        equations=[([q(c) for c in row],q(rhs)) for row,rhs in matrix])


def geometry_germ(task,kind,library):
    from verify import same_value
    if kind=='geometric_limit_from_tangent_angle':
        fields(task,{'given','parameters','source_assumptions','requested_output'})
        if (task.get('given')!='The curve y=f(x) enters the origin as x->0: lim(f(x))=0, under angle alpha.'
                or task['parameters']!=['alpha'] or task.get('source_assumptions')
                or task['requested_output']!=['find lim(y/x) as x->0','geometric_angle_conditions_and_justification']):
            raise Unsupported('The original incidence and tangent angle are required')
        return fact('geometric_limit_transport',dict(
            finite_angle_condition='cos(alpha)!=0',finite_slope=('tan',('s','alpha')),
            vertical_condition='cos(alpha)=0',vertical_magnitude_limit='+inf'),
            'Секущая из начала имеет направление (x,y), поэтому её угловой коэффициент равен y/x. Предел направления с ненулевой горизонтальной компонентой даёт тангенс угла. При вертикали обратный коэффициент стремится к нулю, а знак y/x зависит от ветви.')
    if kind=='prove_limit_under_geometric_bound':
        fields(task,{'given','parameters','source_assumptions','claim','requested_output'})
        if (task['given']!='A continuous curve y=f(x) enters the origin as x->+0, lim(f(x))=0, and for0<x<epsilon stays entirely inside the acute angle bounded by y=-k*x and y=k*x, with finite k.'
                or task['parameters']!=['k','epsilon'] or task['source_assumptions']!=['k finite real','epsilon>0']
                or task['claim']!='lim(x^f(x), x->+0)=1' or task['requested_output']!=[
                'proof','translation_of_geometric_bound','original_positive_base_domain']):
            raise Unsupported('The finite wedge and positive original approach are required')
        return fact('geometric_limit_transport',dict(limit=ONE,approach='0+',
            comparison='abs(f(x)*ln(x))<=abs(k)*x*abs(ln(x))'),
            'На положительной полуоси клин даёт |f(x)|≤|k|x. Модуль логарифма степени ограничен |k|x|ln x|, который стремится к нулю. Непрерывная экспонента переносит предел обратно.')
    if kind=='circular_segment_asymptotic':
        fields(task,{'radius','chord','sagitta','approach','requested_output'})
        if (task['radius']!='R fixed' or task['chord']!='b' or task['sagitta']!='h'
                or task['approach']!='arc length tends to zero' or task['requested_output']!=[
                    'ratio limit','leading approximation in b,h']):
            raise Unsupported('A fixed radius and the complete geometric request are required')
        meta=task.get('source',{})
        if meta.get('literal_requirement') not in (None,
            'Find the limiting ratio of the circular segment area to its inscribed isosceles triangle, then deduce the approximation in chord b and sagitta h.'):
            raise Unsupported('The original area comparison was not bound')
        raw=m.parse('(t-sin(t)*cos(t))/(sin(t)*(1-cos(t)))','t')
        plan,value=stable_germ_at(raw,'t','0','right',library)
        if not isinstance(value,tuple):raise Unsupported('No finite area ratio')
        return fact('geometric_limit_transport',dict(area_ratio=value,coefficient_of_chord_times_sagitta=m.div(value,q(2))),
            'Выражаем площадь кругового сегмента как площадь сектора без центрального треугольника. У обоих сравниваемых площадей сокращается R². Ведущие кубические члены по половине угла дают отношение, а площадь вписанного треугольника равна bh/2.',
            parameter='positive half of the central angle',normalized_area_ratio=raw,calculation=plan)
    fields(task,{'assumptions','goal','requested_output'})
    if (task['assumptions']!=['The base of an isosceles triangle is the chord of a circular arc',
                  'The triangle height is sqrt(4/3) times the sagitta of the arc']
            or task['goal']!=dict(approximation='sum of its two equal sides approximates the circular arc length')
            or task['requested_output']!=['estimate_relative_error_of_Chebyshev_arc_rule']):
        raise Unsupported('The chord, height and target arc must match')
    e=m.parse('sqrt(sin(t)^2+4*(1-cos(t))^2/3)/t-1','t')
    jet,ctx,transport=local_coefficients(e,'t','0','right',8,library)
    order,c=op.leading(jet)
    if not m.nonzero(c,ctx):
        raise Unsupported('No nonzero relative-error coefficient')
    return fact('geometric_limit_transport',dict(relative_error_formula=e,leading_signed_error=(q(order),c),
                leading_absolute_error=(q(order),m.simplify(('abs',c)))),
        'Половина хорды и высота треугольника дают катеты. Деление боковой длины на половину дуги устраняет радиус. Разложение корня даёт первый ненулевой коэффициент относительной ошибки.',
        angle='positive half of the central angle',series=jet,transport=transport)


def abstract_taylor_limits(task,kind,library):
    if kind=='classify_differentiability_at_point':
        fields(task,{'function','point','requested_output'})
        if (task['point']!='0' or task['requested_output']!=[
                'investigate_differentiability_at0','proof','derivative_value_if_it_exists']
                or set(task['function'])!={'branches'}):
            raise Unsupported('The originally assigned value and full point question are required')
        outside,inside=task['function']['branches']
        if set(outside)!={'when','expression'} or set(inside)!={'when','value'} or (
            outside['when'],inside['when'])!=('x!=0','x=0'):
            raise Unsupported('The original punctured branch and point do not agree')
        raw=m.parse(outside['expression'],'x');at=m.parse(inside['value'],None);x=('v','x')
        quotient=('div',('add',raw,('mul',q(-1),at)),x)
        sides=[stable_germ_at(quotient,'x','0',s,library) for s in ('left','right')]
        from verify import same_value
        a,b=[v for _,v in sides]
        if not isinstance(a,tuple) or not isinstance(b,tuple) or not same_value(a,b):
            from verify import different_value
            if any(isinstance(t,dict) for t in (a,b)) or a!=b and not different_value(a,b,m.context({})):
                raise Unsupported('The two full difference-quotient limits have not been compared')
            result=dict(differentiable=False,one_sided=(a,b))
        else:result=dict(differentiable=True,derivative=a,at=at)
        return fact('finite_taylor_obligations',result,
            'В разностном отношении вычитаем исходно заданное значение функции в точке. Сравниваем пределы полученного отношения слева и справа, сохраняя исключение нуля при вычислении исходной ветви.',
            difference_quotient=quotient,side_proofs=[p for p,_ in sides])
    if kind=='prove_second_derivative_symmetric_difference_formula':
        fields(task,{'given','claim','requested_output','transcription_note'})
        if (task['given']!='The second derivative f_second(x) exists.'
                or task['claim']!='f_second(x)=lim((f(x+h)+f(x-h)-2*f(x))/h^2, h->0)'
                or task['requested_output']!=['proof','local_derivative_domain_conditions']
                or task.get('transcription_note','The formula to prove is source input, not a computed answer.')
                    !='The formula to prove is source input, not a computed answer.'):
            raise Unsupported('The two signed Taylor increments must concern the same point')
        return fact('finite_taylor_obligations',dict(proved=True,limit='f_second(x)'),
            'Пишем локальный остаток Пеано при плюс и минус h. Линейные члены сокращаются, квадратичные складываются, а каждый остаток после деления на h² исчезает. Существование второй производной даёт обе локальные формулы.')
    fields(task,{'assumptions','goal','requested_output'})
    g=task['goal'];a=task['assumptions'];want=task['requested_output']
    if kind=='quantified_taylor_remainder':
        if (g!=dict(hypothesis='f(x+h)=sum(h^k*f^(k)(x)/k!, k=0..n-1)+h^n*f^(n)(x+theta*h)/n!',
                    claim='lim(theta(h),h->0)=1/(n+1)')
                or a!=['n is a positive integer','x is fixed','some theta=theta(h) in (0,1) satisfies the given Taylor identity',
                       'f^(n+1)(x) exists and is nonzero'] or want!=['proof_for_every_admissible_theta']):
            raise Unsupported('The nonzero first variation of the n-th derivative must be retained')
        return fact('finite_taylor_obligations',dict(proved=True,limit='1/(n+1)',all_admissible_theta=True),
            'Разложим f в точке x до степени n+1 и отдельно f^(n) до первой степени. Неравенство 0<θ<1 даёт равномерное o(h) при подстановке θh. Сравнение коэффициентов и ненулевость f^(n+1)(x) дают θ=1/(n+1)+o(1).')
    if kind=='limit_under_asymptotic_hypothesis':
        if (g!=dict(claim='lim(f(x)^(1/x),x->0)=exp(k)') or a!=[
                'f(x)=1+k*x+o(x) as x approaches 0','k is a real constant'] or want!=['two_sided_proof_using_hypothesis']):
            raise Unsupported('The first-order source hypothesis cannot be weakened')
        return fact('finite_taylor_obligations',dict(proved=True,limit=('exp',('s','k')),two_sided=True),
            'Вблизи нуля f положительна. Логарифм единицы с малой добавкой сохраняет первый коэффициент k, включая k=0. Деление на x и непрерывность экспоненты дают обе стороны.')
    row1=({'claim':"abs(f'(x))<=A/2 for every 0<=x<=1"},
           ['f is C^2 on [0,1]','f(0)=f(1)=0','abs(f^(2)(t))<=A for 0<t<1'],['proof_with_endpoints'])
    row2=({'claim':'M_1^2<=2*M_0*M_2'},
           ['f is twice differentiable on the entire real line','M_k=sup_{x in R}|f^(k)(x)| is finite for k=0,1,2'],
           ['proof_for_every_such_function'])
    if (g,a,want)==row1:
        return fact('uniform_taylor_error_bound',dict(proved=True,uniform_bound='A/2',includes_endpoints=True),
            'Среднее f′ на [0,1] равно нулю по равенству крайних значений f. Применяем оценку |f′(x)−f′(t)|≤A|x−t| под интегралом. Вычисление интеграла даёт A(x²+(1−x)²)/2≤A/2.')
    if (g,a,want)==row2:
        return fact('uniform_taylor_error_bound',dict(proved=True,squared_bound='2*M_0*M_2',
             vanishing_cases=['M_0=0: zero function','M_2=0: bounded affine function is constant']),
            'Центральное приращение и остатки порядка два дают |f′(x)|≤M₀/h+M₂h/2 для всех h>0. При положительных M₀ и M₂ минимум достигается при h=√(2M₀/M₂). Нулевые множители дают постоянную функцию.')
    raise Unsupported('The derivative-bound hypotheses or endpoint behavior are incomplete')


def approximation_errors(task,kind,library):
    from math import factorial,prod
    from scalar_proofs import global_guard
    from tasks import domain_conditions
    fields(task,{'goal','requested_output'})
    g=task['goal'];want=task['requested_output'];x=('v','x')
    if kind=='approximation_validity_interval':
        if (set(g)!={'function','approximation','absolute_tolerance'} or g['function']!='cos(x)'
                or g['approximation']!='1-x^2/2' or want!=[
                    'interval_where_error_within_tolerance','certified_error_bound']):
            raise Unsupported('The exact cosine error equation and prescribed tolerance must be bound')
        t=m.parse(g['absolute_tolerance'],None)
        if m.sign(t,m.context({}))!=1:raise Unsupported('The tolerance must be positive')
        return fact('uniform_taylor_error_bound',dict(maximal_interval='[-r,r]',
            unique_positive_endpoint=('cos(r)-1+r^2/2',t),guaranteed_radius=('rpow',m.mul(q(24),t),q(1,4))),
            'Чётная ошибка косинуса неотрицательна и строго растёт на положительной полуоси, поскольку x−sin x>0 при x>0. Поэтому точный радиус задаётся единственным корнем уравнения погрешности. Остаток Лагранжа даёт достаточное условие x⁴/24≤δ.')
    if kind=='prove_taylor_remainder_inequality':
        if (want!=['proof_of_both_strict_bounds'] or g!=dict(function='(a^n+x)^(1/n)',linear_part='a+x/(n*a^(n-1))',
                equality='function=linear_part-r',constraints=['n>=2 integer','a>0','x>0'],
                claimed_bounds='0<r<(n-1)*x^2/(2*n^2*a^(2*n-1))')):
            raise Unsupported('The strictly positive increment and the order of the root are required')
        return fact('uniform_taylor_error_bound',dict(proved=True,strict_lower=ZERO,
            strict_upper='(n-1)*x^2/(2*n^2*a^(2*n-1))'),
            'Корень порядка n≥2 имеет отрицательную вторую производную на положительной оси. Модуль этой производной строго убывает, так что в промежуточной точке остатка он строго меньше значения в a^n. Умножение на x²/2 даёт обе строгие границы.')
    if set(g)!={'function','approximation','domain'} or want!=['upper_bound_for_absolute_error','interval_justification']:
        raise Unsupported('The typed expression, polynomial and full error interval are required')
    text=g['function'];domain=g['domain']
    mode=re.fullmatch(r'(0<=x<=|abs\(x\)<=)([0-9./]+)(, n a nonnegative integer)?',domain)
    if not mode:raise Unsupported('The source interval must be explicitly bounded')
    r=m.simplify(m.parse(mode[2],None));R=m.num(r)
    if R is None or R<=0:raise Unsupported('The source interval radius must be positive and rational')
    linear=m.parse(text,'x')
    if mode[3]:
        if (mode[1]!='0<=x<=' or linear!=('exp',x) or g['approximation']!='sum(x^k/k!, k=0..n)'):
            raise Unsupported('The arbitrary-degree exponential polynomial was not bound')
        return fact('uniform_taylor_error_bound',dict(abs_error_bound='exp(R)*R^(n+1)/(n+1)!',
            radius=r,attained_maximum='exp(R)-sum(R^k/k!,k=0..n)'),
            'Каждая производная экспоненты не превосходит exp(R) на исходном отрезке. Остаток Лагранжа даёт требуемую оценку. Точный максимум ошибки достигается справа, поскольку все члены оставшегося ряда неотрицательны и возрастают.')
    approximation=m.parse(g['approximation'],'x')
    if any(not global_guard(g,'x',m.context(dict(variable='x'))) for g in domain_conditions(approximation)):
        raise Unsupported('The Taylor polynomial carries an unproved restriction on the source interval')
    p,d=poly.rf(approximation,'x')
    if len(d)!=1 or not d[0]:raise Unsupported('An ordinary Taylor polynomial is required')
    degree=len(p)-1
    delta=('add',linear,('mul',q(-1),approximation))
    jet,ctx,transport=local_coefficients(delta,'x','0','right',degree+3,library)
    terms,rem=op.unpack(jet)
    if any(j<=degree for j in terms) or rem is not None and rem<=degree:
        raise Unsupported('The original approximation does not match all prescribed Taylor coefficients')
    order=degree+1
    if linear in (('sin',x),('cos',x)):
        if order not in terms:order+=1
        bound=q(R**order/F(factorial(order)))
        argument='Все производные синуса и косинуса имеют модуль не больше единицы. Следующий нулевой коэффициент позволяет поднять степень остатка Лагранжа на один порядок.'
    elif linear==('tan',x) and degree==3 and R<1:
        K=m.div(ONE,('cos',r))
        bound=m.mul(q(R**5/15),m.mul(m.power(K,2),m.add(K,ONE)))
        argument='При |t|≤R<1 положителен cos t, поэтому |tan t|≤K|t| с K=1/cos R. Интегрирование tan²t даёт кубическую оценку tan t−t. Затем интегрирование (tan t−t)(tan t+t) даёт требуемый остаток пятого порядка.'
    elif linear==('sqrt',('add',ONE,x)) and mode[1]=='0<=x<=':
        kernel=abs(prod(F(1,2)-j for j in range(order)))
        bound=q(kernel*R**order/F(factorial(order)))
        argument='Производная порядка остатка есть падающий факториал от 1/2, умноженный на отрицательную степень 1+x. На исходном положительном отрезке эта степень не превосходит единицу.'
    else:raise Unsupported('The uniform derivative bound on the original interval remains open')
    return fact('uniform_taylor_error_bound',dict(abs_error_bound=bound,radius=r,interval=domain),
        argument,original=linear,approximation=approximation,error_jet=jet,transport=transport)


def phase_specialization(e,var,phase,theta):
    """Apply a fixed phase to the exact harmonics along one chosen sequence."""
    from integrals import affine
    from verify import same_value
    x=('v',var);replacements={}
    for _,z in op.expression_positions(e):
        tag,u=(z[0],z[1]) if z[0] in ('sin','cos') else (None,None)
        if tag is None:continue
        if phase==x:
            try:a,b=affine(u,var)
            except Unsupported:continue
            k=m.num(a)
            if k is None or k.denominator!=1:continue
            fixed=m.add(m.mul(a,theta),b)
        elif same_value(u,phase):
            fixed=theta
        else:continue
        replacements[z]=m.simplify((tag,fixed))
    return m.substitute(e,replacements)


def lhopital_source_proof(task,library,request):
    from scalar_proofs import approach_conditions
    from tasks import source,domain_conditions
    from verify import same_value
    fields(task,{'variable','approach','numerator','denominator','requested_output'})
    meta=task.get('source',{})
    if (task.get('requested_output')!=['check hypotheses on the original domain','explain applicability or failure']
            or meta.get('literal_requirement') not in (None,'Investigate applicability of the L’Hopital rule to the given limit.')
            or set(meta)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','page_png_sha256','literal_requirement'}):
        raise Unsupported('Only the complete source applicability question is bound')
    places={
        '0':[('0','left'),('0','right')],
        '+infinity':[('+inf','positive_infinity')],'-infinity':[('-inf','negative_infinity')],
        'infinity as printed':[('-inf','negative_infinity'),('+inf','positive_infinity')],
    }
    if task['approach'] not in places:
        raise Unsupported('The original approach directions are not fixed')
    v=task['variable'];x=('v',v);f,g=[m.parse(task[k],v) for k in ('numerator','denominator')]
    def derivative(e,role):
        child=request(role,dict(kind='ordinary_derivative_order',function=source(e),variable=v,
             orders=[1],requested_output=['derivatives']))
        return freeze(child['value']['derivatives'][0])
    df,dg=derivative(f,'differentiate original numerator'),derivative(g,'differentiate original denominator')
    guards=[*domain_conditions(f,True),*domain_conditions(g,True),('nonzero',g)]
    def check_scope(point,side,specialize=lambda e:e):
        supported=[]
        ctx=m.context(dict(variable=v))
        for relation,original in guards:
            e=specialize(original)
            probe={'nonzero':('div',ONE,e),'positive':('ln',e),'nonnegative':('sqrt',e)}[relation]
            try:
                approach_conditions(probe,v,point,side,ctx)
                supported.append(dict(relation=relation,specialized=e))
            except Unsupported:
                series,side_ctx,_=local_coefficients(e,v,point,side,4,library)
                sign=op.near_sign(series,side_ctx)
                if not (sign==1 or sign==-1 and relation=='nonzero' or sign==0 and relation=='nonnegative'):
                    raise Unsupported('A smoothness or original denominator guard is unproved')
                supported.append(dict(relation=relation,specialized=e,series=series))
        return supported
    halves=(ZERO,m.div(m.PI,q(2)),m.PI,m.mul(q(3,2),m.PI));rows=[]
    for point,side in places[task['approach']]:
        ctx=m.context(dict(variable=v))
        if point!='0':
            zero=None
            for theta in halves:
                reduced=phase_specialization(dg,v,x,theta)
                if not same_value(reduced,ZERO):continue
                try:
                    verified=check_scope(point,side,lambda e:phase_specialization(e,v,x,theta))
                except Unsupported:continue
                zero=dict(phase=theta,sequence='theta+2*pi*k with k tending to the corresponding infinity',
                          original_ratio_guards=verified,specialized_derivative=reduced)
                break
            if zero is not None:
                rows.append(dict(side=side,applicable=False,failed_hypothesis='denominator_derivative_nonzero_on_a_full_tail',
                                 countersequence=zero))
                continue
        else:
            hits=[]
            # Invert any nonzero reciprocal phase before comparing the derivative traces.
            phases={z[1] for _,z in op.expression_positions(df) if z[0] in ('sin','cos')}
            for phase in sorted(phases):
                try:p,d=poly.rf(phase,v)
                except (poly.Undefined,poly.NotRational):continue
                if len(p)!=1 or not p[0] or len(d)!=2 or d[0]:continue
                rate=q(p[0]/d[1]);traces=[]
                for theta in halves:
                    projected=[phase_specialization(e,v,phase,theta) for e in (df,dg)]
                    try:
                        scope=check_scope(point,side,lambda e:phase_specialization(e,v,phase,theta))
                        witness,value=stable_germ_at(('div',*projected),v,point,side,library)
                    except Unsupported:continue
                    if isinstance(value,dict):continue
                    traces.append(dict(phase=theta,sequence=(rate,'divide by theta+2*pi*k with the sign of x on this side'),
                                       value=value,proof=witness,source_scope=scope))
                if traces and any(not same_value(r['value'],traces[0]['value']) for r in traces[1:]):
                    hits=[traces[0],next(r for r in traces[1:] if not same_value(r['value'],traces[0]['value']))]
                    break
            if hits:
                rows.append(dict(side=side,applicable=False,failed_hypothesis='derivative_quotient_has_no_limit',
                                 distinct_derivative_subsequences=hits))
                continue
        plans=[]
        for role,e in [('numerator',f),('denominator',g),('denominator_inverse',('div',ONE,g)),
                       ('derivative_denominator_inverse',('div',ONE,dg)),('derivative_quotient',('div',df,dg))]:
            proof,value=stable_germ_at(e,v,point,side,library)
            if isinstance(value,dict):raise Unsupported('The original quotient or its derivative has no full approach')
            plans.append(dict(role=role,proof=proof,value=value))
        a,b=[r['value'] for r in plans[:2]]
        same_form=a==b==ZERO or a in ('-inf','+inf') and b in ('-inf','+inf')
        if not same_form:
            rows.append(dict(side=side,applicable=False,failed_hypothesis='not_an_indeterminate_ratio',
                             numerator_limit=a,denominator_limit=b))
        else:
            scope=check_scope(point,side)
            rows.append(dict(side=side,applicable=True,form='0/0' if a==ZERO else 'infinite/infinite',
                             derivative_ratio_limit=plans[-1]['value'],proofs=plans,source_scope=scope))
    return fact('lhopital_source_hypotheses',dict(sides=rows,applicable=all(r['applicable'] for r in rows)),
        'Сначала получаем производные именно напечатанных функций. Для каждого подхода проверяем исходный знаменатель, нули его производной на полном хвосте и предел производного частного. Одного доказанного нарушения достаточно, чтобы обычное правило на этой стороне было неприменимо.',
        numerator=f,denominator=g,numerator_derivative=df,denominator_derivative=dg)


def source_limit_proof(task,library,request):
    if not library.data.get('source_asymptotic_proofs'):
        raise Unsupported('The source asymptotic proof methods are not enabled')
    kind=task.get('kind',task.get('task_type'))
    from scalar_families import family_route,family_goal
    if family_route(task,kind) and kind not in KINDS:return family_goal(task,library,request)
    if kind in ('general_polynomial_growth_proof','general_rational_degree_proof',
                'possible_rational_limit_values','general_polynomial_root_proof'):
        return polynomial_family(task,kind)
    if kind=='parametric_right_limit':return nested_radical_right(task)
    if kind=='quadratic_root_asymptotic_analysis':return quadratic_root_family(task)
    if kind in ('asymptotic_coefficient_identification','two_direction_asymptotic_coefficient_identification',
                'asymptote_criterion_proof'):
        return asymptotic_line_fitting(task,kind,library)
    if kind in ('mathematical_question','find_curve_asymptote'):
        return curve_asymptotes(task,kind,library)
    if kind in ('limit',None,'all_infinite_directions_taylor_limit'):
        return finite_source_limit(task,library,kind)
    if kind=='finite_expansion':return source_expansion(task,library)
    if kind in ('fit_asymptotic_coefficients','fit_asymptotic_coefficients_and_apply_to_geometry'):
        return fit_coefficients(task,kind,library)
    if kind in ('geometric_limit_from_tangent_angle','prove_limit_under_geometric_bound',
                'circular_segment_asymptotic','geometric_asymptotic_error'):
        return geometry_germ(task,kind,library)
    if kind in ('prove_second_derivative_symmetric_difference_formula','classify_differentiability_at_point',
                'quantified_taylor_remainder','limit_under_asymptotic_hypothesis','derivative_uniform_bound'):
        return abstract_taylor_limits(task,kind,library)
    if kind in ('uniform_approximation_error','approximation_validity_interval','prove_taylor_remainder_inequality'):
        return approximation_errors(task,kind,library)
    if kind=='lhopital_applicability':return lhopital_source_proof(task,library,request)
    if kind=='integer_parameter_point_and_sides':return integer_sine_trace(task)
    if kind in ('composition_limit_counterexample','growth_theorem_source_review','polynomial_increment_growth_theorem',
                'uniform_array_equivalence_sum_theorem'):
        return logical_limit_example(task,kind)
    if kind in ('reciprocal_newton_iteration_proof','square_root_newton_iteration_proof',
                'kepler_fixed_point_existence_uniqueness'):
        return contraction_iteration(task,kind)
    raise Unsupported('No checked transition for this complete source limit obligation')


def positive_root_scope(task):
    """Read a difference of positive roots with an integer shift in their indices."""
    name=task['variable']
    v=re.escape(name)
    match=re.fullmatch(r'([A-Za-z_]\w*)(?:\^(\d+))?\*\(root_\1\('+v+r'\)-root_\((?:\1\+(\d+)|(\d+)\+\1)\)\('+v+r'\)\)',
                       task['expression'])
    if (match and int(match[3] or match[4])>0 and task.get('parameters')==[match[1]]
            and task.get('stated_conditions')==[name+'>0']
            and task['approach']=={'point':'infinity','side':'both','mode':'magnitude_infinity'}):
        return match[1],int(match[3] or match[4]),int(match[2] or 1)


def structural_power_limit(task):
    """Compare fixed powers and extract divided differences before Taylor search."""
    from integrals import affine
    from tasks import domain_conditions,source
    from verify import same_value
    v=task['variable'];params=task.get('parameters',[]);facts=task.get('stated_conditions',[])
    approach=task['approach'];point=approach['point'];x=('v',v);text=task['expression']
    def result(method,value,*argument,**evidence):
        return dict(theorem='method.'+method,argument=argument,**evidence),value
    roots=positive_root_scope(task)
    if roots is not None:
        index,gap,order=roots
        return result('power_divided_differences','+inf',
            'Индекс корня — положительное целое число, а исходная область допускает только положительное направление бесконечности.',
            'Выносим большую степень x^(1/n). Отношение меньшей к большей имеет показатель −d/(n(n+d)), где d — положительный сдвиг индекса.',
            'Фиксированный положительный множитель не меняет расходимости к положительной бесконечности.',
            index=index,gap=gap,order=order,index_domain='positive integers',side='positive_infinity')

    if 'log(' in text or 'ln(' in text:
        plain=m.parse(re.sub(r'\blog\(', 'ln(',text),v,params)
        if plain[0]!='div' or not same_value(plain[2],m.power(x,2)) or point!='0':
            raise Unsupported('Only a central second logarithmic quotient is admitted')
        others=[('s',p) for p in params]
        if len(others)!=1 or facts!=[params[0]+'>0']:raise Unsupported('The center must be the declared positive parameter')
        a=others[0]
        if not same_value(plain[1],m.add(m.add(('ln',m.add(a,x)),('ln',m.add(a,m.neg(x)))),m.mul(q(-2),('ln',a)))):
            # Compare the exact logarithmic arguments rather than folding domain constraints.
            expected=m.add(m.add(('ln',m.add(a,x)),('ln',m.add(a,m.neg(x)))),m.mul(q(-2),('ln',a)))
            def normalize(e):
                if e[0]=='ln':return ('ln',m.simplify(e[1]))
                if e[0] in ('add','mul'):return (e[0],normalize(e[1]),normalize(e[2]))
                return e
            if not same_value(normalize(plain[1]),expected):
                raise Unsupported('The central logarithmic arguments do not match')
        value=m.neg(m.div(ONE,m.power(a,2)))
        if 'log(' in text:
            value={'natural_logarithm':value,'arbitrary_fixed_logarithm_base':'−1/(ln(B)·'+source(a)+'²), B>0, B≠1'}
        return result('power_divided_differences',value,
            'В малой окрестности оба аргумента логарифма положительны. Объединяем логарифмы в ln(1−h²/a²).',
            'Отношение ln(1+u)/u стремится к единице. Возвращаем исходный квадрат шага.',
            notation='log convention carried symbolically when the base is unstated',
            source_domain=domain_conditions(plain))

    if '^' not in text:raise Unsupported('No source power comparison is applicable')
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=facts))
    raw=m.parse(text,v,params)
    def constant(e):return m.constant_defined(e,ctx) and not m.variable_in(e,v)
    def positive(e):return constant(e) and m.sign(e,ctx)==1
    def difference(expr):
        if expr[0]=='add' and expr[2][:2]==('mul',q(-1)):
            return expr[1],expr[2][2]
        raise Unsupported('A signed difference is required')

    if point=='+inf':
        A,B=difference(raw)
        if A[0]!='rpow' or B[0]!='rpow':raise Unsupported('Two varying powers are required')
        U,P=A[1:];V,Q=B[1:]
        r,u=affine(U,v);s,w=affine(V,v)
        if r!=ONE or s!=ONE or not constant(u) or not constant(w):
            raise Unsupported('Both varying bases must be unit-slope positive tails')
        c=m.simplify(m.mul(m.add(P,q(-1)),V))
        if not constant(c) or not same_value(m.add(Q,q(-1)),m.div(c,U)) or any(
                g[0] not in ('positive','nonzero') or not any(same_value(g[1],z) for z in (U,V)) for g in domain_conditions(raw)):
            raise Unsupported('The reciprocal corrections must use the crossed affine bases')
        return result('power_divided_differences',m.add(u,m.neg(w)),
            'Выделяем из двух степеней их аффинные основания. Оставшиеся показатели экспонент равны c ln(U)/V и c ln(V)/U и стремятся к нулю.',
            'Разность показателей оцениваем через (U−V) ln(V)/(UV) и (ln U−ln V)/V. При фиксированном сдвиге это O(log x/x²).',
            'Умножение разности экспонент на одно основание всё ещё даёт величину, стремящуюся к нулю. Остаётся разность аффинных оснований.',
            bases=(U,V),scale=c)

    if point=='infinity' and approach.get('mode')=='magnitude_infinity' and raw[0]=='rpow':
        base,exponent=raw[1:]
        slope,offset=affine(base,v)
        a=slope[2] if slope[0]=='div' else ONE
        numerator=slope[1] if slope[0]=='div' else slope
        if not (constant(exponent) and exponent[0]=='s' and constant(a)
                and constant(numerator) and m.nonzero(numerator,ctx)):
            raise Unsupported('A fixed exponent and a generically nonzero affine slope are required')
        active={**ctx,'nonzero_expressions':[*ctx.get('nonzero_expressions',[]),a]}
        if (not m.constant_defined(offset,active)
                or any(g[0]!='nonzero' or not m.constant_defined(g[1],active)
                       or not m.nonzero(g[1],active) for g in domain_conditions(base))):
            raise Unsupported('All original affine denominator restrictions must follow from the slope condition')
        p=source(exponent);den=source(a)
        cases=[
            dict(condition=p+'<0',value=ZERO),
            dict(condition=p+'=0',value=ONE),
            dict(condition=p+'>0',positive_base_convention='+inf',
                 odd_reduced_denominator_even_numerator='+inf',
                 odd_reduced_denominator_odd_numerator='DOES_NOT_EXIST',
                 other_exponents='+inf on the positive-base tail only')]
        if a!=ONE:
            if not any(g[0]=='nonzero' and same_value(g[1],a) for g in domain_conditions(base)):
                raise Unsupported('The exceptional slope branch must come from an original denominator')
            cases.insert(0,dict(condition=den+'=0',status='DOMAIN_ERROR'))
        return result('power_divided_differences',dict(fixed_denominator=den,cases=cases),
            'Ненулевой аффинный наклон даёт рост модуля основания в обоих направлениях. Положительное основание лежит на направлении знака наклона.',
            'Отрицательная степень стремится к нулю, нулевая равна единице. При положительной степени положительное основание даёт +∞.',
            'Если расширить вещественное возведение в степень на отрицательные основания, для несократимой рациональной степени с нечётным знаменателем знак второй ветви задаёт чётность числителя. Противоположные бесконечности исключают общий предел.',
            slope=slope,original_domain=domain_conditions(raw))

    if point in ('infinity','-inf') or raw[0]!='div':raise Unsupported('A finite original power quotient is required')
    a=m.parse(point,None,params)
    if not positive(a):raise Unsupported('The original approach point must be strictly positive')
    top,den=raw[1:]
    powers=den[1] if den[0]=='pow' and type(den[2]) is int and den[2]>0 else den
    f,g=difference(powers)
    if f[0]=='rpow' and g[0]=='rpow':
        if f[1]==x and g[1]==a and f[2]==g[2] and f[2][0]=='s':
            A,B=difference(top);beta=f[2]
            if den!=powers or A[0]!='rpow' or B[0]!='rpow' or A[1]!=x or B[1]!=a or A[2]!=B[2] or not constant(A[2]):
                raise Unsupported('Both differences must vanish at the same positive point')
            alpha=A[2]
            value=m.mul(m.div(alpha,beta),('rpow',a,m.add(alpha,m.neg(beta))))
            return result('power_divided_differences',dict(cases=[dict(condition=source(beta)+'!=0',value=value),
                          dict(condition=source(beta)+'=0',status='DOMAIN_ERROR')]),
                'При нулевой степени знаменатель тождественно нулевой. При ненулевой степени он строго монотонен на положительной окрестности.',
                'Делим обе разности на один шаг. Их пределы — производные степенных функций с фиксированными показателями. Делим только на ненулевую производную.',
                approach=a,exponents=(alpha,beta),nonzero_on_defined_branch=beta)
        if f[2]==g[2]==x and f[1]!=g[1] and all(map(positive,(f[1],g[1]))):
            A,B=difference(top)
            if A[0]!='rpow' or B[0]!='rpow' or A[1]!=f[1] or B[1]!=g[1] or A[2]!=B[2] or domain_conditions(A[2]):
                raise Unsupported('The numerator must use the same two positive bases and a continuous common exponent')
            c,d=f[1],g[1]
            value=m.substitute(raw,{x:a})
            return result('power_divided_differences',dict(cases=[dict(condition=source(c)+'!='+source(d),value=value),
                          dict(condition=source(c)+'='+source(d),status='DOMAIN_ERROR')]),
                'На положительном предельном показателе возведение положительных оснований в степень строго монотонно по основанию.',
                'На ветви разных оснований знаменатель отделён от нуля и применима непрерывность. На ветви равных он тождественно нулевой.',
                approach=a,bases=(c,d),nonzero_on_defined_branch=m.substitute(powers,{x:a}))
        if den==powers and f==('rpow',a,x) and g==('rpow',x,a):
            A,B=difference(top)
            if A!=('rpow',a,f) or B!=('rpow',a,g):raise Unsupported('The same outer exponential must be applied to both divided-difference arguments')
            center=('rpow',a,a)
            return result('power_divided_differences',m.mul(('rpow',a,center),('ln',a)),
                'На положительной окрестности равенство внутренних степеней эквивалентно ln(x)/x=ln(a)/a.',
                'Производная ln(x)/x имеет единственный нуль e и меняет там знак. Поэтому даже в критической точке равенство не повторяется в достаточно малой проколотой окрестности.',
                'Оба внутренних аргумента стремятся к одному значению. Теорема о среднем превращает исходное частное в производную внешней экспоненты в промежуточной точке.',
                common_argument=center,nonvanishing_divisor='isolated level of ln(x)/x')
    raise Unsupported('The source power relation requires another intermediate goal')
