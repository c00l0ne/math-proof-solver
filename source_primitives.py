"""Exact algebraic changes for elementary indefinite integrals."""
from fractions import Fraction
import re

import expressions as m
import polynomial as poly
from model import ONE, ZERO, Unsupported, q


TABLE_METHODS={'table_and_rules','elementary_table_and_algebra','elementary_table_and_affine_change',
               'appropriate_integrand_transformation','appropriate_substitution'}
CHARTS=('signed_laurent_chart','positive_exponential_chart','reciprocal_quartic_chart','inverse_function_chart',
        'power_weight_chart','homogeneous_trig_quadratic','binomial_root_chart','circular_branch_chart',
        'paired_circle_chart','constant_radical_difference','positive_exponential_radical','reciprocal_quartic_radical',
        'hyperbolic_logarithm_chart','positive_exponential_pullback','circular_cut_pullback',
        'common_symbolic_power','signed_integer_affine_power','odd_root_rational_coordinate','positive_affine_inverse_chart','regular_harmonic_root','hyperbolic_quadratic_pullback',
        'centered_quadratic_radical','quadratic_radical_square_factor','homogeneous_tangent_ratio',
        'harmonic_product_derivative','reciprocal_shifted_exponential','positive_binomial_projective',
        'diagonal_projective_quadratics','odd_binomial_square_coordinate','shifted_symbolic_trig_ratio',
        'reciprocal_inverse_parts','quadratic_weight_coordinate','inverse_parts_weight_span',
        'circular_log_parts','hyperbolic_log_parts','affine_log_ratio_parts')


class EmptyBranch(ValueError):
    """An original domain guard fails at every point of this chart."""


def require(condition, reason):
    if not condition:raise Unsupported(reason)


def chart_options(task):
    method=task.get('method_requirement','table_and_rules');text=task.get('integrand')
    if not isinstance(text,str):
        return ()
    parameters=task.get('parameters')
    log_ratio=('affine_log_ratio_parts',) if method in TABLE_METHODS|{'integration_by_parts'} and 'ln(abs(' in text and '/' in text else ()
    if method=='specified_fractional_linear_substitution':return ('diagonal_projective_quadratics',)
    projective=('positive_binomial_projective',) if (
        method in TABLE_METHODS|{'rationalizing_substitution'} and '/' in text and re.search(r'\^\(1/(?:2|4|6|8|10|12)\)',text)
    ) else ()
    if (method in TABLE_METHODS and task.get('stated_domain') and 'sqrt(' in text
            and any(w+'(' in text for w in ('sin','cos'))):
        return ('regular_harmonic_root',)
    if method in TABLE_METHODS and parameters and '^' in text:
        trig_ratio=('shifted_symbolic_trig_ratio',) if ('/' in text and 'cos(' in text and 'sin(' in text) else ()
        if task.get('stated_conditions'):return (*projective,*trig_ratio,'signed_integer_affine_power')
        return (*projective,*trig_ratio,*log_ratio,'common_symbolic_power')
    if parameters or task.get('stated_conditions'):
        return (*projective,*log_ratio)
    odd='cbrt(' in text or task.get('source_root_conventions')
    options=['odd_root_rational_coordinate'] if odd and method in TABLE_METHODS|{'rationalizing_substitution'} else []
    centered=('centered_quadratic_radical',) if (
        method in TABLE_METHODS|{'quadratic_canonical_form','partial_fractions_of_rational_factor'} and 'sqrt(' in text and '/' in text) else ()
    if centered and method in TABLE_METHODS: centered+=('diagonal_projective_quadratics',)
    if method not in TABLE_METHODS|{'integration_by_parts','quadratic_canonical_form'}:
        return (*options,*centered,*projective)
    if method in TABLE_METHODS and 'sqrt(' in text:
        if text.lstrip().startswith('sqrt('):options.append('quadratic_radical_square_factor')
        if 'sin(' in text and 'cos(' in text:options.append('regular_harmonic_root')
        if 'tanh(' in text:options.append('hyperbolic_quadratic_pullback')
        if 'ln(' in text:options.append('quadratic_weight_coordinate')
    if method in TABLE_METHODS and re.search(r'\b(?:sqrt|cbrt)\(|\^\(+\s*[+-]?\d+/\d+\)|/\([^()]+\)\^(?:[2-9]\d|\d{3,})(?!\d)',text):
        options.extend(('signed_laurent_chart','power_weight_chart','binomial_root_chart'))
    if method in TABLE_METHODS and re.search(r'\bexp\(|\b\d+\s*\^\s*(?:[A-Za-z]|\([A-Za-z])',text):
        options.append('positive_exponential_chart')
        if 'sqrt(' in text:options.append('positive_exponential_radical')
        if 'exp(' in text and re.search(r'\b(?:sqrt|asin|acos|atan|acot|ln)\(',text):options.append('positive_exponential_pullback')
        if text.count('exp(')>=2 and '/' in text and '^2' in text:options.append('reciprocal_shifted_exponential')
    if method in TABLE_METHODS and '/' in text and '^4' in text:
        options.append('reciprocal_quartic_chart')
        if 'sqrt(' in text:options.append('reciprocal_quartic_radical')
    if 'sqrt(' in text and any(g+'(' in text for g in ('asin','acos','atan','ln')):
        options.append('positive_affine_inverse_chart')
    if re.search(r'\b(?:asin|acos|atan)\(|(?:sin|cos)\(ln\(',text):options.append('inverse_function_chart')
    if '/' in text and re.search(r'\b(?:asin|acos|atan)\(',text):
        options.append('inverse_parts_weight_span')
    if 'ln(' in text and 'sqrt(' in text and '/' in text:
        options.extend(('circular_log_parts','hyperbolic_log_parts'))
    options.extend(log_ratio)
    if 'ln(' in text and 'sqrt(' in text:options.append('hyperbolic_logarithm_chart')
    if re.search(r'\b(?:asin|acos)\(',text):
        options.extend(('circular_branch_chart','circular_cut_pullback'))
        if '/' in text:options.append('reciprocal_inverse_parts')
    if method in TABLE_METHODS and text.lstrip().startswith('cbrt('):options.append('odd_binomial_square_coordinate')
    if method in TABLE_METHODS and text.count('sqrt(')>=2:options.extend(('paired_circle_chart','constant_radical_difference'))
    if method in TABLE_METHODS|{'quadratic_canonical_form'} and '/' in text and 'sin(' in text and 'cos(' in text:
        options.append('homogeneous_trig_quadratic')
        if method in TABLE_METHODS:
            options.extend(('homogeneous_tangent_ratio','harmonic_product_derivative'))
    return (*options,*centered,*projective)


def fixed_source(task,methods=TABLE_METHODS):
    from integrals import input_data
    from verify import same_value
    conventions=task.get('source_root_conventions')
    compiled={k:v for k,v in task.items() if k!='source_root_conventions'}
    x,raw,ctx,method=input_data(compiled,methods)
    require(not ctx['parameters'] and not task.get('stated_conditions'),'A fixed scalar coordinate and original natural domain are required')
    if conventions is not None:
        require(isinstance(conventions,list) and len(conventions)==1,'One explicit original root convention is required')
        c=conventions[0]
        if set(c)=={'index','radicand','meaning'}:
            n=c['index'];require(type(n) is int and n>=3 and n%2==1,'The original root must have a fixed odd index')
            require(re.fullmatch(r'real \w+ root of the complete radicand, including zero before the outer division',c['meaning']),
                    'The original meaning differs from the fixed odd real root')
            require(raw[0]=='div' and raw[1][0]=='rpow' and m.num(m.simplify(raw[1][2]))==Fraction(1,n) and
                    same_value(raw[1][1],m.parse(c['radicand'],x[1])) and same_value(raw[1][1],m.power(raw[2],2)),
                    'The source square under the real odd root must vanish only at excluded poles')
        else:
            require(set(c)=={'subexpression','semantics','forbidden_reinterpretation'}
                    and c['semantics']=='real odd root power: for every real u, u^(2/3) means cbrt(u)^2'
                    and c['forbidden_reinterpretation']=='positive-base-only real power on negative u',
                    'An unresolved source convention would change the real domain')
            term=m.parse(c['subexpression'],x[1])
            require(term[0]=='rpow' and m.num(m.simplify(term[2]))==Fraction(2,3) and m.contains(raw,term),
                    'The declared source cube root must match the original subexpression')
            raw=m.substitute(raw,{term:('pow',('cbrt',term[1]),2)})
    return x,raw,ctx,method


def add(left,right):
    result=dict(left)
    for degree,coef in right.items():
        value=m.add(result.get(degree,ZERO),coef)
        if value==ZERO:result.pop(degree,None)
        else:result[degree]=value
    return result


def mul(left,right,combine=lambda p,q:p+q):
    require(len(left)*len(right)<=192,'The finite expansion would exceed the supported sparse product')
    result={}
    for power,coef in left.items():
        result=add(result,{combine(power,e):m.mul(coef,c) for e,c in right.items()})
    return result


def scaling(data,power,coef):
    return {power+e:m.mul(coef,c) for e,c in data.items()} if coef!=ZERO else {}


def known_sign(data,ctx):
    if not data:return 0
    signs={m.sign(coef,ctx) for coef in data.values()}
    return signs.pop() if len(signs)==1 else None


def square_root(data,ctx):
    """Recover an exact finite square with one sign on the whole positive chart."""
    p=max(data);coef=data[p];root=m.simplify(('sqrt',coef))
    require(m.sign(coef,ctx)==1 and m.mul(root,root)==coef,'The highest square coefficient is not resolved')
    answer={p/2:root}
    while True:
        diff=add(data,scaling(mul(answer,answer),Fraction(0),q(-1)))
        if not diff:break
        degree=max(diff)-p/2
        require(len(answer)<12 and degree<min(answer) and degree>=min(data)/2,'No finite exact square with the original coefficients')
        answer[degree]=m.div(diff[max(diff)],m.mul(q(2),root))
    sign=known_sign(answer,ctx)
    require(sign in (-1,1),'The extracted square may change sign on this real component')
    return scaling(answer,Fraction(0),q(sign))


def power(data, exponent, ctx, convention):
    if not data:
        if exponent<=0 or convention=='rpow':raise EmptyBranch('zero base in a source power requiring a nonzero base')
        return {}
    if exponent.denominator==1 and exponent>0:
        degree=int(exponent);result={Fraction(0):ONE};base=data
        require(degree<=m.MAX_INTEGER_POWER,'The source integer exponent is beyond the supported expansion')
        while degree:
            if degree%2:result=mul(result,base)
            degree//=2
            if degree:base=mul(base,base)
        return result
    if convention=='sqrt' and len(data)>1:
        if known_sign(data,ctx)==-1:raise EmptyBranch('negative radicand on the whole chart')
        return square_root(data,ctx)
    require(len(data)==1,'A nonmonomial base needs a further real coordinate')
    (p,c),=data.items();sign=m.sign(c,ctx)
    require(sign in (-1,1),'The sign of the original power base is undetermined')
    if sign<0 and (convention=='sqrt' or exponent.denominator%2==0):
        raise EmptyBranch('negative base of an even real root')
    require(sign>0 or convention in ('cbrt','integer'),
            'A negative noninteger source power requires an explicit real-root convention')
    n=exponent.numerator;d=exponent.denominator
    if d==1:value=m.power(c,n)
    else:
        r=('sqrt',c) if d==2 else ('cbrt',c) if d==3 else ('rpow',c,q(1,d))
        value=m.power(m.simplify(r),n)
    return {p*exponent:value}


def quotient(numerator,denominator,ctx):
    if not denominator:raise EmptyBranch('an original divisor vanishes identically')
    if len(denominator)==1:
        (p,c),=denominator.items()
        require(m.sign(c,ctx) in (-1,1),'The original divisor coefficient is not proved nonzero')
        return scaling(numerator,-p,m.div(ONE,c))
    require(known_sign(denominator,ctx) in (-1,1),'The original multi-term divisor may vanish')
    require(all(d.denominator==1 and d>=0 and m.num(c) is not None for a in (numerator,denominator) for d,c in a.items()),
            'An exact division of ordinary Laurent chart polynomials is required')
    def dense(data):
        return tuple(m.num(data.get(Fraction(k),ZERO)) for k in range(1+int(max(data,default=0))))
    a,b=poly.pdiv(dense(numerator),dense(denominator))
    require(not any(b),'A nonzero rational remainder needs a separate primitive')
    return {Fraction(p):q(c) for p,c in enumerate(a) if c}


def expression_coefficients(expr, x, coordinate, ctx, exp_coordinate=False):
    from integrals import affine
    if expr==x:
        require(not exp_coordinate,'An explicit x factor is not a power of the new exponential coordinate')
        return coordinate
    if not m.contains(expr,x) and m.constant_defined(expr,ctx):
        c=m.simplify(expr)
        return {} if c==ZERO else {Fraction(0):c}
    op=expr[0]
    if op in ('add','mul','div'):
        a,b=(expression_coefficients(z,x,coordinate,ctx,exp_coordinate) for z in expr[1:])
        if op=='div':return quotient(a,b,ctx)
        return (add if op=='add' else mul)(a,b)
    if op in ('sqrt','cbrt','pow','rpow'):
        data=expression_coefficients(expr[1],x,coordinate,ctx,exp_coordinate)
        if op=='pow':return power(data,Fraction(expr[2]),ctx,'integer')
        if op in ('sqrt','cbrt'):
            return power(data,Fraction(1,2 if op=='sqrt' else 3),ctx,op)
        require(m.constant_defined(expr[2],ctx),'The original exponent is not a fixed real value')
        r=m.num(m.simplify(expr[2]))
        require(r is not None and r.denominator>1,'A fixed noninteger rational exponent is required')
        return power(data,r,ctx,op)
    if exp_coordinate and op=='exp':
        from tasks import domain_conditions,known_guard
        a,b=affine(expr[1],x[1]);p=m.num(a)
        require(p is not None and m.constant_defined(b,ctx) and
                all(known_guard(g,ctx) for g in domain_conditions(expr[1])),
                'The exponential phase is not a globally defined affine scale')
        return {p:m.simplify(('exp',b))}
    raise Unsupported('No exact Laurent expansion of the original operator '+op)


def integrate_terms(data,coordinate,scale):
    result=ZERO;terms=[]
    for d,c in sorted(data.items()):
        c=m.mul(c,scale);k=d+1
        if not k:value=('mul',c,('ln',coordinate))
        elif k.denominator==1:value=('mul',m.div(c,q(k)),('pow',coordinate,int(k)))
        else:value=('mul',m.div(c,q(k)),('rpow',coordinate,q(k)))
        terms.append((q(d),c,value))
        result=value if result==ZERO else ('add',result,value)
    return result,terms


def signed_profile(raw,x,ctx,center):
    from integrals import family
    choices=[];excluded=[];pieces=[]
    for sign in (-1,1):
        coordinate={Fraction(1):q(sign)}
        if center:coordinate[Fraction(0)]=q(center)
        try:data=expression_coefficients(raw,x,coordinate,ctx)
        except EmptyBranch as exc:
            excluded.append(dict(sign=sign,reason=str(exc)));continue
        local=m.mul(q(sign),m.add(x,q(-center)))
        primitive,terms=integrate_terms(data,local,q(sign))
        choices.append(dict(sign=sign,coordinate=local,exact_integrated_terms=terms))
        pieces.append(((None,q(center)) if sign<0 else (q(center),None),primitive))
    require(pieces,'Every original interval is absent')
    try:
        at_center=expression_coefficients(raw,x,{} if not center else {Fraction(0):q(center)},ctx)
        require(set(at_center)<={Fraction(0)},'Original center value is not a real constant')
        require(all(m.num(t[0])>-1 for row in choices for t in row['exact_integrated_terms']),
                'A regular included center needs finite matching traces')
        center_witness=dict(member=True,integrand=at_center.get(Fraction(0),ZERO),primitive=ZERO,
                            proof='Both primitives have zero trace. The real source integrand is continuous at the included point.')
    except EmptyBranch as exc:center_witness=dict(member=False,reason=str(exc))
    region=dict(center=q(center),chart_sides=[row['sign'] for row in choices],center_in_original_domain=center_witness['member'])
    term=pieces[0][1] if len(pieces)==1 else ('piecewise_primitive',tuple(pieces))
    plan=dict(theorem='method.normalize_real_power_products_on_charts',chart='signed_laurent_chart',
              source_cover=region,coordinates=choices,excluded=excluded,center=center_witness,
              argument=['Из исходной формулы выделяем общий аффинный центр и проверяем обе стороны. На положительной координате коэффициенты конечного степенного разложения точны.',
                        'Интегрируем каждый член, включая логарифмический. Учитываем знак дифференциала, исходные выколы и общий след в каждой включённой точке склейки.'])
    return plan,family(raw,term,region=region)


def signed_laurent_chart(task):
    from integrals import affine,learned_nodes
    x,raw,ctx,method=fixed_source(task);centers=[Fraction(0)]
    for u in learned_nodes(raw):
        if not isinstance(u,tuple) or not m.contains(u,x):continue
        try:a,b=map(m.num,affine(u,x[1]))
        except Unsupported:continue
        if a and b is not None and -b/a not in centers:centers.append(-b/a)
    failures=[]
    for c in centers[:12]:
        try:return signed_profile(raw,x,ctx,c)
        except (Unsupported,EmptyBranch,ArithmeticError,TypeError,ValueError) as exc:failures.append(str(exc))
    raise Unsupported('No full real Laurent chart: '+(failures[-1] if failures else 'no affine center'))


def positive_exponential_chart(task):
    from integrals import family,learned_nodes
    x,raw,ctx,_=fixed_source(task)
    if not any(isinstance(z,tuple) and z[0]=='exp' and m.contains(z,x) for z in learned_nodes(raw)):
        data=rational_base_exponential(raw,x,ctx)
        ans=ZERO;terms=[]
        for r,c in sorted(data.items()):
            exponent=('rpow',q(r),x)
            value=m.mul(c,x) if r==1 else m.div(m.mul(c,exponent),('ln',q(r)))
            terms.append((q(r),c,value));ans=m.add(ans,value)
        return dict(theorem='method.collect_positive_exponential_rates',chart='positive_exponential_chart',
                    rates=terms,argument=['Выделяем постоянные сдвиги каждого показателя. Произведения и частные положительных оснований объединяем по точным правилам степеней.',
                    'Собираем одинаковые основания. Производная каждого слагаемого добавляет ненулевой логарифм основания, а для основания единица получаем постоянный вклад.']), \
                    family(raw,ans,region='all real x')
    data=expression_coefficients(raw,x,{},ctx,True)
    t=('exp',x);kernel=scaling(data,Fraction(-1),ONE);ans,terms=integrate_terms(kernel,t,ONE)
    plan=dict(theorem='method.divide_in_positive_exponential_coordinate',chart='positive_exponential_chart',coordinate=t,
              exact_integrated_terms=terms,argument=['Вводим t=e^x>0. Каждая допустимая экспонента даёт степень t, исходный знаменатель проверяется на всей положительной полуоси.',
              'После точного алгебраического деления и dx=dt/t интегрируем конечное степенное разложение и возвращаемся к исходной координате.'])
    return plan,family(raw,ans,region='all real x; positive exponential chart')


def rational_base_exponential(e,x,ctx):
    from integrals import affine
    from tasks import domain_conditions,known_guard
    if not m.contains(e,x) and m.constant_defined(e,ctx):
        value=m.simplify(e);return {Fraction(1):value} if value!=ZERO else {}
    if e[0]=='rpow':
        a=m.num(m.simplify(e[1]));slope,shift=map(m.num,affine(e[2],x[1]))
        require(m.constant_defined(e[1],ctx) and all(known_guard(g,ctx) for g in domain_conditions(e[2])) and
                a is not None and a>0 and slope is not None and shift is not None and slope.denominator==shift.denominator==1,
                'The fixed positive base and integer affine rate are required')
        require(abs(slope)+abs(shift)<=256,'The fixed exact exponential rate is too large')
        return {a**int(slope):q(a**int(shift))}
    if e[0] in ('add','mul','div'):
        u,v=(rational_base_exponential(a,x,ctx) for a in e[1:])
        if e[0]=='add':return add(u,v)
        if e[0]=='mul':return mul(u,v,lambda a,b:a*b)
        require(len(v)==1 and m.sign(next(iter(v.values())),ctx) in (-1,1),'The original denominator is not one nonzero fixed exponential')
        (k,c),=v.items();return {p/k:m.div(z,c) for p,z in u.items()}
    if e[0]=='pow' and 1<=e[2]<=8:
        data=rational_base_exponential(e[1],x,ctx);ans={Fraction(1):ONE}
        for _ in range(e[2]):ans=mul(ans,data,lambda a,b:a*b)
        return ans
    raise Unsupported('No finite combination of fixed positive-base exponentials was identified')


def reciprocal_quartic(task):
    from integrals import family
    from tasks import domain_conditions
    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div' and not any(domain_conditions(t) for t in raw[1:]),
            'A source quotient of everywhere-defined polynomials is required before the reciprocal transformation')
    p,dp=poly.rf(raw[1],x[1]);d,dd=poly.rf(raw[2],x[1])
    require(len(dp)==len(dd)==1 and len(p)==3 and len(d)==5 and not p[1] and not d[1] and not d[3] and d[0]==d[4] and d[4],
            'The original numerator and palindromic even quartic are not a reciprocal differential')
    c=d[2]/d[4];sigma=-p[0]/p[2];k=p[2]*dd[0]/(dp[0]*d[4])
    require(sigma in (-1,1) and c>-2,'The reciprocal sign or positivity of the original quartic was not proved')
    u=m.add(x,m.div(q(sigma),x));a=c-2*sigma
    if a>0:
        r=m.simplify(('sqrt',q(a)));F=m.div(('atan',m.div(u,r)),r)
        right=m.mul(q(int(sigma),2),m.div(m.PI,r))
    elif a==0:
        F=m.neg(m.div(ONE,u));right=ZERO
    else:
        r=m.simplify(('sqrt',q(-a)))
        F=m.div(('ln',('abs',m.div(m.add(u,m.neg(r)),m.add(u,r)))),m.mul(q(2),r));right=ZERO
    pieces=(((None,ZERO),m.mul(q(k),m.add(F,right))),((ZERO,None),m.mul(q(k),m.add(F,m.neg(right)))))
    value=family(raw,('piecewise_primitive',pieces),region='all real x; both reciprocal charts joined with common value 0')
    return dict(theorem='method.reciprocal_differential_and_regular_join',chart='reciprocal_quartic_chart',
                coordinate=u,reduced_denominator=('plus_square',q(a)),scale=q(k),join=ZERO,
                argument=['После деления на x² знаменатель превращается в квадрат x±1/x плюс константу. Знак выбираем по совпадению числителя с производной новой координаты.',
                          'Канонический интеграл даёт арктангенс, логарифм или обратную величину. Проверяем обе вещественные стороны и устраняем только искусственный выкол.',
                          'Подбираем константы для общего следа 0. Производная в точке склейки равна исходному непрерывному интегранду.']),value


def inverse_function_chart(task,request):
    from integrals import family,integrate_child,kernel_symbol,learned_nodes,source
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x,raw,ctx,method=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    name=kernel_symbol(task);u=('v',name);s,c=('sin',u),('cos',u)
    atoms={z for z in learned_nodes(raw) if isinstance(z,tuple) and len(z)==2 and z[1]==x and z[0] in ('asin','acos','atan','ln')}
    require(len(atoms)==1,'A unique declared inverse or logarithmic coordinate is required')
    (chart,)=atoms;op=chart[0];x2=m.power(x,2);quadratic=m.add(ONE,x2)
    guards=[g for g in domain_conditions(raw) if not known_guard(g,ctx)]
    if op in ('asin','acos'):
        inside=m.add(ONE,m.neg(x2))
        require(all((r=='nonnegative' and same_value(g,inside)) for r,g in guards),
                'Other original cuts in the inverse circular coordinate need a separate domain proof')
        inverse,jac=(s,c) if op=='asin' else (c,m.neg(s))
        image='[-pi/2,pi/2]' if op=='asin' else '[0,pi]'
        source_region='[-1,1], with both continuous relative endpoints'
    elif op=='atan':
        require(method!='integration_by_parts','This tangent pullback does not by itself prove the assigned parts method')
        require(all(r in ('nonzero','positive') and
                    (same_value(g,quadratic) or g[0] in ('pow','rpow','sqrt') and same_value(g[1],quadratic)) for r,g in guards),
                'The arctangent pullback has an additional original cut')
        inverse,jac=m.div(s,c),m.power(c,-2)
        image='(-pi/2,pi/2)';source_region='all real x'
    else:
        require(method!='integration_by_parts' and all(r=='positive' and same_value(g,x) for r,g in guards),
                'The logarithmic coordinate needs its exact positive original domain')
        inverse=jac=('exp',u);image='all real u';source_region='x>0'
    def lower(e):
        if not isinstance(e,tuple):return e
        if e==chart:return u
        if e==x:return inverse
        if op=='atan' and e[0] in ('pow','rpow','sqrt') and same_value(e[1],quadratic):
            p=Fraction(e[2]) if e[0]=='pow' else Fraction(1,2) if e[0]=='sqrt' else m.num(m.simplify(e[2]))
            require(p is not None and (2*p).denominator==1,'Only whole powers of positive cos on the arctangent image are admitted')
            return m.power(c,-int(2*p))
        return (e[0],*(lower(a) for a in e[1:]))
    kernel=m.simplify(m.mul(lower(raw),jac))
    require(not domain_conditions(kernel) and not m.contains(kernel,x),
            'The new coordinate would leave an unproved pole or original variable')
    if method=='integration_by_parts':
        target=dict(kind='integrate',variable=name,integrand=source(kernel),method_requirement='integration_by_parts',
                    requested_output=['primitive_family'])
        F=request('assigned integration by parts after the verified change of variable',target)['value']['representative']
    else:F=integrate_child(request,kernel,name)
    from model import freeze
    value=family(raw,m.substitute(freeze(F),{u:chart}),region=source_region)
    return dict(theorem='method.inverse_coordinate_differential_transport',chart='inverse_function_chart',coordinate=chart,
                image=image,inverse=inverse,jacobian=jac,transformed_kernel=kernel,argument=[
                    'Выделяем исходную обратную функцию или логарифм в роли координаты. Её главная ветвь определяет точный образ.',
                    'Подставляем обратную карту и её дифференциал во всю исходную плотность. Сохраняем знак косинуса на главной ветви арктангенса.',
                    'Проверяем отдельную первообразную в новой координате и переносим её обратно. Включённые края исходной области проверяются по непрерывности и относительной производной.',
                ]),value


def binomial_root_chart(task,request):
    from integrals import family,integrate_child,kernel_symbol,learned_nodes
    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div' and m.constant_defined(raw[1],ctx),
            'The original density must have a fixed real numerator')
    den=raw[2]; roots=[z for z in learned_nodes(den) if isinstance(z,tuple)
                      and z[0] in ('sqrt','cbrt','rpow') and m.contains(z,x)]
    require(len(roots)==1,'There must be one binomial radial coordinate')
    root=roots[0];signed=root[0]=='cbrt'
    exponent=Fraction(1,3) if signed else Fraction(1,2) if root[0]=='sqrt' else m.num(m.simplify(root[2]))
    require(exponent is not None and exponent.numerator==1 and exponent.denominator>1,
            'A fixed root of the binomial is required')
    n=exponent.denominator
    denominator_plain=den==root
    require(denominator_plain or den in (('mul',x,root),('mul',root,x)),
            'The original density is neither 1/R nor 1/(xR) up to scale')
    from tasks import domain_conditions
    require(not domain_conditions(root[1]),'The starting binomial has an unproved inner restriction')
    from polynomial import NotRational, Undefined
    try:p,d=poly.rf(root[1],x[1])
    except (NotRational,Undefined) as exc:raise Unsupported('The radicand must be polynomial') from exc
    require(len(d)==1 and len(p)==n+1 and p[0]==d[0] and not any(p[1:n]) and p[n]/d[0]>0
            and (signed or n%2==0),'The required binomial is 1+a*x^n with positive a and a certified real root')
    a=q(p[n]/d[0]);name=kernel_symbol(task);u=('v',name)
    if denominator_plain:
        coordinate=m.div(x,root);D=m.add(ONE,m.neg(m.mul(a,m.power(u,n))))
        image='u<rho or u>rho on the two components' if signed else '-rho<u<rho'
    else:
        require(not signed,'The reciprocal signed root needs a separate component analysis')
        coordinate=m.div(ONE,root);D=m.add(m.power(u,n),m.neg(ONE));image='0<u<1 on both original components'
    f=m.div(m.simplify(raw[1]),D);H=integrate_child(request,f,name)
    region=dict(radial_degree=n,coefficient=a,rho=('rpow',m.div(ONE,a),q(1,n)),
                original_poles=[m.neg(('rpow',m.div(ONE,a),q(1,n)))] if signed
                               else [] if denominator_plain else [ZERO],image=image)
    return dict(theorem='method.binomial_root_rational_differential',chart='binomial_root_chart',
                coordinate=coordinate,transformed_kernel=f,source_cover=region,argument=[
                    'Степень корня совпадает со степенью одночлена под корнем. Проверяем знак коэффициента и область исходного знаменателя.',
                    'Для u=x/R выполняется u′=R^(−n−1) и 1−a*u^n=1/R^n. Для u=1/R исходная плотность 1/(xR) даёт du/(u^n−1).',
                    'Рациональная первообразная переносится обратно по каждой исходной ветви. Исходные нули знаменателя исключены.']),\
           family(raw,m.substitute(H,{u:coordinate}),region=region)


def circular_branch_chart(task,request,keep_cuts=False):
    from integrals import affine,family,integrate_child,kernel_symbol,learned_nodes,source
    from model import freeze
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x,raw,ctx,method=fixed_source(task,TABLE_METHODS|({'integration_by_parts'} if keep_cuts else set()))
    atoms={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0] in ('asin','acos') and m.contains(z,x)}
    require(len(atoms)==1,'A single real principal circular inverse is required')
    (chart,)=atoms;inner=chart[1];root=inner[0]=='sqrt'
    base=inner[1] if root else inner
    a,b=affine(base,x[1]);a,b=map(m.simplify,(a,b))
    require(m.num(a) not in (None,0) and m.num(b) is not None and not domain_conditions(base),
            'The inner inverse argument must be affine or the positive root of an affine term')
    name=kernel_symbol(task);u=('v',name)
    w,dw=(('sin',u),('cos',u)) if chart[0]=='asin' else (('cos',u),m.neg(('sin',u)))
    other=('cos',u) if chart[0]=='asin' else ('sin',u)
    rad=m.add(ONE,m.neg(m.power(inner,2)));core=m.add(ONE,m.neg(base)) if root else rad
    def factors(e):
        if e[0] in ('mul','div'):
            for child in e[1:]:yield from factors(child)
        elif e[0]=='pow':yield from factors(e[1])
        else:yield e
    def guards_of(e):
        for rel,z in domain_conditions(e):
            for p in factors(z) if keep_cuts and rel=='nonzero' else (z,):
                if not known_guard((rel,p),ctx):yield rel,p
    at_boundary=True;source_cuts=[]
    for rel,e in guards_of(raw):
        if rel=='nonnegative' and (e==base and root or same_value(e,core) or same_value(e,rad)):continue
        if rel=='nonzero' and e[0] in ('sqrt','pow','rpow'):e=e[1]
        if not root and rel in ('positive','nonzero') and same_value(e,rad):at_boundary=False;continue
        if keep_cuts and rel=='nonzero' and any(same_value(e,z) for z in (x,inner,chart)):
            if e not in source_cuts:source_cuts.append(e)
            continue
        raise Unsupported('An additional original restriction in the circular branch is unproved')
    inverse=m.div(m.add(m.power(w,2) if root else w,m.neg(b)),a)
    jac=m.div(m.mul(m.mul(q(2),w),dw) if root else dw,a)
    def lower(e):
        if not isinstance(e,tuple):return e
        if e==chart:return u
        if e==inner:return w
        if e==x:return inverse
        if not root and e[0] in ('sqrt','rpow','pow') and same_value(e[1],rad):
            p=Fraction(1,2) if e[0]=='sqrt' else Fraction(e[2]) if e[0]=='pow' else m.num(m.simplify(e[2]))
            require(p is not None and (2*p).denominator==1,'Only whole powers of the fixed-sign circular coordinate are admitted')
            return m.power(other,int(2*p))
        return (e[0],*(lower(z) for z in e[1:]))
    kernel=m.simplify(m.mul(lower(raw),jac))
    pulled=[m.simplify(lower(e)) for e in source_cuts]
    for rel,e in guards_of(kernel):
        if rel=='nonzero' and any(same_value(a,e) for a in pulled):continue
        require(not at_boundary and rel=='nonzero' and (e==other or e[0]=='pow' and e[1]==other),
                'The transformed density has a pole outside the established circular guards')
    if method=='integration_by_parts':
        target=dict(kind='integrate',variable=name,integrand=source(kernel),method_requirement=method,requested_output=['primitive_family'])
        H=freeze(request('integration by parts in the original circular components',target)['value']['representative'])
    else:H=integrate_child(request,kernel,name)
    limits=('[0,pi/2]' if root else '[-pi/2,pi/2]' if chart[0]=='asin' else '[0,pi]')
    if not at_boundary:limits='('+limits[1:-1]+')'
    region=dict(inner_argument=inner,coordinate_image=limits,includes_relative_edges=at_boundary)
    if keep_cuts:region['extra_source_nonzero']=source_cuts;region['extra_image_nonzero']=pulled
    name,theorem=('circular_cut_pullback','circular_pullback_with_original_exclusions') if keep_cuts else ('circular_branch_chart','circular_inverse_branch_pullback')
    return dict(theorem='method.'+theorem,chart=name,
                coordinate=chart,inverse=inverse,jacobian=jac,transformed_kernel=kernel,source_cover=region,argument=[
                    'По области главной ветви обратной функции устанавливаем точный образ, обратную карту и знак второго тригонометрического множителя.',
                    'Переносим исходную плотность в новую координату и проверяем её отдельную первообразную. Допустимые исходные края восстанавливаем по непрерывности.']),\
           family(raw,m.substitute(H,{u:chart}),region=region)


def positive_exponential_pullback(task,request):
    from integrals import affine,common_phase_rate,family,integrate_child,kernel_symbol,learned_nodes
    from tasks import domain_conditions,known_guard
    x,raw,ctx,_=fixed_source(task)
    phases={}
    for e in learned_nodes(raw):
        if not isinstance(e,tuple) or e[0]!='exp' or not m.contains(e,x):continue
        rate,shift=affine(e[1],x[1]);r=m.num(rate)
        require(r and m.constant_defined(shift,ctx) and all(known_guard(g,ctx) for g in domain_conditions(e[1])),
                'An original phase is not affine and everywhere defined')
        phases[e]=(r,shift)
    require(phases,'A genuine exponential scale is missing')
    c=common_phase_rate(r for r,b in phases.values());v=kernel_symbol(task);t=('v',v)
    replacements={e:m.mul(m.simplify(('exp',b)),m.power(t,int(r/c))) for e,(r,b) in phases.items()}
    kernel=m.substitute(raw,replacements)
    require(not m.contains(kernel,x),'The old coordinate remains outside the exponential atoms')
    jac=m.div(ONE,m.mul(q(c),t));kernel=('mul',kernel,jac)
    H=integrate_child(request,kernel,v)
    require(H[0] not in ('piecewise_primitive','joined_periodic_primitive'),'This child needs explicit transportation of its primitive branches')
    coordinate=('exp',m.mul(q(c),x));region=dict(new_coordinate='t>0',original_guards=domain_conditions(raw),
               image_guards=domain_conditions(kernel))
    return dict(theorem='method.positive_exponential_coordinate_with_child',chart='positive_exponential_pullback',
                coordinate=coordinate,source_cover=region,transformed_kernel=kernel,jacobian=jac,argument=[
                    'Выделяем общий аффинный масштаб показателей и заменяем экспоненциальные атомы точными целыми степенями t>0.',
                    'Переносим всю исходную плотность и её условия, умножая на dt/(c t). Число t=0 не является точкой исходной области.',
                    'Решаем дочерний интеграл с его точными условиями и возвращаемся по той же положительной карте.']),family(raw,m.substitute(H,{t:coordinate}),region=region)


def rational_kernel(form,v):
    from integrals import polynomial_expression
    from polynomial import pgcd,pdiv
    p,d=poly.rf(form,v);g=pgcd(p,d)
    return m.div(polynomial_expression(pdiv(p,g)[0],v),polynomial_expression(pdiv(d,g)[0],v))


def paired_circle_chart(task,request):
    from integrals import affine,family,integrate_child,kernel_symbol
    from radical_primitives import quotient_derivative_numerator
    from integrals import polynomial_expression
    from tasks import domain_conditions
    x,raw,ctx,_=fixed_source(task)
    log=raw[0]=='ln'
    require(log or raw[0]=='div' and m.constant_defined(raw[1],ctx),'A reciprocal sum or a logarithmic density is required')
    denominator=raw[1] if log else raw[2]
    def summands(e):
        return (*summands(e[1]),*summands(e[2])) if e[0]=='add' else (e,)
    terms=summands(denominator)
    roots=[z for z in terms if z[0]=='sqrt' and m.contains(z,x)]
    require(len(roots)==2,'Two positive principal radicals from the original sum are required')
    require(not any(domain_conditions(z[1]) for z in roots),'An inner original restriction is unproved')
    constants=[z for z in terms if z not in roots]
    require(all(m.constant_defined(z,ctx) for z in constants),'The remaining terms are not fixed real scalars')
    aux=('v',kernel_symbol(task)); v=aux[1];exponential=('exp',x)
    using_exponential=any(m.contains(e,exponential) for e in roots)
    require(not log or not using_exponential,'Parts leave a logarithmic inverse of the outer coordinate')
    data=[]
    for z in roots:
        a,b=map(m.num,affine(m.substitute(z[1],{exponential:aux}) if using_exponential else z[1],v if using_exponential else x[1]))
        require(a not in (None,0) and b is not None,'The two original radicands must be affine in a shared coordinate')
        data.append((a,b,z))
    (negative,c,S),(a,b,R)=sorted(data)
    total=b+c
    require(a>0 and negative==-a and total>0 and (not using_exponential or c>0),
            'The sum of opposite affine radicands must be a positive constant on a nonempty original interval')
    rho=m.simplify(('sqrt',q(total)));scale=ZERO
    for z in constants:scale=m.add(scale,m.div(z,rho))
    k=m.num(m.simplify(scale));require(k is not None and k>=0,'The fixed summand must be a nonnegative rational multiple of the common radius')
    u=aux;u2=m.power(u,2);D=m.add(ONE,u2)
    Y=m.div(m.mul(q(2),u),D);Z=m.div(m.add(ONE,m.neg(u2)),D);G=m.add(q(k),m.add(Y,Z))
    X=m.div(m.add(m.mul(q(total),m.power(Y,2)),q(-b)),q(a))
    jac=m.div(m.mul(q(Fraction(8)*total/a),m.mul(u,m.add(ONE,m.neg(u2)))),m.power(D,3))
    coordinate=m.div(R,m.add(rho,S));left=q(-b/a);right=q(c/a)
    if log:
        p,d=poly.rf(G,v);Gprime=m.div(polynomial_expression(quotient_derivative_numerator(p,d),v),polynomial_expression(poly.pm(d,d),v))
        kernel=rational_kernel(m.mul(X,m.div(Gprime,G)),v)
        H=integrate_child(request,kernel,v)
        answer=m.add(m.mul(x,('ln',denominator)),m.neg(m.substitute(H,{u:coordinate})))
    else:
        kernel=rational_kernel(m.div(jac,m.mul(G,X) if using_exponential else G),v)
        H=integrate_child(request,kernel,v)
        answer=m.mul(m.div(m.simplify(raw[1]),rho),m.substitute(H,{u:coordinate}))
    region=dict(coordinate_base=exponential if using_exponential else x,
                allowed_interval=[left,right],positive_base_if_exponential=using_exponential,
                image='0<=u<=1 with original positive exponential restriction if applicable')
    return dict(theorem='method.opposite_radicals_via_circle_projection',chart='paired_circle_chart',
                coordinate=coordinate,normalized_root_images=(Y,Z),inverse_base=X,jacobian=jac,
                source_cover=region,transformed_kernel=kernel,argument=[
                    'Сумма двух исходных подкоренных выражений постоянна. На четверти окружности строим стереографическую координату и проверяем положительность суммы корней.',
                    'Обратная карта и её дифференциал рациональны. Если исходная переменная входит через экспоненту, сохраняем её положительность и множитель 1/s.',
                    'У логарифмической плотности применяем части. Производная логарифма нормированной рациональной суммы радикалов даёт рациональное ядро.',
                    'Проверяем рациональную первообразную. Включённые исходные края следуют из непрерывности интегранда и конечности преобразованной плотности.']),family(raw,answer,region=region)


def constant_radical_difference(task,request):
    from integrals import family,integrate_child,learned_nodes
    from tasks import domain_conditions
    from verify import same_value
    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div' and m.constant_defined(raw[1],ctx),'A fixed real numerator is required')
    D=raw[2];require(D[0]=='add','The original denominator is not a difference of two roots')
    roots={z for z in learned_nodes(D) if isinstance(z,tuple) and z[0]=='sqrt' and m.contains(z,x)}
    require(len(roots)==2,'Exactly two variable roots are required')
    R,S=sorted(roots,key=repr)
    target=m.add(R,m.neg(S))
    sign=1 if same_value(D,target) else -1 if same_value(D,m.neg(target)) else 0
    require(sign and len(domain_conditions(D))==2 and not any(domain_conditions(z[1]) for z in roots),
            'The original denominator contains an extra domain restriction')
    delta=m.simplify(m.add(R[1],m.neg(S[1])));c=m.num(delta)
    if c is None:
        p,d=poly.rf(delta,x[1]);c=p[0]/d[0] if len(p)==len(d)==1 else None
    require(c not in (None,0),'The difference of radicands must be a fixed nonzero constant')
    H=integrate_child(request,m.add(R,S),x[1])
    answer=m.mul(m.div(m.simplify(raw[1]),q(sign*c)),H)
    return dict(theorem='method.conjugate_root_differences_with_fixed_gap',chart='constant_radical_difference',
                radicands=[R[1],S[1]],gap=q(sign*c),argument=[
                    'На пересечении исходных областей оба корня определены и не могут совпасть из-за ненулевой разности подкоренных выражений.',
                    'Домножаем на сопряжённую сумму и заменяем знаменатель точной константой. Проверяем первообразную суммы корней в исходной переменной.']),family(raw,answer)


def positive_exponential_radical(task,request):
    from integrals import affine,family,integrate_child,kernel_symbol,learned_nodes
    from tasks import domain_conditions
    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='sqrt' and raw[1][0]=='div','The original root must contain an exponential quotient')
    phases={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0]=='exp' and m.contains(z,x)}
    require(len(phases)==1,'A single affine exponential scale is required')
    (phase,)=phases;rate,shift=affine(phase[1],x[1]);a=m.num(rate)
    require(a not in (None,0) and m.constant_defined(shift,ctx) and not domain_conditions(phase[1]),
            'The original exponential phase must be everywhere-defined and nonconstant affine')
    u=('v',kernel_symbol(task));v=u[1]
    lowered=[m.substitute(z,{phase:u}) for z in raw[1][1:]]
    require(not any(m.contains(z,x) or domain_conditions(z) for z in lowered),'Another original factor or domain cut remains')
    cp,dp=poly.rf(lowered[0],v);cq,dq=poly.rf(lowered[1],v)
    require(len(cp)==len(cq)==2 and len(dp)==len(dq)==1,'Both exponential polynomials must be affine')
    l,h=[z/dp[0] for z in cp];k,b=[z/dq[0] for z in cq]
    require(k>0 and b>0 and l<0 and h>0 and l/k==-h/b,
            'The opposite constant terms and equal normalized exponential rates are required')
    C=q(h/b);coordinate=('sqrt',m.div(raw[1],C));kernel=m.div(m.mul(q(4/a),m.power(u,2)),m.add(ONE,m.neg(m.power(u,4))))
    H=integrate_child(request,kernel,v)
    proof=dict(theorem='method.exponential_fraction_radical_pullback',chart='positive_exponential_radical',
               coordinate=coordinate,affine_rate=rate,positive_threshold=q(k/b),transformed_kernel=kernel,argument=[
                   'Выделяем положительный масштаб s=exp(ax+b). Дробь под корнем пропорциональна (s−q)/(s+q), поэтому исходная область задаётся s≥q>0.',
                   'Координата u=√((s−q)/(s+q)) принимает значения [0,1). Обратная карта s=q(1+u²)/(1−u²) даёт рациональный дифференциал.',
                   'Переносим доказанную первообразную обратно, включая край s=q по исходной непрерывности.'])
    return proof,family(raw,m.mul(m.simplify(('sqrt',C)),m.substitute(H,{u:coordinate})),region=dict(scale=phase,at_least=q(k/b)))


def reciprocal_quartic_radical(task):
    from integrals import family
    from tasks import domain_conditions
    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div' and raw[2][0]=='mul','A quadratic factor beside a quartic square root is required')
    n=raw[1];P,R=raw[2][1:]
    if P[0]=='sqrt':P,R=R,P
    require(R[0]=='sqrt' and not any(domain_conditions(z) for z in (n,P,R[1])),
            'The original polynomials must be everywhere real')
    (N,dn),(A,da),(Q,dq)=[poly.rf(z,x[1]) for z in (n,P,R[1])]
    require(len(dn)==len(da)==len(dq)==1 and len(N)==len(A)==3 and len(Q)==5
            and not any((N[1],A[1],Q[1],Q[3])) and Q[0]==Q[4] and Q[4]/dq[0]>0,
            'The numerator and outer factor must be even quadratics and the root reciprocal')
    s=A[0]/A[2];c=Q[2]/Q[4]
    require(s in (-1,1) and N[0]/N[2]==-s and c>-2,'The reciprocal sign or strict positivity of the quartic remains unproved')
    a=c-2*s;u=m.add(x,m.div(q(s),x));w=('sqrt',m.add(m.power(u,2),q(a)))
    if a>0:
        r=m.simplify(('sqrt',q(a)));H=m.div(('ln',m.div(m.add(w,m.neg(r)),m.add(w,r))),m.mul(q(2),r))
    elif a<0:
        r=m.simplify(('sqrt',q(-a)));H=m.neg(m.div(('atan',m.div(r,w)),r))
    else:H=m.neg(m.div(ONE,w))
    scale=m.div(q(N[2]*da[0]/(dn[0]*A[2])),m.simplify(('sqrt',q(Q[4]/dq[0]))))
    pieces=(((None,ZERO),m.mul(m.neg(scale),H)),((ZERO,None),m.mul(scale,H)))
    region=dict(included_zero=True,original_poles=[] if s==1 else [q(-1),ONE],trace=ZERO)
    return dict(theorem='method.reciprocal_quartic_radical_and_regular_join',chart='reciprocal_quartic_radical',
                coordinate=u,secondary_coordinate=w,scale=scale,sign=q(s),source_cover=region,argument=[
                    'Разделяем многочлен под корнем на x² и замечаем квадрат (x±1/x)². Внешний квадратный множитель даёт ту же координату, а числитель — её дифференциал.',
                    'Сохраняем знак x, поскольку квадратный корень из x² равен |x|. Следующая подстановка w=√(u²+a) сводит интеграл к dw/(w²−a).',
                    'Нормируем первообразную нулём при w→∞. Обе ветви имеют нулевой след в исходной регулярной точке x=0, где производная восстанавливается по непрерывности.']),\
           family(raw,('piecewise_primitive',pieces),region=region)


def power_weight_chart(task):
    """Find a polynomial multiplier of a radical by exact differential coefficients."""
    from graphs import domain_partition
    from integrals import family,polynomial_expression
    from radical_primitives import derivative_product
    from tasks import domain_conditions,known_guard
    x,raw,ctx,method=fixed_source(task);v=x[1];weights=[]
    def split(e,sign=1):
        if e[0] in ('mul','div'):
            return (e[0],split(e[1],sign),split(e[2],sign if e[0]=='mul' else -sign))
        if e[0]=='pow' and e[1][0] in ('sqrt','cbrt') and e[2]>0:
            return split(e[1],sign*e[2])
        if e[0] in ('sqrt','cbrt','rpow'):
            exponent=Fraction(1,2 if e[0]=='sqrt' else 3) if e[0]!='rpow' else m.num(m.simplify(e[2]))
            require(exponent is not None and exponent.denominator>1 and
                    (e[0]!='rpow' or m.constant_defined(e[2],ctx)),'The weighted exponent must be an exact real rational')
            weights.append((e[1],sign*exponent,e[0]));return ONE
        return e
    factor=split(raw)
    require(len(weights)==1 and all(known_guard(g,ctx) for g in domain_conditions(factor)),
            'A single polynomial weight without another original cut is required')
    (Q,p,convention),=weights;qp,dq=poly.rf(Q,v);P,d=poly.rf(factor,v)
    require(2<=len(qp)<=4 and len(dq)==len(d)==1 and not domain_conditions(Q),
            'A fixed low-degree radicand with a polynomial coefficient is required')
    qp=tuple(c/dq[0] for c in qp);P=tuple(c/d[0] for c in P)
    w=p+1;require(w,'A logarithmic weighted remainder needs another method')
    cancelled=-w*(len(qp)-1)
    bound=max(len(P)-len(qp)+1,int(cancelled) if cancelled.denominator==1 else 0,0)
    require(bound<=12,'The weighted polynomial coefficient system is too large')
    monomials=[(Fraction(0),)*j+(Fraction(1),) for j in range(bound+1)]
    columns=[derivative_product(A,qp,w) for A in monomials]
    coefficients=poly.span_coefficients(P,columns)
    require(coefficients is not None and tuple(derivative_product(tuple(coefficients),qp,w))==P,
            'No exact polynomial multiplier satisfies the weighted differential identity')
    A=polynomial_expression(coefficients,v)
    if w.denominator==2:F=m.power(('sqrt',Q),w.numerator)
    elif convention=='cbrt' and w.denominator==3:F=m.power(('cbrt',Q),w.numerator)
    else:F=('rpow',Q,q(w))
    if convention=='cbrt' and len(qp)==4 and qp[1]==qp[2]==0 and p<0:
        root=('cbrt',q(-qp[0]/qp[3]))
        chart=dict(excluded_points=[root],nonempty_components=2,
                   proof='a nonzero multiple of x³ plus a fixed scalar is strictly monotone and has this unique real zero')
        region=dict(cut=root,open_intervals=[(None,root),(root,None)])
    else:
        chart,region=domain_partition(v,domain_conditions(raw))
        require(any(chart['open_cells']),'The original field has no proved open interval')
    if p>0 and convention=='sqrt':
        require(w>1,'Included radical boundaries require a finite continuous trace')
    return dict(theorem='method.solve_weighted_polynomial_differential',chart='power_weight_chart',original_polynomial=Q,
                equation=('Q*A′+(p+1)*A*Q′',tuple(map(q,P))),power=q(p),multiplier=A,source_cover=chart,
                argument=['Предлагаем промежуточную форму A(x)Q(x)^{p+1}. Дифференцирование оставляет линейное уравнение для коэффициентов A.',
                          'Решаем уравнение точной арифметикой и снова проверяем полиномиальное равенство. Исходная вещественная область сохраняется, включая допустимые непрерывные края.']), \
                family(raw,m.mul(A,F),region=region)


def homogeneous_trig_quadratic(task):
    from integrals import family
    from tasks import domain_conditions
    x,raw,ctx,_=fixed_source(task,TABLE_METHODS|{'quadratic_canonical_form'})
    require(raw[0]=='div' and not any(domain_conditions(t) for t in raw[1:]),
            'A single original trigonometric quadratic denominator is required')
    s,cx=('sin',x),('cos',x);t=('tan',x)
    k=m.num(m.simplify(raw[1]));entries,den=m.rational_form(raw[2])
    allowed=(((s,2),),tuple(sorted(((s,1),(cx,1)),key=lambda row:m.render(row[0]))),((cx,2),))
    require(k is not None and k and den=={():Fraction(1)} and not set(entries)-{(),*allowed},
            'An exact nonzero constant numerator and homogeneous quadratic are required')
    a,b,c=(entries.get(j,Fraction(0)) for j in allowed)
    const=entries.get((),Fraction(0))
    a+=const;c+=const
    require(a or b or c,'The original trigonometric quadratic must be nonzero')
    if not a:
        F=m.mul(q(k/c),t) if not b else m.mul(q(k/b),('ln',('abs',m.add(m.mul(q(b),t),q(c)))))
        seam='original cosine cut'
    else:
        U=m.add(m.mul(q(2*a),s),m.mul(q(b),cx));D=4*a*c-b*b
        if D<0:
            L=m.simplify(('sqrt',q(-D)));H=m.mul(L,cx)
            F=m.div(m.mul(q(k),('ln',('abs',m.div(m.add(U,m.neg(H)),m.add(U,H))))),L)
            seam='homogeneous form is regular at all tangent seams'
        elif D==0:
            F=m.div(m.mul(q(-2*k),cx),U);seam='homogeneous double-root form is regular at tangent seams'
        else:
            L=m.simplify(('sqrt',q(D)));seed=m.div(m.mul(q(2*k),('atan',m.div(m.add(m.mul(q(2*a),t),q(b)),L))),L)
            left=m.div(m.mul(q(k if a>0 else -k),m.PI),L)
            F=('joined_periodic_primitive',m.mul(q(2),x),seed,m.mul(q(2),left),left)
            seam='left and right arctangent traces joined by exact periodic shift'
    return dict(theorem='method.lower_homogeneous_trig_quadratic',chart='homogeneous_trig_quadratic',
                coefficients=tuple(map(q,(a,b,c))),original_divisor=raw[2],tangent_seams=seam,
                argument=['В тангенсной координате исходный знаменатель после деления на cos² превращается в квадратный трёхчлен.',
                          'Приводим его к каноническому виду. Сохраняем исходные нули и пересобираем примитив у допустимых полюсов самой карты.']), \
                family(raw,F,region=dict(original_denominator=raw[2],condition='nonzero',artificial_seams=seam))


def hyperbolic_logarithm_chart(task,request):
    """Lower an original logarithmic conic coordinate, including its original real obligations."""
    from integrals import family,integrate_child,kernel_symbol,learned_nodes,source
    from model import freeze
    from tasks import domain_conditions,known_guard
    from verify import same_value

    x,raw,ctx,method=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    available=[]
    for u in learned_nodes(raw):
        if not isinstance(u,tuple) or u[0]!='ln' or u[1][0]!='add' or x not in u[1][1:]:continue
        R=u[1][1] if u[1][2]==x else u[1][2]
        if R[0]!='sqrt' or domain_conditions(R[1]):continue
        try:p,d=poly.rf(R[1],x[1])
        except (poly.NotRational,poly.Undefined):continue
        if len(p)==3 and len(d)==1 and p[2]==d[0] and not p[1] and p[0]/d[0]>0:
            available.append((u,R,q(p[0]/d[0])))
    available=list(dict.fromkeys(available))
    require(len(available)==1,'An original logarithm of x plus its positive hyperbolic radius is required')
    (log,R,c),=available;Q=R[1];scale=m.simplify(('sqrt',c));offset=m.simplify(('ln',scale))
    v=kernel_symbol(task);t=('v',v);X=m.mul(scale,('sinh',t));Y=m.mul(scale,('cosh',t));L=m.add(t,offset)
    coordinate=('ln',m.div(log[1],scale));restricted=False

    def radial_power(e):
        if same_value(e,Q):return Fraction(2)
        if e==R:return Fraction(1)
        if e[0]=='pow' and same_value(e[1],Q):return Fraction(2*e[2])
        if e[0]=='rpow' and same_value(e[1],Q):
            p=m.num(m.simplify(e[2]))
            if p is not None:return 2*p
        return None

    def log_over_radius(e):
        return e[0]=='div' and e[1]==log and same_value(e[2],Q)

    for r,e in domain_conditions(raw):
        if known_guard((r,e),ctx):continue
        if r=='positive' and same_value(e,log[1]):continue
        if radial_power(e) is not None:continue
        if r=='nonnegative' and (e==log or log_over_radius(e)):restricted=True;continue
        raise Unsupported('An original guard remains beyond the proved hyperbolic chart')

    def lower(e):
        if not isinstance(e,tuple):return e
        if e==x:return X
        if e==log:return L
        p=radial_power(e)
        if p is not None and p.denominator==1:return m.power(Y,int(p))
        if e[0]=='sqrt' and log_over_radius(e[1]):return m.div(('sqrt',L),Y)
        return (e[0],*(lower(z) for z in e[1:]))

    kernel=m.simplify(m.mul(lower(raw),Y))
    if method=='integration_by_parts':
        child=dict(kind='integrate',variable=v,integrand=source(kernel),method_requirement=method,
                   requested_output=['primitive_family'])
        H=freeze(request('integration by parts in the exact hyperbolic coordinate',child)['value']['representative'])
    else:H=integrate_child(request,kernel,v)
    region=dict(coordinate_image='all real t' if not restricted else 't+ln(R_scale)>=0',coordinate_shift=offset)
    return dict(theorem='method.hyperbolic_logarithm_coordinate',chart='hyperbolic_logarithm_chart',
                coordinate=coordinate,inverse=X,jacobian=Y,source_cover=region,transformed_kernel=kernel,argument=[
                    'Из x²+c>|x|² следует x+√(x²+c)>0. Берём логарифм после деления на √c. Его обратная карта x=√c·sinh(t) покрывает всю исходную прямую.',
                    'В той же координате радиус равен √c·cosh(t)>0 и совпадает с якобианом. Исходные логарифмические и корневые ограничения переносятся на новую область.',
                    'Проверяем отдельную первообразную новой плотности с обязательным способом, когда он задан. При включённой границе используем непрерывность.'
                ]),family(raw,m.substitute(H,{t:coordinate}),region=region)


def centered_quadratic_radical(task,request):
    """Separate even and odd rational weights in the centered quadratic coordinate."""
    from integrals import family, integrate_child, kernel_symbol, polynomial_expression, rational_proposal, source
    from radical_primitives import data

    methods=TABLE_METHODS|{'quadratic_canonical_form','partial_fractions_of_rational_factor'}
    x,raw,_,method=fixed_source(task,methods)
    name,_,quadratic,p,d,region,_,_=data(task)
    scale=quadratic[2]; offset=-quadratic[1]/(2*scale)
    affine_center=(-offset,Fraction(1))
    center=poly.composition_coefficients(quadratic,affine_center)
    constant=center[0]
    require(constant and center[1]==0,'The centered radical must have two distinct roots over the complex field')
    p_center,d_center=(poly.composition_coefficients(poly0,affine_center) for poly0 in (p,d))
    reflected=None
    if any(d_center[1::2]):
        from graphs import domain_partition
        from tasks import domain_conditions
        reflected=polynomial_expression(poly.composition_coefficients(d,(2*offset,Fraction(-1))),name)
        _,checked_region=domain_partition(name,(*domain_conditions(raw),('nonzero',reflected)))
        require(checked_region==region,'A reflected pole cuts an original component')
        reflected_center=tuple((-1)**i*c for i,c in enumerate(d_center))
        p_center,d_center=poly.pm(p_center,reflected_center),poly.pm(d_center,reflected_center)
    parts=None
    if method=='partial_fractions_of_rational_factor':
        rational=m.div(polynomial_expression(p,name),polynomial_expression(d,name))
        recipe=rational_proposal(dict(kind='integrate',variable=name,integrand=source(rational),
                                      method_requirement='rational_decomposition'),{'max_degree':12})
        parts=recipe['recipe']['terms']
    t_name=kernel_symbol(task); t=('v',t_name)
    square=m.power(t,2); transition=m.add(ONE,m.mul(q(-scale),square))
    y=m.add(x,q(-offset)); root=('sqrt',polynomial_expression(quadratic,name))
    answer=ZERO; branches=[]
    for odd,coeffs in enumerate((p_center[::2],p_center[1::2])):
        if not any(coeffs):continue
        # In the even part t=y/√Q, and dy/√Q=dt/(1−a*t²).
        # In the odd part t=√Q, and y*dy/√Q=dt/a; this identity also holds at y=0.
        y_squared=m.div(m.add(square,q(-constant)),q(scale)) if odd else m.div(m.mul(q(constant),square),transition)
        jacobian=m.div(ONE,q(scale) if odd else transition)
        density=m.div(polynomial_expression(coeffs,t_name),polynomial_expression(d_center[::2],t_name))
        p_new,d_new=poly.rf(('mul',m.substitute(density,{t:y_squared}),jacobian),t_name)
        common=poly.pgcd(p_new,d_new)
        kernel=m.div(polynomial_expression(poly.pdiv(p_new,common)[0],t_name),
                     polynomial_expression(poly.pdiv(d_new,common)[0],t_name))
        coordinate=root if odd else m.div(y,root)
        H=integrate_child(request,kernel,t_name)
        answer=m.add(answer,m.substitute(H,{t:coordinate}))
        branches.append(dict(parity='odd' if odd else 'even',coordinate=coordinate,rational_kernel=kernel,primitive=H))
    argument=[]
    if parts is not None:
        argument.append('Разлагаем исходный рациональный множитель на простые дроби и проверяем числитель после приведения к общему знаменателю.')
    if reflected is not None:
        argument.append('Домножение на отражённый знаменатель делает его чётным. Точная проверка области показывает, что его нули не добавляют разрывов.')
    argument.extend(['Выделяем полный квадрат в радикале и делим числитель на чётную и нечётную части относительно центра.',
                     'Для чётной части делим центрированную переменную на корень, для нечётной берём сам корень.'])
    argument.extend('Замена '+t_name+' = '+source(row['coordinate'])+' даёт рациональную плотность '+source(row['rational_kernel'])+'.'
                    for row in branches)
    argument.append('Возвращаем проверенные первообразные в исходную область и складываем.')
    return dict(theorem='method.centered_quadratic_radical',chart='centered_quadratic_radical',method=method,shift=q(offset),
                centered_quadratic=tuple(map(q,center)),partial_fractions=parts,reflected_factor=reflected,
                branches=branches,argument=argument),family(raw,answer,region=region)


def quadratic_radical_square_factor(task):
    from graphs import domain_partition
    from integrals import family,polynomial_expression
    from radical_primitives import checked_primitive,reduction
    from tasks import domain_conditions

    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='sqrt','The original integrand must be a single square root')
    p,d=poly.rf(raw[1],x[1])
    require(len(p)==5 and len(d)==1 and not domain_conditions(raw[1]),'A globally defined polynomial of degree four is required')
    p=tuple(u/d[0] for u in p)
    g=poly.pgcd(p,tuple(j*u for j,u in enumerate(p) if j))
    require(len(g)==3,'No repeated square factor was determined')
    h=-g[1]/2; linear=(-h,Fraction(1))
    require(g==poly.pp(linear,2),'The repeated part must be an exact affine square')
    Q,rest=poly.pdiv(p,g)
    require(not any(rest) and not sum(u*h**j for j,u in enumerate(Q)),
            'The sign change must occur at a zero of the remaining quadratic')
    S=polynomial_expression(linear,x[1]);Q_expr=polynomial_expression(Q,x[1])
    _,domain=domain_partition(x[1],domain_conditions(raw))
    require(domain[1],'The original real domain has no interval')
    target=poly.pm(linear,Q); recipe=reduction(target,Q)
    H=checked_primitive(recipe,target,Q,x)
    trace=m.substitute(H,{x:q(h)})
    require(m.constant_defined(trace,ctx),'A finite matching primitive trace was not verified')
    H=m.add(H,m.neg(m.simplify(trace)))
    piecewise=('piecewise_primitive',(((None,q(h)),m.neg(H)),((q(h),None),H)))
    return dict(theorem='method.quadratic_radical_square_factor',chart='quadratic_radical_square_factor',
                affine_factor=S,quadratic=Q_expr,common_trace=ZERO,coefficient_identity=recipe,argument=[
                    'Точное деление даёт исходный радиканд в виде S²·Q. На исходной области корень равен |S|·√Q, со знаком S на каждом участке.',
                    'Для S·√Q сравниваем коэффициенты в производной полинома, умноженного на √Q. Остающийся член 1/√Q берём в канонической форме.',
                    'Согласуем обе первообразные нулевым следом в точке S=0. Включённые края сохраняются, там используется производная со стороны области.'
                ]),family(raw,piecewise,region=domain)


def homogeneous_tangent_ratio(task,request):
    from integrals import (affine,family,integrate_child,join_periodic_integral,kernel_symbol,learned_nodes,
                           polynomial_expression,trig_polynomial)
    from tasks import domain_conditions,known_guard

    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div','Expected a ratio of homogeneous trigonometric polynomials')
    angles={e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0] in ('sin','cos')}
    phases={m.simplify(e[1]) for e in angles}
    require(len(phases)==1 and all(known_guard(g,ctx) for a in raw[1:] for g in domain_conditions(a)),
            'Both polynomials must be defined at a common affine angle')
    phase,=phases
    slope,offset=affine(phase,x[1]); rate=m.num(slope)
    require(rate is not None and rate>0 and m.constant_defined(offset,ctx),'A strictly increasing affine phase is required')
    subs={e:(e[0],x) for e in angles}
    polynomials=[trig_polynomial(m.substitute(e,subs),x) for e in raw[1:]]
    degrees=[{i+j for i,j in rows} for rows in polynomials]
    require(all(len(d)==1 for d in degrees) and next(iter(degrees[1]))==next(iter(degrees[0]))+2,
            'The denominator degree must exceed the numerator degree by two')
    symbol=kernel_symbol(task); z=('v',symbol)
    dense=[]
    for rows,degree in zip(polynomials,degrees):
        d,=degree
        coefficients=tuple(m.num(rows.get((i,d-i),ZERO)) for i in range(max(i for i,j in rows)+1))
        require(None not in coefficients,'Expected fixed rational coefficients')
        dense.append(polynomial_expression(coefficients,symbol))
    kernel=m.div(dense[0],m.mul(q(rate),dense[1])); H=integrate_child(request,kernel,symbol)
    coordinate=('tan',phase); pulled=m.substitute(H,{z:coordinate})
    top,bottom=(rows.get((next(iter(d)),0),ZERO) for rows,d in zip(polynomials,degrees))
    pulled,seam=join_periodic_integral(H,pulled,m.mul(q(2),phase),symbol,ctx,request,None if bottom==ZERO else m.div(top,bottom))
    return dict(theorem='method.homogeneous_tangent_ratio',chart='homogeneous_tangent_ratio',coordinate=coordinate,
                kernel=kernel,seam=seam,argument=[
                    'Однородность позволяет вынести степени косинуса. Разность степеней равна двум, поэтому этот множитель сокращается с дифференциалом тангенса.',
                    'Решаем рациональный интеграл в координате тангенса. В регулярной точке склейки проверяем оба односторонних следа; исходные полюсы остаются исключёнными.'
                ]),family(raw,pulled)


def harmonic_product_derivative(task,request):
    from integrals import family,integrate_child,kernel_symbol,polynomial_expression,symmetric_coefficients,trig_polynomial
    from tasks import domain_conditions,known_guard
    from verify import same_value

    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div' and all(known_guard(g,ctx) for e in raw[1:] for g in domain_conditions(e)),
            'The trigonometric numerator and denominator must be defined globally')
    wave=('sin',m.mul(q(4),x)); c=raw[1]
    weight=ONE if c==wave else next((u for u,v in (c[1:],c[1:][::-1]) if v==wave),None) if c[0]=='mul' else None
    require(weight is not None and m.num(weight) is not None and same_value(c,m.mul(weight,wave)),
            'The numerator is not the differential of the product of the squared harmonics')
    coefficients=symmetric_coefficients(trig_polynomial(raw[2],x))
    symbol=kernel_symbol(task); z=('v',symbol)
    kernel=m.div(m.mul(q(2),weight),polynomial_expression(coefficients,symbol))
    coordinate=m.mul(m.power(('sin',x),2),m.power(('cos',x),2))
    H=integrate_child(request,kernel,symbol)
    return dict(theorem='method.harmonic_product_derivative',chart='harmonic_product_derivative',coordinate=coordinate,
                kernel=kernel,argument=[
                    'В знаменателе симметричный многочлен от квадратов синуса и косинуса. Их сумма равна единице, поэтому остаётся многочлен от произведения.',
                    'Это произведение равно (1−cos(4x))/8. Производная совпадает с половиной исходной гармоники. Перенос первообразной сохраняет исходные нули знаменателя.'
                ]),family(raw,m.substitute(H,{z:coordinate}))


def reciprocal_shifted_exponential(task):
    from integrals import affine,family
    from tasks import domain_conditions,known_guard

    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='div' and m.num(m.simplify(raw[1])) is not None and raw[2][0]=='add',
            'A fixed numerator and a difference of squares are required')
    left,right=raw[2][1:]
    if left[0]=='mul' and left[1]==q(-1):left,right=right,left
    require(left[0]=='pow' and left[2]==2 and right[0]=='mul' and right[1]==q(-1)
            and right[2][0]=='pow' and right[2][2]==2,'The source denominator is not a difference of two squares')
    terms=[]
    for form in (left[1],right[2][1]):
        require(form[0]=='add','Both squares must contain an affine exponential expression')
        wave,c=form[1:] if form[1][0]=='exp' else form[1:][::-1]
        require(wave[0]=='exp' and all(known_guard(g,ctx) for g in domain_conditions(form)),
                'The source exponential phase must be defined globally')
        slope,offset=affine(wave[1],x[1]);terms.append((m.num(slope),m.num(offset),m.num(m.simplify(c))))
    (rate,s,C),(other,t,D)=terms
    require(rate and rate==other and s is not None and t is not None and s!=t and C is not None and C==D and C>=0,
            'Expected a common nonzero affine rate, distinct offsets, and a common nonnegative shift')
    from integrals import source
    A,B=('exp',q(s)),('exp',q(t));delta=m.add(A,m.neg(B));K=m.add(A,B); L=q(2*C)
    coordinate=('exp',m.mul(q(-rate),x)); den=m.add(K,m.mul(L,coordinate))
    H=m.div(m.power(coordinate,2),m.mul(q(2),K)) if L==ZERO else m.add(
        m.div(coordinate,L),m.neg(m.mul(m.div(K,m.power(L,2)),('ln',den))))
    answer=m.mul(m.div(m.neg(m.simplify(raw[1])),m.mul(q(rate),delta)),H)
    return dict(theorem='method.reciprocal_shifted_exponential',chart='reciprocal_shifted_exponential',coordinate=coordinate,
                positive_affine_denominator=(K,L),argument=[
                    'Выносим общую экспоненту в каждом слагаемом и раскладываем разность квадратов. Показатели с разными сдвигами различны, сумма экспонент положительна.',
                    'Берём обратную экспоненту '+source(coordinate)+'. Плотность становится линейным числителем над положительным аффинным знаменателем. Деление и логарифм дают первообразную.'
                ]),family(raw,answer)


def positive_binomial_projective(task,request):
    from integrals import exact_sign,family,guarded_input,integrate_child,kernel_symbol,real_polynomial_coefficients

    x,raw,ctx,_=guarded_input(task,TABLE_METHODS|{'rationalizing_substitution'})
    require(raw[0]=='div' and raw[2][0]=='rpow','Expected an original positive even root in the denominator')
    root=raw[2];exponent=m.num(m.simplify(root[2]))
    require(exponent is not None and exponent.numerator==1 and exponent.denominator in (2,4,6,8,10,12),
            'A fixed even root is required')
    n=exponent.denominator
    radicand=real_polynomial_coefficients(root[1],x[1],ctx,n)
    require(len(radicand)==n+1 and not any(c!=ZERO for c in radicand[:-2]),
            'The source radical is not the product of an odd power and an affine factor')
    A,B=radicand[-2],m.neg(radicand[-1])
    require(exact_sign(A,ctx)==exact_sign(B,ctx)==1,'Both affine scales must be positive')
    numerator=real_polynomial_coefficients(raw[1],x[1],ctx,8)
    selected=[(k,c) for k,c in enumerate(numerator) if c!=ZERO]
    require(len(selected)==1,'The source numerator must be a monomial')
    k,C=selected[0];name=kernel_symbol(task);t=('v',name)
    rt=('rpow',B,q(1,n));inverse=m.div(m.div(A,B),m.add(ONE,m.power(t,n)))
    coordinate=m.div(root,m.mul(rt,x))
    kernel=m.div(m.power(t,n-2),m.power(m.add(ONE,m.power(t,n)),k+1))
    H=integrate_child(request,kernel,name)
    scale=m.div(m.mul(q(-n),m.mul(C,m.power(m.div(A,B),k))),rt)
    region=dict(variable=x[1],lower=ZERO,upper=m.div(A,B),strict=True)
    return dict(theorem='method.positive_binomial_projective',chart='positive_binomial_projective',coordinate=coordinate,
                inverse=inverse,kernel=kernel,scale=scale,argument=[
                    'Знак произведения под чётным корнем оставляет интервал между нулём и положительным нулём аффинного множителя. Оба края исключает исходный знаменатель.',
                    'Делим корень на переменную и положительный масштаб. Обратная карта выражает старую переменную через 1+t^n, а дифференциал даёт рациональную плотность.',
                    'Проверяем рациональную первообразную и возвращаемся на исходный интервал.'
                ]),family(raw,m.mul(scale,m.substitute(H,{t:coordinate})),region=region)


def diagonal_projective_quadratics(task,request):
    from integrals import family,kernel_symbol,source
    from model import freeze
    from tasks import domain_conditions

    x,raw,ctx,method=fixed_source(task,TABLE_METHODS|{'specified_fractional_linear_substitution'})
    require(raw[0]=='div' and raw[2][0]=='mul' and m.num(m.simplify(raw[1])) is not None and not domain_conditions(raw[1]),
            'Expected a constant over a quadratic times a quadratic square root')
    P,root=raw[2][1:] if raw[2][2][0]=='sqrt' else raw[2][1:][::-1]
    require(root[0]=='sqrt' and not domain_conditions(P) and not domain_conditions(root[1]),'The source quadratic generators must be defined globally')
    rows=[]
    for e in (P,root[1]):
        coeff,d=poly.rf(e,x[1])
        require(len(coeff)==3 and len(d)==1,'Both source generators must be quadratic')
        c,b,a=(z/d[0] for z in coeff)
        require(a>0 and b*b<4*a*c,'Both source quadratics must be strictly positive')
        rows.append((c,b,a))
    (c,b,a),(g,f,e)=rows
    det=a*f-e*b
    require(det,'The two projective diagonal equations must be independent')
    product=(b*g-c*f)/det; total=2*(e*c-a*g)/det
    discriminant=total**2-4*product
    require(discriminant>0,'The projective anchors must be distinct real roots')
    num=m.perfect_root(discriminant.numerator,2);den=m.perfect_root(discriminant.denominator,2)
    require(num is not None and den is not None,'The projective anchors are not rational')
    gap=Fraction(num,den);alpha,beta=(total-gap)/2,(total+gap)/2
    name=kernel_symbol(task); t=('v',name)
    def diagonal(row):
        c,b,a=row
        require(2*c+b*(alpha+beta)+2*a*alpha*beta==0,'The mixed coefficient does not vanish')
        return m.add(q(c+b*alpha+a*alpha**2),m.mul(q(c+b*beta+a*beta**2),m.power(t,2)))
    U,V=map(diagonal,rows)
    kernel=('div',('add',ONE,t),('mul',U,('sqrt',V)))
    child=dict(kind='integrate',integrand=source(kernel),variable=name,requested_output=['primitive_family'])
    transformed,primitive=centered_quadratic_radical(child,request)
    H=primitive['representative']; limits=[ZERO,ZERO]
    local=kernel_symbol(child);z=('v',local)
    for branch in transformed['branches']:
        seed=branch['primitive']
        if branch['parity']=='odd':
            goal={'kind':'limit','variable':local,'expression':source(seed),'approach':{'point':'+inf','side':'positive_infinity'}}
            common=freeze(request('limit in the positive square-root coordinate',goal)['value'])
            ends=(common,common)
        else:
            root=('sqrt',transformed['centered_quadratic'][2])
            ends=tuple(m.simplify(m.substitute(seed,{z:m.div(q(s),root)})) for s in (1,-1))
        require(all(isinstance(L,tuple) and m.constant_defined(L,ctx) for L in ends),'Expected finite closed primitive limits')
        limits=[m.add(L,ell) for L,ell in zip(limits,ends)]
    coordinate=m.div(m.add(x,q(-alpha)),m.add(q(beta),m.neg(x)))
    scale=q(gap*m.num(m.simplify(raw[1])));pulled=m.substitute(H,{t:coordinate})
    left,right=(m.mul(m.mul(q(s),scale),m.add(pulled,m.neg(L))) for s,L in zip((1,-1),limits))
    answer=('piecewise_primitive',(((None,q(beta)),left),((q(beta),q(beta)),ZERO),((q(beta),None),right)))
    return dict(theorem='method.diagonal_projective_quadratics',chart='diagonal_projective_quadratics',method=method,
                anchors=(q(alpha),q(beta)),coordinate=coordinate,kernel=kernel,rational_branches=transformed['branches'],seam_value=ZERO,limits=limits,argument=[
                    'Подбираем два проективных якоря из уравнений на смешанные коэффициенты. Дробно-линейная замена одновременно делает оба квадрата чётными.',
                    'Корень переносится с модулем 1+t. Разделяем исходную прямую по знаку этого множителя и решаем общий интеграл в новой координате.',
                    'В точке, где координата уходит на бесконечность, исходная функция непрерывна. По двум конечным следам нормируем первообразную нулём, затем применяем теорему о среднем.'
                ]),family(raw,answer,region='all real x including the regular projective seam')


def odd_binomial_square_coordinate(task,request):
    from integrals import family,kernel_symbol,source
    from model import freeze
    from tasks import domain_conditions

    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='cbrt' and not domain_conditions(raw[1]),'An unrestricted real cube root is required')
    p,d=poly.rf(raw[1],x[1]);require(len(p)==4 and len(d)==1 and p[0]==p[2]==0,'Expected a cubic binomial odd in the original coordinate')
    A,B=p[1]/d[0],-p[3]/d[0]
    require(A>0 and B>0,'An increasing linear term and a negative cubic term are required')
    name=kernel_symbol(task);t=('v',name)
    coordinate=('cbrt',m.add(m.div(q(A/B),m.power(x,2)),q(-1)))
    P=m.power(t,3);kernel=m.div(P,m.power(m.add(ONE,P),2))
    goal=dict(kind='integrate',variable=name,integrand=source(kernel),method_requirement='ostrogradsky_reduction')
    H=freeze(request('rational primitive with repeated factors',goal)['value']['representative'])
    lim=dict(variable=name,expression=source(H),approach={'point':'+inf','side':'positive_infinity'})
    at_zero=freeze(request('finite trace from both sides at zero',lim)['value'])
    require(isinstance(at_zero,tuple) and m.constant_defined(at_zero,ctx),'The two finite origin traces are required')
    scale=m.mul(q(-3*A/(2*B)),('cbrt',q(B)))
    local=m.mul(scale,m.add(m.substitute(H,{t:coordinate}),m.neg(at_zero)))
    ans=('piecewise_primitive',(((None,ZERO),local),((ZERO,ZERO),ZERO),((ZERO,None),local)))
    return dict(theorem='method.odd_binomial_square_coordinate',chart='odd_binomial_square_coordinate',coordinate=coordinate,
                kernel=kernel,origin_trace=at_zero,argument=[
                    'Выносим старую координату из нечётного корня с её знаком. Квадрат старой координаты выражается через 1+t³, поэтому дифференциал рационален.',
                    'В точках нулевого радиканда выражение и исходная плотность непрерывны, что восстанавливает производную по теореме о среднем.',
                    'У нуля новая координата стремится к плюс бесконечности с обеих сторон. Проверяем общий след и нормируем первообразную нулём.'
                ]),family(raw,ans,region='the entire real line, joined at the added chart cuts')


def shifted_symbolic_trig_ratio(task):
    from integrals import affine,family,guarded_input,source
    from tasks import domain_conditions,known_guard
    from verify import same_value

    x,raw,ctx,_=guarded_input(task,TABLE_METHODS)
    require(raw[0]=='div' and all(e[0]=='rpow' for e in raw[1:]),'Two original real powers are required')
    (_,cosine,p),(_,sine,qexp)=raw[1:]
    require(cosine[0]=='cos' and sine[0]=='sin' and all(m.constant_defined(e,ctx) for e in (p,qexp))
            and not (m.variable_in(p) or m.variable_in(qexp)) and same_value(m.add(p,q(2)),qexp),
            'Expected a cosine and a sine whose exponents differ by two')
    require(all(known_guard(g,ctx) for phase in (cosine[1],sine[1]) for g in domain_conditions(phase)),
            'The original phases have unresolved holes')
    a,b=affine(cosine[1],x[1]);c,d=affine(sine[1],x[1]);rate=m.num(a)
    require(rate and same_value(a,c) and all(m.constant_defined(e,ctx) for e in (b,d)),
            'A common fixed nonzero rate is required')
    delta=m.add(b,m.neg(d));cos_delta=('cos',delta);sin_delta=('sin',delta)
    t=m.div(cosine,sine);n=m.add(p,ONE)
    denom=m.mul(q(rate),cos_delta);normal=m.neg(m.div(('rpow',t,n),m.mul(denom,n)))
    zero=m.neg(m.div(('ln',t),denom));constant=m.neg(m.div(('cot',sine[1]),q(rate)))
    C,N,S=map(source,(cos_delta,n,sin_delta))
    branches=[dict(condition=C+'!=0 and '+N+'!=0',representative=normal),
              dict(condition=C+'!=0 and '+N+'=0',representative=zero),
              dict(condition=C+'=0 and '+S+'=-1',representative=constant),
              dict(condition=C+'=0 and '+S+'=1',components='empty original positive-base domain')]
    return dict(theorem='method.shifted_symbolic_trig_ratio',chart='shifted_symbolic_trig_ratio',ratio=t,phase_difference=delta,
                order=n,argument=[
                    'Из разности показателей выделяем квадрат синуса. Производная отношения равна минус произведению общего наклона и косинуса разности фаз, делённому на этот квадрат.',
                    'При ненулевой производной берём степенное или логарифмическое ядро. При нулевом косинусе проверяем две постоянные ветви отношения и сохраняем положительность исходных оснований.'
                ]),family(raw,branches=branches)


def reciprocal_inverse_parts(task):
    from integrals import family,learned_nodes,separate_weight
    from radical_primitives import checked_primitive,reduction
    from tasks import domain_conditions,known_guard
    x,raw,ctx,_=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    candidates={e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0] in ('asin','acos') and m.contains(e,x)}
    require(len(candidates)==1,'Expected one circular inverse with a reciprocal argument')
    u,=candidates
    require(all(g in domain_conditions(u) or known_guard(g,ctx) for g in domain_conditions(raw)),
            'The remaining source factors introduce additional holes')
    pn,qn=poly.rf(u[1],x[1]);require(len(pn)==1 and len(qn)==2 and not qn[0] and pn[0],
                                   'The inverse argument must be a nonzero multiple of 1/x')
    R,multiplicity=separate_weight(raw,u); p,d=poly.rf(R,x[1])
    k=len(p)-1
    require(multiplicity==1 and len(d)==1 and 0<=k<=12 and not any(p[:-1]) and p[-1],
            'The remaining factor must be a monomial of bounded nonnegative degree')
    a=pn[0]/qn[1];c=p[-1]/d[0];Q=(-a*a,Fraction(0),Fraction(1))
    target=(Fraction(0),)*k+(Fraction(1),); recipe=reduction(target,Q)
    H=checked_primitive(recipe,target,Q,x)
    orientation=1 if u[0]=='acos' else -1
    uv=m.mul(m.mul(q(c/(k+1)),m.power(x,k+1)),u)
    rest=m.mul(m.mul(q(orientation*a*c/(k+1)),m.div(x,('abs',x))),H)
    region=dict(boundary=q(abs(a)),components='two closed rays with one-sided derivatives at the included endpoints')
    return dict(theorem='method.reciprocal_inverse_parts',chart='reciprocal_inverse_parts',chosen_u=u,radical=tuple(map(q,Q)),
                residual_reduction=recipe,argument=[
                    'Выбираем обратную функцию как u, а одночлен интегрируем напрямую. Производная обратной функции оставляет квадратный радикал и знак исходной координаты.',
                    'Сравнением коэффициентов решаем остаток с квадратным корнем. Обе формулы непрерывны на включённых концах, где первообразная имеет относительную производную.'
                ]),family(raw,m.add(uv,m.neg(rest)),region=region)


def quadratic_weight_coordinate(task,request):
    from integrals import family,integrate_child,kernel_symbol,learned_nodes
    from tasks import domain_conditions

    x,raw,_,_=fixed_source(task)
    name=kernel_symbol(task);t=('v',name)
    def split(e):
        if e==x:return 1,ONE
        if e[0]!='mul':return 0,e
        a,p=split(e[1]);b,q0=split(e[2]);return a+b,('mul',p,q0)
    count,rest=split(raw)
    require(count==1,'The source differential needs exactly one explicit odd monomial factor')
    candidates=dict.fromkeys(e for e in learned_nodes(rest) if isinstance(e,tuple) and e[0]=='sqrt')
    for root in candidates:
        try:p,d=poly.rf(root[1],x[1])
        except (poly.NotRational,poly.Undefined):continue
        if len(p)!=3 or len(d)!=1 or p[1] or domain_conditions(root[1]):continue
        b,a=p[0]/d[0],p[2]/d[0]
        if a<=0 or b<=0:continue
        square=m.div(m.add(m.power(t,2),q(-b)),q(a))
        def mapped(e):
            if e==root:return t
            if e[0]=='pow' and e[1]==x and e[2]%2==0:return m.power(square,e[2]//2)
            return (e[0],*(mapped(z) if isinstance(z,tuple) else z for z in e[1:]))
        transformed=mapped(rest)
        if m.contains(transformed,x):continue
        kernel=m.mul(transformed,m.div(t,q(a)))
        H=integrate_child(request,kernel,name)
        return dict(theorem='method.quadratic_weight_coordinate',chart='quadratic_weight_coordinate',coordinate=root,kernel=kernel,
                    transformed_guards=domain_conditions(transformed),argument=[
                        'Положительный квадратный радикал даёт координату t. Во всех остальных множителях заменяем квадрат исходной переменной через t².',
                        'Явный множитель x·dx переносится в t·dt/a. Исходные логарифмические и корневые ограничения переносятся вместе с аргументами.',
                        'Подставляем доказанную первообразную в исходную координату. Правило цепочки действует и в стационарной точке, если она принадлежит области.'
                    ]),family(raw,m.substitute(H,{t:root}))
    raise Unsupported('No positive quadratic coordinate transports the whole originally even weight')



def singular_guard_at(expr,x,point,ctx):
    from tasks import domain_conditions
    for relation,value in domain_conditions(expr):
        sign=m.sign(m.substitute(value,{x:point}),ctx)
        if relation=='nonzero' and sign==0 or relation=='positive' and sign in (-1,0) or relation=='nonnegative' and sign==-1:
            return True
    return False


def inverse_parts_weight_span(task):
    from integrals import affine,family,kernel_symbol,learned_nodes,separate_weight
    from tasks import domain_conditions,known_guard
    x,raw,ctx,_=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    atoms=set(e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0] in ('asin','acos','atan') and m.contains(e,x))
    require(len(atoms)==1,'One inverse function must be identifiable as the parts factor')
    u,=atoms
    a,b=affine(u[1],x[1]);rate=m.num(a)
    require(rate and m.num(b) is not None and all(known_guard(g,ctx) for g in domain_conditions(u[1])),
            'A fixed regular affine argument is required for the inverse function')
    name=kernel_symbol(task);z=('v',name);arg=u[1];new_chart=m.div(m.add(z,m.neg(b)),a)
    R,n=separate_weight(raw,u)
    require(n==1,'The inverse factor must occur once in the original product')
    circle=u[0]!='atan';sign=q(-1 if u[0]=='acos' else 1)
    square=m.power(z,2);S=('sqrt',m.add(ONE,m.neg(square)))
    W=m.mul(m.substitute(R,{x:new_chart}),q(1/rate))
    P,D=poly.rf(m.mul(W,S) if circle else W,name)
    x2=(Fraction(0),Fraction(0),Fraction(1));unit=(Fraction(1),);plus=poly.pa(unit,x2)
    if circle:
        columns=[D,poly.pm(D,tuple(m.num(sign)*p for p in x2))]
        target=poly.pm(P,x2)
    else:
        columns=[poly.pm(D,plus),poly.pm(D,x2)]
        target=poly.pm(poly.pm(P,x2),plus)
    constants=poly.span_coefficients(target,columns)
    require(constants is not None,'The differential is outside the span of the two verified parts weights')
    a0,b0=constants
    F=m.mul(q(b0/2),m.power(u,2))
    if a0:
        require(singular_guard_at(raw,x,m.neg(m.div(b,a)),ctx),'The zero of the new coordinate is not excluded by the original integrand')
        log=('ln',('abs',z))
        H=m.neg(m.div(S if circle else ONE,z))
        G=m.neg(m.mul(sign,log)) if circle else m.add(m.neg(log),m.mul(q(1,2),('ln',m.add(ONE,square))))
        F=m.add(F,m.mul(q(a0),m.add(m.mul(u,m.substitute(H,{z:arg})),m.neg(m.substitute(G,{z:arg})))))
    return dict(theorem='method.inverse_parts_weight_span',chart='inverse_parts_weight_span',parts_factor=u,
                coefficients=tuple(map(q,constants)),coordinate=arg,kernel_identity=[list(map(q,c)) for c in (*columns,target)],
                argument=[
                    'Выделяем обратную функцию как u. В аффинном аргументе сравниваем коэффициенты двух весов: производной u и производной вспомогательного обратного выражения.',
                    'Для круговой ветви это −√(1−t²)/t, для арктангенса −1/t. Их производные и u′ оставляют элементарный логарифмический остаток.',
                    'Нуль новой координаты проверяем по исходным ограничениям. Включённая крайняя точка главной ветви использует непрерывный след и относительную производную.'
                ]),family(raw,F)


def circular_log_parts(task):
    from integrals import affine,family,learned_nodes,separate_weight
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x,raw,ctx,_=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    logs={e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0]=='ln'}
    require(len(logs)==1,'One logarithmic factor is needed')
    L,=logs
    weight,power=separate_weight(raw,L)
    require(power==1,'The logarithm must be a multiplicative factor')
    roots={e for e in learned_nodes(weight) if isinstance(e,tuple) and e[0]=='sqrt'}
    require(len(roots)==1,'One multiplicative circular radical is required')
    S,=roots
    # The affine coordinate can be read from any linear factor inside the log.
    atoms=tuple(dict.fromkeys(e for e in learned_nodes(L[1]) if isinstance(e,tuple) and m.contains(e,x)))
    for t in atoms:
        try:a,b=affine(t,x[1])
        except Unsupported:continue
        a0=m.num(a)
        if not a0 or m.num(b) is None or not same_value(m.add(ONE,m.neg(m.power(t,2))),S[1]):
            continue
        if any(not known_guard(g,ctx) for g in domain_conditions(t)):continue
        constant=m.num(m.simplify(m.div(m.mul(weight,S),t)))
        if constant is None or not constant:continue
        # Basis leaves t, 1−t and 1+t, with separate signed exponents.
        sign_leaves=(t,m.add(ONE,m.neg(t)),m.add(ONE,t))
        def powers(e,exponent=Fraction(1)):
            if all(known_guard(g,ctx) for g in domain_conditions(e)):
                scalar=m.num(m.simplify(e))
                if scalar is not None and scalar>0:return (Fraction(0),)*3
            for i,leaf in enumerate(sign_leaves):
                if same_value(e,leaf) and not domain_conditions(e):
                    if i==0 and exponent.denominator!=1:
                        raise Unsupported('A signed coordinate cannot use a fractional exponent in this log pattern')
                    return tuple(exponent if j==i else Fraction(0) for j in range(3))
            if e[0] in ('mul','div'):
                l=powers(e[1],exponent);r=powers(e[2],exponent if e[0]=='mul' else -exponent)
                return tuple(p+q0 for p,q0 in zip(l,r))
            if e[0]=='sqrt':return powers(e[1],exponent/2)
            if e[0]=='pow':return powers(e[1],exponent*e[2])
            raise Unsupported('The original argument is not a product of circular affine powers')
        e0,em,ep=powers(L[1])
        S=m.simplify(S);A=('asin',t)
        corrections=[m.mul(q(-em),m.add(A,m.neg(S))),m.mul(q(ep),m.add(A,S))]
        if e0:
            require(singular_guard_at(raw,x,m.neg(m.div(b,a)),ctx),'The coordinate zero must be excluded before adding the logarithm')
            rational_log=('ln',m.div(('abs',t),m.add(ONE,S)))
            corrections.append(m.mul(q(e0),m.add(S,rational_log)))
        result=m.neg(m.mul(S,L))
        for correction in corrections:result=m.add(result,correction)
        answer=m.mul(q(constant/a0),result)
        return dict(theorem='method.circular_log_parts',chart='circular_log_parts',coordinate=t,log_factor=L,
                    exponents=tuple(map(q,(e0,em,ep))),argument=[
                        'Произведение линейных степеней внутри логарифма даёт сумму трёх простых логарифмических производных на исходной положительной области.',
                        'Интегрирование по частям берёт −√(1−t²) как первообразную веса. Остатки при 1±t переписываем через (1∓t)/√(1−t²).',
                        'Остаток при 1/t даёт корень и логарифм модуля. Его дополнительный делитель разрешён только после проверки исходного выкола.'
                    ]),family(raw,answer)
    raise Unsupported('No regular affine coordinate verifies the original circular weight and all log factors')


def hyperbolic_log_parts(task,request):
    from integrals import affine,family,integrate_child,kernel_symbol,learned_nodes,separate_weight
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x,raw,ctx,_=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    atoms={e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0]=='ln' and e[1][0]=='add'}
    require(len(atoms)==1,'A unique logarithm with a positive quadratic radical is required')
    L,=atoms
    t,S=L[1][1:]
    if t[0]=='sqrt':t,S=S,t
    require(S[0]=='sqrt','The logarithm must contain a quadratic root')
    a,b=affine(t,x[1]);rate=m.num(a)
    A=m.num(m.simplify(m.add(S[1],m.neg(m.power(t,2)))))
    require(rate and m.num(b) is not None and A is not None and A>0 and
            all(known_guard(g,ctx) for e in (t,S[1]) for g in domain_conditions(e)),
            'The log needs a globally smooth affine t plus √(t²+A) with A>0')
    R,n=separate_weight(raw,L)
    require(n==1,'One logarithmic factor is required')
    name=kernel_symbol(task);z=('v',name);square=m.power(z,2)
    new_chart=m.div(m.add(z,m.neg(b)),a)
    P,D=poly.rf(m.mul(q(1/rate),m.substitute(R,{x:new_chart})),name)
    require(len(P)==2 and not P[0] and P[1] and len(D)==5 and not D[1] and not D[3],
            'The other factor must be a linear numerator over an even squared quadratic')
    C=D[2]/(2*D[4])
    require(D[0]==D[4]*C*C,'The denominator is not the square of an affine polynomial in t²')
    K=P[1]/D[4];r=m.div(t,S)
    kernel=m.div(q(-K/2),m.add(q(C),m.mul(q(A-C),square)))
    H=integrate_child(request,kernel,name)
    require(H[0] not in ('piecewise_primitive','joined_periodic_primitive'),
            'The child would need explicit transport of its primitive branches')
    # z=t/sqrt(t²+A) maps the real line to (-1,1). Its only new denominator is strictly positive.
    V=m.div(q(-K/2),m.add(m.power(t,2),q(C)))
    answer=m.add(m.mul(V,L),m.neg(m.substitute(H,{z:r})))
    return dict(theorem='method.hyperbolic_log_parts',chart='hyperbolic_log_parts',parts_factor=L,parts_primitive=V,
                replacement=r,image='(-1,1)',kernel=kernel,argument=[
                    'Положительность t+√(t²+A) следует из A>0. Производная его логарифма равна 1/√(t²+A).',
                    'Рациональный вес интегрируем через квадрат аргумента и получаем остаток с положительным квадратным корнем.',
                    'Координата z=t/√(t²+A) рационализует остаток. Тождество t²+C=(C+(A−C)z²)/(1−z²) сохраняет все полюсы.',
                    'Подставляем доказанную первообразную остатка в исходную область.'
                ]),family(raw,answer)


def affine_log_ratio_parts(task):
    from integrals import affine,family,guarded_input,learned_nodes,separate_weight
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x,raw,ctx,_=guarded_input(task,TABLE_METHODS|{'integration_by_parts'})
    logs={e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0]=='ln' and e[1][0]=='abs' and e[1][1][0]=='div'}
    require(len(logs)==1,'One logarithm of an absolute affine ratio is required')
    L,=logs;left,right=L[1][1][1:]
    def root(e):
        a,b=affine(e,x[1]);rate,shift=m.num(a),m.num(b)
        require(rate and shift is not None and all(known_guard(g,ctx) for g in domain_conditions(e)),
                'Both affine factors need fixed rates and exact source roots')
        return q(-shift/rate)
    r,s=map(root,(left,right))
    require(r!=s,'The logarithmic derivative must be nonzero')
    X,Y=m.add(x,m.neg(r)),m.add(x,m.neg(s))
    D=m.mul(X,Y)
    W,n=separate_weight(raw,L)
    require(n==1,'The logarithmic factor occurs more than once')
    N=m.polynomial_quotient(('mul',W,D));p,d=m.rational_form(N)
    require(d=={():Fraction(1)},'The source multiplier must become a polynomial over the two linear factors')
    constant=m.poly_expr({tuple((v,k) for v,k in mon if v!=x):c for mon,c in p.items() if dict(mon).get(x)==2})
    coef=m.div(m.add(N,m.neg(m.mul(constant,D))),m.add(r,m.neg(s)))
    require(all(m.constant_defined(e,ctx) and not m.variable_in(e,x[1]) for e in (coef,constant)),
            'The source weight is not spanned by a constant and the logarithmic derivative')
    require(same_value(W,m.add(constant,m.mul(coef,m.div(m.add(r,m.neg(s)),D)))),
            'Coefficient collection did not reproduce the complete source weight')
    log=lambda e:('ln',('abs',e))
    V=m.add(m.mul(x,L),m.add(m.neg(m.mul(r,log(X))),m.mul(s,log(Y))))
    F=m.add(m.mul(constant,V),m.mul(m.mul(q(1,2),coef),m.power(L,2)))
    return dict(theorem='method.affine_log_ratio_parts',chart='affine_log_ratio_parts',roots=[r,s],
                parts_weight=[constant,coef],argument=[
                    'Логарифмическая производная равна разности обратных линейных множителей. По коэффициентам выделяем постоянную и кратную этой производной часть исходного веса.',
                    'Кратная часть интегрирует квадрат логарифма. Постоянная часть использует интегрирование по частям и два логарифма модуля.',
                    'Обе линейные нулевые точки уже запрещены исходным логарифмом отношения.'
                ]),family(raw,F)


def primitive_chart(task,chart,request):
    variations={'signed_laurent_chart':signed_laurent_chart,'positive_exponential_chart':positive_exponential_chart,
                'reciprocal_quartic_chart':reciprocal_quartic,'power_weight_chart':power_weight_chart,
                'homogeneous_trig_quadratic':homogeneous_trig_quadratic,'reciprocal_quartic_radical':reciprocal_quartic_radical,
                'quadratic_radical_square_factor':quadratic_radical_square_factor,
                'reciprocal_shifted_exponential':reciprocal_shifted_exponential,'shifted_symbolic_trig_ratio':shifted_symbolic_trig_ratio,
                'reciprocal_inverse_parts':reciprocal_inverse_parts,'inverse_parts_weight_span':inverse_parts_weight_span,
                'circular_log_parts':circular_log_parts,'affine_log_ratio_parts':affine_log_ratio_parts}
    with_child={'inverse_function_chart':inverse_function_chart,'binomial_root_chart':binomial_root_chart,
                'circular_branch_chart':circular_branch_chart,'paired_circle_chart':paired_circle_chart,
                'constant_radical_difference':constant_radical_difference,'positive_exponential_radical':positive_exponential_radical,
                'hyperbolic_logarithm_chart':hyperbolic_logarithm_chart,'positive_exponential_pullback':positive_exponential_pullback,
                'common_symbolic_power':common_symbolic_power,'signed_integer_affine_power':signed_integer_affine_power,
                'odd_root_rational_coordinate':odd_root_rational_coordinate,'positive_affine_inverse_chart':positive_affine_inverse_chart,
                'regular_harmonic_root':regular_harmonic_root,'hyperbolic_quadratic_pullback':hyperbolic_quadratic_pullback,
                'centered_quadratic_radical':centered_quadratic_radical,'homogeneous_tangent_ratio':homogeneous_tangent_ratio,
                'harmonic_product_derivative':harmonic_product_derivative,'positive_binomial_projective':positive_binomial_projective,
                'diagonal_projective_quadratics':diagonal_projective_quadratics,'odd_binomial_square_coordinate':odd_binomial_square_coordinate,
                'quadratic_weight_coordinate':quadratic_weight_coordinate,'hyperbolic_log_parts':hyperbolic_log_parts}
    try:
        if chart=='circular_cut_pullback':return circular_branch_chart(task,request,keep_cuts=True)
        return variations[chart](task) if chart in variations else with_child[chart](task,request)
    except (poly.NotRational,poly.Undefined,EmptyBranch) as exc:
        raise Unsupported(str(exc) or 'The original coordinate and real domain could not be certified') from exc


def common_symbolic_power(task,request):
    """Use a single positive monomial as a coordinate for a whole differential."""
    from integrals import common_phase_rate,family,input_data,integrate_child,kernel_symbol,source
    from verify import same_value
    x,raw,ctx,_=input_data(task,TABLE_METHODS)
    require(bool(ctx['parameters']) and not task.get('stated_conditions'),
            'The common exponent must be built from unrestricted fixed real parameters')
    name=kernel_symbol(task);u=('v',name)
    def exponential(e):
        if e==x:return ONE
        if e[0] in ('pow','rpow') and e[1]==x:
            p=q(e[2]) if e[0]=='pow' else e[2]
            require(m.constant_defined(p,ctx) and not m.variable_in(p,x[1]),'The exponent must be fixed and defined')
            return p
        return None
    def split(e):
        p=exponential(e)
        if p is not None:return ONE,p
        if e[0] not in ('mul','div'):return e,ZERO
        a,p=split(e[1]);b,r=split(e[2])
        if e[0]=='mul':return m.mul(a,b),m.add(p,r)
        return ('div',a,b),m.add(p,m.neg(r))
    residue,w=split(raw)
    w=m.add(w,ONE)
    atoms={}
    def collect(e):
        p=exponential(e)
        if p is not None:atoms[e]=p
        elif e[0] not in ('q','pi'):
            require(e[0] in ('add','div','mul','pow','sqrt','cbrt'),
                    'A coordinate-independent factor or a supported radical of the common monomial is required')
            for c in e[1:]:
                if isinstance(c,tuple):collect(c)
    collect(residue)
    exponents=(*atoms.values(),w)
    pivot=next((e for e in exponents if any(m.contains(e,('s',n)) for n in ctx['parameters'])),None)
    require(pivot is not None,'A parameter-dependent common scale is required')
    def rate(e):
        top,bot=m.rational_form(m.div(e,pivot))
        require(set(bot)=={()} and not set(top)-{()},'The exponent is not a constant multiple of the proposed scale')
        return top.get((),Fraction(0))/bot[()]
    rates=[rate(e) for e in exponents]
    unit=common_phase_rate(r for r in rates if r)
    step=m.mul(q(unit),pivot)
    powers=[int(r/unit) for r in rates]
    require(all(abs(j)<=32 for j in powers) and all(same_value(e,m.mul(q(j),step)) for e,j in zip(exponents,powers)),
            'Exact bounded integer powers must reproduce every original exponent')
    collapsed=m.substitute(residue,{e:ONE for e in atoms})
    require(m.constant_defined(collapsed,ctx),'The collapsed scale needs a separate original domain branch')
    lowered=m.substitute(residue,{e:m.power(u,j) for e,j in zip(atoms,powers)})
    kernel=m.simplify(m.mul(m.power(u,powers[-1]-1),lowered))
    H=integrate_child(request,kernel,name)
    coordinate=('rpow',x,step)
    branches=[
        dict(condition=source(step)+'!=0',primitive=m.div(m.substitute(H,{u:coordinate}),step)),
        dict(condition=source(step)+'=0',primitive=m.mul(collapsed,('ln',x)))]
    return dict(theorem='method.common_symbolic_monomial',chart='common_symbolic_power',coordinate=coordinate,
                exponent_relations=tuple(zip(exponents,powers)),residual=lowered,kernel=kernel,
                argument=['Собираем степенные множители дифференциала и добавляем единицу к внешнему показателю.',
                          'Предлагаем общую степень x^g. В точной арифметике проверяем, что каждый показатель является целым кратным g.',
                          'При g≠0 подстановка взаимно однозначна на x>0. Проверяем первообразную нового ядра и возвращаем её на исходную область с сохранением знаменателей.',
                          'При g=0 все связанные степени равны единице, а исходная плотность сводится к постоянному множителю от 1/x.']), \
        family(raw,branches=branches,region=dict(base='x>0',additional_conditions='all original radical and denominator guards'))


def signed_integer_affine_power(task,request):
    from integrals import affine,family,input_data,source
    from tasks import domain_conditions,known_guard
    names=task.get('parameters',[])
    name=names[0] if len(names)==1 and isinstance(names[0],str) else None
    require(name and task.get('stated_conditions') in ([name+' is a positive integer'],[name+' is a natural number']),
            'A positive integral source index must be explicit')
    x,raw,ctx,_=input_data({**task,'stated_conditions':[]},TABLE_METHODS)
    require(raw[0]=='div' and raw[2][0]=='rpow' and m.num(raw[1]) is not None,
            'A fixed numerator over an integer affine power is required')
    base,p=raw[2][1:]
    a,b=affine(base,x[1])
    require(m.constant_defined(a,ctx) and m.nonzero(a,ctx) and m.constant_defined(b,ctx)
            and all(known_guard(g,ctx) for g in domain_conditions(base)),
            'The original affine base must have nonzero fixed slope and no further cuts')
    k='_integer_index'
    symbol=('s',name)
    require(k not in (x[1],name),'The fresh index binder must be distinct')
    step,offset=affine(m.substitute(p,{symbol:('v',k)}),k)
    j,l=map(m.num,(step,offset))
    require(j is not None and l is not None and j.denominator==l.denominator==1 and j>0 and j+l>=1
            and all(known_guard(g,ctx) for g in domain_conditions(p)),
            'The affine exponent must stay integral and positive for every original index')
    scale=m.div(raw[1],a);d=m.add(ONE,m.neg(p))
    F=m.div(m.mul(scale,('signed_integer_power',base,d)),d)
    branch=dict(condition=source(p)+'!=1',primitive=F)
    if j+l==1:
        value=family(raw,branches=[branch,dict(condition=source(p)+'=1',primitive=m.mul(scale,('ln',('abs',base))))])
    else:value=family(raw,F)
    domain=('and',[('nonzero',base)])
    value.update(original_domain=domain,real_domain=domain,integer_exponents=True)
    return dict(theorem='method.common_symbolic_monomial',chart='signed_integer_affine_power',base=base,power=p,slope=a,
               index=name,argument=['Напечатанный индекс — положительное целое число, и исходный показатель целый и положительный на всём этом множестве.',
                                    'Основание аффинно и отлично от нуля на обеих исходных компонентах. Применяем правило целой степени с точным постоянным якобианом.',
                                    'При показателе единица используется логарифм модуля. Константы на двух компонентах независимы.']),value


def perfect_odd_polynomial(p,n):
    if not any(p):return p
    degree,rest=divmod(len(p)-1,n)
    lead=m.perfect_root(abs(p[-1].numerator),n)
    den=m.perfect_root(p[-1].denominator,n)
    require(not rest and lead is not None and den is not None and degree<=12,
            'The polynomial does not have a supported exact odd root')
    s=[Fraction(0)]*(degree+1)
    s[-1]=Fraction(lead if p[-1]>0 else -lead,den)
    scale=n*s[-1]**(n-1)
    for j in range(degree-1,-1,-1):
        k=(n-1)*degree+j
        s[j]=(p[k]-poly.pp(s,n)[k])/scale
    require(poly.pp(s,n)==p,'The proposed root fails the exact polynomial identity')
    return tuple(s)


def odd_root_rational_coordinate(task,request):
    """Propose odd roots of rational coordinates, then check exact rational radicands."""
    from graphs import rational_roots
    from integrals import family,input_data,integrate_child,kernel_symbol,learned_nodes,polynomial_expression
    from tasks import domain_conditions
    from verify import same_value
    method=task.get('method_requirement','table_and_rules')
    root_key='source_root_conventions'
    x,raw,ctx,_=input_data({k:v for k,v in task.items() if k!=root_key},TABLE_METHODS|{'rationalizing_substitution'})
    require(not ctx['parameters'] and not task.get('stated_conditions'),'The projective coefficients must be fixed rational numbers')
    if root_key in task:
        rows=task[root_key]
        require(isinstance(rows,list) and len(rows)==1,'Exactly one source signed-root reading is supported')
        row=rows[0];n=row.get('index')
        require(set(row)=={'index','radicand','meaning'} and type(n) is int and 3<=n<=9 and n%2==1 and
                re.fullmatch(r'real \w+ root of the entire radicand; negative values are admitted before the outer division',row['meaning']),
                'The source must preserve the negative branch of the entire odd root')
        source_rad=m.parse(row['radicand'],x[1])
        powers={e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0]=='rpow' and
                m.num(m.simplify(e[2]))==Fraction(1,n) and same_value(e[1],source_rad)}
        require(len(powers)==1,'The source note must bind to exactly one odd-root expression')
        atom,=powers
        raw=m.substitute(raw,{atom:('real_odd_root',n,atom[1])})
    def odd(e):
        return (3,e[1]) if e[0]=='cbrt' else e[1:] if e[0]=='real_odd_root' else None
    roots={e:odd(e) for e in learned_nodes(raw) if isinstance(e,tuple) and odd(e)}
    require(roots and len(roots)<=3,'A bounded number of original odd real roots is required')
    guard=domain_conditions(raw)
    name=kernel_symbol(task);t=('v',name)
    roots_rational={e:poly.rf(radicand,x[1]) for e,(n,radicand) in roots.items()}
    def source_hole(at):
        def sign(expr):
            desc=odd(expr)
            e=m.substitute(desc[1] if desc else expr,{x:q(at)})
            if any(isinstance(node,tuple) and odd(node) for node in learned_nodes(e)):return None
            return m.sign(e,ctx) if m.constant_defined(e,ctx) else None
        def vanishes(expr):
            if expr[0]=='mul':return any(map(vanishes,expr[1:]))
            if expr[0]=='pow' and expr[2]>0:return vanishes(expr[1])
            return sign(expr)==0
        return any((rel=='nonzero' and vanishes(expr)
                    or rel=='positive' and sign(expr) in (0,-1)
                    or rel=='nonnegative' and sign(expr)==-1) for rel,expr in guard)

    zero=Fraction(0);one=Fraction(1)
    # Forward map (a*x+b)/(c*x+d). Its only possible finite pole must be excluded by the source.
    maps={(one,zero,zero,one)}
    cuts=set()
    for p,d in roots_rational.values():
        if len(p)<=2 and len(d)<=2:
            a,b=(p[1] if len(p)>1 else zero),p[0]
            c,h=(d[1] if len(d)>1 else zero),d[0]
            if a*h!=b*c and (not c or source_hole(-h/c)):maps.add((a,b,c,h))
        if len(p)<=13 and len(d)<=13 and any(p):
            try:points=[v for f in (p,d) for v in rational_roots(f)]
            except Unsupported:continue
            cuts.update(f.a for f in points if f.b==0)
    for pole in sorted(cuts):
        if source_hole(pole):
            maps.update((one,-a,one,-pole) for a in cuts if a!=pole)
    # Start with globally regular coordinates, then try pairs of original poles and zeros.
    for a,b,c,d in sorted(maps,key=lambda row:(bool(row[2]),row!=(one,zero,zero,one),row)):
        for n in sorted({n for n,_ in roots.values()}):
            u=m.power(t,n);inv_d=m.add(q(a),m.mul(q(-c),u))
            inverse=m.div(m.add(m.mul(q(d),u),q(-b)),inv_d)
            jac=m.div(m.mul(q(n*(a*d-b*c)),m.power(t,n-1)),m.power(inv_d,2))
            forward=m.div(m.add(m.mul(q(a),x),q(b)),m.add(m.mul(q(c),x),q(d)))
            coordinate=('cbrt',forward) if n==3 else ('real_odd_root',n,forward)
            try:
                replacements={}
                for atom,(r,radicand) in roots.items():
                    p,s=poly.rf(m.substitute(radicand,{x:inverse}),name)
                    g=poly.pgcd(p,s);p=poly.pdiv(p,g)[0];s=poly.pdiv(s,g)[0]
                    # Reduce the denominator to monic form. Odd roots are unique on the real line.
                    p=tuple(j/s[-1] for j in p);s=tuple(j/s[-1] for j in s)
                    P=polynomial_expression(perfect_odd_polynomial(p,r),name)
                    Q=polynomial_expression(perfect_odd_polynomial(s,r),name)
                    replacements[atom]=m.div(P,Q)
                lowered=m.substitute(m.substitute(raw,replacements),{x:inverse})
                kernel=m.mul(lowered,jac)
                try:
                    p,s=poly.rf(kernel,name)
                    g=poly.pgcd(p,s)
                    kernel=m.div(polynomial_expression(poly.pdiv(p,g)[0],name),polynomial_expression(poly.pdiv(s,g)[0],name))
                except poly.NotRational:
                    if method=='rationalizing_substitution':raise Unsupported('The assigned method requires a rational kernel')
                    require(all(e[0] not in ('ln','asin','acos','atan','rpow') for e in learned_nodes(lowered) if isinstance(e,tuple)),
                            'Additional source restrictions need a separate pullback proof')
            except (Unsupported,poly.NotRational,poly.Undefined,poly.ResourceBound):
                continue
            H=integrate_child(request,kernel,name)
            value=family(raw,m.substitute(H,{t:coordinate}),region=dict(source_conditions=guard,
                         includes_regular_points_with_zero_coordinate=True,root_convention='signed real odd root'))
            return dict(theorem='method.odd_root_projective_pullback',chart='odd_root_rational_coordinate',
                        coordinate=coordinate,inverse=inverse,jacobian=jac,radical_identities=tuple(replacements.items()),
                        kernel=kernel,argument=[
                            'Предлагаем нечётный корень аффинной или дробно-линейной координаты. Любой конечный полюс карты уже исключён исходной областью.',
                            'Выражаем исходную переменную через целую степень координаты. Для каждого радикала точно проверяем степень числителя и знаменателя и используем единственность вещественного нечётного корня.',
                            'Интегрируем полученную плотность и возвращаем исходную переменную. В допустимом нуле координаты непрерывность и теорема о среднем склеивают производную. Исходные ограничения и независимые константы остаются в силе.']),value
    raise Unsupported('No checked real odd-root coordinate')


def positive_affine_inverse_chart(task,request):
    from integrals import affine,family,integrate_child,kernel_symbol,learned_nodes,source
    from model import freeze
    from tasks import domain_conditions
    from verify import same_value
    x,raw,ctx,method=fixed_source(task,TABLE_METHODS|{'integration_by_parts'})
    candidates={}
    for e in learned_nodes(raw):
        if not isinstance(e,tuple) or e[0]!='sqrt' or not m.contains(e,x):continue
        try:a,b=affine(e[1],x[1])
        except Unsupported:continue
        if m.num(a) not in (None,0) and m.num(b) is not None and not domain_conditions(e[1]):
            candidates[e]=(a,b)
    require(len(candidates)==1,'One original square root with a nonconstant affine argument is required')
    coord,(a,b)=next(iter(candidates.items()))
    v=kernel_symbol(task);t=('v',v)
    inverse=m.div(m.add(m.power(t,2),m.neg(b)),a)
    jac=m.div(m.mul(q(2),t),a)
    lowered=m.substitute(raw,{x:inverse,coord:t})
    kernel=m.simplify(m.mul(lowered,jac))
    def inner(e):
        if method=='integration_by_parts':
            task=dict(kind='integrate',variable=v,integrand=source(e),method_requirement=method,
                      requested_output=['primitive_family'])
            return freeze(request('prove integration by parts in the new coordinate',task)['value']['representative'])
        return integrate_child(request,e,v)
    def lift(e):return m.substitute(e,{t:coord})
    argument=['Выбираем исходный неотрицательный корень аффинного выражения и обращаем его. Дифференциал исходной переменной даёт множитель, линейный по новой.',
              'Переносим точные исходные ограничения по этой взаимно однозначной карте. На допустимом краю используем непрерывность и одностороннюю теорему о среднем.']
    folded={e for e in learned_nodes(lowered) if isinstance(e,tuple) and e[0]=='asin'
            and same_value(e[1],m.div(m.mul(q(2),t),m.add(ONE,m.power(t,2))))}
    atom=next(iter(folded)) if len(folded)==1 else None
    if atom and all(g[0]=='nonzero' and same_value(g[1],m.add(ONE,m.power(t,2)))
                    or g[0]=='nonnegative' and same_value(g[1],m.add(ONE,m.neg(m.power(atom[1],2))))
                    for g in domain_conditions(lowered)):
        angle=m.mul(q(2),('atan',t));reflection=m.add(m.PI,m.neg(angle))
        left=inner(m.simplify(m.mul(m.substitute(lowered,{atom:angle}),jac)))
        right=inner(m.simplify(m.mul(m.substitute(lowered,{atom:reflection}),jac)))
        L,R=(m.substitute(z,{t:ONE}) for z in (left,right))
        require(m.constant_defined(L,ctx) and m.constant_defined(R,ctx),'Finite source traces are required for gluing')
        right=m.add(right,m.add(L,m.neg(R)))
        edge=m.div(m.neg(b),a);switch=m.div(m.add(ONE,m.neg(b)),a)
        pieces=(((edge,switch),lift(left)),((switch,None),lift(right))) if m.num(a)>0 else (
                ((None,switch),lift(right)),((switch,edge),lift(left)))
        F=('piecewise_primitive',pieces)
        argument.extend(('Удвоенный арктангенс имеет этот синус. При переходе через единицу его угол пересекает π/2.',
                         'На второй ветви используем отражённый угол и согласуем две первообразные в точке пересечения.'))
    else:F=lift(inner(kernel))
    return dict(theorem='method.nonnegative_affine_root_pullback',chart='positive_affine_inverse_chart',
                coordinate=coord,inverse=inverse,jacobian=jac,kernel=kernel,argument=argument),family(raw,F)


def regular_harmonic_root(task,request):
    """Use the square root itself or a signed half-angle where the differential permits it."""
    from fractions import Fraction
    from math import floor,ceil
    from integrals import affine,family,input_data,integrate_child,kernel_symbol
    from tasks import domain_conditions
    interval=task.get('stated_domain')
    clean=task
    v=task.get('variable','x')
    if interval is not None:
        require(isinstance(interval,dict) and set(interval)=={'kind','left','right'} and interval['kind']=='closed_interval'
                and task.get('stated_conditions')==[f"{interval['left']}<={v}<={interval['right']}"],
                'The original closed interval and displayed bounds must agree')
        clean={**task,'stated_conditions':[],'stated_domain':None}
    x,raw,ctx,method=input_data(clean,TABLE_METHODS)
    require(not ctx['parameters'] and not clean.get('stated_conditions'),'The finite phase and its scales must be fixed')
    if raw[0]=='sqrt':
        root=raw;factor=None
    elif raw[0]=='div' and m.num(raw[1]) is not None and raw[2][0]=='mul':
        a,b=raw[2][1:]
        root,factor=(a,b) if a[0]=='sqrt' else (b,a)
        require(root[0]=='sqrt','An original root factor is required')
    else:raise Unsupported('A single harmonic radical or its reciprocal paired with its phase derivative is required')
    p,d=m.rational_form(root[1]);waves=[(terms,c) for terms,c in p.items() if terms]
    require(not domain_conditions(root[1]) and d=={():1} and len(waves)==1 and len(waves[0][0])==1,
            'A constant plus one harmonic term is required')
    ((wave,j),),B=waves[0];A=p.get((),Fraction(0))
    op,phase=wave
    k,shift=affine(phase,x[1]);rate=m.num(k)
    require(j==1 and op in ('sin','cos') and B and rate and A+abs(B)>0 and not domain_conditions(phase),
            'A nonconstant real affine phase and an admitted sine or cosine wave are required')
    def result(F,steps,**proof):
        return dict(theorem='method.harmonic_radical_coordinates',chart='regular_harmonic_root',
                    argument=steps,source_wave=wave,coefficients=(q(A),q(B)),**proof),family(raw,F,region=interval)
    if factor is not None:
        require(not interval and factor==(('sin' if op=='cos' else 'cos'),phase),
                'The remaining original denominator must be the complementary harmonic factor')
        name=kernel_symbol(task);t=('v',name)
        D=m.add(q(B*B),m.neg(m.power(m.add(m.power(t,2),q(-A)),2)))
        C=q(2*B*m.num(raw[1])*(-1 if op=='cos' else 1)/rate)
        kernel=m.div(C,D);H=integrate_child(request,kernel,name)
        return result(m.substitute(H,{t:root}),[
            'Исходный знаменатель исключает ноль корня и нули дополнительной гармоники.',
            'Дифференцируем квадрат корня. Квадрат дополнительной гармоники заменяем на единицу минус квадрат выделенной.',
            'Получаем рациональную плотность в координате корня и переносим проверенную первообразную на все исходные компоненты.'],
            coordinate=root,kernel=kernel)
    require(interval and A==abs(B),'The harmonic radicand must be an exact square on a finite declared interval')
    L,R=(m.simplify(m.parse(interval[key],None)) for key in ('left','right'))
    l,r=(m.num(m.div(z,m.PI)) for z in (L,R))
    offset=m.num(m.div(shift,m.PI));k2=rate/2
    require(l is not None and r is not None and l<r and offset is not None,
            'Bounds and the phase offset must be rational multiples of pi')
    offset=offset/2-(Fraction(1,4) if B>0 else Fraction(-1,4)) if op=='sin' else offset/2-(Fraction(1,2) if B<0 else Fraction(0))
    u=m.add(m.mul(q(k2),x),m.mul(q(offset),m.PI));amp=('sqrt',q(2*A));base=m.mul(m.div(amp,q(k2)),('sin',u))
    z,w=sorted((k2*l+offset,k2*r+offset))
    require(w-z<=64,'Too many complete half-angle cells')
    cuts=sorted((Fraction(j,1)+Fraction(1,2)-offset)/k2 for j in range(floor(z)-1,ceil(w)+1)
                if z<Fraction(j,1)+Fraction(1,2)<w)
    edges=[l,*cuts,r];pieces=[];acc=ZERO;previous=None
    for lo,hi in zip(edges,edges[1:]):
        sign=(-1)**(floor(k2*(lo+hi)/2+offset+Fraction(1,2))%2)
        if previous is not None:
            trace=(-1)**(int(k2*lo+offset-Fraction(1,2))%2)
            acc=m.add(acc,m.mul(q((previous-sign)*trace/k2),amp))
        expr=m.add(m.mul(q(sign),base),acc)
        pieces.append((tuple(m.mul(q(z),m.PI) for z in (lo,hi)),expr))
        previous=sign
    plan,value=result(('piecewise_primitive',tuple(pieces)),[
        'Полуугол превращает исходный радиканд в квадрат амплитуды, умноженной на косинус.',
        'Нули косинуса точно перечисляем на данном отрезке. На каждом участке знак постоянен, поэтому корень равен подписанному косинусу.',
        'Подбираем постоянные по совпадению следов. Непрерывность исходной плотности обеспечивает относительную производную в точках склейки.'],
        half_angle=u,breakpoints=tuple(map(q,cuts)))
    value['original_domain']=('and',[*domain_conditions(raw),('nonnegative',m.add(x,m.neg(L))),
                                     ('nonnegative',m.add(R,m.neg(x)))])
    return plan,value


def hyperbolic_quadratic_pullback(task,request):
    from integrals import affine,family,learned_nodes
    from tasks import domain_conditions
    from verify import same_value
    x,raw,ctx,_=fixed_source(task)
    require(raw[0]=='sqrt' and not domain_conditions(raw[1]),'A positive quadratic hyperbolic radical is required')
    waves={a for a in learned_nodes(raw) if isinstance(a,tuple) and a[0]=='tanh'}
    require(len(waves)==1,'The original radical must have one hyperbolic tangent phase')
    t,=waves
    k,offset=affine(t[1],x[1]);slope=m.num(k)
    require(slope and m.constant_defined(offset,ctx),'The phase must be fixed affine')
    A=m.simplify(m.substitute(raw[1],{t:ZERO}));B=m.add(m.substitute(raw[1],{t:ONE}),m.neg(A))
    require(m.num(A) is not None and m.num(A)>0 and m.num(B) is not None and m.num(B)>0
            and same_value(raw[1],m.add(A,m.mul(B,m.power(t,2)))),'Both quadratic coefficients must be strictly positive')
    h=m.mul(('sqrt',m.div(B,A)),t);z=('ln',m.add(h,('sqrt',m.add(ONE,m.power(h,2)))))
    w=m.div(m.mul(('sqrt',m.add(A,B)),t),raw)
    atanh=m.mul(q(1,2),('ln',m.div(m.add(ONE,w),m.add(ONE,m.neg(w)))))
    F=m.div(m.add(m.mul(('sqrt',m.add(A,B)),atanh),m.neg(m.mul(('sqrt',B),z))),k)
    return dict(theorem='method.positive_hyperbolic_quadratic_pullback',chart='hyperbolic_quadratic_pullback',
                initial_coordinate=t,second_coordinate=z,final_coordinate=w,quadratic=(A,B),argument=[
        'Подстановка t=tanh(θ) переводит исходную прямую в (−1,1); дифференциал содержит 1−t².',
        'Подстановка t=√(A/B) sinh z превращает радиканд в A cosh² z. Деление даёт постоянный член и ядро 1/(1−(A/B)sinh² z).',
        'Тангенс гиперболический от z рационализует оставшееся ядро. Аргумент обратного гиперболического тангенса по модулю меньше единицы, поскольку |t|<1.']),family(raw,F)
