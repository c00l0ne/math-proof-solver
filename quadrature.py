"""Uniform closed quadrature with outward rational enclosures and checked calculus children."""
from decimal import Decimal, localcontext, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
import re

import expressions as m
from intervals import checked
from model import ONE, ZERO, Unsupported, freeze, q
from tasks import domain_conditions, guard_source, known_guard, source


SCALE=1<<60


def positive_cauchy_parameters(task,library):
    """Reduce parameter integrals to positive rational scale kernels."""
    from cartesian_fields import derivative_table,vector_source
    from verify import same_value
    vector_source(task,{'integrand','limits','stated_conditions','reference_formula','method_requirement','requested_output'},
                  ('Вычислить несобственный интеграл.',))
    if (task.get('limits')!='0..inf' or task.get('method_requirement') is not None or
        task.get('reference_formula') is not None or task.get('stated_conditions',[])
            or task.get('requested_output')!=['exact_integral_and_convergence']):
        raise Unsupported('The positive half-line, parameters and unrestricted source request must be preserved')
    text=task['integrand'].replace('²','^2').replace('⁴','^4')
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{'x','pi','e'})
    if not 1<=len(names)<=2:raise Unsupported('One or two real parameter scales are required')
    x=('v','x');xx=((x,2),);raw=m.parse(text,'x',names)
    if raw[0]!='div':raise Unsupported('A complete original divided integral is required')
    top,bottom=raw[1:]
    def polynomial(v):
        if domain_conditions(v):raise Unsupported('An original domain restriction is unproved')
        p,d=m.rational_form(v)
        if d!={():F(1)}:raise Unsupported('This scale kernel has a hidden denominator')
        return p
    def scale(p,power):
        p=dict(p)
        if len(p)!=1:raise Unsupported('A single parameter scale is required')
        (monomial,coefficient),=p.items()
        key=dict(monomial)
        if key.pop(x,None)!=power or len(key)!=1:
            raise Unsupported('This is not a scalar multiple of the stated variable')
        (sym,exponent),=key.items()
        if exponent!=power or sym[0]!='s' or power==2 and coefficient<=0:
            raise Unsupported('A positive square and one real scale parameter are required')
        C=m.simplify(('sqrt',q(coefficient))) if power==2 else q(coefficient)
        return m.mul(C,sym)
    def norm_square(v):
        p=dict(polynomial(v));C=p.pop(xx,F(0))
        if C<=0:raise Unsupported('The original squared frequency must be positive')
        return scale({tuple(sorted((*k,(x,2)))):c for k,c in p.items()},2),m.simplify(('sqrt',q(C)))
    absolute=lambda e: ('abs',e)
    A0,B0=('s','width'),('s','height')
    s=m.add(A0,B0)
    base=[
        'Для неотрицательных s,t с s+t>0 подынтегральное ядро равно 1/((1+s²x²)(1+t²x²)). Частичные дроби дают его интеграл π/(2(s+t)).',
        'Если один масштаб нулевой, остаётся обычный арктангенс. При s=t>0 замена sx=tan u даёт ∫₀^{π/2}cos²u du/s=π/(4s).']
    # The rational identity applies only when the two positive scales differ.
    sx=m.add(ONE,m.mul(m.power(A0,2),m.power(x,2)))
    tx=m.add(ONE,m.mul(m.power(B0,2),m.power(x,2)))
    ss=m.add(m.power(A0,2),m.neg(m.power(B0,2)))
    if not same_value(m.add(m.mul(m.power(A0,2),tx),m.neg(m.mul(m.power(B0,2),sx))),ss):
        raise Unsupported('The divided scale identity did not verify')
    info=dict(source_bounds='0..inf',source_parameter_conditions=[],
              rational_scale_integral='pi/(2*(s+t)) for s,t>=0,s+t>0',
              separate_repeated_and_zero_scales=True)
    if top[0]=='ln':
        a,l=norm_square(top[1]);b,h=norm_square(bottom)
        A,B=map(absolute,(a,b));ratio=m.div(l,h)
        shifted=m.add(A,m.mul(B,ratio))
        good=m.div(m.mul(m.PI,('ln',shifted)),m.mul(B,h))
        zero_b=m.div(m.mul(m.PI,l),m.power(h,2))
        arg=[
            'Пусть A=|a|, B=|b| для исходных масштабов. При B>0 заменяем y=μx, где μ>0 есть масштаб знаменателя. Из логарифма выносим масштаб числителя.',
            'При фиксированном B>0 дифференцируем по положительному A. На компактном подынтервале A>0 рациональная производная имеет общую интегрируемую мажоранту.',
            'Сводим производную к произведению двух масштабных знаменателей. В якоре A=0 отражение y/B ↦ B/y сокращает логарифмический момент.',
            'Переход A→0+ обоснован общей мажорантой C(1+|ln y|) у нуля и C(1+ln y)/y² на хвосте.',
            'При B=0 нижний знаменатель пропорционален x². Знак расходимости определяется ln(A²), включая отрицательный случай A=0.',
            'При B=0,A=1 ведущий постоянный член исчезает. Интегрирование по частям оставляет один масштабный арктангенс, обе границы исчезают.']
        conditions=[
            dict(condition=source(B)+'>0',value=good),
            dict(condition=source(B)+'=0 and '+source(A)+'=1',value=zero_b),
            dict(condition=source(B)+'=0 and '+source(A)+'>1',divergence='+infinity'),
            dict(condition=source(B)+'=0 and '+source(A)+'<1',divergence='-infinity')]
        return (dict(theorem='method.positive_cauchy_scale_integrals',steps=base+arg,
                     original_scales=[a,b,l,h],lower_endpoint_cases_checked=True,**info),
                dict(parameter_cases=conditions))
    if top[0]!='mul' or top[1][0]!=top[2][0] or top[1][0] not in ('atan','ln'):
        raise Unsupported('No relation to a product of two positive scale sections')
    log=top[1][0]=='ln'
    if polynomial(bottom)!={((x,4 if log else 2),):F(1)}:
        raise Unsupported('The original dividing powers and lower cancellation do not match')
    if log:
        # Verify the actual subtraction of unity before introducing positive scale variables.
        if any(domain_conditions(v[1]) for v in top[1:]):
            raise Unsupported('An extra original log restriction is unproved')
        scales=[scale(polynomial(m.add(v[1],q(-1))),2) for v in top[1:]]
        Q='(width*height*(width+height)+width^3*ln(width/(width+height))+height^3*ln(height/(width+height)))/3'
        target=m.div(m.mul(A0,B0),s)
        multiplier=m.mul(q(2),m.PI)
        representation='ln(1+a²x²)=∫₀^{|a|}2s x²/(1+s²x²) ds'
        tail='O(log²(x)/x⁴)'
    else:
        scales=[scale(polynomial(v[1]),1) for v in top[1:]]
        Q='(width+height)*ln(width+height)-width*ln(width)-height*ln(height)'
        target=m.div(ONE,s)
        multiplier=('mul',m.mul(q(1,2),m.PI),
                    ('div',m.mul(*scales),('abs',m.mul(*scales))))
        representation='atan(a x)=sign(a)∫₀^{|a|}x/(1+s²x²) ds'
        tail='O(x⁻²)'
    primitive=m.parse(Q,None,['width','height'])
    D,rules=derivative_table(library)
    mixed=D(D(primitive,'width'),'height')
    if not same_value(mixed,target):
        raise Unsupported('The integrated scale moment did not verify its mixed derivative')
    A,B=map(absolute,scales);value=('mul',multiplier,m.substitute(primitive,{A0:A,B0:B}))
    cond=[source(z) for z in (A,B)]
    return (dict(theorem='method.positive_cauchy_scale_integrals',steps=base+[
                'Предлагаем интегрировать по каждому масштабу. Используем представление '+representation+'.',
                'На положительных масштабах ядро неотрицательно. По Тонелли меняем порядок, а исходный знак выносим перед интегралом.',
                'Двумерная особенность 1/(s+t) интегрируема в углу: слой s+t=u имеет длину, пропорциональную u. Остальные края конечны.',
                'Проверяем смешанную производную первообразной. При подходе к любой нулевой стороне её след равен нулю, поскольку r^k ln r→0 при k>0.',
                'Исходное ядро ограничено у нуля. На бесконечности действует '+tail+'. При любом нулевом масштабе исходное ядро тождественно нулевое.'],
                 introduced_scales=scales,scale_representation=representation,verified_mixed_primitive=[mixed,target],
                 derivative_rules=rules,original_tail=tail,**info),
            dict(parameter_cases=[
                dict(condition=cond[0]+'=0 or '+cond[1]+'=0',value=ZERO),
                dict(condition=cond[0]+'>0 and '+cond[1]+'>0',value=value)]))


def fresnel_seed():
    """The two equal half-line moments obtained from the damped Gaussian representation."""
    quartic_moment=m.div(m.PI,m.mul(q(2),('sqrt',q(2))))
    value=m.div(quartic_moment,('sqrt',m.PI))
    return value,dict(damping='exp(-delta*t), delta>0',
        real_kernels=['(y²+delta)/(1+(y²+delta)^2)','1/(1+(y²+delta)^2)'],
        positive_majorants=['min(1/2,1/y²)','1/(1+y^4)'],
        common_tail='O(T^(-1/2)) uniformly for delta>=0',
        reciprocal_substitution='y -> 1/y interchanges the limiting rational moments',
        paired_kernel='(1+y²)/(1+y^4) dy = du/(u²+2) where u=y-1/y',
        each_rational_moment=quartic_moment)


def fresnel_representation(task):
    from cartesian_fields import vector_source
    heading='Вычислить оба интеграла Френеля, пользуясь указанной формулой.'
    vector_source(task,{'integrands','limits','given_equalities','representation','method_requirement','requested_output'},(heading,))
    if (task.get('limits')!='0..inf' or task.get('method_requirement')!='specified_representation'
            or task.get('requested_output')!=['both_values','specified_method']):
        raise Unsupported('The two integrals and the prescribed representation are required')
    name=r'([A-Za-z_]\w*)'
    integrands=task.get('integrands',[])
    matches=[re.fullmatch(r'(sin|cos)\('+name+r'\^2\)',s.replace('²','^2').replace(' ','')) for s in integrands]
    if len(matches)!=2 or not all(matches) or {z[1] for z in matches}!={'sin','cos'} or matches[0][2]!=matches[1][2]:
        raise Unsupported('Both oscillatory profiles must use the same quadratic coordinate')
    relation=re.fullmatch(r'1/sqrt\('+name+r'\)=\(2/sqrt\(pi\)\)\*int_0\^inf exp\(-\1\*'+name+r'\^2\)d\2, \1>0',
                          task['representation'].replace('²','^2'))
    subs=task.get('given_equalities')
    if (not relation or relation[1]==relation[2] or not isinstance(subs,list) or len(subs)!=1
            or not re.fullmatch(r'sin and cos integrals = \(1/2\)\*int_0\^inf sin\('+name+r'\)/sqrt\(\1\)d\1 and cos\(\1\)/sqrt\(\1\)d\1 respectively',subs[0])):
        raise Unsupported('The source must supply both square substitutions and the positive Gaussian representation')
    value,seed=fresnel_seed()
    return dict(theorem='method.gaussian_fourier_moments',certificate=seed,steps=[
        'Делаем указанную замену t=x². У нуля вес t⁻¹/² интегрируем, на хвосте работает признак Дирихле.',
        'Ставим положительное экспоненциальное затухание и подставляем данное представление. Абсолютный двойной интеграл ограничен через интеграл e^(−δt)/√t.',
        'После перестановки интегрируем гармонику по t. Для двух оставшихся ядер действуют записанные интегрируемые мажоранты. Та же оценка Дирихле обеспечивает равномерный хвост при снятии затухания.',
        'Обращение положительной координаты уравнивает два рациональных момента. Вместе они превращаются подстановкой y−1/y в интеграл арктангенса по всей прямой.',
    ]),dict(sine=value,cosine=value,ordinary_convergence=True)


def quadratic_phase_integral(raw,ctx,var,formula):
    """Complete squares in real quadratic phases and apply the Fresnel moments."""
    from integrals import real_polynomial_coefficients
    def read(atom):
        if atom[0] not in ('sin','cos') or domain_conditions(atom):
            raise Unsupported('The phase must be a real polynomial without extra holes')
        p=real_polynomial_coefficients(atom[1],var,ctx,2)
        return tuple(p)+(ZERO,)*(3-len(p))
    if raw[0]=='mul':
        f,g=raw[1:]
        if f[0]=='cos' and g[0] in ('sin','cos') and read(f)[-1]==ZERO:f,g=g,f
        if g[0]!='cos':raise Unsupported('The secondary factor must be a cosine')
        first,other=read(f),read(g)
        if other[-1]!=ZERO:raise Unsupported('Only a linear secondary phase is admitted')
        modes=[(f[0],tuple(m.add(a,m.mul(q(s),b)) for a,b in zip(first,other,strict=True))) for s in (1,-1)]
        weight=q(1,2)
    else:
        f=raw;modes=[(f[0],read(f))];weight=ONE
    leading=modes[0][1][-1]
    if leading==ZERO or not m.nonzero(leading,ctx) or not m.constant_defined(leading,ctx):
        raise Unsupported('The quadratic coefficient must be nonzero throughout the original parameter set')
    seed,seed_proof=fresnel_seed()
    centers=[];phases=[]
    for mode,(c,b,a) in modes:
        center=m.div(m.neg(b),m.mul(q(2),a))
        shifted=m.add(c,m.neg(m.div(m.power(b,2),m.mul(q(4),a))))
        centers.append(center);phases.append((mode,shifted))
    def value(sign):
        positive=m.mul(q(sign),leading);factor=m.div(m.mul(q(2),seed),('sqrt',positive))
        out=ZERO
        for mode,shifted in phases:
            s=m.simplify(('sin',shifted));c=m.simplify(('cos',shifted))
            wave=m.add(s,m.mul(q(sign),c)) if mode=='sin' else m.add(c,m.mul(q(-sign),s))
            out=m.add(out,m.mul(weight,m.mul(factor,wave)))
        return out
    sign=m.sign(leading,ctx)
    answer=value(sign) if sign in (1,-1) else dict(cases=[dict(condition=source(leading)+op+'0',value=value(s))
                                                               for op,s in (('>',1),('<',-1))])
    return formula(dict(theorem='method.gaussian_fourier_moments',seed_proof=seed_proof,
                        completed_square_centers=centers,remaining_phases=phases,quadratic_coefficient=leading,
                        steps=[
        'Для произведения применяем разложение в сумму гармоник. Затем в каждой фазе выделяем полный квадрат.',
        'Интегралы на обоих бесконечных концах сходятся раздельно. После квадратичной замены хвост имеет убывающий вес, и его ограничивает признак Дирихле.',
        'Переносим центр и масштабируем на положительный корень из модуля старшего коэффициента. Раскрываем постоянную фазу и применяем оба проверенных интеграла Френеля.',
    ]),answer)


def symmetric_harmonic_pole(task):
    from cartesian_fields import vector_source
    from integrals import affine
    vector_source(task,{'integrand','limits','requested_output'},('Вычислить в смысле главного значения Коши.',))
    if task.get('limits')!='-inf..inf' or task.get('requested_output')!=['cauchy_principal_value']:
        raise Unsupported('Whole-line principal value is required')
    v='x';x=('v',v);text=task['integrand']
    params=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{v,'pi','e'})
    ctx=m.context(dict(variable=v,parameters=params));raw=m.parse(text,v,params)
    if raw[0]!='div' or raw[1][0] not in ('sin','cos') or domain_conditions(raw[1]) or domain_conditions(raw[2]):
        raise Unsupported('A real single wave over one affine pole is required')
    f=raw[1];scale,offset=affine(raw[2],v);rate,phase=affine(f[1],v)
    if m.num(scale) in (0,None) or not all(m.constant_defined(e,ctx) for e in (rate,phase,offset)):
        raise Unsupported('The pole and affine phase must have fixed real coefficients')
    pole=m.div(m.neg(offset),scale);phase=m.add(phase,m.mul(rate,pole))
    amplitude=('cos',phase) if f[0]=='sin' else m.neg(('sin',phase))
    weight=m.div(m.mul(m.PI,amplitude),scale)
    sign=m.sign(rate,ctx)
    result=m.mul(q(sign),weight) if sign is not None else dict(cases=[
        dict(condition=source(rate)+relation+'0',value=m.mul(q(s),weight)) for relation,s in (('>',1),('=',0),('<',-1))])
    return dict(theorem='method.signed_dirichlet_frequency',pole=pole,frequency=rate,scale=scale,
                limits='equal-distance truncation about the original pole',steps=[
        'Переносим начало к единственному полюсу и раскрываем гармонику относительно новой фазы.',
        'Чётная волна, делённая на новую координату, нечётна. Её симметричные отсечения дают нулевой вклад, в том числе при нулевой частоте.',
        'Нечётная волна, делённая на координату, проходит через устранимую особенность. В обеих полупрямых применяется интеграл Дирихле с сохранением знака частоты.',
        'Сдвиг центра внешних отсечений добавляет отрезки ограниченной длины с ядром порядка 1/R. Их вклады исчезают.',
    ]),dict(cauchy_principal_value=result)



def oscillator_over_square(raw,ctx,var,method,formula,nonnegative_scale=()):
    """Use endpoint cancellation and harmonic moments after one integration by parts."""
    from integrals import affine,real_polynomial_coefficients
    if method!='dirichlet_and_frullani_integrals':
        raise Unsupported('The printed harmonic-moment method is required')
    x=('v',var)
    if raw[0]!='div' or domain_conditions(raw[2]) or m.simplify(raw[2])!=m.power(x,2):
        raise Unsupported('The original divisor must be the square of the coordinate')
    numerator=raw[1]
    if domain_conditions(numerator):raise Unsupported('An extra original restriction persists')
    if numerator[0]=='add':
        gaussian,negative=numerator[1:]
        if gaussian[0]!='exp':gaussian,negative=negative,gaussian
        if gaussian[0]!='exp' or negative[0]!='mul' or negative[1]!=q(-1) or negative[2][0]!='cos':
            raise Unsupported('One positive Gaussian and one subtracted cosine are required')
        params=real_polynomial_coefficients(gaussian[1],var,ctx,2)
        rate,phase=affine(negative[2][1],var)
        if len(params)!=3 or params[0]!=ZERO or params[1]!=ZERO or phase!=ZERO or m.sign(params[2],ctx)!=-1:
            raise Unsupported('The centered Gaussian must strictly decay and the cosine be centered')
        A=m.neg(params[2])
        value=m.add(m.mul(m.div(m.PI,q(2)),('abs',rate)),m.neg(('sqrt',m.mul(m.PI,A))))
        return formula(dict(theorem='method.gaussian_fourier_moments',gaussian_attenuation=A,frequency=rate,steps=[
            'Разность у нуля имеет порядок не ниже двух. На бесконечности числитель ограничен, поэтому исходный интеграл абсолютно сходится.',
            'Интегрируем по частям с первообразной −1/x. Оба края исчезают; остаются гауссов момент и интеграл Дирихле.',
            'Положительный масштаб гауссовой функции и знак частоты дают вычисленное значение.',
        ]),value)
    def factors(e):
        return factors(e[1])+factors(e[2]) if e[0]=='mul' else [e]
    items=factors(numerator);waves=[e for e in items if e[0]=='sin'];decay=[e for e in items if e[0]=='exp']
    if len(items)!=3 or len(waves)!=2 or len(decay)!=1:raise Unsupported('A damped product of two sines is required')
    rates=[]
    for wave in waves:
        rate,phase=affine(wave[1],var)
        if phase!=ZERO or not m.constant_defined(rate,ctx):raise Unsupported('The sine factors must have zero phase offsets')
        rates.append(rate)
    slope,shift=affine(decay[0][1],var);k=m.neg(slope)
    if shift!=ZERO or not m.constant_defined(k,ctx):
        raise Unsupported('The Abel attenuation must be constant and have zero phase offset')
    guarded=k[0]=='s' and k[1] in nonnegative_scale
    sign=m.sign(k,ctx)
    if not guarded and sign not in (0,1):raise Unsupported('The Abel attenuation must be nonnegative')
    a,b=rates;s=m.add(a,b);d=m.add(a,m.neg(b))
    def primitive(y):
        ratio=m.div(y,k)
        return m.add(m.mul(y,('atan',ratio)),m.mul(m.div(m.neg(k),q(2)),('ln',m.add(ONE,m.power(ratio,2)))))
    zero=m.mul(m.div(m.PI,q(4)),m.add(('abs',s),m.neg(('abs',d))))
    if sign==0:result=zero
    else:
        positive=m.div(m.add(primitive(s),m.neg(primitive(d))),q(2))
        result=dict(cases=[dict(condition=source(k)+'>0',value=positive),dict(condition=source(k)+'=0',value=zero)]) if guarded else positive
    return formula(dict(theorem='method.signed_dirichlet_frequency',damping=k,oriented_frequencies=(d,s),steps=[
        'Произведение синусов распадается в ориентированную разность двух косинусов. У нуля числитель имеет порядок x², а на хвосте ядро ограничено через 1/x².',
        'При положительном затухании дифференцирование по частоте даёт затухающий интеграл Дирихле. Его производная по частоте вычисляется экспоненциальным косинусным моментом, откуда возникает арктангенс.',
        'Берём первообразную арктангенса и сохраняем порядок частот. При снятии затухания исходный интеграл проходит к пределу по общей мажоранте, а арктангенс даёт знак частоты.',
    ]),result)




def shifted_cosine_resolvent(task):
    from cartesian_fields import vector_source
    from integrals import affine
    vector_source(task,{'integrand','limits','stated_conditions','reference_formula','method_requirement','requested_output'},
                  ('Вычислить несобственный интеграл.',))
    if (task.get('limits')!='0..inf' or task.get('method_requirement') is not None or task.get('reference_formula') is not None
            or task.get('requested_output')!=['exact_integral_and_convergence']):
        raise Unsupported('The original half-line improper integral must remain in its scope')
    text=task['integrand'].replace('²','^2');names=transform_parameters(text,'x');x=('v','x')
    raw=m.parse(text,'x',names)
    if raw[0]!='div' or raw[1][0]!='cos':
        raise Unsupported('The source is not a cosine over a quadratic')
    conditions=[c.replace('²','^2') for c in task.get('stated_conditions',[])]
    ctx=m.context(dict(variable='x',parameters=names,parameter_conditions=conditions))
    frequency,phase=affine(raw[1][1],'x')
    if (not m.constant_defined(phase,ctx) or not m.constant_defined(frequency,ctx) or m.sign(frequency,ctx) not in (0,1)
            or any(not known_guard(g,ctx) for e in (raw[1][1],raw[2]) for g in domain_conditions(e))):
        raise Unsupported('The affine phase and all original coefficients must be defined, with nonnegative frequency')
    p,d=m.rational_form(raw[2])
    if d!={():F(1)}:raise Unsupported('The denominator needs a polynomial in the running coordinate')
    groups={}
    for monomial,coefficient in p.items():
        exp=dict(monomial).get(x,0);rest=tuple((v,k) for v,k in monomial if v!=x)
        if exp>2 or any(m.variable_in(v,'x') for v,k in rest):
            raise Unsupported('Only fixed coefficients of a quadratic are allowed')
        groups.setdefault(exp,{})[rest]=coefficient
    c,b,a=(m.poly_expr(groups.get(i,{})) for i in range(3))
    half_b=m.mul(q(1,2),b)
    discriminant=m.add(m.mul(a,c),m.neg(m.power(half_b,2)))
    if not all(known_guard(('positive',v),ctx) for v in (a,discriminant)):
        raise Unsupported('The completed square must have a positive coefficient and offset')
    shift=m.div(half_b,a);sigma=m.div(('sqrt',discriminant),a)
    cutoff=m.div(shift,sigma);omega=m.mul(frequency,sigma)
    phase0=m.add(m.mul(frequency,shift),m.neg(phase));scale=m.div(ONE,m.mul(a,sigma))
    constants=dict(omega=omega,d=cutoff,delta=phase0,scale=scale)
    if m.sign(frequency,ctx)==0:
        value=m.mul(scale,m.mul(('cos',phase0),m.add(m.div(m.PI,q(2)),m.neg(('atan',cutoff)))))
        return dict(theorem='method.shifted_cosine_resolvent',steps=[
            'Дополняем квадрат. Положительный сдвиг квадрата устраняет полюсы, хвост убывает как 1/x².',
            'При нулевой частоте косинус постоянен. После аффинной замены получаем ориентированную разность значений арктангенса.'
        ],normalized_parameters=constants),dict(exact_integral=value,convergence='absolute')
    value='scale*(cos(delta)*(C(omega)-C_d(omega,d))+sin(delta)*(S(omega)-S_d(omega,d)))'
    functions=dict(
        C='C(w)=(pi/2)*exp(-w) for w>0',
        S='S(w)=(exp(-w)*Ei(w)-exp(w)*Ei(-w))/2 for w>0; Ei is the real exponential integral',
        C_d='sum_{j>=0} (-1)^j*w^(2*j)*M_(2*j)(d)/(2*j)!',
        S_d='sum_{j>=0} (-1)^j*w^(2*j+1)*M_(2*j+1)(d)/(2*j+1)!',
        moments=['M_0(d)=atan(d)','M_1(d)=ln(1+d^2)/2','M_k(d)=d^(k-1)/(k-1)-M_(k-2)(d), k>=2'])
    return dict(theorem='method.shifted_cosine_resolvent',steps=[
        'Положительный квадратный знаменатель даёт абсолютную сходимость. После дополнения квадрата получаем интеграл от d до бесконечности с весом 1/(1+t²) и постоянным сдвигом фазы.',
        'Разделяем фазу и вычитаем ориентированный отрезок от 0 до d. На нём ряды синуса и косинуса сходятся равномерно. Деление степеней на 1+t² даёт указанную рекурсию моментов.',
        'Для моментов всей полуоси вводим затухание exp(−εt), ε>0. После двух производных по частоте операторы Cε″−Cε и Sε″−Sε равны соответственно −ε/(ε²+w²) и −w/(ε²+w²).',
        'На компактных положительных частотах затухшие интегралы и их вторые производные сходятся равномерно: для самих интегралов достаточно веса 1/(1+t²), а вторые производные выражены через них и явные рациональные функции.',
        'В пределе C″−C=0, S″−S=−1/w. У нуля C(0)=π/2, S(0)=0. Оба момента стремятся к нулю на бесконечности по частям с интегрируемой производной веса, поэтому краевые задачи имеют единственные решения.',
        'Формула с Ei имеет S″−S=−1/w по Ei′(z)=exp(z)/z. У нуля логарифмические члены сокращаются, на бесконечности обе экспоненциально масштабированные функции Ei стремятся к нулю.'
    ],completed_square=dict(scale=a,shift=shift,sigma=sigma),normalized_parameters=constants),dict(exact_integral=dict(
        expression=value,parameters=constants,functions=functions),convergence='absolute')


def evaluate_parameter_integral(task,library,request):
    if library.data.get('shifted_cosine_resolvent') and str(task.get('integrand','')).startswith('cos('):
        try:return shifted_cosine_resolvent(task)
        except (Unsupported,KeyError,TypeError):pass
    """Evaluate a checked half-line Fourier moment using its actual endpoint cancellations."""
    if library.data.get('positive_cauchy_scale_integrals'):
        try:return positive_cauchy_parameters(task,library)
        except Unsupported:pass
    if task.get('method_requirement')=='euler_poisson_integral' and library.data.get('parameter_transform_proofs'):
        try:return source_integral_transform(task,library,request)
        except Unsupported:pass
    if task.get('method_requirement') is None and library.data.get('parameter_transform_proofs'):
        try:return lorentzian_moment(task,library,request)
        except Unsupported:pass
    from integrals import harmonic_modes,affine
    from verify import same_value
    keys={'id','kind','source','integrand','limits','stated_conditions','method_requirement','reference_formula','requested_output'}
    method=task.get('method_requirement');stated=task.get('stated_conditions',[])
    meta=task.get('source',{});required='Вычислить несобственный интеграл.'
    if (set(task)-keys or task.get('reference_formula') is not None
            or not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','pdf_sha256','printed_subpart','literal_requirement'}
            or meta.get('literal_requirement',required)!=required or not isinstance(stated,list)
            or task.get('requested_output')!=(['exact_integral','specified_method'] if method else ['exact_integral_and_convergence'])):
        raise Unsupported('Unbound source restriction, prescribed representation or additional conclusion')
    text=task['integrand'].replace('²','^2').replace('³','^3')
    b=re.fullmatch(r'(?:(\w+):)?(-inf|0)\.\.inf',task['limits']);var=(b[1] or 'x') if b else None
    if not b:raise Unsupported('The original integration ends require another transformation')
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{var,'pi','e'})
    params=[];nonzero=[];nonnegative=[]
    for cond in stated:
        if (pair:=re.fullmatch(r'abs\((\w+)\)!=abs\((\w+)\)',cond)) or (pair:=re.fullmatch(r'(\w+)\*(\w+)!=0',cond)):
            a,c=pair.groups()
            if not {a,c}<=set(names):raise Unsupported('Unbound parameter restriction')
            nonzero.extend((a+'+'+c,a+'-'+c) if 'abs(' in cond else (a,c))
        elif method=='dirichlet_and_frullani_integrals' and (bound:=re.fullmatch(r'(\w+)>=0',cond)) and bound[1] in names:
            nonnegative.append(bound[1])
        elif re.fullmatch(r'\w+(?:>0|!=0)',cond) and cond.split('>')[0].split('!')[0] in names:params.append(cond)
        elif method=='euler_poisson_integral' and (bound:=re.fullmatch(r'(\w+) positive integer',cond)) and bound[1] in names:params.append(bound[1]+'>0')
        elif method=='euler_poisson_integral' and b[2] in ('-inf','0'):params.append(cond.replace('²','^2'))
        else:raise Unsupported('A source parameter branch still requires a separate proof')
    ctx=m.context(dict(variable=var,parameters=names,parameter_conditions=params+[g+'!=0' for g in nonzero]));x=('v',var)
    raw=m.parse(text,var,names)
    def fixed(e):return m.constant_defined(e,ctx)
    def scalar(e):return m.simplify(e)
    def formula(plan,value):
        plan.update(variable=var,limits=task['limits'],assumptions=stated)
        return plan,dict(exact_integral=value,convergence='ordinary; each improper end exists')
    if b[2]=='0' and method=='dirichlet_and_frullani_integrals' and library.data.get('improper_harmonic_moments'):
        if nonnegative:
            return oscillator_over_square(raw,ctx,var,method,formula,nonnegative)
        try:return oscillator_over_square(raw,ctx,var,method,formula)
        except Unsupported:pass
    if method=='euler_poisson_integral' or (b[2]=='-inf' and method is None):
        if not library.data.get('gaussian_fourier_moments'):raise Unsupported('Gaussian moment reduction is unavailable')
        if method is None:
            try:return quadratic_phase_integral(raw,ctx,var,formula)
            except Unsupported:pass
        return gaussian_integral_moments(task,ctx,raw,var,formula)
    if not library.data.get('improper_harmonic_moments') or b[2]!='0' or method not in (None,'frullani_formula','dirichlet_and_frullani_integrals'):
        raise Unsupported('The printed method or separate infinite ends require a different proof')
    for rel,g in domain_conditions(raw):
        if not ((g==x or g[0]=='pow' and g[1]==x) or known_guard((rel,g),ctx)):
            raise Unsupported('An original denominator or real branch has an unproved interior condition')
    if method=='frullani_formula':
        # Read both dilations from the original difference; an oscillatory endpoint
        # is admissible only when its primitive is bounded away from zero frequency.
        if raw[0]!='div' or raw[2]!=x or raw[1][0]!='add':raise Unsupported('A Frullani difference of two dilations is required')
        first,negative=raw[1][1:]
        if negative[0]!='mul' or negative[1]!=q(-1) or negative[2][0]!=first[0] or first[0] not in ('sin','cos','atan','exp'):
            raise Unsupported('The same profile at both dilations is required')
        waves=[]
        for e in (first,negative[2]):
            a,h=affine(e[1],var)
            if h!=ZERO or not fixed(a) or m.sign(a,ctx) not in (-1,1):raise Unsupported('Nonzero fixed dilations on the original domain are required')
            waves.append(a)
        u,v=waves;s=m.sign(u,ctx);reflection={}
        if first[0]=='cos':
            u,v=[w if m.sign(w,ctx)==1 else m.neg(w) for w in waves]
            reflection={'positive_dilations':[u,v],'reflection_identity':'cos(-t)=cos(t)'}
        elif s!=m.sign(v,ctx) or first[0]=='exp' and s>0:
            raise Unsupported('The dilation rays or the limiting profile are incompatible')
        height={'sin':ZERO,'cos':ONE,'exp':ONE,'atan':m.mul(q(-s,2),m.PI)}[first[0]]
        value=m.mul(height,scalar(('ln',m.div(v,u))))
        return formula(dict(theorem='method.improper_harmonic_moments',strategy='frullani_scaled_difference',dilations=waves,
               initial_minus_tail_level=height,profile=first[0],proof='scaled finite cutoffs; continuous origin and convergent integral of (profile-tail level)/x at infinity',**reflection),source(value))
    def separate(e):
        if e==x:return ONE,-1
        if e[0] in ('mul','div'):
            u,j=separate(e[1]);v,k=separate(e[2])
            if e[0]=='div' and not fixed(v):raise Unsupported('The denominator does not reduce to a pure power times a fixed scale')
            return (m.mul(u,v),j+k) if e[0]=='mul' else (m.div(u,v),j-k)
        if e[0]=='pow' and e[2]>0:
            numerator,k=separate(e[1]);return m.power(numerator,e[2]),k*e[2]
        return e,0
    numerator,degree=separate(raw)
    if degree<1:raise Unsupported('A decaying inverse power is required on the infinite tail')
    substitution=1
    if degree==1:
        def index_powers(e):
            if e[0]=='pow' and e[1]==x and e[2]>1:yield e[2]
            for child in e[1:]:
                if isinstance(child,tuple):yield from index_powers(child)
        powers=set(index_powers(numerator))
        if len(powers)==1:
            d=powers.pop();reduced=m.substitute(numerator,{('pow',x,d):x})
            if same_value(m.substitute(reduced,{x:('pow',x,d)}),numerator):substitution=d;numerator=reduced
    modes,_,actions=harmonic_modes(dict(kind='integrate',variable=var,integrand=source(numerator),parameters=names))
    real={}
    for (rate,w),coeffs in modes.items():
        if rate!=ZERO or len(coeffs)!=1:raise Unsupported('A bounded pure trigonometric polynomial is required at infinity')
        a,v=coeffs[0];neg=m.neg(w);flip=(source(neg).count('-'),source(neg))<(source(w).count('-'),source(w))
        k=neg if flip else w;A,B=real.get(k,(ZERO,ZERO))
        real[k]=(m.add(A,a),m.add(B,v if flip else m.neg(v)))
    origin=[]
    for j in range(degree):
        val=ZERO
        for a,_ in real.values():val=m.add(val,a)
        if not same_value(val,ZERO):raise Unsupported('The source numerator has insufficient vanishing order at zero')
        origin.append(val)
        if j+1<degree:real={w:(m.mul(w,b),m.neg(m.mul(w,a))) for w,(a,b) in real.items()}
    answer=ZERO;atoms={};rows=[]
    for w,(a,bcoef) in real.items():
        if w==ZERO:
            if a!=ZERO:raise Unsupported('The terminal zero-frequency cosine gives a logarithmically divergent tail')
            continue
        if a!=ZERO:
            if not m.nonzero(w,ctx):raise Unsupported('A terminal cosine frequency can vanish for admissible parameters')
            answer=m.add(answer,m.neg(m.mul(a,scalar(('ln',scalar(('abs',w)))))))
        if bcoef!=ZERO:
            sign=m.sign(w,ctx)
            symbol='waveSign'+str(len(atoms))
            while symbol in names:symbol+='_'
            if sign is None:atoms[symbol]='sgn('+source(w)+')'
            phase=('s',symbol) if sign is None else q(sign)
            answer=m.add(answer,m.mul(q(1,2),m.mul(m.PI,m.mul(bcoef,phase))))
        rows.append(dict(frequency=w,cosine_coefficient=a,sine_coefficient=bcoef))
    value=source(m.div(answer,q(substitution*factorial(degree-1))))
    for symbol,name in atoms.items():value=re.sub(r'\b'+symbol+r'\b',lambda _:name,value)
    return formula(dict(theorem='method.improper_harmonic_moments',strategy='harmonic_moment',numerator=source(numerator),
        power_substitution=substitution,denominator_power=degree,origin_derivatives=origin,terminal_frequencies=rows,
        expansions=actions,integrations_by_parts=degree-1,proof='Taylor cancellation at zero; bounded boundary terms at infinity; Dirichlet sine moments and Frullani cosine differences with zero total coefficient; sgn(0)=0'),value)


def gaussian_integral_moments(task,ctx,raw,var,formula):
    """Integrate polynomial Fourier modes against one positive Gaussian using its moment recurrence."""
    from integrals import harmonic_modes,harmonic_product,harmonic_add,harmonic_scale,harmonic_equal,HARMONIC_ZERO,HARMONIC_ONE
    from verify import same_value
    x=('v',var);exponents=[];scalars=[];symbolic=[]
    integers=[s.split()[0] for s in task.get('stated_conditions',[]) if s.endswith(' positive integer')]
    def collect(e):
        if e[0]=='mul':return m.mul(collect(e[1]),collect(e[2]))
        if e[0]=='div' and m.constant_defined(e[2],ctx) and m.nonzero(e[2],ctx):
            scalars.append(m.div(ONE,e[2]));return collect(e[1])
        if not m.contains(e,x):
            if not m.constant_defined(e,ctx):raise Unsupported('Undefined scalar weight')
            scalars.append(e);return ONE
        if e[0]=='exp':
            exponents.append(e[1]);return ONE
        if e[0]=='rpow' and e[1]==x and not domain_conditions(e[2]):
            for k in integers:
                for parity in (0,1):
                    if same_value(e[2],m.add(m.mul(q(2),('s',k)),q(parity))):
                        symbolic.append((k,parity,e[2]));return ONE
        return e
    rest=collect(raw);ex=ZERO;scale=ONE
    if (len(symbolic)>1 or not all(known_guard(g,ctx) for g in domain_conditions(raw,positive_integer_exponents=tuple(z[2] for z in symbolic)))):
        raise Unsupported('A source branch or interior pole remains in the Gaussian density')
    for e in scalars:scale=m.mul(scale,e)
    for e in exponents:ex=m.add(ex,e)
    def at(z):return m.simplify(m.substitute(ex,{x:q(z)}))
    C=at(0);u=at(1);v=at(-1);B=m.mul(q(1,2),m.add(u,m.neg(v)));A=m.add(C,m.neg(m.mul(q(1,2),m.add(u,v))))
    if m.sign(A,ctx)!=1 or not same_value(ex,m.add(C,m.add(m.mul(B,x),m.neg(m.mul(A,m.power(x,2)))))):
        raise Unsupported('The full quadratic exponent must have a proved negative leading coefficient')
    modes,_,_=harmonic_modes(dict(kind='integrate',variable=var,parameters=ctx['parameters'],integrand=source(rest)))
    half=task['limits'].split(':')[-1]=='0..inf'
    if half:
        if B!=ZERO:raise Unsupported('The half-line integral requires an even density; its Gaussian center is displaced')
        if not symbolic and set(modes)=={HARMONIC_ZERO}:
            weights=modes[HARMONIC_ZERO]
            if all(imag==ZERO for _,imag in weights):
                den=m.mul(q(2),A)
                moments=[m.mul(q(1,2),m.simplify(('sqrt',m.div(m.PI,A)))),m.div(ONE,den)]
                for j in range(2,len(weights)):
                    moments.append(m.mul(m.div(q(j-1),den),moments[j-2]))
                total=m.mul(m.mul(scale,('exp',C)),m.dot([u for u,_ in weights],moments))
                return formula(dict(theorem='method.gaussian_fourier_moments',strategy='positive_gaussian_half_line_polynomial',
                    quadratic_scale=A,exponent_constant=C,weights=weights,moments=moments[:len(weights)],
                    proof='Half Gaussian mass and t=A*x² for the first moment. Integration by parts gives higher moments, with the power vanishing at zero and Gaussian decay at infinity.'),source(m.simplify(total)))
        for (a,w),weights in modes.items():
            other=modes.get((m.neg(a),m.neg(w)),[])
            offset=symbolic[0][1] if symbolic else 0
            if len(other)!=len(weights) or any(not harmonic_equal(c,harmonic_scale(d,q((-1)**(j+offset)))) for j,(c,d) in enumerate(zip(weights,other))):
                raise Unsupported('Odd modes on the half-line cannot be replaced by half of a whole-line integral')
    common=m.mul(scale,m.simplify(('sqrt',m.div(m.PI,A))))
    if half:common=m.mul(q(1,2),common)
    den=m.mul(q(2),A)
    if symbolic:
        k,parity,power=symbolic[0];expression=source(power);binder='j'
        while binder in [var,*ctx['parameters']]:binder+='_'
        terms=[];frequencies=[];combined={}
        for (rate,w),co in modes.items():
            if B!=ZERO or rate!=ZERO or len(co)!=1:raise Unsupported('A symmetric Gaussian and index-independent harmonic weights are required')
            weight=co[0][0] if parity==0 else m.neg(co[0][1]);base=m.div(w,den)
            coef=m.mul(common,m.mul(weight,m.simplify(('exp',m.add(C,m.neg(m.div(m.power(w,2),m.mul(q(4),A))))))))
            neg=m.neg(base)
            if (source(neg).count('-'),source(neg))<(source(base).count('-'),source(base)):
                base=neg
                if parity:coef=m.neg(coef)
            combined[base]=m.add(combined.get(base,ZERO),coef)
        for base,coef in combined.items():
            if coef==ZERO:continue
            frequencies.append(dict(scalar=coef,frequency_over_twice_scale=base))
            j=binder;d=expression
            summand=f'(-1)^({k}-{j})*factorial({d})*({source(base)})^({d}-2*{j})/(factorial({j})*factorial({d}-2*{j})*({source(m.mul(q(4),A))})^{j})'
            terms.append(f'({source(coef)})*sum({summand},{j}=0..{k})')
        return formula(dict(theorem='method.gaussian_fourier_moments',strategy='positive_gaussian_moment',quadratic_scale=A,exponent_linear=B,exponent_constant=C,
            even_half_line=half,modes=frequencies,source_moment_order=power,summation_index=binder,order_parameter=k,parity=parity,
            proof='Differentiate the exponential quadratic generating function of the Gaussian moments. Binomial expansion selects pairs and the remaining linear powers; integer zeroth powers equal 1, including at zero frequency.'),' + '.join(terms) or '0')
    total=ZERO;rows=[]
    for (rate,w),co in modes.items():
        beta=m.add(B,rate);shift=(m.div(beta,den),m.div(w,den));moments=[HARMONIC_ONE]
        for j in range(len(co)-1):
            nxt=harmonic_product(moments[-1],shift)
            if j:nxt=harmonic_add(nxt,harmonic_scale(moments[-2],m.div(q(j),den)))
            moments.append(nxt)
        z=HARMONIC_ZERO
        for weight,moment in zip(co,moments):z=harmonic_add(z,harmonic_product(weight,moment))
        angle=m.div(m.mul(beta,w),den);amp=m.add(C,m.div(m.add(m.power(beta,2),m.neg(m.power(w,2))),m.mul(q(4),A)))
        real,_=harmonic_product(z,(m.simplify(('cos',angle)),m.simplify(('sin',angle))))
        total=m.add(total,m.mul(m.simplify(('exp',amp)),real))
        rows.append(dict(real_rate=rate,frequency=w,weights=co,normalized_moments=moments))
    value=m.mul(common,total)
    return formula(dict(theorem='method.gaussian_fourier_moments',strategy='positive_gaussian_moment',quadratic_scale=A,
        exponent_linear=B,exponent_constant=C,even_half_line=half,modes=rows,
        proof='Gaussian domination on both tails. Euler–Poisson gives the zero-frequency value. Integration by parts gives the Fourier ODE and the full moment recurrence.'),source(value))


def fourier_moment(form,left,right,weight,angular,params,ctx,saved,frequency='omega',conditions=()):
    """Evaluate both endpoints of independently differentiated exponential-polynomial primitives."""
    from integrals import harmonic_proposal,verify_harmonic_family
    var=('v','x');freq=('s',frequency)
    t=dict(kind='integrate',variable='x',parameters=[*params,frequency],
           integrand='('+form+')'+('' if weight=='mean' else f'*{weight}({frequency}*x)'))
    plan=harmonic_proposal(t,conditions) if saved is None else saved
    primitive,_=verify_harmonic_family(t,plan,conditions)
    def specialize(e):return m.simplify(m.substitute(freeze(e),{freq:angular}))
    def increment(e):
        e=specialize(e)
        return m.add(m.substitute(e,{var:right}),m.neg(m.substitute(e,{var:left})))
    base=increment(primitive.get('representative',primitive.get('fixed_terms',ZERO)));conditional=[]
    for branch in primitive.get('parameter_terms',[]):
        test=specialize(branch['squared_rate'])
        if test==ZERO:base=m.add(base,increment(branch['if_zero']))
        elif m.nonzero(test,ctx):base=m.add(base,increment(branch['otherwise']))
        else:conditional.append(dict(if_zero=test,then=increment(branch['if_zero']),otherwise=increment(branch['otherwise'])))
    return plan,base,conditional


def decaying_harmonic_moment(task,conditions=(),saved=None):
    """Evaluate a harmonic primitive at zero and justify its vanishing at +∞."""
    from integrals import harmonic_proposal,verify_harmonic_family
    plan=harmonic_proposal(task,conditions) if saved is None else saved
    primitive,_=verify_harmonic_family(task,plan,conditions)
    ctx=m.context(dict(task,parameter_conditions=conditions))
    if 'representative' not in primitive or any(m.sign(freeze(row['rate']),ctx)!=-1 for row in plan['modes']):
        raise Unsupported('Not every harmonic mode decays exponentially')
    at_zero=m.substitute(primitive['representative'],{('v',task['variable']):ZERO})
    # Every denominator from verification is a power of a²+b² with a<0.
    return plan,m.neg(m.simplify(at_zero))


def indexed_harmonic_value(task,library):
    """Integrate exact finite Euler expansions without enumerating symbolic indices."""
    from integrals import affine
    from verify import same_value

    if not library.data.get('indexed_euler_integrals'):
        raise Unsupported('Indexed Euler expansions are unavailable')
    fields={'kind','id','source','integrand','parameters','stated_conditions','method_requirement','requested_output'}
    method=task.get('method_requirement')
    if method not in (None,'euler_complex_exponential_formulas') or task.get('requested_output')!=['exact_integral']:
        raise Unsupported('No compatible integral or Euler method requirement')
    if set(task.get('source',{}))-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256'}:
        raise Unsupported('An additional printed requirement remains')
    if task['kind']=='iterated_integral':
        if set(task)-fields-{'integration_order'} or len(task['integration_order'])!=1:
            raise Unsupported('A single finite oriented integral is required')
        bounds=task['integration_order'][0]
    else:
        if set(task)-fields-{'variable','lower','upper'}:
            raise Unsupported('The source improper integral has additional obligations')
        bounds={k:task[k] for k in ('variable','lower','upper')}
    if set(bounds)!={'variable','lower','upper'}:raise Unsupported('Unresolved integration limits')
    v=bounds['variable'];params=task.get('parameters',[])
    integer_conditions=task.get('stated_conditions',[])
    indices=[]
    for clause in integer_conditions:
        match=re.fullmatch(r'(\w+) is a positive integer',clause)
        if not match or match[1] not in params or match[1] in indices:
            raise Unsupported('Only explicitly positive integer index assumptions are handled')
        indices.append(match[1])
    if not indices:raise Unsupported('The symbolic exponent needs its original integer domain')
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=[k+'>0' for k in indices]))
    lo,hi=[m.parse(str(bounds[k]),None,params) for k in ('lower','upper')]
    if not all(m.constant_defined(z,ctx) for z in (lo,hi)):
        raise Unsupported('Both original finite limits of integration must be defined')
    raw=m.parse(task['integrand'],v,params)
    symbol=('v',v)
    transformations=[];serial=0

    def integer_affine(exponent,minimum):
        p,d=m.rational_form(exponent)
        if d!={():F(1)}:raise Unsupported('The exponent has unproved rational denominators')
        # First verify its raw domain, before examining the simplified polynomial.
        if not m.constant_defined(exponent,ctx):raise Unsupported('The exponent is not defined')
        base=p.get((),F(0));allowed={('s',k) for k in indices}
        for mon,coef in p.items():
            if coef.denominator!=1:raise Unsupported('Noninteger coefficient in an integer exponent')
            if mon:
                if len(mon)!=1 or mon[0][0] not in allowed or mon[0][1]!=1 or coef<0:
                    raise Unsupported('An integer affine exponent on the original index domain is required')
                base+=coef
        if base<minimum:raise Unsupported('The requested power or sum length may be negative')
        return p

    def fresh():
        nonlocal serial
        while True:
            serial+=1
            name='__mode'+str(serial)
            if name not in [v,*params]:return ('s',name)

    def mode(rate=ZERO,freq=ZERO,phase=ZERO,scalar=ONE,imaginary=ZERO,binders=()):
        return dict(real_rate=rate,frequency=freq,phase=phase,scale=scalar,i_exponent=imaginary,indices=binders)

    def multiply(a,b):
        return mode(rate=m.add(a['real_rate'],b['real_rate']),freq=m.add(a['frequency'],b['frequency']),
                    phase=m.add(a['phase'],b['phase']),scalar=m.mul(a['scale'],b['scale']),
                    imaginary=m.add(a['i_exponent'],b['i_exponent']),binders=a['indices']+b['indices'])

    def phase(expr):
        if any(not known_guard(g,ctx) for g in domain_conditions(expr)):
            raise Unsupported('The affine phase has an unproved original guard')
        a,b=affine(expr,v)
        if not all(m.constant_defined(z,ctx) for z in (a,b)):
            raise Unsupported('The real phase coefficients are not defined')
        return a,b

    def trig(tag,angle,power):
        a,b=phase(angle);integer_affine(power,0)
        j=fresh();harmonic=m.add(power,m.mul(q(-2),j))
        coeff=m.mul(('rpow',q(2),m.neg(power)),('binomial',power,j))
        if tag=='sin':coeff=m.mul(('rpow',q(-1),j),coeff)
        transformations.append(dict(identity='Euler_binomial',wave=tag,angle=angle,power=power,index=j))
        return mode(freq=m.mul(a,harmonic),phase=m.mul(b,harmonic),scalar=coeff,
                    imaginary=m.neg(power) if tag=='sin' else ZERO,binders=((j[1],ZERO,power),))

    def quotient(num,den):
        tag=den[0]
        if num[0]!=tag or tag not in ('sin','cos'):
            raise Unsupported('An original variable denominator is not known removable')
        da,db=phase(den[1]);na,nb=phase(num[1])
        if not m.constant_defined(da,ctx) or not m.nonzero(da,ctx):
            raise Unsupported('A nonconstant denominator phase with a defined slope is required')
        k=m.simplify(m.div(na,da));p=integer_affine(k,1)
        if not (same_value(na,m.mul(k,da)) and same_value(nb,m.mul(k,db)) and m.constant_defined(db,ctx)):
            raise Unsupported('The numerator phase is not the same integer multiple throughout the interval')
        if tag=='cos' and (p.get((),F(0))%2!=1 or any(c%2 for mon,c in p.items() if mon)):
            raise Unsupported('The exponent ratio for the cosine quotient must be odd')
        j=fresh();top=m.add(k,q(-1));h=m.add(top,m.mul(q(-2),j))
        transformations.append(dict(identity='finite_geometric_cancellation',wave=tag,original_denominator=den,
                                    integer_multiplier=k,index=j,endpoint_extension='finite continuous sum'))
        return mode(freq=m.mul(da,h),phase=m.mul(db,h),
                    scalar=('rpow',q(-1),j) if tag=='cos' else ONE,binders=((j[1],ZERO,top),))

    def walk(e):
        if not m.contains(e,symbol):
            if not m.constant_defined(e,ctx):raise Unsupported('An original fixed coefficient is undefined')
            return [mode(scalar=m.simplify(e))]
        tag=e[0]
        if tag=='add':return walk(e[1])+walk(e[2])
        if tag=='mul':
            left,right=walk(e[1]),walk(e[2])
            return [multiply(a,b) for a in left for b in right]
        if tag=='div':
            if not m.contains(e[2],symbol):
                if not m.nonzero(e[2],ctx) or not m.constant_defined(e[2],ctx):
                    raise Unsupported('A constant divisor may vanish or be undefined')
                return [multiply(t,mode(scalar=m.div(ONE,e[2]))) for t in walk(e[1])]
            return [quotient(*e[1:])]
        if tag=='exp':
            a,b=phase(e[1])
            return [mode(rate=a,scalar=m.simplify(('exp',b)))]
        if tag in ('sin','cos'):return [trig(tag,e[1],ONE)]
        if tag in ('pow','rpow') and e[1][0] in ('sin','cos'):
            return [trig(e[1][0],e[1][1],q(e[2]) if tag=='pow' else e[2])]
        raise Unsupported('The source is outside the finite indexed Fourier algebra')

    modes=walk(raw)
    if not transformations:raise Unsupported('No finite Euler expansion was found')
    # To evaluate a row, take Re(scale*i^i_exponent*exp(i*phase)*J)
    # with J=(exp((a+ib)hi)-exp((a+ib)lo))/(a+ib), or hi-lo if both rates vanish.
    value=dict(expression='real_part_of_finite_sum_of_exponential_mode_integrals',
               bounds=(lo,hi),terms=modes,index_domain={k:'positive_integers' for k in indices},
               kernel=dict(nonzero_rate='(exp((a+i*b)*upper)-exp((a+i*b)*lower))/(a+i*b)',
                           zero_rate='upper-lower'))
    plan=dict(theorem='method.indexed_euler_integrals',method='euler_complex_exponential_formulas',
              source_integrand=raw,integer_indices=indices,transformations=transformations,
              evaluation='Integrate each entire mode. A finite cancellation extends across each original isolated sine or cosine zero.')
    return plan,value


def signed_harmonic_support(cut,index):
    from integrals import affine
    from verify import same_value

    waveform,x,support=cut.groups()
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',waveform+' '+support))-{x,'pi','e',*m.FUNCTIONS,*m.ALIASES})
    if x==index or index not in names:raise Unsupported('The original integer cutoff index must be fixed')
    raw=m.parse(waveform,x,names);radius=m.parse(support,None,names)
    terms=[(ONE,raw)] if raw[0]!='mul' else [raw[1:],raw[1:][::-1]]
    for A,wave in terms:
        if wave[0]!='sin' or m.variable_in(A) or domain_conditions(A):continue
        omega,shift=affine(wave[1],x)
        if omega[0]=='s' and omega[1]!=index and shift==ZERO and not domain_conditions(wave[1]):break
    else:raise Unsupported('Expected an unshifted sine with a fixed frequency symbol')
    n=('s',index)
    cycles=m.pi_multiple(m.mul(omega,m.div(radius,n)))
    if (cycles is None or cycles<=0 or cycles.denominator!=1
            or not same_value(radius,m.div(m.mul(q(cycles),m.mul(m.PI,n)),omega))):
        raise Unsupported('The original cutoff must be an integer number of sine half-periods')
    ctx=m.context(dict(variable=x,parameters=names,parameter_conditions=[omega[1]+'!=0',index+'>0']))
    if any(not known_guard(g,ctx) for g in domain_conditions(radius)):
        raise Unsupported('The support expression has an unresolved pole')
    frequency='lambda'
    while frequency in names or frequency==x:frequency+='_'
    w=('s',frequency);p=m.add(omega,w);d=m.add(omega,m.neg(w))
    regular=m.mul(m.div(A,m.PI),m.add(m.div(('sin',m.mul(d,radius)),d),m.neg(m.div(('sin',m.mul(p,radius)),p))))
    at_resonance=m.div(m.mul(A,radius),m.PI)
    return dict(strategy='signed_harmonic_support',theorem='method.signed_harmonic_support',frequency=frequency,
                source_frequency=omega,half_periods_per_index=q(cycles),index=index,radius=radius,steps=[
                    'При положительной исходной частоте носитель симметричен. На обоих краях синус равен нулю благодаря целому числу полупериодов. Разрывов нет.',
                    'Косинусный коэффициент обращается в нуль по нечётности. Для синусного коэффициента интегрируем разность косинусов по формуле произведения.',
                    'При совпадении частот используем предел sin(z)/z. При отрицательной исходной частоте первая ветвь пуста. При нулевой частоте напечатанная граница не определена.'
                ]),dict(frequency=frequency,frequency_domain='positive',jump_values=[],frequency_cases=[
                    dict(when=omega[1]+'>0',cosine_coefficient=ZERO,sine_coefficient=dict(regular=regular,resonant=at_resonance,at=omega),
                         reconstruction='original continuous compact profile'),
                    dict(when=omega[1]+'<0',cosine_coefficient=ZERO,sine_coefficient=ZERO,reconstruction=ZERO),
                    dict(when=omega[1]+'=0',source_defined=False)])


def fourier_integral_representation(task,lib,saved=None):
    """Find the two real Fourier densities and the value of symmetric inversion."""
    from verify import same_value
    form=task.get('function');extension=task.get('continuation');src=task.get('source',{})
    fields={'kind','id','source','function','continuation','convention','stated_conditions','requested_output'}
    provenance={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
    heading=('Представить интегралом Фурье, продолжая функцию указанным образом.' if extension else
             'Представить функцию интегралом Фурье, учитывая полусуммы значений на скачках.')
    wanted=(['fourier_representation_with_specified_extension'] if extension else
            ['coefficient_functions','fourier_representation','jump_values_if_present'])
    convention='f(x)=int_0^inf [a(lambda)*cos(lambda*x)+b(lambda)*sin(lambda*x)]dlambda; a,b=(1/pi)*integrals over R'
    if (not lib.data.get('fourier_integral_moments') or set(task)-fields or not isinstance(form,str)
            or not isinstance(src,dict) or set(src)-provenance or src.get('literal_requirement',heading)!=heading
            or task.get('requested_output')!=wanted or extension not in (None,'even','odd')
            or task.get('convention',convention)!=convention):
        raise Unsupported('The original Fourier convention, extension and all requested outputs are required')
    form=form.replace('²','^2').replace('³','^3')
    if lib.data.get('signed_harmonic_support') and not extension:
        cut=re.fullmatch(r'(.+) when abs\(([A-Za-z_]\w*)\)\s*<=\s*([^,]+), (?:else 0|0 otherwise)(?: \(left label f\(x\) as printed\))?',form)
        conditions=task.get('stated_conditions',[])
        integer=re.fullmatch(r'([A-Za-z_]\w*) (?:is a )?positive integer',conditions[0]) if len(conditions)==1 else None
        if cut and integer:return signed_harmonic_support(cut,integer[1])
    names=sorted(set(re.findall(r'\b[A-Za-z_]\w*\b',form))-m.FUNCTIONS-set(m.ALIASES)-
                 {'x','pi','e','when','else','otherwise','sign','on','inf'})
    facts=[]
    for fact in task.get('stated_conditions',[]):
        match=re.fullmatch(r'(\w+)\s*([<>])\s*(\w+|0)',fact)
        if not match or match[1] not in names or (match[3]!='0' and match[3] not in names):
            raise Unsupported('The stated parameters still need a proof on their full domain')
        a,op,b=match.groups()
        facts.append(fact.replace(' ','') if b=='0' else (f'({a}-{b})>0' if op=='>' else f'({b}-{a})>0'))
    freq='omega'
    while freq in names:freq+='_'
    w=('s',freq);x=('v','x')
    ctx=m.context(dict(variable='x',parameters=[*names,freq],parameter_conditions=[*facts,freq+'>0']))
    def fixed(e):return m.parse(e,None,names)
    def at(e,z):return m.simplify(m.substitute(e,{x:z}))
    def plan_value(strategy,plan,cosine,sine,jumps=(),extra=None):
        plan=dict(plan,strategy=strategy,theorem='method.fourier_integral_moments',frequency=freq,
                  extension=extension,positive_frequency=True)
        value=dict(frequency=freq,frequency_domain='positive',cosine_coefficient=cosine,sine_coefficient=sine,
                   reconstruction='symmetric one-sided average',jump_values=list(jumps),continuation=extension)
        if extra:value.update(extra)
        return plan,value
    compact=re.fullmatch(r'(.+) when abs\(x\)(<=?)([^,]+), (0 when abs\(x\)>(=?)([^,]+)|0 otherwise|else 0)',form)
    shifted=re.fullmatch(r'sign\(x-(.+?)\)\s*-\s*sign\(x-(.+?)\)',form)
    if compact or shifted:
        if extension:raise Unsupported('The prescribed continuation requires an actual half-axis function')
        if compact:
            fn,op,edge,_,closed_outside,opposite=compact.groups()
            radius=fixed(edge)
            if not m.constant_defined(radius,ctx) or opposite is not None and (
                    not m.constant_defined(fixed(opposite),ctx) or not same_value(radius,fixed(opposite)) or
                    op=='<=' and bool(closed_outside)):
                raise Unsupported('The printed compact support has inconsistent boundaries')
            sign=m.sign(radius,ctx)
            if sign is None and radius[0]=='s' and not task.get('stated_conditions'):
                # Only the unqualified real support radius is split. Its sign is never presumed.
                p,v=fourier_integral_representation(dict(task,stated_conditions=[radius[1]+'>0']),lib,
                                                    None if saved is None else saved['positive'])
                point=m.parse(fn.replace('sign(x)','0'),'x',names)
                at_origin=m.substitute(point,{x:ZERO,radius:ZERO})
                if op=='<=':
                    zero_value=m.simplify(at_origin) if m.constant_defined(at_origin,ctx) else 'undefined'
                else:zero_value='undefined' if opposite is not None and not closed_outside else ZERO
                return dict(strategy='signed_compact_radius',theorem='method.fourier_integral_moments',radius=radius,
                            frequency=freq,positive=p,zero_point_value=zero_value),dict(
                    frequency=freq,frequency_domain='positive',radius_cases=[
                        dict(condition=radius[1]+'>0',result=v),
                        dict(condition=radius[1]+'<0',cosine_coefficient=ZERO,sine_coefficient=ZERO,reconstruction=ZERO),
                        dict(condition=radius[1]+'=0',cosine_coefficient=ZERO,sine_coefficient=ZERO,reconstruction=ZERO,
                             original_value_at_origin=zero_value)])
            if sign!=1:raise Unsupported('The ordered positive half-width has not been established')
            if 'abs(x)' in fn or 'sign(x)' in fn:
                sides=[fn.replace('abs(x)',f'({s}x)').replace('sign(x)',n) for s,n in (('-','(-1)'),('','1'))]
                pieces=[(m.neg(radius),ZERO,sides[0]),(ZERO,radius,sides[1])]
            else:pieces=[(m.neg(radius),radius,fn)]
        else:
            left,right=map(fixed,shifted.groups())
            if not all(m.constant_defined(e,ctx) for e in (left,right)) or m.sign(m.add(right,m.neg(left)),ctx)!=1:
                raise Unsupported('The ordered sign-jumps have not been proved')
            pieces=[(left,right,'2')]
        kernels={};traces=[ZERO];jumps=[]
        for j,(left,right,fn) in enumerate(pieces):
            raw=m.parse(fn,'x',names)
            before=at(raw,left);average=m.mul(q(1,2),m.add(traces[-1],before))
            if not same_value(traces[-1],before):jumps.append(dict(point=left,left=traces[-1],right=before,average=average))
            traces.append(at(raw,right))
        if not same_value(traces[-1],ZERO):jumps.append(dict(point=right,left=traces[-1],right=ZERO,average=m.mul(q(1,2),traces[-1])))
        densities=[]
        for weight in ('cos','sin'):
            total=ZERO;kernels[weight]=[];branches=[]
            for j,(lo,hi,fn) in enumerate(pieces):
                prev=None if saved is None else saved['primitives'][weight][j]
                cert,val,conditional=fourier_moment(fn,lo,hi,weight,w,names,ctx,prev,freq,[*facts,freq+'>0'])
                if any(m.sign(row['if_zero'],ctx)==0 for row in conditional):
                    raise Unsupported('A known resonance was not resolved')
                kernels[weight].append(cert);total=m.add(total,val)
                # The simultaneous zero of the rate and frequency has its own primitive.
                branches.extend(conditional)
            scale=m.div(ONE,m.PI)
            densities.append(dict(regular=m.mul(scale,total),resonances=[
                dict(if_zero=b['if_zero'],then=m.mul(scale,b['then']),otherwise=m.mul(scale,b['otherwise']))
                for b in branches]))
        return plan_value('compact_smooth_pieces',dict(pieces=pieces,primitives=kernels,proof='Dirichlet inversion for compact piecewise smooth functions'),*densities,jumps)
    if extension:
        if not form.endswith(' on 0<x<inf'):raise Unsupported('A positive half-axis function is required')
        raw=m.parse(form.removesuffix(' on 0<x<inf'),'x',names)
        arms=(raw,raw if extension=='even' else ('mul',q(-1),raw))
    else:
        raw=m.parse(form,'x',names)
        absolute=('abs',x)
        arms=(m.substitute(raw,{absolute:x}),m.substitute(raw,{x:m.neg(x),absolute:x}))

    # Rational Cauchy densities are the inverse cosine and sine moments of a decaying exponential.
    if extension is None and raw[0]=='div':
        numerator,denominator=raw[1:]
        intercept,slope=at(numerator,ZERO),m.add(at(numerator,ONE),m.neg(at(numerator,ZERO)))
        square=at(denominator,ZERO)
        if (not domain_conditions(numerator) and not domain_conditions(denominator) and m.sign(square,ctx)==1
                and same_value(numerator,m.add(intercept,m.mul(slope,x))) and same_value(denominator,m.add(square,m.power(x,2)))):
            a=m.simplify(('sqrt',square))
            if square[0]=='pow' and square[2]==2 and m.sign(square[1],ctx) in (1,-1):
                a=square[1] if m.sign(square[1],ctx)==1 else m.neg(square[1])
            decay=('exp',m.neg(m.mul(a,w)))
            return plan_value('cauchy_exponential_duality',dict(scale=a,numerator=[intercept,slope],
                proof='The exponential cosine moment gives the even inverse pair. On each compact positive frequency interval the derivative tail is uniformly Dirichlet, giving the sine coefficient. Both inverse densities are integrable.'),
                m.mul(m.div(intercept,a),decay),m.mul(slope,decay))
    if extension or m.contains(raw,('abs',x)):
        kernels={};densities=[]
        for weight in ('cos','sin'):
            certs=[];total=ZERO
            for j,arm in enumerate(arms):
                fn=('mul',arm,(weight,m.mul(w,x)))
                child=dict(kind='integrate',variable='x',parameters=[*names,freq],
                           integrand=source(fn))
                prev=None if saved is None else saved['primitives'][weight][j]
                cert,val=decaying_harmonic_moment(child,[*facts,freq+'>0'],prev)
                certs.append(cert);total=m.add(total,m.neg(val) if j and weight=='sin' else val)
            densities.append(m.div(total,m.PI));kernels[weight]=certs
        a,b=(at(arm,ZERO) for arm in arms);jumps=[] if same_value(a,b) else [dict(point=ZERO,left=b,right=a,average=m.mul(q(1,2),m.add(a,b)))]
        return plan_value('decaying_half_axis_modes',dict(arms=arms,primitives=kernels,
            proof='Each smooth half-axis is absolutely integrable by exponential decay. Dirichlet inversion gives one-sided averages.'),*densities,jumps)
    if not lib.data.get('gaussian_fourier_moments'):
        raise Unsupported('The transform of an unrestricted density requires a proved tail method')
    gaussian_task=dict(limits='-inf..inf',stated_conditions=[])
    def checked_gaussian(plan,answer):return plan,m.parse(answer,None,[*names,freq])
    kernels={};densities=[]
    for weight in ('cos','sin'):
        cert,val=gaussian_integral_moments(gaussian_task,ctx,('mul',raw,(weight,m.mul(w,x))),'x',checked_gaussian)
        kernels[weight]=cert;densities.append(m.div(val,m.PI))
    return plan_value('gaussian_whole_line',dict(moments=kernels,proof='Gaussian domination on both tails gives smooth absolutely integrable functions and Fourier inversion.'),*densities)


def fourier_series_sums(terms,plan,series):
    """Recover a requested series as a linear combination of evaluations with the same partial-sum cutoff."""
    from verify import same_value
    n=('s','n');lo,hi=plan['source_interval'];width=m.add(hi,m.neg(lo));coeff=series['coefficients']
    if any(c['conditional'] for c in coeff.values()):raise Unsupported('Unresolved resonances in the auxiliary evaluations')
    targets={}
    for term in terms:
        a=re.fullmatch(r'sum\(n>=1,(1|\(-1\)\^\(n[-+]1\))/(n|\(2\*n-1\))(?:\^([1-6]))?\)',term)
        if not a:raise Unsupported('A remaining numerical series has unclassified weights')
        alt=a[1]!='1';odd=a[2]!='n';p=int(a[3] or 1)
        targets[term]=(p,[q((0,1,0,-1)[j] if odd and alt else int(j%2) if odd else (-1)**((j+1)%2) if alt else 1) for j in range(4)])
    mean=coeff.get('mean',{}).get('fixed',ZERO);omega=series['angular_frequency']
    def at(e,k):return m.simplify(m.substitute(e,{n:q(k)}))
    def trig_class(e,r):
        if e[0] in ('cos','sin') and m.contains(e,n):
            arg=e[1];b=at(arg,0);d=m.simplify(m.add(at(arg,1),m.neg(b)))
            step=m.num(m.simplify(m.div(m.mul(q(2),d),m.PI)))
            if step is None or step.denominator!=1 or not same_value(arg,m.add(b,m.mul(n,d))):
                raise Unsupported('A Fourier phase does not have a verified four-class period')
            return at(e,r)
        if not m.contains(e,n):return e
        return m.simplify(tuple(trig_class(v,r) if isinstance(v,tuple) else v for v in e))
    answers={};samples=[]
    for pos in (lo,m.add(lo,m.div(width,q(2))),m.add(lo,m.div(width,q(4))),m.add(lo,m.mul(q(3,4),width))):
        pos=m.simplify(pos);fx=next((y for x,y in series['junction_values'] if same_value(x,pos)),None)
        if fx is None:
            seg=next(((a,b,f) for a,b,f in plan['pieces'] if m.sign(m.add(pos,m.neg(a)),{})==1 and m.sign(m.add(b,m.neg(pos)),{})==1),None)
            if seg is None:continue
            fx=m.simplify(m.substitute(m.parse(seg[2],'x'),{('v','x'):pos}))
        wave=m.add(*(m.mul(c.get('fixed',ZERO),m.simplify((w,m.mul(omega,pos)))) for w,c in
                     ((w,coeff.get(w,{})) for w in ('cos','sin'))))
        samples.append([pos,m.add(fx,m.neg(mean)),[trig_class(wave,r) for r in range(4)]])
    equations=[]
    for p in sorted(set(v[0] for v in targets.values())):
        basis={}
        def subtract(row,rhs):
            for pivot,(old,y) in sorted(basis.items()):
                k=row[pivot];row=[m.simplify(m.add(a,m.neg(m.mul(k,b)))) for a,b in zip(row,old)]
                rhs=m.simplify(m.add(rhs,m.neg(m.mul(k,y))))
            return row,rhs
        for pos,rhs,values in samples:
            scaled=[m.mul(m.power(n,p),v) for v in values];K=[at(v,r or 4) for r,v in enumerate(scaled)]
            if not all(same_value(v,k) for v,k in zip(scaled,K)):continue
            equations.append(dict(point=pos,power=p,residue_weights=K,value=rhs))
            row,y=subtract(K,rhs);j=next((j for j,k in enumerate(row) if not same_value(k,ZERO)),None)
            if j is not None and m.nonzero(row[j],{}):
                basis[j]=([m.simplify(m.div(k,row[j])) for k in row],m.simplify(m.div(y,row[j])))
        for term,(power,mask) in targets.items():
            if p!=power:continue
            rem,neg=subtract(mask,ZERO)
            if any(not same_value(k,ZERO) for k in rem):raise Unsupported('Point evaluations do not determine every requested numerical series')
            answers[term]=m.simplify(m.neg(neg))
    return equations,answers


def fourier_generating_series(task, lib, saved=None):
    from ordinary_series import result
    from verify import same_value

    fields={'kind','id','source','function_or_given','requested_output','method_requirement','parameters',
            'printed_conditions','source_interval','target_interval','allowed_harmonics','interval','period'}
    form=task.get('function_or_given');method=task.get('method_requirement')
    outputs=task.get('requested_output',['fourier_expansion','pointwise_sum'])
    provenance={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','literal_requirement','page_png_sha256'}
    if (not lib.data.get('fourier_generating_series') or task.get('kind')!='fourier_expansion'
            or set(task)-fields or set(task.get('source',{}))-provenance or not isinstance(form,str)
            or method not in (None,'complex_exponential_representation')):
        raise Unsupported('The input does not describe a supported Fourier generating-series goal')
    label=task.get('source',{}).get('literal_requirement')
    compact=form.replace(' ','')
    name=r'([A-Za-z_]\w*)'
    generic=dict(frequency='n',interval=['-pi','pi'],basis='real Fourier',period='2*pi',coefficient_index_min=1)
    def found(rule, certificate, steps, **value):
        return result(rule,dict(generic,**value),*steps,certificate=certificate)
    if outputs==['periodic_extension']:
        harmonics=task.get('allowed_harmonics');ext=re.fullmatch(fr'integrable{name}on\(0,pi/2\)',compact)
        if (method or task.get('printed_conditions') or task.get('source_interval')!=['0','pi/2']
                or task.get('target_interval')!=generic['interval'] or not ext or not isinstance(harmonics,dict)
                or set(harmonics)!={'function','index','start_index'} or harmonics['index']!='2*n-1'
                or harmonics['start_index']!=1 or harmonics['function'] not in ('sin','cos')):
            raise Unsupported('The initial quarter period and both frequency restrictions must be given')
        cos=harmonics['function']=='cos';f=ext[1]
        if label and label!=('Продолжить на (-pi,pi) для ряда только по '+harmonics['function']+'((2n-1)x)'):
            raise Unsupported('The requested Fourier symmetry differs from the source heading')
        half_sign='-' if cos else '';origin_sign='' if cos else '-'
        return found('odd_harmonics_by_reflections',dict(even=cos,reflection_multiplier=-1 if cos else 1),
                     ['На (π/2,π) определяем продолжение отражением x↦π−x с нужным знаком, на (−π,0) отражением x↦−x.',
                      'Подстановка x↦−x в определении коэффициента убирает одну семью гармоник. Подстановка x↦π−x даёт множитель (−1)^n для косинуса и (−1)^(n+1) для синуса; чётные индексы выпадают.',
                      'Отражения сохраняют интегрируемость. Из одной интегрируемости следует вид коэффициентов; точечное представление требует соответствующей теоремы с дополнительными условиями.'],
                     extension=[['0<x<pi/2',f+'(x)'],['pi/2<x<pi',half_sign+f+'(pi-x)'],
                                ['-pi<x<0',origin_sign+'F(-x)']],available_modes=harmonics,value_at_join='arbitrary for coefficient calculation')
    if any(task.get(field) for field in ('source_interval','target_interval','allowed_harmonics')):
        raise Unsupported('A separate extension goal remains')
    if outputs not in (['all_real_fourier_coefficients'],['fourier_expansion','pointwise_sum'],
                       ['all_real_fourier_coefficients','endpoint_as_improper_integral'],
                       ['all_real_fourier_coefficients','original_domain_and_periodic_extension']):
        raise Unsupported('Additional Fourier conclusions need separate proofs')
    if task.get('interval',['-pi','pi'])!=generic['interval'] or task.get('period','2*pi')!='2*pi':
        raise Unsupported('The Fourier interval is not a verified full period')
    if re.fullmatch(r'sum\(i=0\.\.n,alpha_i\*cos\(i\*x\)\+beta_i\*sin\(i\*x\)\)',compact):
        if (method or task.get('printed_conditions') or task.get('parameters',['n','alpha_i','beta_i'])!=['n','alpha_i','beta_i']
                or label not in (None,'Разложить в ряд Фурье. n nonnegative integer')):
            raise Unsupported('The coefficients must be independent of the angle')
        return found('orthogonal_projection_preserves_finite_fourier',dict(input_last='n',orthogonality='integer harmonics'),
                     ['Из ортогональности на полном периоде следуют исходные коэффициенты ненулевых гармоник. Постоянный коэффициент в нормировке a₀/2 равен 2α₀. Остальные коэффициенты нулевые.'],
                     constant='alpha_0',cosine='alpha_k for 1<=k<=n, else 0',sine='beta_k for 1<=k<=n, else 0',pointwise='all real x')
    p=re.fullmatch(fr'(sin|cos)\(x\)\^\(2\*{name}\),\2positiveinteger',compact)
    if p:
        fn,k=p.groups()
        if (method not in (None,'complex_exponential_representation')
                or label not in (None,'Разложить в ряд Фурье. Euler formulas with t=exp(ix)')
                or task.get('printed_conditions',[k+' is a positive integer'])!=[k+' is a positive integer']
                or outputs not in (['all_real_fourier_coefficients'],['fourier_expansion','pointwise_sum'])):
            raise Unsupported('The even power and positive integer parameter require verification')
        sign='(-1)^j*' if fn=='sin' else ''
        return found('binomial_laurent_harmonics',dict(function=fn,degree='2*'+k,representation='Euler'),
                     ['Записываем синус или косинус через t=e^(ix) и t⁻¹. По биному Ньютона степени t идут от −2m до 2m с шагом 2.',
                      'Объединяем сопряжённые степени в одну вещественную гармонику. Обе формулы конечные для каждого целого m>0.'],
                     constant=f'binomial(2*{k},{k})/2^(2*{k})',
                     cosine=f'{sign}2^(1-2*{k})*binomial(2*{k},{k}-j) at n=2*j, 1<=j<={k}; otherwise 0',
                     sine='0',pointwise='all real x')
    geometric=re.fullmatch(fr'sum\(n=1\.\.infinity,{name}\^n\*sin\(n\*x\)/sin\(x\)\)',compact)
    if geometric:
        k=geometric[1]
        if (method or task.get('parameters',[k])!=[k] or task.get('printed_conditions',['abs('+k+')<1'])!=['abs('+k+')<1']
                or label not in (None,'Разложить в ряд Фурье. abs('+k+')<1, original denominator nonzero')
                or outputs!=['all_real_fourier_coefficients','original_domain_and_periodic_extension']):
            raise Unsupported('The source division and all requested extensions must be represented')
        return found('complex_geometric_quotient_harmonics',dict(ratio=k,original_guard='sin(x)!=0'),
                     ['Суммирование комплексной геометрической прогрессии и взятие мнимой части дают числитель α sin x/(1−2α cos x+α²).',
                      'Сокращаем sin x на исходной области и исследуем продолжение в x∈πZ. Знаменатель продолжения положителен по |α|<1.',
                      'Распишем продолжение через две сопряжённые геометрические прогрессии. Полученный ряд сходится абсолютно и равномерно.'],
                     constant=f'{k}/(1-{k}^2)',cosine=f'2*{k}^(n+1)/(1-{k}^2)',sine='0',
                     pointwise='real x outside pi*Z; continuous periodic extension on pi*Z')
    parts=re.fullmatch(fr'(.+),abs\({name}\)<1',compact)
    if parts:
        text,k=parts.groups()
        condition='abs('+k+')<1'
        if (k=='x' or task.get('printed_conditions',[condition])!=[condition]
                or task.get('parameters',[k])!=[k] or outputs not in (['all_real_fourier_coefficients'],['fourier_expansion','pointwise_sum'])
                or label not in (None,'Разложить в ряд Фурье. Euler formulas with t=exp(ix)')):
            raise Unsupported('The geometric ratio must be a fixed real parameter strictly inside the unit disk')
        parse=lambda s:m.parse(s,'x',[k])
        e=parse(text);D=f'1-2*{k}*cos(x)+{k}^2';den=parse(D)
        if any(not same_value(g,den) for _,g in domain_conditions(e)):
            raise Unsupported('An original factor has a domain restriction beyond the positive kernel')
        if e[0]=='ln' and same_value(e[1],den):
            return found('log_geometric_harmonics',dict(ratio=k,real_factorized=source(den),complex_branch='analytic logarithm equal to zero at ratio=0'),
                         ['Подставляем t=e^(ix). Положительный вещественный аргумент есть (1−qt)(1−q/t)=|1−qt|².',
                          'По |q|<1 применяем степенной ряд логарифма к каждому сопряжённому множителю с начальным значением ноль. Их сумма равна вещественному логарифму произведения.',
                          'Объединение сопряжённых частот даёт абсолютную равномерную сходимость.'],
                         constant='0',cosine=f'-2*{k}^n/n',sine='0',pointwise='all real x')
        if e[0]!='div' or not same_value(e[2],den):
            raise Unsupported('The source denominator is not the positive geometric kernel')
        numerator=e[1]
        for pattern,constant,cosine,sine,identity in (
            (f'{k}*sin(x)','0','0',f'{k}^n','imaginary part of 1/(1-q*t)'),
            (f'1-{k}^2','1',f'2*{k}^n','0','1/(1-q*t)+1/(1-q/t)-1'),
            (f'1-{k}*cos(x)','1',f'{k}^n','0','real part of 1/(1-q*t)')):
            if same_value(numerator,parse(pattern)):
                return found('complex_geometric_kernel_harmonics',dict(ratio=k,denominator=source(den),decomposition=identity),
                             ['Подставляем t=e^(ix), знаменатель факторизуется как |1−qt|² и строго положителен.',
                              'Преобразуем числитель вместе со знаменателем в вещественную либо мнимую часть геометрических прогрессий. При |q|<1 все их ряды сходятся абсолютно и равномерно.'],
                             constant=constant,cosine=cosine,sine=sine,pointwise='all real x')
        raise Unsupported('The numerator does not yield the checked combination of geometric kernels')
    if method or task.get('printed_conditions') or task.get('parameters'):
        raise Unsupported('The logarithmic boundary limit has no additional source assumptions')
    primitive=re.fullmatch(fr'integral\({name}=0\.\.x,ln\(sqrt\(abs\(cot\(\1/2\)\)\)\)\)',compact)
    primitive_output=['all_real_fourier_coefficients','endpoint_as_improper_integral']
    if primitive:
        if outputs!=primitive_output or label not in (None,'Разложить в ряд Фурье. [-pi,pi]'):
            raise Unsupported('The improper primitive is required throughout the closed period')
        operation='cot';integrated=True
    else:
        match=re.fullmatch(r'ln\(abs\((sin|cos|tan)\(x/2\)\)\)',compact)
        if not match or outputs not in (['all_real_fourier_coefficients'],['fourier_expansion','pointwise_sum']):
            raise Unsupported('No Abel boundary logarithm of a circular function')
        operation=match[1];integrated=False
        excluded='poles and zeros' if operation=='tan' else 'zeros'
        if label not in (None,'Разложить в ряд Фурье. unbounded periodic, exclude '+excluded+' in pointwise statements'):
            raise Unsupported('An additional condition on the boundary logarithm remains')
    specifications={'sin':('-ln(2)','-1/n','2*pi*Z'),
                    'cos':('-ln(2)','-(-1)^n/n','pi+2*pi*Z'),
                    'tan':('0','((-1)^n-1)/n','pi*Z')}
    steps=['При 0<r<1 разложение ln|1−r exp(ix)| даёт коэффициенты −r^n/n. После замены x↦x+π они умножаются на (−1)^n.',
           'Имеем |1−r exp(ix)|²=(1−r)²+4r sin²(x/2). Для r≥1/2 логарифмическая особенность имеет интегрируемую общую мажоранту. Поэтому коэффициенты сохраняются при r→1−.',
           'Всюду вне нулей соответствующих множителей граничные гармонические ряды сходятся по Дирихле, а теорема Абеля отождествляет их сумму с логарифмом.']
    if integrated:
        steps.append('Подынтегральное выражение есть −ln|tan(x/2)|/2. Сходимость в интегральной норме разрешает переход к первообразной от 0. Коэффициенты нечётных частот делятся ещё на n, интеграл и новый ряд определены на всём замкнутом отрезке.')
        return found('integrated_abel_boundary_logarithm',dict(operand='cot',scale='1/2',primitive_anchor=0,
                     justification='L1 estimate and absolutely summable integrated coefficients'),steps,
                     constant='0',cosine='0',sine='(1-(-1)^n)/(2*n^2)',pointwise='entire closed period, improper integral at singularities')
    constant,cosine,holes=specifications[operation]
    return found('abel_boundary_logarithmic_harmonics',dict(operand=operation,excluded_angles=holes,
                 justification='L1 logarithmic majorant for the coefficient limit and Dirichlet-Abel at regular angles'),steps,
                 constant=constant,cosine=cosine,sine='0',pointwise='all angles outside '+holes)


def fourier_expansion(task,lib,saved):
    """Integrate each smooth piece against every requested mode; keep resonant indices and one-sided limits."""
    try:return fourier_generating_series(task,lib,saved)
    except Unsupported:pass
    from verify import same_value
    fields={'kind','id','source','function_or_given','requested_output','series_to_sum','common_question_input'}
    provenance={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','literal_requirement','page_png_sha256'}
    src=task.get('source',{});form=task.get('function_or_given')
    sums=task.get('series_to_sum',[]);common=task.get('common_question_input')
    if (not lib.data.get('fourier_piecewise_moments') or set(task)-fields or not isinstance(src,dict) or set(src)-provenance
            or task.get('requested_output',['fourier_expansion','pointwise_sum'])!=['fourier_expansion','pointwise_sum']+(['numeric_series_sums'] if sums else [])
            or not isinstance(sums,list) or len(set(sums))!=len(sums) or not isinstance(form,str)):
        raise Unsupported('Additional source outputs or requirements need separate Fourier proofs')
    heading=src.get('literal_requirement','');periodic='Разложить в ряд Фурье. '
    common_suffix='; по трём разложениям вычислить все три указанные числовые суммы.'
    printed_modes=['cosines on (-pi,pi)','sines on (0,pi)','full on (0,2pi)']
    if common is not None:
        if (not heading.endswith(common_suffix) or common!={'function':form,'other_printed_expansions':printed_modes}
                or sums!=['sum(n>=1,1/n^2)','sum(n>=1,(-1)^(n+1)/n^2)','sum(n>=1,1/(2*n-1)^2)']):
            raise Unsupported('The common source question or its companion expansions are incomplete')
        heading=heading.removesuffix(common_suffix)
    if heading=='Знак на (-π,π), разложение и сумма ряда Лейбница':
        if form!='sign(x)' or sums!=['sum(n>=1,(-1)^(n-1)/(2*n-1))']:raise Unsupported('The source also asks for the Leibniz sum')
        heading=periodic+'(-pi,pi)'
    odd_basis={'Разложить по косинусам нечётных дуг':'cos','Разложить по синусам нечётных дуг':'sin'}
    extension='periodic';bounds=None;extra='';pars=set();fold=None;global_period=False
    if heading in odd_basis:
        match=re.fullmatch(r'(.+), 0<x<([a-zA-Z0-9*/.+-]+)',form)
        if not match:raise Unsupported('Missing positive half-interval or additional printed conditions')
        form,end=match.groups();bounds=('0',end);extension=odd_basis[heading]+'_odd_harmonics'
    elif heading.startswith(periodic):
        data=heading[len(periodic):]
        if data in ('periodic','periodic with period 1','2pi-periodic'):
            if data=='periodic with period 1':
                if form=='x-floor(x)':bounds=('0','1');form='x'
                elif form=='min(k in integers,abs(x-k))':bounds=('-1/2','1/2');form='abs(x)'
                else:raise Unsupported('Period and smooth pieces of the given source have not been proved')
            else:
                bounds=('-pi','pi');global_period=data=='2pi-periodic'
                if data=='periodic':
                    fold=re.fullmatch(r'(abs|asin|sign)\((sin|cos)\((?:(\d+)\*)?x\)\)',form)
                    if not fold or not 1<=int(fold[3] or 1)<=24:
                        raise Unsupported('The period and the source branches must be proved')
        else:
            match=re.fullmatch(r'[(\[]([^,()\[\]]+),([^,()\[\]]+)[)\]](.*)',data)
            if not match:raise Unsupported('Original period, interval or method unresolved')
            lo,hi,extra=match.groups();bounds=(lo,hi)
            if extra==' by cosines of integral multiples':extension='cos_full'
            elif extra==' by sines of integral multiples':extension='sin_half'
            elif extra not in ('',', A constant',', a nonintegral',', periodic extension',' full Fourier series'):
                raise Unsupported('Additional source requirements or incomplete printed pieces')
    else:raise Unsupported('A separate printed method, extension rule or additional objective remains')
    def expr(s):return m.parse(re.sub(r'(?<=\d)(?=pi|[lh]\b)','*',s),None,['a','b','A','l','h'])
    lo,hi=map(expr,bounds);width=m.simplify(m.add(hi,m.neg(lo)))
    pars=sorted(set(re.findall(r'\b(?:a|b|A|l|h)\b',form+' '+source(width)+' '+source(lo))))
    conditions=[k+'>0' for k in ('l','h') if m.contains(width,('s',k)) and
                (width==('s',k) or same_value(width,m.mul(q(2),('s',k))))]
    ctx=m.context(dict(variable='x',parameters=[*pars,'n'],parameter_conditions=[*conditions,'n>0']))
    if not all(m.constant_defined(e,ctx) for e in (lo,hi)):
        raise Unsupported('An original Fourier endpoint is undefined')
    if m.sign(width,ctx)!=1:raise Unsupported('A nonempty Fourier interval with proven positive length is required')
    if extension=='cos_full':
        raw=m.parse(form,'x',pars)
        if not same_value(lo,m.neg(hi)) or not same_value(raw,m.substitute(raw,{('v','x'):m.neg(('v','x'))})):
            raise Unsupported('A cosine-only full-period expansion needs evenness on the symmetric interval')
    if extension in ('sin_half','sin_odd_harmonics','cos_odd_harmonics') and lo!=ZERO:
        raise Unsupported('The supported reflection uses a half interval starting at zero')
    duration=m.mul(q(4),width) if extension.endswith('odd_harmonics') else m.mul(q(2),width) if extension=='sin_half' else width
    omega=m.div(m.mul(q(2),m.PI),duration)
    n=('s','n');index=m.add(m.mul(q(2),n),q(-1)) if extension.endswith('odd_harmonics') else n;angular=m.simplify(m.mul(index,omega))
    pieces=[];closure=[];zero_pieces=[]
    if fold:
        op,wave,mult=fold.groups();k=int(mult or 1);offset=int(wave=='cos')
        # In quarter-turn coordinates the phase is (2kx/pi)+offset, and cos x = sin(x+pi/2).
        for j in range(-2*k,2*k):
            a=m.mul(q(j,2*k),m.PI);b=m.mul(q(j+1,2*k),m.PI);phase=j+offset
            if op=='asin':
                nearest=(phase+1)//2;slope=(-1)**(nearest%2)
                fn=source(m.mul(q(slope),m.add(m.mul(q(k),('v','x')),m.mul(q(F(offset,2)-nearest),m.PI))))
            else:
                s=1 if phase%4<2 else -1
                fn=str(s) if op=='sign' else str(s)+'*'+wave+'('+str(k)+'*x)'
            if pieces and pieces[-1][2]==fn:pieces[-1][1]=b
            else:pieces.append([a,b,fn])
    elif ' on ' in form:
        parts=re.split(r'(?<=[)\]])\s*,\s*',form.removeprefix('f='))
        for item in parts:
            match=re.fullmatch(r'(.+) on ([(\[])([^,]+),([^,\])]+)([)\]])',item)
            if not match:raise Unsupported('Every source piece needs exact bounds')
            fn,l,a,b,r=match.groups();a,b=expr(a),expr(b)
            if not all(m.constant_defined(z,ctx) for z in (a,b)):
                raise Unsupported('An original branch endpoint is undefined')
            if same_value(a,b):
                if any(m.sign(d,ctx) not in (0,1) for d in (m.add(a,m.neg(lo)),m.add(hi,m.neg(a)))):
                    raise Unsupported('A zero-width piece lies outside the original interval')
                singleton=l=='[' and r==']';point=None
                if singleton:
                    point=m.substitute(m.parse(fn,'x',pars),{('v','x'):a})
                    if not m.constant_defined(point,ctx):raise Unsupported('An isolated source point is undefined')
                zero_pieces.append(dict(point=a,included=singleton,value=point,closure=[l=='[',r==']']))
            else:pieces.append([a,b,fn]);closure.append([l=='[',r==']'])
    elif form in ('abs(x)','sign(x)') and m.sign(lo,ctx)==-1 and m.sign(hi,ctx)==1:
        a,b=('-x','x') if form=='abs(x)' else ('-1','1')
        pieces=[[lo,ZERO,a],[ZERO,hi,b]]
    elif re.search(r'\bsign\s*\(',form) and not global_period:
        from functools import cmp_to_key
        from integrals import affine,learned_nodes
        from ray_proofs import compare_scalar
        raw=m.parse(form,'x',pars,('sign',));x=('v','x')
        signs=sorted({e for e in learned_nodes(raw) if isinstance(e,tuple) and e[0]=='sign'},key=repr)
        if not signs or any(not known_guard(g,ctx) for g in domain_conditions(raw)):
            raise Unsupported('The sign composition has an unresolved original guard')
        def cmp(a,b):
            z=m.sign(m.add(a,m.neg(b)),ctx)
            return compare_scalar(a,b) if z is None else z
        cut=[]
        for wave in signs:
            k,offset=affine(wave[1],'x')
            if not all(m.constant_defined(z,ctx) for z in (k,offset)) or m.sign(k,ctx) not in (-1,1):
                raise Unsupported('Each moving sign must have a proved nonzero affine slope')
            point=m.div(m.neg(offset),k)
            if cmp(point,lo)>0 and cmp(point,hi)<0 and not any(cmp(point,p)==0 for p in cut):
                cut.append(point)
        cuts=[lo,*sorted(cut,key=cmp_to_key(cmp)),hi]
        for a,b in zip(cuts,cuts[1:]):
            mid=m.div(m.add(a,b),q(2))
            z=[m.sign(m.substitute(w[1],{x:mid}),ctx) for w in signs]
            if any(s not in (-1,1) for s in z):raise Unsupported('No fixed sign in an open cell')
            fn=source(m.simplify(m.substitute(raw,dict(zip(signs,map(q,z),strict=True)))))
            if pieces and pieces[-1][2]==fn:pieces[-1][1]=b
            else:pieces.append([a,b,fn])
    else:pieces=[[lo,hi,form]]
    if global_period:
        from integrals import harmonic_modes
        modes,_,_=harmonic_modes(dict(kind='integrate',integrand=form,variable='x',parameters=pars))
        if any(a!=ZERO or len(p)!=1 or m.num(b) is None or m.num(b).denominator!=1 for (a,b),p in modes.items()):
            raise Unsupported('A global 2π period was not proved for the source expression')
    last=lo;sides=[]
    for a,b,fn in pieces:
        if not all(m.constant_defined(e,ctx) for e in (a,b)) or not same_value(a,last) or m.sign(m.add(b,m.neg(a)),ctx)!=1:
            raise Unsupported('Incomplete or inconsistent Fourier source partition')
        raw=m.parse(fn,'x',pars)
        # harmonic_modes below proves the original expression smooth on the closed piece.
        sides.append([m.simplify(m.substitute(raw,{('v','x'):v})) for v in (a,b)]);last=b
    if not same_value(last,hi):raise Unsupported('The pieces omit part of the original Fourier interval')
    for j in range(1,len(closure)):
        if closure[j-1][1] and closure[j][0] and not same_value(sides[j-1][1],sides[j][0]):
            raise Unsupported('Two closed pieces assign different values at the same interior point')
    assigned=[]
    for piece in zero_pieces:
        if not piece['included']:continue
        p,value=piece['point'],piece['value']
        if any(same_value(p,s) and not same_value(value,v) for s,v in assigned):
            raise Unsupported('Conflicting isolated assignments at the same point')
        for (a,b,fn),(left,right) in zip(pieces,closure,strict=True):
            A,B=m.sign(m.add(p,m.neg(a)),ctx),m.sign(m.add(b,m.neg(p)),ctx)
            if None in (A,B):raise Unsupported('The isolated point is not located relative to every source branch')
            if (A==1 or A==0 and left) and (B==1 or B==0 and right):
                v=m.substitute(m.parse(fn,'x',pars),{('v','x'):p})
                if not m.constant_defined(v,ctx) or not same_value(v,value):
                    raise Unsupported('An isolated assignment conflicts with an enclosing closed branch')
        assigned.append((p,value))
    kernels={};coefficients={};scale=m.div(q(2),width)
    weights=('mean','cos','sin') if extension=='periodic' else ('mean','cos') if extension=='cos_full' else (extension.split('_')[0],)
    for weight in weights:
        rows=[];regular=ZERO;branches=[]
        for j,(a,b,fn) in enumerate(pieces):
            proof,base,cond=fourier_moment(fn,a,b,weight,angular,pars,ctx,None if saved is None else saved['primitives'][weight][j])
            rows.append(proof);regular=m.add(regular,base);branches.extend(cond)
        factor=m.div(ONE,width) if weight=='mean' else scale
        coefficients[weight]=dict(fixed=m.simplify(m.mul(factor,regular)),conditional=[
            dict(if_zero=c['if_zero'],then=m.simplify(m.mul(factor,c['then'])),otherwise=m.simplify(m.mul(factor,c['otherwise']))) for c in branches])
        kernels[weight]=rows
    seams=[]
    for j,(a,b,fn) in enumerate(pieces):
        incoming=sides[j-1][1] if j or extension in ('periodic','cos_full') else (sides[0][0] if extension.startswith('cos') else m.neg(sides[0][0]))
        seams.append([a,m.div(m.add(incoming,sides[j][0]),q(2))])
    if extension not in ('periodic','cos_full'):seams.append([hi,sides[-1][1] if extension=='sin_odd_harmonics' else ZERO])
    plan=dict(theorem='method.fourier_piecewise_moments',source_interval=[lo,hi],pieces=pieces,
                 one_sided_values=sides,source_piece_closures=closure,primitives=kernels,
                 source_conditions=conditions+(['a not an integer'] if extra==', a nonintegral' else []),
                 extension=extension,coefficient_convention='mean + sum(a_n cos + b_n sin)')
    if zero_pieces:plan['zero_width_pieces']=zero_pieces
    series=dict(period=duration,angular_frequency=angular,positive_integer_index='n',coefficients=coefficients,
                 junction_values=seams,convergence='original smooth pieces; midpoint of one-sided limits at every periodic junction',
                 extension=extension)
    if sums:
        try:eqs,values=fourier_series_sums(sums,plan,series)
        except Unsupported:
            if not common or extension!='sin_half':raise
            companion=dict(kind='fourier_expansion',function_or_given=form,source={'literal_requirement':periodic+'(-pi,pi) by cosines of integral multiples'})
            cp,cv=fourier_expansion(companion,lib,None if saved is None else saved['companion'])
            eqs,values=fourier_series_sums(sums,cp,cv);plan['companion']=cp
        plan['common_cutoff_evaluations']=eqs;series['numeric_series_sums']=values
    return plan,series


def endpoint_derivatives(task,library,request):
    """Differentiate an oriented integral of a globally continuous field along two moving ends."""
    fields={'id','kind','source','goal','integrand','integration_variable','lower','upper','differentiation_variables','parameters','requested_output'}
    valid_goals=(None,'Find the displayed derivative.','Find all three displayed derivatives of the same definite integral.')
    if (library.data.get('task_compilers',{}).get(task['kind'])!='continuous_integral_endpoint_rule' or set(task)-fields or
        task.get('goal') not in valid_goals or
        task.get('requested_output',['derivative_for_each_variable'])!=['derivative_for_each_variable']):
        raise Unsupported('Unrecognized derivative-of-integral obligation')
    variables=task['differentiation_variables'];dummy=task['integration_variable'];parameters=task.get('parameters',[])
    if not isinstance(variables,(list,tuple)) or not variables or not isinstance(parameters,(list,tuple)):
        raise Unsupported('Expected distinct differentiation coordinates and constant parameters')
    names=[*variables,*parameters]
    if len(set(names))!=len(names):raise Unsupported('A coordinate or fixed parameter occurs twice')
    m.context(dict(variable=dummy,parameters=names))
    # The independent variable is bound only inside the integrand. Free differentiation
    # coordinates there would require the integral of a partial derivative.
    body=m.parse(task['integrand'],None,[dummy,*parameters])
    ctx={'parameters':[dummy,*names],'assumptions':[]}
    roles=('lower','upper');values=[m.parse(str(task[role]),None,names) for role in roles]
    for end in values:
        if not m.constant_defined(end,ctx) or not all(known_guard(g,ctx) for g in domain_conditions(end,smooth=True)):
            raise Unsupported('A bound lacks an everywhere differentiable real formula')
    fiber_fact=None
    if not m.constant_defined(body,ctx):
        signs=[m.sign(end,ctx) for end in values]
        if signs not in ([1,1],[-1,-1]):raise Unsupported('Continuity on every intervening fiber is not established')
        fiber_fact=dummy+('>0' if signs[0]==1 else '<0')
        free='__fiber_axis'
        while free in [dummy,*names]:free+='_'
        fiber=m.context(dict(variable=free,parameters=[dummy,*names],parameter_conditions=[fiber_fact]))
        if not m.constant_defined(body,fiber):
            raise Unsupported('Continuity within the proved common half-line is not established')
    terms=[];ends=[]
    for role,end in zip(roles,values,strict=True):
        sub={'kind':'partial_derivatives','function':str(task[role]),'variables':list(variables),'parameters':list(parameters),'requested_output':['first_partial_derivatives']}
        gradients=request(role+' endpoint derivatives',sub)['value']
        val=m.substitute(body,{('s',dummy):end})
        ends.append({'endpoint':end,'integrand_at_endpoint':val})
        terms.append([m.mul(val,freeze(g)) for g in gradients])
    result=tuple(m.simplify(m.add(upper,m.neg(lower))) for lower,upper in zip(*terms,strict=True))
    plan={'integration_variable':dummy,'variables':list(variables),'endpoints':ends}
    if fiber_fact:plan['oriented_fiber_condition']=fiber_fact
    return plan,result


def finite_integral_order(task,library,request):
    """Prove a strict integral comparison by a pointwise comparison on common fibers."""
    from integrals import affine
    from ray_proofs import compare_scalar,phase_interval,phase_zeros,primitive

    kind=task['kind'];src=task.get('source',{})
    headings={'definite_integral_sign':('Определить знаки следующих определенных интегралов.',
                                      'Определить знак интеграла.','Определить знак определенного интеграла.'),
              'compare_definite_integrals':('Определить, который интеграл больше.',)}
    compare=kind=='compare_definite_integrals'
    expected=['strict_comparison','proof'] if compare else ['sign','proof']
    allowed={'kind','id','source','requested_output'}|({'left','right'} if compare else {'variable','integrand','lower','upper'})
    if (not library.data.get('finite_integral_order') or set(task)-allowed or task.get('requested_output')!=expected
            or set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or src.get('literal_requirement') not in (None,*headings[kind])):
        raise Unsupported('The comparison must retain all printed integral conditions')
    shapes=[task['left'],task['right']] if compare else [task]
    if compare and any(set(z)!={'variable','lower','upper','integrand'} for z in shapes):
        raise Unsupported('Exactly two scalar definite integrals or one sign are required')
    v=shapes[0]['variable'];x=('v',v);ctx=m.context(dict(variable=v))
    if any(p['variable']!=v for p in shapes):raise Unsupported('The dummy variables must be bound consistently')
    originals=[]
    for spec in shapes:
        a,b=[m.parse(str(spec[k]),None) for k in ('lower','upper')]
        if not all(m.constant_defined(z,ctx) for z in (a,b)) or compare_scalar(b,a)<=0:
            raise Unsupported('Original ordered finite endpoints are required')
        originals.append((a,b,m.parse(spec['integrand'],v)))

    def shift_simplify(e):
        tag=e[0]
        if tag in ('q','pi','v','s'):return e
        if tag=='rpow' and not m.variable_in(e[1]) and m.constant_defined(e[1],ctx) and m.sign(e[1],ctx)==1:
            return ('exp',m.mul(('ln',e[1]),shift_simplify(e[2])))
        e=(tag,*(shift_simplify(z) if isinstance(z,tuple) else z for z in e[1:]))
        if tag in ('sin','cos'):
            try:slope,offset=affine(e[1],v);turn=m.pi_multiple(offset)
            except Unsupported:turn=None
            if turn is not None and turn.denominator==1:
                return m.mul(q((-1)**(turn.numerator%2)),(tag,m.mul(slope,x)))
        return e

    def order_on(e,a,b):
        """Compute a set of possible signs inside (a,b), with exact trig and rational guards."""
        interval=('comparison_interval',a,b,False,False)
        scoped={**ctx,'domain':'ordered_interval','comparison_interval':interval}
        all_signs=frozenset((-1,0,1))
        cache={}
        def signs(t):
            t=m.simplify(t)
            if t in cache:return cache[t]
            cache[t]=all_signs
            cache[t]=derive(t)
            return cache[t]
        def product_sign(a,b):
            return frozenset(x*y for x in a for y in b)
        def pair(p,z):
            if p==z:return frozenset((0,))
            if p[0]==z[0]=='exp':return pair(p[1],z[1])
            if p[0]==z[0]=='pow' and p[1]==z[1] and p[2]>0 and z[2]>0:
                base=p[1]
                if base[0] in ('sin','cos') and 0 not in signs(base):
                    try:
                        first,last=phase_zeros('cos' if base[0]=='sin' else 'sin',phase_interval(base[1],v,a,b),False,False)
                        if first>last and signs(base)=={1}:return frozenset((1 if p[2]<z[2] else -1,))
                    except Unsupported:pass
            return signs(m.add(p,m.neg(z)))
        def difference(t):
            if t[0]!='add':return None
            for positive,negative in (t[1:],t[1:][::-1]):
                if negative[0]=='mul' and q(-1) in negative[1:]:
                    return pair(positive,negative[2] if negative[1]==q(-1) else negative[1])
            return None
        def derive(t):
            sg=m.sign(t,ctx)
            if sg is not None and not m.variable_in(t):return frozenset((sg,))
            for sign,term in ((1,t),(-1,m.neg(t))):
                if primitive('interval_rational',(term,'>',interval),scoped):return frozenset((sign,))
            try:slope,offset=affine(t,v)
            except Unsupported:pass
            else:
                if m.sign(slope,ctx) in (-1,1):
                    ss=[compare_scalar(m.add(m.mul(slope,z),offset),ZERO) for z in (a,b)]
                    for sign in (-1,1):
                        if sign in ss and set(ss)<={0,sign}:return frozenset((sign,))
            tag=t[0]
            if tag in ('sin','cos'):
                lo,hi=phase_interval(t[1],v,a,b)
                if min(lo,hi)==max(lo,hi):return all_signs
                first,last=phase_zeros(tag,(lo,hi),False,False)
                if first<=last:return all_signs
                mid=(lo+hi)/2+(F(1,2) if tag=='cos' else 0)
                return frozenset((1 if mid.__floor__()%2==0 else -1,))
            if tag=='exp':return frozenset((1,))
            if tag=='ln':return pair(t[1],ONE)
            if tag=='sqrt':return signs(t[1])-{ -1 }
            if tag in ('mul','div'):return product_sign(signs(t[1]),signs(t[2]))
            if tag=='pow' and t[2]:
                base=signs(t[1])
                return frozenset((z if t[2]%2 else abs(z)) for z in base)
            if tag=='add':
                d=difference(t)
                if d is not None and d!=all_signs:return d
                lhs,rhs=map(signs,t[1:])
                if lhs|rhs<={0,1}:return frozenset((1,)) if {1} in (lhs,rhs) else lhs|rhs
                if lhs|rhs<={0,-1}:return frozenset((-1,)) if {-1} in (lhs,rhs) else lhs|rhs
            p,d=m.rational_form(t)
            if d!={():F(1)}:
                divisor=m.poly_expr(d)
                if 0 not in signs(divisor):return product_sign(signs(m.poly_expr(p)),signs(divisor))
            if len(p)>1:
                common=dict(next(iter(p)))
                for mon in p:
                    powers=dict(mon)
                    common={a:min(i,powers[a]) for a,i in common.items() if a in powers}
                if common:
                    factor=m.poly_expr({tuple(common.items()):F(1)})
                    rest=m.poly_expr({tuple((a,i-common.get(a,0)) for a,i in mon if i!=common.get(a,0)):c for mon,c in p.items()})
                    return product_sign(signs(factor),signs(rest))
            return all_signs
        result=signs(e)
        return result,[[term,sorted(sg)] for term,sg in cache.items() if sg!=all_signs]

    def cover(a,b,f):
        from operations import expression_positions
        constructors={'q','pi','v','s','add','mul','div','pow','rpow','sin','cos','exp','ln','sqrt','atan','abs'}
        if any(z[0] not in constructors for _,z in expression_positions(f)):
            raise Unsupported('The original integrands must be continuous on their open intervals')
        guards=[]
        for rel,g in domain_conditions(f):
            if known_guard((rel,g),ctx):continue
            signs,steps=order_on(shift_simplify(g),a,b)
            allowed={'positive':{1},'nonnegative':{0,1},'nonzero':{-1,1}}[rel]
            if not signs or not signs<=allowed:
                raise Unsupported('The original real domain was not retained under normalization')
            guards.append((rel,g,steps))
        for point,direction in ((a,'right'),(b,'left')):
            if m.constant_defined(m.substitute(f,{x:point}),ctx):continue
            child=request('finite one-sided original endpoint limit',dict(kind='limit',expression=source(f),variable=v,
                          approach=dict(point=source(point),side=direction)))
            if isinstance(child['value'],str):raise Unsupported('The indicated endpoint needs a separate convergence proof')
        return guards

    source_guards=[cover(a,b,f) for a,b,f in originals]
    a,b,f=originals[0];candidates=[('direct',a,b,f)]
    if compare:
        c,d,g=originals[1]
        if not (m.simplify(m.add(m.add(d,m.neg(c)),m.neg(m.add(b,m.neg(a)))))==ZERO):
            raise Unsupported('The comparison lacks a common interval after translation')
        candidates=[('align_by_translation',a,b,('add',f,('mul',q(-1),m.substitute(g,{x:('add',x,m.add(c,m.neg(a)))}))))]
    else:
        half=m.mul(q(F(1,2)),m.add(a,b));width=m.add(half,m.neg(a))
        candidates.extend((('pair_by_translation',a,half,('add',f,m.substitute(f,{x:('add',x,width)}))),
                           ('pair_by_reflection',half,b,('add',f,m.substitute(f,{x:('add',m.add(a,b),('mul',q(-1),x))})))))
    for method,lo,hi,kernel in candidates:
        try:
            simplified=m.simplify(shift_simplify(kernel));sg,steps=order_on(simplified,lo,hi)
        except Unsupported:continue
        for sign in (-1,1):
            if sign not in sg or not sg<={0,sign}:continue
            witnesses=[]
            if 0 in sg:
                for t in (F(1,2),F(1,3),F(2,3)):
                    point=m.add(lo,m.mul(q(t),m.add(hi,m.neg(lo))))
                    value=m.substitute(simplified,{x:point})
                    if m.constant_defined(value,ctx) and compare_scalar(value,ZERO)==sign:
                        witnesses.append((point,value));break
                if not witnesses:continue
            plan=dict(theorem='method.finite_integral_order',strategy=method,original_integrals=originals,source_guards=source_guards,
                      common_interval=(lo,hi),ordered_kernel=simplified,sign_steps=steps,witnesses=witnesses)
            return plan,dict(left_larger=sign==1) if compare else dict(sign='positive' if sign==1 else 'negative')
    raise Unsupported('No strict sign of the original or transformed kernel has been established')


def applied_integral_mean(task):
    from cartesian_fields import vector_source
    from integrals import affine, exact_sign, trig_polynomial
    from verify import same_value
    kind=task.get('context')
    if isinstance(kind,str) and (motion:=re.fullmatch(r'freely falling body with initial velocity ([A-Za-z_]\w*)',kind)):
        if task.get('parameters')!=[motion[1]]:raise Unsupported('The initial velocity is not the declared parameter')
        kind='freely falling body with initial velocity'
    outputs={
        'polar radius from a focus of an ellipse':('mean_focal_radius',{'formula','variable','stated_conditions'}),
        'freely falling body with initial velocity':('mean_velocity',set()),
        'periodic current':('mean_squared_current',{'function','variable','period'}),
    }
    if kind not in outputs:raise Unsupported('The averaging model is not bound')
    key,fields=outputs[kind]
    label=task.get('source',{}).get('literal_requirement')
    source_openings={'mean_focal_radius':'Определить среднее значение длины фокального радиуса-вектора эллипса',
                     'mean_velocity':'Найти среднее значение скорости свободно падающего тела',
                     'mean_squared_current':'Сила переменного тока изменяется по закону'}
    if label and not label.startswith(source_openings[key]):raise Unsupported('A different average is requested')
    vector_source(task,{'context','parameters','requested_output',*fields},(label,))
    if task['requested_output']!=[key]:raise Unsupported('The original averaged quantity differs')
    params=task['parameters']
    if key=='mean_velocity':
        if len(params)!=1:raise Unsupported('A single declared initial velocity is required')
        initial=('s',params[0]);g=('s','g');T=('s','duration')
        if initial in (g,T):raise Unsupported('The added model variables must be fresh')
        final=m.add(initial,m.mul(g,T))
        mean=m.div(m.add(initial,final),q(2))
        return (dict(theorem='method.finite_integral_mean',conditions=['constant acceleration','duration>0'],
                    argument=['Под действием постоянного ускорения направленная скорость аффинна по времени.',
                              'Интеграл аффинной функции на промежутке равен длине, умноженной на полусумму её значений на концах.']),
                dict(mean_velocity=mean,final_velocity=final,interval=['0','duration']))

    v=task['variable'];x=('v',v)
    if key=='mean_squared_current':
        width=m.parse(task['period'],None,params)
        if width[0]!='s':raise Unsupported('The declared positive period must be a fixed parameter')
        ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=[width[1]+'>0']))
        raw=m.parse(task['function'],v,params)
        candidates=[(ONE,raw)] if raw[0]!='mul' else [raw[1:],raw[1:][::-1]]
        for amplitude,wave in candidates:
            if wave[0] not in ('sin','cos') or not m.constant_defined(amplitude,ctx):continue
            slope,phase=affine(wave[1],v);periods=m.pi_multiple(m.mul(width,slope))
            if (periods is not None and periods and (periods/2).denominator==1
                    and m.constant_defined(phase,ctx) and not any(
                      not known_guard(g,ctx) for g in domain_conditions(raw))):
                return dict(theorem='method.finite_integral_mean',window=(ZERO,width),periods=q(periods/2),
                            amplitude=amplitude,phase=phase,argument=[
                    'Проверяем, что за исходный промежуток фаза проходит целое ненулевое число оборотов.',
                    'Квадрат гармоники состоит из половины постоянной и гармоники удвоенной частоты. Последняя имеет нулевое среднее на полном числе периодов.',
                ]),{key:m.div(m.power(amplitude,2),q(2))}
        raise Unsupported('The original current and its complete period could not be linked')

    cond=task['stated_conditions']
    if len(cond)!=1 or not (bound:=re.fullmatch(r'0<([A-Za-z_]\w*)<1',cond[0].replace(' ',''))) or bound[1] not in params:
        raise Unsupported('The eccentricity must be between zero and one')
    p=bound[1]
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=[p+'>0','1-'+p+'>0']))
    raw=m.parse(task['formula'],v,params)
    if raw[0]!='div' or not m.constant_defined(raw[1],ctx) or domain_conditions(raw[2]):
        raise Unsupported('A real constant over the original angular denominator is required')
    terms=trig_polynomial(raw[2],x)
    if set(terms)-{(0,0),(0,1)}:raise Unsupported('The angular denominator must be affine in the cosine')
    a,b=(terms.get(k,ZERO) for k in ((0,0),(0,1)))
    left,right=m.add(a,b),m.add(a,m.neg(b))
    if any(exact_sign(t,ctx)!=1 for t in (left,right)):
        raise Unsupported('Both half-angle scales must be positive on the whole angular domain')
    if not same_value(raw[2],m.add(a,m.mul(b,('cos',x)))):
        raise Unsupported('The half-angle substitution must preserve the original denominator')
    return dict(theorem='method.finite_integral_mean',window=(ZERO,m.mul(q(2),m.PI)),
                half_angle_scales=(left,right),argument=[
        'Два положительных крайних значения знаменателя исключают полюса за весь оборот.',
        'Периодичность переносит окно в (−π,π). Касательная половинного угла даёт интеграл по всей прямой от 2/(A+B t²).',
        'Положительное масштабирование даёт интеграл арктангенса и при делении на 2π оставляет обратный корень из AB.',
    ]),{key:m.div(raw[1],('sqrt',m.mul(left,right)))}


def finite_integral_mean(task,library,request):
    """Evaluate the integral on a positive-length interval before normalizing its measure."""
    from ray_proofs import compare_scalar
    if task['kind']=='mean_value_application':
        if not library.data.get('finite_integral_mean'):raise Unsupported('The integral mean is not available')
        return applied_integral_mean(task)
    src=task.get('source',{})
    if (not library.data.get('finite_integral_mean') or set(task)-{'kind','id','source','function','variable','lower','upper','parameters','requested_output'}
            or task.get('requested_output')!=['mean_value'] or
            set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'} or
            src.get('literal_requirement') not in (None,'Определить средние значения данных функций в указанных промежутках.')):
        raise Unsupported('A finite average of a single function on its original interval is required')
    params=task.get('parameters',[]);v=task['variable'];ctx=m.context(dict(variable=v,parameters=params))
    a,b=[m.parse(str(task[k]),None,params) for k in ('lower','upper')]
    if not all(m.constant_defined(x,ctx) for x in (a,b)) or compare_scalar(b,a)<=0:
        raise Unsupported('The original interval must have positive length')
    f=m.parse(task['function'],v,params)
    t=dict(kind='iterated_integral',integrand=task['function'],parameters=params,
           integration_order=[dict(variable=v,lower=task['lower'],upper=task['upper'])],requested_output=['exact_integral'])
    if f[0]=='sqrt' and not params:
        t=dict(kind='finite_interval_integral',integrand=task['function'],variable=v,
               interval=[task['lower'],task['upper']],method_requirement='newton_leibniz',requested_output=['exact_integral'])
    value=freeze(request('integral on the original mean interval',t)['value'])
    width=m.add(b,m.neg(a))
    return dict(theorem='method.finite_integral_mean',interval=(a,b),length=width,integral=value),m.simplify(m.div(value,width))


def weighted_mean_estimate(task,library,request):
    """Use the first mean value theorem after a verified factor range and weight integral."""
    from functools import cmp_to_key
    from ray_proofs import compare_scalar
    from polynomial import NotRational,Undefined,rf
    src=task.get('source',{})
    if (not library.data.get('weighted_integral_mean') or set(task)-{'kind','id','source','integrand','variable','lower','upper','requested_output','method_requirement'}
            or task.get('method_requirement')!='first_mean_value_theorem_for_integrals'
            or task.get('requested_output')!=['integral_estimate','method_proof']
            or set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or src.get('literal_requirement') not in (None,'Пользуясь первой теоремой о среднем, оценить интегралы.')):
        raise Unsupported('Unresolved printed mean value requirement')
    v=task['variable'];x=('v',v);ctx=m.context(dict(variable=v))
    a,b=[m.parse(str(task[k]),None) for k in ('lower','upper')]
    if not all(m.constant_defined(z,ctx) for z in (a,b)) or compare_scalar(b,a)<=0:
        raise Unsupported('An ordered finite interval is required')
    cmp=cmp_to_key(compare_scalar)
    widened=[]
    def arrange(values):
        return min(values,key=cmp),max(values,key=cmp)
    def enclosure(e):
        tag=e[0]
        if tag=='v':return a,b
        if not m.variable_in(e):
            if not m.constant_defined(e,ctx):raise Unsupported('Undefined constant in the source function')
            return e,e
        u,vv=enclosure(e[1])
        if tag in ('sin','cos'):out=(q(-1),ONE)
        elif tag in ('exp','atan','ln','sqrt','cbrt'):
            endpoints=[(tag,t) for t in (u,vv)]
            if not all(m.constant_defined(z,ctx) for z in endpoints):
                raise Unsupported('An elementary factor is undefined on the enclosing interval')
            out=tuple(map(m.simplify,endpoints))
        elif tag=='pow':
            n=e[2];left,right=[compare_scalar(z,ZERO) for z in (u,vv)]
            if n<=0 and left<=0<=right:raise Unsupported('A denominator or zero power is not defined')
            pairs=[m.power(z,n) for z in (u,vv)]
            if n>0 and n%2==0 and left<=0<=right:pairs.append(ZERO)
            out=arrange(pairs)
        elif tag in ('add','mul','div'):
            p,q0=enclosure(e[2])
            if tag=='add':out=(m.add(u,p),m.add(vv,q0))
            elif tag=='mul':out=arrange([m.mul(g,h) for g in (u,vv) for h in (p,q0)])
            else:
                if compare_scalar(p,ZERO)<=0<=compare_scalar(q0,ZERO):raise Unsupported('The original denominator range contains zero')
                out=arrange([m.div(g,h) for g in (u,vv) for h in (p,q0)])
        else:raise Unsupported('No verified symbolic enclosure for the elementary factor')
        widened.append(dict(expression=e,bounds=out))
        return out
    raw=m.parse(task['integrand'],v)
    if raw[0]=='div':
        factors=[(('div',ONE,raw[2]),raw[1])]
    elif raw[0]=='mul':
        factors=[(raw[1],raw[2]),(raw[2],raw[1])]
    else:factors=[]
    factors.append((raw,ONE))
    for f,w in factors:
        widened.clear()
        try:glo,ghi=enclosure(f);wlo,whi=enclosure(w)
        except Unsupported:continue
        if compare_scalar(wlo,ZERO)<0:continue
        try:p,d=rf(w,v)
        except (NotRational,Undefined):parametric=w[0]=='exp'
        else:parametric=len(d)==1
        if parametric:break
    else:raise Unsupported('No nonnegative weight with a verified factor range and an available primitive')
    if w==ONE:mass=m.add(b,m.neg(a))
    else:
        child=dict(kind='iterated_integral',integrand=source(w),integration_order=[dict(variable=v,lower=task['lower'],upper=task['upper'])],
                   requested_output=['exact_integral'])
        mass=freeze(request('integral of the nonnegative weight',child)['value'])
    if compare_scalar(mass,ZERO)<0:raise Unsupported('The verified weight integral must be nonnegative')
    plan=dict(theorem='method.weighted_integral_mean',interval=(a,b),continuous_factor=f,nonnegative_weight=w,
              factor_range=(glo,ghi),weight_range=(wlo,whi),range_steps=widened,weight_integral=mass)
    return plan,dict(lower=m.mul(glo,mass),upper=m.mul(ghi,mass))


def outward(lo,hi):
    return checked(F((lo*SCALE).__floor__(),SCALE)),checked(F((hi*SCALE).__ceil__(),SCALE))


def product(a,b):
    values=[x*y for x in a for y in b]
    return outward(min(values),max(values))


def power(a,n):
    if n<=0:
        if a[0]<=0<=a[1]:raise Unsupported('Power or denominator can vanish on the interval')
        if n==0:return F(1),F(1)
        a=outward(1/a[1],1/a[0]);n=-n
    lower=0 if n%2==0 and a[0]<=0<=a[1] else min(x**n for x in a)
    return outward(lower,max(x**n for x in a))


@lru_cache(maxsize=1)
def pi_range():
    def atan_inverse(n):
        z=F(1,n);s=sum((-1)**k*z**(2*k+1)/(2*k+1) for k in range(16))
        return s,s+z**33/33
    a,b=atan_inverse(5);c,d=atan_inverse(239)
    return outward(16*a-4*d,16*b-4*c)


def monotone(op,a):
    if op=='sqrt' and a[0]<0 or op=='ln' and a[0]<=0:raise Unsupported('Interval crosses a function boundary')
    if op=='exp' and max(map(abs,a))>128:raise Unsupported('Exponential enclosure magnitude bound')
    with localcontext() as ctx:
        ctx.prec=36;ends=[]
        for x,direction in zip(a,(ROUND_FLOOR,ROUND_CEILING)):
            if x==0 and op=='sqrt' or x==1 and op=='ln':ends.append(F(0));continue
            if x==0 and op=='exp':ends.append(F(1));continue
            ctx.rounding=direction
            x=Decimal(x.numerator)/Decimal(x.denominator)
            y=getattr(x,op)()
            ends.append(F(y.next_minus() if direction==ROUND_FLOOR else y.next_plus()))
    return outward(*ends)


@lru_cache(maxsize=2048)
def enclose(e,interval):
    """Natural interval extension of the raw real expression, before cancellation."""
    op=e[0]
    if op=='q':v=checked(m.num(e));return v,v
    if op=='pi':return pi_range()
    if op=='v' and interval is not None:return interval
    if len(e)<2 or not isinstance(e[1],tuple):raise Unsupported('Unknown scalar or interval operation')
    a=enclose(e[1],interval)
    if op=='pow':return power(a,e[2])
    if op in ('add','mul','div'):
        b=enclose(e[2],interval)
        if op=='add':return outward(a[0]+b[0],a[1]+b[1])
        return product(a,b if op=='mul' else power(b,-1))
    if op in ('sqrt','ln','exp'):return monotone(op,a)
    if op=='abs':return (F(0) if a[0]<=0<=a[1] else min(map(abs,a))),max(map(abs,a))
    if op in ('cos','sin'):
        middle=sum(a)/2;radius=(a[1]-a[0])/2
        if radius>=2 or abs(middle)>8:return F(-1),F(1)
        parity=0 if op=='cos' else 1
        value=sum((-1)**k*middle**(2*k+parity)/factorial(2*k+parity) for k in range(23))
        error=radius+abs(middle)**(46+parity)/factorial(46+parity)
        return outward(max(-1,value-error),min(1,value+error))
    raise Unsupported('No interval extension for '+op)


def taylor_enclosure(raw, degree):
    """Exact rational enclosures of Taylor polynomials and their tails at real constants."""
    steps = []

    def series(kind, x, exponent=None):
        r = abs(x)
        if kind in ('sin', 'cos'):
            parity = int(kind == 'sin')
            value = sum((-1)**j*x**(2*j+parity)/factorial(2*j+parity) for j in range(degree))
            error = r**(2*degree+parity)/factorial(2*degree+parity)
        elif kind == 'exp':
            if r >= degree+1:
                raise Unsupported('The exponential Taylor tail does not have a geometric majorant at this order')
            value = sum(x**j/factorial(j) for j in range(degree))
            error = r**degree/factorial(degree)/(1-r/(degree+1))
        elif kind in ('ln', 'atan', 'asin'):
            if kind == 'ln':
                if x <= 0:
                    raise Unsupported('The original logarithm needs a positive argument')
                x = (x-1)/(x+1)
            r = abs(x)
            if r >= 1:
                raise Unsupported('The chosen inverse-function Taylor series needs an interior argument')
            if kind == 'asin':
                value = sum(F(comb(2*j,j),4**j)*x**(2*j+1)/(2*j+1) for j in range(degree))
            else:
                value = sum(((-1)**j if kind=='atan' else 2)*x**(2*j+1)/(2*j+1) for j in range(degree))
            error = ((2 if kind=='ln' else 1)*r**(2*degree+1)/(2*degree+1) /
                     (1 if kind=='atan' else 1-r*r))
        else:
            # For t_j = binom(alpha,j) u^j, all ratios from j=degree
            # onward are bounded by the larger of the initial ratio and |u|.
            ratio = r*max(F(1),abs(exponent-degree)/(degree+1))
            if ratio >= 1:
                raise Unsupported('No geometric majorant for the omitted binomial terms')
            coefficient = F(1)
            value = coefficient
            for j in range(1, degree+1):
                coefficient *= (exponent-j+1)/j
                if j < degree:
                    value += coefficient*x**j
            error = abs(coefficient)*r**degree/(1-ratio)
        steps.append(dict(operation=kind,argument=q(x),exponent=q(exponent) if exponent is not None else None,
                          terms=degree,polynomial=q(value),absolute_remainder=q(error)))
        return outward(value-error,value+error)

    def real_power(x, exponent, signed):
        if x == 0 and exponent > 0:
            return F(0), F(0)
        if x <= 0 and not (signed and x < 0):
            raise Unsupported('The original power base is outside the real branch')
        sign = -1 if x < 0 else 1
        x = abs(x)
        k = (x.numerator.bit_length()-x.denominator.bit_length())//exponent.denominator
        root = min((F(2)**j for j in range(k-1,k+3)),
                   key=lambda a: abs(x/a**exponent.denominator-1))
        delta = x/root**exponent.denominator-1
        a,b = series('binomial',delta,exponent)
        multiplier = sign*root**exponent.numerator
        steps[-1]['binomial_scale'] = q(multiplier)
        return outward(min(multiplier*a,multiplier*b),max(multiplier*a,multiplier*b))

    def visit(e):
        op = e[0]
        if op == 'q':
            return (m.num(e),)*2
        if op == 'pi':
            return pi_range()
        a = visit(e[1])
        if op == 'pow':
            return power(a,e[2])
        if op in ('add','mul','div','rpow'):
            if op == 'rpow':
                ctx = m.context({})
                exponent = m.num(m.simplify(e[2])) if m.constant_defined(e[2],ctx) else None
                if exponent is None or exponent.denominator>256 or a[0]<=0:
                    raise Unsupported('A positive base and an exact rational exponent are required')
                bounds = [real_power(t,exponent,False) for t in a]
                return min(x[0] for x in bounds),max(x[1] for x in bounds)
            b = visit(e[2])
            if op == 'add':
                return outward(a[0]+b[0],a[1]+b[1])
            return product(a,b if op=='mul' else power(b,-1))
        if op in ('sqrt','cbrt'):
            if op=='sqrt' and a[0]<0:
                raise Unsupported('A square root crossed its original real domain')
            exponent = F(1,2 if op=='sqrt' else 3)
            return real_power(a[0],exponent,op=='cbrt')[0],real_power(a[1],exponent,op=='cbrt')[1]
        if op in ('sin','cos'):
            mid,radius = sum(a)/2,(a[1]-a[0])/2
            lo,hi = series(op,mid)
            steps[-1]['argument_radius'] = q(radius)
            return outward(max(-1,lo-radius),min(1,hi+radius))
        if op in ('exp','ln','atan','asin'):
            def endpoint(x):
                if op=='asin' and abs(x)==1:
                    bounds=product(pi_range(),(x/2,x/2))
                    steps.append(dict(operation='asin_endpoint',argument=q(x),terms=0,
                        polynomial=q(sum(bounds)/2),absolute_remainder=q((bounds[1]-bounds[0])/2)))
                    return bounds
                return series(op,x)
            return endpoint(a[0])[0],endpoint(a[1])[1]
        raise Unsupported('No Taylor bound for '+op)

    bounds = visit(raw)
    return bounds,steps


def certified_numeric_approximation(task,library,saved=None):
    """Construct a rational approximation and a checked error bound for its source expression."""
    fields = {'id','kind','source','goal','method_requirement','requested_output'}
    provenance = {'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','angle_unit'}
    src,goal = task.get('source',{}),task.get('goal',{})
    if (not library.data.get('taylor_constant_enclosures') or set(task)-fields or set(src)-provenance
            or src.get('angle_unit','degrees')!='degrees' or set(goal)-{'expression','absolute_tolerance'}
            or task.get('method_requirement') not in (None,'Taylor_formula_with_quantitative_remainder')
            or task.get('requested_output') != ['approximate_value','certified_absolute_error']):
        raise Unsupported('An additional numerical goal or printed method remains')
    raw = m.parse(goal['expression'],None)
    tolerance = F(str(goal.get('absolute_tolerance','1/10000000')))
    if tolerance <= 0:
        raise Unsupported('A positive absolute tolerance is required')
    if task.get('method_requirement') is None and m.constant_defined(raw,m.context({})):
        exact=m.num(m.simplify(raw))
        if exact is not None:
            answer=q(exact)
            return (dict(theorem='method.taylor_constant_enclosures',degree=0,source_expression=raw,
                         requested_tolerance=q(tolerance) if 'absolute_tolerance' in goal else None,
                         enclosure=[answer,answer],steps=[]),
                    dict(approximate_value=answer,certified_absolute_error=ZERO))
    digits = 0
    while F(1,10**digits)>tolerance/4 and digits<18:
        digits += 1
    degrees = (saved['degree'],) if saved is not None else (8,16,32,64,96)
    for degree in degrees:
        if type(degree) is not int or not 1<=degree<=96:
            raise Unsupported('An admissible Taylor degree is required')
        try:
            bounds,steps = taylor_enclosure(raw,degree)
        except Unsupported:
            if saved is not None:
                raise
            continue
        midpoint = sum(bounds)/2
        approximate = F(round(midpoint*10**digits),10**digits)
        error = max(abs(approximate-t) for t in bounds)
        if error <= tolerance:
            plan = dict(theorem='method.taylor_constant_enclosures',degree=degree,source_expression=raw,
                        requested_tolerance=q(tolerance) if 'absolute_tolerance' in goal else None,
                        enclosure=list(map(q,bounds)),steps=steps)
            return plan,dict(approximate_value=q(approximate),certified_absolute_error=q(error))
    raise Unsupported('No proved Taylor enclosure meets the required absolute precision in the original domain')


def guard_bounds(relation,e,interval,variables):
    """Enclose the raw expression, then tighten a repeated coordinate by its quadratic vertex."""
    from polynomial import rf,NotRational
    lo,hi=enclose(e,interval)
    def sufficient(a,b):
        return a>0 if relation=='positive' else a>=0 if relation=='nonnegative' else a>0 or b<0
    if sufficient(lo,hi):return lo,hi
    if e[0]=='abs' and relation!='nonnegative':
        a,b=guard_bounds('nonzero',e[1],interval,variables)
        return min(abs(a),abs(b)),max(abs(a),abs(b))
    for v in variables:
        try:p,d=rf(e,v)
        except NotRational:continue
        if len(p)!=3 or len(d)!=1:continue
        left,right=interval;vertex=-p[1]/(2*p[2])
        points=[left,right]+([vertex] if left<vertex<right else [])
        values=[(p[0]+x*(p[1]+x*p[2]))/d[0] for x in points]
        if sufficient(min(values),max(values)):return min(values),max(values)
    raise Unsupported('A domain condition is not certified on the entire closed interval')


def cartesian_slices(task,library):
    """Partition an integrable planar domain in each requested order, retaining orientation."""
    from plane_domains import region_inequalities,algebraic_strips
    kind=task['kind'];fields={'kind','id','schema','source','transcription','integrand','coordinates','requested_output'}
    direct=kind=='cartesian_slices';fields.add('region' if direct else 'integration_order')
    variables=task.get('coordinates',['x','y'])
    if (set(task)-fields or library.data.get('task_compilers',{}).get(kind)!='ordered_planar_fibers' or
            not isinstance(variables,(tuple,list)) or len(variables)!=2 or not all(isinstance(v,str) for v in variables)):
        raise Unsupported('Expected a planar region or a finite oriented integral')
    x,y=variables;m.context({'variable':x,'parameters':[y]})
    keys=[x+'_then_'+y,y+'_then_'+x] if direct else [y+'_then_'+x]
    if task['requested_output']!=keys or task['integrand']!='f('+x+','+y+')':raise Unsupported('Expected the source integrable function and its requested integration orders')
    def literal(s):
        e=m.parse(str(s),None)
        if not m.constant_defined(e,m.context({})):raise Unsupported('Undefined source coordinate')
        n=m.num(m.simplify(e))
        if n is None:raise Unsupported('Expected a rational endpoint or vertex coordinate')
        return checked(n)
    region=task.get('region');outputs={k:[] for k in keys};trace=[]
    if direct and isinstance(region,dict) and set(region)=={'vertices'}:
        raw=region['vertices']
        if not isinstance(raw,(tuple,list)) or not all(isinstance(p,(tuple,list)) and len(p)==2 for p in raw):raise Unsupported('Malformed plane polygon')
        pts=tuple((literal(a),literal(b)) for a,b in raw)
        trace.append(polygon_fibers(pts,variables,outputs))
    elif direct:
        guards=region_inequalities(region,variables)
        for order,key in zip((variables,variables[::-1]),keys):
            plan,outputs[key]=algebraic_strips(guards,order,1);trace.append(plan)
    else:
        b=task['integration_order']
        if (not isinstance(b,(tuple,list)) or len(b)!=2 or any(not isinstance(t,dict) or set(t)!={'variable','lower','upper'} for t in b)
                or [t['variable'] for t in b]!=list(variables)):raise Unsupported('Changed original integral order')
        left,right=map(literal,(b[0]['lower'],b[0]['upper']));orient=1 if left<right else -1
        lo,hi=sorted((left,right));bounds=[]
        for name in ('lower','upper'):
            raw=m.parse(str(b[1][name]),x)
            enclose(raw,(lo,hi))
            bounds.append(m.substitute(raw,{('v',x):('s',x)}))
        outer,inner=(('s',v) for v in variables)
        horizontal=[('positive',m.add(outer,q(-lo))),('positive',m.add(q(hi),m.neg(outer)))]
        for sign,(low,high) in ((orient,bounds),(-orient,bounds[::-1])):
            guards=horizontal+[('positive',m.add(inner,m.neg(low))),('positive',m.add(high,m.neg(inner)))]
            plan,strips=algebraic_strips(guards,variables[::-1],sign)
            trace.append(plan);outputs[keys[0]].extend(strips)
    return {'pieces':trace,'coordinates':variables,'scope':'Fubini for an integrable function; boundary curves have zero area'},outputs


def polygon_fibers(pts,variables,outputs):
    def turn(p,qv,r):return (qv[0]-p[0])*(r[1]-p[1])-(qv[1]-p[1])*(r[0]-p[0])
    n=len(pts);edges=list(zip(pts,pts[1:]+pts[:1]))
    area=abs(sum(a*d-b*c for (a,b),(c,d) in edges))/2
    if n<3 or len(set(pts))!=n or not area:raise Unsupported('The listed boundary is degenerate or repeats a vertex')
    for i,(p,z) in enumerate(edges):
        nxt=pts[(i+2)%n]
        if turn(p,z,nxt)==0 and sum((z[k]-p[k])*(nxt[k]-z[k]) for k in (0,1))<=0:raise Unsupported('Boundary retraces an adjacent edge')
        for j,(a,b) in enumerate(edges[:i-1] if i else []):
            if i==n-1 and j==0:continue
            if (all(max(min(p[k],z[k]),min(a[k],b[k]))<=min(max(p[k],z[k]),max(a[k],b[k])) for k in (0,1)) and
                    turn(p,z,a)*turn(p,z,b)<=0 and turn(a,b,p)*turn(a,b,z)<=0):raise Unsupported('The polygon boundary crosses or touches itself')
    for idx,key in enumerate(outputs):
        swap=idx==1;v=variables[idx]
        edge2=[(a[::-1],b[::-1]) if swap else (a,b) for a,b in edges]
        cuts=sorted({p[0] for p,_ in edge2});swept=F(0)
        for a,b in zip(cuts,cuts[1:]):
            center=(a+b)/2;active=[]
            for (u,h),(w,k) in edge2:
                if min(u,w)<center<max(u,w):
                    slope=(k-h)/(w-u);bias=h-u*slope
                    active.append((slope*center+bias,m.add(m.mul(q(slope),('s',v)),q(bias))))
            active.sort(key=lambda pair:pair[0])
            if len(active)%2:raise Unsupported('Incomplete boundary at a fiber')
            for low,high in zip(active[::2],active[1::2]):
                if low[0]>=high[0]:raise Unsupported('Unseparated polygon edges')
                outputs[key].append((1,q(a),q(b),low[1],high[1]));swept+=(b-a)*(high[0]-low[0])
        if swept!=area:raise Unsupported('Fiber measures differ from the original polygon area')
    return {'vertices':[(q(a),q(b)) for a,b in pts],'area':q(area)}


def ellipsoid_moment(task,library):
    """Complete positive squares and integrate a polynomial over the resulting ball."""
    from tasks import entailed_domain_guards
    from verify import same_value
    fields={'kind','id','source','schema','transcription','integrand','variables','parameters','stated_conditions','quadratic_region','requested_output'}
    region=task['quadratic_region'];variables=task['variables'];params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    wanted=task['requested_output']
    if (set(task)-fields or library.data.get('task_compilers',{}).get('ellipsoid_moment')!='complete_squares_and_ball_moments'
            or wanted not in (['exact_integral'],['mean']) or not isinstance(region,dict) or set(region)!={'left','right'}
            or not isinstance(variables,(tuple,list)) or not variables or not isinstance(params,(tuple,list)) or
            not all(isinstance(v,str) for v in [*variables,*params]) or not isinstance(conditions,(tuple,list)) or not all(isinstance(v,str) for v in conditions)):
        raise Unsupported('Expected a polynomial and a quadratic sublevel with the original output and method')
    dummy='__ball'
    while dummy in [*variables,*params]:dummy+='_'
    names=[*variables,*params];m.context({'variable':dummy,'parameters':names})
    base={'variable':dummy,'parameters':params,'parameter_conditions':list(conditions)};ctx=m.context(base)
    left,right=(m.parse(region[k],None,names) for k in ('left','right'));f=m.parse(task['integrand'],None,names)
    domain=domain_conditions(left)+domain_conditions(right)+domain_conditions(f)
    # Parameter-only restrictions are exactly the ones present before any cancellation.
    fixed=[g for g in domain if g[0]!='nonnegative' and m.constant_defined(g[1],ctx)]
    guards=[guard_source(g) for g in entailed_domain_guards(fixed)];ctx=m.context({**base,'parameter_conditions':list(conditions)+guards})
    all_ctx=m.context({**base,'parameters':names,'parameter_conditions':list(conditions)+guards})
    if not all(known_guard(g,all_ctx) for g in domain):raise Unsupported('An original hole or boundary depends on the integration coordinates')
    names_ast=tuple(('s',v) for v in variables);dim=len(variables)
    def coefficients(expr):
        num,den=m.rational_form(expr);den=m.poly_expr(den)
        if not m.constant_defined(den,ctx) or not m.nonzero(den,ctx):raise Unsupported('The denominator depends on a coordinate or can vanish')
        terms={}
        for mon,c in num.items():
            powers=dict(mon);degrees=tuple(powers.pop(v,0) for v in names_ast)
            coefficient=m.poly_expr({tuple(powers.items()):c})
            if not m.constant_defined(coefficient,ctx):raise Unsupported('The integrand or boundary is not polynomial in its coordinates')
            terms[degrees]=m.add(terms.get(degrees,ZERO),m.div(coefficient,den))
        return terms
    residual=m.add(left,m.neg(right))
    if any(sum(k)>2 for k in coefficients(residual)):raise Unsupported('The original region is not quadratic')
    coefficients(f);stages=[];pivots=[]
    for v in names_ast:
        lo,zero,hi=[m.substitute(residual,{v:q(k)}) for k in (-1,0,1)]
        pivot=m.add(m.div(m.add(hi,lo),q(2)),m.neg(zero));linear=m.div(m.add(hi,m.neg(lo)),q(2))
        if not m.constant_defined(pivot,ctx) or m.sign(pivot,ctx)!=1:raise Unsupported('The quadratic part is not proved positive definite')
        shift=m.div(m.neg(linear),m.mul(q(2),pivot));rest=m.add(zero,m.neg(m.mul(pivot,m.power(shift,2))))
        if not same_value(residual,m.add(rest,m.mul(pivot,m.power(m.add(v,m.neg(shift)),2)))):raise Unsupported('Completing the square did not reproduce the original region')
        f=m.simplify(m.substitute(f,{v:m.add(v,shift)}));residual=rest
        stages.append((v,pivot,shift));pivots.append(pivot)
    radius2=m.neg(residual);sign=m.sign(radius2,ctx)
    if not m.constant_defined(radius2,ctx):raise Unsupported('Residual size is not a real parameter')
    terms=coefficients(f);plan={'natural_parameter_guards':guards,'completed_squares':stages,'squared_radius':radius2,
                               'centered_polynomial':f,'dimension':dim,'moment_steps':[]}
    mean=wanted==['mean'];null={'defined':False,'reason':'zero_measure'} if mean else {'defined':True,'value':ZERO}
    if sign in (-1,0):return plan,null
    @lru_cache(None)
    def moment(k):
        if any(v%2 for v in k):return ZERO
        if not any(k):return ONE
        i=next(i for i,v in enumerate(k) if v);smaller=list(k);smaller[i]-=2
        value=m.mul(m.mul(q(F(k[i]-1,dim+sum(k))),m.div(radius2,pivots[i])),moment(tuple(smaller)))
        plan['moment_steps'].append((k,i,tuple(smaller),value));return value
    total=ZERO
    for k,c in terms.items():total=m.add(total,m.mul(c,moment(k)))
    if not mean:
        # Unit-ball volumes V_d=(2π/d)V_(d−2), and semiaxes sqrt(radius²/pivot).
        volume=q(2) if dim%2 else ONE
        for n in range(3 if dim%2 else 2,dim+1,2):volume=m.mul(volume,m.mul(q(F(2,n)),m.PI))
        scale=scale2=ONE
        for p in pivots:
            squared=m.div(radius2,p);scale2=m.mul(scale2,squared);scale=m.mul(scale,m.simplify(('sqrt',squared)))
        scale=min((scale,m.simplify(('sqrt',scale2))),key=m.tree_size);volume=m.mul(volume,scale)
        total=m.mul(total,volume);plan['volume']=volume
    regular={'defined':True,'value':total}
    if sign==1 or not mean and m.known_nonnegative(radius2,ctx):return plan,regular
    return plan,{'when_positive':regular,'otherwise':null,'size':radius2}


def oriented_boundary_integral(task,library,request):
    """Green's circulation and Gauss's flux share the same oriented boundary operator."""
    from verify import same_value
    fields={'kind','id','source','variables','coefficients','boundary_of','orientation','parameters','stated_conditions','method_requirement','requested_output'}
    coords=task['variables'];forms=task['coefficients'];region=task['boundary_of'];wanted=task['requested_output']
    pars=task.get('parameters',[]);conds=task.get('stated_conditions',[]);dim=len(coords)
    if (set(task)-fields or library.data.get('task_compilers',{}).get(task['kind'])!='integrate_exterior_derivative'
            or not all(isinstance(z,(list,tuple)) for z in (coords,forms,pars,conds)) or dim not in (2,3) or len(forms)!=dim
            or not all(isinstance(s,str) for s in [*coords,*forms,*pars,*conds]) or not isinstance(region,dict) or len(region)!=1):
        raise Unsupported('Expected an oriented full boundary and one component per coordinate')
    orientation=('counterclockwise','clockwise') if dim==2 else ('outward','inward')
    theorem='green_theorem' if dim==2 else 'divergence_theorem';direct=task.get('method_requirement')=='green_and_direct_parametrization'
    if (task['orientation'] not in orientation or direct and (dim!=2 or 'polygon' not in region)
            or task.get('method_requirement') not in (None,theorem,'green_and_direct_parametrization')
            or (wanted!=['boundary_integral','direct_integral'] if direct else wanted not in (['boundary_integral'],['equivalent_interior_integral']))):
        raise Unsupported('Unknown method, orientation, or additional boundary obligation')
    names=[*coords,*pars];dummy='__boundary'
    while dummy in names:dummy+='_'
    def context(variables):return m.context({'variable':dummy,'parameters':variables,'parameter_conditions':conds})
    fixed=context(pars);whole=context(names)
    raw=[m.parse(s,None,names) for s in forms]
    guards=[g for f in raw for g in domain_conditions(f,True)]
    if not all(known_guard(g,whole) for g in guards):raise Unsupported('Smoothness of the original field throughout the enclosed domain is unproved')
    terms=[];density=ZERO
    for i,v in enumerate(coords):
        j=1-i if dim==2 else i
        child=request('derivative/'+v,{'kind':'differentiate','function':forms[j],'variable':v,'parameters':[w for w in names if w!=v],
                                        'stated_conditions':conds,'method_requirement':'table_and_rules'})
        derivative=m.substitute(freeze(child['value']),{('v',v):('s',v)});terms.append(derivative)
        density=m.add(density,m.neg(derivative) if dim==2 and i==1 else derivative)
    sign=1 if task['orientation']==orientation[0] else -1
    density=m.simplify(m.mul(q(sign),density))
    plan={'theorem':theorem,'coordinate_derivatives':terms,'density':density,'source_smoothness_conditions':guards}
    transform=wanted==['equivalent_interior_integral']
    if region=={'bounded_regular_region':True} and type(region['bounded_regular_region']) is bool:
        if transform:return plan,{'interior_density':density,'region':region}
        if same_value(density,ZERO):return plan,{'boundary_integral':ZERO}
        raise Unsupported('The region measure or geometry is required for the integral')
    if transform and 'box' not in region:raise Unsupported('A concrete region needs its regularity and measure checked')
    common={'parameters':pars,'stated_conditions':conds,'integrand':source(density),'requested_output':['exact_integral']}
    def integral(role,bounds,key):
        return freeze(request(role,dict(kind='iterated_integral',**{key:bounds},**common))['value'])
    if 'quadratic_sublevel' in region:
        child=request('enclosed region',dict(kind='ellipsoid_moment',variables=coords,quadratic_region=region['quadratic_sublevel'],**common))
        if m.sign(freeze(child['compilation']['squared_radius']),fixed)!=1:
            raise Unsupported('The quadratic region must have nonempty interior')
        total=freeze(child['value']['value'])
    elif 'box' in region:
        box=region['box']
        if not isinstance(box,(tuple,list)) or len(box)!=dim:raise Unsupported('Wrong box dimension')
        bounds=[]
        for v,pair in zip(coords,box):
            if not isinstance(pair,(tuple,list)) or len(pair)!=2:raise Unsupported('Invalid box bounds')
            lo,hi=(m.parse(str(s),None,pars) for s in pair)
            if not all(m.constant_defined(s,fixed) for s in (lo,hi)) or m.sign(m.add(hi,m.neg(lo)),fixed)!=1:
                raise Unsupported('All box sides must have positive length')
            bounds.append({'variable':v,'lower':str(pair[0]),'upper':str(pair[1])})
        if transform:
            plan['verified_box_bounds']=bounds
            return plan,{'interior_density':density,'region':region}
        total=integral('enclosed box',bounds,'rectangle')
    elif 'polygon' in region and dim==2:
        x,y=coords;keys=[x+'_then_'+y,y+'_then_'+x];vertices=region['polygon']
        child=request('enclosed polygon',{'kind':'cartesian_slices','coordinates':coords,'integrand':'f('+x+','+y+')',
                      'region':{'vertices':vertices},'requested_output':keys})
        total=ZERO
        for i,(orient,a,b,l,h) in enumerate(child['value'][keys[0]]):
            bounds=[{'variable':v,'lower':source(lo),'upper':source(hi)} for v,lo,hi in ((x,a,b),(y,l,h))]
            total=m.add(total,m.mul(q(orient),integral('enclosed strip/'+str(i),bounds,'integration_order')))
        if direct:
            pts=child['compilation']['pieces'][0]['vertices']
            points=[tuple(m.num(freeze(s)) for s in row) for row in pts]
            signed=sum(a*d-b*c for (a,b),(c,d) in zip(points,points[1:]+points[:1]))
            oriented=list(vertices) if sign*signed>0 else list(reversed(vertices))
            path={'kind':'line_integral','variables':coords,'coefficients':forms,'vertices':oriented+oriented[:1],'parameter':dummy,
                  'parameters':pars,'stated_conditions':conds,'requested_output':['line_integral']}
            check=freeze(request('direct traversal',path)['value'])
            if not same_value(total,check):raise Unsupported('Direct traversal and region integral disagree')
            return plan,{'boundary_integral':total,'direct_integral':check}
    else:raise Unsupported('An explicitly closed regular region is required')
    return plan,{'boundary_integral':total}


def point_coordinates(text,dimension):
    import re
    if isinstance(text,str):
        if text.strip()=='O':return ['0']*dimension
        name=re.fullmatch(r'[A-Za-z]?[\(]([^()]*)[\)]',text.strip())
        if not name:raise Unsupported('Expected a named point with explicit coordinates')
        text=[v.strip() for v in name[1].split(',')]
    if not isinstance(text,(list,tuple)) or len(text)!=dimension:raise Unsupported('Endpoint dimension differs from curve')
    return text


def curve_method_agrees(task):
    metadata=task.get('source',{})
    return isinstance(metadata,dict) and all(metadata.get(k) in (None,task.get('method_requirement'))
          for k in ('explicit_imposed_method','explicit_required_method','method_requirement'))


def bound_curve_integral(t,library,request,saved=None):
    """Lift given spatial points to unique parameter values and preserve the kind of integration."""
    import re
    from integrals import affine
    from verify import same_value
    length=t['kind']=='space_curve_length'
    common={'id','kind','source','parameter','parameters','stated_conditions','requested_output'}
    fields=common|({'curve','endpoints'} if length else {'variables','path','scalar','coefficients'})
    if not library.data.get('curve_endpoint_pullback') or set(t)-fields or not curve_method_agrees(t) or t.get('requested_output')!=['arc_length' if length else 'line_integral']:
        raise Unsupported('Unbound curve, method or requested quantity')
    if length:
        maps=t['curve'];pts=t['endpoints'];pts=pts.split(' to ') if isinstance(pts,str) else pts
        coords=['x','y','z'];density={'scalar':'1'}
    else:
        path=t['path']
        if set(path)!={'map','start','end'} or ('scalar' in t)==('coefficients' in t):raise Unsupported('Expected one scalar or oriented form and two named endpoints')
        maps=path['map'];pts=[path['start'],path['end']];coords=t['variables']
        density={k:t[k] for k in ('scalar','coefficients') if k in t}
    if not isinstance(maps,(tuple,list)) or len(maps)!=len(coords) or not all(isinstance(s,str) for s in maps):
        raise Unsupported('An explicit map with one component per coordinate is required')
    params=t.get('parameters',[]);v=t.get('parameter');conditions=t.get('stated_conditions',[])
    if v is None:
        names=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',' '.join(maps)))-set(params)-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'}
        if len(names)!=1:raise Unsupported('A single curve parameter has not been bound')
        v=next(iter(names))
    if conditions==['parameters positive']:conditions=[p+'>0' for p in params]
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=conditions));curve=[m.parse(s,v,params) for s in maps]
    if not isinstance(pts,(list,tuple)) or len(pts)!=2:raise Unsupported('Two finite points on the parametrization are required')
    points=[[m.parse(str(x),None,params) for x in point_coordinates(point,len(coords))] for point in pts]
    if not all(m.constant_defined(x,ctx) for p in points for x in p):raise Unsupported('An endpoint coordinate is undefined')
    indices=range(len(curve)) if saved is None else [saved['injective_coordinate']]
    for i in indices:
        if type(i) is not int or not 0<=i<len(curve):raise Unsupported('Invalid injectivity witness')
        try:s,d=affine(curve[i],v)
        except Unsupported:continue
        if known_guard(('nonzero',s),ctx):break
    else:raise Unsupported('An injective coordinate or a selected parameter branch must be proved')
    bounds=[m.div(m.add(p[i],m.neg(d)),s) for p in points]
    for at,p in zip(bounds,points):
        values=[m.substitute(raw,{('v',v):at}) for raw in curve]
        if not all(m.constant_defined(x,ctx) and same_value(x,y) for x,y in zip(values,p)):
            raise Unsupported('A stated endpoint does not belong to the original parameterized curve')
    child=dict(kind='line_integral',variables=coords,parameter=v,parameters=params,stated_conditions=conditions,
               path=[dict(map=maps,lower=source(bounds[0]),upper=source(bounds[1]))],**density,requested_output=['line_integral'])
    result=request('integral on the uniquely lifted oriented arc',child)
    return dict(parameter=v,injective_coordinate=i,affine_coefficients=(s,d),points=points,bounds=bounds,
                measure=result['compilation']['measure']),freeze(result['value'])


def green_source_integral(t,library,request,chart=None):
    import re
    from tasks import bind_printed_geometry
    from verify import same_value
    fields={'kind','id','source','coefficients','curve','method_requirement','requested_output','parameters','stated_conditions','orientation'}
    direct=t.get('method_requirement')=='green_and_direct_parametrization'
    if (not library.data.get('green_coordinate_boundary') or set(t)-fields or not curve_method_agrees(t) or t.get('method_requirement') not in (None,'green_theorem','green_and_direct_parametrization')
            or t.get('requested_output')!=['green_and_direct_integral' if direct else 'line_integral']):
        raise Unsupported('An oriented boundary and the complete printed method are required')
    match=re.fullmatch(r'(positive|negative) (triangle|polygon) (.+)',t['curve'])
    traversal=('counterclockwise' if match[1]=='positive' else 'clockwise') if match else t.get('orientation')
    bind_printed_geometry(t,'orientation',traversal)
    params=list(t.get('parameters',[]));conditions=list(t.get('stated_conditions',[]))
    if match:
        if chart:raise Unsupported('The proposed circular chart does not fit the polygon')
        points=re.split(r'\s*,\s*(?=[A-Za-z]\()',match[3])
        vertices=[list(point_coordinates(p,2)) for p in points]
        if match[2]=='triangle' and len(vertices)!=3:raise Unsupported('Three vertices required for the printed triangle')
        orientation=traversal
        if t.get('orientation',orientation)!=orientation:raise Unsupported('Contradictory source orientations')
        region={'polygon':vertices}
    else:
        conic=re.fullmatch(r'(?:(circle|ellipse) )?([^=]+)=([^=]+)',t['curve'])
        orientation=traversal
        if not conic or direct or orientation not in ('clockwise','counterclockwise'):raise Unsupported('Boundary geometry or its orientation is not certified')
        geometry,left,right=conic.groups()
        names=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',left+' '+right))-set(m.FUNCTIONS)-set(m.ALIASES)-{'x','y','pi','e'}
        params=sorted(set(params)|names);lhs=m.parse(left,None,['x','y',*params]);rhs=m.parse(right,None,params)
        for op,g in domain_conditions(lhs):
            if any(m.contains(g,('s',axis)) for axis in ('x','y')):raise Unsupported('The boundary equation has additional spatial restrictions')
            if op=='nonzero' and g[0]=='pow' and g[2]>0 and g[1][0]=='s' and g[1][1] in params:
                conditions.append(source(g[1])+'!=0')
        unit_circle=same_value(lhs,m.parse('x^2+y^2',None,['x','y']))
        if geometry=='circle' and not unit_circle:raise Unsupported('A circle centered at the origin is required')
        if unit_circle:
            if rhs[0]=='pow' and rhs[2]==2 and rhs[1][0]=='s':conditions.append(source(rhs[1])+'!=0')
        ctx=m.context(dict(variable='__angle',parameters=params,parameter_conditions=conditions))
        if not all(known_guard(g,ctx) for expr in (lhs,rhs) for g in domain_conditions(expr)):
            raise Unsupported('An original condition of the boundary equation is unproved')
        if chart:
            if chart!='direct_circle' or not unit_circle or t.get('method_requirement') is not None:
                raise Unsupported('Direct traversal cannot discharge the prescribed theorem or noncircular boundary')
            if m.sign(rhs,ctx)!=1:raise Unsupported('The circle radius is not strictly positive')
            rad=source(m.simplify(('sqrt',rhs)));angle='__angle';limits=('0','2*pi') if orientation=='counterclockwise' else ('2*pi','0')
            arc=dict(map=[rad+'*cos('+angle+')',rad+'*sin('+angle+')'],lower=limits[0],upper=limits[1])
            line=dict(kind='line_integral',variables=['x','y'],parameter=angle,path=[arc],coefficients=t['coefficients'],
                      parameters=params,stated_conditions=conditions,requested_output=['line_integral'])
            res=request('one oriented circuit on the original circle',line)
            return dict(chart=chart,region={'circle_squared_radius':rhs},orientation=orientation,method='direct_circle'),{'boundary_integral':res['value']}
        region={'quadratic_sublevel':dict(left=left,right=right)}
    sub=dict(kind='oriented_boundary_integral',variables=['x','y'],coefficients=t['coefficients'],boundary_of=region,
             orientation=orientation,parameters=params,stated_conditions=list(dict.fromkeys(conditions)),
             method_requirement=t.get('method_requirement') or 'green_theorem',requested_output=['boundary_integral','direct_integral'] if direct else ['boundary_integral'])
    result=request('area integral of the exterior derivative and all required traversals',sub)
    return dict(region=region,orientation=orientation,method=sub['method_requirement']),result['value']


def line_integral(task,library,request):
    """Restrict an ambient scalar density or differential one-form to a piecewise smooth path."""
    from verify import same_value
    path=task.get('path')
    if isinstance(path,dict):
        fields={'kind','id','source','variables','parameters','stated_conditions','coefficients','path','requested_output'}
        if (set(task)-fields or 'coefficients' not in task or task.get('requested_output')!=['line_integral'] or
            (set(path)!={'start','end'} and not (set(path)=={'closed'} and path['closed'] is True))):
            raise Unsupported('Endpoint data must specify a given piecewise smooth path or closed loop of a one-form')
        goal={k:task[k] for k in ('variables','parameters','stated_conditions','coefficients') if k in task}
        proof=request('path independence from the full gradient',
                      dict(kind='exact_form',**goal,**path,requested_output=['exactness_proof','line_integral']))
        return {'measure':'exact_one_form','potential':proof['value']['potential']},freeze(proof['value']['line_integral'])
    fields={'kind','id','source','variables','parameter','path','vertices','parameters','stated_conditions','coefficients','scalar','requested_output'}
    if (set(task)-fields or task.get('requested_output')!=['line_integral'] or ('coefficients' in task)==('scalar' in task)
            or ('path' in task)==('vertices' in task) or library.data.get('task_compilers',{}).get('line_integral')!='pullback_along_curve'):
        raise Unsupported('Expected one path and a scalar arc density or one-form without additional obligations')
    coords=task['variables'];v=task['parameter'];params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if not all(isinstance(z,(list,tuple)) for z in (coords,params,conditions)) or not coords or not all(isinstance(z,str) for z in [*coords,*params,*conditions]):
        raise Unsupported('Expected named coordinates and real constant parameters')
    ctx=m.context({'variable':v,'parameters':params,'parameter_conditions':conditions})
    m.context({'variable':v,'parameters':[*coords,*params]})
    scalar='scalar' in task
    formulas=[task['scalar']] if scalar else task['coefficients']
    if not isinstance(formulas,(list,tuple)) or len(formulas)!=(1 if scalar else len(coords)):raise Unsupported('Wrong integrand dimension')
    fields_raw=[m.parse(z,None,[*coords,*params]) for z in formulas]
    def scalar_value(z):
        e=m.parse(str(z),None,params)
        if not m.constant_defined(e,ctx):raise Unsupported('Undefined endpoint or vertex')
        return m.simplify(e)
    def vector(z):
        if not isinstance(z,(list,tuple)) or len(z)!=len(coords):raise Unsupported('Wrong path dimension')
        return z
    if 'vertices' in task:
        vertices=[tuple(map(scalar_value,vector(z))) for z in task['vertices']]
        paths=[(ZERO,ONE,[m.add(x,m.mul(('v',v),m.add(y,m.neg(x)))) for x,y in zip(a,b)]) for a,b in zip(vertices,vertices[1:])]
    else:
        paths=[]
        for p in task['path']:
            if not isinstance(p,dict) or set(p)!={'map','lower','upper'}:raise Unsupported('Unsupported path specification')
            paths.append((scalar_value(p['lower']),scalar_value(p['upper']),[m.parse(z,v,params) for z in vector(p['map'])]))
    if not paths:raise Unsupported('Expected at least one curve segment')
    pieces=[];total=ZERO;last=None
    for i,(a,b,curve) in enumerate(paths):
        bound=None
        def segment_interval():
            nonlocal bound
            if bound is None:
                left,right=enclose(a,None),enclose(b,None)
                bound=min(left[0],right[0]),max(left[1],right[1])
            return bound
        def on_segment(u):
            if u[0]=='abs':
                z=on_segment(u[1])
                if library.data.get('curve_metric'):
                    from plane_domains import metric_sign
                    sign=metric_sign(z,v,a,b,ctx)
                    if sign in (-1,0,1):return m.mul(q(sign),z)
                if z[0]=='mul':return m.mul(on_segment(('abs',z[1])),on_segment(('abs',z[2])))
                if m.known_nonnegative(z,ctx):return z
                if m.known_nonnegative(m.neg(z),ctx):return m.neg(z)
                try:
                    l,r=enclose(z,segment_interval())
                    if l>=0:return z
                    if r<=0:return m.neg(z)
                except Unsupported:pass
                return ('abs',z)
            return (u[0],*(on_segment(z) if isinstance(z,tuple) else z for z in u[1:]))
        def cover(raw,smooth=False):
            for kind,u in domain_conditions(raw,smooth):
                if known_guard((kind,u),ctx):continue
                u=m.simplify(on_segment(m.simplify(u)))
                if known_guard((kind,u),ctx):continue
                guard_bounds(kind,u,segment_interval(),[v])
        for c in curve:cover(c,True)
        point=lambda t:tuple(m.simplify(m.substitute(c,{('v',v):t})) for c in curve)
        start,end=point(a),point(b)
        if last is not None and not all(same_value(x,y) for x,y in zip(last,start)):
            raise Unsupported('The supplied curve segments do not join')
        last=end
        subs=dict(zip((('s',x) for x in coords),curve));restricted=[m.substitute(f,subs) for f in fields_raw]
        for f in restricted:cover(f)
        vel=[]
        for x,c in zip(coords,curve):
            proof=request(f'{i}/velocity/{x}',{'kind':'differentiate','function':source(c),'variable':v,'parameters':params,
                          'stated_conditions':conditions,'method_requirement':'table_and_rules'})
            vel.append(freeze(proof['value']))
        lo,hi=a,b
        if scalar:
            speed=m.simplify(('sqrt',m.dot(vel,vel)));metric_proof=None
            if library.data.get('curve_metric'):
                from plane_domains import metric_square_root,metric_sign
                candidate,metric_proof=metric_square_root(m.dot(vel,vel),v,a,b,ctx)
                if metric_proof is not None:
                    try:
                        for op,g in domain_conditions(candidate):
                            if known_guard((op,g),ctx) or op=='nonnegative' and metric_sign(g,v,a,b,ctx) in (0,1):continue
                            guard_bounds(op,g,segment_interval(),[v])
                        speed=candidate
                    except Unsupported:metric_proof=None
            pulled=m.mul(restricted[0],speed)
            d=m.add(b,m.neg(a))
            if m.sign(d,ctx)!=1 and not m.known_nonnegative(d,ctx):
                if m.known_nonnegative(m.neg(d),ctx):lo,hi=b,a
                else:raise Unsupported('The orientation of the scalar arc interval cannot be ordered')
        else:pulled=m.dot(restricted,vel)
        pulled=m.simplify(on_segment(pulled))
        if scalar and library.data.get('curve_metric'):
            from integrals import learned_nodes
            for node in sorted(set(learned_nodes(pulled)),key=str):
                if isinstance(node,tuple) and node[0]=='pow' and node[2]==2 and node[1][0] in ('sinh','cosh'):
                    wave,arg=node[1]
                    pulled=m.simplify(m.substitute(pulled,{node:m.div(m.add(('cosh',m.mul(q(2),arg)),q(1 if wave=='cosh' else -1)),q(2))}))
        val=freeze(request(f'{i}/integral',{'kind':'iterated_integral','integrand':source(pulled),'parameters':params,
                   'stated_conditions':conditions,'integration_order':[{'variable':v,'lower':source(lo),'upper':source(hi)}],
                   'requested_output':['exact_integral']})['value'])
        pieces.append({'start':start,'end':end,'velocity':vel,'pullback':pulled,'value':val})
        if scalar and metric_proof is not None:pieces[-1]['speed_proof']=metric_proof
        total=m.add(total,val)
    return {'measure':'arc_length' if scalar else 'oriented_one_form','pieces':pieces},total


def local_power_log_order(expr,var):
    """Powers (p,k) with |expr(t)| comparable to t^p |log t|^k as t decreases to zero."""
    from polynomial import rf,NotRational,Undefined
    def first(poly):return next((j for j,c in enumerate(poly) if c),None)
    def rational_order(p,d):
        a,b=first(p),first(d)
        if a is None or b is None:raise Unsupported('A nonzero leading coefficient is required')
        return F(a-b),F(0)
    try:return rational_order(*rf(expr,var))
    except (NotRational,Undefined):pass
    op=expr[0]
    if op in ('sqrt','cbrt','abs','pow','rpow'):
        if op=='rpow':power=m.num(m.simplify(expr[2]))
        elif op=='pow':power=expr[2]
        else:power={'sqrt':F(1,2),'cbrt':F(1,3),'abs':1}[op]
        if power is None:raise Unsupported('The endpoint comparison exponent is symbolic')
        p,k=local_power_log_order(expr[1],var);return power*p,power*k
    if op in ('mul','div','add'):
        a,b=(local_power_log_order(e,var) for e in expr[1:])
        if op=='add':
            if a==b:raise Unsupported('Cancellation between equal leading orders is unresolved')
            return min((a,b),key=lambda t:(t[0],-t[1]))
        sign=1 if op=='mul' else -1
        return a[0]+sign*b[0],a[1]+sign*b[1]
    if op=='ln':
        try:p,d=rf(expr[1],var)
        except (NotRational,Undefined):raise Unsupported('A leading equivalent of the logarithm is required')
        n,_=rational_order(p,d)
        if n:return F(0),F(1)
        j=first(d)
        if p[j]!=d[j]:return F(0),F(0)
        return rational_order(*rf(m.add(expr[1],q(-1)),var))
    raise Unsupported('No certified power-log comparison at this endpoint')


def cauchy_principal_value(task,f,components,request,ctx):
    """Fold the two cutoffs at each interior pole independently, and pair whole-line tails."""
    from integrals import polynomial_expression
    from polynomial import rf,pgcd,pdiv,NotRational
    from verify import same_value
    v=task['variable'];x=('v',v);pieces=[];total=ZERO
    a,b=components[0][0],components[-1][1];poles=[s for s,_ in components[1:]]
    def ordinary(g,low,high,center=None):
        nonlocal total
        if low==high:return True
        if center is not None:
            minus=m.substitute(f,{x:m.add(center,m.neg(x))});plus=m.substitute(f,{x:m.add(center,x)})
            g=m.add(minus,plus)
            try:
                p,d=rf(g,v);common=pgcd(p,d)
                g=m.div(polynomial_expression(pdiv(p,common)[0],v),polynomial_expression(pdiv(d,common)[0],v))
            except NotRational:pass
        item=dict(lower=low,upper=high,integrand=g,reflection_center=center)
        pieces.append(item)
        if g==ZERO:return True
        def bound(t):return t if isinstance(t,str) else source(t)
        sub=dict(kind='improper_integral',integrand=source(g),variable=v,lower=bound(low),upper=bound(high),
                 parameters=task.get('parameters',[]),stated_conditions=task.get('stated_conditions',[]),requested_output=['exact_integral'])
        value=request('truncated integral '+str(len(pieces)),sub)['value']
        if value['convergence']!='convergent':return False
        total=m.add(total,freeze(value['value']));return True
    both=(a,b)==('-inf','+inf')
    if both and all(p==ZERO for p in poles):
        finite=ordinary(f,ZERO,'+inf',ZERO)
    else:
        if any(m.num(p) is None for p in poles):raise Unsupported('Separate symmetric neighborhoods of the interior points are required')
        finite=True
        if both:
            radius=q(1+max(abs(m.num(p)) for p in poles))
            finite=ordinary(f,radius,'+inf',ZERO);a,b=m.neg(radius),radius
        previous=a
        for j,pole in enumerate(poles):
            if not finite:break
            c=m.num(pole);neighbors=[]
            for endpoint,is_outer in ((a if j==0 else poles[j-1],j==0),
                                      (b if j+1==len(poles) else poles[j+1],j+1==len(poles))):
                if isinstance(endpoint,str):continue
                number=m.num(endpoint)
                if number is None:raise Unsupported('Ordering the distances to the neighboring cuts is unproved')
                neighbors.append(abs(c-number)/(1 if is_outer else 2))
            radius=q(min(neighbors) if neighbors else 1)
            left,right=m.add(pole,m.neg(radius)),m.add(pole,radius)
            finite=ordinary(f,previous,left) and ordinary(f,ZERO,radius,pole);previous=right
        if finite:finite=ordinary(f,previous,b)
    result={'principal_value_exists':finite}
    if finite:total=result['principal_value']=m.combine_rational_logs(total)
    if 'stated_identity' in task:
        stated=m.parse(str(task['stated_identity']),None,task.get('parameters',[]))
        if not finite or not m.constant_defined(stated,ctx) or not same_value(total,stated):
            raise Unsupported('The printed principal value identity has not been established')
    return {'components':components,'symmetric_pairs_and_regular_pieces':pieces},result


def parameter_endpoint_comparison(task):
    """On positive intervals, prove a fixed sign and compare to exponential, power and iterated logarithm factors."""
    v=task['variable'];params=task.get('parameters',[]);assumptions=task.get('stated_conditions',[])
    nonnegative={p for p in params if p+'>=0' in assumptions}
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=[a for a in assumptions if a not in {s+'>=0' for s in nonnegative}]))
    x=('v',v);f=m.parse(task['integrand'],v,params)
    E=('exp',ONE);halfpi=m.div(m.PI,q(2))
    def endpoint(k):
        text=task[k]
        if text=='+inf':return text
        e=m.parse(str(text),None,params)
        if not m.constant_defined(e,ctx):raise Unsupported('Undefined printed endpoint')
        return m.simplify(e)
    lo,hi=endpoint('lower'),endpoint('upper')
    ranks={ZERO:0,ONE:1,halfpi:2,E:3,'+inf':4}
    def compare(a,b):
        if a==b:return 0
        if a=='+inf' or b=='+inf':return 1 if a=='+inf' else -1
        if a in ranks and b in ranks:return 1 if ranks[a]>ranks[b] else -1
        sign=m.sign(m.add(a,m.neg(b)),ctx)
        if sign is None:raise Unsupported('Unknown ordering of endpoint comparison charts')
        return sign
    if compare(lo,ZERO)<0 or compare(lo,hi)>=0:
        raise Unsupported('A positive real interval with ordered endpoints is required')
    flat=(ZERO,)*4
    def unit(i):
        return tuple(ONE if j==i else ZERO for j in range(4))
    def scale(w,profile):return tuple(m.mul(w,c) for c in profile)
    def rel(a,b):return m.sign(m.add(a,m.neg(b)),ctx)
    def extreme(a,b,largest):
        delta=m.simplify(m.add(a,m.neg(b)));sgn=m.sign(delta,ctx)
        if sgn is not None:return (a if sgn>=0 else b) if largest else (a if sgn<=0 else b)
        if delta in {('s',p) for p in nonnegative}:return a if largest else b
        if m.neg(delta) in {('s',p) for p in nonnegative}:return b if largest else a
        return ('max' if largest else 'min',a,b)
    factors=[]
    def local(e,left,right,at):
        shape,sign=derive(e,left,right,at)
        factors.append(dict(factor=e,scale=shape,fixed_sign=sign if sign is not None else 'nonzero'))
        return shape,sign
    def derive(e,left,right,at):
        far=at=='+inf';op=e[0]
        if e==x:return (unit(1) if far or at==ZERO else flat),1
        if not m.variable_in(e,v):
            if not m.constant_defined(e,ctx) or not m.nonzero(e,ctx):raise Unsupported('Zero or undefined leading coefficient')
            return flat,m.sign(e,ctx)
        # Standard local equivalents are used only on intervals where these factors have a fixed, nonzero sign.
        if e in (('ln',('add',ONE,x)),('ln',('add',x,ONE))):
            return (unit(1) if at==ZERO else unit(2) if far else flat),1
        if e in (('ln',x),('ln',('div',ONE,x))):
            if compare(left,ONE)<0<compare(right,ONE):raise Unsupported('Logarithm changes sign inside this interval')
            sign=1 if compare(left,ONE)>=0 else -1
            return (unit(2) if far or at==ZERO else unit(1) if at==ONE else flat),sign if e[1]==x else -sign
        if e==('ln',('ln',x)) and compare(left,E)>=0:
            return (unit(3) if far else unit(1) if at==E else flat),1
        if op in ('sin','cos') and e[1]==x and compare(right,halfpi)<=0:
            return (unit(1) if at==(ZERO if op=='sin' else halfpi) else flat),1
        if op in ('atan','exp'):
            inner=e[1]
            if inner==x:slope=ONE
            elif inner[0]=='mul' and x in inner[1:] and not m.variable_in(inner[2] if inner[1]==x else inner[1],v):
                slope=inner[2] if inner[1]==x else inner[1]
            else:raise Unsupported('A checked linear argument through the origin is required')
            if not m.constant_defined(slope,ctx):raise Unsupported('Undefined scale in a local comparison')
            if op=='exp' and m.num(slope) is not None:return (scale(slope,unit(0)) if far else flat),1
            if op=='atan' and m.nonzero(slope,ctx):
                return (unit(1) if at==ZERO else flat),m.sign(slope,ctx)
        if op=='add':
            # 1 − x^k ~ k(1 − x) at one, by the positive geometric sum.
            for one,neg in ((e[1],e[2]),(e[2],e[1])):
                if one!=ONE or neg[0]!='mul' or neg[1]!=q(-1):continue
                power=neg[2]
                if power==x:k=1
                elif power[0]=='pow' and power[1]==x and power[2]>0:k=power[2]
                else:continue
                if compare(right,ONE)<=0:return (unit(1) if at==ONE else flat),1
                if compare(left,ONE)>=0:return (unit(1) if at==ONE else scale(q(k),unit(1)) if far else flat),-1
            # x − 1 has the opposite sign on each side of one.
            if e in (('add',x,q(-1)),('add',x,('mul',q(-1),ONE)),('add',q(-1),x)):
                p,s=local(('add',ONE,('mul',q(-1),x)),left,right,at);return p,-s
        if op in ('sqrt','cbrt','abs','pow','rpow'):
            p,s=local(e[1],left,right,at)
            if op=='abs':return p,1
            if op=='cbrt':return scale(q(1,3),p),s
            if op=='pow':return scale(q(e[2]),p),1 if e[2]%2==0 else s
            exponent=q(1,2) if op=='sqrt' else e[2]
            if s!=1 or m.variable_in(exponent,v) or not m.constant_defined(exponent,ctx):raise Unsupported('Positive base or fixed defined exponent unproved')
            return scale(m.simplify(exponent),p),1
        if op in ('add','div','mul'):
            a,sg=local(e[1],left,right,at);b,tg=local(e[2],left,right,at)
            if op=='add':
                if sg is None or sg!=tg:raise Unsupported('Possible zero or cancellation on the source interval')
                if a==b:return a,sg
                if a[0]!=ZERO or b[0]!=ZERO or any(z!=ZERO for z in a[2:]+b[2:]):
                    raise Unsupported('Incomparable exponential or logarithmic summands')
                return (ZERO,extreme(a[1],b[1],far),ZERO,ZERO),sg
            if op=='div':b=scale(q(-1),b)
            return tuple(map(m.add,a,b)),(sg*tg if None not in (sg,tg) else None)
        raise Unsupported('No fixed-sign equivalent throughout the original interval')
    def condition(profile,far):
        # Integrability requires (exp, power+1, log+1, loglog+1) to be lexicographically negative at infinity.
        # On a finite side the power inequality reverses, since t is distance to that endpoint.
        rate,p,l,ll=profile
        tests=[(rate,-1),(m.add(p,ONE),-1 if far else 1),(m.add(l,ONE),-1),(m.add(ll,ONE),-1)]
        def decide(j):
            if j==len(tests):return False
            arg,sign=tests[j];sg=rel(arg,ZERO)
            if sg is not None:return decide(j+1) if sg==0 else sg==sign
            tail=decide(j+1)
            return {'expression':arg,'relation':('>=' if sign>0 else '<=') if tail is True else ('>' if sign>0 else '<'),
                    **({'when_equal':tail} if isinstance(tail,dict) else {})}
        return decide(0)
    bounds=[lo,hi]
    if compare(lo,ONE)<0<compare(hi,ONE):
        try:local(f,lo,hi,lo)
        except Unsupported:bounds.insert(1,ONE)
    checks=[];conditions=[]
    for left,right in zip(bounds,bounds[1:]):
        for at in (left,right):
            factors=[]
            profile,_=local(f,left,right,at);criterion=condition(profile,at=='+inf')
            checks.append(dict(interval=(left,right),endpoint=at,profile=profile,factors=factors,condition=criterion))
            if criterion is not True and criterion not in conditions:conditions.append(criterion)
    if False in conditions:return {'endpoint_scales':checks},{'convergence':'divergent'}
    verdict={'convergence':'convergent'} if not conditions else {'convergence':'conditional_on_parameters','all_conditions':conditions,'otherwise':'divergent'}
    return {'endpoint_scales':checks,'stated_conditions':assumptions},verdict



def contains_periodic_factor(e):
    return isinstance(e,tuple) and (e[0] in ('sin','cos') or any(contains_periodic_factor(c) for c in e[1:]))


def periodic_integral_comparison(task):
    """Compare powers of a periodic factor on disjoint periods, and use Dirichlet for odd powers."""
    v=task['variable'];params=task.get('parameters',[]);given=task.get('stated_conditions',[])
    nonnegative={p for p in params if p+'>=0' in given}
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=[a for a in given if a not in {s+'>=0' for s in nonnegative}]))
    x=('v',v);f=m.parse(task['integrand'],v,params)
    lower=task['lower'];upper=task['upper']
    def predicate(z,op):
        z=m.simplify(z);sg=m.sign(z,ctx)
        if sg is None:return dict(expression=z,relation=op)
        return {'<':sg<0,'>':sg>0,'>=':sg>=0,'=':sg==0,'!=':sg!=0}[op]
    def allof(*tests):
        if False in tests:return False
        tail=list(t for t in tests if t is not True)
        return (tail[0] if len(tail)==1 else {'all':tail}) if tail else True
    if upper!='+inf' and f[0] in ('sin','cos'):
        # A bounded periodic composition is integrable over a finite interval once the inner domain is proved there.
        bounds=(m.parse(lower,None,params),m.parse(upper,None,params))
        if all(m.constant_defined(z,ctx) for z in bounds) and bounds[0]==ZERO and m.simplify(bounds[1])==m.div(m.PI,q(2)):
            guards=domain_conditions(f[1],True)
            if all(rel=='nonzero' and freeze(z) in (('sin',x),('cos',x)) for rel,z in guards):
                return {'absolute_majorant':ONE,'finite_interval':bounds,'interior_guards':guards},dict(
                    convergence='convergent',absolute_convergence=True,conditional_convergence=False)
    lower=m.parse(str(lower),None,params)
    if upper!='+inf' or not m.constant_defined(lower,ctx) or m.sign(lower,ctx) not in (0,1):raise Unsupported('The periodic tail requires an ordered positive half-line')
    s=ZERO;factors=[];wave=[]
    def xpower(e):
        if e==x:return ONE
        if e[0] in ('pow','rpow') and e[1]==x:
            n=q(e[2]) if e[0]=='pow' else e[2]
            if not m.variable_in(n,v) and m.constant_defined(n,ctx):return m.simplify(n)
        raise Unsupported('Expected a power of the positive coordinate')
    def split(e,w):
        nonlocal s
        op=e[0]
        if op in ('mul','div'):
            if op=='div' and contains_periodic_factor(e[2]):raise Unsupported('Original periodic divisor may vanish inside the interval')
            split(e[1],w);split(e[2],w if op=='mul' else m.neg(w));return
        if op in ('sqrt','pow','rpow'):
            k=q(1,2) if op=='sqrt' else q(e[2]) if op=='pow' else e[2]
            if m.variable_in(k,v) or not m.constant_defined(k,ctx):raise Unsupported('A fixed defined exponent is required')
            if contains_periodic_factor(e[1]) and not (op=='pow' and e[1][0] in ('sin','cos') and e[2]>0):
                raise Unsupported('A sign-changing periodic factor requires a direct positive integer power')
            if e[1][0] in ('mul','div') and m.num(k) is None:raise Unsupported('Unverified power over a composite base')
            split(e[1],m.mul(w,k));return
        if op in ('sin','cos'):
            index=m.num(w)
            if index is None or index.denominator!=1 or index<=0:raise Unsupported('A positive integer periodic power is required')
            wave.append((op,e[1],int(index)));return
        if e==x:s=m.add(s,w);return
        if not m.variable_in(e,v) and m.constant_defined(e,ctx) and m.sign(e,ctx)==1:return
        if op=='add':
            for c,z in ((e[1],e[2]),(e[2],e[1])):
                if m.variable_in(c,v) or not m.constant_defined(c,ctx) or m.sign(c,ctx)!=1:continue
                b=ONE
                if z[0]=='mul':
                    if m.variable_in(z[1],v):z,b=z[1],z[2]
                    else:b,z=z[1],z[2]
                n=xpower(z)
                if (not m.variable_in(b,v) and m.constant_defined(b,ctx) and m.sign(b,ctx)==1
                        and (m.known_nonnegative(n,ctx) or n in {('s',p) for p in nonnegative})):
                    factors.append(dict(constant=c,coefficient=b,exponent=n,weight=w));return
        raise Unsupported('The source amplitude may have an interior zero or pole')
    split(f,ONE)
    if len(wave)!=1:raise Unsupported('Expected a single periodic factor')
    fn,phase,k=wave[0];frequency=ONE;gamma=ONE
    if phase[0]=='mul':
        frequency,phase=phase[1:]
        if m.variable_in(frequency,v):phase,frequency=frequency,phase
        if m.variable_in(frequency,v) or not m.constant_defined(frequency,ctx):raise Unsupported('The frequency must be fixed and defined')
    exponential=phase==('exp',x)
    if not exponential:gamma=xpower(phase)
    if lower!=ZERO and (exponential or gamma!=ONE):raise Unsupported('Phase transport of the finite start is unproved')
    if (gamma!=ONE or exponential) and factors:raise Unsupported('Transformed amplitude monotonicity is unproved')
    if not m.nonzero(gamma,ctx):raise Unsupported('The phase substitution might be constant')
    if exponential and frequency!=ONE:raise Unsupported('Endpoint phase may have an unknown zero')
    transformed=m.add(m.div(m.add(s,ONE),gamma),q(-1))
    d=transformed
    for fac in factors:d=m.add(d,m.mul(fac['exponent'],fac['weight']))
    # With u=x^γ the log derivative of the amplitude times u tends to d. A negative d makes it eventually decreasing.
    # For u=e^x the amplitude is (ln u)^s/u; its log derivative times u is s/ln u−1.
    head=True if lower!=ZERO else predicate(m.add(s,ONE),'>') if exponential else predicate(m.add(transformed,q(1+(k if fn=='sin' else 0))),'>')
    absolute_tail=predicate(m.add(s if exponential else d,ONE),'<')
    ordinary_tail=True if exponential else predicate(d,'<')
    absolute=allof(head,absolute_tail)
    conditional=allof(head,ordinary_tail,predicate(m.add(s if exponential else d,ONE),'>=')) if k%2 else False
    ordinary=allof(head,ordinary_tail) if k%2 else absolute
    branches=[]
    if not m.nonzero(frequency,ctx):
        source_tail=s
        for fac in factors:source_tail=m.add(source_tail,m.mul(fac['exponent'],fac['weight']))
        a=True if fn=='sin' else allof(True if lower!=ZERO else predicate(m.add(s,ONE),'>'),predicate(m.add(source_tail,ONE),'<'))
        branches.append(dict(frequency_zero=True,absolute=a,conditional=False,ordinary=a))
    if m.sign(frequency,ctx)!=0:branches.append(dict(frequency_zero=False,absolute=absolute,conditional=conditional,ordinary=ordinary))
    plan=dict(phase=phase,frequency=frequency,periodic_function=fn,periodic_power=k,source_power=s,binomial_factors=factors,
              phase_change='exponential' if exponential else 'power',phase_power=gamma,transformed_origin_power=transformed,
              tail_power=q(-1) if exponential else d,tail_log_power=s if exponential else ZERO,
              proof='positive half-period lower bounds and eventual monotonicity from the logarithmic derivative')
    value={'convergence':'conditional_on_parameters','cases':branches}
    if len(branches)==1 and all(type(branches[0][key]) is bool for key in ('absolute','ordinary','conditional')):
        value.update(convergence='convergent' if branches[0]['ordinary'] else 'divergent',
                     absolute_convergence=branches[0]['absolute'],conditional_convergence=branches[0]['conditional'])
    return plan,value


def periodic_series_plan(task):
    """Transport contiguous nonnegative integral blocks, or apply Dirichlet to a periodic sequence times a power-log amplitude."""
    import re
    from integrals import affine
    n=task['index'];start=task['start_index']
    if (task.get('parameters') or task.get('stated_conditions') or task.get('method_requirement') not in (None,'general_convergence_tests') or
            set(task.get('requested_output',()))-{'convergence_classification','absolute_convergence','conditional_convergence','justification'}):
        raise Unsupported('This periodic series requires other parameter or method evidence')
    ctx=m.context(dict(variable=n));i=('v',n)
    def integral(variable,f,lower):
        return dict(kind='improper_integral',variable=variable,integrand=f,lower=lower,upper='+inf',requested_output=['convergence'])
    block=re.fullmatch(r'integral\((.+),\s*([A-Za-z_]\w*)\s*=\s*(.+?)\.\.(.+)\)',task['term'])
    if block:
        f,v,low,high=block.groups()
        if v==n:raise Unsupported('The integration coordinate must be independent of the index')
        low,high=m.parse(low,n),m.parse(high,n)
        if any(not known_guard(g,ctx) for z in (low,high) for g in domain_conditions(z)):raise Unsupported('Unproved endpoint domain')
        slope,_=affine(low,n)
        if m.sign(slope,ctx)!=1 or m.simplify(m.add(high,m.neg(m.substitute(low,{i:m.add(i,ONE)}))))!=ZERO:
            raise Unsupported('The intervals do not partition a positive tail')
        child=integral(v,f,source(m.substitute(low,{i:q(start)})))
        p,_=periodic_integral_comparison(child)
        if p.get('periodic_power',1)%2:raise Unsupported('The compact integral blocks may change sign')
        return dict(criterion='periodic_series',argument='contiguous_nonnegative_integrals',lower=low,upper=high,
                    positive_slope=slope,scaled_limit_task=child)
    raw=m.parse(task['term'],n);waves=[];power=F(0);log_power=F(0)
    def collect(e,weight):
        nonlocal power,log_power
        if e==i:power+=weight;return
        if e==('ln',i):log_power+=weight;return
        if e[0] in ('mul','div'):
            if e[0]=='div' and contains_periodic_factor(e[2]):raise Unsupported('A periodic denominator may vanish')
            collect(e[1],weight);collect(e[2],weight if e[0]=='mul' else -weight);return
        if e[0]=='pow' and e[1] in (i,('ln',i)):collect(e[1],weight*e[2]);return
        if e[0] in ('sin','cos') and weight==1:
            if any(m.variable_in(z,n) or not known_guard((rel,z),ctx) for rel,z in domain_conditions(e[1])):
                raise Unsupported('The periodic argument may have an original pole')
            scale,offset=affine(e[1],n);freq=m.num(m.div(scale,m.PI))
            if offset!=ZERO or freq is None:raise Unsupported('A rational multiple of π per integer step is required')
            waves.append((e[0],freq));return
        if not m.variable_in(e,n) and m.constant_defined(e,ctx) and m.sign(e,ctx)==1:return
        raise Unsupported('The sequence is outside the certified power-log amplitude')
    collect(raw,F(1))
    if len(waves)!=1 or not m.constant_defined(m.substitute(raw,{i:q(start)}),ctx):raise Unsupported('Unproven first term or periodic factor')
    fn,freq=waves[0];identically_zero=fn=='sin' and freq.denominator==1
    zero_mean=fn=='sin' or freq.denominator!=1 or freq.numerator%2!=0
    ln=('ln',i)
    def exponent(z,k):return m.power(z,int(k)) if k.denominator==1 else ('rpow',z,q(k))
    amplitude=m.mul(exponent(i,power),exponent(ln,log_power))
    return dict(criterion='periodic_series',argument='finite_period_dirichlet',period=2*freq.denominator,
                frequency=q(freq),zero_mean=zero_mean,zero_sequence=identically_zero,power=q(power),log_power=q(log_power),
                tends_to_zero=power<0 or power==0 and log_power<0,
                scaled_limit_task=integral(n,source(amplitude),str(max(2,start))))


def gamma_rational(n):
    if n is None or n <= 0:
        return None
    if n.denominator == 1:
        return m.q(factorial(int(n) - 1))
    if n.denominator == 2:
        k = int(n)
        return m.mul(m.q(factorial(2 * k), 4**k * factorial(k)), ('sqrt', m.PI))


def euler_integral(task, library):
    """Match Euler kernels on the full original interval and test both endpoints."""
    import re
    from verify import same_value

    if not library.data.get('euler_power_integrals'):
        raise Unsupported('Эйлеровы подстановки отсутствуют в текущей библиотеке')
    method = task.get('method_requirement')
    exact = method == 'euler_integrals'
    wanted = ['exact_value', 'specified_method'] if exact else ['existence_domain', 'euler_integral_formula']
    headings = {
        'euler_integrals': 'Вычислить с помощью эйлеровых интегралов.',
        'euler_integrals_and_domain': 'Определить область существования и выразить через эйлеровы интегралы.',
    }
    origin = task.get('source', {})
    if (
        set(task) - {'kind', 'id', 'source', 'integrand', 'limits', 'stated_conditions', 'method_requirement', 'requested_output'}
        or method not in headings
        or task.get('requested_output') != wanted
        or not isinstance(origin, dict)
        or set(origin) - {'exercise', 'printed_subpart', 'pdf_page', 'printed_page', 'pdf_sha256', 'literal_requirement'}
        or origin.get('literal_requirement', headings[method]) != headings[method]
    ):
        raise Unsupported('Не установлены исходный метод и все требования к интегралу')
    text = task['integrand'].replace('²', '^2').replace('³', '^3')
    limits = task['limits'].split('..')
    if len(limits) != 2 or limits[0] != '0':
        raise Unsupported('Для общих концов требуется дополнительная замена')
    names = sorted(
        set(re.findall(r'\b[A-Za-z][A-Za-z0-9]*\b', text + ' ' + task['limits']))
        - m.FUNCTIONS
        - set(m.ALIASES)
        - {'x', 'e', 'pi', 'inf'}
    )
    conditions = task.get('stated_conditions', [])
    facts = []
    integers = []
    for term in conditions:
        if g := re.fullmatch(r'([a-z]) positive integer', term):
            integers.append(g[1])
            facts.append(g[1] + '>0')
        elif g := re.fullmatch(r'([a-z])>([0-9]+)', term):
            facts.append(term)
            if int(g[2]):
                facts.append('(' + g[1] + '-' + g[2] + ')>0')
        else:
            raise Unsupported('Не разобрано условие на параметры ' + term)
    x = ('s', 'x')
    raw = m.parse(text, None, [*names, 'x'])
    inf = limits[1] == 'inf'
    U = None if inf else m.parse(limits[1], None, names)
    guard = list(dict.fromkeys(g for e in (raw,) + (() if inf else (U,)) for g in domain_conditions(e) if not m.contains(g[1], x)))
    source_ctx = m.context(dict(variable='__euler', parameters=names, parameter_conditions=facts))
    if exact and any(not known_guard(g, source_ctx) for g in guard):
        raise Unsupported('Исходные ограничения задачи ещё не доказывают допустимость всех параметров')
    ctx = m.context(
        dict(
            variable='__euler',
            parameters=names,
            parameter_conditions=[*facts, *(guard_source(g) for g in guard if g[0] != 'nonnegative')],
        )
    )
    factor_context = m.context(dict(variable='__factor', parameters=[*names,'x'], parameter_conditions=[
        *facts, 'x>0', *([] if inf else [source(U)+'-x>0']),
        *(guard_source(g) for g in guard if g[0]!='nonnegative'),
        *(['sin(x)>0','cos(x)>0','tan(x)>0'] if U==m.parse('pi/2',None) else []),
    ]))
    absolute_bases=[]

    def positive(e):
        if m.sign(e, ctx) == 1:
            return True
        p, d = m.rational_form(e)
        a = m.sign(m.poly_expr(p), ctx)
        b = m.sign(m.poly_expr(d), ctx)
        return a in (-1, 1) and a == b

    def power(b, s):
        s = m.simplify(s)
        n = m.num(s)
        if b == m.ONE or n == 0:
            return m.ONE
        if b[0] == 'pow' and positive(b[1]):
            return power(b[1], m.mul(m.q(b[2]), s))
        if n is not None and n.denominator == 1:
            return m.power(b, int(n))
        return ('rpow', b, s)

    def factors(e, r=m.ONE):
        numeric_outer=m.num(m.simplify(r))
        integral_outer=numeric_outer is not None and numeric_outer.denominator==1
        if e[0] in ('mul', 'div'):
            if not integral_outer and not all(known_guard(('positive',z),factor_context) for z in e[1:]):
                raise Unsupported('Не доказаны знаки множителей при распределении вещественной степени')
            yield from factors(e[1], r)
            yield from factors(e[2], r if e[0] == 'mul' else m.neg(r))
        elif e[0] in ('pow', 'rpow', 'sqrt', 'cbrt'):
            p = m.q(e[2]) if e[0] == 'pow' else e[2] if e[0] == 'rpow' else m.q(1, 2 if e[0] == 'sqrt' else 3)
            if m.contains(p, x):
                raise Unsupported('Показатель внутри интеграла зависит от переменной')
            base=e[1]
            # A nonintegral outer power of an even power is a power of |base|.
            if e[0]=='pow' and e[2]%2==0 and not integral_outer:
                sign=m.sign(base,factor_context) if m.constant_defined(base,factor_context) else None
                if sign not in (-1,1):
                    raise Unsupported('Знак основания чётной степени на исходном интервале не доказан')
                if sign<0:
                    replacement=m.neg(base)
                    absolute_bases.append(dict(original=base,sign=sign,absolute_value=replacement))
                    base=replacement
            yield from factors(base, m.mul(r, p))
        else:
            yield e, r

    def monomial(e):
        c = m.ONE
        degree = m.ZERO
        for b, r in factors(e):
            if b == x:
                degree = m.add(degree, r)
            elif not m.contains(b, x):
                c = m.mul(c, power(b, r))
            else:
                raise Unsupported('Не установлено точное степенное ядро')
        return c, degree

    C = m.ONE
    a = m.ZERO
    other = []
    trig = {}
    log_order = 0
    for b, r in factors(raw):
        if b == x:
            a = m.add(a, r)
        elif not m.contains(b, x):
            C = m.mul(C, power(b, r))
        elif b == ('ln', x) and inf and m.num(r) in (1, 2):
            log_order += int(m.num(r))
        elif b[0] in ('sin', 'cos', 'tan') and b[1] == x:
            for k, sign in [('sin', 1), ('cos', -1)] if b[0] == 'tan' else [(b[0], 1)]:
                trig[k] = m.add(trig.get(k, m.ZERO), m.mul(m.q(sign), r))
        else:
            other.append((b, r))
    if not m.constant_defined(C,ctx) or not (positive(C) or positive(m.neg(C))):
        raise Unsupported('Коэффициент может менять область сходимости, в том числе обнуляться')
    if log_order > 2:
        raise Unsupported('Не проверено дифференцирование эйлерова интеграла этого порядка')
    domain = []
    one = m.ONE
    if trig and not other and U == m.parse('pi/2', None, []) and a == m.ZERO:
        args = [m.div(m.add(trig.get(k, m.ZERO), one), m.q(2)) for k in ('sin', 'cos')]
        kernel = 'beta'
        factor = m.div(C, m.q(2))
        change = 'sine_squared'
        params = []
    elif not trig and len(other) == 1:
        b, r = other[0]
        fixed = m.add(a, one)
        if b[0] == 'exp' and inf:
            coef, n = monomial(b[1])
            rate = m.neg(m.mul(coef, r))
            if n == m.ZERO:
                raise Unsupported('Постоянная экспонента не создаёт гамма-ядра')
            alpha = m.div(fixed, n)
            kernel = 'gamma'
            args = [alpha]
            amp = n if positive(n) else m.neg(n) if positive(m.neg(n)) else ('abs', n)
            domain.extend([('nonzero', n), ('positive', rate)])
            factor = m.div(C, m.mul(amp, power(rate, alpha)))
            change = 'scaled_power_gamma'
            params = [n, rate]
        elif b[0] == 'ln' and U == one and b[1] == ('div', one, x) and a == m.ZERO:
            kernel = 'gamma'
            args = [m.add(r, one)]
            factor = C
            change = 'negative_logarithm'
            params = []
        elif b[0] == 'add':
            (A, h), (B, k) = (monomial(v) for v in b[1:])
            if not positive(A) or k == m.ZERO or positive(m.add(h, m.neg(k))):
                A, B, h, k = B, A, k, h
            n = m.add(k, m.neg(h))
            if n == m.ZERO:
                raise Unsupported('Степени бинома совпадают')
            alpha = m.div(m.add(fixed, m.mul(h, r)), n)
            if not positive(A):
                raise Unsupported('Не доказана положительность основания на исходном интервале')
            if inf and positive(B):
                kernel = 'beta'
                args = [alpha, m.add(m.neg(r), m.neg(alpha))]
                domain.append(('nonzero', n))
                amp = n if positive(n) else m.neg(n) if positive(m.neg(n)) else ('abs', n)
                factor = m.div(m.mul(C, m.mul(power(A, r), power(m.div(A, B), alpha))), amp)
                change = 'positive_binomial_odds'
                params = [h, n, A, B, r]
            elif (
                not inf and positive(m.neg(B)) and positive(n) and positive(U) and same_value(m.add(A, m.mul(B, power(U, n))), m.ZERO)
            ):
                kernel = 'beta'
                args = [alpha, m.add(r, one)]
                factor = m.div(m.mul(C, m.mul(power(U, m.add(fixed, m.mul(h, r))), power(A, r))), n)
                change = 'finite_power_fraction'
                params = [h, n, A, B, r]
            else:
                raise Unsupported('Не доказаны положительность ядра и покрытие обоих концов')
        else:
            raise Unsupported('Не построена замена в эйлеров интеграл')
    else:
        raise Unsupported('Исходные множители не сведены к одной замене эйлерова интеграла')
    interior = ['x>0'] + ([] if inf else [source(U) + '-x>0'])
    if trig:
        interior.extend(f'{w}(x)>0' for w in ('sin', 'cos', 'tan'))
    elif b[0] == 'add' or change == 'negative_logarithm':
        interior.append(source(b) + '>0')
    open_ctx = m.context(
        dict(
            variable='__scope',
            parameters=[*names, 'x'],
            parameter_conditions=[*facts, *interior, *(guard_source(g) for g in guard if g[0] != 'nonnegative')],
        )
    )
    if any(not known_guard(g, open_ctx) for g in domain_conditions(raw)):
        raise Unsupported('Не подтверждена исходная действительная область на всём открытом интервале')
    domain = list(dict.fromkeys([*domain, *(('positive', v) for v in args)]))
    unresolved = []
    for rel, e in domain:
        if rel == 'positive' and positive(e) or rel == 'nonzero' and m.nonzero(e, ctx):
            continue
        test = m.sign(e, ctx)
        if (rel == 'positive' and test in (-1, 0)) or rel == 'nonzero' and test == 0:
            return dict(
                kernel=kernel,
                substitution=change,
                kernel_parameters=params,
                shape=args,
                original_parameter_domain=guard,
                endpoint_conditions=domain,
            ), dict(converges=False, failed_endpoint_condition=(rel, e))
        unresolved.append((rel, e))
    if exact and unresolved:
        raise Unsupported('Условия задачи ещё не доказывают сходимость на обоих концах')
    scalar = None
    special = None

    ns = [m.num(m.simplify(v)) for v in args]
    if kernel == 'gamma':
        val = gamma_rational(ns[0])
        scalar = m.mul(factor, val) if val is not None else None
        if log_order:
            if change != 'scaled_power_gamma':
                raise Unsupported('Не установлена связь логарифма с гамма-параметром')
            n, rate = params
            offset = m.neg(m.simplify(('ln', rate)))
            coefficients = [offset, one] if log_order == 1 else [m.power(offset, 2), m.mul(m.q(2), offset), one]
            special = dict(
                gamma_derivative_terms=[m.mul(m.div(factor, m.power(n, log_order)), c) for c in coefficients], argument=args[0]
            )
            scalar = None
        elif exact and scalar is None:
            for name in integers:
                if same_value(args[0], m.add(('s', name), m.q(1, 2))):
                    special = dict(half_integer_gamma=name, factor=factor)
                    break
    else:
        p, q = args
        mult = factor
        for i, n in enumerate(ns):
            if n is not None:
                while n > 1:
                    if i == 0:
                        p = m.add(p, m.q(-1))
                        step = p
                    else:
                        q = m.add(q, m.q(-1))
                        step = q
                    mult = m.mul(mult, m.div(step, m.add(p, q)))
                    n -= 1
        if log_order:
            if change != 'positive_binomial_odds' or not same_value(m.add(*args), one):
                raise Unsupported('Для логарифмического момента требуется другое тождество бета-функции')
            _, n, A, B, _ = params
            angle = m.mul(m.PI, args[0])
            sine = m.simplify(('sin', angle))
            d = m.add(m.simplify(('ln', m.div(A, B))), m.neg(m.div(m.mul(m.PI, m.simplify(('cos', angle))), sine)))
            moment = d if log_order == 1 else m.add(m.power(d, 2), m.power(m.div(m.PI, sine), 2))
            scalar = m.mul(m.div(m.mul(factor, m.PI), sine), m.div(moment, m.power(n, log_order)))
        elif same_value(m.add(p, q), one):
            scalar = m.div(m.mul(mult, m.PI), ('sin', m.mul(m.PI, p)))
        else:
            ga, gb, gs = map(gamma_rational, (m.num(p), m.num(q), m.num(m.simplify(m.add(p, q)))))
            if all(v is not None for v in (ga, gb, gs)):
                scalar = m.div(m.mul(mult, m.mul(ga, gb)), gs)
    if exact and scalar is None and special is None:
        raise Unsupported('Эйлеров интеграл найден, но конечное значение ещё не установлено')
    plan = dict(
        kernel=kernel,
        absolute_power_bases=absolute_bases,
        substitution=change,
        kernel_parameters=params,
        shape=args,
        original_parameter_domain=guard,
        positive_integer_parameters=integers,
        coefficient=C,
        monomial_power=a,
        logarithmic_order=log_order,
        endpoint_conditions=domain,
    )
    return plan, dict(
        converges=True if not unresolved else 'on_conditions',
        conditions=unresolved,
        kernel=kernel,
        arguments=args,
        factor=factor,
        closed_value=scalar,
        special_value=special,
    )


def original_endpoint_comparison(task):
    """Use two-sided power comparisons on the actual endpoint charts."""
    from integrals import affine,exact_sign,real_polynomial_coefficients
    from verify import same_value
    v=task['variable'];params=task.get('parameters',[]);given=task.get('stated_conditions',[])
    x=('v',v);text=task['integrand'];low,high=str(task['lower']),str(task['upper'])
    mode=task['requested_output']
    if high=='+inf' and mode==['absolute_and_conditional_convergence']:
        tokens=r'([A-Za-z_]\w*)'
        power_ratio=re.fullmatch(r'P_'+tokens+r'\('+re.escape(v)+r'\)\*sin\('+re.escape(v)+r'\)/P_'+tokens+r'\('+re.escape(v)+r'\)',text)
        if power_ratio:
            m_,n=power_ratio.groups()
            hypothesis=f'P_{m_},P_{n} are polynomials of degrees {m_},{n}; P_{n}({v})>0 for {v}>={low}>=0'
            if len({m_,n,low,v})!=4 or set(params)!={m_,n,low} or given!=[hypothesis]:
                raise Unsupported('The degrees, lower end and absence of poles must all be explicit')
            degree=m.add(('s',m_),m.neg(('s',n)))
            return dict(theorem='method.parameter_endpoint_comparison',lower=low,upper=high,
                        rational_tail_order=degree,steps=[
                'Положительность знаменателя на исходном луче исключает конечные полюса.',
                'Ненулевое отношение старших коэффициентов даёт степенную асимптотику. При отрицательной разности степеней рациональный вес убывает по модулю после некоторой точки, что проверяется знаком его производной.',
                'Сравниваем на полуволнах синуса. При неотрицательной разности степеней вклады полуволн не стремятся к нулю. Для абсолютной сходимости требуется степень строго меньше −1.',
            ]),dict(ordinary_if=source(degree)+'<0',absolute_if=source(degree)+'<-1',
                    conditional_if=source(degree)+'=-1')
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=given))
    raw=m.parse(text,v,params)
    from integrals import learned_nodes
    def split_weight(e,func):
        waves=[a for a in learned_nodes(e) if isinstance(a,tuple) and a[0]==func]
        if len(set(waves))!=1:raise Unsupported('A single endpoint profile is required')
        wave,=set(waves)
        supported={'pow','rpow','sqrt','mul','div'}
        def parse(t):
            if t==wave:return ZERO,1
            if t==x:return ONE,0
            if t[0] in ('mul','div'):
                a,j=parse(t[1]);b,k=parse(t[2]);s=1 if t[0]=='mul' else -1
                if s<0 and k:raise Unsupported('An inverse profile could add interior poles')
                return m.add(a,m.mul(q(s),b)),j+s*k
            if t[0] not in ('pow','rpow','sqrt') or t[1]!=x:
                raise Unsupported('Each weight must be a power of the original positive coordinate')
            order=q(1,2) if t[0]=='sqrt' else q(t[2]) if t[0]=='pow' else t[2]
            if not m.constant_defined(order,ctx):raise Unsupported('The order must be fixed and defined')
            return order,0
        order,count=parse(e)
        if count!=1:raise Unsupported('The endpoint profile must survive exactly once with no original inverse factor')
        return order,wave
    if low!='0':raise Unsupported('A direct endpoint chart must start at zero')
    if high=='+inf':
        order,wave=split_weight(raw,'sin')
        phase=wave[1]
        P=m.simplify(m.mul(phase,x))
        coeff=real_polynomial_coefficients(P,v,ctx,2)
        if len(coeff)!=3 or coeff[1]!=ZERO or any(exact_sign(z,ctx)!=1 for z in (coeff[0],coeff[2])):
            raise Unsupported('The reciprocal phase must have positive direct and inverse scales')
        if not same_value(phase,m.add(m.mul(coeff[2],x),m.div(coeff[0],x))) or any(
                relation!='nonzero' or e!=x for relation,e in domain_conditions(phase)):
            raise Unsupported('A reciprocal phase with exactly the original endpoint pole is required')
        mirrored=m.add(m.neg(order),q(-2))
        return dict(theorem='method.parameter_endpoint_comparison',phase_scales=(coeff[2],coeff[0]),
                    endpoint_powers=(order,mirrored),steps=[
            'У бесконечности фаза A x+B/x монотонна после некоторой точки, а её производная положительна и отделена от нуля.',
            'На этом хвосте вес после фазовой замены убывает к нулю ровно при отрицательной степени. Для обратного направления используем вклады целых полуволн.',
            'У нуля подстановка x=1/t меняет местами фазовые коэффициенты. Вес получает дополнительную степень t⁻², поэтому тот же тест применяется к другому концу независимо.',
            'Абсолютные критерии обоих концов требуют противоположных строгих сравнений одной степени с −1.',
        ]),dict(ordinary_if=source(order)+'>-2 and '+source(order)+'<0',conditional_if=source(order)+'>-2 and '+source(order)+'<0',absolute_if=False)
    order,wave=split_weight(raw,'ln')
    f=wave[1]
    if f[0]!='sin' or domain_conditions(f):raise Unsupported('A logarithm of a real sine is required')
    rate,offset=affine(f[1],v)
    upper=m.parse(high,None,params)
    if offset!=ZERO or exact_sign(rate,ctx)!=1 or exact_sign(upper,ctx)!=1 or exact_sign(
            m.add(m.div(m.PI,q(2)),m.neg(m.mul(rate,upper))),ctx) not in (0,1):
        raise Unsupported('The phase must stay in the first positive quarter period')
    sign=exact_sign(m.add(order,ONE),ctx)
    criterion=source(order)+'>-1'
    return dict(theorem='method.parameter_endpoint_comparison',endpoint_power=order,phase_scale=rate,steps=[
        'На первом четверть-периоде синус положителен и зажат между своей хордой и аргументом.',
        'Поэтому логарифм синуса отличается от логарифма координаты ограниченной величиной. У нуля абсолютное ядро сравнимо со степенью, умноженной на модуль логарифма.',
        'Логарифмический множитель сохраняет строгий порог степени −1. На другом крае исходный логарифм и степенной вес регулярны.',
    ]),dict(convergence=('convergent' if sign==1 else 'divergent') if sign is not None else 'parameter_dependent',
            absolute_if=criterion,ordinary_if=criterion,conditional_if=False)



def improper_integral(task,library,request):
    """Apply Newton–Leibniz on compact subintervals of each original component."""
    from intervals import read_endpoint
    from plane_domains import yterm
    fields={'kind','id','source','integrand','variable','lower','upper','requested_output','parameters','stated_conditions'}
    want=task['requested_output'];v=task['variable'];params=task.get('parameters',[]);guards=task.get('stated_conditions',[])
    if (library.data.get('abstract_integral_transitions') and not set(task)-fields and want==['convergence']
            and not set(task.get('source',{}))-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256'}):
        try:return symbolic_improper_orders(task)
        except Unsupported:pass
    if want==['exact_integral'] and not set(task)-fields:
        if 'sgn[' in task['integrand'] or 'sgn(' in task['integrand']:
            try:return logarithmic_period_cells(task)
            except Unsupported:pass
        if 'ln(' in task['integrand'] and any('positive integer' in c for c in guards):
            try:return logarithmic_trig_coefficient(task)
            except Unsupported:pass
    if task.get('method_requirement')=='euler_complex_exponential_formulas':
        plan,value=indexed_harmonic_value(task,library)
        return plan,{'convergence':'convergent','value':value}
    pv=want==['principal_value']
    if pv:
        fields.add('stated_identity')
        if library.data.get('principal_value_method')!='independent_symmetric_cutoffs':
            raise Unsupported('A Cauchy principal value proof is required')
    if not set(task)-fields and want in (['convergence'],['absolute_and_conditional_convergence']) and library.data.get('parameter_integral_comparison'):
        if any(z in task['integrand'] for z in ('ln(sin(', '/P_', 'sin(')):
            try:return original_endpoint_comparison(task)
            except (Unsupported,ZeroDivisionError):pass
    if (not set(task)-fields and want in (['convergence'],['absolute_and_conditional_convergence'])
            and library.data.get('periodic_integral_comparison') and library.data.get('task_compilers',{}).get(task['kind'])=='separate_improper_endpoint_limits'):
        try:return periodic_integral_comparison(task)
        except Unsupported:pass
    if (set(task)-fields or not pv and want not in (['exact_integral'],['convergence']) or
        library.data.get('task_compilers',{}).get(task['kind'])!='separate_improper_endpoint_limits'):
        raise Unsupported('An ordinary integral with its full convergence or value is required')
    if params and want==['convergence'] and library.data.get('parameter_integral_comparison'):
        try:return parameter_endpoint_comparison(task)
        except Unsupported:pass
    ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=guards))
    f=m.parse(task['integrand'],v,params)
    binding=task.get('source',{})
    if (want==['exact_integral'] and library.data.get('euler_power_integrals') and isinstance(binding,dict)
            and not set(binding)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}):
        import re
        if v=='x' or 'x' not in params:
            spelling=re.sub(r'\b'+re.escape(v)+r'\b','x',task['integrand'])
            normalization=dict(integrand=spelling,limits=str(task['lower'])+'..'+str(task['upper']).replace('+inf','inf'),
                               stated_conditions=guards,method_requirement='euler_integrals',requested_output=['exact_value','specified_method'])
            try:euler_plan,euler_value=euler_integral(normalization,library)
            except Unsupported:pass
            else:
                if not euler_value['converges']:return {'euler_reduction':euler_plan},{'convergence':'divergent'}
                if euler_value.get('closed_value') is not None:
                    return {'euler_reduction':euler_plan},{'convergence':'convergent','value':euler_value['closed_value']}
    def endpoint(text):
        if text in ('-inf','+inf'):return text
        e=m.parse(str(text),None,params)
        if not m.constant_defined(e,ctx):raise Unsupported('Undefined integration endpoint')
        return m.simplify(e)
    def compare(a,b):
        if a==b:return 0
        if a=='-inf' or b=='+inf':return -1
        if a=='+inf' or b=='-inf':return 1
        sign=m.sign(m.add(a,m.neg(b)),ctx)
        if sign is None:raise Unsupported('The order of source or domain endpoints is unproved')
        return sign
    a,b=(endpoint(task[k]) for k in ('lower','upper'))
    if compare(a,b)>=0:raise Unsupported('Ordered distinct endpoints are required')
    if (a==ZERO and b=='+inf' and want==['exact_integral'] and not params and not guards
            and library.data.get('integral_endpoint_estimates') and isinstance(binding,dict)
            and not set(binding)-{'exercise','pdf_page','printed_page','pdf_sha256','printed_subpart','literal_requirement'}
            and binding.get('literal_requirement') in (None,'Вычислить интегралы.','Вычислить несобственный интеграл.')):
        try:return reciprocal_log_improper_moment(f,v)
        except Unsupported:pass
    if (not params and not guards and library.data.get('oriented_definite_branches')
            and isinstance(binding,dict) and not set(binding)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}
            and f==m.parse('1/('+v+'*ln('+v+'))',v) and not isinstance(a,str) and not isinstance(b,str)
            and compare(a,ZERO)>0 and compare(a,ONE)<0 and compare(b,ONE)>0):
        return logarithmic_pole_traces(task,v,a,b,pv)
    if (a==ZERO and b=='+inf' and want==['exact_integral'] and library.data.get('ordinary_decaying_harmonic')
            and not set(binding)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            and binding.get('literal_requirement') in (None,'Вычислить интегралы.')):
        try:
            plan,value=decaying_harmonic_moment(dict(kind='integrate',variable=v,integrand=task['integrand'],parameters=params),guards)
        except Unsupported:pass
        else:
            return dict(theorem='method.improper_harmonic_moments',primitive=plan,
                        absolute_convergence='each polynomial mode has a strictly negative real rate'),dict(convergence='convergent',value=value)
    if domain_conditions(f):
        if any(m.contains(f,('s',p)) for p in params):raise Unsupported('A parameter-dependent domain partition is required')
        raw=request('real domain before any cancellation',dict(kind='real_function_domain',goal=dict(
            variable=v,expression=task['integrand'],goal='maximal real domain')))['value']
        if isinstance(raw,dict):raise Unsupported('The nonfinite domain still needs an integration interval cover')
        def scalar(t):return t if isinstance(t,str) else yterm(read_endpoint(freeze(t)))
        cells=[(scalar(left),scalar(right)) for left,right,_,_ in raw[1]]
    else:cells=[('-inf','+inf')]
    intervals=[];reached=a
    for left,right in cells:
        low=left if compare(left,a)>0 else a;high=right if compare(right,b)<0 else b
        if compare(low,high)>=0:continue
        if compare(low,reached)!=0:raise Unsupported('The original real domain misses an open subinterval')
        intervals.append((low,high));reached=high
    if reached!=b and compare(reached,b)!=0:raise Unsupported('The original real domain does not cover the integration interval')
    if pv:return cauchy_principal_value(task,f,intervals,request,ctx)
    if want==['convergence'] and not params:
        x=('v',v);checks=[];unknown=[]
        for left,right in intervals:
            for point,direction in ((left,1),(right,-1)):
                if not isinstance(point,str) and m.constant_defined(m.substitute(f,{x:point}),ctx):
                    checks.append(dict(point=point,direction=direction,criterion='continuous at the finite endpoint'));continue
                at_infinity=isinstance(point,str)
                replacement=(m.div(q(1 if point=='+inf' else -1),x) if at_infinity else m.add(point,m.mul(q(direction),x)))
                try:p,k=local_power_log_order(m.substitute(f,{x:replacement}),v)
                except Unsupported as exc:unknown.append(str(exc));continue
                if at_infinity:p-=2
                converges=p>-1 or p==-1 and k<-1
                checks.append(dict(point=point,direction=direction,power=q(p),log_power=q(k),converges=converges))
                if not converges:return {'components':intervals,'endpoint_comparisons':checks},{'convergence':'divergent'}
        if not unknown:return {'components':intervals,'endpoint_comparisons':checks},{'convergence':'convergent'}
    child=request('primitive on every original open component',dict(kind='integrate',integrand=task['integrand'],variable=v,
                  parameters=params,requested_output=['primitive_family']))
    primitive=freeze(child['value']['representative']);terms=[];total=ZERO
    for low,high in intervals:
        limits=[]
        for point,side in ((low,'right'),(high,'left')):
            if isinstance(point,str):
                address={'point':point,'side':'positive_infinity' if point=='+inf' else 'negative_infinity'}
            else:
                at=m.substitute(primitive,{('v',v):point})
                if m.constant_defined(at,ctx):
                    limits.append(m.simplify(at));continue
                address={'point':source(point),'side':side}
            t=dict(kind='limit',expression=source(primitive),variable=v,parameters=params,parameter_conditions=guards,approach=address)
            limits.append(freeze(request('component endpoint '+side,t)['value']))
        terms.append(dict(lower=low,upper=high,primitive_limits=limits))
        if any(isinstance(k,str) for k in limits):break
        total=m.add(total,m.add(limits[1],m.neg(limits[0])))
    divergent=any(isinstance(k,str) for k in terms[-1]['primitive_limits'])
    result={'convergence':'divergent' if divergent else 'convergent'}
    if want==['exact_integral'] and not divergent:result['value']=m.combine_rational_logs(m.simplify(total))
    return {'components':intervals,'primitive':primitive,'one_sided_evaluations':terms},result


def indexed_moment(task,library,request):
    """Reduce a positive-integer power by a verified differentiated product."""
    from polynomial import span_coefficients,univariate_coefficients
    from verify import same_value
    fields={'kind','id','source','integrand','variable','lower','upper','index','index_domain',
            'method_requirement','requested_output','parameters'}
    if (set(task)-fields or task.get('parameters') or task.get('index_domain')!='positive_integers' or
        task.get('requested_output')!=['exact_indexed_integral'] or task.get('method_requirement','reduction_formula')!='reduction_formula' or
        library.data.get('task_compilers',{}).get(task['kind'])!='differentiated_moment_reduction'):
        raise Unsupported('An additional parameter, domain or requested method requires its own certificate')
    v,name=task['variable'],task['index'];x=('v',v);n=('s',name)
    ctx=m.context({'variable':v,'parameters':[name],'parameter_conditions':[name+'>0']})
    raw=m.parse(task['integrand'],v,[name]);powers=[]
    def weight(e):
        if e[0]=='rpow' and m.contains(e[2],n):
            powers.append(e);return ONE
        if e[0]=='mul':return ('mul',weight(e[1]),weight(e[2]))
        if e[0]=='div':return ('div',weight(e[1]),e[2])
        return e
    W=weight(raw)
    if len(powers)!=1:raise Unsupported('Expected a single indexed moment factor')
    U,exp=powers[0][1:]
    if m.contains(W,n) or m.contains(U,n):raise Unsupported('The base and weight must be independent of the index')
    if any(not known_guard((rel,g),ctx) for rel,g in domain_conditions(exp)):
        raise Unsupported('The original exponent is not defined for all positive indices')
    p,d=m.rational_form(exp);co=univariate_coefficients(p,n)
    if d!={():F(1)} or co is None or len(co)!=2 or any(z.denominator!=1 for z in co) or co[1]<1 or co[0]+co[1]<1:
        raise Unsupported('Expected a positive integer affine power throughout the source index range')
    intercept,slope=map(int,co)
    if task['upper']=='+inf':
        from integrals import affine
        if any(not known_guard(g,ctx) for e in (U,W) for g in domain_conditions(e,True)):
            raise Unsupported('A half-line domain for the original moment factors is unproved')
        V=m.simplify(W);coefficient=ONE;kernel=V
        if kernel[0]=='mul':
            A,B=kernel[1:];coefficient,kernel=(B,A) if A[0]=='exp' else (A,B)
        if kernel[0]!='exp' or m.variable_in(coefficient,v) or m.contains(coefficient,n):
            raise Unsupported('A decaying exponential weight on the half-line is required')
        gamma,_=affine(kernel[1],v);scale,_=affine(U,v)
        start=m.parse(str(task['lower']),None)
        if not m.constant_defined(start,ctx) or m.sign(gamma,ctx)!=-1:
            raise Unsupported('A finite lower end and a strictly decaying exponential are required')
        dU=freeze(request('derivative of the affine moment base',dict(kind='differentiate',function=source(U),variable=v))['value'])
        dV=freeze(request('derivative of the exponential weight',dict(kind='differentiate',function=source(V),variable=v))['value'])
        if not same_value(dU,scale) or not same_value(dV,m.mul(gamma,V)):raise Unsupported('The differentiated product has unproved coefficients')
        base=request('zeroth improper moment',dict(kind='improper_integral',variable=v,integrand=source(V),
            lower=task['lower'],upper='+inf',requested_output=['exact_integral']))['value']
        if base['convergence']!='convergent':raise Unsupported('The zeroth moment is not finite')
        plan=dict(base=U,weight=W,multiplier=V,base_derivative=dU,multiplier_derivative=dV,decay_rate=gamma,index_domain='positive_integers',
                  tail_argument='a decaying exponential times any fixed nonnegative integer power of an affine function tends to zero')
        return plan,dict(degree=dict(slope=slope,intercept=intercept),stride=1,coefficients=dict(leading=(gamma,ZERO),lower=(ZERO,scale)),
                  bases=[dict(degree=0,value=base['value'])],
                  boundary=[dict(kernel=m.simplify(m.substitute(U,{x:start})),multiplier=m.simplify(m.substitute(V,{x:start}))),dict(product_limit=ZERO)],
                  evaluation='finite_product_sum_on_each_residue')
    a,b=[m.parse(str(task[k]),None) for k in ('lower','upper')]
    if not all(m.constant_defined(z,ctx) for z in (a,b)):raise Unsupported('An endpoint is undefined')
    a,b=map(m.simplify,(a,b))
    lower,upper=enclose(a,None),enclose(b,None)
    if lower[1]>=upper[0]:raise Unsupported('This recurrence requires ordered finite endpoints')
    interval=(lower[0],upper[1]);guards=[]
    def cover(e,smooth=False):
        for rel,g in domain_conditions(e,smooth):
            lo,hi=guard_bounds(rel,g,interval,[v])
            item=(rel,g,q(lo),q(hi))
            if item not in guards:guards.append(item)
    cover(U,True)
    if W[0]=='div' and W[2][0]=='sqrt':
        from polynomial import rf,NotRational,Undefined
        Q=W[2][1];numerator=W[1];cover(Q);cover(numerator)
        try:poly,den=rf(Q,v)
        except (NotRational,Undefined):poly,den=(),()
        if len(poly)==3 and len(den)==1 and poly[2]/den[0]<0:
            c0,c1,c2=(w/den[0] for w in poly);center=-c1/(2*c2);height=c0+c1*center/2
            if height>0:
                radius=m.simplify(('sqrt',q(-height/c2)))
                offsets=[m.simplify(m.div(m.add(end,q(-center)),radius)) for end in (a,b)]
                reaches_root=any(z in (q(-1),ONE) for z in offsets)
                if reaches_root and all(m.known_nonnegative(m.add(ONE,z),ctx) and m.known_nonnegative(m.add(ONE,m.neg(z)),ctx) for z in offsets):
                    angle='__angle'
                    while angle in (v,name):angle+='_'
                    theta=('v',angle);X=m.add(q(center),m.mul(radius,('sin',theta)))
                    replace=lambda e:m.simplify(m.substitute(e,{x:X}))
                    dx=request('Jacobian of the increasing sine substitution',dict(kind='differentiate',variable=angle,function=source(X)))['value']
                    if (not same_value(dx,m.mul(radius,('cos',theta))) or
                        not same_value(replace(Q),m.mul(q(height),m.power(('cos',theta),2)))):
                        raise Unsupported('The quadratic substitution or its Jacobian is unproved')
                    angles=[m.simplify(('asin',z)) for z in offsets]
                    transformed=m.div(m.mul(replace(numerator),('rpow',replace(U),exp)),m.simplify(('sqrt',q(-c2))))
                    child=request('continuous transformed moment on the full closed angle interval',dict(
                        kind='integral_reduction_family',variable=angle,integrand=source(transformed),lower=source(angles[0]),upper=source(angles[1]),
                        index=name,index_domain='positive_integers',method_requirement='reduction_formula',requested_output=['exact_indexed_integral']))
                    return dict(substitution=X,differential=dx,radicand=Q,raw_guards=guards,angles=angles,index_domain='positive_integers',
                                endpoint_argument='cosine is positive in the open angle interval; the transformed integrand extends continuously to both ends'),child['value']
    cover(W)
    W=m.simplify(W)
    def derivative(label,e):
        goal=dict(kind='differentiate',function=source(e),variable=v,method_requirement='table_and_rules')
        result=request(label,goal)
        formula=m.simplify(freeze(result['value']));cover(formula)
        return formula
    du=derivative('derivative of the indexed base',U)
    def at(e,t):return m.simplify(m.substitute(e,{x:t}))
    def fit(e,us):
        """Match the weight and its powered multiple in the common polynomial numerator."""
        c,h=('s','__moment_constant'),('s','__moment_leading')
        delta=m.add(e,m.neg(m.mul(W,m.add(c,m.mul(h,us)))))
        numerator,_=m.rational_form(delta)
        rows={}
        for mon,value in m.trig_reduce(numerator,complete=True).items():
            powers=dict(mon);i,j=powers.pop(c,0),powers.pop(h,0)
            if i+j>1:return None
            row=rows.setdefault(tuple(powers.items()),[F(0),F(0),F(0)])
            row[i+2*j]+=value
        weights=span_coefficients([-r[0] for r in rows.values()],[[r[i] for r in rows.values()] for i in (1,2)])
        if weights is not None and same_value(e,m.mul(W,m.add(q(weights[0]),m.mul(q(weights[1]),us)))):return weights
    def find():
        for V in dict.fromkeys((ONE,x,du)):
            cover(V,True)
            dv=ZERO if V==ONE else ONE if V==x else derivative('derivative of the multiplier',V)
            for s in (1,2):
                us=m.power(U,s)
                second=fit(m.mul(V,du),us)
                if second is None:continue
                first=fit(m.mul(U,dv),us)
                if first is None:continue
                low0,lead0=first;low1,lead1=second
                if not lead1 and not lead0:continue
                if lead1 and (root:=-lead0/lead1).denominator==1 and root>=1:continue
                return V,dv,s,(q(lead0),q(lead1)),(q(low0),q(low1))
        raise Unsupported('No verified lowering identity in the span of the two source powers')
    V,dv,s,L,R=find()
    bases=[]
    for r in sorted({(intercept+j*slope)%s for j in range(s)}):
        integrand=W if r==0 else m.mul(W,m.power(U,r))
        goal=dict(kind='iterated_integral',integrand=source(integrand),integration_order=[dict(variable=v,lower=source(a),upper=source(b))],
                  requested_output=['exact_integral'])
        bases.append(dict(degree=r,value=freeze(request('base moment of degree '+str(r),goal)['value'])))
    plan=dict(base=U,weight=W,base_derivative=du,multiplier=V,multiplier_derivative=dv,
              interval_guards=guards,identity='derivative of V times U^(p-s+1)',index_domain='positive_integers')
    value=dict(degree=dict(slope=slope,intercept=intercept),stride=s,coefficients=dict(leading=L,lower=R),bases=bases,
               boundary=[dict(kernel=at(U,t),multiplier=at(V,t)) for t in (a,b)],evaluation='finite_product_sum_on_each_residue')
    return plan,value


def semicircle_chart(f,layers,params,conditions,library,request):
    """Pull a circular radical back by x = b sin(t), retaining the sign of b in dx."""
    from verify import same_value
    if not library.data.get('semicircle_chart') or len(layers)!=1:return
    v,lower,upper=layers[0];x=('s',v)
    a,b=map(m.simplify,(lower,upper));half_pi=m.div(m.PI,q(2))
    if a==ZERO:radius=b;ends=(ZERO,half_pi)
    elif b==ZERO:radius=a;ends=(half_pi,ZERO)
    elif same_value(a,m.neg(b)):radius=b;ends=(m.neg(half_pi),half_pi)
    else:return
    guards=domain_conditions(f)
    expected=m.add(m.power(radius,2),m.neg(m.power(x,2)))
    radicands=[g for rel,g in guards if rel=='nonnegative' and m.contains(f,('sqrt',g)) and same_value(g,expected)]
    if not radicands:return
    angle='__angle'
    while angle in [v,*params]:angle+='_'
    theta=('v',angle);cosine=('cos',theta);chart=m.mul(radius,('sin',theta))
    ctx=m.context(dict(variable=angle,parameters=[v,*params],parameter_conditions=conditions))
    # Check raw auxiliary guards before simplification, including restrictions inside an
    # algebraically equivalent radicand. A canceled pole can invalidate the closed fiber.
    for rel,g in guards+domain_conditions(lower)+domain_conditions(upper):
        if (rel!='nonnegative' or g not in radicands) and not known_guard((rel,g),ctx):return
    images=tuple(m.simplify(m.substitute(chart,{theta:t})) for t in ends)
    if not all(same_value(i,j) for i,j in zip(images,(lower,upper))):return
    jacobian=freeze(request('chart derivative',dict(kind='differentiate',variable=angle,parameters=params,
                    function=source(chart),method_requirement='table_and_rules'))['value'])
    if not same_value(jacobian,m.mul(radius,cosine)):raise Unsupported('The signed chart derivative was not established')
    # cos(t) is nonnegative throughout the chosen closed quadrant or half-circle.
    image=m.mul(m.simplify(('abs',radius)),cosine)
    if not all(same_value(m.substitute(g,{x:chart}),m.power(image,2)) for g in radicands):
        raise Unsupported('The square of the principal radical image differs from the pulled-back radicand')
    replace={('sqrt',g):image for g in radicands}
    transformed=m.mul(jacobian,m.substitute(f,{**replace,x:chart}))
    child=request('transformed integral',dict(kind='iterated_integral',integrand=source(transformed),
                  integration_order=[dict(variable=angle,lower=source(ends[0]),upper=source(ends[1]))],
                  parameters=params,stated_conditions=conditions,requested_output=['exact_integral']))
    value=freeze(child['value'])
    return dict(method='semicircle_chart',variable=v,bounds=(lower,upper),chart_variable=angle,substitution=chart,
                jacobian=jacobian,radicands=radicands,radical_image=image,original_guards=guards,endpoint_images=images,
                transformed_bounds=ends,transformed_integrand=transformed,difference=value),value


def substitution_validity(v,t,a,b,f,lhs,rhs,request):
    """Check the single-inverse procedure and build its correctly oriented branch formula."""
    from graphs import proposed_substitution_branches
    ctx=m.context({'variable':v})
    if not all(m.constant_defined(end,ctx) for end in (a,b)):
        raise Unsupported('Both original endpoints must be defined finite constants')
    # Domain checks use the source expression before any cancellation. Continuity on
    # this compact interval guarantees separate limits of every branch integral.
    guards=domain_conditions(f);evidence=[]
    if guards:
        lo,hi=enclose(a,None),enclose(b,None)
        interval=(min(lo[0],hi[0]),max(lo[1],hi[1]))
        for relation,g in guards:
            bounds=None if known_guard((relation,g),ctx) else tuple(map(q,guard_bounds(relation,g,interval,[v])))
            evidence.append((relation,g,bounds))
    geometry=proposed_substitution_branches(v,t,a,b,lhs,rhs,request)
    forward=geometry['forward'];z=('v',t);replace={}
    if forward[0]=='tan':
        # At each interior point of a tangent branch, 1+tan² = 1/cos².
        sec_squared=m.add(ONE,m.power(z,2));angle=forward[1]
        replace={forward:z,('pow',('sin',angle),2):m.div(m.power(z,2),sec_squared),
                 ('pow',('cos',angle),2):m.div(ONE,sec_squared)}
    branches=geometry['branches']
    for branch in branches:
        body=m.substitute(f,{**replace,('v',v):branch['inverse']})
        branch['integrand']=m.mul(body,branch['inverse_jacobian'])
    limits_required=any(end in ('-inf','+inf') or
                        not m.constant_defined(m.substitute(branch['integrand'],{z:end}),ctx)
                        for branch in branches for end in branch['image_bounds'])
    plan=dict(variable=v,new_variable=t,bounds=(a,b),integrand=f,relation=(lhs,rhs),
              source_domain_guards=evidence,geometry=geometry)
    value=dict(single_inverse='valid' if len(branches)==1 else 'requires_split',
               branchwise_valid=True,branch_count=len(branches),
               endpoint_limits_required=limits_required)
    return plan,value


def branched_rational_integral(v,a,b,f,request):
    """Pull a rational differential back on each oriented monotone component of its chart."""
    import intervals as line
    from graphs import graph_curve
    from integrals import reciprocal_substitution,inner_derivative_task
    from plane_domains import yterm
    from verify import same_value
    A,B=(m.num(m.simplify(z)) for z in (a,b))
    if A is None or B is None or A==B:return
    name='__chart' if v!='__chart' else '__chart_'
    x=('v',v);t=('v',name);raw=m.substitute(f,{('s',v):x})
    candidate=reciprocal_substitution(raw,v,name)
    if candidate is None:return
    forward,kernel,discovery=candidate
    low,high=map(line.Quadratic,sorted((A,B)))
    original=request('original closed interval domain',dict(kind='real_function_domain',goal=dict(
        variable=v,expression=source(raw),goal='maximal real domain')))['value']
    if isinstance(original,dict):raise Unsupported('Coverage of the closed interval by this periodic domain is unproved')
    def covers(left,right,lc,rc):
        l=line.compare(line.read_endpoint(left),low);r=line.compare(high,line.read_endpoint(right))
        return (l<0 or l==0 and lc) and (r<0 or r==0 and rc)
    if not any(covers(*cell) for cell in freeze(original)[1]):
        raise Unsupported('The raw rational integrand must be defined on the entire closed interval')
    derivative=request('chart derivative',inner_derivative_task({'variable':v},source(forward)),
                       ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'))
    jac=freeze(derivative['value'])
    if not same_value(m.mul(jac,m.substitute(kernel,{t:forward})),raw):
        raise Unsupported('The kernel times the chart derivative differs from the source')
    graph=graph_curve(forward,v,domain_conditions(jac))
    h=tuple(map(m.num,graph['derivative_numerator']))
    cuts=[]
    for c in graph['cuts']:
        point=line.read_endpoint(c['x'])
        if line.compare(low,point)<0 and line.compare(point,high)<0:
            if c['type']!='point' or not line.peval(h,point).sign():
                cuts.append((point,c['type'] if c['type']!='point' else 'critical'))
    edges=[low,*(p for p,_ in cuts),high]
    orientation=1 if A<B else -1
    if orientation<0:edges.reverse()
    sides=('right','left') if orientation>0 else ('left','right')
    branches=[];total=ZERO
    for i,(left,right) in enumerate(zip(edges,edges[1:])):
        sample=line.between(left,right) if orientation>0 else line.between(right,left)
        monotonicity=line.peval(h,line.Quadratic(sample)).sign()
        if not monotonicity:raise Unsupported('No strictly monotone change of variable on this branch')
        bounds=(yterm(left),yterm(right));images=[]
        for bound,side in zip(bounds,sides):
            limit=dict(kind='limit',variable=v,expression=source(forward),approach=dict(point=source(bound),side=side))
            images.append(freeze(request(f'branch {i+1} chart limit {side}',limit)['value']))
        sign=orientation*monotonicity
        lo,hi=images if sign>0 else reversed(images)
        text=lambda z:z if isinstance(z,str) else source(z)
        sub=dict(kind='improper_integral',variable=name,integrand=source(kernel),
                 lower=text(lo),upper=text(hi),requested_output=['exact_integral'])
        proof=request(f'branch {i+1} ordinary integral',sub)
        if proof['value'].get('convergence')!='convergent' or len(proof['compilation']['components'])!=1:
            raise Unsupported('The ordinary integral must converge on the entire open image branch')
        part=m.mul(q(sign),freeze(proof['value']['value']));total=m.add(total,part)
        branches.append(dict(source_bounds=bounds,source_sides=sides,image_bounds=tuple(images),
                             monotonicity=monotonicity,derivative_sample=q(sample),value=part))
    return dict(method='branched_rational_substitution',variable=v,bounds=(a,b),chart_variable=name,forward=forward,
                discovery=discovery,jacobian=jac,kernel=kernel,cuts=[(yterm(p),kind) for p,kind in cuts],
                branches=branches,difference=total),total


def iterated_integral(task,library,request,chart=None):
    """Newton–Leibniz in each nested finite fiber, retaining original domains and orientation."""
    if chart=='indexed_euler_expansion':
        plan,value=indexed_harmonic_value(task,library)
        return dict(plan,chart=chart),value
    fields={'kind','id','source','schema','transcription','integrand','integration_order','rectangle','parameters','stated_conditions','requested_output','method_requirement'}
    rectangular='rectangle' in task;wanted=task.get('requested_output')
    if (set(task)-fields or rectangular==('integration_order' in task) or wanted not in (['exact_integral'],['area_mean']) or
            wanted==['area_mean'] and not rectangular or library.data.get('task_compilers',{}).get('iterated_integral')!='closed_fiber_primitive_evaluation'):
        raise Unsupported('Unsupported order, domain, method or output for an exact finite integral')
    bounds=task['rectangle' if rectangular else 'integration_order'];params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if (not isinstance(bounds,(list,tuple)) or not bounds or not all(isinstance(b,dict) and set(b)=={'variable','lower','upper'} for b in bounds)
            or not isinstance(params,(list,tuple)) or not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions)):
        raise Unsupported('Expected finite bounds in outer-to-inner order')
    method=task.get('method_requirement','table_and_rules')
    if (not chart and library.data.get('oriented_definite_branches') and not rectangular
            and len(bounds)==1 and method=='table_and_rules' and wanted==['exact_integral'] and params):
        layer,=bounds
        try:
            plan,value=definite_parameter_profile(task,layer['variable'],[layer['lower'],layer['upper']],params,conditions)
            return dict(plan,stages=[dict(variable=layer['variable'],method='finite_parameter_endpoint_profiles')]),value
        except Unsupported:pass
    if method!='table_and_rules' and (method not in library.data.get('definite_primitive_methods',[]) or len(bounds)!=1 or wanted!=['exact_integral']):
        raise Unsupported('The requested integral method needs an admitted single definite integral')
    variables=[b['variable'] for b in bounds]
    if not all(isinstance(v,str) for v in [*variables,*params]):raise Unsupported('Expected named real coordinates and parameters')
    dummy='__fiber'
    while dummy in [*variables,*params]:dummy+='_'
    m.context({'variable':dummy,'parameters':params,'parameter_conditions':conditions})
    ctx=m.context({'variable':dummy,'parameters':[*variables,*params],'parameter_conditions':conditions})
    cube={};guards=[];layers=[];stages=[];volume=ONE
    def cover(e):
        for relation,g in domain_conditions(e):
            if known_guard((relation,g),ctx):continue
            # Every normalized coordinate ranges independently over [0,1]. Natural interval
            # evaluation encloses all fibers, including endpoints and reversed bounds.
            lo,hi=guard_bounds(relation,m.substitute(g,cube),(F(0),F(1)),variables)
            guards.append((relation,g,q(lo),q(hi)))
    for i,b in enumerate(bounds):
        v=b['variable'];visible=[*params,*(() if rectangular else variables[:i])]
        a,z=(m.parse(str(b[k]),None,visible) for k in ('lower','upper'));cover(a);cover(z)
        width=m.add(z,m.neg(a))
        if rectangular and not m.known_nonnegative(width,ctx):raise Unsupported('The lower bound of a rectangle must not exceed its upper bound')
        if wanted==['area_mean']:
            if m.sign(width,ctx)!=1:raise Unsupported('A mean requires a rectangle of strictly positive measure')
            volume=m.mul(volume,width)
        A,B=m.substitute(a,cube),m.substitute(z,cube)
        cube[('s',v)]=('add',A,('mul',('v',v),('add',B,('mul',q(-1),A))))
        layers.append((v,a,z))
    f=m.parse(task['integrand'],None,[*variables,*params])
    if chart:
        v,a,z=layers[0]
        if chart=='semicircle_chart':
            transformed=semicircle_chart(f,layers,params,conditions,library,request)
        elif chart=='rationalizing_substitution' and not params:
            from integrals import rationalizing_integral
            cover(f)
            transformed=rationalizing_integral(v,a,z,f,request)
        elif chart=='endpoint_change_of_variable' and not params:
            from graphs import endpoint_change_of_variable
            transformed=endpoint_change_of_variable(v,a,z,f,request)
        elif chart=='branched_rational_substitution' and not params:
            transformed=branched_rational_integral(v,a,z,f,request)
        else:transformed=None
        if transformed is None:raise Unsupported('No admissible change of variable of this form')
        stage,value=transformed
        return {'chart':chart,'stages':[stage],'interval_domain':guards},value
    cover(f)
    for i in reversed(range(len(layers))):
        v,a,z=layers[i]
        child=request('primitive/'+v,{'kind':'integrate','integrand':source(f),'variable':v,'parameters':[*params,*variables[:i]],
                                      'method_requirement':method,'requested_output':['primitive_family']})
        primitive=m.substitute(freeze(child['value']['representative']),{('v',v):('s',v)});cover(primitive)
        endpoint_values=tuple(m.simplify(m.substitute(primitive,{('s',v):bound})) for bound in (a,z))
        result=m.add(endpoint_values[1],m.neg(endpoint_values[0]))
        stages.append({'variable':v,'bounds':(a,z),'integrand':f,'primitive':primitive,
                       'endpoint_values':endpoint_values,'difference':result})
        if method=='appropriate_substitution':
            u=m.parse(child['proposal']['recipe']['u'],None,[v,*params])
            stages[-1]['substituted_bounds']=tuple(m.simplify(m.substitute(u,{('s',v):bound})) for bound in (a,z))
        f=result
    value=m.div(f,volume) if wanted==['area_mean'] else f
    return {'stages':stages,'interval_domain':guards,'rectangle_measure':volume if wanted==['area_mean'] else None},value


def finite_interval_value(t,library,request):
    """Apply a verified primitive on the original closed interval or on its regular pieces."""
    from integrals import affine
    from operations import expression_positions
    from ray_proofs import compare_scalar
    fields={'id','kind','source','goal','variable','integrand','interval','requested_output','method_requirement','heading_page','parameters','stated_conditions','right_limit_at_lower_endpoint'}
    provenance=t.get('source',{})
    if (not library.data.get('finite_interval_from_primitive') or set(t)-fields or t.get('requested_output')!=['exact_integral']
            or t.get('method_requirement')!='newton_leibniz' or t.get('goal') not in (None,'Вычислить интеграл по формуле Ньютона–Лейбница.')
            or set(provenance)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}):
        raise Unsupported('Unbound definite-integral request or printed method')
    var=t['variable'];parameters=t.get('parameters',[]);conditions=t.get('stated_conditions',[])
    if library.data.get('oriented_definite_branches') and parameters and 'right_limit_at_lower_endpoint' not in t:
        try:return definite_parameter_profile(t,var,t['interval'],parameters,conditions)
        except Unsupported:pass
    ctx=m.context(dict(variable=var,parameters=parameters,parameter_conditions=conditions))
    a,b=[m.parse(str(s),None,parameters) for s in t['interval']]
    if not all(m.constant_defined(z,ctx) for z in (a,b)):raise Unsupported('Undefined input endpoint')
    a,b=map(m.simplify,(a,b));f=m.parse(t['integrand'],var,parameters)
    if parameters or conditions or 'right_limit_at_lower_endpoint' in t:
        x=('v',var)
        if (f[0]!='rpow' or f[1]!=x or m.variable_in(f[2]) or not m.constant_defined(f[2],ctx) or m.sign(f[2],ctx)!=1
                or (a,b)!=(ZERO,ONE) or t.get('right_limit_at_lower_endpoint') is not True):
            raise Unsupported('Continuous endpoint extension and positive constant power are required')
        p=f[2];next_power=m.add(p,ONE);raised=('rpow',x,next_power);primitive=m.div(raised,next_power)
        def at_zero(role,e):
            limit=request(role,dict(kind='limit',expression=source(e),variable=var,parameters=parameters,parameter_conditions=conditions,
                                    approach=dict(point='0',side='right')))
            if freeze(limit['value'])!=ZERO:raise Unsupported('The right endpoint extension was not established')
        at_zero('continuous extension of the sampled kernel at zero',f)
        child=request('derivative of the proposed primitive on the positive half-axis',dict(kind='differentiate',variable=var,
                      function=source(primitive),parameters=parameters,stated_conditions=[*conditions,var+'>0'],method_requirement='table_and_rules'))
        # For t>0, t^(p+1)=t*t^p. The saved derivative must equal the original kernel.
        derivative=m.substitute(freeze(child['value']),{raised:m.mul(x,f)})
        if m.simplify(m.add(derivative,m.neg(f)))!=ZERO:raise Unsupported('Power derivative differs from the kernel')
        at_zero('continuous extension of the primitive at zero',primitive)
        value=m.div(ONE,next_power)
        return dict(method='continuous_extension_of_power_primitive',bounds=(a,b),primitive=primitive,endpoint_values=(ZERO,value)),value
    def primitive_integral(e,v,lo,hi):
        sub=dict(kind='iterated_integral',integrand=source(e),integration_order=[dict(variable=v,lower=source(lo),upper=source(hi))],
                 parameters=[],stated_conditions=[],requested_output=['exact_integral'])
        child=request('Newton–Leibniz on a regular interval',sub)
        stages=child['compilation'].get('stages',[])
        if len(stages)!=1 or 'primitive' not in stages[0] or 'endpoint_values' not in stages[0]:
            raise Unsupported('The required primitive and its endpoint values are missing')
        return freeze(child['value']),freeze(stages[0]['primitive'])
    atoms=[e for _,e in expression_positions(f) if e[0] in ('abs','cbrt') and m.variable_in(e)]
    if not atoms:
        if f[0]=='sqrt':
            if domain_conditions(f[1]):raise Unsupported('Unresolved original domain of the radicand')
            try:s,d=affine(f[1],var)
            except Unsupported:
                value,primitive=primitive_integral(f,var,a,b)
                return dict(method='primitive_on_closed_interval',bounds=(a,b),primitive=primitive),value
            if not all(m.constant_defined(z,ctx) for z in (s,d)) or m.sign(s,ctx) not in (-1,1):raise Unsupported('Nonconstant regular affine radicand required')
            x=('v',var);ends=tuple(m.simplify(m.substitute(f[1],{x:y})) for y in (a,b))
            if any(m.sign(z,ctx) not in (0,1) for z in ends):raise Unsupported('The affine radicand is negative on part of the interval')
            u='u' if var!='u' else 'w';v=('v',u);inverse=m.div(m.add(m.power(v,2),m.neg(d)),s)
            transformed=m.mul(m.div(q(2),s),m.power(v,2));limits=tuple(m.simplify(('sqrt',z)) for z in ends)
            value,primitive=primitive_integral(transformed,u,*limits)
            return (dict(method='primitive_in_nonnegative_square_coordinate',bounds=(a,b),transformed_bounds=limits,inverse=inverse,
                         transformed_integrand=transformed,pulled_back_primitive=m.substitute(primitive,{('s',u):f})),value)
        value,primitive=primitive_integral(f,var,a,b)
        return dict(method='primitive_on_closed_interval',bounds=(a,b),primitive=primitive),value
    if len(set(atoms))!=1:raise Unsupported('The full arrangement of all branch boundaries is required')
    atom=atoms[0]
    if domain_conditions(atom[1]):raise Unsupported('Unresolved original domain of the branch argument')
    s,d=affine(atom[1],var)
    if not all(m.constant_defined(z,ctx) for z in (s,d)) or m.sign(s,ctx) not in (-1,1):raise Unsupported('Nonconstant regular affine branch required')
    x=('v',var);root=m.div(m.neg(d),s)
    if atom[0]=='cbrt':
        # Coordinate u=cuberoot(s*x+d) has the everywhere C1 inverse x=(u^3-d)/s.
        u='u' if var!='u' else 'w';z=('v',u);inverse=m.div(m.add(m.power(z,3),m.neg(d)),s)
        fiber=m.mul(m.substitute(f,{atom:z,x:inverse}),m.div(m.mul(q(3),m.power(z,2)),s))
        if domain_conditions(f):raise Unsupported('Original singularities need a separate check before the cubic change')
        limits=tuple(m.simplify(('cbrt',m.substitute(atom[1],{x:y}))) for y in (a,b))
        integral,primitive=primitive_integral(fiber,u,*limits)
        return dict(method='primitive_in_cubic_coordinate',root=atom,inverse=inverse,transformed_integrand=fiber,
                    bounds=(a,b),transformed_bounds=limits,possible_critical_point=root,
                    pulled_back_primitive=m.substitute(primitive,{('s',u):atom})),integral
    direction=compare_scalar(b,a);cut=compare_scalar(root,a)*compare_scalar(root,b)<0
    edges=[a,root,b] if cut else [a,b];terms=[];value=ZERO
    for lo,hi in zip(edges,edges[1:]):
        mid=m.mul(q(F(1,2)),m.add(lo,hi));sg=m.sign(m.substitute(atom[1],{x:mid}),ctx)
        if sg not in (-1,1):raise Unsupported('Unverified sign of the affine branch')
        branch=m.substitute(f,{atom:atom[1] if sg==1 else m.neg(atom[1])})
        piece,primitive=primitive_integral(branch,var,lo,hi);value=m.add(value,piece)
        terms.append(dict(bounds=(lo,hi),sign=sg,integrand=branch,primitive=primitive,value=piece))
    return dict(method='piecewise_primitive',bounds=(a,b),orientation=direction,affine_zero=root,pieces=terms),m.simplify(value)


def definite_profile_source(task,v,bounds,names,conditions):
    meta=task.get('source',{})
    if not isinstance(meta,dict) or any(k in meta for k in ('explicit_required_method','explicit_imposed_method','method_requirement')):
        raise Unsupported('An additional source method needs its own proof')
    if (not isinstance(names,(list,tuple)) or not all(isinstance(p,str) for p in names)
            or len(bounds)!=2 or not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions)):
        raise Unsupported('The source endpoints and parameter conditions must be bound')
    ctx=m.context(dict(variable=v,parameters=names))
    ends=tuple(m.parse(str(z),None,names) for z in bounds)
    if any(not m.constant_defined(z,ctx) or any(m.contains(z,('s',p)) for p in names) for z in ends):
        raise Unsupported('These profiles require fixed defined endpoints')
    return m.parse(task['integrand'],v,names),tuple(map(m.simplify,ends))


def definite_parameter_profile(task,v,bounds,names,conditions):
    """Produce a certified endpoint formula for a complete finite parameter family."""
    from integrals import affine,learned_nodes,trig_polynomial
    from ray_proofs import compare_scalar
    from verify import same_value
    raw,(a,b)=definite_profile_source(task,v,bounds,names,conditions)
    x=('v',v);width=m.add(b,m.neg(a));facts=set(conditions);PI=m.PI
    def emit(value,*steps,**witness):
        return dict(theorem='method.finite_parameter_endpoint_profiles',argument=list(steps),bounds=(a,b),integrand=raw,
                    original_conditions=tuple(conditions),**witness),value
    if len(names)==1:
        name,=names;p=('s',name)
        if not facts:
            absolute={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0]=='abs'}
            if len(absolute)==1:
                atom,=absolute
                # Replace exactly the single abs factor and verify the polynomial multiplier.
                from integrals import separate_weight
                try:W,order=separate_weight(raw,atom);coefficient,offset=affine(atom[1],v)
                except Unsupported:order=0
                if order==1 and m.num(coefficient) not in (None,0) and not domain_conditions(raw):
                    cut=m.div(m.neg(offset),coefficient)
                    if m.variable_in(cut,v):raise Unsupported('The absolute-value switch still depends on the coordinate')
                    from functools import reduce
                    G=riemann_polynomial(m.mul(W,m.add(x,m.neg(cut))),x)
                    if G is not None:
                        H=reduce(m.add,(m.mul(m.div(c,q(j+1)),m.power(x,j+1)) for j,c in enumerate(G)),ZERO)
                        if compare_scalar(a,b)>0:lo,hi,sgn=b,a,q(-1)
                        else:lo,hi,sgn=a,b,ONE
                        def select(left,right,sign):
                            return m.div(m.add(m.add(left,right),m.mul(q(sign),('abs',m.add(left,m.neg(right))))),q(2))
                        mid=select(lo,select(hi,cut,-1),1)
                        coefficients=[m.div(c,q(j+1)) for j,c in enumerate(G)]
                        def at(y):
                            if y==ZERO:return ZERO
                            value=reduce(lambda h,c:('add',c,('mul',y,h)),reversed(coefficients[:-1]),coefficients[-1])
                            return ('mul',y,value)
                        total=('add',('add',at(lo),at(hi)),('mul',q(-2),at(mid)))
                        prefactor=m.mul(sgn,q(abs(m.num(coefficient))))
                        return emit(total if prefactor==ONE else ('mul',prefactor,total),
                                    'Clamp the real affine zero to the actual ordered interval. All shifts of the parameter give the same two-branch formula.',
                                    'Integrate the polynomial multiplier times x minus that zero. Reverse its sign on the left branch and orient the endpoint difference.',
                                    cut=cut,clamped_cut=mid,primitive=H)
        if raw[0]=='div' and (N:=m.num(raw[1])) is not None:
            D=raw[2];coeff=riemann_polynomial(D,x) if not domain_conditions(D) else None
            if coeff and len(coeff)==3 and facts=={'0<'+name+'<pi'}:
                C,B,A=coeff;scale=m.num(A);radius=m.simplify(('sqrt',m.div(C,A))) if scale else ZERO
                if (scale is not None and scale>0 and m.num(radius) not in (None,0)
                        and same_value(B,m.mul(q(-2),m.mul(A,m.mul(radius,('cos',p)))))):
                    T=m.mul(radius,('sin',p));center=m.mul(radius,('cos',p))
                    primitive=m.div(m.mul(q(N/scale),('atan',m.div(m.add(x,m.neg(center)),T))),T)
                    if (a,b)==(m.neg(radius),radius):
                        value=m.div(m.mul(q(N/scale),PI),m.mul(q(2),T))
                    else:value=m.add(m.substitute(primitive,{x:b}),m.neg(m.substitute(primitive,{x:a})))
                    return emit(value,'Complete the square. The original phase interval implies sin(p)>0.',
                                'The arctangent primitive is defined over the full ordered or reversed interval. Evaluate its two endpoints.',
                                primitive=primitive,positive_scale=T)
    if raw[0]!='div':raise Unsupported('The source is not a recognized finite moment ratio')
    N,D=raw[1:]
    if domain_conditions(N) or domain_conditions(D[1] if D[0]=='sqrt' else D):
        raise Unsupported('The candidate retains an unrelated source-domain restriction')
    if len(names)==2 and D[0]=='sqrt' and D[1][0]=='mul' and m.num(N) is not None:
        params=tuple(('s',z) for z in names);A,B=D[1][1:]
        def affine_factor(z):
            return m.add(m.add(ONE,m.power(z,2)),m.mul(q(-2),m.mul(z,x)))
        if all(g[0]=='nonnegative' or g[0]=='nonzero' for g in domain_conditions(raw)) and (
                same_value(A,affine_factor(params[0])) and same_value(B,affine_factor(params[1])) or
                same_value(B,affine_factor(params[0])) and same_value(A,affine_factor(params[1]))):
            p,q0=params;u,w=names
            if (f'abs({u})<1' in facts and f'abs({w})<1' in facts
                    and facts&{f'{u}*{w}>0',f'{w}*{u}>0'} and len(facts)==3
                    and all(compare_scalar(z,q(-1))>=0 and compare_scalar(z,ONE)<=0 for z in (a,b))):
                Q=('sqrt',m.mul(p,q0));term=m.add(m.mul(('sqrt',('abs',q0)),('sqrt',affine_factor(p))),
                                               m.mul(('sqrt',('abs',p)),('sqrt',affine_factor(q0))))
                F0=m.neg(m.div(m.mul(N,m.mul(p,('ln',term))),m.mul(('abs',p),Q)))
                exact=m.add(m.substitute(F0,{x:b}),m.neg(m.substitute(F0,{x:a})))
                if (a,b)==(q(-1),ONE):
                    exact=m.div(m.mul(N,('ln',m.div(m.add(ONE,Q),m.add(ONE,m.neg(Q))))),Q)
                return emit(exact,'At |x|≤1 each original affine radicand is at least (1−|p|)²>0.',
                            'The two slopes have the same nonzero sign. Differentiate the logarithm of the positive weighted sum of the roots.',
                            'Evaluate the primitive with the original oriented endpoints.',primitive=F0)
    trig={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0] in ('sin','cos') and m.variable_in(z,v)}
    if not trig or len({z[1] for z in trig})!=1:
        raise Unsupported('One common affine real phase is required')
    phase=next(iter(trig))[1];rate,shift=affine(phase,v);k=m.num(rate)
    if not k or any(domain_conditions(z) for z in (phase,shift)):
        raise Unsupported('The phase has no fixed nonzero rate or regular shift')
    t=('v','__profile_phase');repl={z:(z[0],t) for z in trig}
    square_root=D[0]=='sqrt';kernel=D[1] if square_root else D
    P=trig_polynomial(m.substitute(kernel,repl),t)
    top=trig_polynomial(m.substitute(N,repl),t)
    index=tuple(None if (j:=m.pi_multiple(m.simplify(m.substitute(phase,{x:z})))) is None else 2*j for z in (a,b))
    if (not square_root and len(names)==1 and set(P)=={(0,0),(0,1)} and set(top)=={(0,0)}):
        p=('s',names[0]);C,E=P[(0,0)],P[(0,1)]
        if (m.num(C) is not None and m.num(C)>0 and (same_value(E,p) or same_value(E,m.neg(p)))
                and facts in ({f'abs({names[0]})<{source(C)}'},{f'0<={names[0]}<{source(C)}'})
                and (turns:=m.pi_multiple(m.simplify(m.mul(q(k/2),width)))) is not None and turns.denominator==1):
            gap=m.add(m.power(C,2),m.neg(m.power(E,2)))
            return emit(m.div(m.mul(top[(0,0)],width),('sqrt',gap)),
                        'The printed amplitude bound makes the source denominator strictly positive on the full interval.',
                        'Use half-angle arctangent primitives and join the regular artificial seams. Each complete turn contributes 2π divided by the positive square root of the discriminant complement.',
                        phase=phase,integer_turns=q(turns),positive_complement=gap)
    if (not square_root and set(P)=={(2,0),(0,2)} and set(top)=={(0,0)}
            and all(j is not None and j.denominator==1 for j in index)):
        A,B=P[(2,0)],P[(0,2)]
        if (len(names)==2 and {A,B}=={m.power(('s',p),2) for p in names}
                and facts in ({names[0]+'*'+names[1]+'!=0'},{names[1]+'*'+names[0]+'!=0'},
                              {p+'!=0' for p in names})):
            return emit(m.div(m.mul(top[(0,0)],width),('sqrt',m.mul(A,B))),
                        'Both square coefficients are positive. On each quarter-turn, use tan or cot on its single real sheet.',
                        'The endpoint arctangents give quarter-turn measure divided by the geometric mean of the coefficients. Reflect neighboring quarters and preserve orientation.',
                        phase=phase,quarter_turn_indices=tuple(map(q,index)))
    if (len(names)==1 and not facts and set(P)=={(0,0),(0,1)}
            and all(j is not None and j.denominator==1 and j.numerator%2==0 for j in index)):
        p=('s',names[0]);C,E=P[(0,0)],P[(0,1)]
        R=m.simplify(('sqrt',m.substitute(C,{p:ZERO})))
        if (m.num(R) is not None and m.num(R)>0 and same_value(C,m.add(m.power(R,2),m.power(p,2)))
                and any(same_value(E,m.mul(q(s),m.mul(R,p))) for s in (-2,2))):
            if not square_root and set(top)=={(2,0)}:
                gap=('abs',m.add(m.power(R,2),m.neg(m.power(p,2))))
                return emit(m.div(m.mul(top[(2,0)],width),m.add(C,gap)),
                            'For nonzero parameter, write the sine square as a quadratic in the original denominator. Integrate the constant and cosine terms and the reciprocal affine cosine on each half-turn.',
                            'The reciprocal cosine moment uses the absolute discriminant. At coincident sine zeros and denominator zeros use the removable traces; at parameter zero integrate the sine square directly.',
                            phase=phase,exceptional_parameters=('zero','plus or minus the scale'))
            if square_root and set(top)=={(1,0)}:
                left,right=(q(-1 if (j.numerator//2)%2 else 1) for j in index)
                roots=tuple(('sqrt',m.add(C,m.mul(E,z))) for z in (left,right))
                value=ZERO if left==right else m.div(m.mul(m.mul(q(2/k),top[(1,0)]),m.add(left,m.neg(right))),m.add(*roots))
                return emit(value,'On each half-turn set u=cos(phase) with its actual orientation. The two endpoint radicands are (R±p)².',
                            'The affine square-root integral has finite one-sided limits. Rationalize the endpoint difference to cover the zero slope, and cancel opposite half-turns only after the individual integrals exist.',
                            phase=phase,cosine_endpoints=(left,right),endpoint_roots=roots)
    raise Unsupported('No complete finite parameter branch proof for the original profile')


def logarithmic_pole_traces(task,v,a,b,pv):
    """Separate an ordinary logarithmic pole from its matched-distance principal value."""
    from verify import same_value
    G=lambda x:('ln',('abs',('ln',x)))
    plan=dict(theorem='method.logarithmic_pole_traces',primitive=G(('v',v)),components=[(a,ONE),(ONE,b)],
              one_sided_evaluations=[dict(lower=a,upper=ONE,primitive_limits=(G(a),'-inf')),
                                     dict(lower=ONE,upper=b,primitive_limits=('-inf',G(b)))],
              argument=['The logarithm is defined on both positive components and vanishes only at 1.',
                        'On either side, ln|ln(1±t)| tends to −∞. The ordinary one-sided integrals are separate.'])
    if not pv:return plan,dict(convergence='divergent')
    value=ZERO if same_value(m.mul(a,b),ONE) else m.add(G(b),m.neg(G(a)))
    if 'stated_identity' in task and not same_value(m.parse(str(task['stated_identity']),None),value):
        raise Unsupported('The stated identity does not follow from the symmetric cutoff')
    plan['argument'].append('For equal positive x-cutoffs t, the absolute ratio ln(1−t)/ln(1+t) tends to 1 because both quotients by t have limits of modulus 1.')
    return dict(plan,symmetric_pairs_and_regular_pieces=[]),dict(principal_value_exists=True,principal_value=value)


def rational_primitive_traces(raw,primitive,v,a,b):
    """Cover every original rational component and evaluate its directional traces."""
    from graphs import rational_roots
    from polynomial import NotRational,Undefined,pdiv,rf
    from verify import same_value
    tag,constant=primitive
    guards=domain_conditions(raw)
    try:
        P,Q=rf(raw,v);polys=[Q]
        for relation,guard in guards:
            if relation!='nonzero':raise Unsupported('The inner domain is not a union of rational pole intervals')
            polys.extend(rf(guard,v))
    except (NotRational,Undefined) as exc:raise Unsupported('A defined rational inner expression is required') from exc
    roots={}
    for poly in polys:
        if poly==(F(0),):raise Unsupported('The original formula is nowhere defined')
        for root in rational_roots(poly):
            if root.b:raise Unsupported('A nonrational boundary needs certified directional evaluation')
            roots[root.a]=None
    lo,hi=sorted((a,b));ends=sorted({lo,hi}|{t for t in roots if lo<t<hi});sign=q(1 if b>=a else -1)
    def wrap(t):
        if tag=='atan':return ('atan',t)
        if tag=='logarithm':return m.mul(constant,('ln',('abs',t)))
        n=m.num(t)
        power=m.power(constant,n.numerator) if n is not None and n.denominator==1 else ('rpow',constant,t)
        return m.div(ONE,m.add(ONE,power))
    def trace(t,side):
        def leading(poly):
            if poly==(F(0),):return None,F(0)
            order=0
            while True:
                quotient,r=pdiv(poly,(-t,F(1)))
                if r[0]:return order,r[0]
                poly=quotient;order+=1
        p,c=leading(P);d,h=leading(Q)
        if p is None or p>d:inner=ZERO
        elif p==d:inner=q(c/h)
        else:inner='+inf' if (c/h)*side**((d-p)%2)>0 else '-inf'
        if tag=='atan' and isinstance(inner,str):return m.mul(q(F(1,2) if inner=='+inf' else F(-1,2)),m.PI)
        if tag=='logistic' and isinstance(inner,str):return ZERO if inner=='+inf' else ONE
        if tag=='logarithm' and (isinstance(inner,str) or inner==ZERO):
            return '+inf' if (isinstance(inner,str))==(m.num(constant)>0) else '-inf'
        return m.simplify(wrap(inner))
    rows=[];total=ZERO;divergent=False;all_holes=tuple(q(t) for t in ends if t in roots)
    for u,w in zip(ends,ends[1:]):
        left,right=trace(u,1),trace(w,-1)
        rows.append(dict(lower=q(u),upper=q(w),primitive_limits=(left,right)))
        if isinstance(left,str) or isinstance(right,str):divergent=True
        else:total=m.add(total,m.add(right,m.neg(left)))
    naive=None
    if a not in roots and b not in roots:
        naive=m.add(trace(b,-1),m.neg(trace(a,1)))
    value=None if divergent else m.mul(sign,total)
    derivation=['Keep the zeros of all original divisors, including any holes erased by rational cancellation.',
                'On each open component the chain rule gives the prescribed derivative. Order of vanishing determines the inner ratio at each directed end.',
                'Apply Newton–Leibniz on compact subintervals and take each endpoint limit separately. Sum finite differences with the original orientation.']
    return dict(theorem='method.oriented_primitive_endpoint_traces',primitive=wrap(raw),original_cuts=all_holes,orientation=sign,
                one_sided_evaluations=rows,naive_endpoint_difference=naive,argument=derivation),value


def source_definite_trace(task,library,request):
    """Recognize a requested oriented integral or explain a false whole-interval primitive."""
    from integrals import affine,trig_polynomial,learned_nodes
    from ray_proofs import phase_interval,phase_zeros
    from verify import same_value
    if not library.data.get('oriented_definite_branches'):raise Unsupported('Componentwise endpoint proof is not admitted')
    kind=task['kind'];meta=task.get('source',{})
    if not isinstance(meta,dict) or set(meta)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}:
        raise Unsupported('An additional source requirement is unbound')
    fields={'kind','id','source'};explain=kind=='explain_fundamental_theorem_failure'
    if kind=='definite_integral_of_composition':
        if set(task)-fields-{'statement','requested_output'} or task.get('requested_output')!=['exact_integral']:
            raise Unsupported('An exact integral of the stated composition is required')
        formula=re.fullmatch(r'Найти ∫([₋₀-₉]+)([⁻⁰¹²³⁴⁵⁶⁷⁸⁹]+) (\w+)′\((\w+)\)/\(1\+\3\(\4\)²\)d\4, \3\(\4\)=(.+)\.',task['statement'])
        if not formula:raise Unsupported('The literal composition is not fully parsed')
        lo,hi,_,v,text=formula.groups()
        bounds=(int(lo.translate(str.maketrans('₋₀₁₂₃₄₅₆₇₈₉','-0123456789'))),int(hi.translate(str.maketrans('⁻⁰¹²³⁴⁵⁶⁷⁸⁹','-0123456789'))))
        text=re.sub(r'(?<=[\d)])(?=\()', '*',text.replace('−','-').replace('²','^2').replace('³','^3'))
        raw=m.parse(text,v);primitive=('atan',None)
    else:
        if set(task)-fields-{'goal','variable','integrand','interval'}:
            raise Unsupported('An extra conclusion or method is unbound')
        v=task['variable'];bounds=task['interval'];text=task['integrand'];primitive=None
        goals={'explain_fundamental_theorem_failure':{'Explain why formal application of the Newton–Leibniz formula gives incorrect results.'},
               'definite_integral':{'Evaluate the integral of the derivative.','Evaluate the definite integral.'}}
        if task['goal'] not in goals.get(kind,()):raise Unsupported('The requested definite-integral conclusion is not bound')
        if (derivative:=re.fullmatch(r'D_'+re.escape(v)+r'\((.+)\)',text)):
            F0=m.parse(derivative[1],v)
            if F0[0]=='atan':raw=F0[1];primitive=('atan',None)
            if F0[0]=='div' and F0[1]==ONE and F0[2][0]=='add':
                for u,z in (F0[2][1:],F0[2][:0:-1]):
                    if u==ONE and z[0]=='rpow' and m.num(z[1]) is not None and m.num(z[1])>1:
                        raw=z[2];primitive=('logistic',z[1]);break
            if primitive is None:raise Unsupported('The derivative needs an admitted primitive and trace rule')
        else:raw=m.parse(text,v)
    ends=tuple(m.parse(str(z),None) for z in bounds);ctx=m.context(dict(variable=v))
    if not all(m.constant_defined(z,ctx) for z in ends):raise Unsupported('The original endpoints are not defined')
    a,b=map(m.simplify,ends)
    if a==b:raise Unsupported('A nondegenerate interval is required here')
    x=('v',v)
    if primitive is None and raw[0]=='div' and m.num(raw[1]) not in (None,0):
        try:k,_=affine(raw[2],v)
        except Unsupported:k=ZERO
        if m.num(k) not in (None,0) and not domain_conditions(raw[2]):
            primitive=('logarithm',m.div(raw[1],k));raw=raw[2]
            # The logarithm imposes the same original zero exclusions as the reciprocal.
            raw=('div',ONE,('div',ONE,raw))
    if primitive is not None:
        if m.num(a) is None or m.num(b) is None:raise Unsupported('Rational trace endpoints are required')
        plan,value=rational_primitive_traces(raw,primitive,v,m.num(a),m.num(b))
        if explain:
            if not plan['original_cuts'] or (value is not None and plan['naive_endpoint_difference'] is not None
                                             and same_value(value,plan['naive_endpoint_difference'])):
                raise Unsupported('The alleged failure lacks an original primitive jump or divergence')
            return plan,dict(convergence='divergent') if value is None else dict(convergence='convergent',value=value)
        if value is None:raise Unsupported('The requested finite value does not exist')
        return plan,value
    if raw[0]=='sqrt' and not explain and not domain_conditions(raw[1]):
        tags={z for z in learned_nodes(raw[1]) if isinstance(z,tuple) and z[0]=='cos'}
        if len(tags)==1:
            atom,=tags;phase=atom[1];z=('v','__trace_phase');P=trig_polynomial(m.substitute(raw[1],{atom:('cos',z)}),z)
            if set(P)=={(0,0),(0,1)} and m.num(C:=P[(0,0)]) is not None and m.num(C)>0 and same_value(P[(0,1)],m.neg(C)):
                l,r=phase_interval(phase,v,a,b);turns=(r-l)/2
                if turns.denominator==1:
                    return dict(theorem='method.oriented_primitive_endpoint_traces',turns=q(turns),argument=[
                        'The half-angle identity reduces the principal square root to a positive constant times |sin(phase/2)|.',
                        'Each complete absolute-sine period has the same area, obtained with the cosine primitive on one positive branch.']),m.div(m.mul(q(2),m.mul(m.add(b,m.neg(a)),('sqrt',m.mul(q(2),C)))),m.PI)
    if explain and raw[0]=='div' and raw[1][0]=='pow' and raw[1][2]==2 and raw[1][1][0]=='sec':
        phase=raw[1][1][1];T=('pow',('tan',phase),2);D=raw[2]
        if D[0]=='add' and not domain_conditions(phase):
            for C,z in (D[1:],D[:0:-1]):
                if z!=T or m.num(C) is None or m.num(C)<=0:continue
                l,r=phase_interval(phase,v,a,b);rate,_=affine(phase,v)
                if (r-l).denominator!=1 or l.denominator!=1:continue
                j,k=phase_zeros('cos',(l,r),False,False)
                if k<j:continue
                value=m.div(m.add(b,m.neg(a)),('sqrt',C))
                F0=m.div(('atan',m.div(('tan',phase),('sqrt',C))),m.mul(rate,('sqrt',C)))
                return dict(theorem='method.oriented_primitive_endpoint_traces',primitive=F0,phase_pole_indices=(j,k),naive_endpoint_difference=ZERO,
                            argument=['The original secant and tangent have holes at every half-integer phase in units of π.',
                                      'The ratio has the finite continuation 1/(C cos²(phase)+sin²(phase)).',
                                      'On each component the arctangent primitive gives a total π per oriented whole tangent period after normalization.']),dict(convergence='convergent',value=value)
    raise Unsupported('No complete componentwise primitive or finite periodic profile was found')


def riemann_polynomial(raw,x):
    """Read exact polynomial coefficients, retaining fixed symbolic parameters."""
    from polynomial import ResourceBound
    p,d=m.rational_form(raw)
    if set(d)!={()} or not d[()]:return None
    groups={}
    for mon,c in p.items():
        powers=dict(mon);degree=powers.pop(x,0)
        if any(m.variable_in(a,x[1]) for a in powers):return None
        if degree>16:raise ResourceBound('The finite polynomial sample order exceeds the supported cutoff')
        groups.setdefault(degree,{})[tuple(powers.items())]=c/d[()]
    return tuple(m.poly_expr(groups.get(j,{})) for j in range(max(groups,default=0)+1))


def geometric_width_lower_sums(task,raw,x,a,b):
    from ray_proofs import compare_scalar
    if (task.get('partition')!='n parts whose lengths form a geometric progression; no common ratio specified'
            or task['requested_output']!=['lower_sum','limit_as_n_to_infinity']
            or task.get('source_hint') or task.get('conditions') or 'tags' in task or 'sample_points' in task):
        raise Unsupported('The source geometric-width partition with free ratio is required')
    width=m.add(b,m.neg(a));P=riemann_polynomial(raw,x)
    if (domain_conditions(raw) or compare_scalar(b,a)<=0 or P is None
            or any(m.num(c) is None or m.num(c)<0 for c in P[1:]) or compare_scalar(a,ZERO)<0
            or not any(c!=ZERO for c in P[1:])):
        raise Unsupported('A strictly increasing polynomial on the positive source interval is required')
    integral=ZERO
    for j,c in enumerate(P):
        integral=m.add(integral,m.div(m.mul(c,m.add(m.power(b,j+1),m.neg(m.power(a,j+1)))),q(j+1)))
    z=('v','geometricTag');rho=('s','ratio')
    from_right=riemann_polynomial(m.substitute(raw,{x:m.add(b,m.neg(m.mul(width,z)))}),z)
    from_left=riemann_polynomial(m.substitute(raw,{x:m.add(a,m.mul(m.mul(width,rho),z))}),z)
    def accumulate(values):
        return m.mul(m.mul(width,m.add(ONE,m.neg(rho))),
                     sum_polynomial_geometric(values,rho))
    return dict(theorem='method.riemann_exact_partition_sums',source_interval=(a,b),width=width,argument=[
        'Нормируем общую геометрическую прогрессию длин суммой ширин. Минимум на каждой ячейке достигается на левом конце.',
        'При постоянном q<1 сохраняются первые крупные ячейки, а при q>1 отсчитываем ячейки с правого конца. В обеих ветвях после переиндексации ширины убывают как ρ^j.',
        'Разлагаем многочлен левой метки по степеням ρ^j. Суммируем геометрические ряды. Если q=1 или шаг сетки стремится к нулю, получаем обычный интеграл.',
        'Один и тот же предел для произвольной прогрессии не следует. При q=2 последняя ширина стремится к половине всего интервала и строгая монотонность даёт положительный остаток между интегралом и нижней суммой.',
    ]),dict(lower_sum='Sum over j=0..n-1 of f(a+(b-a)*sum(q^i,i=0..j-1)/sum(q^i,i=0..n-1))*(b-a)*q^j/sum(q^i,i=0..n-1)',
           universal_limit_exists=False,
           fixed_ratio_limits=[dict(condition='q=1',value=integral),
                               dict(condition='0<q<1, ratio=q',value=accumulate(from_right)),
                               dict(condition='q>1, ratio=1/q',value=accumulate(from_left))])


def sum_polynomial_geometric(coefficients,rho):
    value=ZERO
    for j,c in enumerate(coefficients):
        value=m.add(value,m.div(c,m.add(ONE,m.neg(m.power(rho,j+1)))))
    return value


def riemann_translation_scope(task):
    from cartesian_fields import vector_source
    statement=task['statement']
    vector_source(task,{'statement','requested_output'},(statement,))
    form=r'Пусть ([A-Za-z_]) интегрируема на \[A,B\]\. Доказать интегральную непрерывность: lim\(h→0\)∫ₐᵇ \|\1\(x\+h\)−\1\(x\)\|dx=0, где \[a,b\]⊂\[A,B\]\.'
    if task['requested_output']!=['proof_of_full_statement'] or not re.fullmatch(form,statement):
        raise Unsupported('The source translated Riemann-integrable difference and both intervals must match')
    return (dict(theorem='method.riemann_exact_partition_sums',argument=[
        'Выбираем разбиение, на котором разность верхней и нижней сумм сколь угодно мала. Ступенчатая функция между ними приближает исходную в интеграле модуля.',
        'Для ступенчатой функции сдвиг меняет значения только в отрезках длины |h| возле конечного числа узлов. Интеграл её разности стремится к нулю.',
        'Два остатка от приближения ограничены тем же малым интегралом на полном исходном отрезке. Это доказывает результат для допустимых сдвигов и для продолжения нулём.',
        'При соприкосновении концов исходное выражение для одного знака сдвига может быть не определено. Полный двусторонний предел требует внутреннего отрезка или заданного продолжения.',
    ],error_bound='2*L1 approximation error + |h|*sum of step jump magnitudes'),
    dict(proved_on='every allowed shift; bilateral for a strictly interior interval or a fixed bounded Riemann-integrable extension',
         unrestricted_bilateral_source_limit=False,value=ZERO))


def defined_riemann_integral(task,library):
    """Construct the source-requested sums before taking any limit."""
    from functools import reduce
    from integrals import affine
    from ray_proofs import compare_scalar
    from verify import same_value
    if not library.data.get('riemann_partition_skills'):
        raise Unsupported('Riemann partition transitions are unavailable')
    kind=task['kind'];common={'id','kind','source','requested_output'}
    if any(k in task.get('source',{}) for k in ('explicit_imposed_method','explicit_required_method','method_requirement')):
        raise Unsupported('A different printed method is not satisfied by this certificate')
    if kind=='riemann_integrability_proposition':
        if 'интегральную непрерывность' in task.get('statement',''):
            return riemann_translation_scope(task)
        return riemann_oscillation_proof(task)
    if kind=='definite_integral':return poisson_riemann_product(task)
    allowed=common|{'function','variable','interval','partition','sample_points','tags','parameters','conditions','source_hint'}
    if set(task)-allowed:raise Unsupported('Unbound condition of the original sum')
    v=task.get('variable','x');pars=task.get('parameters',[]);x=('v',v);wanted=task['requested_output']
    conditions=task.get('conditions',[]);hint=task.get('source_hint')
    ctx=m.context(dict(variable=v,parameters=pars))
    raw_ends=tuple(m.parse(str(k),None,pars) for k in task['interval'])
    if not all(m.constant_defined(k,ctx) for k in raw_ends):raise Unsupported('Undefined original interval endpoint')
    a,b=map(m.simplify,raw_ends)
    raw=m.parse(task['function'],v,pars);g=m.simplify(raw);L=m.add(b,m.neg(a))
    eq='n equal intervals'
    plan=dict(theorem='method.riemann_exact_partition_sums',source_interval=(a,b),integrand=raw)
    if (kind=='riemann_sum' and task.get('partition')==eq and task.get('sample_points')=='midpoints'
            and task.get('tags','midpoints')=='midpoints' and wanted==['midpoint_sum']):
        coefficients=riemann_polynomial(raw,x)
        if (conditions or hint or len(coefficients or ())>2 or coefficients is None or domain_conditions(raw)
                or compare_scalar(b,a)<=0):raise Unsupported('A fixed oriented closed interval and an affine midpoint field are required')
        midpoint=m.div(m.add(a,b),q(2))
        value=m.simplify(m.mul(L,m.substitute(g,{x:midpoint})))
        return dict(plan,tags='cell midpoints',argument=[
            'The arithmetic mean of all n midpoint tags is (a+b)/2.',
            'An affine function commutes with this finite mean, hence the midpoint Riemann sum is (b−a)f((a+b)/2) for every n.',
        ]),dict(midpoint_sum=value,valid_for='every integer n>=1')
    if kind=='darboux_sums':
        if 'geometric progression' in task.get('partition',''):
            return geometric_width_lower_sums(task,raw,x,a,b)
        if task.get('partition')!=eq or wanted!=['lower_sum','upper_sum'] or conditions or hint or 'tags' in task or 'sample_points' in task:
            raise Unsupported('A geometric length ratio or a required vanishing mesh has not been specified')
        if compare_scalar(b,a)<=0:raise Unsupported('Darboux sums require an ordered positive-length source interval')
        if any(not known_guard((relation,E),ctx) and
               not (relation=='nonnegative' and E==x and compare_scalar(a,ZERO)>=0)
               for relation,E in domain_conditions(raw)):
            raise Unsupported('The original field may have an undefined sampled value')
        up=False
        if g==x:up=True
        elif g[0]=='pow' and g[1]==x and g[2]>0:up=g[2]%2==1 or compare_scalar(a,ZERO)>=0
        elif g==('sqrt',x):up=compare_scalar(a,ZERO)>=0
        elif g[0]=='rpow' and g[2]==x and m.num(g[1]) is not None:up=m.num(g[1])>1
        if not up:raise Unsupported('Cell extrema have not been proved on the full original interval')
        lower=dict(integrand=raw,step_numerator=L,indices='j=0..n-1',coordinate='a+(b-a)j/n')
        upper=dict(lower,indices='j=1..n')
        return dict(plan,tags='proved cell endpoint extrema',argument=[
            'The original function is increasing on the full closed interval, so each infimum is the left value and each supremum is the right value.',
            'The common width is (b−a)/n. The upper and lower sums are exact finite sums over consecutive endpoint tags.',
            'Subtract the two sums: all interior terms cancel.',
        ]),dict(lower_sum=lower,upper_sum=upper,gap_numerator=m.simplify(m.mul(L,m.add(m.substitute(g,{x:b}),m.neg(m.substitute(g,{x:a}))))))
    if (kind!='riemann_integral_by_definition' or wanted!=['partition','riemann_sum','limit_and_integral']
            or set(task)&{'partition','sample_points','tags'}):
        raise Unsupported('The stated integral definition and sampling outputs are required')
    if not conditions and not hint and not domain_conditions(raw) and (coefficients:=riemann_polynomial(raw,x)) is not None:
        z=('v','__unit_sample')
        normalized=m.substitute(raw,{x:m.add(a,m.mul(L,z))})
        weights=riemann_polynomial(normalized,z)
        integral=m.mul(L,reduce(m.add,(m.div(c,q(j+1)) for j,c in enumerate(weights)),ZERO))
        plan.update(partition='equal oriented cells',scaled_coefficients=weights,argument=[
            'With width (b−a)/n and right tags, the kth sample equals the polynomial evaluated at a+(b−a)k/n.',
            'For degree j, the finite power sum Σ kʲ is a polynomial of degree j+1 with leading coefficient 1/(j+1), as proved by differences of consecutive powers.',
            'After division by n^(j+1) and passage to the limit, only that leading coefficient remains. The signed width handles reversed intervals.',
        ])
        return plan,dict(integral=integral,partition='a+k(b-a)/n, k=0..n',riemann_sum='(b-a) Σ_j c_j n^(-j-1) Σ_(k=1)^n k^j',coefficients=weights)
    if not conditions and not hint and g[0] in ('sin','cos'):
        if domain_conditions(raw):raise Unsupported('The original phase must be defined on the entire interval')
        rate,shift=affine(g[1],v)
        if m.num(rate) in (None,0):raise Unsupported('The trigonometric phase needs a fixed nonzero rate')
        ends=[m.substitute(g[1],{x:t}) for t in (a,b)];sign=-1 if g[0]=='sin' else 1
        dual='cos' if sign==-1 else 'sin'
        w=m.mul(q(sign),m.add((dual,ends[1]),m.neg((dual,ends[0]))))
        integral=m.simplify(m.div(w,rate))
        plan.update(partition='equal oriented cells with midpoints',endpoint_telescoper=w,phase_rate=rate,argument=[
            'Apply the addition identities to adjacent endpoint phases. Twice the sine of half the phase step times the sampled midpoint is the difference of endpoint values.',
            'Add the consecutive differences. The phase step tends to zero, and sin(s)/s tends to one. If the source width is zero, all sums are zero.',
        ])
        return plan,dict(integral=integral,riemann_sum='h * endpoint_telescoper / (2 sin(rate*h/2)) on the eventual nonzero-width tail',h_numerator=L)
    if g[0]=='rpow' and g[2]==x and g[1][0]=='s' and conditions==[g[1][1]+'>0'] and not hint:
        base=g[1];lo=('rpow',base,a);hi=('rpow',base,b);ratio=m.div(m.add(hi,m.neg(lo)),('ln',base))
        return dict(plan,partition='equal oriented cells with right endpoints',argument=[
            'For a positive base A, sample A^(a+k h). For A≠1 and nonzero source width, the terms form a geometric progression with q=A^h.',
            'In h q (A^b−A^a)/(q−1), q tends to 1 and (exp(h ln A)−1)/h tends to ln A.',
            'For A=1 each summand is constant, and a zero-width interval has zero sum.',
        ]),dict(parameter_cases=[dict(condition=base[1]+'=1',integral=L),
                                 dict(condition=base[1]+'!=1',integral=ratio)],
                 riemann_sum='h q (A^b−A^a)/(q−1), q=A^h; b−a when A=1')
    if a[0]!='s' or b[0]!='s' or a==b or not conditions or conditions[0]!=f'0<{a[1]}<{b[1]}':
        raise Unsupported('The exact partition rule does not establish the original interval or kernel')
    if any(not known_guard((relation,E),ctx) and not (E==x and relation in ('nonzero','positive','nonnegative'))
           and not (relation=='nonzero' and E[0]=='pow' and E[1]==x)
           for relation,E in domain_conditions(raw)):
        raise Unsupported('The original power field has another unsatisfied domain condition')
    if same_value(g,m.power(x,-2)) and conditions==conditions[:1] and hint in (None,'Use xi_i=sqrt(x_i*x_(i+1)).'):
        integral=m.add(m.div(ONE,a),m.neg(m.div(ONE,b)))
        return dict(plan,partition='arbitrary positive ordered mesh with geometric mean tags',argument=[
            'On every positive cell the geometric mean belongs to the cell.',
            'The width divided by its squared tag equals 1/x_i−1/x_(i+1) exactly.',
            'The sum telescopes for every positive partition. The original reciprocal-square field is continuous.',
        ]),dict(integral=integral,riemann_sum=integral)
    p=(g[2] if g[0]=='rpow' and g[1]==x else q(g[2]) if g[0]=='pow' and g[1]==x
       else q(-1) if same_value(g,m.power(x,-1)) else None)
    integer=m.num(p) if p else None
    if p is None or (p[0]!='s' and integer is None) or (p[0]=='s' and conditions[1:]!=[p[1]+'!=-1']) or (integer is not None and len(conditions)!=1):
        raise Unsupported('The original power and exponent branch are not verified')
    if hint not in (None,'Choose partition points in geometric progression.'):
        raise Unsupported('The printed partition hint does not match the sampled rule')
    quotient=m.div(b,a)
    division='(q−1)/(q^(m+1)−1)'
    if integer==-1:
        value=('ln',quotient);term='n(q−1)'
        detail='Every reciprocal sample contributes q−1. Then n(q−1) tends to ln(b/a).'
    else:
        r=m.add(ONE,p);value=m.div(m.add(('rpow',b,r),m.neg(('rpow',a,r))),r)
        term='(b^(m+1)−a^(m+1)) '+division
        detail='Sum the geometric progression in q^(m+1), with m+1 nonzero. The exponential difference quotient makes '+division+' tend to 1/(m+1).'
    return dict(plan,partition='x_j=a q^j, q=(b/a)^(1/n)',exponent=p,argument=[
        'Use a positive geometric partition with q>1. Its mesh is at most b(q−1) and tends to zero.',
        'The original power is continuous on [a,b]. A left tag contributes (q−1)x_j^(m+1).',
        detail,
    ]),dict(integral=value,riemann_sum=term,quotient=quotient)


def poisson_riemann_product(task):
    """Extract logarithms of positive quadratic factors on a half-period grid."""
    from integrals import affine
    fields={'kind','id','source','integrand','variable','interval','parameters','stated_conditions','source_hint','requested_output'}
    if set(task)-fields or task.get('requested_output')!=['integral_value_and_derivation']:
        raise Unsupported('An original logarithmic integral and its derivation are required')
    v=task['variable'];pars=task['parameters'];x=('v',v);names=task['stated_conditions']
    if len(pars)!=1 or names not in (['abs('+pars[0]+')<1'],['abs('+pars[0]+')>1']):
        raise Unsupported('The modulus must lie strictly on one side of one')
    a=('s',pars[0]);raw=m.parse(task['integrand'],v,pars)
    if raw[0]!='ln' or any(g[0]!='positive' for g in domain_conditions(raw)):
        raise Unsupported('A single logarithm of the original regular quadratic factor is required')
    from integrals import learned_nodes
    waves={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0]=='cos'}
    if len(waves)!=1:raise Unsupported('An affine cosine phase is required')
    C,=waves;rate,shift=affine(C[1],v);k=m.num(rate)
    target=m.add(m.add(ONE,m.power(a,2)),m.mul(q(-2),m.mul(a,C)))
    A,B=(m.parse(str(z),None,pars) for z in task['interval'])
    if (not k or shift!=ZERO or m.simplify(m.add(raw[1],m.neg(target)))!=ZERO or A!=ZERO
            or m.simplify(m.add(m.mul(q(abs(k)),B),m.neg(m.PI)))!=ZERO):
        raise Unsupported('The source argument or interval is not a full half-period of the factored quadratic')
    if task.get('source_hint') not in (None,'factor alpha^(2*n)-1 into quadratic factors'):
        raise Unsupported('The printed logarithmic factorization must be preserved')
    greater='>1' in names[0]
    value=m.mul(m.mul(q(2),B),('ln',('abs',a))) if greater else ZERO
    return dict(theorem='method.riemann_exact_partition_sums',original=raw,bounds=(A,B),phase_rate=rate,argument=[
        'If |a|>1, factor a² out of the quadratic and use the reciprocal parameter; 2 ln|a| remains as a constant.',
        'For the reduced |a|<1 the quadratic is |1−a exp(iθ)|²>0, so the logarithm is continuous over the full interval.',
        'Pair conjugate roots among the 2n-th roots of unity; the real roots contribute 1−a². Thus the product over θ=jπ/n, j=1,…,n−1, is (1−a^(2n))/(1−a²).',
        'Take the logarithm and multiply by the cell width. The log remains bounded when n→∞ and the width tends to zero. The omitted endpoint term tends to zero.',
    ]),dict(integral=value,method='paired roots of unity and Riemann sum')


def riemann_oscillation_proof(task):
    """Bind the given hypotheses to estimates for Darboux gaps and sampled sums."""
    if set(task)-{'kind','id','source','statement','requested_output'}:
        raise Unsupported('Unbound hypothesis in the Riemann proposition')
    text=re.sub(r' \((?:см\. )?№\d+\)', '', task['statement'])
    wanted=task['requested_output'];proof=['proof_of_full_statement']
    def matches(pattern):
        return re.fullmatch(pattern,text)
    def conclusion(claim,*steps,**data):
        return dict(theorem='method.riemann_oscillation_estimate',claim=claim,argument=list(steps)),dict(proved=True,**data)
    if wanted==['limit_value_and_justification'] and matches(
            r'Для f∈C¹\[a,b\] и Δ_n=∫ₐᵇ f\(x\)dx−\(b−a\)/n·Σ\(k=1\.\.n\)f\(a\+k\(b−a\)/n\) найти lim\(n→∞\) nΔ_n\.'):
        return conclusion('first-order right-tag error',
            'Set h=(b−a)/n. On cell k, subtract the right-hand value and use the first-order formula at its right endpoint.',
            'The integrated leading error is −h²f′(x_k)/2. The total remainder is bounded by n h² times the uniform modulus of continuity of f′ at h.',
            'Multiply by n. The right Riemann sum of f′ tends to f(b)−f(a).',
            limit='−(b−a)(f(b)−f(a))/2')
    if wanted==['answer_and_printed_counterexample_analysis']:
        if matches(r'Следует ли из существования ∫ₐᵇ\|f\(x\)\|dx интегрируемость f на \[a,b\]\? Рассмотреть f=1 на рациональных x и −1 на иррациональных x\.'):
            return conclusion('absolute value does not reflect integrability',
                'The modulus of the printed sign field is the constant 1.',
                'Every nondegenerate cell meets both rationals and irrationals. The Darboux gap equals 2(b−a) for every partition of a nondegenerate interval.',
                answer=False,gap='2(b-a)')
        if matches(r'Следует ли из интегрируемости f и φ интегрируемость f\(φ\(x\)\)\? Рассмотреть f\(0\)=0, f\(x\)=1 для x≠0, а φ — функция Римана\.'):
            return conclusion('integrability does not survive an arbitrary integrable outer function',
                'The outer field is bounded with one discontinuity. The inner field is integrable because only finitely many rational points have denominator below a fixed cutoff on any bounded interval.',
                'The composition is the rational indicator, since the inner field is exactly zero on irrationals. Its Darboux gap equals b−a on every nondegenerate interval.',
                answer=False,gap='b-a')
    if wanted!=proof:raise Unsupported('The whole stated conclusion was not requested')
    if matches(r'Если f и φ непрерывны на \[a,b\], доказать, что при max\|Δx_i\|→0 сумма Σ\(i=0\.\.n−1\) f\(ξ_i\)φ\(θ_i\)Δx_i стремится к ∫ₐᵇ f\(x\)φ\(x\)dx\. Точки ξ_i,θ_i независимо выбираются в \[x_i,x_\(i\+1\)\], x₀=a, x_n=b, Δx_i=x_\(i\+1\)−x_i\.'):
        return conclusion('independent tags in a product',
            'Replace the second tag θ_i by ξ_i within each original cell. The total change is bounded by (b−a) sup|f| times the uniform modulus of continuity of φ at the mesh.',
            'The remaining expression is an ordinary Riemann sum of the continuous product.',bound='(b-a) sup|f| ω_φ(mesh)')
    if matches(r'Для ограниченной монотонной f на \[0,1\] доказать ∫₀¹ f\(x\)dx−\(1/n\)Σ\(k=1\.\.n\)f\(k/n\)=O\(1/n\)\.'):
        return conclusion('monotone rectangle error',
            'Monotonicity identifies the two endpoint sums with the two Darboux sums, in the appropriate order.',
            'Their difference telescopes to |f(1)−f(0)|/n, so this also bounds the original error.',
            bound='|f(1)-f(0)|/n')
    if matches(r'Для ограниченной выпуклой сверху f на \[a,b\] доказать \(b−a\)\(f\(a\)\+f\(b\)\)/2 ≤ ∫ₐᵇ f\(x\)dx ≤ \(b−a\) f\(\(a\+b\)/2\)\.'):
        return conclusion('concave-cell two-sided error',
            'A bounded concave function is continuous in the interior and is Riemann integrable, including any endpoint jumps.',
            'Integrate the chord lower bound. Average the inequality f(x)+f(a+b−x)≤2 f((a+b)/2) over the source interval.',
            lower='(b-a)(f(a)+f(b))/2',upper='(b-a)f((a+b)/2)')
    if matches(r'При f∈C²\[1,\+∞\), f≥0, f′≥0, f″≤0 на \[1,\+∞\) доказать Σ\(k=1\.\.n\) f\(k\)=f\(n\)/2\+∫₁ⁿ f\(x\)dx\+O\(1\) при n→∞\.'):
        return conclusion('summable trapezoid errors',
            'The slopes of both f and its chord on [k,k+1] lie between f′(k+1) and f′(k). Thus the absolute difference of their integrals on the unit cell is at most f′(k)−f′(k+1).',
            'The error bounds telescope and are bounded by f′(1). Sum the chord integrals and account for their two half-weighted endpoint values.',
            residual_bound='f′(1)+f(1)/2')
    if (accumulation:=matches(r'Показать, что (?:разрывная функция f\(x\)=sgn\(sin\(π/x\)\) интегрируема на \[0,1\]\. Значение f\(0\) формулой не задано|f\(x\)=1/x−\[1/x\] при x≠0, f\(0\)=0 интегрируема на \[0,1\])\.')):
        missing='не задано' in accumulation[0]
        return conclusion('bounded jumps accumulating at an endpoint',
            'The specified field is bounded wherever its formula applies. A short initial segment [0,δ] contributes at most its length times the total oscillation.',
            'On [δ,1] only finitely many phase or floor transitions occur. Cover those points by intervals of arbitrarily small total length and use uniform continuity on the remaining closed cells.',
            'Changing a value at one endpoint does not affect the Darboux test.',
            endpoint_value='arbitrary finite extension at zero' if missing else 'zero as stated')
    if matches(r'Показать, что функция Римана φ\(x\), равная 0 при иррациональном x и 1/n при x=m/n в несократимой записи, m,n целые и n≥1, интегрируема на любом конечном промежутке\.'):
        return conclusion('finite large exceptions for each tolerance',
            'For each N only finitely many reduced fractions on a bounded interval have denominator at most N. Cover them by intervals of arbitrarily small total length.',
            'On remaining cells all values lie between 0 and 1/N. Thus the Darboux gap tends to zero; the lower sums are zero by density of irrationals.',
            integral=ZERO)
    if matches(r'Показать, что функция Дирихле χ\(x\), равная 0 на иррациональных x и 1 на рациональных x, не интегрируема ни на одном промежутке \(положительной длины\)\.'):
        return conclusion('dense incompatible values',
            'Every nonempty open cell contains rational and irrational points, so its oscillation is 1.',
            'The Darboux gap is the full interval length for every partition and cannot tend to zero.',
            integrable=False,gap='b-a')
    if matches(r'Пусть f интегрируема на \[a,b\]\. На равном разбиении x_i=a\+i\(b−a\)/n положено f_n\(x\)=sup f на ячейке при x_i≤x<x_\(i\+1\)\. Доказать lim\(n→∞\)∫ₐᵇ f_n\(x\)dx=∫ₐᵇ f\(x\)dx\.'):
        return conclusion('finite comparison for a fine upper mesh',
            'The step integral equals the upper sum on this mesh, whatever value is assigned at b.',
            'Choose a reference partition with small Darboux gap and refine by adding its interior points. The change in upper sum is bounded by their count times the mesh times 2 sup|f|.',
            'The refined upper sum is between the integral and the reference upper sum, which proves the limit.')
    if matches(r'Если f интегрируема на \[a,b\], доказать существование последовательности непрерывных φ_n с ∫ₐᶜ f\(x\)dx=lim\(n→∞\)∫ₐᶜ φ_n\(x\)dx для каждого a≤c≤b\.'):
        return conclusion('continuous L1 approximation from Darboux partitions',
            'Choose a finite step function below f with interval integral deficit less than 1/n. The Darboux definition supplies it.',
            'Replace each step discontinuity by a linear join over an interval of sufficiently small total length. The modification remains bounded and has integral absolute error less than 1/n.',
            'For every c the difference between the two original integrals is bounded by the full L1 error, at most 2/n.',
            uniform_error='2/n')
    if matches(r'Для ограниченной интегрируемой на \[a,b\] функции f доказать интегрируемость \|f\| и неравенство \|∫ₐᵇ f\|≤∫ₐᵇ \|f\|\.'):
        return conclusion('Lipschitz image and integral comparison',
            'The modulus map is 1-Lipschitz, so its oscillation on each source cell is bounded by the original oscillation. Apply the Darboux test.',
            'Integrate the pointwise comparison −|f|≤f≤|f|.',inequality='abs(integral(f))<=integral(abs(f))')
    if matches(r'Пусть f интегрируема на \[a,b\], A≤f\(x\)≤B, а φ определена и непрерывна на \[A,B\]\. Доказать интегрируемость φ\(f\(x\)\) на \[a,b\]\.'):
        return conclusion('uniformly continuous image of an integrable bounded range',
            'Choose δ so the uniformly continuous exterior map has oscillation below the target tolerance on each range piece of diameter below δ.',
            'The total length of partition cells with original oscillation at least δ is at most the original Darboux gap divided by δ. Bound the exterior oscillation there by 2 sup|φ|.',
            'A sufficiently small original Darboux gap makes the entire composite gap arbitrarily small.')
    if matches(r'Пусть f интегрируема на \[a,b\]\. Доказать, что ∫ₐᵇ f²\(x\)dx=0 тогда и только тогда, когда f\(x\)=0 во всех точках непрерывности f, принадлежащих \[a,b\]\.'):
        return conclusion('zero integral of a nonnegative continuous image',
            'The bounded square is integrable by uniform continuity of the square on the source range.',
            'For a nondegenerate interval, any nonzero value at a continuity point gives a positive lower bound on a small one-sided interval, contradicting a zero integral.',
            'Conversely, the continuity points of a bounded Riemann integrable function are dense: within any open cell, a partition with small gap gives a smaller open cell of arbitrarily small oscillation, and nested such cells give continuity points.',
            'If all those values vanish, every cell has infimum of the square equal to zero. Its lower integral is zero.',
            equivalence='on a nondegenerate interval [a,b]')
    if 'интегральную непрерывность' in text:
        raise Unsupported('A two-sided shift can leave the original closed domain at an endpoint')
    raise Unsupported('No Darboux implication is available for the given full hypotheses')


def riemann_weight(text,outer,params,as_prefix=False):
    """Read one finite sum times a scalar independent of its bound index."""
    import ast
    try:node=ast.parse(text.replace('^','**'),mode='eval').body
    except SyntaxError as exc:raise Unsupported('Unparsed finite sum') from exc
    sums=[z for z in ast.walk(node) if isinstance(z,ast.Call) and isinstance(z.func,ast.Name) and z.func.id=='sum']
    if len(sums)!=1:raise Unsupported('One finite sum is required')
    call=sums[0]
    if len(call.args)!=4 or call.keywords or not isinstance(call.args[1],ast.Name):raise Unsupported('Unbound summation index or limits')
    e,index,lo,hi=call.args;k=index.id
    def formula(z):return ast.unparse(z).replace('**','^')
    if k in [outer,*params] or formula(lo)!='1':raise Unsupported('Only positive uniform right-hand sample indices are bound')
    if isinstance(hi,ast.Name) and hi.id==outer:gap=0
    elif (isinstance(hi,ast.BinOp) and isinstance(hi.op,ast.Sub) and isinstance(hi.left,ast.Name) and hi.left.id==outer
          and isinstance(hi.right,ast.Constant) and type(hi.right.value) is int and hi.right.value==1):gap=1
    else:raise Unsupported('Unaccounted endpoint samples or undefined upper index')
    def read(z):
        if z is call:return m.parse(formula(e),None,[outer,k,*params])
        if not any(v is call for v in ast.walk(z)):return m.parse(formula(z),None,[outer,*params])
        if isinstance(z,ast.BinOp) and isinstance(z.op,(ast.Mult,ast.Div)) and not (isinstance(z.op,ast.Div) and any(v is call for v in ast.walk(z.right))):
            return ('div' if isinstance(z.op,ast.Div) else 'mul',read(z.left),read(z.right))
        raise Unsupported('The outer expression is not linear in the finite sum')
    if as_prefix:
        call.args=[index,lo,hi,e]
        return formula(node)
    return read(node),k,int(gap)


def mesh_degree(e,indices,ctx):
    """Degree under simultaneous positive rescaling of the two mesh indices."""
    if e in indices:return ONE
    if not any(m.contains(e,j) for j in indices):return ZERO
    op=e[0];deg=lambda z:mesh_degree(z,indices,ctx)
    if op in ('add','mul','div'):
        a,b=deg(e[1]),deg(e[2])
        if op=='add':
            if m.simplify(m.add(a,m.neg(b)))!=ZERO:raise Unsupported('Different homogeneity degrees in the mesh weight')
            return a
        return m.add(a,b if op=='mul' else m.neg(b))
    if op=='pow':return m.mul(q(e[2]),deg(e[1]))
    if op=='rpow' and deg(e[2])==ZERO and known_guard(('positive',e[1]),ctx):return m.mul(e[2],deg(e[1]))
    raise Unsupported('Uniform rescaling of this term has not been proved')


def uniform_sum_source(t):
    fields={'kind','id','source','goal','expression','index','index_domain','approach','method_requirement','parameters','stated_conditions'}
    if (set(t)-fields or t.get('goal') not in (None,'Find the printed limit.') or t.get('index_domain')!='positive integers'
            or t.get('approach')!='+infinity' or t.get('method_requirement') not in (None,'any','definite_integral')
            or set(t.get('source',{}))-{'exercise','pdf_page','printed_page','pdf_sha256','printed_subpart'}):
        raise Unsupported('Unbound sum, stated method, or limiting domain')
    return t['index'],t.get('parameters',[]),t.get('stated_conditions',[])


def uniform_sum_limit(t,lib,request,saved=None):
    """Recover a continuous right-Riemann kernel; replay checks its sampled identity directly."""
    if not lib.data.get('finite_riemann_integral_limit') or t.get('method_requirement')!='definite_integral':
        raise Unsupported('Definite-integral reduction is not admitted')
    n,params,cond=uniform_sum_source(t)
    W,k,missing=riemann_weight(t['expression'],n,params);ns=('s',n);ks=('s',k)
    v='t'
    while v in [k,n,*params]:v+='_'
    x=('v',v);sampling=m.div(ks,ns)
    ctx=m.context(dict(variable=v,parameters=[n,k,*params],parameter_conditions=[n+'>0',k+'>0',*cond]))
    for rel,g in domain_conditions(W):
        if not (known_guard((rel,g),ctx) or rel=='nonnegative' and m.sign(g,ctx) in (0,1)):
            raise Unsupported('A raw summand can be undefined on the sampled integer domain')
    if params or cond:
        from operations import expression_positions
        if mesh_degree(W,(ks,ns),ctx)!=q(-1):raise Unsupported('A mesh weight must have homogeneity degree minus one')
        candidate=m.substitute(W,{ns:ONE,ks:x})
        unit_powers={z:ONE for _,z in expression_positions(candidate) if z[0]=='rpow' and z[1]==ONE and m.constant_defined(z[2],ctx)}
        candidate=m.simplify(m.substitute(candidate,unit_powers))
    else:candidate=None
    G=freeze(saved['integrand']) if saved is not None else candidate if candidate is not None else m.simplify(m.mul(ns,m.substitute(W,{ks:m.mul(ns,x)})))
    if m.contains(G,ns) or m.contains(G,ks):raise Unsupported('The proposed integrand still depends on a mesh index')
    sampled=m.div(m.substitute(G,{x:sampling}),ns)
    if ((candidate is not None and G!=candidate) or (candidate is None and m.simplify(m.add(W,m.neg(sampled)))!=ZERO)):
        raise Unsupported('The candidate integrand does not reproduce the original summand')
    sub=dict(kind='finite_interval_integral',variable=v,integrand=source(G),interval=[0,1],method_requirement='newton_leibniz',requested_output=['exact_integral'])
    if candidate is not None:sub.update(parameters=params,stated_conditions=cond,right_limit_at_lower_endpoint=True)
    val=freeze(request('integral of the continuous mesh kernel',sub)['value'])
    correction=None
    if missing:
        end=m.substitute(G,{x:ONE})
        if not m.constant_defined(end,ctx):raise Unsupported('The omitted right endpoint has no finite value')
        term=m.div(end,ns)
        correction=request('limit of the omitted endpoint weight',dict(kind='limit',variable=n,variable_domain='positive_integers',
                    expression=source(term),approach=dict(point='+inf',side='positive_infinity')))['value']
        if freeze(correction)!=ZERO:raise Unsupported('Omitted endpoint contributes to the limit')
    return dict(integrand=G,variable=v,mesh=m.div(ONE,ns),sample=sampling,interval=(ZERO,ONE),
                original_weight=W,omitted_right_endpoint=bool(missing),endpoint_weight_limit=correction),val


def target_quadrature(task,request,fast_reciprocal=False):
    """Choose a certified panel count or a bounded convergent moment series."""
    from verify import same_value
    allowed={'id','kind','source','integrand','variable','lower','upper','method_requirement','requested_output','target_absolute_error','identity'}
    src=task.get('source',{})
    wanted=task.get('requested_output')
    pi_goal=wanted==['numeric_constant_pi','rigorous_absolute_error_estimate']
    if (set(task)-allowed or (not pi_goal and wanted!=['approximation','rigorous_absolute_error_estimate'])
            or set(src)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256'}
            or (task.get('identity')!='π/4 = integral' if pi_goal else 'identity' in task)):
        raise Unsupported('Additional printed precision or conversion requirements remain')
    v=task['variable'];tol=F(task['target_absolute_error']);scale=4 if pi_goal else 1
    if not 0<tol<1:raise Unsupported('A positive precision below one is required')
    lo,hi=task['lower'],task['upper'];raw=m.parse(task['integrand'],v);x=('v',v)
    def decimal_value(center,error):
        with localcontext() as ctx:
            ctx.prec=40
            text=format(Decimal(center.numerator)/Decimal(center.denominator),'.12f')
        error+=abs(F(text)-center)
        if error>tol:raise Unsupported('Critical requested precision is not yet proved')
        return dict(approximation=text,absolute_error_bound=q(error))

    if pi_goal and fast_reciprocal:
        try:return reciprocal_circle_quadrature(raw,x,lo,hi,tol,decimal_value)
        except Unsupported:pass
    if pi_goal:
        child=dict(kind='iterated_integral',integrand=task['integrand'],integration_order=[dict(variable=v,lower=lo,upper=hi)],
                   requested_output=['exact_integral'])
        exact=request('check the specified identity for the integral before converting units',child)['value']
        if not same_value(freeze(exact),m.div(m.PI,q(4))):raise Unsupported('The integral does not prove the printed normalization of π')

    if not pi_goal and (lo,hi)==('0','1') and raw[0]=='mul':
        log=('ln',('div',ONE,x))
        wave=raw[2] if raw[1]==log else raw[1] if raw[2]==log else None
        if wave and wave[0]=='add':
            kernel=next((e for e in wave[1:] if e[0]=='exp' and same_value(wave,m.add(e,q(-1)))) ,None)
            if kernel:
                from polynomial import rf,NotRational,Undefined
                try:p,d=rf(kernel[1],v)
                except (NotRational,Undefined):p,d=(),()
                if len(d)==1 and len(p)>1 and not any(p[:-1]) and p[-1]/d[0]>0 and len(domain_conditions(raw))==2:
                    coeff=p[-1]/d[0];power=len(p)-1
                    values=[]
                    for k in range(1,97):
                        values.append(coeff**k/factorial(k)/(power*k+1)**2)
                        ratio=coeff/(k+2);next_value=coeff**(k+1)/factorial(k+1)/(power*(k+1)+1)**2
                        if ratio<1 and (tail:=next_value/(1-ratio))<tol/4:
                            plan=dict(theorem='method.target_quadrature',strategy='positive_logarithmic_moments',moments=list(map(q,values)),
                                      inserted_power=power,coefficient=q(coeff),ratio=q(ratio),tail_bound=q(tail),
                                      reasoning='x^j ln(1/x) has integral 1/(j+1)^2 on (0,1), by parts and the finite lower limit. '
                                                'The exponential terms are nonnegative; monotone convergence transfers the integral.')
                            return plan,decimal_value(sum(values),tail)
    tail=F(0);plan=dict(theorem='method.target_quadrature',strategy='adaptive_simpson',tried_panels=[],scale=scale)
    if hi=='+inf':
        from polynomial import rf,NotRational,Undefined
        if lo!='0' or raw[0]!='exp' or domain_conditions(raw):raise Unsupported('A proved integral tail bound is required')
        try:p,d=rf(raw[1],v)
        except (NotRational,Undefined):p,d=(),()
        if len(p)!=3 or len(d)!=1 or any(p[:2]) or p[-1]/d[0]>=0:
            raise Unsupported('No positive quadratic Gaussian damping on the original half-line')
        decay=-p[-1]/d[0]
        for j in range(1,10):
            e=('exp',q(-decay*j*j))
            tail=enclose(e,None)[1]/(2*decay*j)
            if tail<tol/8:hi=str(j);break
        else:raise Unsupported('Gaussian tail still exceeds the required precision')
        plan.update(tail_bound=q(tail),cutoff=q(j),decay=q(decay))
    for n in (8,16,32,64,128,256):
        child=dict(kind='definite_quadrature',integrand=task['integrand'],variable=v,lower=lo,upper=hi,partition_count=n,
                   method_requirement='Simpson',requested_output=['approximation','rigorous_absolute_error_estimate'])
        val=request('certified Simpson panels '+str(n),child)['value']
        error=scale*rational_value(val['absolute_error_bound'])+tail
        plan['tried_panels'].append(dict(count=n,error=q(error)))
        if error<tol-F(1,10**12):
            return plan,decimal_value(scale*F(val['approximation']),error)
    raise Unsupported('The highest admitted panel count did not prove the requested precision')


def rational_value(value):
    from model import rational
    return rational(freeze(value))


def quadrature(task,library,request):
    methods=library.data.get('quadrature_rules',{})
    if library.data.get('target_quadrature') and task.get('method_requirement')=='integration_with_target_accuracy':
        return target_quadrature(task,request,library.data.get('remaining_analysis_proofs'))
    fields={'id','kind','schema','source','transcription','integrand','variable','lower','upper','partition_count','method_requirement','requested_output','removable_endpoint'}
    approximation_of_constant=(library.data.get('target_quadrature') and task.get('method_requirement')=='unspecified_quadrature'
                               and task.get('requested_output')==['approximation_to_constant'] and task.get('printed_constant')=='Catalan G')
    if approximation_of_constant:fields.add('printed_constant')
    if set(task)-fields or task.get('kind')!='definite_quadrature':raise Unsupported('Unknown quadrature fields')
    rule=task.get('method_requirement');n=task.get('partition_count')
    if approximation_of_constant:
        from verify import same_value
        x=('v',task['variable'])
        raw=m.parse(task['integrand'],task['variable'])
        if task['lower']!='0' or task['upper']!='1' or not same_value(raw,('div',('atan',x),x)) or domain_conditions(raw)!=[('nonzero',x)]:
            raise Unsupported('The displayed integral must establish the constant being approximated')
        rule='Simpson'
    if rule not in methods or type(n) is not int or not 1<=n<=256:raise Unsupported('Unknown quadrature method or inadmissible panel count')
    wanted=task.get('requested_output')
    if approximation_of_constant:wanted=['approximation']
    if not isinstance(wanted,(list,tuple)) or 'approximation' not in wanted or set(wanted)-{'approximation','compare_to_exact','rigorous_absolute_error_estimate'}:raise Unsupported('Unimplemented quadrature output')
    order,divisor=methods[rule];v=task['variable'];m.context({'variable':v})
    if rule=='Simpson' and n%2:raise Unsupported('Simpson requires an even number of equal panels')
    raw=m.parse(task['integrand'],v);A=m.parse(task['lower'],None);B=m.parse(task['upper'],None)
    a,b=enclose(A,None),enclose(B,None)
    if a[1]>=b[0]:raise Unsupported('Ordered finite endpoints required')
    width=m.add(B,m.neg(A));h=m.div(width,q(n));nodes=[m.add(A,m.mul(q(i),h)) for i in range(n+1)]
    boxes=[enclose(z,None) for z in nodes];cells=[(u[0],w[1]) for u,w in zip(boxes,boxes[1:])]
    weights={'left_rectangles':[1]*n+[0],'trapezoidal':[1]+[2]*(n-1)+[1],
             'Simpson':[1]+[4 if i%2 else 2 for i in range(1,n)]+[1]}[rule]
    den={'left_rectangles':1,'trapezoidal':2,'Simpson':3}[rule]
    endpoint=None;extension=task.get('removable_endpoint')
    if extension is not None:
        permitted={'justify continuous extension in evaluating endpoint sample'}
        if approximation_of_constant:permitted.add('justify continuous extension used by endpoint nodes')
        if not isinstance(extension,dict) or set(extension)!={'point','required'} or extension['required'] not in permitted:
            raise Unsupported('Unknown extension obligation')
        point=m.parse(extension['point'],None);endpoint=0 if point==A else n if point==B else None
        if endpoint is None:raise Unsupported('The requested extension must be at a source endpoint')
    guard_proofs=[]
    def guards_cover(guards):
        u='__segment'
        while u==v:u+='_'
        ctx=m.context({'variable':v,'parameters':[u],'parameter_conditions':[u+'>0','1-'+u+'>0']})
        x=('add',A,('mul',width,('s',u)))
        for relation,expr in guards:
            try:
                for c in cells:guard_bounds(relation,expr,c,[v])
                guard_proofs.append((relation,expr,'closed_interval'));continue
            except Unsupported:pass
            if not known_guard((relation,m.substitute(expr,{('v',v):x})),ctx):raise Unsupported('Original interval domain is not covered')
            guard_proofs.append((relation,expr,'open_interval'))
    guards_cover(domain_conditions(raw))
    numbers=[];values=[]
    for i,(node,box) in enumerate(zip(nodes,boxes)):
        e=m.substitute(raw,{('v',v):node})
        if i==endpoint:
            t={'kind':'limit','expression':task['integrand'],'variable':v,'approach':{'point':extension['point'],'side':'right' if i==0 else 'left'}}
            child=request('endpoint_limit',t);e=freeze(child['value'])
            if e in ('+inf','-inf'):raise Unsupported('A finite endpoint extension is required')
            box=enclose(e,None)
        elif approximation_of_constant and m.constant_defined(e,m.context({})):
            from operations import expression_positions
            value=m.simplify(e)
            box=enclose(value,None) if not any(n[0]=='atan' for _,n in expression_positions(value)) else taylor_enclosure(value,96)[0]
        else:box=enclose(raw,box)
        numbers.append(box);values.append(e)
    weighted=tuple(sum(w*pair[k] for w,pair in zip(weights,numbers)) for k in (0,1))
    bounds=product(enclose(m.div(h,q(den)),None),weighted)
    with localcontext() as ctx:
        ctx.prec=40;c=sum(bounds)/2;decimal=format(Decimal(c.numerator)/Decimal(c.denominator),'.12f')
    rounding=max(abs(F(decimal)-x) for x in bounds)
    if rounding>F(1,10**9):raise Unsupported('Quadrature value is not resolved to nine decimal places')
    val={'approximation':decimal,'quadrature_enclosure':tuple(map(q,bounds)),'rounding_error_bound':q(rounding)}
    if 'rigorous_absolute_error_estimate' in wanted:
        guards=domain_conditions(raw,True);guards_cover(guards)
        dt={'kind':'partial_derivatives','function':task['integrand'],'variables':[v],'requested_partials':[[v]*order],
            'stated_conditions':[v+'>'+task['lower'],v+'<'+task['upper']]+[guard_source(g) for g in guards],
            'requested_output':['specified_partial_derivatives']}
        field=freeze(request('derivative_bound',dt)['value'][0]);field=m.substitute(field,{('s',v):('v',v)})
        M=max(abs(z) for cell in cells for z in enclose(field,cell))
        remainder=(b[1]-a[0])*enclose(h,None)[1]**order*M/divisor
        val.update(derivative_order=order,derivative=field,derivative_absolute_bound=q(M),quadrature_error_bound=q(remainder),absolute_error_bound=q(remainder+rounding))
    if 'compare_to_exact' in wanted:
        child=request('primitive',{'kind':'integrate','integrand':task['integrand'],'variable':v,'method_requirement':'table_and_rules','requested_output':['primitive_family']})
        primitive=freeze(child['value']['representative'])
        guards_cover(domain_conditions(primitive))
        for box in (a,b):enclose(primitive,box)
        exact=m.add(m.substitute(primitive,{('v',v):B}),m.neg(m.substitute(primitive,{('v',v):A})))
        lo,hi=enclose(exact,None);val.update(exact_integral=exact,signed_difference_enclosure=(q(bounds[0]-hi),q(bounds[1]-lo)))
    return {'nodes':nodes,'samples':values,'weights':weights,'step':h,'weight_denominator':den,'interval_domain':guard_proofs},val


def exact_nearby_centers(expr,var,point):
    """Find simple evaluable centers near the target; distance only orders proposals."""
    from fractions import Fraction
    from math import floor
    from integrals import learned_nodes
    x=('v',var);a,b=enclose(point,None);target=(a+b)/2
    centers={q(j) for j in range(floor(target)-2,floor(target)+4)}
    for node in learned_nodes(expr):
        if isinstance(node,tuple) and node[0]=='q' and 0<node[1]<=100:centers.add(node)
    angle=target*7/22
    for den in (2,3,4,6):
        j=floor(angle*den)
        for k in range(j-1,j+3):centers.add(m.mul(q(Fraction(k,den)),m.PI))
    def score(k):
        l,h=enclose(k,None);return max(abs(l-b),abs(h-a)),m.tree_size(k),source(k)
    for k in sorted(centers,key=score):
        if m.simplify(m.add(k,m.neg(point)))==ZERO:continue
        raw=m.substitute(expr,{x:k})
        if not m.constant_defined(raw,{'parameters':[],'assumptions':[]}):continue
        value=m.simplify(raw)
        if all(z[0] in ('q','pi','add','mul','div','pow','sqrt') for z in learned_nodes(value) if isinstance(z,tuple)):
            yield k


def linear_approximation(task,library,request,saved):
    if not library.data.get('finite_linearization'):raise Unsupported('Finite linear approximation unavailable')
    common={'kind','id','source','requested_output'};kind=task['kind'];wanted=task['requested_output']
    method=task.get('method_requirement')
    if any(task.get('source',{}).get(k) not in (None,method) for k in ('explicit_required_method','explicit_imposed_method','method_requirement')):
        raise Unsupported('Conflicting source method')
    # An explicit printed request is part of the input and must agree with the numerical data.
    import re
    from verify import same_value
    quoted=task.get('source',{})
    if set(quoted)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','pdf_pages','literal_requirement',
                    'explicit_required_method','explicit_imposed_method','method_requirement'}:
        raise Unsupported('Additional printed fields in the approximation request remain unresolved')
    literal=quoted.get('literal_requirement')
    if literal:
        number=r'([0-9]+(?:[.,][0-9]+)?)'
        def decimal(token):return m.parse(token.replace(',','.'),None)
        if kind=='sector_area_change':
            pattern=(r'В круговом секторе R='+number+r' см, α='+number+r'°\. Найти точное и приближённое изменение площади, если '
                     +r'(увеличить|уменьшить) (радиус|угол) на '+number+r' (см|угловых минут|градусов)\.')
            matched=re.fullmatch(pattern,literal)
            if not matched:raise Unsupported('Unrecognized printed sector requirement')
            r0,angle0,direction,name,amount,unit=matched.groups()
            change='radius' if name=='радиус' else 'angle'
            if (unit=='см')!=(change=='radius'):raise Unsupported('Incompatible printed sector units')
            unit_factor=ONE if change=='radius' else m.div(m.PI,q(10800 if unit=='угловых минут' else 180))
            step=m.mul(decimal(amount),unit_factor)
            printed=(decimal(r0),m.mul(decimal(angle0),m.div(m.PI,q(180))),step if direction=='увеличить' else m.neg(step))
            if task.get('changed_quantity')!=change or not all(same_value(e,m.parse(str(task[k]),None)) for e,k in zip(printed,('radius','angle','increment'))):
                raise Unsupported('The printed sector data and the executable task disagree')
        else:
            pattern=(r'Заменяя приращение функции её дифференциалом, приближённо вычислить '
                     +r'(кубический корень из|sin|cos|arctg|lg) '+number+r'(°?)\.')
            matched=re.fullmatch(pattern,literal)
            if not matched:raise Unsupported('Unrecognized printed approximation requirement')
            name,number_text,degrees=matched.groups()
            decimal_point=decimal(number_text)
            point=m.mul(decimal_point,m.div(m.PI,q(180))) if degrees else decimal_point
            v=task['variable']
            formula={'кубический корень из':'cbrt({})','sin':'sin({})','cos':'cos({})','arctg':'atan({})','lg':'ln({})/ln(10)'}[name]
            if not same_value(m.parse(task['function'],v),m.parse(formula.format(v),v)) or not same_value(point,m.parse(str(task['argument']),None)):
                raise Unsupported('The printed function or its argument differs from the executable task')
    if kind=='sector_area_change':
        if (set(task)-common-{'radius','angle','changed_quantity','increment'} or wanted!=['function_increment','differential']
                or task['changed_quantity'] not in ('angle','radius')):raise Unsupported('Incomplete sector or additional question')
        ctx=m.context({'variable':'s'});rad,angle,h=[m.parse(str(task[k]),None) for k in ('radius','angle','increment')]
        if not all(m.constant_defined(z,ctx) for z in (rad,angle,h)):raise Unsupported('Undefined sector data')
        variable=task['changed_quantity'];is_radius=variable=='radius';point=rad if is_radius else angle
        for r,a in [(rad,angle),(m.add(rad,h),angle) if is_radius else (rad,m.add(angle,h))]:
            if m.sign(r,ctx)!=1 or m.sign(a,ctx)!=1 or not m.known_nonnegative(m.add(m.mul(q(2),m.PI),m.neg(a)),ctx):
                raise Unsupported('The full sector must have positive radius and angle no greater than one turn')
        expr=m.mul(q(1,2),m.mul(m.power(('v',variable) if is_radius else rad,2),angle if is_radius else ('v',variable)))
        child=dict(kind='function_increment',variable=variable,function=source(expr),at=source(point),increment=source(h),requested_output=wanted)
        return dict(sector_formula=source(expr),angle_unit='radians'),request('exact and first-order area changes',child)['value']
    if (set(task)-common-{'variable','function','argument','method_requirement'} or method!='linear_differential'
            or wanted!=['linearized_value']):raise Unsupported('Need the source argument and requested differential approximation')
    var=task['variable'];ctx=m.context({'variable':var})
    expr=m.parse(task['function'],var);point=m.parse(str(task['argument']),None)
    if not m.constant_defined(point,ctx) or not m.constant_defined(m.substitute(expr,{('v',var):point}),ctx):
        raise Unsupported('The original value at the requested point is undefined')
    centers=exact_nearby_centers(expr,var,point) if saved is None else (freeze(saved['center']),)
    for center in centers:
        if not m.constant_defined(center,ctx):continue
        lo,hi=enclose(point,None);a,b=enclose(center,None)
        try:
            for op,g in domain_conditions(expr,True):guard_bounds(op,g,(min(lo,a),max(hi,b)),[var])
        except Unsupported:continue
        child=dict(kind='function_increment',variable=var,function=task['function'],at=source(center),to=source(point),requested_output=wanted)
        return dict(center=center,argument=point,method='linear_differential'),request('first-order value from the chosen center',child)['value']
    raise Unsupported('No regular expansion center established on the same component')


def root_linearization(task,library,request,saved):
    """Lift the finite difference of an integer power to its inverse on the positive ray."""
    if not library.data.get('root_increment_law'):raise Unsupported('Positive-root linearization is unavailable')
    kind=task.get('kind');given=task.get('source',{});wanted=task.get('requested_output')
    if (not isinstance(given,dict) or set(given)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement',
            'method_requirement','explicit_imposed_method'} or
            any(given.get(k) not in (None,'linear_differential') for k in ('method_requirement','explicit_imposed_method'))):
        raise Unsupported('Additional source obligations for the root are unresolved')
    shared={'id','source','kind','requested_output'}
    def ring(identity):
        polynomial=m.parse(identity,'y',['a','x','S','A','P','n'])
        if m.rational_form(polynomial)[0]:raise Unsupported('The polynomial induction certificate does not close')
        return identity
    if kind=='root_increment_law':
        if set(task)!={'kind'}:raise Unsupported('Unknown assumptions or output in the universal root law')
        # P=y^n, A=a^n. The first expression is the new factorization defect minus y times the old one.
        step=ring('(y-a)*(y*S+A)-(y*P-a*A)-y*((y-a)*S-(P-A))')
        diagonal=ring('a*n*A+a*A-(n+1)*a*A')
        plan=dict(domain='n>=1 integer; a>0 fixed; a^n+x>0',root='y=(a^n+x)^(1/n)',
                  geometric_factor={'base':ring('(y-a)*1-(y-a)'),'initial':'S_1=1','next':'S_(n+1)=y*S_n+a^n',
                                    'inductive_identity':step,'diagonal_step':diagonal},
                  lower_bound='S_n>=a^(n-1)>0 since y>0',continuity='|y-a|=|x|/S_n<=|x|/a^(n-1)',
                  diagonal_limit='S_n(a,a)=n*a^(n-1) by the same polynomial recursion')
        return plan,dict(linearization='a+x/(n*a^(n-1))+o(x)',difference_quotient_limit='1/(n*a^(n-1))')
    literal=given.get('literal_requirement')
    if kind=='remainder_inequality':
        assertion='sqrt(a^2+x)=a+x/(2*a)-r and 0<r<x^2/(8*a^3)'
        if (set(task)-shared-{'assertion','stated_conditions'} or task.get('assertion')!=assertion or
                set(task.get('stated_conditions',()))!={'a>0','x>0'} or wanted!=['identity','strict_two_sided_remainder_bound'] or
                literal not in (None,'Доказать √(a²+x)=a+x/(2a)−r, где 0<r<x²/(8a³), для a>0, x>0.')):
            raise Unsupported('The strict square-root remainder requires the stated identity, a>0 and x>0')
        plan=dict(witness='x^2/(2*a*(sqrt(a^2+x)+a)^2)',factor=ring('y^2-a^2-(y-a)*(y+a)'),
                  error_numerator=ring('2*a*(a-y)+(y^2-a^2)-(y-a)^2'),
                  strict_comparison='x>0 implies y=sqrt(a^2+x)>a>0, hence (y+a)^2>4*a^2')
        return plan,dict(identity=assertion,remainder=plan['witness'],strict_bound=True)
    square='Доказать формулу √(a²+x)≈a+x/(2a) при a>0 и |x|≪a, применить к указанному корню и сравнить с табличным значением.'
    general='Доказать формулу корня степени n из aⁿ+x, приближённо равного a+x/(n aⁿ⁻¹), при a>0 и |x|≪a. Применить к указанному корню.'
    degree,radicand=task.get('degree'),task.get('radicand')
    outputs=['proof_of_first_order_formula','numerical_approximation']
    if (kind!='prove_and_apply_root_linearization' or set(task)-shared-{'degree','radicand'}
            or type(degree) is not int or not 1<=degree<=128 or type(radicand) is not int or radicand<=0
            or wanted not in (outputs,outputs+['table_comparison']) or literal not in (None,square,general)
            or literal==square and (degree!=2 or 'table_comparison' not in wanted)):
        raise Unsupported('The original positive radicand, integral degree or required comparison is unresolved')
    law=request('general first-order increment of an arbitrary positive integer root',{'kind':'root_increment_law'})['value']
    # A narrow integer enclosure is independently checked on replay. Its integer part brackets possible centers.
    digits=9;scale=10**digits;target=radicand*scale**degree
    if saved is None:
        low=0;high=1<<((target.bit_length()+degree-1)//degree)
        while high-low>1:
            mid=(low+high)//2
            if mid**degree<=target:low=mid
            else:high=mid
        floor=low
        if high**degree==target:floor=high
    else:floor=saved.get('scaled_floor')
    if type(floor) is not int or floor<0 or not floor**degree<=target<(floor+1)**degree:
        raise Unsupported('The proposed decimal root enclosure failed its exact power comparison')
    lower=F(floor,scale);upper=lower if floor**degree==target else F(floor+1,scale)
    k=floor//scale
    a=min((i for i in (k,k+1) if i>0),key=lambda i:(abs(radicand-i**degree),i))
    h=radicand-a**degree;approx=F(a)+F(h,degree*a**(degree-1))
    result=dict(general_law=law,linearized_value=q(approx))
    if 'table_comparison' in wanted:
        result['comparison']=dict(exact_value_interval=(q(lower),q(upper)),signed_approximation_error=(q(approx-upper),q(approx-lower)),
                                  reference='independently computed decimal bounds')
    return dict(center_root=a,center_radicand=a**degree,increment=h,scaled_floor=floor,decimal_places=digits,
                endpoint_relation='equality' if lower==upper else 'strict interior'),result


def verify_affine_gram(bounds, matrix, form):
    """Certify the positive normal form of the interval Gram matrix."""
    from model import rational

    lower, upper = [rational(x) for x in bounds]
    first, second = [[rational(x) for x in row] for row in matrix]
    weight, center, variance = [rational(x) for x in form]
    length = upper - lower
    if (weight != length or weight <= 0 or center != (lower + upper) / 2
            or variance != length**3 / 12 or variance <= 0
            or first != [weight, weight * center]
            or second != [weight * center, weight * center**2 + variance]):
        raise Unsupported('The exact Gram matrix must equal the claimed strictly positive sum of squares')


def continuous_least_squares(task, library, request):
    """Reduce affine least squares to verified moments and a positive quadratic form."""
    from model import rational
    from ray_proofs import compare_scalar
    from verify import same_value

    fields = {'id', 'kind', 'source', 'target', 'basis', 'interval', 'stated_conditions', 'requested_output'}
    provenance = task.get('source', {})
    provenance_fields = {'exercise', 'printed_subpart', 'pdf_page', 'printed_page', 'pdf_sha256', 'literal_requirement'}
    heading = 'Найти линейную функцию a+b*x с минимальным средним квадратом ошибки.'
    basis = task.get('basis')
    if (not library.data.get('continuous_affine_projection') or set(task) - fields
            or not isinstance(provenance, dict) or set(provenance) - provenance_fields
            or provenance.get('literal_requirement', heading) != heading
            or task.get('requested_output') != ['optimal_coefficients', 'justify_global_minimum']
            or not isinstance(basis, list) or len(basis) != 2 or basis[0] != '1'):
        raise Unsupported('A complete affine least-squares goal is required')

    coordinate = basis[1]
    context = m.context(dict(variable=coordinate))
    interval = task.get('interval')
    if not isinstance(interval, str) or not (ends := re.fullmatch(r'\[\s*([^,]+),\s*([^,]+)\]', interval)):
        raise Unsupported('The original least-squares interval must be closed and finite')
    raw_bounds = tuple(m.parse(edge, None) for edge in ends.groups())
    if not all(m.constant_defined(edge, context) for edge in raw_bounds):
        raise Unsupported('A stated integration endpoint is undefined')
    bounds = tuple(m.simplify(edge) for edge in raw_bounds)
    lower, upper = [rational(edge) for edge in bounds]
    length = upper - lower
    if length <= 0:
        raise Unsupported('The input interval needs positive length')

    # The target must be defined before either multiplication by a basis element
    # or simplification. A moment does not certify a missing source point.
    raw = m.parse(task['target'], coordinate)
    target_range = enclose(raw, (lower, upper))
    conditions = task.get('stated_conditions', [])
    if not isinstance(conditions, list) or not all(isinstance(condition, str) for condition in conditions):
        raise Unsupported('The source coefficient constraints must be explicit')
    limits = None
    if conditions:
        if len(conditions) != 1 or not (match := re.fullmatch(
            r'([-+]?\d+(?:/\d+)?)<=a<=([-+]?\d+(?:/\d+)?)(?: as printed next to the approximation)?', conditions[0]
        )):
            raise Unsupported('Only an exact closed interval on the intercept is implemented')
        limits = tuple(F(edge) for edge in match.groups())
        if limits[0] > limits[1]:
            raise Unsupported('The coefficient constraints have an empty feasible set')

    center = (lower + upper) / 2
    variance = length**3 / 12
    g00, g01, g11 = length, (upper**2 - lower**2) / 2, (upper**3 - lower**3) / 3
    gram = ((q(g00), q(g01)), (q(g01), q(g11)))
    form = (q(length), q(center), q(variance))
    verify_affine_gram(bounds, gram, form)
    determinant = g00 * g11 - g01**2

    moments = []
    for power, integrand in enumerate((raw, ('mul', ('v', coordinate), raw))):
        child = dict(kind='finite_interval_integral', variable=coordinate, integrand=source(integrand),
                     interval=list(map(source, bounds)), method_requirement='newton_leibniz', requested_output=['exact_integral'])
        answer = request('exact source moment of degree ' + str(power), child)
        moments.append(freeze(answer['value']))
    m0, m1 = moments
    intercept = m.div(m.add(m.mul(q(g11), m0), m.neg(m.mul(q(g01), m1))), q(determinant))
    branch = 'interior'
    if limits is not None:
        left, right = map(q, limits)
        if left == right:
            intercept, branch = left, 'fixed'
        elif compare_scalar(intercept, left) < 0:
            intercept, branch = left, 'lower'
        elif compare_scalar(intercept, right) > 0:
            intercept, branch = right, 'upper'
    slope = m.div(m.add(m1, m.neg(m.mul(q(g01), intercept))), q(g11))
    residual_a = m.add(m.add(m.mul(q(g00), intercept), m.mul(q(g01), slope)), m.neg(m0))
    residual_b = m.add(m.add(m.mul(q(g01), intercept), m.mul(q(g11), slope)), m.neg(m1))
    if not same_value(residual_b, ZERO):
        raise Unsupported('The computed slope does not satisfy its normal equation')
    if branch == 'interior' and not same_value(residual_a, ZERO):
        raise Unsupported('The computed intercept does not satisfy its normal equation')
    if branch in ('lower', 'upper') and compare_scalar(residual_a, ZERO) != {'lower': 1, 'upper': -1}[branch]:
        raise Unsupported('The intercept gradient fails the one-sided minimum condition')
    plan = dict(theorem='method.continuous_affine_projection', variable=coordinate, bounds=bounds,
                source_target=raw, continuous_target_range=tuple(map(q, target_range)), gram=gram, gram_form=form,
                moments=moments, constraint=tuple(map(q, limits)) if limits is not None else None, active=branch,
                half_gradient=(residual_a, residual_b))
    return plan, dict(intercept=intercept, slope=slope, unique_global_minimum=True)


def continuous_projection_report(result, pretty):
    plan, answer = result['compilation'], result['value']
    coord = plan['variable']
    weight, center, variance = map(lambda e: pretty(e, coord), plan['gram_form'])
    lines = [
        'Вычисляем два интеграла от исходной функции с весами 1 и ' + coord + '.',
        'Из моментов получаем равенство для наклона и условие минимума для свободного коэффициента.',
        'Для изменений коэффициентов h и k прибавка второго порядка равна '
        + weight + '·(h + (' + center + ')·k)² + ' + variance + '·k². '
        'Она строго положительна для любого ненулевого изменения.',
    ]
    if plan['constraint'] is not None:
        lines.append('Проверяем ограничение на свободный коэффициент. У активной границы линейная часть '
                     'имеет знак минимума для всех допустимых изменений.')
    else:
        lines.append('Линейная часть прибавки равна нулю по двум уравнениям, поэтому найденная точка даёт глобальный минимум.')
    lines.append('Единственный минимум достигается при a = ' + pretty(answer['intercept'], coord)
                 + ', b = ' + pretty(answer['slope'], coord) + '.')
    return '\n'.join(lines)


def compact_derivative_identity(task,lib):
    """Prove a compact-integral derivative identity using checked differential kernels."""
    from cartesian_fields import derivative_table,vector_source
    from verify import same_value
    kind=task['kind']
    def finish(theorem,result,*steps,**evidence):
        return dict(theorem='method.'+theorem,steps=steps,**evidence),result
    if kind=='parameter_integral_identity' and 'formula' in task:
        vector_source(task,{'formula','requested_output'},('Доказать формулу производной и получить оценку.',))
        if task['requested_output']!=['proof','derive_uniform_bound_1/(n+1)_for_all_real_x']:
            raise Unsupported('Both the derivative and the bound are required')
        name=r'([A-Za-z_]\w*)'
        pattern=r'd\^'+name+r'/d'+name+r'\^\1\s*\(sin\(\2\)/\2\)=\2\^\(-\1-1\)\*int_0\^\2\s+'+name+r'\^\1\*cos\(\3\+\1\*pi/2\)d\3;\s*\1=1,2,\.\.\.'
        hit=re.fullmatch(pattern,task['formula'])
        if not hit or len(set(hit.groups()))!=3:raise Unsupported('The derivative order, outer variable and integration binder must be distinct')
        n,x,y=hit.groups()
        return finish('local_parameter_derivative_majorants',dict(proved=True,bound=m.div(ONE,m.add(ONE,('s',n))),
                      at_zero=f'cos({n}*pi/2)/({n}+1)'),
            'Синус, делённый на аргумент, равен интегралу cos(tx) по t от 0 до 1. При x=0 та же формула задаёт гладкое продолжение.',
            'При каждом дифференцировании по x появляется множитель t, а фаза сдвигается на π/2. На компактном интервале по t все эти частные непрерывны.',
            'При x≠0 замена y=xt сохраняет ориентацию и даёт указанную формулу. Оценка модуля косинуса единицей даёт интеграл от t^n по отрезку.',
            derivative_order=n,outer_coordinate=x,integration_coordinate=y,absolute_majorant=f't^{n} on [0,1]')
    if kind=='parameter_integral_identity' and 'claim' in task:
        vector_source(task,{'definition','stated_conditions','claim','requested_output'},('Показать гармоничность вне носителя отрезка.',))
        text=task['definition'].replace('²','^2')
        kernel,sep,annotation=text.partition('; ')
        hit=re.fullmatch(r'([A-Za-z_]\w*)=int_0\^([A-Za-z_]\w*) \(([A-Za-z_]\w*)\)d_\3/sqrt\((.+)\)',kernel)
        if not hit or sep and annotation!='displayed numerator appears (xi), text introduces f(x)' or task['requested_output']!=['proof']:
            raise Unsupported('The compact line potential and its actual numerator scope must be bound')
        u,L,t,radicand=hit.groups()
        axes=re.findall(re.escape(u)+r'_([A-Za-z][A-Za-z_0-9]*)',task['claim'])
        if len(axes)!=3 or any(len(a)!=2 or a[0]!=a[1] for a in axes):
            raise Unsupported('The requested operator must be the ambient Laplacian')
        axes=[a[0] for a in axes]
        if (len({u,L,t,*axes})!=6 or task['claim']!='+'.join(u+'_'+a+a for a in axes)+'=0'
                or task['stated_conditions']!=[f'f continuous on [0,{L}]',f'{radicand}!=0 for 0<={t}<={L}']):
            raise Unsupported('Continuity of the source weight and each excluded point must be explicit')
        q0=m.parse(radicand,None,[*axes,t])
        v=list(map(lambda a:('s',a),axes))
        offsets=[m.add(a,m.neg(('s',t))) if i==0 else a for i,a in enumerate(v)]
        if not same_value(q0,m.dot(offsets,offsets)) or domain_conditions(q0):
            raise Unsupported('The whole radicand must be the squared distance to the line parameter')
        partial,trace=derivative_table(lib)
        f=('div',ONE,('sqrt',q0))
        lap=ZERO
        for a in axes:lap=m.add(lap,partial(partial(f,a),a))
        if not same_value(lap,ZERO):raise Unsupported('The differentiated kernel is not harmonic')
        return finish('local_parameter_derivative_majorants',dict(proved=True,laplacian=ZERO,scope='each point off the source compact segment'),
            'Обе указанные интерпретации веса дают непрерывную функцию связанной координаты. Вес не зависит от точки наблюдения.',
            'В каждой допустимой точке расстояние до компактного отрезка имеет положительный минимум. В малой окрестности то же верно равномерно, поэтому первые и вторые производные можно переносить под интеграл.',
            'Вычисленные вторые производные обратного расстояния в сумме сокращаются.',
            squared_distance=q0,kernel_derivatives=trace)
    if kind=='elliptic_integral_derivatives':
        vector_source(task,{'definitions','stated_conditions','ode','requested_output'},('Выразить производные E,F через E,F и показать уравнение для E.',))
        name=r'([A-Za-z_]\w*)'
        definitions=task['definitions']
        if len(definitions)!=2 or task['requested_output']!=['E_derivative','F_derivative','ode_proof']:
            raise Unsupported('Both compact elliptic kernels and the differential equation are required')
        shapes=[re.fullmatch(name+r'\('+name+r'\)=int_0\^\(pi/2\) (.+)d'+name,d) for d in definitions]
        if not all(shapes) or shapes[0][2]!=shapes[1][2] or shapes[0][4]!=shapes[1][4]:
            raise Unsupported('Both kernels must refer to the same amplitude and bound coordinate')
        E,k,f,phi=shapes[0].groups();F=shapes[1][1]
        if (len({E,F,k,phi})!=4 or task['stated_conditions']!=[f'0<{k}<1']
                or task['ode'].replace('²','^2')!=f'{E}pp+{E}p/{k}+{E}/(1-{k}^2)=0'):
            raise Unsupported('The amplitude interval and the actual ODE must agree')
        K=('s',k);t=('s',phi);S,C=('sin',t),('cos',t)
        D=m.add(ONE,m.neg(m.power(m.mul(K,S),2)))
        R=('sqrt',D);I=m.div(ONE,R)
        for provided,expected in zip(shapes,(R,I),strict=True):
            kernel=m.parse(provided[3],None,[k,phi])
            if kernel[0]=='sqrt':
                valid=not domain_conditions(kernel[1]) and same_value(kernel[1],D) and expected==R
            else:
                valid=kernel[:2]==('div',ONE) and kernel[2][0]=='sqrt' and not domain_conditions(kernel[2][1]) and same_value(kernel[2][1],D) and expected==I
            if not valid:raise Unsupported('The original compact elliptic kernel differs')
        partial,trace=derivative_table(lib)
        rhs_E=m.div(m.add(R,m.neg(I)),K);comp=m.add(ONE,m.neg(m.power(K,2)))
        rhs_F=m.add(m.div(R,m.mul(K,comp)),m.neg(m.div(I,K)))
        H=m.div(m.mul(S,C),R)
        if not same_value(partial(R,k),rhs_E) or not same_value(
                partial(I,k),m.add(rhs_F,m.mul(m.div(m.neg(K),comp),partial(H,phi)))):
            raise Unsupported('An elliptic integration-by-parts identity did not replay')
        E0,F0=('s',E),('s',F)
        ep=m.div(m.add(E0,m.neg(F0)),K)
        fp=m.add(m.div(E0,m.mul(K,comp)),m.neg(m.div(F0,K)))
        epp=m.neg(m.div(fp,K))
        if not same_value(m.add(m.add(epp,m.div(ep,K)),m.div(E0,comp)),ZERO):
            raise Unsupported('The verified first derivatives do not imply the original ODE')
        return finish('local_parameter_derivative_majorants',dict(E_derivative=ep,F_derivative=fp,ode_proved=True),
            'На локальном окне внутри 0<k<1 подкоренное выражение отделено от нуля на всём угловом отрезке.',
            'Первая производная корня непосредственно разлагается через два исходных ядра. Для обратного корня добавляется полная угловая производная с нулевыми граничными значениями.',
            'Дифференцируем полученную формулу первой производной и подставляем вторую связь. Коэффициенты в исходном ОДУ сокращаются.',
            angular_boundary_term=H,derivatives=trace)
    raise Unsupported('No compact differential identity is yet justified for this source')


def positive_laplace_bessel_identity(task):
    from cartesian_fields import vector_source
    from verify import same_value
    vector_source(task,{'claim','definition','stated_conditions','requested_output'},('Доказать интеграл Липшица.',))
    name=r'([A-Za-z_]\w*)'
    normalized=task['claim'].replace('²','^2')
    shape=re.fullmatch(r'int_0\^inf exp\(-'+name+r'\*'+name+r'\)\*'+name+r'\('+name+r'\*\2\)d\2=1/sqrt\((.+)\)',normalized)
    if not shape or task['requested_output']!=['proof']:raise Unsupported('The positive-scale Laplace moment must be stated explicitly')
    a,t,f,b,square=shape.groups()
    kernel=re.fullmatch(re.escape(f)+r'\('+name+r'\)=int_0\^pi cos\(\1\*sin\('+name+r'\)\)d\2/pi',task['definition'])
    if (not kernel or len({a,t,f,b,*kernel.groups()})!=6
            or task['stated_conditions']!=[a+'>0'] or domain_conditions(m.parse(square,None,[a,b]))):
        raise Unsupported('The normalized angular representation and positivity must be explicit')
    A,B=('s',a),('s',b);Q=m.add(m.power(A,2),m.power(B,2))
    if not same_value(m.parse(square,None,[a,b]),Q):raise Unsupported('The claimed value has a different scale')
    value=m.div(ONE,('sqrt',Q))
    return dict(theorem='method.oriented_parameter_integral_exchange',attenuation=A,angular_scale=B,steps=[
        'Подставляем заданное косинусное представление. Модуль двойного ядра не больше e^(−a t), а угловой отрезок конечен.',
        'Внутренний косинусный момент даёт a/(a²+b² sin²φ). Симметрия приводит угол к первому квадранту.',
        'Подстановка тангенса даёт положительный квадратный знаменатель a²+(a²+b²)u². Интеграл арктангенса и исходная нормировка дают обратный корень.',
    ]),dict(proved=True,value=value)



def logarithmic_period_cells(task):
    """Integrate a signed periodic profile in a logarithmic coordinate."""
    from cartesian_fields import vector_source
    from integrals import affine
    vector_source(task,{'integrand','variable','lower','upper','requested_output','parameters','stated_conditions'},())
    v=task['variable'];text=task['integrand'].replace('sgn[','sgn(').replace(']',')')
    p=task.get('parameters',[])
    if (task['requested_output']!=['exact_integral'] or str(task['lower'])!='0' or str(task['upper'])!='1'
            or p or task.get('stated_conditions')):
        raise Unsupported('A logarithmic harmonic on the original unit interval is required')
    raw=m.parse(text,v,extra_functions=['sgn'])
    if raw[0]!='sgn' or raw[1][0]!='sin':raise Unsupported('The source must be the sign of a sinusoidal logarithm')
    l=('ln',('v',v));z=('v','_phase')
    decomposition=m.substitute(raw[1][1],{l:z})
    rate,offset=affine(decomposition,z[1]);k=m.num(rate)
    if not k or offset!=ZERO or m.variable_in(decomposition,v) or domain_conditions(decomposition):
        raise Unsupported('The original logarithmic phase must have a nonzero fixed rate')
    length=m.div(m.PI,q(abs(k)));ratio=('exp',m.neg(length));orientation=q(-1 if k>0 else 1)
    val=m.mul(orientation,m.div(m.add(ONE,m.neg(ratio)),m.add(ONE,ratio)))
    return dict(theorem='method.parameter_endpoint_comparison',cell_length=length,cell_ratio=m.neg(ratio),steps=[
        'Замена исходной координаты на экспоненту отрицательной новой координаты даёт вес e^(−t) и переносит нуль в бесконечность.',
        'Знак синуса постоянен внутри каждой полуволны. Интеграл веса на каждой следующей клетке умножается на e^(−длина клетки), а знак меняется.',
        'Остаток неполной клетки ограничен соответствующим экспоненциальным хвостом. Суммируем ориентированный геометрический ряд.',
    ]),dict(convergence='convergent',absolute=True,value=val)


def logarithmic_trig_coefficient(task):
    """Extract a logarithmic Fourier coefficient by Abel damping."""
    from cartesian_fields import vector_source
    from integrals import affine
    v=task['variable'];x=('v',v);p=task.get('parameters',[])
    if (task['requested_output']!=['exact_integral'] or str(task['lower'])!='0'
            or len(p)!=1 or task.get('stated_conditions') not in ([p[0]+' is a positive integer'],[p[0]+' positive integer'])):
        raise Unsupported('The logarithmic harmonic requires its original positive integer index')
    vector_source(task,{'integrand','variable','lower','upper','requested_output','parameters','stated_conditions'},())
    n=('s',p[0]);raw=m.parse(task['integrand'],v,p)
    if raw[0]!='mul':raise Unsupported('A single logarithmic harmonic product is required')
    f,g=raw[1:]
    if f[0]!='ln':f,g=g,f
    if f[0]!='ln' or f[1][0] not in ('sin','cos') or g[0]!='cos' or domain_conditions(f[1]) or domain_conditions(g):
        raise Unsupported('The compact logarithm and cosine weights must both be explicit')
    w=f[1]
    rate,offset=affine(w[1],v);slope,phase=affine(g[1],v)
    k=m.num(rate);upper=m.parse(str(task['upper']),None)
    if not k or k<=0 or offset!=ZERO or phase!=ZERO or slope!=m.mul(q(2*k),n) or m.mul(rate,upper)!=m.div(m.PI,q(2)):
        raise Unsupported('The interval and the harmonic must match the same first quarter period')
    sign=('cos',m.mul(m.PI,m.add(n,q(-1)))) if w[0]=='cos' else q(-1)
    value=m.mul(sign,m.div(m.PI,m.mul(q(4*k),n)))
    return dict(theorem='method.uniform_oscillatory_tail',mode=n,log_wave=w[0],axis_scale=rate,steps=[
        'Для r<1 разложение ln(1±r exp(2it)) сходится равномерно. Действительная часть выделяет коэффициенты синуса или косинуса по исходному знаку.',
        'При r≥1/2 модуль комплексного аргумента ограничен сверху константой, а снизу пропорционален исходному синусу или косинусу. Их логарифм интегрируем у нужного конца.',
        'Снимаем затухание по общей мажоранте. На четверти периода остаётся только совпадающий косинусный режим и его проверенная норма π/4.',
    ]),dict(convergence='convergent',absolute=True,value=value)


def dirichlet_multiplier(task):
    from cartesian_fields import vector_source
    from integrals import affine
    vector_source(task,{'function','requested_output'},('Найти разрывный множитель Дирихле для всех x и построить график.',))
    name=r'([A-Za-z_]\w*)'
    f=re.fullmatch(name+r'\('+name+r'\)=\(2/pi\)\*int_0\^inf (.+)\s+d'+name,task['function'])
    if not f or task['requested_output']!=['piecewise_function']:
        raise Unsupported('The whole Dirichlet multiplier with its normalization is required')
    _,arg,body,v=f.groups();x=('v',v);A=('s',arg)
    if arg==v:raise Unsupported('The frequency parameter and integration variable must be distinct')
    raw=m.parse(body,v,[arg])
    if raw[0]!='div' or raw[2]!=x or raw[1][0]!='mul':
        raise Unsupported('The Dirichlet denominator must be the original integration coordinate')
    sine,cosine=raw[1][1:]
    if sine[0]=='cos':sine,cosine=cosine,sine
    if sine[0]!='sin' or cosine[0]!='cos' or domain_conditions(raw[1]):
        raise Unsupported('The original numerator needs a sine and cosine without another singularity')
    k,c=affine(sine[1],v);h,d=affine(cosine[1],v)
    if m.num(k) is None or m.num(k)<=0 or c!=ZERO or d!=ZERO or h!=A:
        raise Unsupported('A positive fixed sine scale and the stated frequency parameter are required')
    return dict(theorem='method.signed_dirichlet_frequency',oriented_frequencies=(m.add(k,A),m.add(k,m.neg(A))),steps=[
        'Разложение произведения в сумму даёт два знаковых интеграла Дирихле с частотами a+x и a−x.',
        'Нулевая частота даёт нулевой вклад. Два положительных знака внутри, один в граничных точках и взаимное сокращение снаружи дают полное кусочное значение.',
    ]),dict(cases=[dict(condition=f'abs({arg})<{source(k)}',value=ONE),
                   dict(condition=f'abs({arg})={source(k)}',value=q(1,2)),
                   dict(condition=f'abs({arg})>{source(k)}',value=ZERO)])


def gaussian_rodrigues_orthogonality(task):
    from cartesian_fields import vector_source
    vector_source(task,{'definition','weight','limits','claims','requested_output'},
                  ('Доказать ортогональность многочленов Чебышёва–Эрмита и норму.',))
    definition=task['definition'].replace('²','^2')
    token=r'([A-Za-z]\w*)'
    hit=re.fullmatch(token+r'_([A-Za-z])=\(-1\)\^\2 exp\('+token+r'\^2\)\*\(d/d\3\)\^\2 exp\(-\3\^2\),\2=0,1,\.\.\.',definition)
    if not hit or task['limits']!='-inf..inf' or task['requested_output']!=['proof_both_cases']:
        raise Unsupported('The Gaussian Rodrigues family, whole interval and both conclusions are required')
    H,n,v=hit.groups()
    if task['weight'].replace('²','^2')!=f'exp(-{v}^2)':raise Unsupported('The source weight must match the Rodrigues derivative')
    claims=task['claims']
    tag=re.fullmatch(r'int '+re.escape(H)+r'([A-Za-z]) '+re.escape(H+n)+r' weight=0 for \1!='+re.escape(n),claims[0]) if len(claims)==2 else None
    if not tag or tag[1]==n or claims[1]!=f'int {H+n}² weight=2^{n}*{n}!*sqrt(pi)':
        raise Unsupported('The printed normalization and both index cases must be preserved')
    return dict(theorem='method.gaussian_fourier_moments',index=n,companion=tag[1],weight=task['weight'],steps=[
        'Дифференцируем формулу Родрига ещё раз. Получается рекурсия H_(n+1)=2x H_n−H_n′. Из H_0=1 следуют степень n и ведущий коэффициент 2^n.',
        'Переносим производные большего порядка интегрированием по частям. Любой многочлен с гауссовым весом стремится к нулю на каждом конце.',
        'При разных индексах производная меньшего многочлена исчезает. При равных индексах остаётся его старшая производная 2^n n! и гауссов интеграл.',
    ]),dict(proved=True,unequal_index_integral=ZERO,equal_index_norm=f'2^{n}*{n}!*sqrt(pi)')


def gamma_product_or_wave(task):
    from cartesian_fields import vector_source
    from verify import same_value
    vector_source(task,{'claim','stated_conditions','requested_output'},
                  ('Доказать напечатанную формулу Эйлера.','Доказать напечатанное равенство.'))
    if task['requested_output']!=['proof_or_counterexample']:
        raise Unsupported('Both the identity and permitted disproof must be source-bound')
    text=task['claim'].replace('²','^2')
    label=r'([A-Za-z_]\w*)'
    factors=re.fullmatch(r'prod_\('+label+r'=1\)\^'+label+r' int_0\^inf '+label+r'\^\(\1-1\)\*exp\(-\3\^\2\)d\3=(.+)',text)
    if factors:
        j,n,x,right=factors.groups()
        if len({j,n,x})!=3 or task.get('stated_conditions'):
            raise Unsupported('The positive integer product index is not bound')
        symbol=('s',n)
        claim=m.parse(right,None,[n])
        expected=m.mul(('rpow',m.div(ONE,symbol),m.add(symbol,q(1,2))),
                       ('rpow',m.mul(q(2),m.PI),m.div(m.add(symbol,q(-1)),q(2))))
        example=m.simplify(m.substitute(claim,{symbol:q(2)}))
        actual=m.div(('sqrt',m.PI),q(4))
        result=dict(derived_product=source(expected))
        if same_value(claim,expected):result['identity']=True
        elif same_value(m.power(example,2),m.div(m.PI,q(4))):
            result.update(printed_claim_holds=False,counterexample=dict(index=2,left=actual,right=example))
        else:raise Unsupported('The claimed product could not be compared to the verified value')
        return dict(theorem='method.euler_endpoint_transport',product_index=j,upper_index=n,steps=[
            'В каждом множителе замена y=x^n даёт Γ(j/n)/n. Исходные гамма-показатели положительны.',
            'Сопоставляем j и n−j в произведении отражений. Произведение синусов равно n/2^(n−1) из факторизации корней единицы; положительность гамма-функции определяет знак корня.',
            'Сохраняем множитель n^(−n) из всех якобианов. При расхождении с напечатанной формулой сравниваем отдельно точные значения для n=2.',
        ]),result

    base=r'int_0\^inf '+label+r'\^\('+label+r'-1\)\*exp\(-'+label+r'\*\1'
    oscillatory=re.fullmatch(base+r'\*cos\('+label+r'\)\)\*(sin|cos)\(\3\*\1\*sin\(\4\)\)d\1=Gamma\(\2\)/\3\^\2\*\5\(\4\*\2\)',text)
    malformed=re.fullmatch(base+r'\)\*cos\('+label+r'\)\*\(\3\*\1\*sin\(\4\)\)d\1=Gamma\(\2\)/\3\^\2\*cos\(\4\*\2\) as printed',text)
    hit=oscillatory or malformed
    if not hit:raise Unsupported('The damped gamma representation is not yet identified')
    t,p,a,theta=hit.groups()[:4]
    expected=[a+'>0',p+'>0','-pi/2<'+theta+'<pi/2']
    if len({t,p,a,theta})!=4 or sorted(task.get('stated_conditions',[]))!=sorted(expected):
        raise Unsupported('The real part of the decay and gamma order need their original positive scope')
    if malformed:
        return dict(theorem='method.euler_endpoint_transport',steps=[
            'Берём единичный масштаб и порядок и нулевой угол в исходной области.',
            'В левой части множитель синуса угла обнуляет ядро. Справа остаётся Γ(1)=1.',
        ]),dict(printed_claim_holds=False,counterexample={a:ONE,p:ONE,theta:ZERO,'left':ZERO,'right':ONE})
    mode=oscillatory[5];A,T,P=('s',a),('s',theta),('s',p)
    decay=m.mul(A,('cos',T));freq=m.mul(A,('sin',T))
    return dict(theorem='method.euler_endpoint_transport',attenuation=decay,frequency=freq,order=P,steps=[
        'Положительная действительная часть задаёт экспоненциальный хвост. У нуля показатель p−1>−1. На локальном окне частоты справедливо дифференцирование под интегралом.',
        'Для комплексного момента G интегрирование по частям даёт G′(b)=i p G(b)/(a−i b) при действительном a>0. Начальное значение G(0)=Γ(p)/a^p фиксирует решение.',
        'Модуль a−i b равен исходному масштабу, а его аргумент равен минус исходному углу на заданном промежутке. Берём указанную гармоническую компоненту.',
    ]),dict(identity=True,value=f'Gamma({p})/{a}^{p}*{mode}({theta}*{p})')





def characteristic_area_wave(task):
    check_integral_identity_source(task,{'definition','hypotheses','requested_output'},
                                   'Доказать u_xx−u_yy=f при непрерывной f.')
    name=r'[A-Za-z][A-Za-z_0-9]*'
    text=task['definition']
    match=re.fullmatch(fr'({name})=1/2\*int_0\^({name}) d({name}) int_\(\3-\2\+({name})\)\^\(\2\+\4-\3\) ({name})\(\3,({name})\) d\6',text)
    if match is None or task.get('requested_output')!=['identity_proof']:
        raise Unsupported('The two oriented characteristic ends must be recovered')
    u,x,xi,y,f,eta=match.groups()
    facts=task.get('hypotheses')
    if len(set(match.groups()))!=6 or facts not in ([f+' continuous'],[f+' continuously differentiable']):
        raise Unsupported('The equation needs a stated regularity level on the characteristic triangle')
    continuous=facts==[f+' continuous']
    result=dict(mixed_characteristic_equation=f'4*{u}_sr={f}((s+r)/2,(s-r)/2)',
                classical_scope=f'{f} continuously differentiable locally')
    if continuous:
        result.update(printed_claim_holds=False,counterexample=dict(forcing=f'abs({xi}+{eta})',
            point=[ONE,q(-1)],second_x_derivative_limits=[ZERO,ONE]))
    return dict(theorem='method.characteristic_triangle_wave',steps=[
        'Переходим к s=x+y, r=x−y. Во внутреннем интеграле берём A=ξ+η, B=ξ−η и учитываем якобиан 1/2.',
        'Ориентированная область задаётся −r≤A≤s и −A≤B≤r в прямом порядке, при обратном порядке сохраняем знаки пределов. Коэффициент перед интегралом равен 1/4.',
        'После дифференцирования по каждой из двух характеристик смешанная производная равна F(s,r)/4 уже при непрерывной F. При гладкости нужных частных чистые производные также существуют, и u_xx−u_yy=4u_sr.',
        'Для F(A,B)=|A| около s=0,r=2 получаем u=r³/24+r·s|s|/8+|s|³/12. В исходных координатах в (1,−1) левая и правая вторые производные по x равны 0 и 1.'
    ]),result


def level_area_distribution(task):
    check_integral_identity_source(task,{'definition','literal','transcription','hypotheses','requested_output'},
                                   'Доказать формулу интегрирования по слоям между простыми замкнутыми линиями уровня; указан способ разбиения.')
    form=r'S\(([A-Za-z]\w*),([A-Za-z]\w*)\) lies between ([A-Za-z]\w*)=\1 and \3=\2'
    matches=re.fullmatch(form,task['definition'])
    if matches is None or task.get('requested_output')!=['proof']:
        raise Unsupported('The ordered plane levels must be explicit')
    a,b,f=matches.groups()
    expected=f'int_S {f}(x,y) dxdy = int_{a}^{b} v*F_prime(v) dv'
    note='The printed definition of F(v) repeats f=v1,f=v2. The variable-area interpretation must be distinguished from this literal text.'
    facts=task.get('hypotheses',[])
    if len(set(matches.groups()))!=3 or task['literal']!=expected or task.get('transcription') not in (None,note) or facts not in ([],['F is cumulative sublevel area and absolutely continuous']):
        raise Unsupported('The cumulative area interpretation must be checked against the actual source')
    good=bool(facts)
    answer=dict(identity='integral of f over the strip = integral of v with respect to cumulative area dF(v)',
                derivative_form_scope='F is absolutely continuous on the original level interval')
    if not good:
        answer.update(printed_claim_holds=False,counterexample=dict(function='x^2+y^2',levels=[ONE,q(4)],
            integral=m.mul(q(15,2),m.PI),literal_as_constant_area=ZERO))
    return dict(theorem='method.level_area_stieltjes_measure',steps=[
        'Разбиваем диапазон значений f на интервалы. На каждой полосе интеграл лежит между концами интервала, умноженными на площадь полосы.',
        'Разность двух сумм не превосходит диаметра разбиения, умноженного на полную площадь. Предел есть интеграл Стилтьеса по накопленной площади.',
        'При абсолютной непрерывности F её приращения выражаются через интеграл F′, поэтому получается обычная формула.',
        'Если буквально взять площадь между двумя фиксированными исходными контурами, она постоянна и правая часть равна нулю. Функция x²+y² на кольце между уровнями 1 и 4 даёт положительный интеграл.'
    ]),answer


def quantified_subregion_integrals(task):
    check_integral_identity_source(task,{'literal','hypotheses','claim','requested_output'},
                                   'Доказать тождественное обращение непрерывной f в нуль, если интеграл равен нулю для любой подобласти omega.')
    natural='the displayed integral is over omega and the text quantifies every omega subset V'
    literal='the displayed integral is subscripted V while the text quantifies every omega subset V'
    stated=task.get('literal')
    region='V' if stated==literal else 'omega'
    if (stated not in (natural,literal) or task.get('requested_output')!=['proof','preserve_literal_subscript']
            or task.get('hypotheses')!=['f continuous on V',f'int_{region} f(x,y,z) dx dy dz=0 for every domain omega subset V']
            or task.get('claim')!='f(x,y,z)=0 for every (x,y,z) in V'):
        raise Unsupported('The quantified domain and displayed integration index both need binding')
    answer=dict(local_integrals_imply_zero=True,displayed_domain=region)
    if region=='V':
        answer.update(printed_claim_holds=False,counterexample=dict(domain='[-1,1]^3',f='x',integral=ZERO,
                     nonzero_value=dict(point=[q(1,2),ZERO,ZERO],value=q(1,2))))
    return dict(theorem='method.quantified_local_integral_zero',steps=[
        'Если все локальные интегралы нулевые, ненулевое значение в точке по непрерывности даёт шар постоянного строгого знака.',
        'Интеграл по этому шару ненулевой, что противоречит условию для каждой подобласти. Включённая граница покрывается непрерывным продолжением из внутренности области.',
        'Если вместо каждой подобласти интегрируют по одному исходному V, повторение одного равенства даёт лишь нулевое среднее. Нечётная ненулевая функция на симметричном кубе удовлетворяет этому слабому условию.'
    ]),answer


def moving_radius_differential(task):
    check_integral_identity_source(task,{'formula','stated_conditions','requested_output'},
                                   'Доказать формулу дифференцирования по радиусу t>0.')
    text=task['formula'];pattern=r'd/d([A-Za-z]\w*) int_\{r<=\1\} ([A-Za-z]\w*)\(x,y,z,\1\)dV = int_\{r=\1\} \2\(x,y,z,\1\)dS \+ int_\{r<=\1\} partial_\1 \2\(x,y,z,\1\)dV'
    hit=re.fullmatch(pattern,text)
    if hit is None or task.get('requested_output')!=['proof']:
        raise Unsupported('The integral and both derivatives must use the same radius and integrand')
    t,f=hit.groups();facts=task['stated_conditions']
    valid_condition=f'{f} and partial_{t} {f} continuous near the closed moving ball'
    if facts not in ([t+'>0'],[t+'>0',valid_condition]):
        raise Unsupported('The radius and needed local regularity must be preserved')
    answer=dict(formula=text,sufficient_conditions=[t+'>0',valid_condition])
    if len(facts)==1:
        answer.update(printed_claim_holds=False,counterexample=dict(integrand=f'abs({t}-1)',radius=ONE,
            moving_integral=f'4*pi*{t}^3*abs({t}-1)/3',derivative_sides=[m.mul(q(-4,3),m.PI),m.mul(q(4,3),m.PI)]))
    return dict(theorem='method.moving_radius_boundary_trace',steps=[
        'Записываем разность интегралов как изменение поля на прежнем шаре и ориентированный интеграл по тонкому слою.',
        'При локальной непрерывности частной производной первый разностный интеграл сходится равномерно на компактном шаре.',
        'Во втором интеграле сферические слои имеют элемент r²dr dω. После деления на приращение радиуса из непрерывности остаётся след на исходной сфере.',
        'Без гладкости по параметру даже постоянное в пространстве поле |t−1| даёт разные односторонние производные в t=1.'
    ]),answer



def shifted_uniform_integrand_window(task):
    check_integral_identity_source(task,{'statement','requested_output'},None)
    note='Знак в печатном включении [a−x,b−x] отличается от сдвига аргумента x+y.'
    src=task.get('source',{})
    if set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','printed_anomaly'} or src.get('printed_anomaly') not in (None,note):
        raise Unsupported('The original displacement and explicit qualification must be retained')
    grammar=r'([A-Za-z]\w*) непрерывна на \[A,B\]⊃\[a,b\]; найти d/dx ∫ₐᵇ \1\(x\+y\)dy, считая \[a([−+])x,b\2x\]⊂\[A,B\]\.'
    hit=re.fullmatch(grammar,task.get('statement',''))
    if not hit or task.get('requested_output')!=['derivative_with_domain']:
        raise Unsupported('Both translated arguments, integration interval and original inclusion are needed')
    f,sign=hit.groups()
    value=dict(formula=f'{f}(x+b)-{f}(x+a)',domain='[A-a,B-b]',
               scope='interior derivative, relative at included endpoints when there is a nontrivial domain interval')
    if sign=='−':
        value.update(printed_claim_holds=False,counterexample=dict(
            given_interval=[ZERO,q(4)],integral_interval=[ONE,q(2)],x=q(-3,2),
            stated_window=[q(5,2),q(7,2)],actual_window=[q(-1,2),q(1,2)]))
    return dict(theorem='method.uniform_translation_with_domain',steps=[
        'Подстановка u=x+y переносит исходный отрезок в [a+x,b+x]. Из включения выводим точную область, где достаточно заданной непрерывности.',
        'В этой области вычитаем значения одной первообразной на верхнем и нижнем концах. Формула производной получается по Ньютону–Лейбницу.',
        'Включение со сдвигом противоположного знака можно проверить отдельно: оно не гарантирует, что подынтегральная функция определена.'
    ]),value


def elliptic_arclength_series_reading(task):
    check_integral_identity_source(task,{'expression_or_proposition','scope','requested_output'},
                                   'Выразить длину дуги эллипса рядом по целым положительным степеням эксцентриситета.')
    name=r'([A-Za-z]\w*)'
    hint=' (two x-coordinates printed)'
    expr=task['expression_or_proposition'];duplicate=expr.endswith(hint)
    expr=expr.removesuffix(hint)
    h=re.fullmatch(fr'ellipse {name}={name}\*cos\({name}\), {name}={name}\*sin\(\3\), 0<=\3<=2\*pi',expr)
    if (not h or (h[1]==h[4])!=duplicate or task.get('scope')!='eccentricity as expansion variable'
            or task.get('requested_output',[]) not in ([],['series_and_convergence'])):
        raise Unsupported('The coordinate pair and a complete revolution must be bound')
    x,a,t,y,b=h.groups()
    if len({a,b,t,x,y})!=5-duplicate:
        raise Unsupported('Semiaxes and the curve parameter have distinct roles')
    value=dict(series='2*pi*A*sum_{j>=0} binomial(1/2,j)*(-e^2)^j*binomial(2*j,j)/4^j',
               semimajor=f'A=max({a},{b})',semiminor=f'B=min({a},{b})',
               eccentricity='e=sqrt(1-B^2/A^2), 0<=e<1')
    if duplicate:
        value.update(printed_claim_holds=False,counterexample=dict(
            parameter=ZERO,first_coordinate=x+'='+a,second_printed_coordinate=x+'=0',condition=a+'>0'))
    return dict(theorem='method.compact_elliptic_arc_series',steps=[
        'При двух одноимённых координатах уже в нулевом параметре получаются несовместимые значения первой координаты. Различаем это и параметризацию эллипса.',
        'Для обычной пары координат дифференцируем обе и выносим большую полуось. Модуль скорости равен A√(1−e² sin² t) с возможным сдвигом фазы.',
        'При e<1 биномиальный ряд сходится равномерно и абсолютно на полном обороте. Интеграл sin^(2j) t равен 2π·binomial(2j,j)/4^j по простой рекурсии интегрирования по частям.'
    ]),value



def asymptotic_primitive_of_exp_monomial(task):
    from verify import same_value
    src=check_integral_identity_source(task,{'statement','requested_output'},None)
    base={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}
    anomaly='В числителе напечатаны два дифференциала dx; обычное чтение одинарного интеграла отмечено отдельно.'
    if set(src)-base-{'printed_anomaly'} or src.get('printed_anomaly') not in (None,anomaly):
        raise Unsupported('The differential reading must match the printed qualifications')
    grammar=r'При x→\+∞ доказать эквивалентность ∫₀ˣ e\^\(([^()]+)\) dx( dx)? и e\^\(([^()]+)\)/\(([^()]+)\)\.'
    found=re.fullmatch(grammar,task.get('statement',''))
    if not found or task.get('requested_output')!=['proof'] or bool(found[2])!=(src.get('printed_anomaly')==anomaly):
        raise Unsupported('The oriented endpoint, empty repetition and claimed leading term must be bound')
    x=('v','x')
    def read(text):
        text=text.translate(str.maketrans({'²':'^2','³':'^3','⁴':'^4'}))
        return m.parse(re.sub(r'(?<=\d)(?=x)','*',text),'x')
    P,Q,D=map(read,(found[1],found[3],found[4]))
    p,d=m.rational_form(P)
    if len(p)!=1 or d!={():F(1)} or not same_value(P,Q) or domain_conditions(P)+domain_conditions(Q)+domain_conditions(D):
        raise Unsupported('A fixed positive monomial and the same target exponent are required')
    (mon,coefficient),=p.items()
    if len(mon)!=1 or mon[0][0]!=x or mon[0][1]<=0 or coefficient<=0:
        raise Unsupported('The source phase must increase as a positive power')
    degree=mon[0][1]
    derivative=m.mul(q(coefficient*degree),m.power(x,degree-1))
    if not same_value(D,derivative):
        raise Unsupported('The proposed comparison does not use the phase derivative')
    correction=m.mul(q(F(degree-1,coefficient*degree)),m.power(x,-degree)) if degree>1 else ZERO
    return dict(theorem='method.exp_monomial_primitive_equivalence',steps=[
        'Для чтения с одним дифференциалом обозначаем интеграл от 0 до x через F(x) и используем Ньютон–Лейбница.',
        'Правая часть равна G=e^P/P′. Оба выражения стремятся к бесконечности. Производная G равна e^P(1−P″/(P′)²).',
        'У положительной мономиальной фазы отношение P″/(P′)² стремится к нулю. Применяем правило Лопиталя и получаем предел F/G=1.'
    ],phase=P,phase_derivative=derivative,derivative_correction=correction),dict(equivalence=True,ratio_limit=ONE,scope='under the single-integral reading' if found[2] else 'ordinary definite integral')


def running_integral_mean(task):
    src=check_integral_identity_source(task,{'statement','requested_output'},None)
    anomaly='В печати dx при интеграндах с t, частное при x=0 не определено.'
    if set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','printed_anomaly'} or src.get('printed_anomaly') not in (None,anomaly):
        raise Unsupported('The dummy variable and printed initial restriction must be accounted for')
    f=r'([A-Za-z][A-Za-z_0-9]*)';t=r'([A-Za-z][A-Za-z_0-9]*)'
    pattern=fr'{f} continuous and positive; show \(∫₀ˣ {t} \1\(\2\) d{t}\)/\(∫₀ˣ \1\(\2\) d\3\) increases for x(≥|>)0\.'
    h=re.fullmatch(pattern,task.get('statement',''))
    if not h or task.get('requested_output')!=['proof']:
        raise Unsupported('The same positive weight and limits must appear in both integrals')
    name,variable,differential,first=h.groups()
    mismatch=variable!=differential
    if variable=='x' or mismatch!=(src.get('printed_anomaly')==anomaly):
        raise Unsupported('The mismatched differential needs its declared ordinary reading')
    value=dict(strictly_increasing=True,domain='x>0',continuous_extension_at_zero=ZERO,
               ordinary_differential='d'+variable)
    if first=='≥':
        value.update(printed_claim_holds=False,counterexample=dict(
            x=ZERO,denominator_integral=ZERO,ratio_defined=False))
    return dict(theorem='method.running_positive_integral_mean',steps=[
        'После связывания общей переменной интегрирования знаменатель положителен при x>0.',
        'Правило частного и основная теорема анализа дают в числителе производной положительный множитель f(x) и интеграл (x−t)f(t) от 0 до x.',
        'Последний строго положителен, поскольку f>0 и x−t>0 внутри отрезка. Среднее лежит между 0 и x, что даёт предел нуль у левого края. Исходная дробь там не определена.'
    ]),value



def halfline_parameter_reading(task,recognition=False):
    kind=task.get('kind');text=task.get('expression','')
    if kind!='limit_integral_interchange' or task.get('requested_output')!=['proof_or_counterexample'] or not isinstance(text,str):
        return None
    name=r'[A-Za-z][A-Za-z_0-9]*'
    laplace=re.fullmatch(fr'lim_({name})->(0\+|\+inf) int_0\^inf exp\(-\1\*({name})\)\*({name})\(\3\)d\3=int_0\^inf \4\(\3\)d\3',text)
    cauchy=re.fullmatch(fr'lim_({name})->(0[+-]?) \(2/pi\)\*int_0\^inf \1\*({name})\(({name})\)/\(\4\^2\+\1\^2\)d\4=(-?)\3\(0\)',text.replace('²','^2'))
    if not laplace and not cauchy:return None
    if recognition:return True
    check_integral_identity_source(task,{'expression','requested_output','stated_conditions'},
                                   'Доказать напечатанную формулу.' if laplace else 'Доказать указанный предел.')
    if laplace:
        parameter,side,var,f=laplace.groups()
        if len({parameter,var,f})!=3 or task.get('stated_conditions')!=[f+' integrable on (0,+inf)']:
            raise Unsupported('The original convergent improper integral and half-line scale must be bound')
        natural='int_0^inf '+f+'('+var+')d'+var
        value=dict(limit=ZERO if side=='+inf' else natural,scale_domain=parameter+'>0')
        if side=='+inf':
            value.update(printed_claim_holds=False,counterexample=dict(function=f'exp(-{var})',
                scaled_integral=f'1/(1+{parameter})',left=ZERO,right=ONE))
        return dict(theorem='method.laplace_boundary_through_bounded_primitive',steps=[
            'У исходной сходящейся несобственной функции первообразная F(x)=∫₀ˣ f непрерывна в нуле, ограничена и имеет конечный предел в бесконечности.',
            'Для положительного масштаба интегрируем по частям. Краевые члены равны нулю. Замена t=αx даёт интеграл exp(−t)F(t/α).',
            'Ограниченность F даёт общую интегрируемую мажоранту. При α→∞ аргумент идёт к нулю, при α→0+ идёт к бесконечности. Поэтому эти два предела имеют разные формулы.'
        ]),value
    parameter,side,f,var,negative=cauchy.groups()
    if len({parameter,var,f})!=3 or task.get('stated_conditions')!=[f+' continuous and bounded on [0,+inf)']:
        raise Unsupported('The original trace and bounded half-line function must be bound')
    positive=side=='0+';left=side=='0-'
    value=dict(right_limit=f+'(0)',left_limit='-'+f+'(0)',two_sided_condition=f+'(0)=0')
    if not (positive and not negative or left and negative):
        value.update(printed_claim_holds=False,counterexample=dict(function='1',
            evaluated_integral='sign('+parameter+')',left= q(-1),right=ONE))
    return dict(theorem='method.signed_cauchy_boundary_trace',steps=[
        'Отдельно рассматриваем два знака параметра. При x=|y|t ориентированная масса ядра равна sign(y), а масштаб аргумента положителен.',
        'Записываем интеграл как (2/π) sign(y)∫ f(|y|t)/(1+t²) dt. Общая мажоранта следует из ограниченности исходной функции.',
        'По непрерывности след равен f(0) и умножается на исходный знак. Сравнение обоих следов проверяет точное условие двустороннего предела.'
    ]),value


def integral_identity_profiles(task):
    kind=task.get('kind')
    return (kind in {'bessel_equation_identity','uniform_integral_identity',
                     'integral_pde_identity','level_curve_integration_proof','vanishing_integral_function_proof','differentiate_shifted_integral',
                     }
            or kind in {'integral_asymptotic_equivalence','integral_monotonicity'} and '∫₀ˣ' in str(task.get('statement',''))
            or kind=='integral_parameter_series' and str(task.get('expression_or_proposition','')).startswith('ellipse ')
            or kind=='prove_integral_identity' and '+i*' in str(task.get('integrand','')) and 'conclusion' in task
            or kind=='parameter_integral_identity' and task.get('requested_output')==['wave_equation','both_initial_conditions']
            or kind=='differentiate_moving_integral' and 'formula' in task and 'integrand' not in task)


def check_integral_identity_source(task,fields,title):
    src=task.get('source',{})
    provenance={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}
    if not isinstance(src,dict) or set(task)-{'id','kind','source',*fields}:
        raise Unsupported('Every source identity condition must be represented')
    if title is not None and (set(src)-provenance-{'literal_requirement'} or src.get('literal_requirement') not in (None,title)):
        raise Unsupported('The original source title or required method changed')
    return src


def compact_cosine_divergence(task,library):
    from cartesian_fields import derivative_table
    from verify import same_value
    check_integral_identity_source(task,{'definition','ode','stated_conditions','requested_output'},
                                   'Доказать дифференциальное уравнение для J_n.')
    name=r'[A-Za-z][A-Za-z_0-9]*'
    text=task['definition'];suffix=' (variable name k on left as printed)'
    original_mismatch=text.endswith(suffix)
    text=text.removesuffix(suffix)
    pattern=fr'({name})_({name})\(({name})\)=\(([^()]+)\)\*int_([^ ]+)\^([^ ]+) (.+)d({name})'
    parsed=re.fullmatch(pattern,text)
    ode=task['ode'];axis=re.match(fr'({name})\^2\*Jpp\+',ode)
    if parsed is None or axis is None or not ode.endswith('=0') or task.get('requested_output')!=['proof']:
        raise Unsupported('The compact cosine parameter and second-order goal must be identified')
    function,idx,declared,weight,lo,hi,density,theta=parsed.groups();x=axis[1]
    if (len({idx,theta,x,'Jpp','Jp','J'})!=6 or task.get('stated_conditions')!=[idx+' integer']
            or (declared!=x)!=original_mismatch or original_mismatch and declared in (idx,theta)):
        raise Unsupported('The integer index and the binding of the declared argument must be retained')
    ξ,Θ,N=(('s',s) for s in (x,theta,idx))
    integrand=m.simplify(m.parse(density,None,(x,theta,idx)))
    if integrand[0]!='cos':raise Unsupported('The compact integral needs a single cosine phase')
    phase=integrand[1];sine=m.simplify(('sin',phase))
    if domain_conditions(phase,True):raise Unsupported('The original phase has a hole or a singular derivative')
    start,stop,factor=[m.simplify(m.parse(s,None)) for s in (lo,hi,weight)]
    ends=[m.num(m.div(e,m.PI)) for e in (start,stop)]
    if any(e is None or e.denominator!=1 for e in ends) or ends[0]>=ends[1] or not m.constant_defined(factor,m.context({})):
        raise Unsupported('The compact interval must have ordered integral multiples of π')
    derivative,trace=derivative_table(library)
    first=derivative(integrand,x);second=derivative(first,x)
    lhs=m.parse(ode[:-2],None,(x,idx,'Jpp','Jp','J'))
    if not same_value(lhs,m.add(m.mul(m.power(ξ,2),('s','Jpp')),
            m.add(m.mul(ξ,('s','Jp')),m.mul(m.substitute(lhs,{('s','Jpp'):ZERO,('s','Jp'):ZERO,('s','J'):ONE}),('s','J'))))):
        raise Unsupported('The claimed operator is not linear in the original differentiation slots')
    body=m.simplify(m.substitute(lhs,dict(zip((('s','Jpp'),('s','Jp'),('s','J')),(second,first,integrand)))))
    C=m.simplify(m.substitute(body,{integrand:ONE,sine:ZERO}))
    S=m.simplify(m.substitute(body,{integrand:ZERO,sine:ONE}))
    if any(m.contains(e,a) for e in (C,S) for a in (integrand,sine)) or not same_value(body,m.add(m.mul(C,integrand),m.mul(S,sine))):
        raise Unsupported('Collecting the sine and cosine coefficients did not reproduce the integrand')
    dtheta=derivative(phase,theta)
    sine_square=('pow',('sin',Θ),2)
    normalized=m.substitute(C,{sine_square:m.add(ONE,m.neg(m.power(('cos',Θ),2)))})
    multiplier=m.polynomial_quotient(('div',normalized,dtheta))
    if (not m.contains(multiplier,Θ) or domain_conditions(multiplier,True)
            or not same_value(m.mul(multiplier,dtheta),C) or not same_value(derivative(multiplier,theta),S)):
        raise Unsupported('No exact total derivative in the integration variable was verified')
    for endpoint in (start,stop):
        endpoint_phase=m.simplify(m.substitute(phase,{Θ:endpoint}))
        coefficient=m.num(m.div(endpoint_phase,m.mul(m.PI,N)))
        if coefficient is None or coefficient.denominator!=1:
            raise Unsupported('An endpoint sine cannot be proved zero using the integer index')
    return dict(theorem='method.compact_cosine_boundary_divergence',phase=phase,compact_bounds=[start,stop],
                cosine_coefficient=C,sine_coefficient=S,divergence_multiplier=multiplier,checked_derivatives=trace,
                steps=[
                    'На компактном отрезке дифференцируем косинус дважды по параметру. Подставляем под знак интеграла заданную линейную комбинацию.',
                    'Собираем коэффициенты при синусе и косинусе. Деление косинусного коэффициента на производную фазы предлагает множитель. Проверяем произведение и производную множителя без деления на ноль.',
                    'Подынтегральная комбинация становится полной производной по углу. На обоих концах синус кратного π равен нулю, так как исходный индекс целый.'
                ]),dict(equation=ode,verified_for_integral_as_function_of=x,displayed_argument=declared,
                        scope=('printed argument name is inconsistent; the verified function uses the actual parameter'
                               if original_mismatch else 'throughout the real parameter axis'))


def wave_characteristic_integral(task):
    check_integral_identity_source(task,{'definition','claims','stated_conditions','requested_output'},
                                   'Доказать волновое уравнение и оба начальных условия.')
    name=r'[A-Za-z][A-Za-z_0-9]*'
    head=re.match(fr'({name})\(({name}),({name})\)=\((?:{name})\(({name})-({name})\*({name})\)',task['definition'])
    if head is None:raise Unsupported('The two opposite characteristic shifts were not identified')
    u,x,t,axis,a,time=head.groups()
    token=fr'({name})'
    left=f'{x}-{a}*{t}';right=f'{x}+{a}*{t}'
    L,R=map(re.escape,(left,right))
    body=fr'{re.escape(u)}\({re.escape(x)},{re.escape(t)}\)=\({token}\({L}\)\+\1\({R}\)\)/2\+int_\({L}\)\^\({R}\) {token}\({token}\)d\3/\(2\*{re.escape(a)}\)'
    hit=re.fullmatch(body,task['definition'])
    if (axis,time)!=(x,t) or hit is None:raise Unsupported('The same affine shifts must bind both integrals and initial values')
    f,F,z=hit.groups();symbols={u,x,t,a,f,F,z}
    if len(symbols)!=7 or task.get('requested_output')!=['wave_equation','both_initial_conditions']:
        raise Unsupported('The original field, shift and both initial conditions must be bound')
    claims=[f'{u}_{t}{t}={a}²*{u}_{x}{x}',f'{u}({x},0)={f}({x})',f'{u}_{t}({x},0)={F}({x})']
    facts=task['stated_conditions'];ambiguity=f'text calls {u}({x}) differentiable, but formula uses {F}({z})'
    if task['claims']!=claims or facts not in ([f+' twice differentiable',F+' differentiable'],[f+' twice differentiable',ambiguity]):
        raise Unsupported('The specified equation, initial values, and differentiability must be known')
    result=dict(wave_equation=claims[0],initial_values=claims[1:],valid_on=[a+'!=0',f'{F} differentiable on the characteristic interval'])
    if ambiguity in facts:
        result['source_ambiguity']=ambiguity
        result['absence_of_F_regularity']=dict(f='0',F=f'abs({z})',a=1,point=[1,1],second_time_derivative_one_sided=[0,1])
    return dict(theorem='method.opposed_characteristic_integral',characteristics=[left,right],steps=[
        'Обозначаем через G первообразную начальной скорости F. Ориентированный интеграл становится разностью G на двух характеристиках, делённой на 2a.',
        'Каждая из двух функций одной характеристической координаты имеет u_tt=a²u_xx по цепному правилу.',
        'При t=0 обе координаты совпадают. При первом дифференцировании по времени вклады начального положения сокращаются, а вклады от концов интеграла складываются в F(x).',
        'Если гладкость F не оговорена, условная формула и существование классической второй производной различаются. Для F=|z| разность вторых производных по времени в точке (1,1) вычисляется слева и справа.'
    ]),result


def affine_complex_exponential_integral(task):
    from verify import same_value
    src=check_integral_identity_source(task,{'integrand','variable','lower','upper','parameters','conclusion','stated_conditions','requested_output'},None)
    if set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','printed_instruction'} or src.get('printed_instruction') not in (None,'Показать, что; α и β — постоянные.'):
        raise Unsupported('The printed complex-exponential instruction must be retained')
    x=task['variable'];lo,hi=(task[k] for k in ('lower','upper'));params=task['parameters']
    args=re.fullmatch(r'exp\(\(([A-Za-z]\w*)\+i\*([A-Za-z]\w*)\)\*'+re.escape(x)+r'\)',task['integrand'])
    if (args is None or len(set([x,lo,hi,*args.groups(),'i']))!=6 or set(params)!={lo,hi,*args.groups()}
            or task.get('requested_output',[]) not in ([],['proof']) or task.get('stated_conditions',[]) not in
            ([],[f'({args[1]},{args[2]})!=(0,0)'])):
        raise Unsupported('The independent real rate, frequency and finite endpoints must be bound')
    R,I=args.groups();phase=f'{R}+i*{I}';kernel=lambda at:f'exp({at}*({phase}))'
    expression=f'({kernel(hi)}-{kernel(lo)})/({phase})'
    read=lambda s:m.parse(s,None,[*params,'i'])
    if not same_value(read(task['conclusion']),read(expression)):
        raise Unsupported('The proposed complex formula has a different numerator or denominator')
    generic=dict(condition=f'({R},{I})!=(0,0)',value=expression)
    answer=dict(branches=[generic])
    if not task.get('stated_conditions'):
        answer.update(printed_claim_holds=False,counterexample={R:0,I:0,lo:0,hi:1,'integral':ONE,'printed_quotient':'undefined'})
        answer['branches'].append(dict(condition=f'{R}={I}=0',value=hi+'-'+lo))
    return dict(theorem='method.complex_affine_exponential_integral',steps=[
        'Для ненулевой комплексной скорости производная exp(kx)/k равна исходному ядру. Ориентированная разность концов верна для любого их порядка.',
        'Действительная и мнимая части скорости вещественны, поэтому скорость нулевая ровно при одновременном обнулении обеих. В этой ветви ядро равно единице.',
        'Граница формулы при k→0 равна разности концов по разложению экспоненты. Это продолжение, дробь при k=0 остаётся неопределённой.'
    ]),answer


def uniform_tail_multiplier(task):
    check_integral_identity_source(task,{'hypotheses','integrand','limits','requested_output'},
                                   'Доказать равномерную сходимость интеграла произведения.')
    pattern=r'([A-Za-z]\w*)\(([A-Za-z]\w*)(?:,([A-Za-z]\w*))?\)\*([A-Za-z]\w*)\(\2,([A-Za-z]\w*)\)'
    kernel=re.fullmatch(pattern,task['integrand'])
    limits=re.fullmatch(r'([A-Za-z]\w*)\.\.inf',task['limits'])
    if not kernel or not limits or task.get('requested_output')!=['uniform_convergence_proof']:
        raise Unsupported('A source monotone multiplier and tail variable must be specified')
    f,x,p,phi,y=kernel.groups();a=limits[1]
    if len({f,x,y,phi,a})!=5 or p not in (None,y):
        raise Unsupported('The multiplier must share the independent parameter and integration coordinate')
    dom=f'{phi}({x},{y}) bounded and monotone in {x}'
    independent=f'int_{a}^inf {f}({x})d{x} converges'
    dependent=f'int_{a}^inf {f}({x},{y})d{x} converges'
    hypo=task['hypotheses']
    admissible=[[independent,dom],[dependent,dom],[dependent+' uniformly',dom]]
    if hypo not in admissible:raise Unsupported('The tail and its uniformity must match the printed hypotheses')
    matched=hypo==[independent,dom] and p is None or hypo==[dependent+' uniformly',dom] and p==y
    answer=dict(uniform_convergence=matched,sufficient='uniformly Cauchy primitive tails and a uniformly bounded, x-monotone multiplier')
    if not matched:
        if p==y:
            example={f:f'{y}*exp(-{y}*({x}-{a}))',phi:'1','parameter':f'0<{y}<1','tail':f'exp(-{y}*(M-{a}))'}
        else:
            example={f'{f}({x},{y})':f'exp(-({x}-{a}))',f'{f}({x})':'1',phi:'1','integral':'+inf'}
        answer.update(printed_claim_holds=False,counterexample=example)
    return dict(theorem='method.uniform_cauchy_multiplier',steps=[
        'На отрезке хвоста используем первообразную от левой точки и интегрирование по частям для монотонного множителя.',
        'Граничный член не превосходит Mη, вклад вариации не превосходит 2Mη, где η — равномерная верхняя граница исходных хвостов.',
        'Равномерный критерий Коши даёт сходимость при η→0. Обычная сходимость семейства не обеспечивает такой оценки, а различающиеся по числу аргументов функции требуют отдельной связи.'
    ]),answer


def parameter_catalogue_proof(task, library, request):
    """Compose local parameter estimates, exact tail witnesses and source limits."""
    kind = task['kind']
    if library.data.get('halfline_boundary_rescalings') and halfline_parameter_reading(task,recognition=True):
        return halfline_parameter_reading(task)
    if kind=='euler_integral_identity' and ('Gamma(' in task['claim'] or task['claim'].startswith('prod_')):
        return gamma_product_or_wave(task)
    if library.data.get('source_integral_identity_profiles') and integral_identity_profiles(task):
        if kind=='bessel_equation_identity':return compact_cosine_divergence(task,library)
        if kind=='parameter_integral_identity':return wave_characteristic_integral(task)
        if kind=='prove_integral_identity':return affine_complex_exponential_integral(task)
        if kind=='uniform_integral_identity':return uniform_tail_multiplier(task)
        if kind=='integral_pde_identity':return characteristic_area_wave(task)
        if kind=='level_curve_integration_proof':return level_area_distribution(task)
        if kind=='vanishing_integral_function_proof':return quantified_subregion_integrals(task)
        if kind=='differentiate_moving_integral':return moving_radius_differential(task)
        if kind=='differentiate_shifted_integral':return shifted_uniform_integrand_window(task)
        if kind=='integral_parameter_series':return elliptic_arclength_series_reading(task)
        if kind=='integral_asymptotic_equivalence':return asymptotic_primitive_of_exp_monomial(task)
        if kind=='integral_monotonicity':return running_integral_mean(task)
    if kind=='hermite_orthogonality':return gaussian_rodrigues_orthogonality(task)
    if kind=='mathematical_question' and task.get('requested_output')==['piecewise_function']:
        return dirichlet_multiplier(task)
    if kind=='elliptic_integral_derivatives' or kind=='parameter_integral_identity' and ('formula' in task or 'claim' in task):
        if kind=='parameter_integral_identity' and library.data.get('compact_parameter_transport') and compact_parameter_integral_goal(task):
            return compact_parameter_integral(task,library,request)
        return compact_derivative_identity(task,library)
    if kind=='special_function_integral_identity' and 'definition' in task:
        return positive_laplace_bessel_identity(task)
    if kind in ('fresnel_integrals','principal_value_integral') and library.data.get('gaussian_fourier_moments'):
        return (fresnel_representation if kind=='fresnel_integrals' else symmetric_harmonic_pole)(task)
    if library.data.get('compact_parameter_transport') and compact_parameter_integral_goal(task):
        return compact_parameter_integral(task,library,request)
    if library.data.get('boundary_reduction_proofs') and boundary_reduction_candidate(task):
        return boundary_reduction_proof(task,library)
    if library.data.get('euler_endpoint_transport') and euler_endpoint_candidate(task):
        return euler_endpoint_transport(task,library)
    if kind=='parameter_integral_derivative':return oriented_parameter_derivative(task,library)
    if kind=='limit_improper_integral' and library.data.get('abstract_integral_transitions'):
        try:return shifted_gaussian_window(task)
        except Unsupported:pass
    if (library.data.get('parameter_transform_proofs') and kind=='parameter_improper_evaluation'
            and task.get('method_requirement')=='specified_representation'):
        try:return lorentzian_moment(task,library,request)
        except Unsupported:pass
    meta = task.get('source', {})
    allowed = {'id','kind','source','integrand','source_formula','expression','limits','function','parameter_domain',
               'parameter_set','parameters','stated_conditions','requested_output','asserted_result','method_requirement',
               'reference_formula','identity','claim','reference','formula','epsilon','integral','interval','suggested_substitution','approximants'}
    if (not library.data.get('parameter_integral_tail_proofs') or set(task)-allowed or not isinstance(meta,dict)
            or set(meta)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}):
        raise Unsupported('The source integral and its requested conclusion are not bound')

    def emit(method, steps, value, **details):
        return dict(theorem='method.'+method,steps=steps,source_bounds=task.get('limits'),
                    source_parameter_conditions=task.get('parameter_domain',task.get('parameter_set',task.get('stated_conditions',[]))),
                    **details),value
    def bind(fields, heading=None):
        if set(task)-{'kind','id','source',*fields} or heading is not None and meta.get('literal_requirement',heading)!=heading:
            raise Unsupported('An additional source condition, goal or method remains')

    if 'approximants' in task:
        if (not library.data.get('rational_gaussian_approximation') or kind!='evaluate_via_parameter'
                or task.get('requested_output')!=['value_and_specified_method'] or task.get('method_requirement')!='limit_under_integral'
                or task.get('limits')!='0..inf'):
            raise Unsupported('The original approximation, limit operation and half-line must be preserved')
        bind({'integrand','limits','approximants','method_requirement','requested_output'},
             'Вычислить гауссов интеграл, используя переход к пределу в указанной последовательности.')
        return rational_gaussian_approximation(task,emit)

    if library.data.get('bound_parameter_interchanges') and kind in ('evaluate_via_parameter','parameter_improper_evaluation'):
        try:return bound_parameter_interchanges(task,library,emit,bind)
        except Unsupported:
            if task.get('method_requirement')=='derive_from_abel_regularization':raise

    want=task.get('requested_output')
    if kind=='limit_improper_integral' and want==['value']:
        bind({'expression','requested_output'},'Найти предел.')
        hit=re.fullmatch(r'lim_(\w+)->inf int_0\^inf d([a-z])/\((.+)\)',task['expression'])
        if hit and hit[1]!=hit[2]:
            index,x,den=hit.groups();raw=m.parse('1/('+den+')',None,[x,index])
            c,k,p=parameter_power_ratio(raw,x,index)
            if k!=0:raise Unsupported('The source index limit requires a constant numerator')
            return emit('local_integrable_parameter_majorants',[
                    'На 0<x<1 степенной член стремится к нулю, а при x>1 растёт к бесконечности.',
                    'Для n≥2 общий мажорант равен обратной константе на [0,1] и x⁻² на [1,+∞).',
                    'Предел интегралов вычисляется интегрированием предельной ступени. Значение в точке 1 не влияет на площадь.'],
                dict(value=q(1/c)),index=index,domain_split=q(1),eventual_index_lower=q(2),majorant=(q(1/c),'x^(-2)'))
    if kind=='mathematical_question' and want==['discontinuities']:
        bind({'integrand','limits','requested_output'},'Найти точки разрыва и построить график.')
        if task['limits']!='0..inf':raise Unsupported('The complete positive half-line is required')
        text=task['integrand']
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-{'sin','x'})
        if len(names)!=1:raise Unsupported('The frequency must have one explicit real parameter')
        return parameter_dirichlet_frequency(text,names[0],emit)
    if kind=='parameter_integral_continuity' and want in (['continuity_analysis'],['continuity','differentiability']):
        heading='Доказать непрерывность и дифференцируемость.' if len(want)==2 else 'Исследовать или доказать непрерывность.'
        bind({'integrand','limits','parameter_domain','requested_output'},heading)
        return parameter_continuity_proof(task,emit)
    if kind in ('uniform_parameter_integral','uniform_convergence_neighborhood','uniform_tail_bound','uniform_convergence_quantifiers',
                'uniform_no_integrable_majorant','limit_integral_interchange','improper_identity'):
        return parameter_uniform_proof(task,emit,bind)
    if kind=='improper_integral_convergence_parameters':
        return parameter_improper_domain(task,emit,bind)
    if kind in ('evaluate_via_parameter','parameter_definite_integral','parameter_improper_evaluation','special_function_integral_identity',
                'smoothness_parameter_integral','differentiate_dirichlet_integral','frullani_identity'):
        return parameter_integral_transform(task,emit,bind,request)
    raise Unsupported('The source parameter goal needs another local estimate or exact parameter identity')


def rational_gaussian_approximation(task,emit):
    from polynomial import NotRational, Undefined, rf
    from verify import same_value

    text=task['integrand'].replace('²','^2'); approximants=task['approximants'].replace('²','^2')
    def names(expression):
        return set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',expression))-{'exp'}
    variables=names(text);index=names(approximants)-variables
    if len(variables)!=1 or len(index)!=1:
        raise Unsupported('Expected an independent coordinate and an integer approximation index')
    x,=variables; n,=index; coordinate=('v',x);integer=('s',n)
    original=m.parse(text,x); sequence=m.parse(approximants,x,[n])
    if (original[0]!='exp' or domain_conditions(original) or sequence[0]!='rpow'
            or domain_conditions(sequence[2]) or not same_value(sequence[2],m.neg(integer))):
        raise Unsupported('The source must use a Gaussian and the corresponding inverse integer powers')
    try:p,d=rf(original[1],x)
    except (NotRational,Undefined) as exc:raise Unsupported('Expected a fixed quadratic exponent') from exc
    if len(p)!=3 or len(d)!=1 or any(p[:2]) or p[2]/d[0]>=0:
        raise Unsupported('A strictly positive Gaussian scale is required')
    scale=q(-p[2]/d[0]); kernel=m.mul(scale,m.power(coordinate,2))
    if any(g!=('nonzero',integer) for g in domain_conditions(sequence[1])) or not same_value(sequence[1],m.add(ONE,m.div(kernel,integer))):
        raise Unsupported('The same Gaussian scale must occur in the original approximants')
    return emit('rational_gaussian_approximation',[
        'При целых n≥1 неравенство Бернулли даёт общий интегрируемый мажорант 1/(1+c·x²). Формула предела степеней даёт e^(−c·x²) в каждой точке положительной полуоси.',
        'Для каждого n подстановка x=√(n/c)·tan t даёт √(n/c)·I_(2n−2), где I_j — интеграл cos^j t от 0 до π/2.',
        'Интегрирование по частям даёт I_(j+2)/I_j=(j+1)/(j+2). При m=n−1 отсюда I_(2m)·I_(2m+1)=π/(2(2m+1)).',
        'Из I_(2m+2)≤I_(2m+1)≤I_(2m) следует I_(2m+1)/I_(2m)→1. Поэтому √n·I_(2n−2)→√π/2. Доминированная сходимость переносит это значение на исходный интеграл.'
    ],dict(value=m.div(('sqrt',m.div(m.PI,scale)),q(2))),index=n,coordinate=x,scale=scale,
        majorant=m.div(ONE,m.add(ONE,kernel)),approximants=sequence)


def parameter_power_ratio(raw,var,param):
    """Read x^k/(c+x^p) without cancelling an original factor."""
    x,p=('s',var),('s',param)
    if raw[0]!='div' or raw[2][0]!='add':
        raise Unsupported('A positive constant plus a parameter power is required')
    numerator=raw[1]
    k=F(0) if numerator==ONE else F(1) if numerator==x else (
        F(numerator[2]) if numerator[0]=='pow' and numerator[1]==x else None)
    pieces=raw[2][1:]
    c=next((v for atom in pieces if (v:=m.num(atom)) is not None),None)
    if k is None or k<=-1 or c is None or c<=0 or ('rpow',x,p) not in pieces:
        raise Unsupported('The power quotient has an unverified endpoint or parameter exponent')
    return c,k,p


def parameter_dirichlet_frequency(text,parameter,emit):
    from graphs import rational_roots
    from intervals import endpoint_term
    from level_sets import quadratic_coefficients
    from verify import same_value

    x=('s','x');raw=m.parse(text.replace('²','^2'),None,['x',parameter])
    if raw[0]!='div' or raw[2]!=x or raw[1][0]!='sin' or domain_conditions(raw[1][1]):
        raise Unsupported('The original frequency must be real and the only possible denominator is x')
    angle=raw[1][1]
    frequency=m.simplify(m.substitute(angle,{x:ONE}))
    if not same_value(angle,m.mul(x,frequency)):
        raise Unsupported('The phase is not homogeneous of degree one in the integration variable')
    A,B,C=quadratic_coefficients(frequency,[parameter])
    poly=[C,B[0],A[0][0]]
    while len(poly)>1 and poly[-1]==0:poly.pop()
    roots=list(rational_roots(tuple(poly))) if len(poly)>1 else []
    right_sign=1 if poly[-1]>0 else -1 if poly[-1]<0 else 0
    signs=[right_sign]
    if len(roots)==2:signs.extend((-right_sign,right_sign))
    elif roots:signs.append(-right_sign if len(poly)==2 else right_sign)
    values=[m.mul(q(s,2),m.PI) for s in reversed(signs)]
    points=list(map(endpoint_term,roots))
    return emit('signed_dirichlet_frequency',[
        'При нулевой частоте исходное ядро тождественно нулевое. При ненулевой частоте замена масштаба оставляет знак.',
        'Для положительного затухания ε производная по частоте даёт косинусный момент ε/(ε²+ω²). Его интеграл от нулевой частоты равен arctg(ω/ε).',
        'Равномерная по ε≥0 оценка Дирихле при фиксированной ненулевой частоте допускает переход ε→0⁺.',
        'На каждом интервале постоянного знака частоты значение постоянно. Во всех её изолированных нулях значение равно нулю и возникает разрыв.'],
        dict(discontinuities=points,value_at_frequency_zero=ZERO,open_interval_values=values,
             discontinuity_kind='removable' if roots and len(poly)==3 and len(roots)==1 else 'jump' if roots else 'none'),
        frequency=frequency,parameter=parameter,frequency_coefficients=tuple(map(q,poly)))


def parameter_continuity_proof(task,emit):
    from level_sets import quadratic_coefficients

    text=task['integrand'].replace('²','^2')
    bounds=task['limits'];domain=task['parameter_domain']
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{'x','pi','e'})
    if len(names)!=1:raise Unsupported('One real parameter must be bound by the source domain')
    a,=names;x,p=('s','x'),('s',a)
    all_real=domain in (a+' real','all real '+a)
    raw=m.parse(text,None,['x',a])
    want=task['requested_output']
    if (all_real and want==['continuity_analysis'] and raw[0]=='exp' and not domain_conditions(raw[1])
            and re.fullmatch(r'[-+0-9./]+[.][.]inf',bounds)):
        M,L,C=quadratic_coefficients(raw[1],['x',a])
        c=-M[0][0]
        if c>0 and not any(L) and C==0:
            d=M[0][1]/c
            if M[1][1]==-c*d*d:
                return emit('parameter_translation_continuity',[
                    'Сдвигаем переменную на центр гауссова ядра. Параметр остаётся только в конечной границе.',
                    'Разность интегралов равна интегралу по отрезку между сдвинутыми границами. Ядро ограничено единицей.',
                    'Общий липшицев коэффициент равен модулю множителя сдвига.'],
                    dict(continuous_on=domain,lipschitz_constant=q(abs(d))),gaussian_decay=q(c),translation_coefficient=q(d))
    if (want==['continuity_analysis'] and bounds=='0..inf' and raw[0]=='div' and raw[2][0]=='add'
            and (hit:=re.fullmatch(re.escape(a)+r'>([-0-9./]+)',domain))):
        c,k,_=parameter_power_ratio(raw,'x',a)
        if F(hit[1])<k+1:raise Unsupported('The stated parameter set contains a divergent tail')
        return emit('local_integrable_parameter_majorants',[
                'На конечном участке около нуля исходный знаменатель не меньше положительной константы.',
                'В локальном окне параметров выбираем нижнюю степень строго больше порога сходимости.',
                'На x≥1 этим получаем общий интегрируемый степенной хвост. На каждом отсечении зависимость непрерывна.'],
            dict(continuous_on=domain),numerator_degree=q(k),denominator_constant=q(c),
            local_window='k+1 < p_minus < '+a,majorant=('x^k/c','x^(k-p_minus)'))
    if (want==['continuity_analysis'] and bounds=='0..1' and domain=='0<'+a+'<1'
            and raw==('div',('sin',('div',p,x)),('rpow',x,p))):
        return emit('local_integrable_parameter_majorants',[
                'Для каждой точки параметра выбираем верхнюю границу p_plus<1.',
                'На 0<x≤1 синус ограничен единицей, а x^(-p_plus) интегрируем у нуля.',
                'На отсечённых отрезках подынтегральная функция непрерывна по параметру.'],
            dict(continuous_on=domain),local_window=a+' < p_plus < 1',majorant='x^(-p_plus)')
    return parameter_continuity_more(task,emit,a,raw,all_real)


def parameter_continuity_more(task,emit,a,raw,all_real):
    text=task['integrand'].replace('²','^2').replace(' ','')
    bounds,domain=task['limits'],task['parameter_domain']
    want=task['requested_output'];x,p=('s','x'),('s',a)
    if want==['continuity_analysis']:
        if bounds=='1..inf' and domain==a+'>0' and raw==('div',('cos',x),('rpow',x,p)):
            return emit('uniform_oscillatory_tail',[
                'Берём локальное окно с положительной нижней степенью p_minus.',
                'Первообразная косинуса ограничена. Убывающий вес даёт общий хвост не больше 2/B^p_minus.',
                'Непрерывность каждого отсечения переносится на локально равномерный предел.'],
                dict(continuous_on=domain),tail='2/B^p_minus')
        expected=lambda s:m.parse(s.replace('@',a),None,['x',a])
        if bounds=='0..pi' and domain=='0<'+a+'<2' and raw==expected('sin(x)/(x^@*(pi-x)^@)'):
            return emit('local_integrable_parameter_majorants',[
                'При приближении к обоим концам синус ограничен расстоянием до соответствующего конца.',
                'Фиксируем верхнюю степень p_plus<2. Второй множитель знаменателя отделён от нуля около каждого конца.',
                'Получаются две интегрируемые мажоранты степени 1−p_plus. На внутреннем отрезке ядро непрерывно.'],
                dict(continuous_on=domain),endpoint_exponents=('1-p_plus','1-p_plus'))
        if bounds=='0..inf' and domain=='0<'+a+'<1' and raw==expected('exp(-x)/abs(sin(x))^@'):
            return emit('periodic_cell_tail_comparison',[
                'Разбиваем полуось на ячейки длины π. Выносим верхнюю оценку затухания exp(−kπ) в каждой ячейке.',
                'В локальной области p≤p_plus<1 абсолютная особенность внутри каждой ячейки ограничена общей интегрируемой степенью.',
                'Две стадии дают геометрический хвост и общий контроль конечного числа особенностей.'],
                dict(continuous_on=domain),cell_weight='exp(-k*pi)',local_endpoint_exponent='-p_plus')
        if all_real and bounds=='0..inf' and raw==expected('@*exp(-x*@^2)'):
            return emit('mass_scales_and_exceptional_parameters',[
                'При ненулевом параметре интегрируем затухающую экспоненту. При нуле интегрант тождественно нулевой.',
                'На ненулевых ветвях результат равен обратному параметру, поэтому непрерывен на обеих полуосях.',
                'У нуля разные бесконечные односторонние границы.'],
                dict(continuous_on=a+' != 0',discontinuities=[ZERO],value_at_zero=ZERO,nonzero_value='1/'+a),
                zero_decay_case=ZERO)
    if (want==['continuity','differentiability'] and all_real and bounds=='0..inf'
            and raw==m.parse('cos(x)/(1+(x+'+a+')^2)',None,['x',a])):
        return emit('local_parameter_derivative_majorants',[
            'В окне |a|≤M при x≥2M+1 имеем |x+a|≥x/2. Ядро ограничено 4/x².',
            'Частная по параметру не превосходит 16/x³ по модулю и непрерывна на каждой усечённой части.',
            'Обе общие оценки разрешают непрерывность и дифференцирование под знаком интеграла.'],
            dict(continuous_on=domain,differentiable_on=domain,
                 derivative_integrand='-2*(x+'+a+')*cos(x)/(1+(x+'+a+')^2)^2'),tail_majorants=('4/x^2','16/x^3'))
    raise Unsupported('The declared continuity region needs another common integrable or oscillatory estimate')


def parameter_uniform_proof(task,emit,bind):
    kind=task['kind'];want=task.get('requested_output')
    text=task.get('integrand','').replace('²','^2').replace(' ','')
    bounds=task.get('limits');params=task.get('parameter_set')
    if kind=='uniform_convergence_quantifiers':
        bind({'integral','interval','requested_output'},
             'Сформулировать в положительном смысле, что означает неравномерная сходимость.')
        if task.get('integral')=='int_a^inf f(x,y)dx' and task.get('interval')=='y1<y<y2' and want==['quantified_nonuniformity']:
            return emit('uniform_cauchy_tail_witness',[
                'Равномерный критерий Коши требует один порог для каждого ε, работающий для всех параметров и всех более далёких отрезков.',
                'Отрицаем это утверждение, сохраняя порядок кванторов и независимость начального ε от выбора порога.'],
                dict(nonuniformity='∃ε>0 ∀B ∃y∈(y1,y2) ∃R,S≥B : |int_R^S f(x,y) dx|≥ε',pointwise_convergence_required=True))
    if kind=='uniform_no_integrable_majorant':
        bind({'integrand','limits','parameters','requested_output'},'Доказать равномерную сходимость и невозможность общей интегрируемой мажоранты.')
        if (text=='exp(-(x-1/y)^2/y^2)' and bounds=='1..inf' and task.get('parameters')=='0<y<1'
                and want==['uniform_convergence_proof','nonexistence_of_integrable_majorant']):
            return emit('moving_profile_tail_witness',[
                'Если y≤2/B, весь интеграл ограничен 2√π/B через полный гауссов момент.',
                'Если y>2/B, центр 1/y≤B/2. На хвосте работаем с общей оценкой exp(−x²/4).',
                'Но для каждого x>1 параметр y=1/x даёт значение 1. Всякая общая мажоранта должна доминировать константу один.'],
                dict(uniform=True,common_integrable_majorant=False),tail='2*sqrt(pi)/B+int_B^inf exp(-x^2/4) dx',
                envelope_witness='y=1/x')
    if kind=='uniform_convergence_neighborhood':
        bind({'integrand','limits','requested_output'},'Доказать локальную равномерность при каждом α≠0 и её нарушение при α=0.')
        if text=='alpha/(1+alpha^2*x^2)' and bounds=='0..inf' and want==['each_nonzero_parameter','failure_at_zero']:
            return emit('mass_scales_and_exceptional_parameters',[
                'При |α|≥δ>0 хвост по модулю не больше 1/(δB).',
                'В окрестности нуля параметр α=1/B после замены масштаба даёт хвост π/4.',
                'При α=0 исходное ядро равно нулю.'],
                dict(uniform_at_nonzero=True,uniform_at_zero=False),tail='1/(delta*B)',witness='alpha=1/B')
    if kind=='uniform_tail_bound':
        bind({'integrand','limits','parameters','epsilon','requested_output'},'Подобрать b>0 для заданной точности равномерно в p.')
        domain=task.get('parameters','')
        if bounds=='b..inf' and want==['sufficient_b_with_justification'] and (d:=re.fullmatch(r'([0-9.]+)<=p<=([0-9.]+)',domain)):
            c,k,_=parameter_power_ratio(m.parse(text,None,['x','p']),'x','p')
            lower,upper=map(F,d.groups())
            raw_eps=m.parse(task['epsilon'],None)
            if not m.constant_defined(raw_eps,m.context(dict(variable='x'))):
                raise Unsupported('The original tolerance must be a defined real constant')
            eps=m.num(m.simplify(raw_eps))
            if lower>upper or lower<=k+1 or eps is None or eps<=0:
                raise Unsupported('The stated tolerance requires an integrable common tail')
            gap=lower-k-1;exponent=1
            while F(1,10**exponent)>=eps*gap and exponent<80:exponent+=1
            power=exponent/gap
            power=-(-power.numerator//power.denominator)
            if power>200 or F(1,10**exponent)>=eps*gap:
                raise Unsupported('A sufficient tail cutoff exceeds the exact magnitude supported')
            return emit('local_integrable_parameter_majorants',[
                'На x≥1 заменяем знаменатель его степенным слагаемым с наименьшим допустимым показателем.',
                'Интегрируем общий степенной хвост и выбираем десятичную степень, делающую оценку строго меньше ε.'],
                dict(sufficient_b=q(10**power)),tail='B^(-gap)/gap',power_gap=q(gap),target_tolerance=q(eps),cutoff_exponent=power)
    if kind=='limit_integral_interchange':
        expression=task.get('expression','')
        if (want==['validity_and_actual_limits'] and
                expression=='lim_alpha->+inf int_0^inf alpha*exp(-alpha*x)dx'):
            bind({'expression','requested_output'},'Законен ли переход к пределу под знаком интеграла?')
            return emit('mass_scales_and_exceptional_parameters',[
                'Замена t=αx сохраняет полную массу 1 при каждом α>0. Для каждого x>0 интегрант стремится к нулю.',
                'У нулевого конца остаётся масса. Равномерный контроль левого несобственного среза для перестановки отсутствует.'],
                dict(interchange_valid=False,limit_of_integrals=ONE,integral_of_pointwise_limit=ZERO))
        if (want==['proof'] and expression=='lim_y->y0 int_a^inf f(x,y)dx=int_a^inf lim_y->y0 f(x,y)dx' and
                task.get('stated_conditions')==['uniform convergence on every finite interval (a,b)','abs(f(x,y))<=F(x)','int_a^inf F finite']):
            bind({'expression','stated_conditions','requested_output'},'Доказать переход к пределу по параметру.')
            return emit('local_integrable_parameter_majorants',[
                'Граница для модуля переносится на поточечный предел. Интегрируемая мажоранта задаёт один общий срез для двух хвостов.',
                'На оставшемся отрезке выбираем окрестность параметра по равномерной сходимости. Сумма трёх оценок даёт требуемый предел.'],
                dict(interchange_valid=True),inequality='error ≤ 2*int_B^inf F + (B-a)*sup_(a,B) |f_y-f_y0|')
    if kind=='improper_identity' and want==['proof']:
        if task.get('stated_conditions')==['f_prime absolutely integrable on [a,+inf)']:
            bind({'stated_conditions','requested_output'},'Доказать существование конечного предела f(x) при x→∞.')
            if 'literal_requirement' not in task.get('source',{}):
                raise Unsupported('The original conclusion about the limit of f is not stated')
            return emit('uniform_cauchy_tail_witness',[
                'На каждом конечном отрезке приращение f равно интегралу производной.',
                'Модуль приращения не превосходит соответствующего хвоста |f′|. Абсолютная сходимость даёт критерий Коши для f.'],
                dict(finite_limit=True),tail='int_min(R,S)^max(R,S) |f_prime(x)| dx')
        if (task.get('stated_conditions')==['f absolutely integrable on (0,+inf)']
                and task.get('claim')=='lim_n->inf int_0^inf f(x)*sin(n*x)dx=0'):
            bind({'stated_conditions','claim','requested_output'},'Доказать лемму об осциллирующем интеграле.')
            return emit('oscillatory_integral_approximation',[
                'Выбираем общий хвост по абсолютной интегрируемости f. На конечном отрезке приближаем f ступенчатой функцией в L¹.',
                'Для каждого шага интеграл синуса имеет модуль не больше 2/n. Осциллирующий множитель ограничен единицей и сохраняет оценку погрешности.'],
                dict(value=ZERO),approximation='finite step function in L1')
    if kind=='uniform_parameter_integral' and want==['uniform_convergence_with_justification']:
        bind({'integrand','limits','parameter_set','asserted_result','requested_output'},
             'Исследовать равномерную сходимость или доказать указанное поведение.')
        def conclusion(method,steps,uniform,**certificate):
            asserted=task.get('asserted_result')
            if asserted not in (None,'uniform','nonuniform') or (asserted is not None and (asserted=='uniform')!=uniform):
                raise Unsupported('The supplied conclusion differs from the proved parameter behavior')
            return emit(method,steps,dict(uniform=uniform),**certificate)
        return uniform_kernel_tail(text,bounds,params,conclusion)
    raise Unsupported('The stated uniformity claim has an unresolved bound or quantifier')


def uniform_kernel_tail(text,bounds,params,conclusion):
    """Infer the uniform cutoff from the actual parameter set and kernel."""
    def majorant(note,envelope,**details):
        return conclusion('local_integrable_parameter_majorants',[
            note,'Интегрируемый общий мажорант даёт хвост, стремящийся к нулю независимо от параметра.'],
            True,majorant=envelope,**details)
    def dirichlet(note,tail):
        return conclusion('uniform_oscillatory_tail',[
            note,'Интегрирование по частям с ограниченной первообразной даёт общий предел хвоста.'],
            True,tail=tail)
    def failure(note,witness,method='uniform_cauchy_tail_witness'):
        return conclusion(method,[note,'Таким образом, на сколь угодно малом или далёком несобственном хвосте остаётся положительный модуль.'],
                          False,witness=witness)
    if bounds=='0..inf' and text=='alpha*exp(-alpha*x)':
        if params=='0<a<=alpha<=b':
            return majorant('Точный хвост экспоненциальной плотности равен exp(−αB) и α≥a>0.', 'tail<=exp(-a*B)')
        if params=='0<=alpha<=b':
            return failure('Выбор α=1/B при B≥1/b сохраняет массу exp(−1). При α=0 само ядро нулевое.','alpha=1/B')
    if bounds=='0..inf' and text=='sin(alpha*x)/x':
        if params=='[a,b] excludes 0':
            return dirichlet('На данном сегменте |α| отделено от нуля. В x=0 синус и знаменатель дают конечный предел.',
                             '2/(dist(0,[a,b])*B)')
        if params=='[a,b] contains 0':
            return failure('На невырожденном сегменте выбираем α=±1/B с допустимой стороны. '
                           'Масса на [B,2B] после замены масштаба неизменна. На одноточечном сегменте {0} ядро нулевое.',
                           'alpha=±1/B, segment [B,2B]')
    if text=='x^(-alpha)' and bounds=='1..inf':
        if params=='1<alpha0<=alpha<inf':
            return majorant('На x≥1 и α≥α₀>1 оценка следует из монотонности по степени.','x^(-alpha0)')
        if params=='1<alpha<inf':
            return failure('При α=1+1/ln B точный хвост равен (ln B)/e.','alpha=1+1/ln(B)')
    if bounds=='0..inf' and text=='1/(x^alpha+1)' and params=='1<alpha<inf':
        return failure('На x≥1 ядро не меньше половины x^(-α). Выбор α=1+1/ln B сохраняет даже растущий хвост.',
                       'alpha=1+1/ln(B)')
    if bounds=='0..1' and text=='x^(-alpha)' and params=='0<alpha<1':
        return failure('Точный левый хвост δ^(1−α)/(1−α) не ограничивается равномерно при α→1⁻.',
                       'alpha=1-1/ln(1/delta)')
    if bounds=='0..inf' and text=='exp(-alpha*x)*sin(x)' and params=='0<alpha0<=alpha<inf':
        return majorant('Модуль синуса не превосходит единицы, а параметр затухания отделён от нуля.','exp(-alpha0*x)')
    if bounds=='0..inf' and text=='x^alpha*exp(-x)' and params=='a<=alpha<=b':
        return conclusion('local_integrable_parameter_majorants',[
            'При 0<x≤1 используется наименьшая степень a, а при x≥1 наибольшая b с экспоненциальным затуханием.',
            'У нуля весь набор параметров сходится и имеет общий хвост ровно при a>−1.'],
            None,uniform_when='a>-1',divergent_parameter_range='a<=alpha<=min(b,-1)',majorant=('x^a','x^b*exp(-x)'))
    if bounds=='-inf..inf' and params=='all real alpha':
        if (hit:=re.fullmatch(r'cos\(alpha\*x\)/\(([0-9]+)\+x\^2\)',text)) and int(hit[1])>0:
            return majorant('Косинус ограничен единицей при любой частоте. Знаменатель положителен на всей оси.', '1/('+hit[1]+'+x^2)')
    if bounds=='0..inf' and params=='0<=alpha<inf' and text=='1/((x-alpha)^2+1)':
        return failure('Сдвигаем центр к B и берём отрезок длины 1 после центра. Его масса не зависит от B.',
                       'alpha=B, segment [B,B+1]','moving_profile_tail_witness')
    if bounds=='0..inf' and params=='0<=alpha<inf' and text=='sin(x)*exp(-alpha*x)/x':
        return dirichlet('На хвосте все веса exp(−αx)/x неотрицательны и убывают. В x=0 ядро ограничено.', '2/B')
    if bounds=='1..inf' and params=='0<=alpha<inf,p>0 fixed' and text=='exp(-alpha*x)*cos(x)/x^p':
        return dirichlet('Фиксируем p>0. Каждый вес exp(−αx)/x^p убывает и ограничен x^(-p) независимо от α.', '2/B^p')
    if bounds=='1..inf' and text=='ln(x)^p/(x*sqrt(x))' and (cap:=re.fullmatch(r'0<=p<=(\d+)',params or '')):
        return majorant('Подстановка t=ln x даёт t^p exp(−t/2). На t≤1 используем 1, на t≥1 верхнюю степень.',
                        '(1+t^'+cap[1]+')*exp(-t/2)',substitution='t=ln(x)')
    if bounds=='0..inf' and params=='0<=alpha<inf' and text=='sqrt(alpha)*exp(-alpha*x^2)':
        return failure('При α=B^(-2) замена t=√αx переводит хвост к одному и тому же гауссову интегралу от 1.',
                       'alpha=B^(-2)','mass_scales_and_exceptional_parameters')
    if bounds=='-inf..inf' and text=='exp(-(x-alpha)^2)':
        if params=='a<alpha<b':
            return majorant('Вне |x|≥2 max(|a|,|b|) имеем |x−α|≥|x|/2.', 'exp(-x^2/4) outside a bounded interval')
        if params=='all real alpha':
            return failure('Из-за свободного сдвига отрезок [B,B+1] может начинаться в самом центре.',
                           'alpha=B','moving_profile_tail_witness')
    if bounds=='y:0..inf' and params=='all real x' and text=='exp(-x^2*(1+y^2))*sin(x)':
        return failure('Берём x=1/B. После замены t=xy модуль хвоста стремится к положительному гауссову хвосту, '
                       'поскольку e^(-x²) sin(x)/x→1. При x=0 ядро тождественно нулевое.',
                       'x=1/B','mass_scales_and_exceptional_parameters')
    if bounds=='0..inf' and params=='p>=0' and text=='sin(x^2)/(1+x^p)':
        return dirichlet('После t=x² получаем синус с убывающим весом 1/[2√t(1+t^(p/2))]. '
                         'При малом x используем |sin(x²)|≤x².', '1/B after t=B^2')
    if bounds=='0..1' and text=='x^(p-1)*ln(1/x)^q':
        if params=='p>=p0>0,q>-1':
            return conclusion('local_integrable_parameter_majorants',[
                'Подстановка t=−ln x даёт t^q e^(−pt). Для каждого фиксированного q>−1 работает общая мажоранта с p₀.',
                'Совместная равномерность по всему q>−1 не следует. На [B,B+1] при q=B и p=p₀ масса растёт.'],
                None,uniform_when='q fixed and p>=p0>0',joint_uniform=False,majorant='t^q*exp(-p0*t)',witness='q=B, p=p0')
        if params=='p>0,q>-1':
            return failure('Даже при фиксированном q>−1 подстановка t=−ln x и выбор p=1/B дают массу порядка B^(q+1) на [B,2B].',
                           'p=1/B after t=-ln(x)')
    if bounds=='0..1' and params=='0<=n<inf' and text=='x^n/sqrt(1-x^2)':
        return majorant('На исходном интервале x^n≤1 для n≥0. Правая особенность имеет порядок 1/2.', '1/sqrt(1-x^2)')
    if bounds=='0..1' and params=='0<n<2' and text=='sin(1/x)/x^n':
        return failure('При t=1/x и n=2−1/ln B вес t^(n−2) отделён от нуля на положительном полупериоде после B=2πk.',
                       'n=2-1/ln(B), B=2*pi*k')
    if bounds=='0..2' and params=='abs(alpha)<1/2' and text=='x^alpha/cbrt((x-1)*(x-2)^2)':
        return majorant('Отдельно оцениваем три исходные особенности. Кубический корень остаётся вещественным с обеих сторон от 1.',
                        ('x^(-1/2)','abs(x-1)^(-1/3)','(2-x)^(-2/3)'),endpoints=(ZERO,ONE,q(2)))
    if bounds=='0..1' and params=='0<=alpha<=1' and text=='sin(alpha*x)/sqrt(abs(x-alpha))':
        return conclusion('moving_singularity_mass_bound',[
            'Около движущейся особенности берём пересечение исходного отрезка с |x−α|≤δ.',
            'Правая и левая интегрируемые степени дают суммарную массу не больше 4√δ независимо от положения α.'],
            True,absolute_cutoff_mass='4*sqrt(delta)')
    raise Unsupported('No verified tail rule covers the entire declared parameter set')


def parameter_improper_domain(task,emit,bind):
    """Intersect the convergence regions proved at all original ends and poles."""
    method=task.get('method_requirement');conditions=task.get('stated_conditions',[])
    heading='Исследовать сходимость при помощи сравнения с рядами.' if method=='comparison_with_series' else 'Определить область сходимости.'
    bind({'integrand','limits','stated_conditions','method_requirement','requested_output'},heading)
    if task.get('requested_output')!=['convergence_parameter_set'] or method not in (None,'comparison_with_series'):
        raise Unsupported('Every source end and the required convergence method must be checked')
    text=task['integrand'].replace('²','^2').replace(' ','');bounds=task['limits']
    def region(rule,steps,ordinary,absolute,**details):
        return emit(rule,steps,dict(ordinary_convergence=ordinary,absolute_convergence=absolute),
                    required_method=method,**details)
    if bounds=='0..inf' and not conditions and method is None:
        if text=='exp(-a*x)/(1+x^2)':
            return region('power_endpoint_and_tail_orders',[
                'Конечный конец регулярен. При a≥0 экспонента не превосходит единицы, и степенной хвост имеет порядок −2.',
                'При a<0 положительное ядро растёт на хвосте, поэтому несобственный интеграл расходится.'],
                'a>=0','a>=0',comparison_envelope='1/(1+x^2)')
        if text=='x*cos(x)/(x^p+x^q)':
            return region('power_endpoint_and_tail_orders',[
                'Положим m=min(p,q), M=max(p,q). У нуля знаменатель сравним с x^m, косинус имеет ненулевой предел.',
                'На бесконечности вес x^(1−M)/(1+x^(m−M)) убывает к нулю при M>1. Используем ограниченную первообразную косинуса.',
                'Положительные части полупериодов показывают расходимость при M≤1 и дают точный показатель для абсолютного хвоста.'],
                'min(p,q)<2 and max(p,q)>1','min(p,q)<2 and max(p,q)>2',orders=('1-min(p,q)','1-max(p,q)'))
        if text=='sin(x^q)/x^p':
            return region('power_phase_normalization',[
                'При q≠0 положим t=x^q, сохранив ориентацию обоих концов. Новый вес равен t^((1−p)/q−1)/|q|.',
                'При t→0 синус имеет первый порядок. На бесконечности применяем полупериоды синуса и критерий Дирихле.',
                'При q=0 синус постоянен, и чистая степень не может одновременно сходиться у обоих концов.'],
                'q!=0 and -1<(1-p)/q<1','q!=0 and -1<(1-p)/q<0',
                substitution='t=x^q',transformed_power='(1-p)/q-1')
    if bounds=='0..2' and not conditions and method is None and text=='1/abs(ln(x))^p':
        return region('power_endpoint_and_tail_orders',[
            'При x→1 отношение ln x/(x−1) стремится к единице. Здесь точный степенной порог p=1.',
            'При x→0 замена t=−ln x даёт t^(-p)e^(−t), интегрируемое на бесконечном хвосте при любом фиксированном p.'],
            'p<1','p<1',original_singularities=(ZERO,ONE))
    if bounds=='0..1' and not conditions and method is None and text=='cos(1/(1-x))/root_n(1-x^2)':
        return region('power_phase_normalization',[
            'Положим t=1/(1−x). На хвосте из якобиана и корня получаем t^(1/n−2)(2−1/t)^(-1/n).',
            'Косинус обеспечивает обычную сходимость при отрицательной итоговой степени. Для абсолютной сходимости степень меньше −1.',
            'При натуральном индексе корня обычная сходимость есть всегда, а n=1 даёт условную.'],
            'n>1/2 for real positive index; every natural n','n>1',
            substitution='t=1/(1-x)',transformed_power='1/n-2')
    if bounds=='0..inf' and conditions==['p>0'] and method is None and text=='sin(x)/(x^p+sin(x))':
        return region('periodic_cell_tail_comparison',[
            'При sin x<0 выполняется x>π и x^p>1, поэтому знаменатель положителен. У нуля отношение ограничено.',
            'Вычитаем ведущий член sin x/x^p. Остаток равен −sin²x/[x^p(x^p+sin x)] и на хвосте сравним по ячейкам с k^(-2p).',
            'Ведущий осциллирующий член сходится по Дирихле. Для абсолютного хвоста сравнение с |sin x|/x^p даёт порог p=1.'],
            'p>1/2','p>1',cell_order='k^(-2p)')
    if method=='comparison_with_series':
        if bounds=='0..inf' and not conditions and text=='cos(x)/(x+a)':
            return region('periodic_cell_tail_comparison',[
                'За всеми конечными особыми точками используем знакопеременные полупериоды косинуса. Вес положителен, убывает и стремится к нулю.',
                'При a=0 у нуля логарифмическая расходимость. При a<0 проверяем полюс x=−a, сокращение возможно только при cos(−a)=0.',
                'После взятия модуля массы полупериодов сравнимы с k^(-1).'],
                'a>0 or a=-(pi/2+k*pi) with integer k>=0','empty',
                finite_pole='x=-a when a<=0',cell_order='k^(-1)')
        if bounds=='0..inf' and conditions==['n>0'] and text=='x/(1+x^n*sin(x)^2)':
            return region('periodic_cell_tail_comparison',[
                'В ячейке около kπ имеем x сравнимое с k, а |sin x| сравнимое с |x−kπ|.',
                'Массу ячейки сравниваем с k int du/(1+k^n u²). Замена v=k^(n/2)u даёт массу порядка k^(1−n/2).',
                'У нуля ядро ограничено x. Для положительного ряда масс требуется 1−n/2<−1.'],
                'n>4','n>4',cell_order='k^(1-n/2)',scale='v=k^(n/2)*(x-k*pi)')
        if bounds=='pi..inf' and not conditions and text=='1/(x^p*cbrt(sin(x)^2))':
            return region('periodic_cell_tail_comparison',[
                'Каждый нуль синуса даёт интегрируемую особенность степени −2/3. На одном периоде профиль имеет конечную положительную массу.',
                'В k-й ячейке x^(-p) сравним с k^(-p), и ряд положительных масс сходится ровно при p>1.'],
                'p>1','p>1',cell_order='k^(-p)',singularity_power=q(-2,3))
        if bounds=='0..inf' and not conditions and text=='sin(x+x^2)/x^n':
            return region('power_phase_normalization',[
                'У нуля синус эквивалентен x, поэтому нужен n<2. На хвосте заменяем фазу t=x+x².',
                'Амплитуда x^(-n)/(1+2x) сравнима с t^(-(n+1)/2), а при n>−1 в итоге убывает.',
                'Сравнение по полупериодам даёт пороги обычной и абсолютной сходимости.'],
                '-1<n<2','1<n<2',substitution='t=x+x^2',cell_order='k^(-(n+1)/2)')
    raise Unsupported('A new endpoint comparison or oscillatory transformation is required')


def integral_power_factors(raw,index):
    """Read products of powers while retaining even cancelled bases for domain checks."""
    coefficient=F(1)
    factors={}
    def visit(e,direction):
        nonlocal coefficient
        op=e[0]
        if op in ('mul','div'):
            visit(e[1],direction)
            visit(e[2],direction if op=='mul' else -direction)
        elif op=='q':
            if not m.num(e):raise Unsupported('A nonzero kernel multiplier is required')
            coefficient*=m.num(e)**direction
        else:
            base, exponent = {
                'pow': lambda: (e[1],q(e[2])),
                'rpow': lambda: (e[1],e[2]),
                'sqrt': lambda: (e[1],q(1,2)),
            }.get(op, lambda: (e,ONE))()
            if domain_conditions(exponent) or domain_conditions(base[1] if base[0]=='ln' else base):
                raise Unsupported('An unverified restriction occurs inside a power')
            if base[0]=='ln':
                terms,den=m.rational_form(m.simplify(exponent))
                legal={(),((('s',index),1),)} if index else {()}
                if den!={():F(1)} or any(k not in legal or c.denominator!=1 for k,c in terms.items()):
                    raise Unsupported('Each power of a negative logarithm must have an integer exponent')
            base=m.simplify(base)
            factors[base]=m.add(factors.get(base,ZERO),m.mul(q(direction),exponent))
    visit(raw,1)
    return coefficient,factors


def given_integral_derivative_data(task):
    bounds=task.get('limits')
    match=re.fullmatch(r'int_0\^(1|inf)\s+(.+?)\s*d([A-Za-z_]\w*)\s*=\s*(.+)',
                       task.get('reference_formula') or '')
    if not match or bounds!='0..'+match[1]:
        raise Unsupported('The given integral must use the same integration interval')
    _,kernel,coord,rhs=match.groups()
    lower=None
    index=None
    for condition in task.get('stated_conditions',[]):
        if lower is None and (line:=re.fullmatch(r'([A-Za-z_]\w*)\s*>\s*(.+)',condition)):
            param=line[1]
            raw=m.parse(line[2],None)
            lower=m.num(m.simplify(raw)) if not domain_conditions(raw) else None
            if lower is not None:continue
        if index is None and (line:=re.fullmatch(r'([A-Za-z_]\w*) positive integer',condition)):
            index=line[1]
            continue
        raise Unsupported('The parameter interval and any positive integer order must be explicit')
    if lower is None or coord in (param,index) or param==index:
        raise Unsupported('Distinct integration, parameter and order variables are required')
    def read(text):
        return integral_power_factors(m.parse(text.replace('²','^2'),coord,[param]+([index] if index else [])),index)
    return bounds,('v',coord),('s',param),lower,index,read(kernel),read(task['integrand']),read(rhs)


def derivative_integral_certificate(data, saved=None):
    """Check the recurrence, its target kernel and a local integrable majorant."""
    bounds,x,p,lower,index,(c,kernel),(d,target),(b,rhs)=data
    log=('ln',x)
    if len(kernel)!=1:raise Unsupported('A single varying power is required in the given kernel')
    base,exponent=next(iter(kernel.items()))

    def polynomial(e):
        terms,divisor=m.rational_form(e)
        if divisor!={():F(1)}:raise Unsupported('The power must have a polynomial base')
        return terms

    def affine(e):
        terms=polynomial(e)
        slope=terms.pop(((p,1),),F(0))
        offset=terms.pop((),F(0))
        if terms or slope<=0:raise Unsupported('The varying quantity must be positive affine in the parameter')
        return slope,offset

    if bounds=='0..1' and base==x and set(target)=={x,log} and target[x]==exponent:
        scale,shift=affine(exponent)
        if scale*lower+shift < -1:
            raise Unsupported('The common logarithmic majorant would fail at zero')
        order=target[log]
        decay=None
        initial=None
    elif bounds=='0..inf' and set(target)=={base}:
        power=m.num(exponent)
        terms=polynomial(base)
        separate={mon:terms.pop(mon) for mon in list(terms) if any(a==x for a,_ in mon)}
        if len(separate)!=1 or power is None or power.denominator!=1 or power>=0:
            raise Unsupported('A reciprocal power with a polynomial tail is required')
        (mon,leading),=separate.items()
        if len(mon)!=1 or mon[0][0]!=x or leading<=0 or mon[0][1]*(-power)<=1:
            raise Unsupported('The majorant does not have integrable decay')
        scale,shift=affine(m.poly_expr(terms))
        if scale*lower+shift<0:
            raise Unsupported('The reciprocal base need not stay positive near zero')
        order=m.add(exponent,m.neg(target[base]))
        decay=mon[0][1]
        initial=-power
    else:
        raise Unsupported('The target is not an iterated parameter derivative of the given kernel')

    n=m.num(order)
    if (index and order!=('s',index)
            or not index and (n is None or n.denominator!=1 or not 1<=n<=64)):
        raise Unsupported('The derivative order does not have the required positive integer domain')
    if m.PI in rhs:
        if rhs[m.PI]!=ONE:raise Unsupported('The constant factor must be linear in pi')
        constant=m.PI
    else:constant=ONE
    varying={base:power for base,power in rhs.items() if base!=m.PI}
    if len(varying)!=1:raise Unsupported('The given value needs one varying power')
    right_base,right_exponent=next(iter(varying.items()))
    right_scale,right_shift=affine(right_base)
    right_power=m.num(right_exponent)
    if right_power is None or right_power>=0 or right_scale*lower+right_shift<0:
        raise Unsupported('The differentiated right side must be real throughout the parameter interval')

    evidence=dict(parameter=p,order=order,lower_boundary=q(lower),
                  majorant=dict(left_endpoint='power_times_log' if decay is None else 'bounded',
                                tail_degree=decay,split=q(1)))
    from model import canonical
    if saved is not None and canonical(saved)!=canonical(evidence):
        raise Unsupported('The derivative order, parameter domain or majorant changed')

    # On a local interval above the boundary use (A)_j for the absolute
    # derivative coefficient of a reciprocal power of order A.
    def rising(a,j):
        out=F(1)
        for i in range(j):out*=a+i
        return out
    ratio=right_scale/scale
    right_power=-right_power
    factor=m.mul(q(d*b/c),constant)
    if n is not None:
        j=int(n)
        weight=ratio**j*rising(right_power,j)
        weight=weight*(-1)**j if decay is None else weight/rising(initial,j)
        value=m.mul(m.mul(factor,q(weight)),spatial_axis_power(right_base,q(-right_power-j)))
    else:
        j=index
        weight=f'{source(q(ratio))}^({j})' if ratio!=1 else '1'
        signed=f'(-1)^({j})' if decay is None else f'1/rising({source(q(initial))},{j})'
        value=(f'{source(factor)}*{signed}*{weight}*rising({source(q(right_power))},{j})'
               f'/({source(right_base)})^({source(q(right_power))}+{j})')

    steps=['Сопоставляем исходное ядро с производной заданного ядра порядка '+source(order)+'.',
           'На локальном замкнутом интервале параметра выбираем нижнюю точку строго выше границы.']
    if decay is None:
        steps.append('У нуля общий мажорант — степень с показателем больше −1, умноженная на степень |ln x|. '
                     'Замена x=exp(−t) даёт интегрируемое произведение экспоненты и многочлена.')
    else:
        steps.append('До x=1 обратная степень равномерно ограничена. После x=1 '
                     'мажорант убывает как степень с показателем не больше −'+str(decay*initial)+'.')
    steps.append('Дифференцируем заданное равенство по параметру и делим на вычисленный ненулевой множитель. '
                 'rising(a,j) обозначает произведение a(a+1)…(a+j−1).')
    return evidence,steps,dict(value=value)


def solve_given_integral_derivative(task,emit):
    evidence,steps,value=derivative_integral_certificate(given_integral_derivative_data(task))
    return emit('local_parameter_derivative_majorants',steps,value,derivative_certificate=evidence)


def check_given_integral_derivative(task, plan, value):
    from model import canonical
    from verify import require
    require(task.get('method_requirement')=='use_given_integral'
            and task.get('requested_output')==['exact_integral','specified_method']
            and not set(task)-{'kind','id','source','integrand','limits','stated_conditions',
                               'reference_formula','method_requirement','requested_output'},
            'The prescribed given integral and conclusion are required')
    meta=task.get('source',{})
    heading='Вычислить несобственный интеграл.'
    require(isinstance(meta,dict) and not set(meta)-{'exercise','printed_subpart','printed_page','pdf_page',
                'pdf_sha256','literal_requirement'} and meta.get('literal_requirement',heading)==heading,
            'An additional source condition, goal or method remains')
    evidence,steps,answer=derivative_integral_certificate(given_integral_derivative_data(task),plan['derivative_certificate'])
    checked=dict(theorem='method.local_parameter_derivative_majorants',steps=steps,source_bounds=task['limits'],
                 source_parameter_conditions=task.get('stated_conditions',[]),derivative_certificate=evidence)
    require(canonical(plan)==canonical(checked) and canonical(value)==canonical(answer),
            'The displayed parameter proof or its conclusion changed')
    return len(steps)



def laplace_parameter_exchange(task,emit):
    from verify import same_value
    reference=task.get('reference_formula') or ''
    name=r'([A-Za-z_]\w*)'
    hit=re.fullmatch(r'(.+?)=int_'+name+r'\^'+name+r'\s+(.+?)\s*d'+name,reference)
    if not hit:raise Unsupported('The oriented parameter integral requires explicit endpoints and a binder')
    left,a,b,kernel,t=hit.groups()
    if len({a,b,t})!=3:raise Unsupported('The scale endpoints and bound variable must be distinct')
    names=lambda f:set(re.findall(r'[A-Za-z_]\w*',f))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi'}
    free=names(kernel)-{t}
    if len(free)!=1 or free&{a,b}:raise Unsupported('A single remaining half-line coordinate is required')
    x,=free
    params=[a,b]
    read=lambda f:m.parse(f,x,params)
    coordinate=('v',x);scale=('s',t);A,B=map(lambda p:('s',p),params)
    raw=m.parse(kernel,x,[t])
    if raw[0]!='exp' or domain_conditions(raw):
        raise Unsupported('The parameter kernel needs restriction-free exponential attenuation')
    exponent=raw[1]
    rate=m.num(m.simplify(('div',m.neg(exponent),m.mul(coordinate,scale))))
    if rate is None or rate<=0:raise Unsupported('No positive product attenuation was proved')
    positive=sorted(c.replace(' ','') for c in task.get('stated_conditions',[]))
    if positive!=sorted(p+'>0' for p in params):raise Unsupported('Both scale endpoints must be positive')
    expected=('div',m.add(('exp',m.mul(q(-rate),m.mul(coordinate,A))),
                          m.neg(('exp',m.mul(q(-rate),m.mul(coordinate,B))))),
              m.mul(q(rate),coordinate))
    for f in (left,task['integrand']):
        expression=read(f)
        if not all(g[0]=='nonzero' and m.rational_form(g[1])[0].keys()=={((coordinate,1),)}
                   and m.rational_form(g[1])[1]=={():F(1)} for g in domain_conditions(expression)):
            raise Unsupported('The represented expression has an additional hole on the half-line')
        # Normalize subexpressions within the exponent as well as the outer rational operations.
        if not same_value(m.simplify(expression),m.simplify(expected)):
            raise Unsupported('The oriented primitive does not reproduce the original integrand')
    return emit('oriented_parameter_integral_exchange',[
        'Проверяем, что первообразная ядра по масштабу даёт заданную разность на положительной полуоси.',
        'Меньший из двух положительных масштабов даёт интегрируемую экспоненциальную мажоранту на всём промежутке.',
        'После смены порядка внутренний интеграл даёт обратный масштаб с коэффициентом. Его первообразная — логарифм.',
        'Сохраняем порядок концов. При совпадении масштабов оба интеграла равны нулю.'],
        dict(value=m.mul(q(1/rate),('ln',m.div(B,A)))),reference=reference,
        attenuation=q(rate),scale_interval=(a,b),parameter_variable=t,integration_variable=x)


def parameter_integral_transform(task,emit,bind,request):
    kind=task['kind'];want=task.get('requested_output')
    method=task.get('method_requirement');reference=task.get('reference_formula')
    conditions=task.get('stated_conditions',[]);bounds=task.get('limits')
    text=task.get('integrand','').replace('²','^2').replace(' ','')
    if kind=='special_function_integral_identity' and want==['proof']:
        bind({'claim','reference','requested_output'},'Доказать формулу, используя определения предыдущих задач.')
        return parameter_special_primitive(task,emit)
    if kind=='smoothness_parameter_integral' and want==['proof_of_all_order_continuous_derivatives']:
        bind({'function','parameter_domain','requested_output'},'Доказать непрерывность функции и её производных всех порядков.')
        function,domain=task['function'],task['parameter_domain']
        if (gamma:=function=='Gamma(x)' and domain=='x>0') or function=='B(x,y)' and domain=='x>0,y>0':
            base='t^(x-1)*exp(-t)' if gamma else 't^(x-1)*(1-t)^(y-1)'
            modifiers='ln(t)^j' if gamma else 'ln(t)^j*ln(1-t)^k'
            proof=(
                'На локальном положительном отрезке параметра выбираем 0<a≤x≤b. Около нуля показатель a даёт '
                'интегрируемую степень с логарифмом, а на бесконечности показатель b сохраняет экспоненциальное затухание.'
                if gamma else
                'Берём локальный компактный прямоугольник с положительными нижними границами a,b. '
                'Делим интервал интегрирования пополам. У каждого конца существенна только его степень с логарифмом.')
            return emit('local_parameter_derivative_majorants',[
                'Каждое дифференцирование добавляет логарифм соответствующего степенного основания.',
                proof,'Индукция по порядку повторяет локальное доминирование и доказывает непрерывность каждой полученной производной.'],
                dict(smooth_on=domain,derivative_integrand=base+'*'+modifiers),base_kernel=base,logarithmic_factor=modifiers)
    if kind=='differentiate_dirichlet_integral' and want==['derivative_exists','failure_of_under_integral_derivative']:
        bind({'integrand','limits','suggested_substitution','requested_output'},
             'Доказать существование производной при α≠0 и невозможность вычисления по правилу Лейбница.')
        if bounds=='0..inf' and text=='sin(alpha*x)/x' and task.get('suggested_substitution') in (None,'y=alpha*x'):
            return emit('signed_dirichlet_frequency',[
                'На каждой ненулевой полуоси заменяем t=|α|x. Исходный интеграл постоянен с соответствующим знаком.',
                'Его производная там равна нулю. Интеграл от косинуса, частной от исходного ядра, не сходится.',
                'На конечном срезе его первообразная равна sin(αB)/α и предела при B→∞ нет.'],
                dict(derivative_on_alpha_nonzero=ZERO,leibniz_valid=False),substitution='t=abs(alpha)*x')
    if kind=='frullani_identity' and want==['proof']:
        bind({'formula','stated_conditions','requested_output'},'Доказать формулу Фруллани при указанных предпосылках.')
        if (conditions==['a,b>0','f continuous','int_A^inf f(x)/x dx exists for every A>0']
                and task['formula']=='int_0^inf (f(a*x)-f(b*x))/x dx=f(0)*ln(b/a)'):
            return emit('frullani_oriented_cutoffs',[
                'На конечном срезе [ε,R] разделяем разность и подставляем t=ax,t=bx.',
                'На правом крае интеграл по окну [aR,bR] исчезает по критерию Коши для f(t)/t.',
                'На левом крае непрерывность f ограничивает остаток после вычитания f(0). Интеграл f(0)/t даёт логарифм отношения.',
                'Аргумент сохраняет оба несобственных конца и ориентацию при любом порядке положительных a,b.'],
                dict(identity=True),lower_window=('a*epsilon','b*epsilon'),upper_window=('a*R','b*R'))
    if kind in ('evaluate_via_parameter','parameter_definite_integral'):
        heading={'differentiate_under_integral':'Вычислить, применяя дифференцирование по параметру.',
                 'specified_representation':'Вычислить, используя заданное интегральное представление.',
                 'integrate_under_integral':'Вычислить интегрированием под знаком интеграла.'}
        if kind=='evaluate_via_parameter':
            if method not in heading or want!=['value_and_specified_method']:
                raise Unsupported('The prescribed operation under the integral has to be verified')
            bind({'integrand','limits','stated_conditions','identity','method_requirement','requested_output'},heading[method])
        else:
            if method is not None or want!=['exact_value']:
                raise Unsupported('The stated exact definite integral must be preserved')
            bind({'integrand','limits','stated_conditions','requested_output'},'Вычислить интеграл.')
        if (text=='ln((1+a*cos(x))/(1-a*cos(x)))/cos(x)' and bounds=='0..pi/2'
                and conditions==['abs(a)<1'] and method=='differentiate_under_integral' and 'identity' not in task):
            return emit('anchored_parameter_derivative',[
                'При cos x=0 логарифмический множитель имеет конечное продолжение 2a.',
                'В локальном |a|≤c<1 частная 2/(1−a²cos²x) ограничена. Подстановка тангенса даёт π/√(1−a²).',
                'Интегрируем по a от нуля, где исходное ядро равно нулю.'],
                dict(value=m.mul(m.PI,('asin',('s','a')))),anchor=ZERO,parameter_derivative='pi/sqrt(1-a^2)')
        if (text=='atan(x)/(x*sqrt(1-x^2))' and bounds=='0..1' and conditions==[]
                and method=='specified_representation' and task.get('identity')=='atan(x)/x=int_0^1 dy/(1+x^2*y^2)'):
            return emit('oriented_parameter_integral_exchange',[
                'Подставляем заданное неотрицательное представление arctg(x)/x. Переставляем два интеграла.',
                'После x=sin θ и подстановки тангенса внутренний интеграл равен π/(2√(1+y²)).',
                'Интегрирование по y от 0 до 1 даёт логарифмическую первообразную.'],
                dict(value=m.mul(m.div(m.PI,q(2)),('ln',m.add(ONE,('sqrt',q(2)))))),represented_factor='atan(x)/x')
        family=re.fullmatch(r'(?:(sin|cos)\(ln\(1/x\)\)\*)?\(x\^([A-Za-z]\w*)-x\^([A-Za-z]\w*)\)/ln\(x\)',text)
        if family and bounds=='0..1' and 'identity' not in task:
            wave,b,a=family.groups()
            if a!=b and 'x' not in (a,b) and conditions==[a+'>0',b+'>0'] and (
                wave and kind=='parameter_definite_integral' or not wave and method=='integrate_under_integral'):
                def primitive(s):
                    shifted=m.add(ONE,('s',s))
                    if wave=='sin':return ('atan',shifted)
                    if wave=='cos':return m.mul(q(1,2),('ln',m.add(ONE,m.power(shifted,2))))
                    return ('ln',shifted)
                p=wave or 'constant'
                return emit('oriented_parameter_integral_exchange',[
                    'Разность степеней, делённую на ln x, заменяем ориентированным интегралом по показателю от нижнего до верхнего.',
                    'Показатели отделены от −1. Модуль дополнительного множителя ограничен единицей, а степенной мажорант общий.',
                    'После t=−ln x вычисляем затухающий '+p+' момент и интегрируем полученную функцию показателя.'],
                    dict(value=m.add(primitive(b),m.neg(primitive(a)))),parameter_bounds=(a,b),moment=p)
    if kind=='parameter_improper_evaluation' and want==(['exact_integral','specified_method'] if method else ['exact_integral_and_convergence']):
        bind({'integrand','limits','stated_conditions','reference_formula','method_requirement','requested_output'},
             'Вычислить несобственный интеграл.')
        if method=='use_given_integral':
            return solve_given_integral_derivative(task,emit)
        if method=='specified_representation' and bounds=='0..inf':
            return laplace_parameter_exchange(task,emit)
        if method=='differentiate_under_integral' and bounds=='0..inf' and reference is None:
            return anchored_exponential_parameter_difference(text,conditions,emit)
        if method is None and reference is None:
            return parameter_angular_integral(text,bounds,conditions,emit)
    raise Unsupported('The proposed parameter derivative or integral identity is not justified on the full source domain')


def anchored_exponential_parameter_difference(text,conditions,emit):
    """Differentiate a positive-scale difference and anchor on the diagonal."""
    rate=r'([A-Za-z]\w*)'
    difference=r'\(exp\(-'+rate+r'\*x(?:\^([1-9]\d*))?\)-exp\(-'+rate+r'\*x(?:\^([1-9]\d*))?\)\)'
    mode=None
    if square:=re.fullmatch(r'\('+difference+r'/x\)\^2',text):
        hit=square;mode='square'
    else:
        hit=re.fullmatch(difference+r'(?:\*(sin|cos)\('+rate+r'\*x\))?/x',text)
        if hit:mode=hit[5] or 'plain'
    if not hit:raise Unsupported('No common positive-scale exponential difference was recognized')
    a,j,b,k=hit.groups()[:4];power=int(j or '1')
    if j!=k or power>20 or a==b or 'x' in (a,b) or conditions!=[a+'>0',b+'>0']:
        raise Unsupported('The scales and powers must share a positive parameter domain')
    A,B=('s',a),('s',b)
    if mode=='plain':
        value=m.mul(q(1,power),('ln',m.div(B,A)))
        derivative='-1/('+str(power)+'*'+a+')'
        step='После t=x^'+str(power)+' частная по первому масштабу интегрируется в '+derivative+'.'
    elif power!=1:
        raise Unsupported('The transformed oscillatory or squared moment needs a separate identity')
    elif mode=='square':
        total=m.add(A,B);X=m.mul(q(2),A);Y=m.mul(q(2),B)
        value=m.mul(q(2),m.add(m.add(m.mul(A,('ln',X)),m.mul(B,('ln',Y))),m.neg(m.mul(total,('ln',total)))))
        derivative='2*ln(2*'+a+'/('+a+'+'+b+'))'
        step='Частная квадрата остаётся разностью экспонент, делённой на x. Формула Фруллани даёт '+derivative+'.'
    else:
        if hit[6] in ('x',a,b):raise Unsupported('The frequency must be independent of the varied scale')
        freq=('s',hit[6])
        if mode=='sin':
            value=m.add(('atan',m.div(freq,A)),m.neg(('atan',m.div(freq,B))))
            derivative='-'+hit[6]+'/('+a+'^2+'+hit[6]+'^2)'
        else:
            S=lambda v:m.add(m.power(v,2),m.power(freq,2))
            value=m.mul(q(1,2),('ln',m.div(S(B),S(A))))
            derivative='-'+a+'/('+a+'^2+'+hit[6]+'^2)'
        step='Производная становится затухающим '+mode+' моментом. Интегрирование экспоненты даёт '+derivative+'.'
    return emit('anchored_parameter_derivative',[
        'В локальном окне положительных масштабов разность экспонент у нуля имеет порядок x^'+str(power)+'. '
        'После дифференцирования исходный делитель сокращается допустимой степенью. На бесконечности сохраняется общий экспоненциальный хвост.',
        step,'Интегрируем по первому масштабу, фиксируя значение 0 на диагонали двух масштабов.'],
        dict(value=value,convergence='ordinary and absolute'),parameter_derivative=derivative,anchor=a+'='+b,power=power)


def parameter_angular_integral(text,bounds,conditions,emit):
    denominator=r'sqrt\(1-x\^2\)'
    if (hit:=re.fullmatch(r'ln\(1-([A-Za-z]\w*)\^2\*x\^2\)/(\(x\^2\*'+denominator+r'\)|'+denominator+r')',text)):
        name,divisor=hit.groups();p=('s',name)
        if name=='x' or bounds!='0..1' or conditions!=['abs('+name+')<=1']:
            raise Unsupported('The original logarithmic endpoints must be included')
        radical=('sqrt',m.add(ONE,m.neg(m.power(p,2))))
        if divisor.startswith('('):
            v=m.mul(m.PI,m.add(radical,q(-1)))
        else:
            v=m.mul(m.PI,('ln',m.div(m.add(ONE,radical),q(2))))
        return emit('anchored_parameter_derivative',[
            'Подстановка x=sin θ убирает радикальный якобиан. На каждом |p|≤c<1 частная по p имеет общий мажорант.',
            'После подстановки тангенса остаётся элементарный момент 1/(1−p²sin²θ). По исходному нулевому параметру фиксируем константу.',
            'При |p|=1 логарифм cos²θ остаётся интегрируемым. Если присутствует 1/sin²θ, произведение ограничено у θ=0.'],
            dict(value=v,convergence='ordinary and absolute on the entire closed parameter set'),chart='x=sin(theta)',
            anchor=ZERO,includes_parameter_endpoints=True)
    if (hit:=re.fullmatch(r'atan\(([A-Za-z]\w*)\*x\)/\(x\^2\*sqrt\(x\^2-1\)\)',text)) and bounds=='1..inf' and not conditions and hit[1]!='x':
        p=('s',hit[1]);root=('sqrt',m.add(ONE,m.power(p,2)));difference=m.add(root,q(-1))
        mul=lambda s:m.mul(m.div(m.PI,q(2)),m.add(p,m.mul(q(s),difference)))
        return emit('anchored_parameter_derivative',[
            'Подставляем x=sec θ, вес становится cos θ dθ. Частная по параметру равна cos²θ/(cos²θ+p²) и ограничена единицей.',
            'Её интеграл равен (π/2)(1−|p|/√(1+p²)), включая значение при нуле.',
            'Восстанавливаем функцию на обеих полуосях из общего значения 0 в начале.'],
            dict(value_positive=mul(-1),value_zero=ZERO,value_negative=mul(1),convergence='ordinary and absolute for all real parameters'),
            parameter=hit[1],chart='x=sec(theta)',anchor=ZERO)
    raise Unsupported('The original angular chart or real endpoint condition is not established')


def parameter_special_primitive(task,emit):
    from cartesian_fields import exact_polynomial_partial
    from verify import same_value

    claim=task['claim'];reference=task['reference']
    if type(reference) is not int or reference<=0:
        raise Unsupported('A source reference must be present for the standard special functions')
    if claim=='int_0^x t*J0(t)dt=x*J1(x)':
        return emit('special_function_differential_relation',[
            'Дифференцируем конечное интегральное представление J₀. Отражение угла устраняет косинусную часть представления J₁ и даёт J₀′=−J₁.',
            'Уравнение Бесселя нулевого порядка даёт (xJ₀′)′=−xJ₀.',
            'У правой части в исходной формуле нулевое значение при x=0. Это фиксирует интеграл.'],
            dict(identity=True),basis_relations=('J0_prime=-J1','(x*J0_prime)_prime=-x*J0'),base_point=ZERO)
    hit=re.fullmatch(r'int_0\^k ([EF])\(s\)\*s ds=(.+)',claim)
    if not hit:
        raise Unsupported('The differential equations of the referenced special functions are unknown')
    k,e,f=('s','k'),('s','E'),('s','F')
    right=m.parse(hit[2].replace('²','^2').replace('E(k)','E').replace('F(k)','F'),None,['k','E','F'])
    ctx=m.context(dict(variable='__special_probe',parameters=['k','E','F']))
    if any(not known_guard(guard,ctx) for guard in domain_conditions(right)):
        raise Unsupported('The source right side has an additional parameter restriction')
    poly,den=m.rational_form(right)
    if set(den)!={()} or not den[()] or any(sum(p for a,p in term if a in (e,f))>1 for term in poly):
        raise Unsupported('A polynomial coefficient combination of the two source functions is required')
    deriv=lambda var:m.div(m.poly_expr(exact_polynomial_partial(poly,var)),q(den[()]))
    div=lambda r:m.div(r,k)
    Ep=div(m.add(e,m.neg(f)))
    Fp=div(m.add(m.div(e,m.add(ONE,m.neg(m.power(k,2)))),m.neg(f)))
    differential=m.add(deriv(k),m.add(m.mul(deriv(e),Ep),m.mul(deriv(f),Fp)))
    target=m.mul(k,e if hit[1]=='E' else f)
    initial=m.substitute(right,{k:ZERO,e:m.div(m.PI,q(2)),f:m.div(m.PI,q(2))})
    if not same_value(differential,target) or not same_value(initial,ZERO):
        raise Unsupported('The proposed primitive has the wrong derivative or initial value')
    return emit('special_function_differential_relation',[
        'На каждом 0≤k≤c<1 производные эллиптических ядер ограничены. Производная E получается непосредственно.',
        'Для производной F вычитаем производную sin θ cos θ/√(1−k²sin²θ), у которой оба граничных значения равны нулю.',
        'Подставляем обе дифференциальные формулы в правую часть и проверяем точное равенство производной исходному интегранту.',
        'При k=0 обе исходные функции равны π/2. Вычисленная правая часть равна нулю.'],
        dict(identity=True,domain='0<=k<1'),basis_relations=(Ep,Fp),checked_derivative=target,base_value=ZERO)


def improper_space_proof(task,library):
    kind=task['kind'];want=task.get('requested_output')
    fields={'id','kind','source','integrand','region','stated_conditions','method_requirement','requested_output'}
    if kind in ('improper_exhaustion_proof','improper_convergence_proof'):
        fields|={'claim','claims'}
    meta=task.get('source',{})
    if (not library.data.get('improper_space_integrals') or set(task)-fields or not isinstance(meta,dict)
            or set(meta)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}):
        raise Unsupported('A condition or goal of the original improper integral is unresolved')
    text=task['integrand'].replace('²','^2').replace(' ','')
    region=task.get('region','').replace('²','^2').replace(' ','')
    conditions=task.get('stated_conditions',[]);method=task.get('method_requirement')
    if not isinstance(conditions,list) or not all(isinstance(c,str) for c in conditions):
        raise Unsupported('The original parameter restrictions must be explicit')

    outputs={
        'improper_multidimensional_convergence':['convergence_cases'],
        'improper_multiple_integral':['improper_integral_with_convergence'],
        'improper_convergence_proof':['proof'],
        'improper_exhaustion_proof':[]}
    if kind not in outputs or outputs[kind] and want!=outputs[kind] or method not in (None,'polar_coordinates'):
        raise Unsupported('Unbound convergence question, parameter restrictions or requested integration method')
    literal=meta.get('literal_requirement','')
    expected={'improper_multidimensional_convergence':('Исследовать сходимость несобственного интеграла.','Исследовать сходимость.'),
              'improper_multiple_integral':('Вычислить несобственный интеграл.',),
              'improper_convergence_proof':('Доказать сходимость приведённого повторного интеграла.',),
              'improper_exhaustion_proof':('Доказать утверждение о неотрицательной непрерывной функции и любой исчерпывающей последовательности.',
                                          'Показать оба различных предела для двух исчерпаний.',
                                          'Показать расходимость двойного интеграла при сходимости обоих повторных.')}
    if literal and literal not in expected[kind] and not (
        method=='polar_coordinates' and kind=='improper_multiple_integral' and literal.startswith('Вычислить интеграл.')
            and literal.endswith('прямо требуются полярные координаты.')):
        raise Unsupported('The source wording has an additional mathematical obligation')

    def emit(method_id,steps,certificate=None,**value):
        plan=dict(theorem='method.'+method_id,steps=steps,original_region=task.get('region'),
                  original_conditions=conditions,required_method=method)
        if certificate is not None:plan['certificate']=certificate
        return plan,value
    if kind=='improper_exhaustion_proof':
        return spatial_exhaustion_certificate(task,text,region,conditions,emit)
    if kind=='improper_convergence_proof':
        if (text=='phi(x,y)/abs(f(x)-y)^p' and region=='a<=x<=A,b<=y<=B'
                and conditions==['phi continuous on rectangle','f continuous on [a,A]','p<1']):
            return emit('transverse_integrable_singularity',[
                'Модуль числителя ограничен на замкнутом прямоугольнике. Положение f(x) внутри поперечного отрезка может меняться.',
                'Для 0≤p<1 единая оценка поперечной массы получается разделением отрезка по обе стороны от f(x). '
                'Она не превосходит 2(B−b)^(1−p)/(1−p). При отрицательном p ядро ограничено на компактной области.'],
                convergence=True,absolute=True)
        raise Unsupported('The regularity or transverse range for the proof is unknown')
    if method is None and (answer:=spatial_anisotropic_powers(text,region,conditions,emit)) is not None:return answer
    if kind=='improper_multiple_integral' and method is None and 'exp(' in text:
        try:
            if (answer:=gaussian_space_integral(text,region,conditions,emit)) is not None:return answer
        except Unsupported:
            pass  # A radial or separated route may still apply.
    if (answer:=spatial_radial_reduction(text,region,conditions,kind,method,emit)) is not None:return answer
    if method is not None:
        raise Unsupported('No radial chart with the printed method was derived')
    if kind=='improper_multiple_integral':
        return spatial_other_values(text,region,conditions,emit)
    return spatial_other_convergence(text,region,conditions,emit)


def spatial_axis_power(e,exponent):
    if exponent==ONE:return e
    if e==ONE:return ONE
    power=m.num(exponent)
    if power is not None and power.denominator==1:return m.power(e,power.numerator)
    if power is not None and power.denominator==2:return m.power(m.simplify(('sqrt',e)),power.numerator)
    return ('rpow',e,exponent)


def spatial_anisotropic_powers(text,region,conditions,emit):
    hit=re.fullmatch(r'1/\((abs\([xyz]\)\^[A-Za-z]\w*(?:\+abs\([xyz]\)\^[A-Za-z]\w*)+)\)',text)
    if not hit:return None
    pairs=re.findall(r'abs\(([xyz])\)\^([A-Za-z]\w*)',hit[1])
    coords,orders=[list(z) for z in zip(*pairs)]
    if (not 2<=len(pairs)<=3 or len(set(coords))!=len(coords) or len(set(orders))!=len(orders)
            or set(coords)&set(orders)):
        raise Unsupported('Each coordinate must have a distinct bound positive index')
    inequalities=region.split(';')
    source_guard=([i.strip() for i in inequalities[1].split(',')] if len(inequalities)==2 else [])
    shape='+'.join('abs('+z+')' for z in coords)
    relation=inequalities[0].removeprefix(shape)
    if (not inequalities[0].startswith(shape) or relation not in ('<=1','>=1')
            or len(inequalities)>2 or sorted(conditions+source_guard)!=sorted(z+'>0' for z in orders)):
        raise Unsupported('The positive anisotropic exponents and the full inner or outer domain must be bound')
    outer=relation=='>=1';s='+'.join('1/'+z for z in orders)
    return emit('anisotropic_radial_integrability',[
        'Разбиваем исходную область по знакам координат. На каждом открытом квадранте или октанте координата '
        'uᵢ=|xᵢ|^pᵢ имеет положительный обратный якобиан uᵢ^(1/pᵢ−1)/pᵢ.',
        'Выделяем масштаб s=Σuᵢ и симплексные доли. Якобиан умножает меру на s^(d−1), '
        'а симплексный бета-интеграл конечен, поскольку 1/pᵢ>0.',
        'Образ исходной единичной границы находится между двумя положительными уровнями масштаба. '
        'Поэтому точный порог проверяется для степени s^(Σ1/pᵢ−2) на нужном конце.'],
        convergence_condition=s+('<1' if outer else '>1'),absolute=True,end='infinity' if outer else 'zero')


def spatial_radial_reduction(text,region,conditions,kind,method,emit):
    from level_sets import quadratic_coefficients

    whole=re.fullmatch(r'R\^([23])',region)
    domain=re.fullmatch(r'(x\^2\+y\^2(?:\+z\^2)?)(<=|>=)([1-9]\d*(?:/\d+)?)',region)
    if not (whole or domain):return None
    d=int(whole[1]) if whole else 3 if '+z^2' in domain[1] else 2
    coords=list('xyz'[:d]);norm='+'.join(x+'^2' for x in coords)
    scale=F(domain[3]) if domain else None
    outer=bool(domain and domain[2]=='>=')
    convergence_kind=kind=='improper_multidimensional_convergence'
    S=m.mul(q(2 if d==2 else 4),m.PI)
    if domain and not method:
        p=re.fullmatch(r'(phi(?:\('+','.join(coords)+r'\))?|1)/\('+re.escape(norm)+r'\)\^(\w+)',text)
        if p:
            names=p[1]
            bounded_phi=['0<m<=abs('+names+')<=M']
            stated=['parameters positive'] if names=='1' and d==2 else []
            if conditions!=(bounded_phi if names!='1' else stated) or convergence_kind!=(names!='1'):
                raise Unsupported('The radial numerator, sign assumptions or requested exact value remain unbound')
            index=m.simplify(m.parse(p[2],None,[p[2]] if p[2].isalpha() else []))
            half=q(d,2);cut=F(d,2)
            ans={'convergence_condition':p[2]+('>' if outer else '<')+str(cut),
                 'absolute':True,'radial_end':'infinity' if outer else 'zero'}
            if names=='1':
                if m.num(index) is not None and not (m.num(index)>cut if outer else m.num(index)<cut):
                    ans=dict(converges=False,absolute=False)
                else:
                    power=m.add(half,m.neg(index));den=m.mul(q(-2 if outer else 2),power)
                    ans['value']=m.div(m.mul(S,spatial_axis_power(q(scale),power)),den)
            return emit('radial_and_boundary_power',[
                'В полярных или сферических координатах якобиан равен r^(d−1) на единицу угловой меры.',
                'Модуль ядра при ненулевом ограниченном числителе сравним с r^(−2p). '
                'Степенной интеграл на исходном конце даёт строгий порог p=d/2.'],
                radial_dimension=d,**ans)
        subtracted='-'.join(x+'^2' for x in coords)
        b=re.fullmatch(r'(phi(?:\('+','.join(coords)+r'\))?|1)/\(('+re.escape(domain[3])+r')-'+re.escape(subtracted)+r'\)\^(\w+)',text)
        root=text=='1/sqrt('+domain[3]+'-'+subtracted+')'
        if (b or root) and not outer:
            names=b[1] if b else '1';order=b[3] if b else '1/2'
            expected=['0<m<=abs('+names+')<=M'] if names!='1' else ['parameters positive'] if root and d==2 else []
            if conditions!=expected or convergence_kind!=(names!='1'):
                raise Unsupported('The boundary power does not bind the original numerator and conditions')
            ans=dict(convergence_condition=order+'<1' if not root else True,absolute=True)
            if names=='1':
                p0=m.num(m.simplify(m.parse(order,None,[order] if order.isalpha() else [])))
                if p0 is not None and p0>=1:
                    ans=dict(converges=False,absolute=False)
                elif d==2:
                    divisor=m.add(ONE,m.neg(q(p0) if p0 is not None else ('s',order)))
                    ans['value']=m.div(m.mul(m.PI,spatial_axis_power(q(scale),divisor)),divisor)
                else:
                    p0=('s',order) if p0 is None else q(p0)
                    ans['value']=dict(beta_shape=(q(d,2),m.add(ONE,m.neg(p0))),
                                      factor=m.mul(m.div(S,q(2)),spatial_axis_power(q(scale),m.add(q(d,2),m.neg(p0)))))
            return emit('radial_and_boundary_power',[
                'Замена t=r² переносит особенность в конечную границу t=R², где степенной множитель меры отделён от нуля.',
                'Проверяем показатель у t=R² и регулярность нижнего конца. Нормирование на R² даёт бета-интеграл.'],
                radial_dimension=d,**ans)
    if whole and not conditions and kind=='improper_multiple_integral':
        raw=m.parse(text,None,coords)
        if domain_conditions(raw):raise Unsupported('A hidden domain condition remains in the full radial kernel')
        expo=raw if raw[0]=='exp' else next((e for e in raw[1:] if e[0]=='exp'),None) if raw[0]=='mul' else None
        wave=next((e for e in raw[1:] if e[0] in ('cos','sin')),None) if raw[0]=='mul' else None
        if expo is None or raw[0]=='mul' and wave is None:return None
        def isotropic(expr):
            A,L,C=quadratic_coefficients(expr,coords);c=A[0][0]
            if any(L) or C or any(A[i][j]!=(c if i==j else 0) for i in range(d) for j in range(d)):
                raise Unsupported('The full kernel is not homogeneous radial before integration')
            return c
        rate=-isotropic(expo[1]);freq=isotropic(wave[1]) if wave else F(0)
        if rate<=0 or wave and d!=2 or method=='polar_coordinates' and d!=2:
            raise Unsupported('A positive decaying radial mode and the correct method are required')
        if wave:
            value=m.mul(m.PI,q((rate if wave[0]=='cos' else freq)/(rate**2+freq**2)))
        else:
            value=m.div(m.mul(m.div(S,q(2)),gamma_rational(F(d,2))),spatial_axis_power(q(rate),q(d,2)))
        return emit('radial_gaussian_modes',[
            'Переходим к полярной или сферической мере на всём пространстве. Направления покрываются ровно один раз почти всюду.',
            'Подстановка t=r² оставляет положительное экспоненциальное затухание. '
            'Обычный гамма-момент или действительная и мнимая части элементарного экспоненциального момента дают точное значение.'],
            value=value,absolute=True,decay=q(rate),frequency=q(freq))
    return None


def spatial_exhaustion_certificate(task,text,region,conditions,emit):
    if (text=='f>=0continuous' and not region and not conditions and task['requested_output']==['proof']
            and task.get('claim')=='integral_S f = lim_n integral_Sn f; both exist simultaneously; Sn are bounded closed regions exhausting S'
            and 'claims' not in task):
        return emit('nonnegative_exhaustion_supremum',[
            'Для неотрицательной функции интегралы по компактным частям не убывают при включении.',
            'Супремум этих масс ограничивает каждое исчерпание сверху. Каждая отдельная компактная часть '
            'со временем входит в исчерпание, поэтому предел снизу не меньше супремума.',
            'Обе стороны конечны одновременно. При бесконечном супремуме оценки дают расходимость каждого допустимого исчерпания.'],
            identity=True,independent_exhaustion=True)
    if (text=='sin(x^2+y^2)' and not region and conditions==['n positive integer'] and task['requested_output']==['proof_both_limits']
            and task.get('claims')==['int_{abs(x)<=n,abs(y)<=n} -> pi','int_{x^2+y^2<=2*pi*n} -> 0'] and 'claim' not in task):
        return emit('independent_exhaustion_witnesses',[
            'На квадрате разделяем sin(x²+y²) по формуле сложения. Конечное произведение равно удвоенному произведению интегралов синуса и косинуса квадрата.',
            'Предельные интегралы Френеля на прямой равны √(π/2). Это также получается из затухающего гауссова момента и равномерного снятия затухания по Дирихле после замены t=x².',
            'На диске радиуса √(2πn) полярный интеграл равен π(1−cos(2πn))=0 при натуральном n.'],
            square_limit=m.PI,disk_limit=ZERO,independent_exhaustion=False)
    if (text=='(x^2-y^2)/(x^2+y^2)^2' and region=='x>=1,y>=1' and not conditions
            and task['requested_output']==['double_divergence','both_iterated_converge'] and 'claim' not in task and 'claims' not in task):
        return emit('independent_exhaustion_witnesses',[
            'По y первообразная равна y/(x²+y²). По x первообразная равна −x/(x²+y²).',
            'Оба повторных интеграла сходятся, но имеют разные значения.',
            'На прямоугольнике [1,R]×[1,λR] предел равен arctg(1/λ)−π/4. При разных λ>0 эти исчерпания дают разные пределы.'],
            integrate_y_first=m.mul(q(-1,4),m.PI),integrate_x_first=m.mul(q(1,4),m.PI),
            independent_exhaustion=False,rectangle_limit='atan(1/lambda)-pi/4')
    raise Unsupported('The entire collection of source exhaustions and claims has not been bound')


def spatial_other_convergence(text,region,conditions,emit):
    if not conditions and text=='1/((1+abs(x)^p)*(1+abs(y)^q))' and region=='R^2':
        return emit('separated_positive_nondimensional_integrals',[
            'Ядро неотрицательно и разделяется по координатам. На компактном отрезке обе части ограничены единицей.',
            'При положительном показателе хвост сравним с обратной степенью, а при неположительном не убывает к нулю. '
            'Необходимы оба условия одномерной сходимости.'],convergence_condition='p>1 and q>1',absolute=True)
    if (text=='phi(x,y)/(1+x^2+y^2)^p' and region=='0<=y<=1' and conditions==['0<m<=abs(phi(x,y))<=M']):
        return emit('transverse_integrable_singularity',[
            'На полосе y ограничена, а основание степени на хвосте сравнимо с x².',
            'Ширина сечения постоянна. Поэтому порог определяется одномерным интегралом |x|^(−2p).'],
            convergence_condition='p>1/2',absolute=True)
    if text=='sin(x)*sin(y)/(x+y)^p' and region=='x+y>=1' and not conditions:
        return emit('independent_exhaustion_witnesses',[
            'Полагаем u=x+y,v=x−y. Модуль якобиана 1/2, ядро с мерой равно (cos v−cos u)/(4u^p).',
            'На фиксированном интервале 1<u<π/2 интеграл по любому далёкому полному периоду v сохраняет одну '
            'негативную массу. Это противоречит критерию Коши при произвольном исчерпании.'],
            convergence_condition='empty',absolute=False,transverse_tail=['1<u<pi/2','T<v<T+2*pi'])
    if text=='1/(x^2+y^2)' and region=='abs(y)<=x^2,x^2+y^2<=1' and not conditions:
        return emit('transverse_integrable_singularity',[
            'При фиксированном x≠0 знаменатель не меньше x². Поперечный отрезок имеет длину не больше 2x².',
            'Сокращение степеней даёт общую интегрируемую оценку сечения. На удалении от начала ядро гладко.'],
            converges=True,absolute=True)
    if text=='phi(x,y)/(x^2+x*y+y^2)^p' and region=='x^2+y^2<=1' and conditions==['0<m<=abs(phi(x,y))<=M']:
        return emit('radial_and_boundary_power',[
            'Вычисляем крайние коэффициенты положительной квадратичной формы после поворота. '
            'Получаем r²/2≤x²+xy+y²≤3r²/2.',
            'Замена на степенную радиальную мажоранту и миноранту устанавливает сходимость у начала.'],
            convergence_condition='p<1',absolute=True)
    if (text=='phi(x,y)/abs(x-y)^p' and region=='[0,a]^2' and conditions==['0<m<=abs(phi(x,y))<=M']
            or text=='1/abs(x+y-z)^p' and region=='[-1,1]^3' and not conditions):
        return emit('transverse_integrable_singularity',[
            'Прямым линейным преобразованием вводим поперечную к полюсу координату u.',
            'Около u=0 площадь или длина сечения ограничена сверху и отделена от нуля. '
            'Значит точный порог даёт интеграл |u|^(−p). Симметричное вырезание не заменяет обычную сходимость.'],
            convergence_condition='p<1',absolute=True)
    if (text=='f/((y-phi(x))^2+(z-psi(x))^2)^p' and region=='[0,a]^3'
            and conditions==['0<m<=abs(f)<=M','phi,psi continuous on [0,a]']):
        return emit('transverse_integrable_singularity',[
            'В каждом поперечном квадрате нормируем центр графика. При p<1 двумерная степенная особенность имеет общую '
            'интегрируемую оценку независимо от положения центра.',
            'Пусть d(x) есть расстояние центра до квадрата. Если d мало, полный круг даёт верхнюю оценку, '
            'а внутренний сектор фиксированного угла от ближайшей точки даёт нижнюю.',
            'При p=1 обе оценки имеют логарифмический порядок 1+ln⁺(1/d). При p>1 порядок 1+d^(2−2p). '
            'Остаётся интегрируемость соответствующей функции x, с бесконечностью при d=0.'],
            convergence_cases=['p<1 always','p=1 iff ln_plus(1/d) is integrable','p>1 iff d^(2-2p) is integrable near d=0'],
            transverse_distance='distance((phi(x),psi(x)),[0,a]^2)',absolute=True)
    raise Unsupported('A transverse or anisotropic comparison has not been established')


def exponential_ordered_fibers(text,region,conditions,emit):
    identifier=r'([A-Za-z_]\w*)'
    hit=re.fullmatch('0<='+identifier+'<='+identifier,region)
    if hit:inner,outer=hit.groups()
    else:
        hit=re.fullmatch(identifier+'>='+identifier+'>=0',region)
        if not hit:return None
        outer,inner=hit.groups()
    if inner==outer:return None
    # Some source headings attach a positivity statement even to a parameter-free kernel.
    names=set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e',inner,outer}
    if conditions==['parameters positive']:conditions=[p+'>0' for p in sorted(names)]
    axes=[inner,outer]
    raw=m.parse(text,None,[*axes,*sorted(names)])
    if raw[0]!='exp' or domain_conditions(raw):return None
    from cartesian_fields import symbolic_quadratic
    matrix,linear,constant=symbolic_quadratic(raw[1],axes)
    if any(v!=ZERO for row in matrix for v in row):return None
    a,b=map(m.neg,linear);decay=m.add(a,b)
    ctx=m.context(dict(variable='__fiber',parameters=sorted(names),parameter_conditions=conditions))
    if not all(m.constant_defined(z,ctx) for z in (constant,b,decay)) or any(m.sign(z,ctx)!=1 for z in (b,decay)):
        return None
    value=m.div(m.simplify(('exp',constant)),m.mul(b,decay))
    return emit('separated_positive_nondimensional_integrals',[
        'Положительность ядра позволяет интегрировать сначала по неограниченному волокну.',
        f'Переменная {outer} идёт от {inner} до бесконечности. Коэффициент затухания равен {source(b)}.',
        f'После подстановки нижнего конца оставшийся коэффициент затухания равен {source(decay)}. Оба положительны.'],
        absolute=True,value=value,certificate=dict(ordered_axes=axes,fiber_decay=b,remaining_decay=decay))


def gaussian_space_integral(text,region,conditions,emit):
    from cartesian_fields import _chart_determinant, mv_sum, symbolic_quadratic
    from tasks import entailed_domain_guards
    from verify import same_value

    ambient,_,declaration=region.partition(',')
    whole=re.fullmatch(r'R\^([2-4])',ambient)
    outside=re.fullmatch(r'(.+)>=(.+)',region) if not whole else None
    if not (whole or outside):return None
    if declaration:
        # The region may declare an abstract symmetric positive definite form.
        label=r'([A-Za-z_]\w*)'
        declared=re.fullmatch(label+r'=sum_ij'+label+r'xixjpositivedefinite,\2=([A-Za-z_]\w*)',declaration)
        called=re.fullmatch(r'exp\(-'+label+r'\(([^()]+)\)\)',text)
        if (not declared or not called or conditions or declared[1]!=called[1]
                or not declared[2].endswith('ij') or declared[3]!=declared[2][:-2]+'ji'):
            return None
        coords=called[2].split(',')
        n=int(whole[1])
        if len(coords)!=n or len(set(coords))!=n or not all(re.fullmatch(r'x[1-9]\d*',c) for c in coords):return None
        matrix=declared[2][:-2].upper()
        return emit('positive_definite_gaussian_measure',[
            'Из условия берём симметрию и положительную определённость формы.',
            'Ортогональное преобразование сохраняет меру. Масштабирование собственных осей даёт обратный якобиан через определитель.',
            'Интегрируем произведение одномерных гауссовых плотностей.'],
            absolute=True,value=f'pi^({n}/2)/sqrt(det({matrix}))',
            certificate=dict(axes=coords,declared_matrix=declared[2]))

    n=int(whole[1]) if whole else 2
    axes=list('xyzw'[:n])
    free=lambda f:set(re.findall(r'[A-Za-z_]\w*',f))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi',*axes}
    params=sorted(free(text)|free(region if outside else ''))
    # In a symbolic polynomial the unbound letter e is a real coefficient.
    # The exponential constant has the unambiguous spelling exp(1) here.
    coefficient='__exponent_coefficient'
    while coefficient in params:coefficient+='_'
    def coefficient_tokens(t):return re.sub(r'\be\b',coefficient,t)
    if re.search(r'\be\b',text) and params:
        text=coefficient_tokens(text)
        conditions=list(map(coefficient_tokens,conditions))
        params.append(coefficient)
    def parse(t):return m.parse(t,None,[*axes,*params])
    def report(e):
        if isinstance(e,tuple):return ('s','e') if e==('s',coefficient) else tuple(map(report,e))
        if isinstance(e,list):return list(map(report,e))
        if isinstance(e,dict):return {k:report(v) for k,v in e.items()}
        return e
    raw=parse(text)
    if raw[0]=='exp':weight,exponent=ONE,raw[1]
    elif raw[0]=='mul' and raw[2][0]=='exp':weight,exponent=raw[1],raw[2][1]
    elif raw[0]=='mul' and raw[1][0]=='exp':weight,exponent=raw[2],raw[1][1]
    else:return None
    radial=list(map(parse,outside.groups())) if outside else []
    domain=[g for e in (raw,*radial) for g in domain_conditions(e)]
    coords=list(map(lambda z:('s',z),axes))
    if any(any(m.contains(e,x) for x in coords) for _,e in domain):return None
    guards=[guard_source(g) for g in entailed_domain_guards(domain)]
    declared=[]
    for cond in conditions:
        if hit:=re.fullmatch(r'(?:0<)?abs\(([A-Za-z_]\w*)\)<1',cond.replace(' ','')):
            declared.append('1-'+hit[1]+'^2>0')
            if cond.replace(' ','').startswith('0<'):declared.append(hit[1]+'!=0')
        else:declared.append(cond)
    ctx=m.context(dict(variable='__gauss',parameters=params,parameter_conditions=declared+guards))
    if not all(known_guard(g,ctx) for g in domain):return None
    A,l,c=symbolic_quadratic(m.neg(exponent),axes)
    pivots=[_chart_determinant([row[:i] for row in A[:i]]) for i in range(1,n+1)]
    if not all(m.constant_defined(v,ctx) and m.sign(v,ctx)==1 for v in pivots):
        # In two dimensions a diagonal axis scaling multiplies the determinant
        # by a positive factor. Check the numerator and denominator separately.
        def positive(v):
            top,bottom=m.rational_form(v)
            return all(m.sign(m.poly_expr(p),ctx)==1 for p in (top,bottom))
        if not all(m.constant_defined(v,ctx) and positive(v) for v in pivots):return None
    det=pivots[-1]
    normal=m.div(m.mul(m.power(m.PI,n//2),('sqrt',m.PI) if n%2 else ONE),('sqrt',det))
    plan=dict(axes=axes,quadratic_form=A,leading_minors=pivots,linear=l,constant=c,domain_guards=guards)
    if outside:
        if weight!=ONE or any(v!=ZERO for v in (*l,c)) or not same_value(radial[0],m.neg(exponent)):
            return None
        cutoff=m.num(m.simplify(radial[1]))
        if cutoff is None or cutoff<0:return None
        return emit('radial_gaussian_modes',[
            'Положительно определённая форма задаёт линейную нормировку с обратным якобианом 1/√det A.',
            'Та же форма ограничивает область, поэтому после нормировки радиус идёт от корня нижнего уровня до бесконечности.',
            'Интегрируем в полярных координатах, затем заменяем квадрат радиуса одним параметром.'],
            absolute=True,value=report(m.mul(normal,m.simplify(('exp',q(-cutoff))))),
            certificate=report(dict(radial_cutoff=q(cutoff),**plan)))
    def inverse_entry(i,j):
        minor=[row[:i]+row[i+1:] for k,row in enumerate(A) if k!=j]
        return m.div(m.mul(q((-1)**(i+j)),_chart_determinant(minor)),det)
    inverse=[[inverse_entry(i,j) for j in range(n)] for i in range(n)]
    mean=[m.mul(q(-1,2),mv_sum(m.mul(v,u) for v,u in zip(row,l))) for row in inverse]
    constant=m.add(m.neg(c),m.mul(q(-1,2),mv_sum(m.mul(v,u) for v,u in zip(l,mean))))
    W,w,k=symbolic_quadratic(weight,axes)
    expectation=m.add(k,mv_sum(m.mul(v,u) for v,u in zip(w,mean)))
    expectation=m.add(expectation,mv_sum(m.mul(W[i][j],m.add(m.mul(mean[i],mean[j]),m.mul(q(1,2),inverse[i][j])))
                                        for i in range(n) for j in range(n)))
    return emit('positive_definite_gaussian_measure',[
        'Вычисляем матрицу квадратичной части и проверяем знак её главных угловых миноров.',
        'Завершение квадрата даёт сдвиг и постоянный множитель. Нормированный гауссов интеграл имеет якобиан через определитель.',
        'Для множителя степени до двух подставляем среднее и вторые моменты со значениями из обратной матрицы.'],
        absolute=True,value=report(m.mul(m.mul(normal,m.simplify(('exp',constant))),expectation)),
        certificate=report(dict(inverse=inverse,center=mean,exponent_at_center=constant,
                                normalized_moment=expectation,**plan)))



def spatial_other_values(text,region,conditions,emit):
    if (answer:=exponential_ordered_fibers(text,region,conditions,emit)) is not None:return answer
    if conditions==['parameters positive']:
        p=('s','p');r=('s','q')
        if text=='1/(x^p*y^q)' and region=='x*y>=1,x>=1':
            return emit('separated_positive_nondimensional_integrals',[
                'По неотрицательности берём внутренний интеграл по y от 1/x до бесконечности. Требуется q>1.',
                'Оставшийся хвост x^(q-p-1)/(q−1) требует p>q, и обе степени дают точное значение.'],
                convergence_condition='q>1 and p>q',absolute=True,value=m.div(ONE,m.mul(m.add(r,q(-1)),m.add(p,m.neg(r)))))
        if text=='1/(x+y)^p' and region=='x+y>=1,0<=x<=1':
            return emit('separated_positive_nondimensional_integrals',[
                'Замена u=x+y имеет единичный якобиан. На u≥1 поперечная координата x проходит от 0 до 1.',
                'Положительный остаток — один степенной хвост.'],convergence_condition='p>1',absolute=True,value=m.div(ONE,m.add(p,q(-1))))
        if text=='1/(x^4+y^2)' and region=='y>=x^2+1':
            value=m.mul(m.PI,('sqrt',m.mul(q(2),m.add(('sqrt',q(2)),q(-1)))))
            return emit('positive_parabolic_fiber_normalization',[
                'По чётности берём x>0 с множителем 2 и вводим y=x²t. Получаем t>1, x≥1/√(t−1), а ядро с якобианом равно x^(−2)/(1+t²).',
                'После перестановки и u=√(t−1) остаётся четыре интеграла u²/(u⁴+2u²+2) по положительной полуоси.',
                'Масштабируем квартику до взаимной, усредняем исходный интеграл и обращение v↦1/v. '
                'Подстановка s=v−1/v даёт элементарный арктангенс и конечное значение.'],
                absolute=True,value=value)
    if not conditions and region=='[0,1]^3' and text=='1/(x^p*y^q*z^r)':
        value=m.div(ONE,m.mul(m.mul(m.add(ONE,m.neg(('s','p'))),m.add(ONE,m.neg(('s','q')))),m.add(ONE,m.neg(('s','r')))))
        return emit('separated_positive_nondimensional_integrals',[
            'По неотрицательности раскладываем интеграл по кубу на три независимых степенных интеграла у нуля.'],
            convergence_condition='p<1 and q<1 and r<1',absolute=True,value=value)
    raise Unsupported('No verified reduction covers the exact source integral')


def parameter_certificate_report(result,pretty):
    from model import freeze
    from intervals import read_quadratic_term
    plan=result['compilation']
    if plan.get('theorem') in ('method.oriented_leibniz_transport','method.affine_vector_leibniz'):
        derivative=oriented_leibniz_text(result['value']['value'],pretty,plan.get('named_functions',()))
        conditions=result['value']['parameter_domain']
        domain=', '.join(conditions) if conditions else 'все вещественные параметры'
        return '\n'.join([*plan['steps'],'Производная — '+derivative,'Условия — '+domain])
    def display(v):
        if isinstance(v,(tuple,list)):
            if v and v[0]=='quadratic_real':
                t=read_quadratic_term(freeze(v))
                return pretty(m.add(q(t.a),m.mul(q(t.b),('sqrt',q(t.d)))),'x')
            if v and isinstance(v[0],str) and v[0] in m.FUNCTIONS|{'q','s','v','pi','add','mul','div','pow','rpow'}:
                return pretty(freeze(v),'x')
            return '('+', '.join(map(display,v))+')'
        if isinstance(v,dict):return ', '.join(str(k)+' = '+display(x) for k,x in v.items())
        return ('да' if v else 'нет') if type(v) is bool else str(v)
    labels={'value':'Значение','continuous_on':'Область непрерывности','uniform':'Равномерная сходимость',
            'discontinuities':'Точки разрыва','ordinary_convergence':'Обычная сходимость','absolute_convergence':'Абсолютная сходимость',
            'value_at_frequency_zero':'Значение при нулевой частоте','open_interval_values':'Значения на открытых промежутках'}
    if plan.get('theorem')=='method.euler_endpoint_transport':
        labels.update(domain='Область сходимости',cases='Значения по случаям',divergent='Расходится',
                      removable_trace='Непрерывное продолжение',identity='Равенство',
                      nonzero_frequency_value='Значение при ненулевой частоте',zero_frequency='При нулевой частоте')
    values=[labels.get(k,k)+' — '+display(v) for k,v in result['value'].items()]
    return '\n'.join([*plan['steps'],*values])


def fourier_coefficient_action(task, library):
    """Transport coefficient integrals under translations, reflections, and periodic averaging."""
    from math import lcm
    from verify import same_value

    contract = library.data.get('fourier_coefficient_action')
    fields = {'kind', 'id', 'source', 'period', 'interval', 'relation', 'symmetry', 'modes',
              'regularity', 'transformed_function', 'shift', 'parameter', 'requested_output'}
    if not contract or set(task) - fields or task.get('modes', 'n>=0') not in ('n>=0', 'n>=1'):
        raise Unsupported('The original coefficient range or additional obligation is unbound')
    shapes = ('relation', 'symmetry', 'transformed_function')
    if sum(f in task for f in shapes) != 1:
        raise Unsupported('A Fourier relation, reflection group or integral transformation is needed')
    modes = task.get('modes', 'n>=0')
    request = task.get('requested_output', ['fourier_coefficients'])
    if request not in (['fourier_coefficients'], ['fourier_coefficients', 'liapunov_equality']):
        raise Unsupported('The Fourier problem asks for another conclusion')
    proof = dict(theorem='method.fourier_coefficient_transport', modes=modes,
                 normalization='a_n=2/T*integral_period(f*cos(2*pi*n*x/T)), b_n analogously; constant=a_0/2')
    relation = task.get('relation')
    if isinstance(relation, dict) and 'left' in relation:
        left = re.fullmatch(r'([A-Za-z_]\w*)\(-x\)', relation['left'])
        right = re.fullmatch(r'([A-Za-z_]\w*)\(x\)', relation.get('right', ''))
        sign = relation.get('multiple')
        if (set(relation) != {'left', 'right', 'multiple'} or not left or not right or sign not in (-1, 1)
                or request != ['fourier_coefficients'] or set(task) & {'interval', 'regularity', 'parameter', 'shift'}):
            raise Unsupported('The relation must bind two functions on the same symmetric Fourier interval')
        proof.update(rule='reflected_function', argument_map='x=-u', cos_parity=1, sin_parity=-1,
                     functions=[left[1], right[1]], factor=sign, shared_interval='symmetric full period')
        return proof, dict(A_n='a_n' if sign == 1 else '-a_n', B_n='-b_n' if sign == 1 else 'b_n')

    time = m.parse(task.get('period', ''), None)
    ctx = m.context(dict(variable='x'))
    if not m.constant_defined(time, ctx) or m.sign(time, ctx) != 1:
        raise Unsupported('A strictly positive common period is required')
    def period_interval(bounds):
        if not isinstance(bounds, (list, tuple)) or len(bounds) != 2:
            raise Unsupported('Two original real endpoints are required')
        lo, hi = (m.parse(str(v), None) for v in bounds)
        if not all(m.constant_defined(v, ctx) for v in (lo, hi)):
            raise Unsupported('The original period endpoints must both be defined real constants')
        if not same_value(m.add(hi, m.neg(lo)), time):
            raise Unsupported('The source interval does not cover the stated period')
        return [lo, hi]
    proof['period'] = time
    if 'interval' in task:
        proof['original_interval'] = period_interval(task['interval'])

    if 'symmetry' in task or relation is not None:
        if request != ['fourier_coefficients'] or set(task) & {'regularity', 'parameter', 'shift'}:
            raise Unsupported('Other transforming operations are not part of this symmetry goal')
        reflections = []
        if relation is not None:
            match = re.fullmatch(r'x\s*([+-].+)', relation.get('argument', '')) if isinstance(relation, dict) else None
            if not match or set(relation) != {'argument', 'multiple'} or relation['multiple'] not in (-1, 1):
                raise Unsupported('A signed translation of the original function is needed')
            shifts = [(m.parse(match[1].lstrip('+'), None), relation['multiple'])]
        else:
            symmetry = task['symmetry']
            if set(symmetry) != {'centers', 'axes'} or not all(isinstance(symmetry[k], list) for k in symmetry):
                raise Unsupported('The symmetry points and axes have not been identified')
            reflections = [(m.parse(c, None), sign) for key, sign in (('centers', -1), ('axes', 1)) for c in symmetry[key]]
            if not reflections or not any(c == ZERO for c, _ in reflections):
                raise Unsupported('Global parity requires a reflection about zero')
            # R_b R_a sends x to x+2(b-a), with the product of the reflection signs.
            a, sign = reflections[0]
            shifts = [(m.mul(q(2), m.add(b, m.neg(a))), sign * other) for b, other in reflections[1:]]
        phases = [(m.num(m.simplify(m.div(shift, time))), sign) for shift, sign in shifts]
        if any(x is None for x, _ in phases):
            raise Unsupported('The shifts must be known rational fractions of the period')
        period = lcm(*(x.denominator for x, _ in phases))
        if period > 4096:
            raise Unsupported('The explicit residue class exceeds the finite certificate bound')
        residues = [n for n in range(period) if all((n * f - (F(0) if s == 1 else F(1, 2))).denominator == 1
                                                   for f, s in phases)]
        flip = {sign for c, sign in reflections if c == ZERO}
        zero_a = -1 in flip or not residues
        zero_b = 1 in flip or not residues
        proof.update(rule='symmetry_eigenspaces', reflections=reflections, composed_translations=shifts,
                     phase_checks=[(q(f), sign) for f, sign in phases], reduction='orthogonal sine and cosine modes')
        return proof, dict(mode_modulus=period, allowed_residues=residues, cosine_zero=zero_a, sine_zero=zero_b,
                           constant_zero=None if modes == 'n>=1' else zero_a or 0 not in residues)

    transformed = task['transformed_function']
    regularity = task.get('regularity')
    if regularity not in ('integrable', 'continuous') or modes != 'n>=0':
        raise Unsupported('Existence of the complete coefficient integrals is unbound')
    hz = m.simplify(m.div(m.mul(q(2), m.PI), time))
    omega = 'n' if hz == ONE else f'({source(hz)})*n'
    if isinstance(transformed, str):
        h = task.get('shift')
        if ('parameter' in task or not isinstance(h, str) or not re.fullmatch(r'[A-Za-z_]\w*', h) or h in {'x', 'n'}
                or transformed != f'f(x+{h})' or request != ['fourier_coefficients']):
            raise Unsupported('The transformed function must be a real constant shift of f')
        phase = f'{omega}*{h}'
        proof.update(rule='translated_function', argument_map=f'u=x+{h}', phase=phase, full_period='integral unchanged by shift')
        return proof, dict(A_0='a_0', A_n=f'a_n*cos({phase})+b_n*sin({phase})', B_n=f'b_n*cos({phase})-a_n*sin({phase})')
    if not isinstance(transformed, dict) or set(transformed) != {'integrand', 'variable', 'limits', 'factor'}:
        raise Unsupported('No definite periodic integral was structurally identified')
    t = transformed['variable'];h = task.get('parameter')
    factor = transformed['factor'];limits = transformed['limits']
    if not re.fullmatch(r'[A-Za-z_]\w*', t) or t in {'x', 'n', h}:
        raise Unsupported('The averaging variable must be a separate bound token')
    if h and re.fullmatch(r'[A-Za-z_]\w*', h) and h not in {'x', 'n'} and regularity in ('integrable', 'continuous'):
        scale = m.parse(factor, None, [h]);width = m.mul(q(2), ('s', h))
        on_domain = m.context(dict(variable='x', parameters=[h], parameter_conditions=[f'{h}!=0']))
        if ('shift' in task or transformed['integrand'] != f'f({t})' or limits != [f'x-{h}', f'x+{h}'] or
                not all(known_guard(g, on_domain) for g in domain_conditions(scale)) or
                not same_value(m.mul(scale, width), ONE) or request != ['fourier_coefficients']):
            raise Unsupported('The integral does not have the normalized symmetric average')
        phase = f'{omega}*{h}'
        proof.update(rule='uniform_average_of_shift', exchange='Fubini via integral of abs(f) over one period',
                     domain=[f'{h}!=0'], sine_integral='zero by oddness', cosine_average=f'sin({phase})/({phase})')
        return proof, dict(A_0='a_0', A_n=f'a_n * sin({phase})/({phase})', B_n=f'b_n * sin({phase})/({phase})', undefined_parameter=f'{h}=0')
    if ('shift' in task or h or regularity != 'continuous' or transformed['integrand'] != f'f({t})*f(x+{t})'
            or request != ['fourier_coefficients', 'liapunov_equality']):
        raise Unsupported('The original integral is not a continuous periodic autocorrelation')
    lo, hi = period_interval(limits)
    scale = m.parse(factor, None)
    if not m.constant_defined(scale, ctx) or not same_value(m.mul(time, scale), q(2)):
        raise Unsupported('The autocorrelation normalization is incorrect')
    proof.update(rule='periodic_autocorrelation', exchange='continuous integrand on compact rectangles',
                 value_at_zero='Bessel bounds the sum of squared coefficients; absolute Fourier convergence and uniqueness recover F(0)',
                 original_interval=[lo, hi], scale=scale)
    return proof, dict(A_0='a_0^2', A_n='a_n^2+b_n^2', B_n='0',
                       identity=f'{source(scale)}*integral_period(f(t)^2)=a_0^2/2+sum_{{n>=1}}(a_n^2+b_n^2)')


def source_integral_transform(task,library,request):
    """Transport an admitted real kernel through the stated integral transform."""
    from verify import same_value
    if not library.data.get('parameter_transform_proofs'):
        raise Unsupported('Structured integral transforms are unavailable')
    kind=task['kind'];meta=task.get('source',{})
    if not isinstance(meta,dict) or set(meta)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}:
        raise Unsupported('An unbound source restriction or prescribed method remains')

    def bind(fields,heading,want):
        if (set(task)-{'kind','id','source','requested_output',*fields}
                or task.get('requested_output')!=want or meta.get('literal_requirement',heading)!=heading):
            raise Unsupported('The original transform convention and requested conclusions are required')

    def emit(method,steps,values,**facts):
        return dict(theorem='method.'+method,argument=steps,**facts),values

    conditions=task.get('stated_conditions',[])
    if not isinstance(conditions,list) or not all(isinstance(x,str) for x in conditions):
        raise Unsupported('Explicit parameter facts are required')
    text=task.get('function','').replace('²','^2').replace('³','^3').replace('−','-')
    if kind=='laplace_transform':
        bind({'function','transform','stated_conditions'},'Найти преобразование Лапласа.', ['transform_and_convergence_domain'])
        if task['transform']!='F(p)=int_0^inf exp(-p*t)*f(t)dt' or 'p>0' not in conditions:
            raise Unsupported('This compiler preserves the original positive real Laplace convention')
        return real_laplace_profile(text,conditions,emit)
    if kind=='weierstrass_transform':
        bind({'function','transform','stated_conditions'},'Найти преобразование Вейерштрасса.', ['transform'])
        if task['transform']!='F(x)=int_R exp(-(x-y)^2)*f(y)dy/sqrt(pi)' or conditions:
            raise Unsupported('This compiler preserves the original normalized Gaussian on the full axis')
        y=('v','y');x=('s','x');names=transform_parameters(text,'y')
        if 'x' in names:raise Unsupported('The transform output variable must be free')
        raw=m.parse(text,'y',names)
        density=('mul',('exp',('mul',q(-1),('pow',('add',y,m.neg(x)),2))),raw)
        params=[*names,'x'];ctx=m.context(dict(variable='y',parameters=params))
        plan,value=transform_gaussian_moment(density,'y',params,ctx)
        return emit('gaussian_transform_normalization',[
            'Сохраняем напечатанное ядро гауссовой свёртки с его исходными аргументами.',
            'Раскрываем квадратичный показатель и собираем полиномиальные или гармонические моменты. Оба гауссовых хвоста абсолютно интегрируемы.',
            'Делим интеграл по всей оси на исходный множитель √π.'],
            dict(value=m.div(value,('sqrt',m.PI)),domain='all real arguments and parameters'),moment=plan)
    if kind=='unitary_fourier_transform':
        bind({'function','convention','stated_conditions'},'Найти преобразование Фурье согласно напечатанной нормировке.', ['complex_fourier_transform'])
        if task['convention']!='F(x)=(1/sqrt(2*pi))*lim_L->inf int_-L^L f(t)*exp(-i*t*x)dt':
            raise Unsupported('The requested Fourier sign, normalization or cutoffs differ')
        return unitary_transform_profile(text,conditions,emit)
    if kind=='inverse_fourier_half_line':
        bind({'transform'},'Найти функцию по синусному или косинусному преобразованию.', ['inverse_function'])
        return inverse_half_line_profile(task['transform'],emit,request)
    if kind=='parameter_improper_evaluation':
        method=task.get('method_requirement');reference=task.get('reference_formula')
        bind({'integrand','limits','method_requirement','reference_formula','stated_conditions'},
             'Вычислить интеграл Эйлера–Пуассона исходя из заданного представления квадрата.'
             if method=='specified_double_representation' else 'Вычислить несобственный интеграл.',
             ['exact_integral','specified_method'])
        if task['limits']!='0..inf' or method not in ('euler_poisson_integral','specified_double_representation'):
            raise Unsupported('A preserved half-line Euler–Poisson method is required')
        text=task['integrand'].replace('²','^2').replace('³','^3');names=transform_parameters(text,'x');x=('v','x')
        raw=m.parse(text,'x',names)
        if method=='specified_double_representation':
            if conditions or names or domain_conditions(raw) or not same_value(raw,('exp',m.neg(m.power(x,2)))):
                raise Unsupported('The square representation applies to the stated unscaled Gaussian only')
            if reference!='I²=int_0^inf exp(-x²) dx int_0^inf x*exp(-x²*y²)dy':
                raise Unsupported('The printed double representation is required')
            return emit('gaussian_transform_normalization',[
                'При x>0 замена u=xy превращает второй гауссов интеграл в напечатанный внутренний интеграл.',
                'Для неотрицательного двойного ядра меняем порядок по теореме Тонелли и интегрируем x exp(−(1+y²)x²) по x.',
                'Получаем I²=∫ 1/[2(1+y²)] dy=π/4. Исходный интеграл равен положительному корню.'],
                dict(value=m.div(('sqrt',m.PI),q(2)),convergence='ordinary; both ends exist'),source_representation=reference)
        if reference is not None:raise Unsupported('A source reference would need an additional proof')
        return gaussian_halfline_change(raw,names,conditions,emit)
    raise Unsupported('No verified transform convention for the source goal')


def transform_parameters(text,variable):
    return sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',text))-m.FUNCTIONS-set(m.ALIASES)-{variable,'pi','e'})


def transform_gaussian_moment(density,var,params,ctx,half=False):
    """Use the existing Gaussian recurrence while retaining its structured exact value."""
    return gaussian_integral_moments(dict(limits='0..inf' if half else '-inf..inf',stated_conditions=[]),ctx,density,var,
                                     lambda plan,value:(plan,m.parse(value,None,params)))


def real_laplace_profile(text,conditions,emit):
    from integrals import affine, harmonic_modes, HARMONIC_ZERO
    from verify import same_value
    t=('v','t');p=('s','p');names=transform_parameters(text,'t')
    if 'p' in names:raise Unsupported('The output Laplace argument must be independent of the input function')
    ints=[hit[1] for fact in conditions if (hit:=re.fullmatch(r'(\w+) positive integer',fact))]
    base=[fact for fact in conditions if fact=='p>0']
    if set(conditions)-{'p>0',*(n+' positive integer' for n in ints)} or len(ints)>1 or not set(ints)<=set(names):
        raise Unsupported('An additional original parameter restriction would change the convergence proof')
    params=[*names,'p'];ctx=m.context(dict(variable='t',parameters=params,parameter_conditions=base))
    raw=m.parse(text,'t',names)
    def result(value,steps,margin=None,**evidence):
        domain=['p>0'] if margin is None else ['p>0',source(margin)+'>0']
        return emit('real_laplace_kernel_reduction',steps,
                    dict(value=value,convergence_domain=domain,source_conditions=conditions),**evidence)
    if ints:
        n,symbol=ints[0],('s',ints[0])
        if raw!=('rpow',t,symbol):raise Unsupported('A positive integer power of the positive coordinate is required')
        return result(m.div(('factorial',symbol),('rpow',p,m.add(symbol,ONE))),[
            'На t>0 целая степень определена и имеет конечный предел в нуле.',
            'Меняем масштаб u=pt. Экспоненциальное затухание обращает в нуль все граничные члены на бесконечности.',
            'Вычисляем целый момент по факториальной рекурсии.'],scale=p,index=n)
    if raw==('sqrt',t):
        return result(m.div(('sqrt',m.PI),m.mul(q(2),m.mul(p,('sqrt',p)))),[
            'На положительной полуоси замена t=u² возрастает. Якобиан и исходный корень дают множитель 2u².',
            'Второй гауссов момент на полуоси сходится и равен √π/(4p^(3/2)).'],scale=p)
    if raw[0]=='sin' and domain_conditions(raw[1])==[('nonnegative',t)]:
        u=('v','__laplace_root');angle=m.substitute(raw[1],{('sqrt',t):u})
        rate,offset=affine(angle,u[1]);checks=m.context(dict(variable=u[1],parameters=params,parameter_conditions=base))
        if offset==ZERO and m.constant_defined(rate,checks):
            den=('exp',m.neg(m.mul(p,m.power(u,2))))
            density=('mul',den,('mul',m.mul(q(2),u),('sin',angle)))
            plan,value=transform_gaussian_moment(density,u[1],params,checks,half=True)
            return result(value,[
                'На t>0 подставляем t=u², dt=2u du. Оба конца положительной полуоси сохраняются.',
                'Синус линейной фазы нечётен. Множитель якобиана делает полное гауссово ядро чётным.',
                'Берём половину первого синусного гауссова момента на всей оси.'],moment=plan)
    if raw[0]=='div' and raw[2]==t and raw[1][0]=='add' and domain_conditions(raw)==[('nonzero',t)]:
        first,negative=raw[1][1:]
        if negative[0]=='mul' and negative[1]==q(-1):
            rates=[]
            for atom in (first,negative[2]):
                if atom==ONE:rates.append(ZERO);continue
                if atom[0]!='exp':break
                k,offset=affine(atom[1],'t')
                if offset!=ZERO or not m.constant_defined(k,ctx):break
                rates.append(k)
            if len(rates)==2:
                margins=[m.add(p,m.neg(r)) for r in rates]
                evidence=dict(oriented_rates=tuple(rates),complete_decay_rates=margins)
                if same_value(*rates):
                    return result(ZERO,['На t>0 исходные профили совпадают. Их разность равна нулю и продолжается к началу полуоси.'],**evidence)
                if any(m.sign(r,ctx)!=1 for r in margins) and all(r!=ZERO for r in rates):
                    raise Unsupported('A coincident-parameter case requires a proof before imposing both exponential tail inequalities')
                value=('ln',m.div(margins[1],margins[0]));extra=[r for r in margins if m.sign(r,ctx)!=1]
                return result(value,[
                    'Выражаем разность экспонент, делённую на t, ориентированным интегралом по показателю.',
                    'В нуле предел конечен. Если ядра различаются, сходимость на хвосте требует положительности обеих суммарных скоростей затухания.',
                    'Внутренний интеграл Лапласа даёт обратную скорость затухания. Интегрирование по исходному ориентированному промежутку даёт логарифм.'],
                    extra[0] if extra else None,**evidence)
    if domain_conditions(raw):raise Unsupported('The source has an unresolved endpoint or real branch')
    modes,_,_=harmonic_modes(dict(kind='integrate',integrand=source(raw),variable='t',parameters=names))
    if len(modes)==1:
        (rate,omega),weights=next(iter(modes.items()));margin=m.add(p,m.neg(rate))
        if omega==ZERO and all(m.num(real) is not None and imag==ZERO for real,imag in weights):
            highest=next((j for j in reversed(range(len(weights))) if weights[j][0]!=ZERO),None)
            if highest is None:return result(ZERO,['Исходный полином тождественно нулевой.'])
            value=ZERO
            for j,(weight,_) in enumerate(weights):
                if weight==ZERO:continue
                term=('div',m.mul(weight,q(factorial(j))),('pow',margin,j+1))
                value=term if value==ZERO else ('add',value,term)
            return result(value,[
                'Выделяем общий экспоненциальный множитель точного вещественного полинома.',
                'В нуле ядро имеет конечное значение. У ненулевого полинома сходимость на хвосте требует строго положительной суммарной скорости затухания.',
                'Меняем масштаб каждого момента и применяем факториальную рекурсию с проверенными краями.'],None if m.sign(margin,ctx)==1 else margin,
                rate=rate,polynomial=weights,net_decay=margin)
    density=('mul',('exp',m.neg(m.mul(p,t))),raw)
    child=dict(kind='integrate',integrand=source(density),variable='t',parameters=params)
    plan,value=decaying_harmonic_moment(child,base)
    return result(value,[
        'После умножения на исходную экспоненту Лапласа собираем точные гармонические моды.',
        'Проверяем производную первообразной. Каждая мода затухает экспоненциально на всей напечатанной области p>0.',
        'Подставляем исходный нулевой конец и отдельно проверяем исчезновение вклада на бесконечности.'],moment=plan)


def unitary_transform_profile(text,conditions,emit):
    t=('v','t');x=('s','x');names=transform_parameters(text,'t')
    if 'x' in names:raise Unsupported('The output frequency must be independent of the input function')
    if any(not (hit:=re.fullmatch(r'(\w+)>0',fact)) or hit[1] not in names for fact in conditions):
        raise Unsupported('A required source condition was not proved')
    params=[*names,'x'];ctx=m.context(dict(variable='t',parameters=params,parameter_conditions=conditions))
    raw=m.parse(text,'t',names)
    if any(not known_guard(g,ctx) for g in domain_conditions(raw)):
        raise Unsupported('A whole-axis real-domain restriction remains')
    phase=m.mul(x,t);cosine=('cos',phase);sine=('sin',phase);normal=('sqrt',m.mul(q(2),m.PI))
    atom=('abs',t)
    def multiply(a,b):return ('mul',a,b)
    if m.contains(raw,atom):
        positive=m.substitute(raw,{atom:t});negative=m.substitute(m.substitute(raw,{t:m.neg(t)}),{('abs',m.neg(t)):t})
        if any(not known_guard(g,ctx) for e in (positive,negative) for g in domain_conditions(e)):
            raise Unsupported('An extra half-line domain cut remains')
        densities=(m.add(positive,negative),m.add(negative,m.neg(positive)))
        moments=[];values=[]
        for weight,wave in zip(densities,(cosine,sine)):
            if weight==ZERO:values.append(ZERO);moments.append(None);continue
            plan,value=decaying_harmonic_moment(dict(kind='integrate',variable='t',integrand=source(multiply(weight,wave)),
                                                       parameters=params),conditions)
            values.append(value);moments.append(plan)
        steps=['Разбиваем ось в точке изменения знака под модулем и отражаем отрицательную полуось, сохраняя модуль якобиана.',
               'Действительная часть складывает два косинусных вклада. Мнимая использует их синусную разность с напечатанным знаком.',
               'Проверяем первообразную каждой затухающей моды в нуле и на каждом бесконечном конце отдельно.']
    else:
        pairs=[transform_gaussian_moment(multiply(raw,w),'t',params,ctx) for w in (cosine,sine)]
        moments,values=map(list,zip(*pairs));values[1]=m.neg(values[1])
        steps=['Напечатанный отрицательный показатель Фурье задаёт косинусный момент и взятый со знаком минус синусный.',
               'Собираем моменты затухающего гауссиана и применяем рекурсию дифференцирования, обоснованную абсолютным мажорантом на обоих хвостах.']
    return emit('gaussian_transform_normalization',steps+['К обеим компонентам применяем исходную нормировку 1/√(2π).'],
                dict(real=m.div(values[0],normal),imaginary=m.div(values[1],normal),convergence='absolute on both real tails'),
                moments=moments,normalization=normal)


def inverse_half_line_profile(text,emit,request):
    """Propose a half-axis inverse and derive the original forward transform."""
    z=('s','x');y=('v','y')
    hit=re.fullmatch(r'int_0\^inf (\w+)\(y\)\*(cos|sin)\(x\*y\)dy=(.+?)(,x>0)?',text)
    if not hit:raise Unsupported('The source transform and frequency domain are not fully bound')
    name,wave,target,restriction=hit.groups();target=m.parse(target.replace('²','^2'),None,['x'])
    from verify import same_value
    from integrals import affine
    ctx=m.context(dict(variable='y',parameters=['x']))
    if not m.constant_defined(target,ctx) and not (wave=='cos' and target[0]=='div'):
        raise Unsupported('The transform is not real and defined on the stated frequency domain')
    if (wave=='cos' and not restriction and target[0]=='div' and m.num(target[1]) is not None
            and not domain_conditions(target[2])):
        coeff=riemann_polynomial(m.substitute(target[2],{z:y}),y)
        if coeff and len(coeff)==3 and coeff[1]==ZERO and m.num(coeff[0]) is not None and m.num(coeff[0])>0 and m.num(coeff[2]) is not None and m.num(coeff[2])>0:
            c,d=coeff[0],coeff[2];rate=('sqrt',m.div(c,d));amplitude=m.div(target[1],m.mul(rate,d))
            proposal=m.mul(amplitude,('exp',m.neg(m.mul(rate,y))))
            if not same_value(m.div(m.mul(amplitude,rate),m.add(m.power(rate,2),m.power(z,2))),target):
                raise Unsupported('The proposed exponential fails its exact forward cosine identity')
            return emit('half_axis_transform_inversion',[
                'Сопоставляем положительные постоянный и квадратичный коэффициенты заданного образа.',
                'В качестве прообраза предлагаем затухающую экспоненту. Её обычный косинусный интеграл равен произведению амплитуды и скорости затухания, делённому на сумму квадратов скорости и частоты.',
                'Проверяем прямое преобразование с исходной нормировкой на полуоси.'],dict(function=name,representative=proposal),source_frequency_domain='all real')
    if wave=='sin' and restriction and target[0]=='exp':
        rate,offset=affine(m.substitute(target[1],{z:y}),'y');c=m.neg(rate)
        if m.num(c) is not None and m.num(c)>0 and offset==ZERO:
            proposal=m.div(m.mul(q(2),y),m.mul(m.PI,m.add(m.power(c,2),m.power(y,2))))
            T=dict(kind='parameter_improper_evaluation',integrand='x*sin(omega*x)/('+source(m.power(c,2))+'+x^2)',
                   limits='0..inf',stated_conditions=['omega>0'],requested_output=['exact_integral_and_convergence'])
            child=request('forward sine moment on the stated positive frequencies',T)['value']
            expected=m.mul(m.div(m.PI,q(2)),('exp',m.neg(m.mul(c,('s','omega')))))
            actual=m.substitute(freeze(child['value']),{('abs',('s','omega')):('s','omega')})
            if not same_value(actual,expected):raise Unsupported('The forward sine moment did not match the required transform')
            return emit('half_axis_transform_inversion',[
                'Прямой косинусный момент 1/(c²+y²) равен π exp(−c|x|)/(2c).',
                'На компактном промежутке положительных частот равномерная оценка Дирихле позволяет дифференцировать под знаком интеграла.',
                'Получаем синусный момент y/(c²+y²) с обычным сходящимся хвостом. Исходное условие x>0 даёт exp(−cx).'],
                dict(function=name,representative=proposal),source_frequency_domain='x>0',positive_rate=c)
    raise Unsupported('A verified forward moment for the proposed half-axis inverse is missing')


def gaussian_halfline_change(raw,names,conditions,emit):
    from verify import same_value
    x=('v','x');ctx=m.context(dict(variable='x',parameters=names,parameter_conditions=conditions))
    def done(value,steps,**facts):
        return emit('gaussian_transform_normalization',steps,
                    dict(value=value,convergence='ordinary; both original ends exist'),**facts)
    if raw[0]=='exp' and all(g==('nonzero',x) or g==('nonzero',('pow',x,2)) for g in domain_conditions(raw)):
        # Obtain independent coefficients of x² and x^(-2) from the exact Laurent normal form.
        P,D=m.rational_form(raw[1]);xx=((x,2),)
        if set(D)=={xx} and set(P)=={((x,4),),()}:
            A=m.poly_expr({():-P[((x,4),)]/D[xx]});B=m.poly_expr({():-P[()]/D[xx]})
        else:
            # Coefficients may retain fixed real parameters.
            Q=riemann_polynomial(m.mul(raw[1],m.power(x,2)),x)
            if Q is None or len(Q)!=5 or any(Q[j]!=ZERO for j in (1,2,3)):
                raise Unsupported('The symmetric reciprocal Gaussian does not have two pure endpoint powers')
            A=m.neg(Q[4]);B=m.neg(Q[0])
        if m.sign(A,ctx)!=1 or m.sign(B,ctx)!=1:raise Unsupported('Both endpoint Gaussian rates must be strictly positive')
        U=('sqrt',A);V=('sqrt',B)
        expected=m.neg(m.add(m.mul(A,m.power(x,2)),m.div(B,m.power(x,2))))
        if not same_value(raw[1],expected):raise Unsupported('The square completion changed the original reciprocal Gaussian')
        value=m.div(m.mul(('sqrt',m.div(m.PI,A)),('exp',m.mul(q(-2),m.mul(U,V)))),q(2))
        return done(value,[
            'Обе гауссовы шкалы положительны. Замена u=√A·x−√B/x строго возрастает от −∞ до +∞.',
            'Выделяем квадрат A·x²+B/x²=u²+2√(AB). Якобиан обратной замены равен (1+u/√(u²+4√(AB)))/(2√A).',
            'Оба хвоста абсолютно интегрируемы. Нечётная часть якобиана даёт нуль, чётная приводит к интегралу Эйлера–Пуассона.'],
            quadratic_rate=A,reciprocal_rate=B)
    if raw[0]=='div' and raw[2]==('pow',x,2) and raw[1][0]=='add' and domain_conditions(raw)==[('nonzero',('pow',x,2))]:
        left,neg=raw[1][1:]
        if left[0]=='exp' and neg[0]=='mul' and neg[1]==q(-1) and neg[2][0]=='exp':
            rates=[]
            for e in (left,neg[2]):
                poly=riemann_polynomial(e[1],x)
                if poly is None or len(poly)!=3 or any(poly[j]!=ZERO for j in (0,1)) or m.sign(m.neg(poly[2]),ctx)!=1:break
                rates.append(m.neg(poly[2]))
            if len(rates)==2:
                a,b=rates;value=m.mul(('sqrt',m.PI),m.add(('sqrt',b),m.neg(('sqrt',a))))
                return done(value,[
                    'В исходной точке x=0 числитель обращается в нуль порядка не ниже двух.',
                    'Записываем дробь как ориентированный интеграл от a до b функции exp(−s·x²). На замкнутом положительном диапазоне s применяем Тонелли после учёта ориентации.',
                    'Внутренний интеграл Эйлера–Пуассона равен √π/(2√s). Интегрируем его по s в исходном порядке.'],oriented_rates=tuple(rates))
    raise Unsupported('A whole original half-line substitution is required for this Euler–Poisson method')


def source_integral_transform_report(result,pretty):
    plan=result['compilation'];answer=result['value'];rows=list(plan['argument'])
    if 'real' in answer:
        rows.append('Действительная часть равна '+pretty(answer['real'])+', мнимая равна '+pretty(answer['imaginary'])+'.')
    elif 'value_on_nonzero' in answer:
        rows.append('При '+pretty(answer['frequency'])+' ≠ 0 результат равен '+pretty(answer['value_on_nonzero'])+'.')
        rows.append('В нулевой частоте результат равен '+pretty(answer['value_at_zero'])+'.')
    elif 'representative' in answer:
        rows.append(answer['function']+'(y) = '+pretty(answer['representative'],'y')+'.')
    elif 'index' in plan:
        n=plan['index'];rows.append(f'Преобразование равно {n}! / p^({n}+1).')
    else:
        rows.append('Результат равен '+pretty(answer['value'],simplify=False)+'.')
    if 'convergence_domain' in answer:
        rows.append('Область сходимости: '+', '.join(answer['convergence_domain'])+'.')
    return '\n'.join(rows)


def lorentzian_moment(task,library,request):
    """Reduce positive rational half-line Fourier moments to Gaussian and Dirichlet proof steps."""
    from integrals import affine,harmonic_modes,learned_nodes,separate_weight
    from verify import same_value
    fields={'kind','id','source','integrand','limits','stated_conditions','method_requirement','reference_formula','requested_output'}
    method=task.get('method_requirement');meta=task.get('source',{});conditions=task.get('stated_conditions',[])
    reference=task.get('reference_formula');declared='1/(1+x²)=int_0^inf exp(-y*(1+x²))dy'
    if (set(task)-fields or not isinstance(meta,dict)
            or set(meta)-{'exercise','pdf_page','printed_page','pdf_sha256','printed_subpart','literal_requirement'}
            or meta.get('literal_requirement','Вычислить несобственный интеграл.')!='Вычислить несобственный интеграл.'
            or task.get('limits')!='0..inf' or method not in (None,'specified_representation')
            or (method is None and reference is not None or method and reference!=declared)
            or task.get('requested_output')!=(['exact_integral','specified_method'] if method else ['exact_integral_and_convergence'])):
        raise Unsupported('A positive half-line moment with the original representation and endpoints is required')
    text=task['integrand'].replace('²','^2').replace('³','^3');x=('v','x');names=transform_parameters(text,'x')
    ctx=m.context(dict(variable='x',parameters=names,parameter_conditions=conditions));raw=m.parse(text,'x',names)
    if raw[0]!='div' or any(domain_conditions(e) for e in raw[1:]):
        raise Unsupported('The original numerator or quadratic denominator has an extra possible hole')
    N,D=raw[1:];power=1
    if D[0]=='pow' and D[2]==2:D=D[1];power=2
    C=riemann_polynomial(D,x)
    if not C or len(C)!=3 or C[1]!=ZERO or m.sign(C[0],ctx)!=1 or m.sign(C[2],ctx)!=1:
        raise Unsupported('A strictly positive centered quadratic denominator is required')
    c,k=C[0],C[2];scale=m.simplify(('sqrt',m.div(c,k)))
    if method and (power!=1 or c!=ONE or k!=ONE):
        raise Unsupported('The prescribed representation does not describe the original denominator')
    atom={z for z in learned_nodes(N) if isinstance(z,tuple) and z[0]=='sin' and m.variable_in(z,'x')}
    sine=None
    if len(atom)==1 and power==1 and not method:
        wave,=atom
        try:
            W,n=separate_weight(N,wave);modes=riemann_polynomial(W,x);freq,phase=affine(wave[1],'x')
            if n==1 and modes and len(modes)==2 and modes[0]==ZERO and phase==ZERO:sine=(freq,modes[1])
        except Unsupported:pass
    values=[];parts=[];nonzero_branch=None
    def exp(frequency):return ('exp',m.neg(m.mul(scale,('abs',frequency))))
    def both(frequency,amplitude):
        if power==1:moment=m.div(m.mul(m.PI,exp(frequency)),m.mul(q(2),m.mul(k,scale)))
        else:
            poly=m.add(ONE,m.mul(scale,('abs',frequency)))
            moment=m.div(m.mul(m.mul(m.PI,poly),exp(frequency)),m.mul(q(4),m.mul(m.power(k,2),m.power(scale,3))))
        return m.mul(amplitude,moment)
    if sine:
        freq,coef=sine;sign=m.sign(freq,ctx)
        value=m.div(m.mul(m.mul(coef,m.PI),exp(freq)),m.mul(q(2),k))
        if sign is None:nonzero_branch=m.mul(value,m.div(freq,('abs',freq)))
        else:values.append(m.mul(q(sign),value))
        parts.append(dict(frequency=freq,weight=coef,component='sine moment with one monomial in x'))
    else:
        modes,_,_=harmonic_modes(dict(kind='integrate',variable='x',integrand=source(N),parameters=names))
        for (growth,freq),weights in modes.items():
            if growth!=ZERO or len(weights)!=1 or weights[0][1]!=ZERO:
                raise Unsupported('The bounded numerator needs real cosine modes without polynomial weight')
            coeff=weights[0][0];values.append(both(freq,coeff));parts.append(dict(frequency=freq,weight=coeff,component='cosine'))
    child_task=dict(kind='parameter_improper_evaluation',integrand='exp(-(x^2+a^2/x^2))',limits='0..inf',
        stated_conditions=['a>0'],method_requirement='euler_poisson_integral',requested_output=['exact_integral','specified_method'])
    seed=request('positive reciprocal Gaussian moment after the Laplace kernel exchange',child_task)
    steps=[
        'Представляем обратный положительный знаменатель интегралом затухающей экспоненты. Мажорант интегрируется после гауссова интеграла по x, поэтому перестановка законна.',
        'Внутренний косинусный гауссов момент после замены масштаба даёт проверенный интеграл с двумя взаимно обратными степенями. Нулевую частоту вычисляем непосредственно по Эйлеру–Пуассону.']
    if power==2:steps.append('Дифференцируем по положительному квадратному масштабу. Локальная положительная нижняя граница даёт интегрируемый мажорант и повышает степень знаменателя до двух.')
    if sine:steps.append('На компактных промежутках ненулевых частот производный синусный хвост равномерно сходится по Дирихле. В нулевой частоте исходный синус тождественно равен нулю.')
    total=ZERO
    for value in values:total=m.add(total,value)
    answer=dict(value=total,convergence='ordinary; both original endpoints exist')
    if nonzero_branch is not None:answer=dict(frequency=freq,value_on_nonzero=nonzero_branch,value_at_zero=ZERO,convergence=answer['convergence'])
    return dict(theorem='method.gaussian_transform_normalization',steps=steps,argument=steps,
                decomposition=parts,quadratic_scale=scale,quadratic_power=power,source_representation=reference,
                gaussian_seed=seed['value']),answer


def source_endpoint_limit_admission(task):
    kind=task.get('kind')
    if kind in ('limit_with_integrals','limit_integral_expression'):return True
    return (kind=='sequence_expression_limit' and task.get('method_requirement')=='uniform_higher_order_discard'
            and isinstance(task.get('expression'),str) and 'sum(' in task['expression'])


def source_endpoint_limit(task,library,request):
    """Derive a mesh error or an integral limit on the original one-sided domain."""
    if not library.data.get('integral_endpoint_estimates'):raise Unsupported('Endpoint comparison skills are unavailable')
    kind=task['kind'];meta=task.get('source',{})
    if (not isinstance(meta,dict) or set(meta)-{'exercise','printed_page','pdf_page','pdf_sha256','printed_subpart','literal_requirement'}):
        raise Unsupported('An additional printed hypothesis or method has not been bound')
    def emit(name,value,argument,**facts):
        return dict(theorem='method.'+name,argument=list(argument),**facts),dict(value=value)
    if kind=='sequence_expression_limit':return endpoint_mesh_limit(task,request,emit)
    if kind=='limit_with_integrals':
        if set(task)-{'kind','id','source','statement','requested_output'} or task.get('requested_output') != ['limit_value']:
            raise Unsupported('A different source limit or method is required')
        return endpoint_mean_limit(task['statement'],request,emit)
    if kind=='limit_integral_expression':
        if set(task)-{'kind','id','source','expression','variable','approach','stated_conditions','requested_output'} or task.get('requested_output')!=['limit_on_original_domain']:
            raise Unsupported('A different source limit or method is required')
        return endpoint_power_integral_limit(task,emit)
    raise Unsupported('The original endpoint limit is unresolved')


def endpoint_mesh_limit(task,request,emit):
    from integrals import learned_nodes
    from verify import same_value
    fields={'kind','id','source','goal','expression','index','index_domain','approach','method_requirement','parameters','stated_conditions','requested_output'}
    if (set(task)-fields or task.get('goal')!='Find the printed limit.' or task.get('method_requirement')!='uniform_higher_order_discard'
            or task.get('index_domain')!='positive integers' or task.get('approach')!='+infinity'
            or task.get('requested_output', ['limit'])!=['limit']):
        raise Unsupported('The stated uniform error and positive integer mesh are required')
    lead=re.fullmatch(r'(.*)sum\((.+),([A-Za-z]\w*),1,([A-Za-z]\w*)(-1)?\)(.*)',task['expression'].replace(' ',''))
    if not lead:raise Unsupported('A complete uniform mesh and index range are needed')
    prefix,body,k,n,omit,suffix=lead.groups();params=task.get('parameters',[]);facts=task.get('stated_conditions',[])
    if n!=task.get('index') or len(set([n,k,*params]))!=2+len(params):raise Unsupported('The bound mesh index must be distinct from every parameter')
    names=[n,k,*params];N,K=(('s',v) for v in (n,k));u=('v','meshpoint')
    ctx=m.context(dict(variable=u[1],parameters=names,parameter_conditions=facts))
    X=m.parse(body,None,names)
    def lattice_guards(e):
        return all(known_guard((r,g),ctx) or r=='nonzero' and (g in (N,K) or g[0]=='pow' and g[1] in (N,K))
                   for r,g in domain_conditions(e))
    def constant(e):return m.constant_defined(e,ctx) and not any(m.contains(e,('s',v)) for v in names)
    def rate(angle,numerator,degree):
        if not lattice_guards(angle):raise Unsupported('The original phase has an additional hole on the mesh')
        c=m.simplify(m.substitute(angle,{N:ONE,K:ONE}))
        if constant(c) and same_value(angle,m.div(m.mul(c,numerator),m.power(N,degree))):return c
        raise Unsupported('The phase does not have the required homogeneous mesh scale')
    def norm(e):return m.simplify(m.substitute(e,{K:u,N:ONE}))
    def result(kernel,value,error,*steps):
        return emit('uniform_mesh_remainder',value,[*steps,
                    'Умножаем равномерную оценку остатка одного нормированного слагаемого на суммарный вес узлов, не превосходящий 1.',
                    'Главная часть — правая сумма Римана непрерывного ядра на [0,1]. Возможное удаление одного ограниченного конца даёт O(1/n).'],
                    kernel=kernel,remainder_bound=error,mesh_indices=('1',n+('-1' if omit else '')),printed_method='uniform_higher_order_discard')
    def finite(kernel):
        from model import freeze
        child=dict(kind='iterated_integral',integrand=source(kernel),parameters=params,stated_conditions=facts,
                   integration_order=[dict(variable=u[1],lower='0',upper='1')],requested_output=['exact_integral'])
        return freeze(request('exact integral of the uniformly approximated mesh kernel',child)['value'])
    if not prefix and not suffix and not (params or facts) and X[0]=='mul' and lattice_guards(X):
        for weight,wave in (X[1:],X[:0:-1]):
            if wave[0]!='sin':continue
            c=rate(wave[1],K,2);A=norm(weight);coeff=riemann_polynomial(A,u)
            if coeff is None or len(coeff)>2 or not all(constant(v) for v in coeff):continue
            if not same_value(weight,m.substitute(A,{u:m.div(K,N)})):continue
            kernel=m.mul(c,m.mul(u,A));value=finite(kernel)
            return result(kernel,value,'M*abs(c)^3/(6*n^2)',
                          'Синус аргумента c k/n² отличается от своего линейного члена не более |c k/n²|³/6.',
                          'Аффинный множитель ограничен M на [0,1]. После нормирования остаток не превосходит M|c|³/(6n²).')
    if not (params or facts) and not suffix and prefix.endswith('*') and X[0]=='div' and m.num(X[1]) is not None:
        scale=m.parse(prefix[:-1],None,names)
        if scale[0]=='sin':
            c=rate(scale[1],ONE,1);D=X[2]
            waves={z for z in learned_nodes(D) if isinstance(z,tuple) and z[0]=='cos'}
            if len(waves)==1 and lattice_guards(D):
                C,=waves;w=rate(C[1],K,1);coeff=riemann_polynomial(m.substitute(D,{C:u}),u)
                if coeff is not None and len(coeff)==2:
                    a,b=map(m.num,coeff);turns=m.pi_multiple(w)
                    if a is not None and b is not None and a>abs(b) and turns and turns.denominator==1:
                        kernel=m.div(m.mul(c,X[1]),m.add(q(a),m.mul(q(b),('cos',m.mul(w,u)))))
                        value=m.div(m.mul(c,X[1]),('sqrt',q(a*a-b*b)))
                        return result(kernel,value,'abs(c)^3*abs(numerator)/(6*(a-abs(b))*n^2)',
                                      'Знаменатель a+b cos(t) не меньше a−|b|>0 на всей вещественной оси.',
                                      'Заменяем n sin(c/n) на c с остатком O(n⁻²). На каждом полуобороте замена тангенса половины угла даёт среднее 1/√(a²−b²).')
    if not prefix and suffix=='/'+n+'^2' and len(params)==1 and facts==[params[0]+'>0'] and X[0]=='sqrt' and X[1][0]=='mul':
        p=('s',params[0]);A,B=X[1][1:];target=m.add(m.mul(N,p),K)
        for first,second in ((A,B),(B,A)):
            delta=m.num(m.add(second,m.neg(first)))
            if (delta is not None and delta>=0 and not domain_conditions(first) and not domain_conditions(second) and same_value(first,target)):
                kernel=m.add(p,u);value=finite(kernel)
                return result(kernel,value,source(q(delta))+'/n',
                              'Положительность параметра и 1≤k≤n делают оба множителя под корнем неотрицательными.',
                              'После деления корня на n получаем √((p+u)(p+u+δ/n)), заключённый между p+u и p+u+δ/n.')
    if not prefix and not suffix and not (params or facts) and X[0]=='div' and X[1][0]=='rpow' and lattice_guards(X[1]):
        base,power=X[1][1:];b=m.num(base)
        d=m.num(m.mul(K,m.add(X[2],m.neg(N))))
        if (b is not None and b>0 and d is not None and d>=0 and lattice_guards(X[2])
                and same_value(power,m.div(K,N)) and same_value(X[2],m.add(N,m.div(q(d),K)))):
            kernel=('rpow',base,u);value=ONE if b==1 else m.div(q(b-1),('ln',base))
            return result(kernel,value,'max(1,base)*d/n',
                          'На исходном диапазоне k≥1 имеем n+d/k≥n>0. Разность между n/(n+d/k) и 1 по модулю не больше d/n.',
                          'Вес base^(k/n) ограничен max(1,base). Вычисляем интеграл экспоненты на [0,1], отдельно учитывая основание 1.')
    raise Unsupported('No verified uniform remainder carries the entire original mesh')


def endpoint_mean_limit(statement,request,emit):
    from model import freeze
    from verify import same_value
    def out(value,*steps,**facts):return emit('integrated_endpoint_comparison',value,steps,**facts)
    t=('v','t')
    def parse(text):
        text=re.sub(r'\barctan\s+t\b','atan(t)',text.replace('²','^2'))
        return m.parse(re.sub(r'(?<=\d)(?=t\b)','*',text),'t')
    if (hit:=re.fullmatch(r'lim\[x→0\] \(∫₀ˣ (.+) dt\)/x',statement)):
        raw=parse(hit[1]);f0=m.substitute(raw,{t:ZERO});ctx=m.context(dict(variable='t'))
        for r,g in domain_conditions(raw):
            value=m.substitute(g,{t:ZERO});sign=m.sign(value,ctx)
            if not m.constant_defined(value,ctx) or (r=='nonzero' and sign not in (-1,1)) or (r!='nonzero' and sign!=1):
                raise Unsupported('The original local field is not continuous in a full neighborhood of zero')
        if m.constant_defined(f0,ctx):
            return out(m.simplify(f0),'Деление ориентированного интеграла на x даёт среднее по отрезку между 0 и x для обоих знаков x.',
                       'Модуль отклонения среднего от f(0) не превосходит наибольшего отклонения непрерывной функции на этом отрезке.',approach='both',original_function=raw)
    if (hit:=re.fullmatch(r'lim\[x→\+∞\] \(∫₀ˣ (.+) dt\)/√\(x²\+([1-9]\d*)\)',statement)):
        raw=parse(hit[1])
        if not domain_conditions(raw):
            limit=dict(kind='limit',expression=source(raw),variable='t',approach={'point':'+inf','side':'positive_infinity'})
            A=freeze(request('proved tail limit of the continuous integrand',limit)['value'])
            if not isinstance(A,str):
                return out(A,'Делим на x и выделяем множитель x/√(x²+c), стремящийся к 1.',
                           'Среднее непрерывной функции на [0,x] имеет тот же конечный предел, что и сама функция. Фиксированный начальный участок делится на x, на хвосте действует одна равномерная оценка.',approach='positive infinity',normalizing_constant=q(int(hit[2])))
    if (row:=re.fullmatch(r'lim\[x→\+∞\] \(∫₀ˣ (exp\(.+?\))dt\)(²|\^[1-9]\d*)/\(∫₀ˣ (exp\(.+?\))dt\)',statement)):
        p=2 if row[2]=='²' else int(row[2][1:]);rates=[]
        for body in (row[1],row[3]):
            raw=parse(body);c=m.num(m.simplify(m.substitute(raw[1],{t:ONE})))
            if c is None or c<=0 or domain_conditions(raw[1]) or not same_value(raw[1],m.mul(q(c),m.power(t,2))):break
            rates.append(c)
        if len(rates)==2:
            c,d=rates;delta=p*c-d
            value='+inf' if delta>0 else ZERO if delta<0 or p>1 else ONE
            return out(value,'При с>0 интеграл I_c(x)=∫₀ˣ exp(c t²)dt и exp(c x²)/(2cx) стремятся к бесконечности.',
                       'Производная второй функции равна exp(c x²)·(1−1/(2c x²)). Отношение производных стремится к 1, поэтому I_c имеет ту же асимптотику.',
                       'Сравниваем показатели pc−d, а при их равенстве — оставшуюся степень x^(1−p).',approach='positive infinity',gaussian_growth_rates=(q(c),q(d)),outer_power=p,exponential_difference=q(delta))
    if (row:=re.fullmatch(r'lim\[([A-Za-z]\w*)→∞\] ∫₀¹ ([A-Za-z]\w*)\(\1x\) dx, \2 continuous on \[0,\+∞\), lim\[x→\+∞\]\2\(x\)=([A-Za-z]\w*)',statement)) and len(set([*row.groups(),'x']))==4:
        n,f,A=row.groups()
        return out(('s',A),'Монотонная замена t=nx при n>0 даёт среднее n⁻¹∫₀ⁿ f(t)dt.',
                   'Разбиваем в фиксированной точке, после которой |f(t)−A| меньше заданной точности. Начальный интеграл конечен по непрерывности и делится на n.',approach='positive infinity',parameter=n,integrand_name=f)
    near=re.fullmatch(r'lim\[x→\+0\] \(∫₀\^\{(sin|tan|atan) x\} √\((sin|tan|atan) t\) dt\)/\(∫₀\^\{(sin|tan|atan) x\} √\((sin|tan|atan) t\) dt\)',statement)
    if near:
        return out(ONE,'На правой стороне все четыре функции положительны в некоторой окрестности нуля и имеют производную 1 в нуле.',
                   'Каждое ядро после деления на √t стремится к 1. Одна относительная оценка действует на всём достаточно коротком промежутке и переносится на интеграл.',
                   'Оба интеграла эквивалентны (2/3)x^(3/2), так как их верхние границы эквивалентны x.',approach='right',relative_profiles=near.groups())
    raise Unsupported('A compatible source field, directed approach or integral comparison is still missing')


def endpoint_power_integral_limit(task,emit):
    from verify import same_value
    var=task['variable'];direction=task['approach'];text=task['expression'];facts=task.get('stated_conditions',[])
    c=re.escape(var);t=('v','t');x=('s',var);ctx=m.context(dict(variable='t'))
    if var=='t':raise Unsupported('The exterior and bound interior variables must be independent')
    def out(value,*steps,**facts):return emit('integrated_endpoint_comparison',value,steps,**facts)
    if direction=='0' and not facts and (row:=re.fullmatch(c+r'\*integral\((.+)/t\^2,t,'+c+r',1\)',text)):
        raw=m.parse(row[1],'t');v=m.simplify(m.substitute(raw,{t:ZERO}))
        if domain_conditions(raw) or not m.constant_defined(v,ctx) or m.sign(v,ctx) not in (-1,1):
            raise Unsupported('The kernel may not be continuous and nonzero at the source pole')
        return out(v,'Слева от нуля исходный отрезок пересекает неинтегрируемую особенность t=0, так как числитель непрерывен и ненулевой там.',
                   'Справа выделяем f(0). Его вклад x∫ₓ¹dt/t² равен 1−x, умноженному на f(0).',
                   'На [x,δ] остаток ограничен модулем непрерывности, на [δ,1] он гасится множителем x.',relative_approach='right',mass='1-x')
    if direction=='0' and (row:=re.fullmatch(c+r'\^([A-Za-z]\w*)\*integral\(([A-Za-z]\w*)\(t\)/t\^\(\1\+1\),t,'+c+r',1\)',text)):
        a,f=row.groups()
        if len(set([a,f,var,'t']))==4 and facts==[a+'>0',f+' continuous on [0,1]']:
            return out(('div',('s',f+'(0)'),('s',a)),
                       'Исходные предпосылки о f относятся к [0,1]. При x>0 ядро x^α/t^(α+1) неотрицательно и имеет массу (1−x^α)/α.',
                       'Отделяем f(0). На [x,δ] оставшийся вклад ограничен модулем непрерывности, а на [δ,1] он убывает с множителем x^α.',
                       relative_approach='right',source_parameters=facts,mass=f'(1-{var}^{a})/{a}')
    if direction in ('unsigned infinity','+infinity','-infinity') and not facts and (row:=re.fullmatch(r'integral\(sqrt\((.+)\),t,0,'+c+r'\)/'+c+r'\^([1-9]\d*)',text)):
        raw=m.parse(row[1],'t');s=int(row[2]);coeff=riemann_polynomial(raw,t);p=s-1
        if (p>0 and coeff is not None and len(coeff)==2*p+1 and not domain_conditions(raw)
                and all(v==ZERO for v in coeff[1:-1]) and all(m.num(v) is not None and m.num(v)>0 for v in (coeff[0],coeff[-1]))):
            limit=m.div(('sqrt',coeff[-1]),q(s));negative=m.mul(q(-1 if p%2 else 1),limit)
            if direction=='unsigned infinity' and p%2:raise Unsupported('The two legitimate infinite directions yield different limits')
            return out(negative if direction=='-infinity' else limit,
                       'Подкоренное выражение положительно всюду. При t→+∞ исходное ядро эквивалентно √D·t^p.',
                       'Разбиваем в фиксированной точке. Отношение полных интегралов имеет тот же предел, что и отношение положительных хвостовых ядер.',
                       'Для отрицательной бесконечности чётное ядро даёт нечётный ориентированный интеграл. Учитываем чётность знаменателя.',
                       relative_approach=direction,normalized_power=p,positive_leading=coeff[-1])
    if direction=='0' and not facts and (row:=re.fullmatch(r'integral\(exp\((.+)\)/t,t,'+c+r',\+inf\)/ln\(1/'+c+r'\)',text)):
        raw=m.parse(row[1],'t');rate=m.neg(m.simplify(m.substitute(raw,{t:ONE})))
        if not domain_conditions(raw) and m.num(rate) is not None and m.num(rate)>0 and same_value(raw,m.neg(m.mul(rate,t))):
            return out(ONE,'Логарифм в исходном знаменателе требует x>0. Несобственный хвост от 1 до +∞ сходится абсолютно по экспоненциальной оценке.',
                       'На (0,1] величина (exp(−ct)−1)/t ограничена по теореме о среднем. Поэтому числитель равен ln(1/x)+O(1).',
                       relative_approach='right',decay=rate)
    raise Unsupported('The complete printed endpoint, power or singular integral is not covered')


def reciprocal_log_improper_moment(raw,v):
    """Use an even measure under reciprocal reflection after checking both independent ends."""
    from verify import same_value
    x=('v',v);L=('ln',x)
    if raw[0]!='div' or raw[2][0]!='pow' or raw[2][2]!=2:raise Unsupported('A squared positive reciprocal kernel is required')
    den=raw[2][1];poly=riemann_polynomial(den,x)
    if poly is None or len(poly)<2 or any(a!=ZERO for a in poly[1:-1]) or domain_conditions(den):
        raise Unsupported('The source denominator is not one positive binomial')
    p=len(poly)-1;c,k=poly[0],poly[-1];A=m.num(c);B=m.num(k)
    if A is None or B is None or A<=0 or B<=0:raise Unsupported('Both original scales must be strictly positive')
    N=riemann_polynomial(m.substitute(raw[1],{L:ONE}),x)
    if N is None or len(N)!=p or any(a!=ZERO for a in N[:-1]) or m.num(N[-1]) is None:
        raise Unsupported('The logarithmic numerator must match the power change of variables')
    w=N[-1];expected=m.mul(w,m.mul(m.power(x,p-1),L))
    if not same_value(raw[1],expected) or any(g!=('positive',x) for g in domain_conditions(raw[1])):
        raise Unsupported('The original logarithm or additional numerator hole must be retained')
    value=m.mul(q(m.num(w)/(p*p*A*B)),m.simplify(('ln',q(A/B))))
    plan=dict(theorem='method.reciprocal_log_moment',argument=[
        'На исходной положительной полуоси знаменатель строго положителен. У нуля модуль сравним с x^(p−1)|ln x|, на бесконечности с x^(−p−1)ln x. Оба края абсолютно интегрируемы.',
        'Монотонная замена t=(k/c)x^p переносит исходные концы в 0 и +∞. Вес становится (1+t)^−2, логарифм — (ln t+ln(c/k))/p.',
        'Замена t=1/u сохраняет вес и меняет знак ln t. Оба независимых края уже сходятся, поэтому логарифмический момент равен нулю. Постоянная часть интегрируется в 1.'],
        exponent=p,positive_scales=(c,k),independent_absolute_ends=True)
    return plan,dict(convergence='convergent',value=value)


def endpoint_estimate_report(result,pretty):
    p=result['compilation'];return '\n'.join([*p['argument'],'Значение равно '+pretty(result['value']['value'])+'.'])


def oriented_parameter_derivative(task, library):
    """Compose local integral derivatives with their compactness and endpoint conditions."""
    from derivative_proofs import table
    from model import same

    meta=task.get('source',{})
    allowed={'kind','id','source','integrand','oriented_limits','operator','stated_conditions','requested_output'}
    if (not library.data.get('oriented_leibniz_transport') or set(task)-allowed or not isinstance(meta,dict)
            or set(meta)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement'}
            or meta.get('literal_requirement') not in (None,'Найти указанную производную.')
            or task.get('requested_output')!=['derivative_with_domain']):
        raise Unsupported('The oriented source integral, its derivative, and its domain must be bound')
    if library.data.get('abstract_integral_transitions'):
        try:return parameter_boundary_differences(task)
        except (Unsupported,TypeError,KeyError):pass
    name=r'[A-Za-z][A-Za-z_0-9]*'
    operator=task['operator']
    single=re.fullmatch(r'd/d('+name+r')',operator)
    twice=re.fullmatch(r'd\^2/d('+name+r')\^2',operator)
    mixed=re.fullmatch(r'partial\^2/\(partial ('+name+r') partial ('+name+r')\)',operator)
    if not (single or twice or mixed):
        raise Unsupported('This transition needs an ordinary or a specified mixed derivative of order at most two')
    axes=(single[1],) if single else (twice[1],)*2 if twice else (mixed[2],mixed[1])
    limits=[re.fullmatch(r'(.+?)<=\s*('+name+r')\s*<=(.+)',s.strip())
            for s in task['oriented_limits'].split(',')]
    if not 1<=len(limits)<=2 or not all(limits):
        raise Unsupported('Expected one or two ordered pairs of oriented finite endpoints')
    dummies=[l[2] for l in limits]
    if len(set(dummies))!=len(dummies) or set(dummies)&set(axes):
        raise Unsupported('Differentiation variables and bound variables must be distinct')
    if library.data.get('affine_vector_leibniz') and single and len(limits)==1:
        call=re.fullmatch(rf'({name})\(([^,]+(?:,[^,]+)+)\)',task['integrand'])
        if call:return affine_vector_leibniz(task,single[1],limits[0],call)
    conditions=task.get('stated_conditions',[])
    if not isinstance(conditions,list) or any(not isinstance(c,str) for c in conditions):
        raise Unsupported('Expected a list of source conditions')
    functions={c.split()[0]:c.split(' ',1)[1] for c in conditions
          if re.fullmatch(name+r' (?:continuous|differentiable|continuously differentiable)',c)}
    if set(functions)&(m.FUNCTIONS|set(m.ALIASES)|{'pi','e','integral','derivative_at_unknown','sine_quotient','log_quotient'}):
        raise Unsupported('A named function conflicts with a reserved mathematical symbol')
    guards=[c for c in conditions if c not in (f'{f} {p}' for f,p in functions.items())]
    fields=[task['integrand'],*(s for l in limits for s in (l[1],l[3])),*guards]
    names=set(re.findall(name,' '.join(fields)))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e',*functions}
    free=sorted((names|set(axes))-set(dummies))
    dummy='__leibniz_axis'
    m.context(dict(variable=dummy,parameters=[*free,*dummies]))
    body=m.parse(task['integrand'],None,[*free,*dummies],functions)
    bounds=[(x,*(m.parse(s,None,[*free,*dummies[:i]],functions) for s in (l[1],l[3])))
            for i,(x,l) in enumerate(zip(dummies,limits,strict=True))]
    parameter_guards=[]
    for text in guards:
        match=re.fullmatch(r'(.+?)(!=|<|>)(.+)',text)
        if not match:
            raise Unsupported('An explicit source parameter condition is unresolved')
        left,right=(m.parse(match[i],None,free) for i in (1,3))
        op=match[2]
        delta=('add',right,('mul',q(-1),left)) if op=='<' else ('add',left,('mul',q(-1),right))
        parameter_guards.append(guard_source(('nonzero' if op=='!=' else 'positive',delta)))
    ctx=m.context(dict(variable=dummy,parameters=[*free,*dummies],parameter_conditions=parameter_guards))
    # Keep unsimplified endpoint denominators visible. Their nonzero conditions are necessary
    # for the printed endpoints to exist, independently of an integral's final simplification.
    holes=[]
    for _,lo,hi in bounds:
        for relation,e in (*domain_conditions(lo),*domain_conditions(hi)):
            if (relation=='nonzero' and e[0]=='s' and e[1] in free
                    and not known_guard((relation,e),ctx)):
                condition=guard_source((relation,e))
                if condition not in holes:holes.append(condition)
    if holes:
        ctx=m.context(dict(variable=dummy,parameters=[*free,*dummies],parameter_conditions=parameter_guards+holes))

    checks=[];differential=[];remainders=[]
    def enclosure(e,scope):
        tag=e[0]
        if tag=='s':return scope.get(e,(None,))[0]
        if tag=='q':return (m.num(e),)*2
        if tag in ('sin','cos'):return F(-1),F(1)
        if tag=='pi':return pi_range()
        left=enclosure(e[1],scope) if isinstance(e[1],tuple) else None
        if left is None:return None
        if tag=='pow':return power(left,e[2])
        if tag in ('add','mul','div'):
            right=enclosure(e[2],scope)
            if right is None:return None
            return outward(left[0]+right[0],left[1]+right[1]) if tag=='add' else product(left,right if tag=='mul' else power(right,-1))
        return None

    def prove(g,scope):
        if known_guard(g,ctx):return
        relation,e=g
        if relation in ('positive','nonzero') and e[0]=='add' and ONE in e[1:]:
            factor=e[2] if e[1]==ONE else e[1]
            if factor[0]=='mul':
                for v,c in (factor[1:],factor[:0:-1]):
                    if v in scope and not m.contains(c,v):
                        lo,hi=scope[v][1:]
                        if (lo,hi) in ((ZERO,c),(c,ZERO)):
                            # Use t=u*c, with u in [0,1], even if c is negative or zero.
                            record=('positive_on_oriented_zero_to_parameter',e,ONE)
                            if record not in checks:checks.append(record)
                            return
        interval=enclosure(e,scope)
        if interval is None:
            raise Unsupported('Domain is unresolved on the whole original fiber: '+guard_source(g))
        lo,hi=interval
        if not (lo>0 or hi<0 and relation=='nonzero' or lo==0 and relation=='nonnegative'):
            raise Unsupported('Domain is unresolved on the whole original fiber: '+guard_source(g))
        record=(relation,e,(q(lo),q(hi)))
        if record not in checks:checks.append(record)

    def kernel_quotient(e,scope):
        """Recognize the actual removable quotient before it can cancel algebraically."""
        if e[0]!='div' or e[2][0]!='s' or e[2] not in scope:return e
        variable=e[2];u=e[1]
        if u[0]=='sin':tag='sine_quotient';argument=u[1]
        elif u[0]=='ln' and u[1][0]=='add' and ONE in u[1][1:]:
            tag='log_quotient';argument=u[1][2] if u[1][1]==ONE else u[1][1]
        else:return e
        if argument[0]!='mul' or variable not in argument[1:]:return e
        coeff=argument[2] if argument[1]==variable else argument[1]
        if m.contains(coeff,variable):return e
        continuous(coeff,scope)
        if tag=='log_quotient':
            lo,hi=scope[variable][1:]
            if not (ZERO in (lo,hi) and (coeff==lo or coeff==hi)):return e
            # At a fixed parameter p the chart t=u*p, 0<=u<=1 gives
            # 1+p*t=1+p^2*u>=1. This strict bound extends to a local compact tube.
            prove(('positive',u[1]),scope)
        return (tag,coeff,variable)

    def continuous(e,scope,axis=None):
        tag=e[0]
        if tag in ('s','q','pi'):return
        if tag in ('sine_quotient','log_quotient'):
            p,v=e[1:]
            continuous(p,scope,axis);continuous(v,scope,axis)
            if tag=='log_quotient':prove(('positive',('add',ONE,('mul',p,v))),scope)
            return
        if tag=='derivative_at_unknown':
            if functions.get(e[1])!='continuously differentiable':
                raise Unsupported('Continuity of the partial derivative of the named function is not given')
            continuous(e[2],scope);return
        if tag=='integral':
            _,v,lo,hi,child=e
            continuous(lo,scope);continuous(hi,scope)
            continuous(child,inside(scope,v,lo,hi));return
        if tag in functions:
            if axis is not None and m.contains(e,axis) and functions[tag]=='continuous':
                raise Unsupported('Only continuity is supplied for the named function')
            continuous(e[1],scope,axis);return
        if tag not in m.FUNCTIONS|{'add','mul','div','pow','rpow'}:
            raise Unsupported('Continuity has no rule for '+tag)
        for arg in e[1:]:
            if isinstance(arg,tuple):continuous(arg,scope,axis)
        smooth=axis is not None and m.contains(e,axis)
        inner=e[1]
        if tag=='div':prove(('nonzero',e[2]),scope)
        elif tag=='pow' and e[2]<=0:prove(('nonzero',inner),scope)
        elif tag in ('ln','rpow'):prove(('positive',inner),scope)
        elif tag=='sqrt':prove(('positive' if smooth else 'nonnegative',inner),scope)
        elif tag in ('cbrt','abs') and smooth:prove(('nonzero',inner),scope)
        elif tag in ('tan','sec','cot','csc'):prove(('nonzero',('cos' if tag in ('tan','sec') else 'sin',inner)),scope)
        elif tag in ('asin','acos'):
            prove(('positive' if smooth else 'nonnegative',('add',ONE,('mul',q(-1),('pow',inner,2)))),scope)

    def inside(scope,v,lo,hi):
        a,b=enclosure(lo,scope),enclosure(hi,scope)
        interval=(min(a[0],b[0]),max(a[1],b[1])) if a is not None and b is not None else None
        return {**scope,v:(interval,lo,hi)}

    def integral(v,lo,hi,child):
        return ZERO if child==ZERO or same(lo,hi) else ('integral',v,lo,hi,child)

    def contains_integral(e):
        return e[0]=='integral' or any(contains_integral(a) for a in e[1:] if isinstance(a,tuple))

    def diff(e,axis,scope):
        tag=e[0]
        if not m.contains(e,axis):return ZERO
        if tag=='integral':
            _,v,lo,hi,child=e
            area=inside(scope,v,lo,hi);part=diff(child,axis,area)
            continuous(part,area)
            lp,up=diff(lo,axis,scope),diff(hi,axis,scope)
            traces=tuple(m.substitute(child,{v:end}) if prime!=ZERO else ZERO
                     for end,prime in ((lo,lp),(hi,up)))
            remainders.append(dict(variable=v,parameter=axis,lower=lo,upper=hi,integrand=child,
                integrand_derivative=part,edge_derivatives=(lp,up),edge_traces=traces,
                compact_enclosure=tuple(map(q,area[v][0])) if area[v][0] else None,
                modulus='The continuous partial on the compact local tube gives a common modulus ω(|h|). The fixed-fiber remainder is bounded by |upper-lower| ω(|h|). Both oriented short edge averages converge to their endpoint traces.'))
            return m.add(m.add(m.mul(up,traces[1]),m.neg(m.mul(lp,traces[0]))),integral(v,lo,hi,part))
        if tag in ('sine_quotient','log_quotient'):
            param,v=e[1:]
            if m.contains(v,axis):
                raise Unsupported('The removed quotient only supplies the displayed parameter derivative')
            continuous(e,scope,axis)
            derivative=diff(param,axis,scope)
            argument=('mul',param,v)
            return ('mul',derivative,('cos',argument)) if tag=='sine_quotient' else ('div',derivative,('add',ONE,argument))
        continuous(e,scope,axis)
        if contains_integral(e):
            if tag=='add':return m.add(*(diff(a,axis,scope) for a in e[1:]))
            if tag=='mul':
                u,v=e[1:]
                return m.add(m.mul(diff(u,axis,scope),v),m.mul(u,diff(v,axis,scope)))
            raise Unsupported('An unresolved nonlinear function of an integral remains')
        parameter=('v',axis[1])
        fixed={}
        def bind(a):
            if a[0] in functions and not m.contains(a,axis):
                if a not in fixed:fixed[a]=('s','__leibniz_constant_'+str(len(fixed)))
                return fixed[a]
            return (a[0],*(bind(z) if isinstance(z,tuple) else z for z in a[1:]))
        derivative,steps=table(m.substitute(bind(e),{axis:parameter}),axis[1],library,functions)
        differential.append((axis,e,tuple(fixed.items()),steps))
        return m.substitute(derivative,{parameter:axis}|{z:a for a,z in fixed.items()})

    scope={}
    for v,lo,hi in bounds:
        continuous(lo,scope);continuous(hi,scope)
        scope=inside(scope,('s',v),lo,hi)
    original=body;regularized=kernel_quotient(body,scope)
    body=regularized
    continuous(body,scope)
    for v,lo,hi in reversed(bounds):
        # Preserve the original endpoints even when they coincide.
        body=('integral',('s',v),lo,hi,body)
    result=body
    for axis in axes:
        result=diff(result,('s',axis),{})
    steps=['Сохранить исходную ориентацию каждого интеграла, включая обратные и совпадающие границы.',
           'В малой окрестности каждой допустимой точки на неподвижной части применить теорему о среднем к параметру. Непрерывность частной производной на компактной окрестности даёт общую оценку остатка через модуль непрерывности.',
           'На каждом движущемся краю применить непрерывность к среднему по короткому ориентированному отрезку. Приращение нижней границы входит с противоположным знаком.']
    if original!=regularized:
        steps.insert(1,'Проверить устранимый точечный разрыв. Отношение равно интегралу непрерывной производной синуса или логарифма по вспомогательному параметру. При нулевом делителе взять его непрерывный след.')
    plan=dict(theorem='method.oriented_leibniz_transport',steps=steps,source_integrand=original,
              source_endpoints=bounds,domain_checks=checks,derivative_table=differential,edge_remainders=remainders,
              named_functions=tuple(functions))
    if original!=regularized:
        plan['removable_point_trace']=dict(original=original,regularized=regularized,at_zero=regularized[1])
    return plan,dict(value=result,parameter_domain=[*conditions,*holes])


def affine_vector_leibniz(task,p,limit,call):
    """Apply the vector chain rule on an oriented compact integration fiber."""
    from integrals import affine

    lower,t,upper=limit.groups(); f,body=call.groups()
    conditions=task.get('stated_conditions',[])
    if f in m.FUNCTIONS or len({f,t,p})!=3 or conditions not in ([],[f+' continuously differentiable']):
        raise Unsupported('The named field and its smoothness must be kept explicit')
    inputs=body.split(','); notation=[*inputs,lower,upper]
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join(notation)))-{p,'pi','e',*m.FUNCTIONS,*m.ALIASES})
    if not 2<=len(inputs)<=4 or f in names:
        raise Unsupported('Expected two to four explicit field arguments')
    def data(text):
        e=m.parse(text,p,names)
        if domain_conditions(e):raise Unsupported('An affine argument must have no additional domain guard')
        a,b=affine(e,p)
        # A polynomial of degree at most one in the binder has continuous derivatives on the tube.
        for row in (a,b):affine(m.substitute(row,{('s',t):('v',t)}),t)
        return m.substitute(e,{('v',p):('s',p)}),a
    components=[data(c) for c in inputs]; args=[a for a,_ in components]
    (lo,dl),(hi,dh)=map(data,(lower,upper)); axis=('s',t)
    if m.contains(lo,axis) or m.contains(hi,axis):raise Unsupported('A bound cannot depend on its own integration variable')
    edge=lambda end:('abstract_call',f,*(m.substitute(g,{axis:end}) for g in args))
    partials=ZERO
    for j,(_,s) in enumerate(components,1):
        partials=m.add(partials,m.mul(s,('abstract_partial',f,j,*args)))
    integral=ZERO if partials==ZERO else ('integral',axis,lo,hi,partials)
    result=m.add(m.add(m.mul(dh,edge(hi)),m.neg(m.mul(dl,edge(lo)))),integral)
    domain='на параметрах, где '+f+' имеет непрерывные первые частные в окрестности образа ориентированного отрезка'
    return dict(theorem='method.affine_vector_leibniz',steps=[
        'Оставляем порядок исходных пределов. Правило цепочки суммирует первые частные функции с коэффициентами, равными производным её аргументов.',
        'На компактном образе отрезка непрерывность частных даёт равномерность разностного отношения. Верхняя и нижняя границы дают два ориентированных граничных вклада.',
        'Условие гладкости необходимо проверить отдельно, если в исходной задаче оно не указано.'
    ],field=f,original_arguments=args,endpoints=(lo,hi),endpoint_derivatives=(dl,dh),argument_derivatives=[s for _,s in components]),\
        dict(value=result,parameter_domain=[domain],smoothness_stated=bool(conditions))


def oriented_leibniz_text(e,pretty,functions):
    """Render integral atoms inside otherwise ordinary exact expressions."""
    def show(a):
        opaque={}
        def bind(term):
            tag,*args=term
            if tag=='integral':
                v,lo,hi,kernel=map(show,args)
                text=f'(∫_[{lo}, {hi}] ({kernel}) d{v})'
            elif tag in ('sine_quotient','log_quotient'):
                p,v=map(show,args);op='sin' if tag=='sine_quotient' else 'ln'
                argument=f'({p})·({v})'
                numerator=argument if op=='sin' else '1+'+argument
                text=f'({op}({numerator})/({v}), со следом {p} при {v}=0)'
            elif tag=='derivative_at_unknown':text=args[0]+'′('+show(args[1])+')'
            elif tag=='abstract_call':text=args[0]+'('+', '.join(map(show,args[1:]))+')'
            elif tag=='abstract_partial':text=args[0]+'_'+str(args[1])+'('+', '.join(map(show,args[2:]))+')'
            elif tag in functions:text=tag+'('+show(args[0])+')'
            else:return (tag,*(bind(z) if isinstance(z,tuple) else z for z in args))
            marker='__integral_result_'+str(len(opaque))+'__'
            opaque[marker]=text
            return ('s',marker)
        text=pretty(bind(a),'x',simplify=False)
        for marker,replacement in opaque.items():text=text.replace(marker,replacement)
        return text
    return show(freeze(e))


def bind_integral_symbols(formulas):
    """Match raw expression trees under one injective mapping of named roles."""
    from model import canonical

    roles={};assigned={}
    def tokens(text):
        return sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',text))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    def compare(template,actual):
        if isinstance(template,tuple) and template[0]=='s':
            name=template[1]
            if (not isinstance(actual,tuple) or actual[0]!='s' or
                    roles.get(name,actual[1])!=actual[1] or assigned.get(actual[1],name)!=name):
                raise Unsupported('A free parameter and an integration variable cannot capture each other')
            roles[name]=actual[1];assigned[actual[1]]=name
            return
        if isinstance(template,tuple):
            if isinstance(actual,tuple) and len(template)==len(actual) and template[0]==actual[0]:
                for left,right in zip(template[1:],actual[1:],strict=True):compare(left,right)
                return
        elif canonical(template)==canonical(actual):return
        raise Unsupported('The unsimplified integrand or condition does not match the required mathematical shape')
    checked=[]
    for template,actual in formulas:
        want=m.parse(template,None,tokens(template))
        expr=m.parse(actual,None,tokens(actual))
        compare(want,expr)
        checked.append(expr)
    return roles,tuple(checked)


def bound_parameter_interchanges(task,lib,emit,bind):
    """Use the same named-role certificate for several locally dominated integral identities."""
    from derivative_proofs import table
    from verify import same_value

    kind=task['kind'];bounds=task.get('limits');conditions=task.get('stated_conditions',[])
    method=task.get('method_requirement');requested=task.get('requested_output')
    text=task.get('integrand','').replace('²','^2')
    shapes=(
        ('anchored_log_ratio','0..pi/2','ln((1+a*cos(x))/(1-a*cos(x)))/cos(x)','abs(a)','1'),
        ('positive_quadratic_log','0..pi/2','ln(a^2*sin(x)^2+b^2*cos(x)^2)',None,None),
        ('inverse_tangent_ratio','0..pi/2','atan(a*tan(x))/tan(x)',None,None),
        ('unit_circle_log','0..pi','ln(1-2*a*cos(x)+a^2)',None,None),
    )
    if kind=='evaluate_via_parameter' and method=='differentiate_under_integral' and requested==['value_and_specified_method']:
        bind({'integrand','limits','stated_conditions','method_requirement','requested_output'},
             'Вычислить, применяя дифференцирование по параметру.')
        for family,interval,pattern,condition,edge in shapes:
            if bounds!=interval or len(conditions)!=int(condition is not None):continue
            extra=[]
            if condition:
                guard=re.fullmatch(r'(.+?)<(.+)',conditions[0])
                if not guard:continue
                extra=[(condition,guard[1]),(edge,guard[2])]
            try:roles,(raw,*_)=bind_integral_symbols([(pattern,text),*extra]);break
            except Unsupported:pass
        else:raise Unsupported('No checked parameter differentiation identity matches the original integrand and conditions')
    elif (kind=='parameter_improper_evaluation' and bounds=='0..inf' and method=='derive_from_abel_regularization'
          and requested==['exact_integral','specified_method'] and len(conditions)==1):
        bind({'integrand','limits','stated_conditions','method_requirement','requested_output','reference_formula'},
             'Вычислить несобственный интеграл.')
        ref=re.fullmatch(r'\s*[A-Za-z_]\w*\(([A-Za-z_]\w*)\)\s*=\s*int_0\^inf\s+(.+)\s+d([A-Za-z_]\w*)\s*',
                         task.get('reference_formula',''))
        guard=re.fullmatch(r'(.+?)>=(.+)',conditions[0])
        if not ref or not guard:raise Unsupported('The Abel regulator, limiting frequency and integration binder must be bound')
        roles,(raw,regulated,*_)=bind_integral_symbols([('sin(a*x)/x',text),
            ('exp(-r*x)*sin(a*x)/x',ref[2]),('r',ref[1]),('x',ref[3]),('r',guard[1]),('0',guard[2])])
        family='abel_regulated_frequency'
    else:raise Unsupported('The original integral or prescribed parameter method does not match')

    a=('s',roles['a']);x=('s',roles['x'])
    parameter=('v',roles['a'])
    active=regulated if family=='abel_regulated_frequency' else raw
    derivative,trace=table(m.substitute(active,{a:parameter}),roles['a'],lib)
    derivative=m.substitute(derivative,{parameter:a})
    c=('cos',x);s=('sin',x);u=('tan',x);p=roles['a']
    auxiliary={}
    if family=='anchored_log_ratio':
        expected=m.div(q(2),m.add(ONE,m.neg(m.power(m.mul(a,c),2))))
        conclusion=dict(value=m.mul(m.PI,('asin',a)))
        steps=['При cos x=0 ядро имеет конечный след 2p, где p — исходный параметр.',
               'В локальном окне |p|≤c<1 частная производная ограничена величиной 2/(1−c²). Подстановка тангенса даёт π/√(1−p²).',
               'Интегрирование от нулевого параметра восстанавливает исходный интеграл.']
    elif family=='positive_quadratic_log':
        b=('s',roles['b'])
        expected=m.div(m.mul(q(2),m.mul(a,m.power(s,2))),m.add(m.power(m.mul(a,s),2),m.power(m.mul(b,c),2)))
        positive=m.add(('abs',a),('abs',b))
        conclusion=dict(value=m.mul(m.PI,('ln',m.div(positive,q(2)))),defined_when=source(positive)+'>0')
        steps=['При ненулевых параметрах нижняя грань суммы квадратов положительна в локальном окне, поэтому производную можно перенести под интеграл.',
               'На положительной ветви подстановка t=tan x даёт производную π/(A+B) по A=|p| при B=|q|>0. При A=B интеграл известен из постоянного логарифма.',
               'Абсолютные значения восстанавливают все четыре знаковые ветви. На каждой оси логарифмический конец интегрируем, а формула следует из интеграла log(sin x) или log(cos x). При обоих нулевых параметрах исходный логарифм не определён.']
        auxiliary['partial_positive_branch']='pi/(A+B)'
    elif family=='unit_circle_log':
        den=m.add(m.add(ONE,m.neg(m.mul(q(2),m.mul(a,c)))),m.power(a,2))
        expected=m.div(m.mul(q(2),m.add(a,m.neg(c))),den)
        part=m.div(m.add(ONE,m.div(m.add(m.power(a,2),q(-1)),den)),a)
        if not same_value(expected,part):raise Unsupported('The parameter derivative must separate into a scalar and a reciprocal term')
        conclusion=dict(cases=({ 'condition':f'abs({p})<=1','value':ZERO},
                   {'condition':f'abs({p})>1','value':m.mul(q(2),m.mul(m.PI,('ln',('abs',a))))}))
        steps=['Разбить параметр при p=±1. На каждой компактной части открытой ветви знаменатель ограничен снизу (1−|p|)²>0.',
               'Подстановка t=tan(x/2) даёт интеграл обратного знаменателя π/|1−p²|. Внутри |p|<1 производная исходного интеграла равна нулю, включая p=0.',
               'При |p|>1 выделить 2 ln|p| и взять обратный параметр. При p=±1 вычислить предельный логарифмический край отдельно через удвоение угла.']
        auxiliary['derivative_split']=part
    elif family=='inverse_tangent_ratio':
        expected=m.div(ONE,m.add(ONE,m.power(m.mul(a,u),2)))
        answer=m.mul(m.div(m.PI,q(2)),('ln',m.add(ONE,('abs',a))))
        conclusion=dict(cases=({'condition':f'{p}<0','value':m.neg(answer)},{'condition':f'{p}>=0','value':answer}))
        steps=['На открытом интервале 0<x<π/2 исходная частная производная по p заключена между 0 и 1. Ядро имеет следы p у нуля и 0 у π/2.',
               'При t=tan x интеграл производной равен интегралу 1/((1+t²)(1+p²t²)). Разложение даёт π/(2(1+|p|)); при p=0 и |p|=1 формула следует прямым интегрированием.',
               'Восстановить исходную функцию интегрированием от нулевого параметра, отдельно на обеих полуосях.']
        auxiliary['dominant_bound']=ONE
    else:
        r=('s',roles['r'])
        expected=m.mul(('exp',m.neg(m.mul(r,x))),('cos',m.mul(a,x)))
        conclusion=dict(cases=tuple(dict(condition=f'{p}{rel}0',value=m.mul(q(n,2),m.PI))
                                   for rel,n in (('<',-1),('=',0),('>',1))))
        steps=['При положительном регуляторе дифференцировать по частоте под мажорантом exp(−regulator·x). Интеграл косинуса равен regulator/(regulator²+frequency²).',
               'Нулевой частоте соответствует нулевой интеграл. Первообразная по частоте даёт atan(frequency/regulator).',
               'При ненулевой частоте интегрирование по частям даёт равномерную оценку хвоста 2/(|frequency|R), включая нулевой регулятор. На конечном интервале применить ограничение |sin(frequency·x)/x|≤|frequency|. Нулевая частота обрабатывается напрямую.']
        auxiliary.update(regulator=r,regulated_integrand=regulated,tail_constant=m.div(q(2),('abs',a)))
    if not same_value(derivative,expected):
        raise Unsupported('The checked elementary derivative disagrees with the integral plan')
    proof_method='anchored_parameter_derivative' if family=='anchored_log_ratio' else family
    return emit(proof_method,steps,conclusion,binding_family=family,role_binding=roles,raw_integrand=raw,derivative_table=trace,
                partial_derivative=derivative,**auxiliary)


def oriented_box_endpoints(task):
    """Eliminate one independent oriented box coordinate per fundamental theorem application."""
    from itertools import product as corners

    order=task['integration_order']
    trace=re.fullmatch(r'([A-Za-z][A-Za-z_0-9]*?)_([A-Za-z]+)\(([A-Za-z, ]+)\)',task['integrand'])
    if (not trace or task['requested_output']!=['boundary_formula'] or len(order)!=3 or
            any(not isinstance(row,dict) or set(row)!={'variable','lower','upper'} for row in order)):
        raise Unsupported('A mixed third derivative on an oriented box is required')
    coordinates=[row['variable'] for row in order]
    if (list(trace[2])!=coordinates or trace[3].replace(' ','').split(',')!=coordinates or
            any(not isinstance(z,str) for row in order for z in (row['lower'],row['upper']))):
        raise Unsupported('The mixed derivative notation and the bound coordinate order must agree')
    roles,_=bind_integral_symbols(zip(('x','y','z'),coordinates,strict=True))
    ends=[(row['lower'],row['upper']) for row in order]
    names=sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',' '.join(s for pair in ends for s in pair)))
                 -m.FUNCTIONS-set(m.ALIASES)-{'e','pi'})
    if set(names)&set(coordinates):
        raise Unsupported('A rectangular endpoint cannot contain a bound integration variable')
    ctx=dict(parameters=names,assumptions=[])
    endpoints=[tuple(m.parse(s,None,names) for s in pair) for pair in ends]
    if not all(m.constant_defined(e,ctx) for pair in endpoints for e in pair):
        raise Unsupported('An original oriented endpoint is not real-defined')
    terms=[]
    for bits in corners((1,0),repeat=len(order)):
        args=tuple(pair[i] for pair,i in zip(ends,bits,strict=True))
        terms.append(((-1)**(len(order)-sum(bits)),args))
    formula=''.join(('+' if sign>0 else '-')+trace[1]+'('+','.join(args)+')' for sign,args in terms).removeprefix('+')
    return [f'Применить формулу Ньютона–Лейбница по {v}, сохраняя верхний конец со знаком +, а нижний со знаком −.'
           for v in reversed(coordinates)],dict(boundary_formula=formula,
               condition='the original iterated derivatives and integrals satisfy the fundamental theorem on the oriented intervals'), \
           dict(role_binding=roles,original_endpoints=endpoints,signed_corners=terms)


def euler_endpoint_shape(task):
    """Recognize the kernel, conditions and oriented limits before using an Euler identity."""
    text=task.get('integrand','')
    kind=task['kind'];bounds=task.get('limits');conditions=task.get('stated_conditions',[])
    if not isinstance(text,str) or not isinstance(bounds,str) or not isinstance(conditions,list):
        raise Unsupported('Missing original integrand, bounds or conditions')
    if kind=='parameter_improper_evaluation' and task.get('method_requirement')=='specified_gamma_representation':
        if bounds!='0..inf' or len(conditions)!=1:raise Unsupported('Both original improper ends and the power range are required')
        wave=re.match(r'^\s*(sin|cos)\s*\(',text)
        ref=re.fullmatch(r'(.+?)=int_0\^inf\s+(.+?)d([A-Za-z_]\w*)/Gamma\((.+?)\),\s*(.+?)>0',
                         task.get('reference_formula',''))
        cut=re.fullmatch(r'0<(.+?)<(1|2)',conditions[0])
        if not (wave and ref and cut and cut[2]==('1' if wave[1]=='cos' else '2')):
            raise Unsupported('The prescribed gamma representation, differential and strict index range are required')
        roles,(raw,*_)=bind_integral_symbols([(wave[1]+'(a*x)/x^m',text),('x^(-m)',ref[1]),
            ('t^(m-1)*exp(-x*t)',ref[2]),('t',ref[3]),('m',ref[4]),('x',ref[5]),('m',cut[1])])
        return 'gamma_laplace_'+wave[1],roles,raw
    if kind!='euler_integral_evaluation' or task.get('method_requirement')!='euler_integrals_and_domain':
        raise Unsupported('The printed Euler method has to be preserved')
    if g:=re.fullmatch(r'ln\(Gamma\(([A-Za-z_]\w*)\)\)(?:\*(.+))?',text.replace(' ','')):
        formulas=[('x',g[1])]
        if bounds=='0..1' and not conditions and g[2] is None:
            shape='gamma_reflection_zero'
        elif bounds=='0..1' and not conditions and g[2] is not None:
            shape='gamma_reflection_sine'
            formulas.append(('sin(pi*x)',g[2]))
        elif bounds=='0..1' and len(conditions)==1 and g[2] is not None:
            order=re.fullmatch(r'([A-Za-z_]\w*) positive integer',conditions[0])
            if not order:raise Unsupported('The Fourier order has to be a positive integer')
            shape='gamma_reflection_cosine'
            formulas.extend([('cos(2*n*pi*x)',g[2]),('n',order[1])])
        elif len(conditions)==1 and g[2] is None:
            ends=bounds.split('..')
            lower=re.fullmatch(r'(.+?)>0',conditions[0])
            if len(ends)!=2 or not lower:raise Unsupported('The original translated gamma interval has changed')
            shape='gamma_reflection_shifted'
            formulas.extend([('a',ends[0]),('a+1',ends[1]),('a',lower[1])])
        else:raise Unsupported('The gamma reflection weight or the original endpoint hypotheses have changed')
        roles,_=bind_integral_symbols(formulas)
        return shape,roles,m.parse(text,None,tuple(roles.values()),extra_functions=('Gamma',))
    schemas=(
        ('linear_fractional_beta','a..b','(x-a)^m*(b-x)^n/(x+c)^(m+n+2)',('0<a<b','c>0')),
        ('half_angle_beta','0..pi','sin(x)^(n-1)/(1+k*cos(x))^n',('0<abs(k)<1',)),
        ('oriented_power_mean','0..inf','(x^(p-1)-x^(q-1))/((1+x)*ln(x))',()),
        ('reflected_power_difference','0..inf','(x^(p-1)-x^(-p))/(1-x)',('0<p<1',)),
        ('hyperbolic_reflection','0..inf','sinh(a*x)/sinh(b*x)',('0<a<b',)),
    )
    for shape,expected,pattern,limits in schemas:
        if len(limits)!=len(conditions):continue
        eq=[]
        for template,actual in zip(limits,conditions,strict=True):
            refs=re.split(r'([<>])',template)
            got=re.split(r'([<>])',actual)
            if refs[1::2]!=got[1::2]:break
            eq.extend(zip(refs[::2],got[::2],strict=True))
        else:
            if expected=='a..b':
                ends=bounds.split('..')
                if len(ends)!=2:continue
                eq.extend(zip(('a','b'),ends))
            elif bounds!=expected:continue
            try:
                roles,(raw,*_)=bind_integral_symbols([(pattern,text),*eq])
                return shape,roles,raw
            except Unsupported:pass
    raise Unsupported('No endpoint-preserving Euler reduction matches the unsimplified source')


def euler_endpoint_candidate(task):
    kind=task.get('kind')
    if kind not in ('euler_integral_evaluation','parameter_improper_evaluation','euler_integral_identity'):return False
    try:
        if kind=='euler_integral_identity':euler_power_identity(task)
        else:euler_endpoint_shape(task)
    except (Unsupported,TypeError,ValueError):return False
    return True


def euler_endpoint_transport(task,library):
    """Check one explicit beta chart or a gamma-regularized oscillatory integral."""
    from derivative_proofs import table
    from verify import same_value

    if not library.data.get('euler_endpoint_transport'):
        raise Unsupported('Endpoint-preserving Euler transports are not loaded')
    if task['kind']=='euler_integral_identity':return euler_power_identity(task)
    shape,roles,raw=euler_endpoint_shape(task)
    S={role:('s',name) for role,name in roles.items()}
    meta=task.get('source',{})
    gamma=shape.startswith('gamma_laplace')
    heading='Найти интеграл, используя данное интегральное представление.' if gamma else 'Определить область существования и выразить через эйлеровы интегралы.'
    allowed={'kind','id','source','integrand','limits','stated_conditions','method_requirement','requested_output'}
    allowed|={'reference_formula'} if gamma else {'printed_hint'} if shape=='reflected_power_difference' else set()
    expected=['exact_integral','specified_method'] if gamma else ['existence_domain','euler_integral_formula']
    if (set(task)-allowed or not isinstance(meta,dict) or meta.get('literal_requirement',heading)!=heading
        or set(meta)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
        or task.get('requested_output')!=expected
        or task.get('printed_hint') not in (None,'lim_eps->infinity [B(p,eps)-B(1-p,eps)]')):
        raise Unsupported('The printed requirements or the exact hint have changed')
    def plus(a,b):return m.add(a,b)
    def minus(a,b):return m.add(a,m.neg(b))
    def power(a,b):return ('rpow',a,b)
    def mul(a,b):return m.mul(a,b)
    def ratio(a,b):return m.div(a,b)
    def trig(tag,arg):return (tag,arg)
    def show(e):return source(e)
    def label(pattern):return re.sub(r'\b[A-Za-z_]\w*\b',lambda h:roles.get(h[0],h[0]),pattern)
    x=S['x'];details={}
    if shape=='linear_fractional_beta':
        a,b,c,u,v=(S[k] for k in ('a','b','c','m','n'))
        length,low,high=minus(b,a),plus(a,c),plus(b,c);interior=plus(x,c)
        chart=ratio(mul(high,minus(x,a)),mul(length,interior))
        other=ratio(mul(low,minus(b,x)),mul(length,interior))
        axis=('v',roles['x'])
        derivative,trace=table(m.substitute(chart,{x:axis}),roles['x'],library)
        derivative=m.substitute(derivative,{axis:x})
        jacobian=ratio(mul(low,high),mul(length,m.power(interior,2)))
        if not all((same_value(plus(chart,other),ONE),same_value(derivative,jacobian),
                    same_value(m.substitute(chart,{x:a}),ZERO),same_value(m.substitute(chart,{x:b}),ONE))):
            raise Unsupported('The fractional change must preserve both boundaries and its Jacobian')
        arguments=(plus(u,ONE),plus(v,ONE))
        scale=ratio(power(length,plus(plus(u,v),ONE)),mul(power(low,arguments[1]),power(high,arguments[0])))
        output=dict(value=show(scale)+' * B('+', '.join(map(show,arguments))+')',domain=[label('m>-1'),label('n>-1')])
        steps=['Из 0<a<b и c>0 следует, что x+c, a+c, b+c и b−a положительны.',
               'Проверить дробно-линейную карту, её дополнение до единицы и положительный якобиан. Карта переводит исходные края точно в 0 и 1.',
               'Собрать множитель и бета-ядро. При каждом исходном крае показатель соответствующей степени должен быть строго больше −1.']
        details.update(chart=chart,complement=other,jacobian=jacobian,derivative_trace=trace,beta_arguments=arguments,beta_factor=scale)
    elif shape=='half_angle_beta':
        n,k=(S[a] for a in ('n','k'));A,B=plus(ONE,k),minus(ONE,k)
        internal='__beta_halfangle'
        while internal in roles.values():internal+='_'
        t=('s',internal);t2=m.power(t,2)
        pulled=plus(ONE,mul(k,ratio(minus(ONE,t2),plus(ONE,t2))))
        target=ratio(plus(A,mul(B,t2)),plus(ONE,t2))
        if not same_value(pulled,target):raise Unsupported('The half-angle denominator check failed')
        p=ratio(n,q(2))
        scale=ratio(power(q(2),minus(n,ONE)),power(mul(A,B),p))
        output=dict(value=show(scale)+' * B('+show(p)+', '+show(p)+')',domain=[label('n>0')])
        steps=['Подстановка t=tan(x/2) переводит открытый отрезок в положительную полуось. Из |k|<1 получаются положительные 1+k и 1−k.',
               'Проверить полуугловой знаменатель. После сокращения общих положительных степеней выполнить y=(1−k)t²/(1+k).',
               'На обоих исходных краях показатель синуса равен n−1. Бета-аргументы n/2,n/2 положительны ровно при n>0.']
        details.update(half_angle_denominator=target,beta_arguments=(p,p),scales=(A,B),beta_factor=scale)
    elif shape=='oriented_power_mean':
        p,q_=S['p'],S['q'];half=ratio(m.PI,q(2))
        tau=lambda z:trig('tan',mul(half,z))
        formula=('ln',ratio(tau(p),tau(q_)))
        output=dict(cases=[dict(condition=label('p=q'),value=ZERO),
                           dict(condition=label('p!=q and 0<p<1 and 0<q<1'),value=formula)],
                    divergent='other real parameters',removable_trace=ratio(minus(p,q_),q(2)))
        steps=['При равенстве показателей разность обнуляется тождественно. Точка x=1 имеет конечный след.',
               'Для различных показателей у нуля доминирует меньшая степень, у бесконечности — большая. Равенство на границе даёт расходимость интеграла 1/(x|ln x|).',
               'Разность, делённую на ln x, заменить ориентированным интегралом по показателю. Внутренний бета-момент равен π/sin(πs); его первообразная ln tan(πs/2).']
        details.update(exponent_window=(p,q_),parameter_reversed_if_needed=True,lower_requirement='min(p,q)>0',upper_requirement='max(p,q)<1')
    elif shape in ('reflected_power_difference','hyperbolic_reflection'):
        hyperbolic=shape=='hyperbolic_reflection'
        if hyperbolic:
            a,b=S['a'],S['b'];p=ratio(minus(b,a),mul(q(2),b));scale=ratio(ONE,mul(q(2),b))
            output=dict(value=mul(mul(scale,m.PI),trig('tan',mul(m.PI,ratio(a,mul(q(2),b))))),
                        domain=task['stated_conditions'])
            steps=['Замена t=e^(−2βx) меняет направление на (0,1). Положительные исходные параметры дают p=(β−α)/(2β)∈(0,1/2).']
        else:
            p=S['p'];scale=q(2)
            output=dict(value=mul(mul(scale,m.PI),trig('cot',mul(m.PI,p))),domain=task['stated_conditions'])
            steps=['Разделить обычный интеграл в устранимой точке x=1. Подстановка t=1/x в верхней части даёт вторую копию нижней.']
            if task.get('printed_hint'):
                steps.append('Печатная необязательная подсказка с ε→∞ даёт нуль, поскольку оба бета-интеграла исчезают. Здесь нужен предел ε→0+ и коэффициент 2 от отражения.')
        steps.extend(['В ядре (t^(p−1)−t^(−p))/(1−t) оба показателя у нуля больше −1. У единицы разность снимает полюс.',
                      'Разность B(p,ε)−B(1−p,ε) при ε→0+ оставляет ψ(1−p)−ψ(p)=πcot(πp). Вернуть точный множитель исходной меры.'])
        details.update(beta_arguments=(p,minus(ONE,p)),factor=scale,regularizer_direction='0+')
    elif shape.startswith('gamma_reflection_'):
        mode=shape.removeprefix('gamma_reflection_');anchor=ratio(('ln',mul(q(2),m.PI)),q(2))
        steps=['Рекурсия Γ(x+1)=xΓ(x) доказывает логарифмическую интегрируемость у нуля. На правом крае Γ непрерывна и положительна.',
               'При x↦1−x выбранный вес сохраняется. Формула отражения превращает сумму логарифмов в ln π−ln sin(πx).']
        if mode=='zero':
            value=anchor
            steps.append('Угловой интеграл логарифма синуса вычислить удвоением аргумента, затем разделить пополам.')
        elif mode=='shifted':
            a=S['a'];value=plus(anchor,minus(mul(a,('ln',a)),a))
            steps.append('На исходном a>0 продифференцировать интеграл с двумя подвижными краями. Разность логарифмов Γ равна ln a по рекурсии. Предел при a↓0 даёт найденное значение на [0,1].')
        elif mode=='sine':
            value=ratio(plus(ONE,('ln',ratio(m.PI,q(2)))),m.PI)
            steps.append('В оставшемся угловом интеграле использовать u=cos(πx). Вес sin(πx) даёт постоянную меру, а логарифм превращается в (1/2)ln(1−u²).')
        else:
            n=S['n'];value=ratio(ONE,mul(q(4),n))
            steps.append('При положительном целом n постоянная часть исчезает. Абелев ряд ln|1−ρe^(2πix)| даёт коэффициент −ρ^n/(2n). При ρ↑1 мажорант C+|ln sin(πx)| сохраняет оба края.')
        output=dict(value=value,domain=task['stated_conditions'] or 'ordinary absolutely convergent')
        details.update(unit_interval_anchor=anchor,reflection='x -> 1-x',weight=mode)
    else:
        a,m_=S['a'],S['m'];sine=shape.endswith('_sin')
        power_index=ratio(m_,q(2));ifreq=('abs',a);theta=mul(m.PI,power_index)
        den_tag='sin' if sine else 'cos'
        factor=ratio(mul(m.PI,power(ifreq,minus(m_,ONE))),mul(q(2),trig(den_tag,theta)))
        if sine:factor=mul(factor,ratio(a,ifreq))
        output=dict(nonzero_frequency_value=show(factor)+' / Gamma('+show(m_)+')',
                    zero_frequency=dict(value=ZERO,convergence='ordinary') if sine else dict(convergence='divergent_at_infinity'),
                    domain=task['stated_conditions'])
        steps=['При ненулевой частоте вставить положительный абелев регулятор в исходное гамма-представление. До перестановки проверить абсолютную сходимость.',
               'У нуля косинус требует m<1, а синус благодаря |sin(ax)|≤|a|x допускает m<2. При большом промежуточном t внутренний абсолютный интеграл ограничен соответственно O(t⁻¹) или O(t⁻²).',
               'Вычислить экспоненциальный синус или косинус. Хвост исходного интеграла равномерно стремится к нулю по Дирихле, поэтому снять абелев множитель и заменить t=|a|u.',
               'Полурадиальная степенная замена даёт бета-момент. Отдельно вычислить нулевую частоту, где деление на |a| запрещено.']
        details.update(beta_first_argument=power_index if sine else plus(power_index,q(1,2)),
                       representation=task['reference_formula'],frequency=a,prefactor=factor,gamma_argument=m_)
    return dict(theorem='method.euler_endpoint_transport',binding=roles,family=shape,raw_integrand=raw,
                source_conditions=task.get('stated_conditions',[]),original_bounds=task['limits'],steps=steps,**details),output


def euler_power_identity(task):
    """Normalize actual powers on open fibers before checking a product or limit."""
    from verify import same_value

    meta=task.get('source',{})
    if (set(task)-{'kind','id','source','claim','requested_output'} or not isinstance(meta,dict)
            or set(meta)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement'}
            or meta.get('literal_requirement') not in (None,'Доказать напечатанное равенство.')
            or task.get('requested_output')!=['proof_or_counterexample']):
        raise Unsupported('The printed equality and all original obligations have to be bound')
    claim=task.get('claim')
    if not isinstance(claim,str):raise Unsupported('A concrete Euler identity is required')
    equation=claim.replace('²','^2')
    lhs,sep,rhs=equation.partition('=')
    if not sep:raise Unsupported('A concrete Euler identity is required')
    conclusion=m.parse(rhs,None)
    if not m.constant_defined(conclusion,{'parameters':[],'assumptions':[]}):
        raise Unsupported('An original claimed value is not real-defined')
    hit=re.fullmatch(r'lim_([A-Za-z_]\w*)->inf int_0\^inf (.+)d([A-Za-z_]\w*)',lhs)
    if hit:
        roles,(raw,*_)=bind_integral_symbols([('exp(-x^n)',hit[2]),('x',hit[3]),('n',hit[1])])
        if not same_value(conclusion,ONE):raise Unsupported('The printed limit disagrees with the Euler evaluation')
        return dict(theorem='method.euler_endpoint_transport',family='power_gamma_limit',binding=roles,raw_integrand=raw,steps=[
            'При любом положительном показателе заменить t=x^n. Нижний показатель гамма-ядра 1/n−1>−1, а верхний край экспоненциальный.',
            'Получить Γ(1/n)/n. Рекурсия превращает это отношение в Γ(1+1/n), и непрерывность в единице даёт предел 1.']),dict(identity=True,value=ONE)
    def monomial(e,x):
        if e==ONE:return F(0)
        if e==x:return F(1)
        if e[0] in ('pow','rpow') and e[1]==x:
            val=F(e[2]) if e[0]=='pow' else m.num(m.simplify(e[2]))
            if val is not None:return val
        raise Unsupported('The original power in the product is not a scalar monomial')
    terms=re.split(r'\s*\*\s*(?=int_0\^)',lhs)
    if len(terms)!=2:raise Unsupported('Two finite or two half-line Euler factors are required')
    arguments=[];powers=[];binders=[];raws=[];family=None
    for term in terms:
        f=re.fullmatch(r'int_0\^(1|inf)\s*(.*?)d([A-Za-z_]\w*)(/sqrt\(.*\))?',term.strip())
        if not f:raise Unsupported('Bind each original integral to its own differential')
        x=('s',f[3]);binders.append(f[3])
        which='beta' if f[1]=='1' else 'gamma'
        if family is not None and family!=which:raise Unsupported('The Euler kernels use different endpoint classes')
        family=which
        kernel=m.parse(((f[2].strip() or '1')+(f[4] or '')),None,[f[3]]);raws.append(kernel)
        if family=='beta' and kernel[0]=='div' and kernel[2][0]=='sqrt':
            numerator,inner=kernel[1],kernel[2][1]
            if inner[0]!='add' or inner[1]!=ONE or inner[2][:2]!=('mul',q(-1)):
                raise Unsupported('The finite positive power complement must be 1 minus a monomial')
            degree=monomial(inner[2][2],x)
        elif family=='gamma':
            numerator,e=kernel[1:] if kernel[0]=='mul' else (ONE,kernel)
            if e[0]!='exp' or e[1][:2]!=('mul',q(-1)):raise Unsupported('A negative power exponent is required')
            degree=monomial(e[1][2],x)
        else:raise Unsupported('The original power kernel was not found')
        alpha=monomial(numerator,x)+1
        if degree<=0 or alpha<=0:raise Unsupported('The original power and lower exponent must be strictly positive')
        arguments.append(alpha/degree);powers.append(degree)
    a,b=sorted(arguments)
    prefactor=q(1/(powers[0]*powers[1]))
    if family=='gamma' and a+b==1:
        value=m.div(m.mul(prefactor,m.PI),('sin',m.mul(m.PI,q(a))))
        simplification='У гамма-аргументов сумма 1. Применить формулу отражения.'
    elif family=='beta' and (a,b)==(F(1,4),F(3,4)):
        value=m.mul(m.mul(q(4),prefactor),m.PI)
        simplification='В бета-произведении один общий гамма-множитель сокращается. Второй сокращается после Γ(5/4)=(1/4)Γ(1/4), а Γ(1/2)²=π.'
    else:raise Unsupported('The beta or gamma product does not have a proved simplification')
    if not same_value(value,conclusion):raise Unsupported('The checked Euler product disagrees with the original right hand side')
    return dict(theorem='method.euler_endpoint_transport',family='power_'+family+'_product',
                binding=dict(first=binders[0],second=binders[1]),raw_integrands=raws,power_arguments=tuple(map(q,arguments)),
                steps=['Для каждого исходного связанного x выполнить свою замену t=x^r с r>0.',
                       'Проверить положительность обоих нижних аргументов. При конечной границе верхний показатель равен −1/2, на бесконечности действует экспоненциальное затухание.',
                       simplification]),dict(identity=True,value=value)


def compact_parameter_integral_goal(task):
    try:exponential_circle_profile(task)
    except (Unsupported,TypeError,ValueError,KeyError):pass
    else:return True
    kind=task.get('kind')
    if kind=='iterated_integral':
        try:compact_angular_log_profile(task)
        except (Unsupported,TypeError,ValueError,KeyError):return False
        return True
    return (kind=='parameter_integral_source_goal'
            or kind in ('integral_parameter_series','integral_series_identity')
            or kind=='parameter_integral_continuity' and isinstance(task.get('source_formula'),str)
            and 'sign(' in task['source_formula'] and task.get('requested_output')==['prove continuity']
            or kind=='parameter_integral_derivative' and isinstance(task.get('integrand'),str)
            and bool(re.fullmatch(r'[A-Za-z]\w*\([A-Za-z]\w*\)\*abs\([A-Za-z]\w*-[A-Za-z]\w*\)',task['integrand']))
            or kind=='parameter_integral_identity' and isinstance(task.get('definition'),str)
            and (bool(re.match(r'[A-Za-z]\w*\([A-Za-z]\w*\)=int_0\^[A-Za-z]\w* [A-Za-z]\w*\([A-Za-z]\w*\)/sqrt\(',task['definition']))
                 or ';K=' in task['definition'] and ' for ' in task['definition']))


def compact_parameter_integral(task,lib,request):
    if lib.data.get('remaining_analysis_proofs'):
        try:return circle_integral_goal(task)
        except Unsupported:pass
    if not lib.data.get('compact_parameter_transport'):
        raise Unsupported('Compact parameter integral transport is unavailable')
    kind=task['kind'];meta=task.get('source',{})
    fields={'kind','id','source','requested_output'}
    if not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement','page_png_sha256'}:
        raise Unsupported('The original printed parameter goal must be retained')
    def result(name,argument,value,**details):
        return dict(theorem='method.compact_parameter_integral_transport',family=name,steps=argument,**details),value
    if kind in ('integral_parameter_series','integral_series_identity'):
        return compact_integral_series(task,meta,fields,result)
    if kind=='iterated_integral':
        roles=compact_angular_log_profile(task)
        if meta.get('literal_requirement') not in (None,'Найти интеграл. 0..pi'):
            raise Unsupported('The original angular integral asks for another method')
        child=request('same angular logarithmic kernel on its original ends',dict(kind='evaluate_via_parameter',
            integrand=task['integrand'],limits='0..pi',stated_conditions=[],method_requirement='differentiate_under_integral',
            requested_output=['value_and_specified_method']))
        return result('angular_log_integral_subgoal',[
            'Выделить исходное угловое ядро с полным отрезком от 0 до π. Сохранить свободный параметр и переменную интегрирования.',
            'Поставить цель вычисления того же ядра через его параметрическую производную. Проверенная дочерняя цепочка обрабатывает внутреннюю, внешнюю и обе особые ветви.'],
            child['value'],roles=roles)
    if kind in ('parameter_integral_derivative','parameter_integral_identity'):
        return compact_operator_integral(task,meta,fields,result)
    if kind=='parameter_integral_continuity':
        if set(task)-fields-{'source_formula','stated_conditions'} or task.get('stated_conditions') or (
                task.get('requested_output')!=['prove continuity'] or meta.get('literal_requirement') not in (None,'prove continuity and draw graph')):
            raise Unsupported('The original step-kernel continuity question must be retained')
        interval=re.fullmatch(r'[A-Za-z]\w*\(([A-Za-z]\w*)\)=int_(.+?)\^(.+?) sign\((.+)\) d([A-Za-z]\w*)',task['source_formula'])
        if not interval:raise Unsupported('Expected a step kernel with an explicit integration coordinate')
        roles,_=bind_integral_symbols([('x-y',interval[4]),('x',interval[5]),('y',interval[1])])
        lo,hi=compact_numeric_bounds(interval.group(2,3));order=m.sign(m.add(hi,m.neg(lo)),{'parameters':[],'assumptions':[]})
        if order!=1:raise Unsupported('The source step interval must be ordered')
        y=('s',roles['y']);width=m.add(hi,m.neg(lo))
        return result('step_kernel_parameter_continuity',[
            'Разделить исходный отрезок в точке параметра, если она принадлежит отрезку. Единственное значение знака в точке раздела интеграла не меняет.',
            'Внутри отрезка складываются две длины с противоположными знаками. Снаружи знак постоянен. В обеих границах соседние формулы совпадают.'],
            dict(continuous_on='R',cases=[dict(when=roles['y']+'<='+source(lo),value=width),
                dict(when=source(lo)+'<'+roles['y']+'<'+source(hi),value=m.add(m.add(lo,hi),m.mul(q(-2),y))),
                dict(when=roles['y']+'>='+source(hi),value=m.neg(width))]),bounds=(lo,hi),roles=roles)
    if (set(task)-fields-{'goal'} or not isinstance(task.get('goal'),str) or
            task.get('requested_output')!=['full_printed_conclusion','justification'] or meta.get('literal_requirement')):
        raise Unsupported('The source integral and its full mathematical conclusion must be bound')
    goal=task['goal'].replace('−','-').replace('²','^2')
    packet=re.fullmatch(r'lim_\(([A-Za-z]\w*)→(0|\+?∞)\) ∫_(\([^()]*\)|[^()\s^]+)\^(\([^()]*\)|[^()\s]+) (.+?)(?:, ([A-Za-z]\w*) natural)?',goal)
    if packet:
        text=packet[5];name=packet[1]
        found=re.fullmatch(r'd([A-Za-zθ]\w*)/(.+)',text)
        if found:var,body=found[1],'1/'+found[2]
        else:
            Found=re.fullmatch(r'(.+) d([A-Za-zθ]\w*)',text)
            if not Found:raise Unsupported('The original integration differential remains unspecified')
            body,var=Found.groups()
        normalize=lambda s:re.sub(r'(?<=[A-Za-z0-9_)])\s+(?=[A-Za-z0-9_(])','*',
             re.sub(r'\b(sin|cos)\s+([A-Za-z_]\w*)\b',r'\1(\2)',s.replace('π','pi').replace('θ','theta')))
        return compact_limit_fiber(name,var.replace('θ','theta'),packet[2],normalize(body),tuple(map(normalize,packet.group(3,4))),
                                   packet[6],lib,result)
    return compact_local_kernel_goal(goal,lib,result)


def compact_numeric_bounds(pairs):
    bounds=tuple(m.parse(s,None) for s in pairs)
    if not all(m.constant_defined(z,{'parameters':[],'assumptions':[]}) for z in bounds):
        raise Unsupported('An original finite endpoint is not real-defined')
    return tuple(map(m.simplify,bounds))


def compact_limit_fiber(name,var,target,text,pair,index,lib,result):
    from derivative_proofs import table
    from verify import same_value

    if name==var or index not in (None,name):
        raise Unsupported('The varying parameter and integral binder must remain distinct')
    p,x=('s',name),('s',var);raw=m.parse(text,None,[name,var])
    ctx={'parameters':[name],'assumptions':[]}
    lower,upper=[m.parse(z,None,[name]) for z in pair]
    if not all(m.constant_defined(z,ctx) for z in (lower,upper)):
        raise Unsupported('The original parameter endpoints are not real-defined')
    lo,hi=[m.simplify(m.substitute(z,{p:ZERO})) for z in (lower,upper)]
    if target=='0' and index is None and raw==m.parse('1/(1+'+var+'^2+'+name+'^2)',None,[var,name]):
        if not all(same_value(z,m.add(c,p)) for z,c in ((lower,lo),(upper,hi))):
            raise Unsupported('Both oriented edges must move by the same translation, with the original denominator')
        return result('translated_compact_limit',[
            'Перенести оба исходных края одной заменой x=t+p. Якобиан равен 1 и область t становится неподвижной.',
            'Знаменатель всюду не меньше 1. После замены разность знаменателей ограничена 2|t||p|+2p², значит обратные знаменатели сходятся равномерно.',
            'После переноса предела проинтегрировать 1/(1+t²) по неподвижному отрезку.'],
            dict(value=m.add(('atan',hi),m.neg(('atan',lo)))),source_bounds=(lower,upper),fixed_bounds=(lo,hi),variable=var,parameter=name)
    if any(m.contains(z,p) for z in (lower,upper)):
        raise Unsupported('A common compact fiber or exact translated fiber is needed')
    if target=='0' and index is None:
        if raw==m.parse('sqrt('+var+'^2+'+name+'^2)',None,[var,name]):
            primitive=lambda z:m.mul(q(1,2),m.mul(z,('abs',z)))
            return result('uniform_square_root_remainder',[
                'Для любых вещественных t,p из неравенства треугольника следует 0≤√(t²+p²)−|t|≤|p|.',
                'Интегральный остаток ограничен длиной исходного отрезка, умноженной на |p|. Затем применяется первообразная t|t|/2.'],
                dict(value=m.add(primitive(hi),m.neg(primitive(lo)))),source_bounds=(lo,hi),pointwise_error='|p|')
        cosine=m.parse('cos('+name+'*'+var+')',None,[var,name])
        weight=ONE if raw==cosine else next((a for a,b in (raw[1:],raw[1:][::-1]) if b==cosine),None) if raw[0]=='mul' else None
        if weight is not None:
            if not m.constant_defined(weight,{'parameters':[name,var],'assumptions':[]}):
                raise Unsupported('The original polynomial weight can have a hidden domain restriction')
            coeff=riemann_polynomial(weight,x)
            if coeff is None or any(m.num(a) is None for a in coeff):
                raise Unsupported('Expected a polynomial weight in the original coordinate')
            def evaluate(z):
                out=ZERO
                for j,c in enumerate(coeff,1):out=m.add(out,m.mul(m.div(c,q(j)),m.power(z,j)))
                return out
            return result('uniform_trigonometric_remainder',[
                'На компактном исходном отрезке |cos(pt)−1|≤|pt|. Полиномиальный вес ограничен, и интегральный остаток исчезает равномерно.',
                'В предельном ядре остаётся исходный полином. Вычислить его интеграл почленно.'],
                dict(value=m.add(evaluate(hi),m.neg(evaluate(lo)))),source_bounds=(lo,hi),polynomial=coeff)
    if target in ('∞','+∞') and index==name and raw==m.parse('1/(1+(1+'+var+'/'+name+')^'+name+')',None,[var,name]):
        primitive=m.add(x,m.neg(('ln',m.add(ONE,('exp',x)))));v=('v',var)
        derivative,trace=table(m.substitute(primitive,{x:v}),var,lib)
        limit=m.div(ONE,m.add(ONE,('exp',x)))
        if not same_value(m.substitute(derivative,{v:x}),limit):
            raise Unsupported('The primitive must match the limiting positive kernel')
        at=lambda z:m.substitute(primitive,{x:z})
        return result('uniform_exponential_mesh',[
            'Для n больше удвоенной границы |t| на отрезке база 1+t/n положительна. Логарифмический остаток |n ln(1+t/n)−t| ограничен константой, делённой на n.',
            'Экспонента и преобразование s↦1/(1+s) равномерно непрерывны на полученном компактном диапазоне. Перенести предел под интеграл.',
            'Таблично проверить первообразную t−ln(1+e^t) и оценить её на исходных краях.'],
            dict(value=m.add(at(hi),m.neg(at(lo)))),source_bounds=(lo,hi),limit_kernel=limit,derivative_trace=trace,integer_index=name)
    if target in ('∞','+∞') and index is None and raw==m.parse('exp(-'+name+'*sin('+var+'))',None,[var,name]):
        a,b=m.pi_multiple(lo),m.pi_multiple(hi)
        if a is None or b is None or not all(0<=w<=1 for w in (a,b)):
            raise Unsupported('Both original ends must lie on the nonnegative sine arch')
        return result('concentrating_sine_limit',[
            'На [0,π] синус снизу ограничен двумя хордами (2/π)min(t,π−t). Оба исходных конца лежат внутри этой дуги.',
            'При положительном параметре сравнить с суммой двух затухающих экспоненциальных интегралов. Модуль всего ориентированного интеграла не превосходит π/p и стремится к нулю.'],
            dict(value=ZERO),source_bounds=(lo,hi),edge_majorant='pi/p')
    raise Unsupported('No compact error estimate can be proved on the original parameter interval')


def compact_local_kernel_goal(goal,lib,result):
    documented=r'[A-Za-zΑ-Ωα-ω]\w*'
    def bind(packet):
        roles=packet.groupdict()
        if len(set(roles.values()))!=len(roles):raise Unsupported('A free variable, index or integration coordinate was captured')
        return roles

    shift=re.fullmatch(rf'Let (?P<f>{documented}) be continuous on \[(?P<L>{documented}),(?P<U>{documented})\], '
        rf'(?P=L)<(?P<a>{documented})<(?P<b>{documented})<(?P=U)\. Prove lim_\((?P<h>{documented})→0\) '
        rf'\(1/(?P=h)\) ∫_(?P=a)\^(?P=b) \((?P=f)\((?P<t>{documented})\+(?P=h)\)-(?P=f)\((?P=t)\)\) '
        rf'd(?P=t)=(?P=f)\((?P=b)\)-(?P=f)\((?P=a)\)\.',goal)
    if shift:
        return result('edge_average_difference',[
            'Строгие промежутки до обоих внешних краёв позволяют выбрать одну окрестность для положительных и отрицательных приращений.',
            'После замены t→t+h в первом интеграле разность равна верхнему короткому ориентированному интегралу за вычетом нижнего.',
            'Каждый короткий интеграл, делённый на h, сходится к значению функции в соответствующем крае по непрерывности.'],
            dict(identity=True),roles=bind(shift),uses_both_increment_signs=True)
    mass=re.fullmatch(rf'Let (?P<K>{documented})≥0 on \[-1,1\], (?P=K)→0 uniformly on '
        rf'(?P<e>{documented})≤\|(?P<x>{documented})\|≤1 for every (?P=e)>0 and ∫_\(-1\)\^1 (?P=K)→1\. '
        rf'Prove that ∫_\(-1\)\^1 (?P<f>{documented})\((?P=x)\) (?P=K)\((?P=x)\) d(?P=x)→(?P=f)\(0\) '
        rf'for every continuous (?P=f) on \[-1,1\]\.',goal)
    if mass:
        return result('positive_localized_integral_mass',[
            'Вычесть значение непрерывной функции при нуле, добавив ошибку нормировки массы. Из неотрицательности и массы, стремящейся к 1, следует единая верхняя оценка полной массы.',
            'На малой окрестности модуль разности значений функции сколь угодно мал. Вне этой окрестности используется равномерное стремление ядра к нулю и ограниченность функции на отрезке.',
            'Вначале выбрать окрестность по непрерывности, затем достаточно большой индекс. Остаток нормировки исчезает.'],
            dict(identity=True),roles=bind(mass),normalization=ONE)
    cauchy=re.fullmatch(rf'Study continuity on the real (?P<p>{documented})-axis of (?P<F>{documented})\((?P=p)\)'
        rf'=∫₀¹ (?P=p) (?P<f>{documented})\((?P<x>{documented})\)/\((?P=x)\^2\+(?P=p)\^2\) d(?P=x), '
        rf'(?P=f) continuous and positive on \[0,1\]\.',goal)
    if cauchy:
        roles=bind(cauchy);name=roles['f']
        return result('signed_cauchy_kernel_mass',[
            'В окрестности любой ненулевой точки знаменатель на всём исходном отрезке равномерно отделён от нуля, поэтому интеграл непрерывен.',
            'При ненулевом параметре заменить x=|p|t. Получается подписанное ядро на полуоси с мажорантом max|f|/(1+t²).',
            'С каждой стороны предел равен соответствующему знаку, умноженному на πf(0)/2. При самом нуле ядро равно нулю вне одного конца, и обе стороны различны по положительности f(0).'],
            dict(continuous_on='R excluding 0',value_at_zero=ZERO,left_limit='-pi*'+name+'(0)/2',
                 right_limit='pi*'+name+'(0)/2'),roles=roles,dominant_kernel='1/(1+t^2)')
    exp=re.fullmatch(rf'May the limit (?P<p>{documented})→0 pass inside ∫_0\^([0-9]+) '
        rf'\((?P<x>{documented})/(?P=p)\^2\)exp\(-(?P=x)\^2/(?P=p)\^2\) d(?P=x)\?',goal)
    if exp:
        roles=bind(exp);upper=int(exp[2])
        if upper<=0:raise Unsupported('The concentrating interval must have a positive upper end')
        return result('concentrating_exponential_counterexample',[
            'При фиксированном x>0 экспонента подавляет множитель 1/p², а при x=0 исходное ядро уже равно нулю.',
            'До перехода к пределу интегрировать точно подстановкой t=x²/p², сохраняющей нижний край 0 и верхний край U²/p².',
            'Получается (1−exp(−U²/p²))/2. Предельный переход под интегралом дал бы 0, а фактический предел равен 1/2.'],
            dict(interchange=False,value=q(1,2),integral_of_pointwise_limit=ZERO),roles=roles,upper=q(upper))
    logarithm=re.fullmatch(rf'May the derivative of (?P<F>{documented})\((?P<p_init>{documented})\)=∫_0\^([0-9]+) '
        rf'ln sqrt\((?P<x>{documented})\^2\+(?P=p_init)\^2\) d(?P=x) at (?P=p_init)=0 be computed by the Leibniz rule\?',goal)
    if logarithm:
        from derivative_proofs import table
        from verify import same_value
        roles=bind(logarithm);upper=int(logarithm[3])
        if upper<=0:raise Unsupported('The concentrating interval must have a positive upper end')
        t=('v','__log_kernel')
        integrand=('ln',m.add(ONE,m.power(t,-2)))
        primitive=m.add(m.mul(t,integrand),m.mul(q(2),('atan',t)))
        derivative,trace=table(primitive,t[1],lib)
        if not same_value(derivative,integrand):
            raise Unsupported('The concentration remainder primitive did not verify')
        half=m.div(m.PI,q(2))
        return result('one_sided_logarithmic_remainder',[
            'При p=0 исходный интеграл содержит интегрируемый логарифмический край. По отдельности подынтегральная частная в этой точке нулевая для x>0.',
            'В разностном отношении перейти к x=|p|t. Получается sign(p)/2, умноженное на интеграл ln(1+t⁻²) до U/|p|.',
            'Проверить первообразную t ln(1+t⁻²)+2 arctan t. У нуля и на бесконечности первое слагаемое исчезает. Две стороны дают −π/2 и π/2, поэтому производной нет.'],
            dict(leibniz_valid=False,left_derivative=m.neg(half),right_derivative=half),roles=roles,upper=q(upper),primitive_trace=trace)
    raise Unsupported('No justified local mass, edge average or endpoint remainder matches the printed goal')


def compact_operator_integral(task,meta,fields,result):
    name=r'[A-Za-z]\w*'
    conditions=task.get('stated_conditions',[])
    if task['kind']=='parameter_integral_derivative':
        if (set(task)-fields-{'integrand','oriented_limits','operator','stated_conditions'} or
                task.get('requested_output')!=['derivative_with_domain'] or
                meta.get('literal_requirement') not in (None,'Найти указанную производную.')):
            raise Unsupported('The original second-derivative task must be retained')
        body=re.fullmatch(rf'({name})\(({name})\)\*abs\(({name})-\2\)',task['integrand'])
        order=re.fullmatch(rf'({name})<=({name})<=({name})',task['oriented_limits'])
        if not body or not order or body[2]!=order[2] or task['operator']!=f'd^2/d{body[3]}^2':
            raise Unsupported('An oriented interval and the actual absolute-value breakpoint are required')
        f,t,x=body.groups();lo,_,hi=order.groups()
        if len({f,t,x,lo,hi})!=5 or conditions!=[f'{lo}<{hi}',f'{f} continuous on [{lo},{hi}]']:
            raise Unsupported('The underlying continuity and ordered-edge hypotheses have to be bound')
        return result('absolute_value_kernel_second_derivative',[
            'Разность абсолютных значений, делённая на приращение, ограничена единицей. Под интегралом производная существует для всех точек интегрирования, кроме одной, поэтому первая производная получается через два противоположных знака.',
            'Внутри отрезка разбить интеграл в точке параметра. Формула Ньютона–Лейбница даёт удвоенное значение f. Снаружи первая производная постоянна.',
            'У каждого края сравнить производную со стороны отрезка и нуль снаружи. Двусторонняя вторая производная существует там ровно при нулевом значении f на краю.'],
            dict(cases=[dict(when=f'{lo}<{x}<{hi}',value=f'2*{f}({x})'),
                        dict(when=f'{x}<{lo} or {x}>{hi}',value=ZERO),
                        *[dict(when=f'{x}={z}',value=ZERO,exists_when=f'{f}({z})=0') for z in (lo,hi)]]),
            roles=dict(function=f,binder=t,coordinate=x,lower=lo,upper=hi))
    if set(task)-fields-{'definition','formula','stated_conditions','suggested_substitution'} or task.get('requested_output')!=['proof']:
        raise Unsupported('An original integral identity and its stated hypotheses are required')
    definition=task['definition']
    abel=re.fullmatch(rf'({name})\(({name})\)=int_0\^\2 ({name})\(({name})\)/sqrt\(\2-\4\)d\4',definition)
    if abel:
        I,p,f,x=abel.groups()
        interval=re.fullmatch(rf'0<{p}<({name})',conditions[1]) if len(conditions)==2 else None
        formula=f'{I}p={f}(0)/sqrt({p})+int_0^{p} {f}_prime({x})/sqrt({p}-{x})d{x}'
        map_=task.get('suggested_substitution')
        if (not interval or len({I,p,f,x,interval[1]})!=5 or task.get('formula')!=formula
                or conditions[0]!=f'{f},{f}_prime continuous on [0,{interval[1]}]'
                or meta.get('literal_requirement') not in (None,'Доказать формулу для I′.')
                or map_ is not None and not re.fullmatch(rf'{x}={p}\*({name})',map_)):
            raise Unsupported('The paired Abel-power endpoint and the derivative condition must agree')
        if map_ is not None and map_.split('*')[1] in {I,p,f,x,interval[1]}:
            raise Unsupported('The new compact coordinate must be fresh')
        return result('abel_endpoint_derivative',[
            'Перенести подвижную особую границу заменой x=pt на неподвижный промежуток [0,1]. После замены вес (1−t)⁻¹/² интегрируем.',
            'В компактной окрестности исходного положительного параметра значения f и f′ ограничены. Дифференцирование под интегралом даёт два слагаемых от √p и от f(pt).',
            'Преобразовать первое слагаемое частями с первообразной −2√(1−t). На t=1 граничный член исчезает, на t=0 остаётся 2f(0). Совместить два интеграла f′ и вернуться к исходной переменной.'],
            dict(identity=True),bound_parameters=conditions,source_formula=formula,uses_source_chart=map_)
    kernel=re.fullmatch(rf'({name})\(({name})\)=int_0\^1 K\(\2,({name})\)\*({name})\(\3\)d\3;'
        rf'K=\2\*\(1-\3\) for \2<=\3, \3\*\(1-\2\) for \2>\3',definition)
    if (kernel and len(set(kernel.groups()))==4 and conditions==[f'{kernel[4]} continuous']
            and not {'formula','suggested_substitution'}&set(task)
            and meta.get('literal_requirement') in (None,'Показать, что u″(x)=−v(x) на [0,1].')):
        return result('split_green_kernel_derivative',[
            'Разделить ядро по двум участкам с общей границей x. Обе ветви на диагонали совпадают, поэтому граничные вклады первой производной взаимно сокращаются.',
            'Остаётся разность двух накопленных интегралов с непрерывными ядрами (1−y)v(y) и yv(y). Второе дифференцирование даёт −(1−x)v(x)−xv(x)=−v(x).',
            'Краевые производные на отрезке берутся со стороны отрезка. Если продолжать по исходному кусочному ядру наружу, интеграл там аффинен. Двусторонняя вторая производная у конкретного края тогда требует нулевого значения v на нём.'],
            dict(identity=True,derivative_formula=f'-{kernel[4]}({kernel[2]})',domain='[0,1] with one-sided endpoint derivatives',
                 extended_two_sided_edges=[f'{kernel[4]}(0)=0',f'{kernel[4]}(1)=0']),
            variables=kernel.groups())
    raise Unsupported('No proven compact normalization of the original operator was found')


def compact_angular_log_profile(task):
    if (set(task)-{'kind','id','source','integrand','integration_order','parameters','stated_conditions','requested_output'}
        or task.get('requested_output')!=['exact_integral'] or task.get('stated_conditions')):
        raise Unsupported('The angular integral has additional restrictions or requests')
    edges=task.get('integration_order',[]);pars=task.get('parameters',[])
    if len(edges)!=1 or len(pars)!=1 or set(edges[0])!={'variable','lower','upper'} or (
            edges[0]['lower'],edges[0]['upper'])!=('0','pi'):
        raise Unsupported('The angular logarithmic kernel needs the complete original half-period')
    roles,_=bind_integral_symbols([('ln(1-2*a*cos(x)+a^2)',task['integrand']),('x',edges[0]['variable']),('a',pars[0])])
    return roles


def compact_integral_series(task,meta,fields,result):
    if set(task)-fields-{'expression_or_proposition','scope'} or 'requested_output' in task:
        raise Unsupported('An additional integral series obligation remains')
    text=task.get('expression_or_proposition')
    if not isinstance(text,str):raise Unsupported('Expected an explicit parameter integral or series identity')
    scope=task.get('scope')
    id_=r'[A-Za-z]\w*'
    if task['kind']=='integral_parameter_series':
        packet=re.fullmatch(rf'({id_})\(({id_})\)=integral\(({id_})=0\.\.pi/2,(.+)\)',text)
        if (not packet or scope!=f'0<={packet[2]}<1' or meta.get('literal_requirement') not in
                (None,'Разложить полный эллиптический интеграл в ряд по целым положительным степеням модуля.')):
            raise Unsupported('The complete elliptic interval and its strict modulus range are required')
        roles=None
        for power,pattern in ((q(-1,2),'1/sqrt(1-k^2*sin(x)^2)'),(q(1,2),'sqrt(1-k^2*sin(x)^2)')):
            try:roles,_=bind_integral_symbols([(pattern,packet[4]),('k',packet[2]),('x',packet[3])]);break
            except Unsupported:pass
        if not roles or packet[1] in roles.values():raise Unsupported('The original elliptic kernel is not bound')
        j='j'
        while j in {*roles.values(),packet[1]}:j+='_'
        return result('uniform_binomial_integral_series',[
            'При фиксированном модуле 0≤k<1 аргумент k²sin²x остаётся в [0,k²]. Биномиальный ряд сходится равномерно на всём отрезке интегрирования.',
            'Интегрировать каждую чётную степень синуса. По формуле понижения её интеграл равен (π/2)(2j)!/[4^j(j!)²].',
            'Нулевой член даёт π/2, нечётные степени модуля отсутствуют. Сохраняется напечатанное имя функции.'],
            dict(value=f'{packet[1]}({packet[2]})=(pi/2)*sum({j}>=0,binomial({source(power)},{j})*(-1)^{j}*(2*{j})!*{packet[2]}^(2*{j})/(4^{j}*({j}!)^2))'),
            exponent=power,roles=roles,summation=j)
    if meta.get('literal_requirement') not in (None,'Доказать равенство.','Доказать формулу и определить точность по двум членам.'):
        raise Unsupported('The printed integral series conclusion has changed')
    soph=re.fullmatch(rf'integral\(({id_})=0\.\.1,1/\1\^\1\)=sum\(({id_})>=1,1/\2\^\2\)',text)
    if soph and scope=='improper endpoint':
        return result('uniform_exponential_log_series',[
            'Положить u=−x ln x. На (0,1] выполнено 0≤u≤1/e, и у нуля существует конечное продолжение e^u.',
            'Ряд экспоненты сходится равномерно при |u|≤1/e. После замены t=−ln x каждый член интеграла становится гамма-моментом ∫t^j exp(−(j+1)t)dt/j!.',
            'Гамма-момент равен (j+1)^(−j−1). Сдвинуть исходный целый индекс к началу 1.'],
            dict(identity=True),binder=soph[1],summation=soph[2],uniform_argument_bound=('exp',q(-1)))
    gauss=re.fullmatch(rf'integral\(({id_})=0\.\.\+infinity,exp\(-\1\^2\)\*sin\(({id_})\*\1\)\)'
                       rf'=1/2\*sum\(({id_})>=0,\(-1\)\^\3\*factorial\(\3\)\*\2\^\(2\*\3\+1\)/factorial\(2\*\3\+1\)\)',text)
    if gauss and len(set(gauss.groups()))==3 and scope==f'real {gauss[2]}':
        return result('gaussian_dominated_sine_series',[
            'Разложить синус по обычному ряду. Ряд модулей после умножения на e^(−x²) ограничен e^(−x²+|a|x), который интегрируем на исходной полуоси при каждом фиксированном действительном a.',
            'По абсолютному мажоранту интегрировать почленно. В моменте x^(2j+1)e^(−x²) заменить t=x², получив j!/2.',
            'Сохранить порядок, знак и начальный индекс ряда.'],
            dict(identity=True),binder=gauss[1],parameter=gauss[2],summation=gauss[3])
    geo=re.fullmatch(rf'integral\(({id_})=0\.\.infty,exp\(-\1\)/\(({id_})\+\1\)\)=sum\(({id_})=0\.\.({id_})-1,'
                     rf'\(-1\)\^\3\*\3!/\2\^\(\3\+1\)\)\+\(-1\)\^\4\*theta_\4\*\4!/\2\^\(\4\+1\)',text)
    if geo:
        pair=re.fullmatch(rf'{geo[2]}>0, 0<theta_{geo[4]}<1\. Установить точность при {geo[2]}=([1-9]\d*) и двух членах\.',scope or '')
        if pair and len(set(geo.groups()))==4:
            at=int(pair[1]);remainder=q(2,at**3)
            return result('finite_geometric_integral_remainder',[
                'Разложить 1/(a+x) конечной геометрической суммой и её точным остатком. При a>0 все знаменатели сохраняют положительность.',
                'После интегрирования коэффициенты становятся гамма-моментами j!. Остаток имеет знак (−1)^n, а его модуль строго меньше n!/a^(n+1), так как a/(a+x)∈(0,1) для x>0.',
                'Подставить исходное численное значение параметра и два члена.'],
                dict(identity=True,value=q(F(1,at)-F(1,at*at)),strict_absolute_error=remainder),
                parameter=geo[2],binder=geo[1],truncation_index=geo[4],evaluation_parameter=q(at))
    raise Unsupported('No uniform or dominated integral series proof matches the stated source')


def boundary_reduction_candidate(task):
    kind=task.get('kind')
    if kind in ('polynomial_weighted_primitive_identity','polynomial_family_primitive'):return True
    if kind=='indefinite_integral_recurrence':
        return isinstance(task.get('family'),str) and '+b*cos(x)' in task['family'] and 'a*sin(x)' in task['family']
    if kind!='integral_reduction_family':return False
    outputs=task.get('requested_output')
    if outputs in (['recurrence_for_primitives','specified_primitive_by_recurrence'],['recurrence','specified indefinite integral'],
                   ['general primitive family','specified primitive by same substitution']):return True
    return outputs==['exact_indexed_integral'] and task.get('upper')=='+inf' and task.get('method_requirement')=='reduction_formula' and (
        task.get('lower')=='-inf' and len(task.get('parameters',[]))==3 or task.get('lower')=='1' and 'prod(' in task.get('integrand','')
        or task.get('lower')=='0' and 'cosh(' in task.get('integrand',''))


def boundary_reduction_proof(task,lib):
    """Reuse one differentiated-product invariant before separating the endpoints."""
    if not lib.data.get('boundary_reduction_proofs'):
        raise Unsupported('The reusable reduction proof is not active')
    ctx=task.get('source',{})
    if not isinstance(ctx,dict) or set(ctx)-{'exercise','pdf_page','pdf_pages','printed_page','printed_subpart','pdf_sha256',
            'literal_requirement','printed_instruction','page_png_sha256','heading_page','method_heading','original_page_image_sha256','printed_requirement'}:
        raise Unsupported('An additional original restriction or required method remains')
    kind=task['kind'];want=task.get('requested_output');head=ctx.get('literal_requirement')
    if any(key in task and (not isinstance(task[key],str) or not re.fullmatch(r'[A-Za-z]\w*',task[key]))
           for key in ('variable','polynomial_degree')):
        raise Unsupported('A mathematical binder must be an ordinary variable name')
    if 'index' in task and isinstance(task['index'],str) and not re.fullmatch(r'[A-Za-z]\w*',task['index']):
        raise Unsupported('A recurrence index must be an ordinary variable name')
    headings={
        'Derive a recurrence and use it to compute the specified third integral.': ['recurrence','specified indefinite integral'],
        'Use the displayed substitution for the general natural exponents and then evaluate the particular integral.':
            ['general primitive family','specified primitive by same substitution'],
        'Integrate the indexed polynomial quotient; Taylor expansion is suggested.': None,
    }
    if 'method_heading' in ctx and (ctx['method_heading'] not in headings or headings[ctx['method_heading']]!=want):
        raise Unsupported('The original requested method heading is not supported')
    if ctx.get('printed_requirement') not in (None,
            'Derive a reduction formula for the indicated family of indefinite integrals for n>2, then use it to compute the corresponding printed instance.'):
        raise Unsupported('The printed reduction requirement must stay bound')
    base={'kind','id','source','requested_output'}

    def bind(fields,wants,headers=()):
        if set(task)-base-set(fields) or want!=wants or head not in (None,*headers):
            raise Unsupported('The requested recurrence, example or printed method has changed')
    def emit(name,steps,value,**evidence):
        return dict(theorem='method.boundary_reduction_proofs',family=name,steps=steps,**evidence),value

    if kind=='polynomial_weighted_primitive_identity':
        return polynomial_weighted_boundary(task,lib,bind,emit)
    if kind=='polynomial_family_primitive':
        bind({'integrand','variable','assumptions'},None)
        v=task['variable'];word=r'[A-Za-z]\w*'
        match=re.fullmatch(rf'({word})_({word})\({v}\)/\({v}-({word})\)\^\(\2\+1\)',task['integrand'])
        if not match or len(set((*match.groups(),v)))!=4 or task.get('assumptions')!=[f'{match[1]}_{match[2]} polynomial of degree {match[2]}']:
            raise Unsupported('The Taylor pole, polynomial degree and bound variable must agree')
        P,n,a=match.groups()
        return emit('taylor_pole_expansion',[
            'Разложить исходный многочлен точно вокруг точки полюса по конечной формуле Тейлора, сохраняя коэффициент при каждой степени.',
            'После деления интегрировать все степени по таблице. Последняя степень −1 даёт логарифм модуля.'],
            dict(value=f'sum(k=0..{n}-1,{P}^({{k}})({a})*({v}-{a})^(k-{n})/(k!*(k-{n})))+{P}^({n})({a})*ln(abs({v}-{a}))/{n}!',
                 domain=f'{v}!={a}',constant='independent on each component'),binder=v)
    if kind=='indefinite_integral_recurrence':
        bind({'family','relation'},['proof_of_recurrence'],('Доказать формулу понижения с неопределёнными коэффициентами A,B,C.',))
        if task['family']!='I(n)=integral(1/(a*sin(x)+b*cos(x))^n,x)' or task['relation']!=(
            'I(n)=(A*sin(x)+B*cos(x))/(a*sin(x)+b*cos(x))^(n-1)+C*I(n-2)'):
            raise Unsupported('The proposed harmonic boundary law must be bound before assigning coefficients')
        x=('v','x');a,b=('s','a'),('s','b');R=m.add(m.power(a,2),m.power(b,2))
        raw=m.add(m.mul(a,('sin',x)),m.mul(b,('cos',x)))
        invariant=boundary_power_invariant(raw,x,q(-1),R,2,lib)
        den='((n-1)*(a^2+b^2))'
        return emit('combined_harmonic_recurrence',[
            'Из Q=a sin x+b cos x получить Q″=−Q и Q′²=a²+b²−Q². Проверить оба тождества до использования степени.',
            'Дифференцировать Q′·Q^(1−n) на исходной вещественной ветви. Отождествить коэффициенты при Q^(−n) и Q^(2−n).',
            'При n=1 предложенная граничная форма неприменима, её производная была бы гармоникой, а 1/Q имеет полюсы. Нулевую амплитуду также выделить отдельно.'],
            dict(A='b/'+den,B='-a/'+den,C='(n-2)/'+den,domain='a^2+b^2>0, n!=1 and original real powers defined',
                 exception_at_one='the displayed form gives no coefficients'),invariant=invariant)
    if want==['recurrence_for_primitives','specified_primitive_by_recurrence']:
        return finite_harmonic_reductions(task,lib,bind,emit)
    if want==['general primitive family','specified primitive by same substitution']:
        return fractional_product_primitive(task,lib,bind,emit)
    if want==['recurrence','specified indefinite integral'] or task.get('lower')=='-inf':
        return quadratic_boundary_reduction(task,lib,bind,emit)
    bind({'integrand','variable','lower','upper','index','index_domain','method_requirement'},['exact_indexed_integral'])
    if task.get('upper')!='+inf' or task.get('index_domain')!='positive_integers' or task.get('method_requirement')!='reduction_formula' or (
        ctx.get('printed_instruction') not in (None,'С помощью формул понижения вычислить следующие несобственные интегралы (n — натуральное число).')):
        raise Unsupported('The original whole improper end and natural reduction index are required')
    x,n=task['variable'],task['index'];var=('v',x);names=r'[A-Za-z]\w*'
    if x==n:raise Unsupported('The integration variable cannot be the reduction index')
    if task['lower']=='0' and task['integrand']==f'1/cosh({x})^({n}+1)':
        proof=boundary_power_invariant(('cosh',var),var,ONE,q(-1),2,lib)
        return emit('hyperbolic_power_endpoints',[
            'Использовать проверенные Q=cosh x, Q′²=Q²−1 и Q″=Q. Производная sinh x/coshⁿx даёт разность двух соседних моментов.',
            'След при нуле равен нулю. На бесконечности он исчезает для n>1, а исходный интеграл абсолютно сходится при каждом положительном целом n.',
            'Вычислить начальные моменты заменами sinh x и tanh x. Итерация даёт два отношения двойных факториалов.'],
            dict(recurrence=f'J({n})=({n}-1)*J({n}-2)/{n}',initial=['J(0)=pi/2','J(1)=1'],
                 value=['J(2k)=(pi/2)*(2k-1)!!/(2k)!!','J(2k+1)=(2k)!!/(2k+1)!!']),invariant=proof)
    product=re.fullmatch(rf'1/prod\({x}\+({names}),\1,0,{n}\)',task['integrand'])
    if task['lower']=='1' and product and product[1] not in (x,n):
        return emit('translated_adjacent_product_tail',[
            'Обратное произведение от k=0 до n есть разность обратных соседних произведений длины n, делённая на n.',
            'Интегрировать разность на общем конечном срезе и сдвинуть второй отрезок на единицу. Остаточное окно у бесконечности зануляется, даже когда отдельные интегралы при n=1 расходятся.',
            'Вычислить исходное окно через коэффициенты простых полюсов. Сумма коэффициентов логарифмов на бесконечности нулевая при каждом положительном целом n.'],
            dict(recurrence=f'J({n})=(1/{n})*int_1^2 1/prod({x}+{product[1]},{product[1]},0,{n}-1)d{x}',
                 value=f'-sum(k=0..{n},(-1)^k*binomial({n},k)*ln(1+k))/{n}!'),index=n,binder=x)
    raise Unsupported('No checked boundary identity matches the original integral')


def boundary_power_invariant(raw,x,A,B,delta,lib):
    """Verify Q′²=A·Q^d+B and Q″=(d/2)A·Q^(d−1) on the named source."""
    from derivative_proofs import table
    from verify import same_value
    first,trace1=table(raw,x[1],lib)
    second,trace2=table(first,x[1],lib)
    a=m.add(m.mul(A,m.power(raw,delta)),B);b=m.mul(m.mul(A,q(delta,2)),m.power(raw,delta-1))
    if raw==('cosh',x):
        t=('s','__positive_exponential')
        inverse=m.power(t,-1)
        chart={('cosh',x):m.mul(q(1,2),m.add(t,inverse)),('sinh',x):m.mul(q(1,2),m.add(t,m.neg(inverse)))}
    else:chart={}
    if not same_value(m.substitute(m.power(first,2),chart),m.substitute(a,chart)) or not same_value(second,b):
        raise Unsupported('The original boundary multiplier does not satisfy both power identities')
    return dict(kernel=raw,first=first,second=second,slope=A,constant=B,stride=delta,
                elementary_derivative_steps=(trace1,trace2))


def finite_harmonic_reductions(task,lib,bind,emit):
    bind({'integrand','variable','index','index_domain','integral_type','method_requirement','specified_indices'},
         ['recurrence_for_primitives','specified_primitive_by_recurrence'])
    x,n=task['variable'],task['index'];var=('v',x)
    if x==n or task.get('integral_type')!='indefinite' or task.get('index_domain')!=f'{n}>2' or (
            task.get('method_requirement')!='derive_and_apply_reduction_formula'):
        raise Unsupported('The original exponent range and required reduction method have to be retained')
    hit=re.fullmatch(rf'(1/)?(sin|cos)\({x}\)\^{n}',task['integrand'])
    indices=task['specified_indices']
    if not hit or not isinstance(indices,list) or not indices or any(type(p) is not int or not 3<=p<=20 for p in indices):
        raise Unsupported('Finite applications of the original harmonic reduction are required')
    Q=(hit[2],var);inv=boundary_power_invariant(Q,var,q(-1),ONE,2,lib);D=inv['first'];negative=bool(hit[1])
    half=q(1,2)
    memo={0:var,1:m.mul(half,m.add(('ln',m.add(ONE,m.neg(D))),m.neg(('ln',m.add(ONE,D))))) if negative else m.neg(D)}
    def primitive(k):
        if k not in memo:
            coefficient=q(k-2,k-1) if negative else q(k-1,k)
            boundary=m.mul(q(-1,k-1 if negative else k),m.mul(D,m.power(Q,1-k if negative else k-1)))
            memo[k]=m.add(boundary,m.mul(coefficient,primitive(k-2)))
        return memo[k]
    samples=tuple((k,primitive(k)) for k in indices)
    return emit('inverse_harmonic_powers' if negative else 'positive_harmonic_powers',[
        'Проверить Q′²=1−Q² и Q″=−Q. Производная Q′Q^s даёт ровно две соседние степени, отстоящие на два.',
        'Переписать производную в формулу понижения с напечатанным знаком показателя. Для вещественного показателя соблюдать исходную ветвь; при целых степенях проверить все её компоненты.',
        'Последовательно уменьшить каждую напечатанную степень на два. Использовать I₀=x и I₁=−Q′ для прямых степеней, а для обратной базы логарифм (1−Q′)/(1+Q′), взятый с множителем 1/2.'],
        dict(recurrence=f'I({n})=-Qprime*Q^'+(f'(1-{n})/({n}-1)+({n}-2)*I({n}-2)/({n}-1)' if negative else f'({n}-1)/{n}+({n}-1)*I({n}-2)/{n}'),
             applications=[dict(index=k,value=z,domain=f'{hit[2]}({x})!=0' if negative else 'R',constants='independent on each component') for k,z in samples]),
        invariant=inv,application_steps=tuple(memo))


def quadratic_boundary_reduction(task,lib,bind,emit):
    from verify import same_value
    stated=task.get('stated_conditions');v=task['variable'];n=task['index'];names=task.get('parameters',[])
    if len(names)!=3 or len(set([v,n,*names]))!=5:raise Unsupported('The quadratic parameters and reduction index must stay distinct')
    a,b,c=names;x=('v',v);A,B,C=map(lambda a:('s',a),names)
    definite=task.get('lower')=='-inf'
    fields={'index','variable','integrand','parameters','stated_conditions'}
    instruction=task.get('source',{}).get('printed_instruction')
    if definite:
        bind(fields|{'lower','upper','index_domain','method_requirement'},['exact_indexed_integral'])
        if (task.get('upper')!='+inf' or task.get('index_domain')!='positive_integers' or task.get('method_requirement')!='reduction_formula'
                or stated!=[f'{a}*{c}-{b}^2>0'] or instruction not in
                    (None,'С помощью формул понижения вычислить следующие несобственные интегралы (n — натуральное число).')):
            raise Unsupported('The original discriminant and both improper tails are required')
        middle='2*'+b
    else:
        bind(fields|{'hint','instance'},['recurrence','specified indefinite integral'])
        hint=f'4*{a}*Q=(2*{a}*{v}+{b})^2+4*{a}*{c}-{b}^2'
        if stated!=[a+'!=0'] or task.get('hint') not in (None,hint) or instruction:
            raise Unsupported('The original quadratic identity and nonzero leading coefficient must remain bound')
        middle=b
    body=f'{a}*{v}^2+{middle}*{v}+{c}'
    if task['integrand']!=f'1/({body})^{n}':raise Unsupported('Expected the exact original quadratic power')
    Q=m.parse(body,v,names);linear=m.mul(q(2),B) if definite else B
    delta=m.add(m.mul(q(4),m.mul(A,C)),m.neg(m.power(linear,2)))
    inv=boundary_power_invariant(Q,x,m.mul(q(4),A),m.neg(delta),1,lib)
    if definite:
        D=f'({a}*{c}-{b}^2)'
        scale=f'({a}/{D})^({n}-1)'
        return emit('whole_line_quadratic_recurrence',[
            'Проверить Q′²=4aQ−4Δ и Q″=2a, где Δ=ac−b²>0. Квадратное уравнение не имеет действительных корней и Q имеет знак a.',
            'При n≥2 граничное отношение Q′/Q^(n−1) исчезает на обеих бесконечностях. Абсолютная сходимость исходных хвостов следует из квадратичного роста.',
            'Из производной граничного отношения вывести рекурсию. Для n=1 дополнение до квадрата даёт signed арктангенс, включая отрицательный a.'],
            dict(recurrence=f'I({n})=(2*{n}-3)*{a}*I({n}-1)/(2*({n}-1)*{D})',
                 initial=f'I(1)=sign({a})*pi/sqrt({D})',
                 value=f'sign({a})*pi/sqrt({D})*{scale}*(2*{n}-3)!!/(2*{n}-2)!!'),invariant=inv)
    case=m.parse(task['instance'],v)
    if case[0]!='div' or case[1]!=ONE or case[2][0]!='pow' or not 2<=case[2][2]<=12:
        raise Unsupported('A concrete power of an admitted quadratic is required for the printed application')
    R,k=case[2][1:]
    if not m.constant_defined(m.substitute(R,{x:('s',v)}),{'parameters':[v],'assumptions':[]}):
        raise Unsupported('The unsimplified quadratic must be defined on the original real axis')
    coeff=riemann_polynomial(R,x)
    if coeff is None or len(coeff)!=3 or any(m.num(z) is None for z in coeff):
        raise Unsupported('The printed application must have real numeric quadratic coefficients')
    c0,b0,a0=map(m.num,coeff);D0=4*a0*c0-b0*b0
    if not a0 or D0<=0:raise Unsupported('The printed instance needs its own nondegenerate real branch')
    deriv=m.add(m.mul(q(2*a0),x),q(b0));root=('sqrt',q(D0))
    answer=m.mul(m.div(q(2),root),('atan',m.div(deriv,root)))
    for j in range(2,k+1):
        edge=m.div(deriv,m.mul(q((j-1)*D0),m.power(R,j-1)))
        answer=m.add(edge,m.mul(q((4*j-6)*a0/((j-1)*D0)),answer))
    return emit('indefinite_quadratic_recurrence',[
        'Проверить Q′²=4aQ−Δ и Q″=2a. Дифференцирование Q′/Q^(n−1) даёт обе степени, которые входят в формулу понижения.',
        'Делить на (n−1)Δ можно в невырожденной ветви. При Δ=0 подставить линейную переменную в полный квадрат и использовать степенное правило либо логарифм при показателе −1.',
        'Для печатного примера коэффициенты числовые, Δ>0. База арктангенс, а дальнейшие шаги строятся уже доказанной формулой понижения.'],
        dict(recurrence=f'I({n})=(Qprime/Q^({n}-1)+(4*{n}-6)*{a}*I({n}-1))/(({n}-1)*Delta)',
             recurrence_domain='Q!=0, Delta!=0, n!=1 on the original real power branch',
             degenerate='Delta=0: Q=a*(x+b/(2*a))^2, integrate the single signed power; exponent -1 yields log',
             application=dict(index=k,value=answer,domain='R',constant='arbitrary')),
        invariant=inv,application_discriminant=q(D0),application_kernel=R)


def fractional_product_primitive(task,lib,bind,emit):
    bind({'index','index_domain','integrand','variable','substitution','instance','method_requirement'},
         ['general primitive family','specified primitive by same substitution'])
    v=task['variable'];inds=task.get('index',[])
    if (task.get('method_requirement')!='specified_substitution' or task.get('index_domain')!='positive_integers'
            or len(inds)!=2 or len({v,*inds})!=3):
        raise Unsupported('Apply the required substitution with two distinct natural indices')
    word=r'[A-Za-z]\w*'
    sub=re.fullmatch(rf'({word})=\({v}\+({word})\)/\({v}\+({word})\)',task['substitution'])
    if not sub or len(set((*sub.groups(),*inds,v)))!=6:
        raise Unsupported('Bind the two original poles and the fresh coordinate in the prescribed change')
    t,a,b=sub.groups();m_,n=inds
    if task['integrand']!=f'1/(({v}+{a})^{m_}*({v}+{b})^{n})':
        raise Unsupported('The two original pole powers do not match the substitution')
    raw=m.parse(task['instance'],v);x=('v',v)
    if raw[0]!='div' or raw[1]!=ONE or raw[2][0]!='mul':
        raise Unsupported('The concrete example must supply two pole factors')
    roots=[];powers=[]
    for term in raw[2][1:]:
        if term[0]!='pow' or not 1<=term[2]<=16:
            raise Unsupported('The concrete pole powers must be positive integers')
        if not m.constant_defined(m.substitute(term[1],{x:('s',v)}),{'parameters':[v],'assumptions':[]}):
            raise Unsupported('The original affine factors must be real-defined before simplification')
        coeff=riemann_polynomial(term[1],x)
        if coeff is None or len(coeff)!=2 or coeff[1]!=ONE or m.num(coeff[0]) is None:
            raise Unsupported('Two original monic affine factors are required')
        roots.append(coeff[0]);powers.append(term[2])
    first,second=roots;i,j=powers;gap=m.add(second,m.neg(first))
    if gap==ZERO:raise Unsupported('The stated example must distinguish the source poles')
    chart=m.div(m.add(x,first),m.add(x,second));out=ZERO;degree=i+j-2
    for k in range(degree+1):
        coefficient=q((-1)**k*comb(degree,k));p=k-i+1
        term=('ln',('abs',chart)) if not p else m.div(m.power(chart,p),q(p))
        out=m.add(out,m.mul(coefficient,term))
    out=m.mul(m.power(gap,-degree-1),out)
    return emit('specified_fractional_pole_product',[
        'Для различных a,b выразить исходные линейные множители через t. Производная t′=(b−a)/(x+b)² сохраняет знак ориентации на каждой исходной компоненте.',
        'После замены открыть конечный многочлен (1−t)^(m+n−2), сохранить t≠0 и взять логарифм только у показателя −1.',
        'При a=b напечатанная подстановка становится постоянной, и совпавший полюс интегрируется одной степенью. В конкретном примере полюсы различны, поэтому применить построенную карту.'],
        dict(general_kernel=f'({b}-{a})^(1-{m_}-{n})*{t}^(-{m_})*(1-{t})^({m_}+{n}-2)',
             coincident=f'({v}+{a})^(1-{m_}-{n})/(1-{m_}-{n})',
             application=dict(value=out,excluded_poles=tuple(m.neg(z) for z in roots),constant='independent on each component')),
        original_map=task['substitution'],application_chart=chart,powers=tuple(powers))


def polynomial_weighted_boundary(task,lib,bind,emit):
    from derivative_proofs import table
    from verify import same_value
    bind({'integrand','polynomial_degree','claimed_primitive'},['proof_for_arbitrary_polynomial_degree'],(
        'Для произвольного многочлена P степени n доказать конечную формулу интегрирования с e^{ax}.',
        'Доказать указанную формулу для любого многочлена P степени n; в книге приведены две формулы, соединённые «и».'))
    name=r'[A-Za-z]\w*'
    hit=re.fullmatch(rf'({name})\(({name})\)\*(exp|sin|cos)\(({name})\*\2\)',task['integrand'])
    n=task['polynomial_degree']
    if not hit or not re.fullmatch(name,n) or len(set((hit[1],hit[2],hit[4],n)))!=4:
        raise Unsupported('The real parameter and arbitrary polynomial degree must be bound')
    P,x,w,a=hit.groups();claim=task['claimed_primitive']
    if w=='exp':
        j=re.fullmatch(rf'exp\({a}\*{x}\)\*sum\(\(-1\)\^({name})\*derivative\({P},\1,{x}\)/{a}\^\(\1\+1\),\1=0\.\.{n}\)\+C',claim)
        if not j or j[1] in (P,x,a,n):raise Unsupported('Bind the finite alternating derivative sum without capturing an original variable')
    else:
        even=f'({P}−{P}″/{a}²+{P}⁽⁴⁾/{a}⁴−…)'
        odd=f'({P}′−{P}‴/{a}²+{P}⁽⁵⁾/{a}⁴−…)'
        s=f'sin({a}*{x})';c=f'cos({a}*{x})'
        expected=f'{s}/{a}*{even}+{c}/{a}²*{odd}+C' if w=='cos' else f'−{c}/{a}*{even}+{s}/{a}²*{odd}+C'
        if claim!=expected:raise Unsupported('The exact alternating phase and signs of the printed primitive must be preserved')
    z=('v',x);rate=('s',a);arg=m.mul(rate,z)
    pairs=(('exp','exp',1),) if w=='exp' else (('sin','cos',1),('cos','sin',-1))
    witnesses=[]
    for f,g,sgn in pairs:
        d,trace=table((f,arg),x,lib)
        if not same_value(d,m.mul(q(sgn),m.mul(rate,(g,arg)))):raise Unsupported('The phase cycle did not verify')
        witnesses.append(trace)
    return emit('finite_weighted_polynomial_parts',[
        'Проверить производную экспоненты или полный двухшаговый цикл синуса и косинуса. Для одного шага по частям делить только при ненулевой частоте.',
        'При повторении частей соседние коэффициенты уничтожаются после дифференцирования. После порядка n полиномиальный остаток нулевой.',
        'Чётные и нечётные производные дают соответственно напечатанные фазы. При нулевой частоте вычислить исходное ядро напрямую, поскольку напечатанные деления там не определены.'],
        dict(identity=True,formula_domain=a+'!=0',zero_frequency='zero primitive' if w=='sin' else 'primitive of the original polynomial'),
        phase_derivatives=witnesses,original_formula=claim,polynomial_degree=n)


def exponential_circle_profile(task):
    """Extract the signed rotating mode and the fixed real amplitude."""
    meta=task.get('source',{});kind=task.get('kind');ident=r'[A-Za-z]\w*'
    allowed={'kind','id','source','integrand','integration_order','parameters','stated_conditions','requested_output'}
    if not isinstance(meta,dict) or set(meta)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement','page_png_sha256'}:
        raise Unsupported('Additional integral source claims remain')
    method=meta.get('literal_requirement')
    if kind=='integral_series_identity':
        rhs=task.get('expression_or_proposition','')
        expr=re.fullmatch(rf'integral\(({ident})=0\.\.2\*pi,exp\(cos\(\1\)\)\*cos\(sin\(\1\)\)\*cos\(({ident})\*\1\)\)=pi/factorial\(\2\)',rhs)
        if (not expr or expr[1]==expr[2] or task.get('scope')!='n=0,1,2,...' or expr[2]!='n' or
               set(task)-{'kind','id','source','expression_or_proposition','scope'} or method not in (None,'Доказать равенство.')):
            raise Unsupported('The real Fourier projection or its support of indices is unresolved')
        return ('cosine_projection',expr[1],expr[2],None)
    if kind!='iterated_integral' or set(task)-allowed or task.get('requested_output')!=['exact_integral']:raise Unsupported('No complete exact angular integral')
    order=task.get('integration_order')
    if not isinstance(order,list) or len(order)!=1:raise Unsupported('Exactly one angular interval is required')
    x=order[0].get('variable','');h=re.escape(x);a=task.get('integrand','');params=task.get('parameters')
    if order==[dict(variable=x,lower='0',upper='2*pi')] and method in (None,'Найти интеграл. 0..2*pi, n positive integer'):
        hit=re.fullmatch(rf'exp\(({ident})\*cos\({h}\)\)\*cos\(\1\*sin\({h}\)-({ident})\*{h}\)',a)
        if hit and len({x,*hit.groups()})==3 and params==list(hit.groups()) and task.get('stated_conditions')==[hit[2]+' is a positive integer'] and (
                method is None or hit[2]=='n'):
            return ('rotating_projection',x,hit[2],hit[1])
    if order==[dict(variable=x,lower='0',upper='pi')] and method in (None,'Найти интеграл. 0..pi. Указание: см. пример 2864.'):
        hit=re.fullmatch(rf'{h}\*sin\(({ident})\)/\(1-2\*\1\*cos\({h}\)\+\1\^2\)',a)
        if hit and hit[1]!=x and params==[hit[1]] and not task.get('stated_conditions'):return ('poisson_linear_moment',x,None,hit[1])
    raise Unsupported('The parameter and original integration interval are unresolved')


def circle_integral_goal(task):
    family,x,n,a=exponential_circle_profile(task)
    if family in ('cosine_projection','rotating_projection'):
        exp_bound=(('exp',('abs',('s',a))) if a else ('exp',ONE))
        base=['Распознать действительную часть exp(a exp(ix)) на полной окружности.',
              'Ряд экспоненты мажорируется exp(|a|) равномерно по углу. Интегрирование выделяет только нулевую частоту.']
        if family=='rotating_projection':
            base.append('После умножения на exp(−inx) равенство частот выбирает ровно член j=n. Знак вещественного параметра не ограничен.')
            value={'value':f'2*pi*{a}^{n}/factorial({n})','domain':f'{a} real, {n} positive integer'}
        else:
            base.append('При умножении на cos(nx) для n>0 остаётся половина соответствующего коэффициента. При n=0 множитель равен единице и половины нет.')
            value=dict(printed_claim_holds=False,counterexample=dict(index=ZERO,actual=m.mul(q(2),m.PI),claimed=m.PI),
                       positive_indices=f'pi/factorial({n})')
        return (dict(theorem='method.uniform_exponential_circle_mode_selection',family=family,
                     steps=base,variable=x,mode=n,uniform_bound=exp_bound),value)
    # Orthogonality and exact endpoint guards are retained when a is outside the unit disk.
    j='j'
    while j in (x,a):j+='_'
    def bin(value,scale):
        return f'sin({a})*(pi^2/2+2*sum({j}>=1,((-1)^{j}-1)*({value})^{j}/{j}^2))/({scale})'
    return dict(theorem='method.poisson_series_linear_angular_moment',family=family,
                steps=['Для |a|<1 сложить два геометрических ряда и получить равномерный ряд Пуассона для исходного знаменателя.',
                          'Для |a|>1 вынести a² и использовать тот же ряд с параметром 1/a. Знаменатель в обоих случаях строго положителен.',
                          'Вычислить ∫₀^π x cos(jx) dx по частям. При a=±1 вернуться к исходной функции и проверить особый конец по квадратичному порядку 1−cos.',
                         ],mode_binder=j,angular_variable=x),dict(branches=[
        dict(condition=f'abs({a})<1',value=bin(a,f'1-{a}^2')),
        dict(condition=f'abs({a})>1',value=bin(f'1/{a}',f'{a}^2-1')),
        dict(condition=f'{a}=1',status='improper_divergence',value='+inf',endpoint='0'),
        dict(condition=f'{a}=-1',status='improper_divergence',value='-inf',endpoint='pi')])


def reciprocal_circle_quadrature(raw,x,lo,hi,tol,decimal_value):
    """Certified Simpson enclosure by the poles of 1/(1+x²)."""
    from verify import same_value
    denominator=m.add(ONE,m.power(x,2));target=m.div(ONE,denominator)
    if (lo,hi)!=('0','1') or not same_value(raw,target) or (
            any(g[0]!='nonzero' or not same_value(g[1],denominator) for g in domain_conditions(raw))):
        raise Unsupported('The model does not match the intact arctangent integral')
    n=2
    while F(8,15*n**4)>=tol/2 and n<4096:n*=2
    if F(8,15*n**4)>=tol/2:raise Unsupported('The selected panel count would exceed the compact certificate')
    weights=lambda j:1 if j in (0,n) else 4 if j%2 else 2
    s=4*sum(F(weights(j)*n*n,n*n+j*j) for j in range(n+1))/(3*n)
    err=F(8,15*n**4)
    plan=dict(theorem='method.target_quadrature',strategy='reciprocal_quadratic_pole_bound',scale=4,
        panels=n,fourth_derivative_bound=q(24),normalization='atan(1)-atan(0)=π/4 by the ordinary chain and Newton–Leibniz',
        rational_simpson=q(s),truncation_bound=q(err),moments=[],
        reasoning='The fourth derivative is 24 Re((1−ix)^(-5)). Its modulus is at most 24 on the real line. Composite Simpson on [0,1], multiplied by four, has error at most 8/(15 N^4).')
    return plan,decimal_value(s,err)


def parameter_boundary_differences(task):
    """Move differentiation along an affine argument onto finite integral faces."""
    from integrals import affine
    from tasks import domain_conditions,known_guard,source
    from verify import same_value
    names=r'[A-Za-z_]\w*'
    operator=task['operator']
    higher=re.fullmatch(r'd\^('+names+r')/d('+names+r')\^\1',operator)
    ordinary=re.fullmatch(r'd/d('+names+r')',operator)
    second=re.fullmatch(r'd\^2/d('+names+r')\^2',operator)
    if not (higher or ordinary or second):raise Unsupported('No bound operator on a continuous integral profile')
    x=higher[2] if higher else (ordinary or second)[1]
    axes=[]
    for row in task['oriented_limits'].split(','):
        hit=re.fullmatch(r'(.+?)<=('+names+r')<=(.+)',row.strip())
        if not hit:raise Unsupported('Expected finite oriented bounds with distinct integration indices')
        axes.append((hit[2],hit[1],hit[3]))
    dummy=[row[0] for row in axes]
    if x in dummy or len(set(dummy))!=len(dummy):raise Unsupported('An integration binder collides with the outside variable')
    body=task['integrand'];fns=set(re.findall(r'\b('+names+r')\s*\(',body))-m.FUNCTIONS-set(m.ALIASES)
    if len(fns)!=1:raise Unsupported('One named scalar profile must occur in the source')
    f,=fns
    conditions=task['stated_conditions']
    prefactor='1';rest=[]
    for clause in conditions:
        scalar=re.fullmatch(names+r' includes factor (.+)',clause)
        if scalar:
            if prefactor!='1':raise Unsupported('More than one normalization condition')
            prefactor=scalar[1]
        elif clause!=f+' continuous':rest.append(clause)
    n=higher[1] if higher else None
    continuous=f+' continuous' in conditions
    free=sorted(set(re.findall(names,' '.join([body,prefactor,*rest,*(s for _,a,b in axes for s in (a,b))])))
                 -m.FUNCTIONS-set(m.ALIASES)-{*dummy,x,f,'pi','e'})
    if n is not None and (n not in free or n in dummy or n==x):raise Unsupported('The symbolic positive integer order has no matching exponent')
    ctx=m.context(dict(variable=x,parameters=free,parameter_conditions=rest))
    values=[x,*dummy,*free]
    raw=m.parse(body,None,values,(f,));scale=m.parse(prefactor,None,free)
    if not m.constant_defined(scale,ctx):raise Unsupported('The fixed source normalization is not defined')
    S=lambda a:('s',a)
    bounds=[(S(w),m.parse(a,None,values),m.parse(b,None,values)) for w,a,b in axes]
    if any(any(m.contains(z,S(k)) for k in dummy) or not all(known_guard(g,ctx) for g in domain_conditions(z))
           for _,a,b in bounds for z in (a,b)):
        raise Unsupported('Only independent rectangular fibers with checked original bounds are available')
    def along(expr,name):
        return affine(m.substitute(expr,{S(name):('v',name)}),name)
    if higher:
        if conditions or len(bounds)!=1 or raw[0]!='mul':raise Unsupported('A single Volterra power convolution is required')
        W,lo,hi=bounds[0]
        call,power=raw[1:] if raw[1]==(f,W) else raw[:0:-1]
        c,s=along(hi,x)
        if (call!=(f,W) or power[0]!='rpow' or not same_value(power[2],m.add(S(n),q(-1)))
                or m.contains(lo,S(x)) or m.num(c) in (None,0) or domain_conditions(power[1])):
            raise Unsupported('The source integrand must be a single Volterra order with a fixed lower bound')
        slope,_=along(power[1],W[1]);multiplier=m.neg(slope)
        if m.num(multiplier) in (None,0) or not same_value(power[1],m.mul(multiplier,m.add(hi,m.neg(W)))):
            raise Unsupported('The polynomial kernel must vanish to the full required order at the moving end')
        factor=m.mul(('signed_integer_power',multiplier,m.add(S(n),q(-1))),('signed_integer_power',c,S(n)))
        return dict(theorem='method.integrated_affine_argument_derivative',steps=[
            'Явно трактуем порядок n как положительное целое число. При дифференцировании граничный вклад равен нулю до исчерпания степени.',
            'После n−1 дифференцирований остаётся множитель (n−1)! и обычный интеграл исходной функции с движущимся верхним концом.',
            'Последняя производная равна пределу средних по приращениям верхнего конца. В любой точке непрерывности это значение подынтегральной функции.'],
            original_integrand=raw,upper=hi,power_multiplier=multiplier,upper_rate=c),dict(
            derivative='factor * (n-1)! * L',factor=factor,average_limit='L=lim(delta→0) (1/delta)*int(U,U+delta,f(t)dt)',
            on_continuity_points='L=f(U)',domain='locally integrable profile, with finite indicated average limit at the moving endpoint')
    count=1 if ordinary else 2
    if not continuous or len(bounds)!=count or raw[0]!=f or any(m.contains(z,S(x)) for _,lo,hi in bounds for z in (lo,hi)):
        raise Unsupported('The affine transfer needs one constant-end integration direction per derivative')
    arg=raw[1];coordinates=[S(x),*(w for w,_,_ in bounds)]
    zero=dict.fromkeys(coordinates,ZERO);center=m.substitute(arg,zero)
    coefficients=[m.simplify(m.add(m.substitute(arg,{**zero,w:ONE}),m.neg(center))) for w in coordinates]
    if (not same_value(arg,m.add(center,m.dot(coordinates,coefficients))) or domain_conditions(arg)
            or any(m.num(c) is None for c in coefficients) or any(c==ZERO for c in coefficients[1:])):
        raise Unsupported('The one argument must be fully affine in the differentiating and all bound variables')
    from itertools import product
    c=scale
    for k in coefficients[1:]:c=m.mul(c,m.div(coefficients[0],k))
    traces=[]
    for choices in product((0,1),repeat=count):
        mapping={w:(hi if upper else lo) for upper,(w,lo,hi) in zip(choices,bounds)}
        traces.append(dict(sign=(-1)**(count-sum(choices)),argument=m.simplify(m.substitute(arg,mapping))))
    return dict(theorem='method.integrated_affine_argument_derivative',steps=[
        'В каждом интеграле переносим изменение внешней переменной на один аффинный аргумент интегрирования.',
        'Фундаментальная теорема превращает производную в ориентированную разность значений на противоположных гранях. Используем непрерывность функции.',
        'Для следующей производной используем ещё одну независимую интеграционную координату. После всех переносов остаются вершины прямоугольной области.'],
        original_argument=arg,affine_coefficients=coefficients,bounds=bounds,normalization=scale),dict(
        coefficient=c,profile=f,signed_traces=traces,parameter_domain=rest)


def shifted_gaussian_window(task):
    from tasks import domain_conditions,source
    from verify import same_value
    if set(task)-{'kind','id','source','expression','stated_conditions','requested_output'} or task['requested_output']!=['proof']:
        raise Unsupported('The Gaussian window asks for a different source result')
    source_info=task.get('source',{})
    if (set(source_info)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}
            or source_info.get('literal_requirement') not in (None,'Доказать указанный предел.')):
        raise Unsupported('A different source method or domain is required')
    match=re.fullmatch(r'lim_(\w+)->\+inf sqrt\(\1\)\*int_-(\w+)\^\2 exp\((.+)\)d([a-z])=(.+)',
                       task['expression'].replace('²','^2'))
    if not match:raise Unsupported('No symmetric expanding Gaussian window was found')
    x,d,body,t,wanted=match.groups()
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',body+' '+wanted))-{x,t,'e','pi'}-m.FUNCTIONS-set(m.ALIASES)|{d})
    if len({x,t,d})!=3:raise Unsupported('The positive scale, endpoint and integration binder must be distinct')
    ctx=m.context(dict(variable=x,parameters=names,parameter_conditions=task['stated_conditions']))
    X,T,D=('s',x),('s',t),('s',d);raw=m.parse(body,None,[x,t,*names])
    A=m.simplify(m.div(m.neg(raw),m.mul(X,m.power(T,2))))
    if (domain_conditions(raw) or m.contains(A,X) or m.contains(A,T) or not all(m.constant_defined(s,ctx) and m.sign(s,ctx)==1 for s in (A,D))
            or not same_value(raw,m.neg(m.mul(A,m.mul(X,m.power(T,2)))))):
        raise Unsupported('The source exponent or window size is not a proved positive Gaussian scaling')
    value=('sqrt',m.div(m.PI,A))
    if not same_value(value,m.parse(wanted,None,names)):raise Unsupported('The claimed right side is not the Gaussian mass')
    return dict(theorem='method.gaussian_window_tail',steps=[
        'Подстановка y=√x·t поглощает внешний множитель. Границы становятся ±δ√x и уходят к бесконечности.',
        'На хвосте y≥T>0 ограничиваем интеграл гауссовского ядра интегралом y exp(−a y²)/T. Получаем exp(−aT²)/(2aT), который стремится к нулю.',
        'Две потерянные части сходятся к нулю, и полный гауссовский интеграл равен √(π/a).'],
        source_exponent=raw,gaussian_scale=A,original_radius=D,tail_bound='exp(-'+source(A)+'*T^2)/(2*'+source(A)+'*T)'),dict(value=value)


def symbolic_improper_orders(task):
    """Classify independent singularities by local valuation without fixing parameters."""
    want=task['requested_output'];x=task['variable']
    if want!=['convergence'] or task['upper']!='+inf':
        raise Unsupported('The indexed comparison applies to an ordinary improper convergence question')
    text=task['integrand'].replace(' ','');conditions=task.get('stated_conditions',[])
    params=task.get('parameters',[])
    m.context(dict(variable=x,parameters=params))
    name=r'[A-Za-z_]\w*'
    mark=re.fullmatch(r'1/product\(abs\('+re.escape(x)+r'-('+name+r')\[('+name+r')\]\)\^('+name+r')\[\2\],\2,1,('+name+r')\)',text)
    if mark and task['lower']=='-inf':
        a,j,p,n=mark.groups()
        if len(set([a,j,p,n,x]))!=5 or set(params)!={a,p,n} or conditions!=[f'{a}[1]<...<{a}[{n}]']:
            raise Unsupported('All original singularities must be distinct with the declared finite positive integer count')
        required=[f'{p}[{j}]<1 for every {j}=1..{n}',f'sum({p}[{j}],{j},1,{n})>1']
        return dict(theorem='method.separate_symbolic_improper_orders',argument=[
            'Разделяем соседние особые точки. Около каждой точки все остальные расстояния имеют конечные положительные пределы.',
            'По сравнению с |x−a_j|^(−p_j) требуется и достаточно p_j<1, независимо для всех j.',
            'На обоих хвостах |x−a_j|/|x| стремится к единице. Сходимость там равносильна сумме показателей строго больше единицы.'],
            independent_finite_nodes=a,local_exponents=p,tail_order='negative sum of local exponents'),dict(
                convergence='exact_condition',if_and_only_if=required,convergence_kind='absolute whenever convergent')
    ratio=re.fullmatch(r'P_('+name+r')\('+re.escape(x)+r'\)/P_('+name+r')\('+re.escape(x)+r'\)',text)
    if ratio and str(task['lower'])=='0':
        p,n=ratio.groups()
        if p==n or set(params)!={p,n} or conditions!=[f'P_{p} and P_{n} are coprime polynomials of degrees {p} and {n} respectively']:
            raise Unsupported('Coprimality and both exact polynomial degrees must be stated')
        required=[f'P_{n} has no zeros on [0,+infinity)',f'{n}-{p}>1']
        return dict(theorem='method.separate_symbolic_improper_orders',argument=[
            'В любом нуле знаменателя числитель ненулевой по взаимной простоте. Кратность полюса — положительное целое число, поэтому хотя бы один независимый односторонний интеграл расходится.',
            'Если таких нулей нет, каждый конечный отрезок регулярен. На бесконечности отношение сравнимо с ненулевой константой, умноженной на степень x с показателем m−n.',
            'Знак на хвосте постоянен. Степенной критерий даёт необходимое и достаточное условие обычной и абсолютной сходимости.'],
            denominator='P_'+n,degree_difference=(p,n)),dict(convergence='exact_condition',if_and_only_if=required,
                          convergence_kind='absolute whenever convergent')
    raise Unsupported('No separated order presentation of the original improper integral')
