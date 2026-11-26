"""Prove finite sums and bounds on positive integer sequences in the shared proof graph."""
import re
from fractions import Fraction
from math import comb, lcm

import expressions as m
from model import ONE, ZERO, Unsupported, freeze, q, rational
from polynomial import NotRational, Undefined, distinct_root_counter, pa, pdiv, pgcd, pm, pp, rf, span_coefficients
from tasks import domain_conditions


def translated_coefficients(poly,start):
    """Exact coefficients after x = start + t."""
    result=(Fraction(0),)
    for c in reversed(poly):
        result=pa(pm(result,(start,Fraction(1))),(c,))
    return result


def generating_series_source(task):
    """Read all method obligations before proposing a generating function."""
    fields={'kind','id','source','term','index','start_index','parameters','stated_conditions',
            'index_domain','method_requirement','requested_output'}
    provenance={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256',
                'literal_requirement','printed_instruction','explicit_required_method'}
    src=task.get('source',{});method=task.get('method_requirement')
    methods={'termwise differentiation':'termwise_differentiation','termwise integration':'termwise_integration',
             'abel method':'abel','telescoping':'telescoping'}
    if (set(task)-fields or not isinstance(src,dict) or set(src)-provenance or type(task['start_index']) is not int
            or task['start_index']<0 or task.get('index_domain','integers_from_start')!='integers_from_start'
            or task.get('requested_output',['sum']) not in (['sum'],['convergence_and_sum'])):
        raise Unsupported('Unbound summation scope')
    for key in ('literal_requirement','printed_instruction'):
        if key not in src:continue
        text=src[key].rstrip('.').casefold()
        suffix='. указание: производную умножить на 1-x'
        if text.endswith(suffix):text=text[:-len(suffix)]
        goal,sep,required=text.partition(' by ')
        if goal!='найти сумму ряда' or sep and required not in methods:
            raise Unsupported('The printed summation method is unbound')
        if sep:
            if method not in (None,methods[required]):raise Unsupported('Conflicting summation methods')
            method=methods[required]
    if src.get('explicit_required_method',method)!=method:
        raise Unsupported('Conflicting explicit summation method')
    if method not in (None,*methods.values()):raise Unsupported('Unknown summation method')
    return method


def geometric_kernel_difference(raw,index,start,parameter,spec):
    """Recover an exact antidifference after a geometric or power-map substitution."""
    from operations import expression_positions
    x=('s',parameter);n=('v',index);y=('s','__stage')
    if parameter==y[1] or index==y[1] or start<1:raise Unsupported('The geometric stage must be fresh and have positive exponent')
    nodes=[e for _,e in expression_positions(raw)]
    def shifted(e):return translated_coefficients(coefficients(e,index,start),Fraction(start))
    for e in nodes:
        if e[0] not in ('pow','rpow') or e[1]!=x or e[0]!='rpow':continue
        power=e[2]
        if power[0]=='rpow' and m.num(power[1]) not in (None,0,1):
            base=m.num(power[1]);inner=power[2]
            if base.denominator!=1 or not 2<=base<=8:continue
            try:a,b=shifted(inner)
            except (ValueError,NotRational,Unsupported):continue
            if b!=1 or a<0 or a.denominator!=1:continue
            first=base**a;step=m.power(y,int(base));mode='power'
        else:
            try:a,b=shifted(power)
            except (ValueError,NotRational,Unsupported):continue
            if b<1 or a<1 or any(c.denominator!=1 for c in (a,b)):continue
            first=a;step=m.mul(m.power(x,int(b)),y);mode='linear'
        if first>128:continue
        def transform(z):
            if z[0]=='rpow' and z[1]==x:
                if mode=='linear':
                    co=shifted(z[2])
                    if len(co)==2 and co[1]==b and co[0]>=a and co[0].denominator==1:
                        return step if co[0]-a==b else m.mul(y,m.power(x,int(co[0]-a)))
                elif z[2][0]=='rpow' and m.num(z[2][1])==base:
                    c=shifted(z[2][2])
                    if len(c)==2 and c[1]==1 and c[0]>=a and c[0].denominator==1 and base**(c[0]-a)<=16:
                        return m.power(y,int(base**(c[0]-a)))
                if z==e:return y
            return (z[0],*(transform(c) if isinstance(c,tuple) else c for c in z[1:]))
        try:term=transform(raw)
        except (NotRational,Unsupported):continue
        if m.contains(term,n):continue
        # The original denominators may be products of 1−x^m or 1−(x^m)^b.
        safe={x,y,step}
        for d in (x,y):
            safe.update(m.power(d,k) for k in range(1,17))
        def denominator(g):
            if g[0]=='mul':return all(denominator(z) for z in g[1:])
            return any(m.simplify(g)==m.add(ONE,m.neg(v)) for v in safe)
        if any(relation!='nonzero' or not denominator(g) for relation,g in domain_conditions(term)):
            continue
        kernel=m.div(ONE,m.add(ONE,m.neg(y)))
        delta=m.add(kernel,m.neg(m.substitute(kernel,{y:step})))
        pn,pd=m.rational_form(m.div(term,delta))
        if not pn or not pd:continue
        a0=min(dict(mon).get(y,0) for mon in pn);b0=min(dict(mon).get(y,0) for mon in pd)
        if a0!=b0:continue
        def coefficient(p):
            return m.poly_expr({tuple((s,k) for s,k in mon if s!=y):c
                                for mon,c in p.items() if dict(mon).get(y,0)==a0})
        scale=coefficient(pn),coefficient(pd);v=('v',parameter)
        try:
            U,V=rf(m.substitute(('div',*scale),{x:v}),parameter);common=pgcd(U,V)
            u,_=pdiv(U,common);w,_=pdiv(V,common)
            def polynom(co):return m.poly_expr({((x,i),) if i else ():c for i,c in enumerate(co) if c})
            scale=m.div(polynom(u),polynom(w))
        except (NotRational,Undefined):continue
        if m.contains(scale,y) or m.rational_form(m.add(term,m.neg(m.mul(scale,delta))))[0]:continue
        if any(rel!='nonzero' or not (denominator(g) or denominator(m.neg(g)) or g==x and spec=='outside')
               for rel,g in domain_conditions(scale)):continue
        lower=m.substitute(kernel,{y:m.power(x,int(first))});upper=ONE if spec=='inside' else ZERO
        return dict(theorem='method.geometric_antidifference',stage=e,next_stage=step,original_term=raw,
                    transformed_term=term,kernel=kernel,scale=scale,tail_limit=upper,parameter_domain=spec),m.mul(scale,m.add(lower,m.neg(upper)))
    raise Unsupported('No safe geometric antidifference was identified')


def radical_logarithm_moment(task,lib):
    """Identify the inverse hyperbolic primitive first, then integrate its verified binomial coefficients."""
    from integrals import affine
    from math import factorial
    from tasks import known_guard
    from verify import same_value
    if not lib.data.get('radical_log_series_moments') or task.get('kind')!='integrate_by_series':
        raise Unsupported('No active radical-logarithm moment transition')
    fields={'kind','id','source','expression_or_proposition','scope','variable','parameters','stated_conditions',
            'method_requirement','requested_output'}
    provenance={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
    src=task.get('source',{});heading='Вычислить интеграл разложением подынтегральной функции в ряд.'
    if (set(task)-fields or set(src)-provenance or src.get('literal_requirement',heading)!=heading
            or task.get('parameters') or task.get('stated_conditions')
            or task.get('method_requirement','termwise_integration')!='termwise_integration'
            or task.get('requested_output',['exact_integral'])!=['exact_integral']):
        raise Unsupported('The interval, original expansion method, or full source conclusion remains unbound')
    bounds=task['scope'].split('..')
    try:left,right=map(Fraction,bounds)
    except (ValueError,ZeroDivisionError) as exc:raise Unsupported('Need rational fixed interval bounds') from exc
    if left!=0 or right<=0:raise Unsupported('Use a positive interval anchored at the series origin')
    var=task.get('variable','x');x=('v',var)
    raw=m.parse(task['expression_or_proposition'],var)
    if raw[0]!='div' or raw[2]!=x or raw[1][:1]!=('ln',):
        raise Unsupported('The original quotient is not a logarithm divided by its vanishing argument variable')
    base=raw[1][1]
    if base[0]!='add':raise Unsupported('No matching radical alongside an affine expression')
    line,root=base[1:]
    if line[0]=='sqrt':line,root=root,line
    ctx=m.context(dict(variable=var))
    if root[0]!='sqrt' or not all(known_guard(g,ctx) for g in (*domain_conditions(line),*domain_conditions(root[1]))):
        raise Unsupported('The original logarithm argument contains an additional undefined operation')
    a,b=affine(line,var);a=m.num(a)
    if (a is None or b!=ZERO or not a or abs(a*right)>1
            or not same_value(root[1],m.add(ONE,m.power(line,2)))):
        raise Unsupported('Need the matching real radical and a range contained in the closed binomial disk')
    z=a*right
    def term(j):
        return Fraction((-1)**j*comb(2*j,j),4**j*(2*j+1)**2)*z**(2*j+1)
    # Alternating even and odd partial sums give an exact rational enclosure.
    partial=sum(term(j) for j in range(24));adjacent=partial+term(24)
    enclosure=tuple(map(q,sorted((partial,adjacent))))
    index=next(k for k in ('n','j','k') if k!=var)
    formula=f'sum({index}=0..infinity,(-1)^{index}*binomial(2*{index},{index})*({z})^(2*{index}+1)/(4^{index}*(2*{index}+1)^2))'
    plan=dict(theorem='method.termwise_integral_moments',kernel='inverse_hyperbolic_binomial_primitive',
              original_integrand=raw,interval=[q(left),q(right)],linear_argument=line,
              derivative=('div',q(a),root),input_hole=ZERO,moment_denom_power=2,radius_parameter=q(z),
              argument=[
               'Из sqrt(1+u²)>|u| следует положительность исходного логарифмического аргумента. Непосредственное дифференцирование даёт a/sqrt(1+(a*x)²), исходный логарифм при x=0 равен 0.',
               'При |a*x|<1 применяем биномиальный ряд производной и интегрируем от 0. После деления на x коэффициент получает делитель 2n+1, ноль имеет устранимое продолжение.',
               'Оценка binomial(2n,n)/4^n=O(n^(-1/2)) даёт равномерную абсолютную сходимость ряда интегранда на всём исходном отрезке. Его момент ещё раз делит коэффициент на 2n+1.',
               'Модули числовых членов убывают. Две соседние частичные суммы дают указанное точное ограждение.'])
    return plan,dict(exact_series=formula,enclosure=enclosure,defined_at_left_by_continuity=q(a))


def affine_factorial_series(task,lib):
    """Create an Euler-operator evaluation and keep the original first factorial index."""
    from math import factorial
    from tasks import source
    if not lib.data.get('affine_factorial_series'):
        raise Unsupported('No affine factorial coordinate in this library')
    old=task.get('given')
    method=generating_series_source({k:v for k,v in task.items() if k!='given'})
    if method is not None or task.get('stated_conditions'):
        raise Unsupported('The original method or extra range requires a separate argument')
    index=task['index'];start=task['start_index'];text=task['term'];patt=r'([A-Za-z_]\w*)';n=('v',index)
    if old is not None:
        poly=re.fullmatch(fr'{patt}\({patt}\)=sum\({patt}=0\.\.{patt},{patt}_\3\*\2\^\3\)',old)
        match=re.fullmatch(fr'{patt}\({re.escape(index)}\)\*{patt}\^{re.escape(index)}/factorial\({re.escape(index)}\)',text)
        if not poly or not match or match[1]!=poly[1] or len(set(poly.groups()))!=5:
            raise Unsupported('Bind the finite polynomial and the identical factorial coefficient without index capture')
        func,coord=match.groups();degree=poly[4]
        if coord in (index,func) or task.get('parameters',[coord])!=[coord]:
            raise Unsupported('The generating coordinate must be independent of the integer index')
        j=next(k for k in ('j','k','r','s','t','l','w') if k not in (*poly.groups(),index,coord))
        formula=f'exp({coord})*sum({j}=0..{degree},Delta^{j} {func}(0)*{coord}^{j}/{j}!)'
        subtraction=f'sum({index}=0..{start-1},{func}({index})*{coord}^{index}/{index}!)' if start else '0'
        return (dict(theorem='method.factorial_polynomial_series',polynomial_definition=old,coefficient_index=index,basis_index=j,
                    argument='Падающие факториалы образуют базис полиномов, коэффициенты равны конечным разностям в нуле, делённым на факториал. Сдвиг каждого факториального ряда даёт экспоненту, а начальное исключение вычитается точно.'),
                dict(sum=formula+'-('+subtraction+')',convergence_domain='all_real'))
    names=set(re.findall(r'\b[A-Za-z_]\w*',text))-{index,'factorial','e','pi'}-m.FUNCTIONS-set(m.ALIASES)
    if len(names)!=1 or task.get('parameters',sorted(names))!=sorted(names):
        raise Unsupported('A single independent generating variable is required')
    coord=names.pop();x=('s',coord);raw=m.parse(text,index,[coord],('factorial',))
    if raw[0]!='div' or raw[2][0]!='factorial' or raw[2][1]==n:
        raise Unsupported('The factorial must be a single denominator')
    def linear(e):
        cs=translated_coefficients(coefficients(e,index,start),Fraction(start))
        if len(cs)!=2 or any(c.denominator!=1 for c in cs):
            raise Unsupported('Need an integral affine progression')
        return tuple(map(int,cs))
    c,d=linear(raw[2][1])
    if d not in (1,2) or not 0<=d*start+c<=6:
        raise Unsupported('Only the exponential and its even or odd projections are admitted')
    stride=shift=0;scale=multiplier=Fraction(1);seen=False
    def peel(e):
        nonlocal stride,shift,scale,multiplier,seen
        if e[0]=='mul':return ('mul',peel(e[1]),peel(e[2]))
        if e[0]=='rpow' and (e[1]==x or m.num(e[1]) is not None):
            b=m.num(e[1]);offset,step=linear(e[2])
            if b is not None:
                if not b or max(abs(offset),abs(step))>24:raise Unsupported('Invalid geometric coefficient or phase')
                scale*=b**step;multiplier*=b**offset
            else:
                if step<=0 or step*start+offset<0 or seen:raise Unsupported('An original power may have a pole or an unbound factor')
                seen=True;stride=step;shift=offset
            return ONE
        if domain_conditions(e) or m.contains(e,x):
            raise Unsupported('An original factor is not a total polynomial weight on this lattice')
        return e
    residual=peel(raw[1])
    if not seen:raise Unsupported('Missing original numerator power')
    P,Q=rf(residual,index)
    if Q!=(1,) or len(P)>12:raise Unsupported('A finite real polynomial weight is required')
    start_factorial=d*start+c;deleted=(start_factorial//d)
    residue=start_factorial%d
    kernel='exp(u)' if d==1 else ('cosh(sqrt(u)) if u>=0, cos(sqrt(-u)) otherwise' if residue==0
                       else 'sinh(sqrt(u))/sqrt(u) if u>0, sin(sqrt(-u))/sqrt(-u) if u<0, 1 at 0')
    deleted_powers=[dict(power=k,coefficient=q(1,factorial(d*k+residue))) for k in range(deleted)]
    # Reindex n=start+j. K is divided by u**deleted only after subtracting its
    # first deleted coefficients; the quotient is extended by its next coefficient.
    u=m.mul(q(scale),m.power(x,stride));weight=translated_coefficients(P,Fraction(start))
    pref=m.mul(q(multiplier*scale**start),m.power(x,stride*start+shift))
    atzero=m.mul(pref if not (stride*start+shift) else ZERO,q(weight[0]/factorial(start_factorial)))
    data=dict(series_coordinate=source(u),prefactor=source(pref),kernel=kernel,
              omitted_initial_kernel_terms=deleted_powers,divide_kernel_by_power=deleted,
              euler_operator_coefficients=list(map(q,weight)),value_at_coordinate_zero=atzero,
              evaluation='Build K from the kernel with omitted terms subtracted and removable division by u^k. Apply the polynomial in u*d/du, substitute the series coordinate and multiply by the prefactor.',
              convergence_domain='all_real')
    return dict(theorem='method.factorial_polynomial_series',original_term=raw,
                source_index=index,source_start=start,factorial_stride=d,factorial_first=start_factorial,
                argument='После точного сдвига индекса восстановить полный экспоненциальный ряд или его чётную/нечётную часть. Убрать остаток в начале и применить полином от оператора Эйлера, который умножает члены на исходные степени индекса. В точке нуля использовать доказанное устранимое продолжение.'),data


def generating_series_sum(task,library,request):
    """Sum a coefficient sequence by a proved operator on a basic analytic series."""
    from functools import reduce
    from math import factorial
    from operations import expression_positions
    from tasks import source
    try:return affine_factorial_series(task,library)
    except (Unsupported,NotRational,Undefined):pass
    try:return analytic_coefficient_reduction(task,library,request)
    except (Unsupported,NotRational,Undefined):pass
    method=generating_series_source(task)
    n=task['index'];start=task['start_index'];text=task['term'];idx=('v',n)
    inferred=sorted(set(re.findall(r'\b[A-Za-z_]\w*',text))-{n,'factorial','binomial','prod','pi','e'}-m.FUNCTIONS)
    if 'prod(' in text:return rising_series_sum(task,method)
    if inferred and re.search(r'\b(?:sin|cos)\(',text):
        return harmonic_series_sum(task,method,inferred)
    if task.get('parameters',inferred)!=inferred or len(inferred)>1:
        raise Unsupported('Need a single independent power-series variable')
    if not inferred:return abel_series_sum(task,method,request)
    x=inferred[0];z=('v',x);param=('s',x);constraints=task.get('stated_conditions',[])
    if constraints:
        if method not in (None,'telescoping') or constraints not in ([f'abs({x})<1'],[f'abs({x})>1']):
            raise Unsupported('No generating function preserves these parameter restrictions')
        return geometric_kernel_difference(m.parse(text,n,[x]),n,start,x,'inside' if '<' in constraints[0] else 'outside')
    if method not in (None,'termwise_integration','termwise_differentiation'):
        raise Unsupported('This series cannot use the requested coefficient operation')
    raw=m.parse(text,n,[x],extra_functions={'factorial'})
    b=0;k=0;ratio=Fraction(1);r0=Fraction(1);factorial_weight=False;atomic=[]
    def factors(e,orientation):
        nonlocal b,k,ratio,r0,factorial_weight
        op=e[0]
        if op in ('mul','div'):
            factors(e[1],orientation);factors(e[2],orientation if op=='mul' else -orientation);return
        if e==('factorial',idx) and orientation==-1 and not factorial_weight and start==0:
            factorial_weight=True;return
        if op=='rpow':
            base=e[1];power=translated_coefficients(coefficients(e[2],n,start),Fraction(start))
            if len(power)>2 or any(c.denominator!=1 for c in power):raise Unsupported('The power progression is not integral affine')
            a,h=(int(c) for c in (*power,0)[:2]);a*=orientation;h*=orientation
            if a<0 and base==param or orientation<0 and base==param:raise Unsupported('Do not fill a source pole at zero')
            if base==param:k+=a;b+=h;return
            c=m.num(base)
            if c in (None,0) or max(abs(a),abs(h))>256:raise Unsupported('A finite nonzero geometric coefficient is required')
            ratio*=c**h;r0*=c**a;return
        if m.contains(e,param) or any(a[0]=='factorial' for _,a in expression_positions(e)):
            raise Unsupported('No polynomial/geometric coefficient decomposition')
        atomic.append(e if orientation>0 else ('div',ONE,e))
    factors(raw,1)
    if not 0<b<=24 or not 0<=k<=48:raise Unsupported('Need an increasing nonnegative exponent progression')
    coefficient=ONE
    for e in atomic:coefficient=('mul',coefficient,e)
    p,d=rational_on_tail(coefficient,n,start);p=translated_coefficients(p,Fraction(start));d=translated_coefficients(d,Fraction(start))
    if not any(p):raise Unsupported('The zero generating series requires accounting for its original domain')
    y=m.mul(q(ratio),m.power(z,b));power=m.power(z,k);domain='all_real' if factorial_weight else {'condition':'absolute_value_less_than_one','expression':y}
    from graphs import peval
    def closed_poly(c):
        w=tuple(peval(c,Fraction(i)) for i in range(len(c)));parts=[]
        while w:
            degree=len(parts)
            parts.append(m.mul(q(w[0]*(1 if factorial_weight else factorial(degree))),m.power(y,degree)))
            w=tuple(v-u for u,v in zip(w,w[1:]))
        if factorial_weight:return m.mul(('exp',y),reduce(m.add,parts,ZERO))
        return reduce(m.add,(m.div(v,m.power(m.add(ONE,m.neg(y)),j+1)) for j,v in enumerate(parts)),ZERO)
    p0,remain=pdiv(p,d)
    plan=dict(theorem='method.generating_series_operators',source_term=raw,first_exponent=k,exponent_step=b,geometric_scale=q(ratio),
              initial_weight=q(r0),polynomial_numerator=list(map(q,p)),polynomial_denominator=list(map(q,d)),
              factorial_weight=factorial_weight,method=method)
    def differentiate(e):
        from tasks import guard_source
        t=dict(kind='differentiate',function=source(e),variable=x,method_requirement='table_and_rules',
               stated_conditions=[guard_source(g) for g in domain_conditions(e,True)])
        return freeze(request('differentiate the checked integrated generating function',t)['value'])
    def integrate(e):
        t=dict(kind='integrate',integrand=source(e),variable=x,method_requirement='table_and_rules')
        val=request('primitive of the differentiated generating function',t)['value']
        f=freeze(val.get('representative',val.get('primitive')))
        ctx=m.context(dict(variable=x));zero=m.substitute(f,{z:ZERO})
        if not m.constant_defined(zero,ctx):raise Unsupported('The primitive does not have a known initial value at zero')
        return m.add(f,m.neg(zero))
    if not any(remain):
        if method=='termwise_differentiation':
            k1=k-1
            if k1<0:raise Unsupported('The first coefficient has a separate constant term')
            differential=closed_poly(pm(p0,(Fraction(k),Fraction(b))))
            value=integrate(m.mul(q(r0),m.mul(m.power(z,k1),differential)))
            plan['differentiated_series_sum']=differential
        elif method=='termwise_integration':
            for shift in (0,-1):
                degree=k+1+shift
                if degree<=0:continue
                coeff,left=pdiv(p0,(Fraction(degree),Fraction(b)))
                if any(left):continue
                anti=m.mul(q(r0),m.mul(m.power(z,degree),closed_poly(coeff)))
                value=m.mul(m.power(z,-shift),differentiate(anti));plan['integrated_series_sum']=anti;plan['weight_power']=shift
                break
            else:raise Unsupported('No integration lowers the polynomial coefficient')
        else:value=m.mul(q(r0),m.mul(power,closed_poly(p0)))
    else:
        if factorial_weight or method=='termwise_integration' or k<=0:raise Unsupported('No checked rational series derivative')
        pp,dd=pm(p,(Fraction(k),Fraction(b))),d;poly,excess=pdiv(pp,dd)
        if not any(excess):F1=m.mul(q(r0),m.mul(m.power(z,k-1),closed_poly(poly)))
        else:
            pp=pm(pp,(Fraction(k-1),Fraction(b)));poly,excess=pdiv(pp,dd)
            if k<=1 or any(excess):raise Unsupported('Differentiation leaves a nongeometric coefficient')
            F2=m.mul(q(r0),m.mul(m.power(z,k-2),closed_poly(poly)));F1=integrate(F2);plan['second_derivative_sum']=F2
        value=integrate(F1);plan['differentiated_series_sum']=F1
    # Boundary terms (relative to the interior real interval) are decided from
    # the exact degree difference and the sign of the geometric phase.
    ends=[]
    if not factorial_weight:
        radius=m.simplify(('rpow',q(1/abs(ratio)),q(1,b)));decay=len(d)-len(p)
        for direction in (-1,1):
            a=m.mul(q(direction),radius);alternates=ratio*(direction**b)<0
            classification='absolute' if decay>=2 else 'conditional' if decay==1 and alternates else 'divergent'
            # Abel's continuity theorem gives the radial value on each convergent end.
            answer=None
            if classification!='divergent':
                endpoint=m.substitute(value,{z:a})
                if m.constant_defined(endpoint,m.context(dict(variable=x))):answer=m.simplify(endpoint)
                else:
                    t=dict(kind='limit',variable=x,expression=source(value),approach=dict(point=source(a),side='right' if direction<0 else 'left'))
                    answer=freeze(request('radial limit at a proved convergent endpoint',t)['value'])
                    if isinstance(answer,str):raise Unsupported('A finite endpoint sum remains unproved')
            ends.append(dict(point=a,convergence=classification,sum=answer))
    return plan,dict(interior_sum=value,convergence_domain=domain,boundaries=ends)


def rising_series_sum(task,method):
    """Use the consecutive coefficient recurrence to obtain a binomial series."""
    n=task['index'];text=task['term'];N=re.escape(n)
    match=re.fullmatch(r'prod\(([A-Za-z_]\w*)=0\.\.'+N+r'-1,(.+)\)\*(.+)\^'+N+
                      r'/\((.+)\^'+N+r'\*factorial\('+N+r'\)\)',text)
    first=task['start_index']
    if not match or first not in (0,1) or method not in (None,'termwise_differentiation'):
        raise Unsupported('No consecutive numerator product with n! has been bound')
    j,product,argument,base=match.groups()
    if j==n:raise Unsupported('Product index and series index must differ')
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join((product,argument,base))))-{j})
    if n in names or task.get('parameters',names)!=names:raise Unsupported('Unbound binomial parameters')
    ctx=m.context(dict(variable=j,parameters=names,parameter_conditions=task.get('stated_conditions',[])))
    from integrals import affine
    from tasks import known_guard
    product_expression=m.parse(product,j,names);d=m.parse(base,None,names)
    if not m.constant_defined(d,ctx) or not all(known_guard(g,ctx) for g in domain_conditions(product_expression)):
        raise Unsupported('An original product factor is undefined')
    slope,offset=affine(product_expression,j)
    from verify import same_value
    if m.sign(d,ctx)!=1 or not same_value(slope,d) or not m.constant_defined(offset,ctx):
        raise Unsupported('The product step must match its positive normalizing base')
    z=m.parse(argument,None,names)
    if not m.constant_defined(z,ctx):raise Unsupported('The argument has unresolved original domain')
    a=m.div(offset,d)
    value=m.add(('rpow',m.add(ONE,m.neg(z)),m.neg(a)),q(-first))
    # If a=-m, the consecutive numerator contains a zero from n=m+1 on.
    # Otherwise |c[n+1]/c[n]|→1, and |c[n]|∼C n^(a-1) (sum log of ratios).
    # The signed coefficients at argument -1 eventually alternate and decrease for a<1.
    return dict(theorem='method.generating_series_operators',method=method,binomial_argument=z,normalized_offset=a,
                product=product,first_index=first,recurrence='(n+1)c[n+1]=(n+a)c[n], c[0]=1',
                differential_equation=f"(1-z)F'(z)=a(F(z)+{first}), F(0)={1-first}"),dict(interior_sum=value,
                argument=z,coefficient_parameter=a,convergence_domain='|z|<1, all real z if a is a nonpositive integer',
                terminating_polynomial=f'when a=-m use (1-z)^m-{first} as a polynomial, for m a nonnegative integer',
                boundaries=[
                    dict(point=q(1),condition='a<0 except terminating polynomial',sum=q(-first)),
                    dict(point=q(-1),condition='a<1 except terminating polynomial',sum=m.add(('rpow',q(2),m.neg(a)),q(-first)))])


def abel_series_sum(task,method,request):
    """Apply the original Abel boundary method to geometric and central binomial coefficients."""
    if task['start_index']!=0 or method!='abel' or task.get('stated_conditions') or task.get('parameters'):
        raise Unsupported('No Abel boundary specified for this series')
    from tasks import source
    n=task['index'];idx=('v',n);z=('v','__abel')
    if n==z[1]:raise Unsupported('The radial variable must be fresh')
    central_token='__binomial';N=re.escape(n)
    text=re.sub(r'binomial\(2\*'+N+','+N+r'\)',central_token,task['term'])
    if n==central_token:raise Unsupported('The symbolic central coefficient must be fresh')
    raw=m.parse(text,n,[central_token])
    alternating=('rpow',q(-1),idx);central=('binomial',m.mul(q(2),idx),idx)
    base=('div',('s',central_token),('rpow',q(4),idx))
    normalized=m.simplify(raw)
    original=m.substitute(raw,{('s',central_token):central})
    if raw==('mul',alternating,base) or normalized==m.simplify(('mul',alternating,base)):
        return dict(theorem='method.abel_series_values',method=method,radial_sum=('div',ONE,('sqrt',m.add(ONE,z))),
                    original_term=original,boundary='alternating Wallis coefficients decrease to zero'),m.div(ONE,('sqrt',q(2)))
    if normalized==m.simplify(('div',base,m.add(m.mul(q(2),idx),ONE))):
        return dict(theorem='method.abel_series_values',method=method,radial_sum=('asin',z),original_term=original,
                    boundary='positive integrated Wallis coefficients are O(n^(-3/2))'),m.div(m.PI,q(2))
    if raw[0]!='div' or raw[1]!=alternating:raise Unsupported('A geometric Abel primitive cannot be read')
    c=coefficients(raw[2],n,0)
    if len(c)!=2 or c[0]!=1 or c[1].denominator!=1 or not 1<=c[1]<=8:
        raise Unsupported('No positive index progression with a rational Abel derivative')
    k=int(c[1]);deriv=m.div(ONE,m.add(ONE,m.power(z,k)))
    val=request('Abel generating function from 0 to 1',dict(kind='iterated_integral',integrand=source(deriv),
        integration_order=[dict(variable=z[1],lower='0',upper='1')],requested_output=['exact_integral']))['value']
    if isinstance(val,dict):val=val['exact_integral']
    return dict(theorem='method.abel_series_values',method=method,radial_derivative=deriv,original_term=raw,
                boundary='alternating decreasing reciprocals and Abel limit at 1'),freeze(val)


def harmonic_series_sum(task,method,names):
    """Reduce finitely many real harmonics to exponential or boundary-logarithm modes."""
    from integrals import affine,harmonic_modes
    from tasks import known_guard,source
    from verify import same_value
    if method is not None or task.get('parameters',names)!=names:raise Unsupported('Unexpected method for harmonic summation')
    name=task['index'];n=('v',name);start=task['start_index']
    conditions=task.get('stated_conditions',[]);linear_bounds=[]
    for c in conditions:
        match=re.fullmatch(r'0<([A-Za-z_]\w*)<(pi(?:/[1-9][0-9]*)?)',c)
        if not match or match[1] not in names:raise Unsupported('The trigonometric parameter assumptions are unbound')
        linear_bounds.extend([match[1]+'>0',match[2]+'-'+match[1]+'>0'])
    ctx=m.context(dict(variable=name,parameters=names,parameter_conditions=linear_bounds))
    raw=m.parse(task['term'],name,names,extra_functions={'factorial'})
    if raw[0]!='div':raise Unsupported('The harmonic weight must be separated')
    wave,weight=raw[1:];factorial_weight=weight==('factorial',n) and start==0
    if not all(known_guard(g,ctx) for g in domain_conditions(wave)):
        raise Unsupported('An original harmonic factor has an unresolved real domain')
    if factorial_weight:stride=1;first=0;degree=0
    else:
        degree=weight[2] if weight[0]=='pow' else 1
        if degree not in (1,2):raise Unsupported('No base harmonic series for this denominator degree')
        progression=weight[1] if weight[0]=='pow' else weight
        b=translated_coefficients(coefficients(progression,name,start),Fraction(start))
        if b not in ((1,1),(1,2)):raise Unsupported('The positive harmonic progression has an unsupported start or stride')
        first,stride=map(int,b)
    if stride==2:
        if wave[0] not in ('sin','cos'):raise Unsupported('The coefficient parity filter needs one harmonic')
        theta,c=affine(wave[1],name)
        if not same_value(c,m.mul(q(1-2*start,2),theta)):
            raise Unsupported('The angular phase must follow the same odd progression as the denominator')
        theta=m.div(theta,q(2));r=wave[0]
        if r=='sin' and degree==1:
            kernel=('periodic_sawtooth',theta)
            even=('periodic_sawtooth',m.mul(q(2),theta))
        elif r=='cos' and degree==2:
            kernel=('periodic_second_bernoulli',theta)
            even=('periodic_second_bernoulli',m.mul(q(2),theta))
        else:raise Unsupported('No real convergent odd harmonic kernel')
        value=('sub',kernel,('scale',q(1,2**degree),even))
        domains={r:'all_real'}
        plan=dict(odd_progression=(first,stride),kernel=kernel,even_part=('scale',q(1,2**degree),even))
    else:
        t=dict(kind='integrate',integrand=source(wave),variable=name,parameters=names,method_requirement='table_and_rules')
        modes,_,_=harmonic_modes(t);items=[]
        for (a,theta),p in modes.items():
            if a!=ZERO or len(p)!=1:raise Unsupported('A constant harmonic coefficient is required')
            u,v=p[0]
            if not all(m.constant_defined(c,ctx) for c in (u,v,theta)):
                raise Unsupported('An original harmonic coefficient or phase is undefined')
            items.append(dict(phase=theta,cosine=u,sine=m.neg(v)))
        if factorial_weight:
            value=ZERO
            for p in items:
                theta=p['phase']
                z=m.mul(('exp',('cos',theta)),m.add(m.mul(p['cosine'],('cos',('sin',theta))),
                                                  m.mul(p['sine'],('sin',('sin',theta)))))
                value=m.add(value,z)
            domains='all_real'
        else:
            if degree!=1:raise Unsupported('The higher sine harmonic kernel has not been admitted')
            # Resonant cosine rows have the same H_N. Their coefficients have
            # to be added before any divergent contribution can be removed.
            value=dict(nonresonant_terms=items,
                       formula='Sum cosine*log_cosine_kernel(phase)+sine*periodic_sawtooth(phase) over nonresonant rows',
                       resonance='sum the cosine weights for phases in 2*pi*Z; all resonant sine terms vanish')
            domains=dict(convergence_condition='the sum of resonant cosine weights is zero',divergence='otherwise, with the sign of that sum')
        plan=dict(harmonic_modes=items)
    theory=dict(periodic_argument='r = theta mod (2*pi), 0<=r<2*pi',
                periodic_sawtooth='zero at r=0; (pi-r)/2 when 0<r<2*pi',
                log_cosine_kernel='-ln(2*sin(r/2)) for 0<r<2*pi',
                periodic_second_bernoulli='pi^2/6-pi*r/2+r^2/4, including r=0')
    plan.update(theorem='method.harmonic_series_values',original_term=raw,positive_progression=(first,stride),theory=theory)
    if isinstance(value,tuple) and factorial_weight:return plan,m.simplify(value)
    return plan,dict(sum=value,convergence_domain=domains,conditions=conditions,kernels=theory)


def elementary_log_moment(term,x,ctx):
    """Identify x^a log(1−s*x^b) log(x)^k on the full open unit interval."""
    z=('v',x);sense=1;log=None;alpha=ZERO;k=0
    def decompose(e,exp):
        nonlocal sense,log,alpha,k
        if e[0] in ('mul','div'):
            decompose(e[1],exp);decompose(e[2],exp if e[0]=='mul' else -exp)
        elif e==q(-1):sense=-sense
        elif e==ONE:return
        elif e==z:alpha=m.add(alpha,q(exp))
        elif e[0] in ('pow','rpow') and e[1]==z:
            power=q(e[2]) if e[0]=='pow' else e[2]
            if not m.constant_defined(power,ctx):raise Unsupported('An original exponent is undefined')
            alpha=m.add(alpha,m.mul(q(exp),power))
        elif e==('ln',z) and exp==1:k+=1
        elif e[0]=='ln' and exp==1 and log is None:
            g=e[1]
            if g[0]=='div' and g[1]==ONE:sense=-sense;g=g[2]
            log=g
        else:raise Unsupported('A factor does not have an elementary logarithmic moment')
    decompose(term,1)
    if log is None or log[0]!='add' or log[1]!=ONE:raise Unsupported('The logarithm is not normalized to one at zero')
    v=log[2];sign=-1
    if v[0]=='mul' and v[1]==q(-1):v=v[2];sign=1
    beta=ONE if v==z else q(v[2]) if v[0]=='pow' and v[1]==z else v[2] if v[0]=='rpow' and v[1]==z else None
    if beta is None:raise Unsupported('No positive logarithmic moment exponent may be inferred')
    return sense,alpha,k,sign,beta


def termwise_integral_sum(task,library,request):
    """Integrate a logarithmic or exponential series using exact whole-interval moments."""
    try:return radical_logarithm_moment(task,library)
    except (Unsupported,NotRational,Undefined):pass
    from math import factorial
    from integrals import affine
    from tasks import source
    if not library.data.get('termwise_integration_moments'):raise Unsupported('No admitted termwise integral law')
    fields={'kind','id','source','expression_or_proposition','scope','variable','parameters','stated_conditions','method_requirement','requested_output'}
    provenance={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
    src=task.get('source',{});heading='Вычислить интеграл разложением подынтегральной функции в ряд.'
    if (set(task)-fields or not isinstance(src,dict) or set(src)-provenance
            or src.get('literal_requirement',heading)!=heading
            or task.get('method_requirement','termwise_integration')!='termwise_integration'
            or task.get('requested_output',['exact_integral'])!=['exact_integral']):
        raise Unsupported('The source integration method, interval, or output remains unbound')
    scope=task['scope'];interval,*inline=(p.strip() for p in scope.split(','))
    if inline and task.get('stated_conditions'):raise Unsupported('Do not merge distinct parameter conditions')
    conditions=inline or task.get('stated_conditions',[])
    x=task.get('variable','x');z=('v',x);text=task['expression_or_proposition'];n='__moment'
    if n==x:raise Unsupported('The series index must be fresh')
    pars=sorted(set(re.findall(r'\b[A-Za-z_]\w*',text))-{x,'pi','e'}-m.FUNCTIONS)
    if task.get('parameters',pars)!=pars:raise Unsupported('Additional integral parameters are unbound')
    ctx=m.context(dict(variable=x,parameters=pars,parameter_conditions=conditions));raw=m.parse(text,x,pars)
    plan=dict(theorem='method.termwise_integral_moments',original_integrand=raw,interval=interval)
    if interval=='0..1':
        try:sense,a,k,s,b=elementary_log_moment(raw,x,ctx)
        except Unsupported:raise Unsupported('No verified moment representation for the original function')
        a=m.add(a,ONE)
        if not m.constant_defined(a,ctx) or not m.known_nonnegative(a,ctx) or not m.constant_defined(b,ctx) or m.sign(b,ctx)!=1:
            raise Unsupported('Powers in each integral need a positive moment exponent')
        index=('v',n);exponent=m.add(a,m.mul(b,index))
        coefficient=q(sense*(-1)**(k+1)*factorial(k));growth=k+2
        plan.update(kernel='logarithmic',moment_power=exponent,logarithm_degree=k,series_sign=s,
                    absolute_moment_majorant=m.div(q(factorial(k)),m.power(b,k+1)),decay_order=growth)
        A,B=m.num(a),m.num(b)
        if A is None or B is None:
            if not k and s==1 and m.sign(a,ctx)==1:
                # Direct convergent digamma series at 1+a/b.
                value=m.mul(m.div(coefficient,a),m.add(('digamma',m.add(ONE,m.div(a,b))),('euler_gamma',)))
            else:raise Unsupported('A symbolic logarithmic moment remains')
        else:
            denominator=m.mul(index,m.power(exponent,k+1));numerator=ONE if s==1 else ('rpow',q(-1),index)
            t=dict(kind='series_sum',index=n,start_index=1,term=source(m.div(numerator,denominator)),method_requirement='partial_fractions')
            value=m.mul(coefficient,freeze(request('sum the absolutely convergent logarithmic moments',t)['value']))
        return plan,value
    if (interval!='0..+infinity' or raw[0]!='div' or raw[2][0]!='add' or raw[2][1][0]!='exp'
            or m.num(m.simplify(raw[2][2])) not in (-1,1)):
        raise Unsupported('No exponential moment with a geometric denominator')
    a,b=affine(raw[2][1][1],x);p,d=rational_on_tail(raw[1],x,1)
    if b!=ZERO or not m.constant_defined(a,ctx) or m.sign(a,ctx)!=1 or len(d)!=1 or sum(c!=0 for c in p)!=1 or len(p)<2:
        raise Unsupported('The moments require decay, a monomial, and an integrable lower endpoint')
    r=-int(m.num(m.simplify(raw[2][2])));k=len(p)-1;c=q(p[-1]/d[0]);j=('v',n);powj=m.power(j,k+1)
    numerator=ONE if r==1 else ('rpow',q(-1),m.add(j,q(-1)))
    t=dict(kind='series_sum',index=n,start_index=1,term=source(m.div(numerator,powj)),method_requirement='partial_fractions')
    constant=m.div(m.mul(c,q(factorial(k))),m.power(a,k+1))
    plan.update(kernel='exponential',coefficient=constant,decay_order=k+1,series_sign=r)
    return plan,m.mul(constant,freeze(request('sum the absolutely convergent exponential moments',t)['value']))


def positive_rational_log(value):
    """Write ln(value) as a logarithm in [1,2) plus an integer multiple of ln 2."""
    if value<=0:raise Unsupported('The logarithm argument must be positive')
    k=value.numerator.bit_length()-value.denominator.bit_length();u=value/Fraction(2)**k
    if u<1:k-=1;u*=2
    return m.add(('ln',q(u)),m.mul(q(k),('ln',q(2))))


def power_series_quadrature(task,library):
    """Integrate each monomial exactly and bound the integrated tail on its source interval."""
    from math import factorial
    from quadrature import taylor_enclosure
    if not library.data.get('termwise_integration_moments'):raise Unsupported('No admitted termwise integral law')
    fields={'kind','id','source','integrand','variable','interval','absolute_accuracy','method_requirement','requested_output'}
    source_fields={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
    src=task.get('source',{});heading=src.get('literal_requirement','')
    if (set(task)-fields or set(src)-source_fields or heading and heading!='С помощью разложения подынтегральной функции в ряд вычислить интеграл с точностью до 0,001.'
            or task.get('requested_output',['certified_integral'])!=['certified_integral']
            or task.get('method_requirement')!='integrand_series_and_termwise_integration'):
        raise Unsupported('The original termwise integration method is unbound')
    eps=Fraction(task['absolute_accuracy']);a,b=task['interval']
    L=Fraction(a);R=None if b=='+infinity' else Fraction(b)
    if eps<=0 or L<0 or R is not None and L>=R or heading and eps!=Fraction(1,1000):
        raise Unsupported('Invalid integral interval or accuracy')
    x=task['variable'];z=('v',x);raw=m.parse(task['integrand'],x)
    def monomial(e):
        # Only Laurent monomials, with raw guards restricted to powers of x
        # and nonzero constants, are replaced here.
        ctx=m.context(dict(variable=x))
        from tasks import known_guard
        for rel,g in domain_conditions(e):
            if known_guard((rel,g),ctx):continue
            if rel!='nonzero' or g!=z and not (g[0]=='pow' and g[1]==z):raise Unsupported('An original interior pole may remain')
        p,d=rf(e,x)
        if sum(c!=0 for c in p)!=1 or sum(c!=0 for c in d)!=1:
            raise Unsupported('No single Laurent monomial')
        return p[-1]/d[-1],len(p)-len(d)
    bounds=(Fraction(0),Fraction(0));extra=''
    if raw==('rpow',z,z) and L==0 and R==1:
        # x log x is real inside (0,1), takes values in [-1/e,0],
        # and extends by zero at x=0. Taylor's real exponential remainder
        # is bounded by 1/(2^n n!) on the full interval.
        moment=lambda j: (Fraction((-1)**j,(j+1)**(j+1)),)*2
        tail=lambda j: Fraction(1,2**j*factorial(j))
        basis='exponential_of_x_log_x';peak=Fraction(1,2);s=0;p=1;c=Fraction(1);alpha=None
    else:
        outer=ONE;f=raw
        if f[0]=='div':
            try:monomial(f[2])
            except (NotRational,Undefined,Unsupported):
                if f[1]!=ONE:
                    monomial(f[1]);outer=f[1];f=('div',ONE,f[2])
            else:outer=('div',ONE,f[2]);f=f[1]
        if f[0]=='mul':
            for k in (1,2):
                try:monomial(f[k])
                except (NotRational,Undefined,Unsupported):continue
                outer=('mul',outer,f[k]);f=f[3-k];break
        alpha=None;basis=f[0]
        if basis in ('ln','exp','sin','cos','sinh','cosh','asin','atan'):argument=f[1]
        else:
            basis='binomial';alpha=Fraction(1);argument=f
            if argument[0]=='div' and argument[1]==ONE:alpha=-alpha;argument=argument[2]
            if argument[0] in ('sqrt','cbrt','rpow'):
                op=argument[0]
                if op=='rpow' and not m.constant_defined(argument[2],m.context(dict(variable=x))):
                    raise Unsupported('The original exponent is undefined')
                exponent=Fraction(1,2) if op=='sqrt' else Fraction(1,3) if op=='cbrt' else m.num(m.simplify(argument[2]))
                if exponent is None:raise Unsupported('The binomial exponent is not rational')
                alpha*=exponent;argument=argument[1]
        C,s=monomial(outer)
        if basis in ('binomial','ln'):
            if argument[0]!='add' or argument[1]!=ONE:raise Unsupported('Need a unit-centered logarithmic/binomial argument')
            v,p=monomial(argument[2])
            if p>0 and L>0 and (R is None or abs(v)*R**p>1) and abs(v)*L**p>1:
                # Factor the positive growing monomial before expanding at infinity.
                if v!=1:raise Unsupported('Need an exact unit scale for the outside expansion')
                if basis=='binomial':
                    if (p*alpha).denominator!=1:raise Unsupported('The outside Laurent offset is nonintegral')
                    s+=int(p*alpha)
                else:
                    if R is None or s!=-1:raise Unsupported('The split logarithm needs its exact finite logarithmic moment')
                    part=m.mul(q(C*p/2),m.add(m.power(positive_rational_log(R),2),m.neg(m.power(positive_rational_log(L),2))))
                    bounds,_=taylor_enclosure(part,16)
                p=-p;extra='factor positive growing monomial'
        else:v,p=monomial(argument)
        if p==0:raise Unsupported('Need a nonconstant monomial argument')
        if p>0 and R is None or p<0 and L==0:raise Unsupported('The argument is unbounded')
        peak=abs(v)*(R if p>0 else L)**p
        first=1 if basis=='ln' else int(basis in ('sin','sinh','atan','asin'))
        stride=2 if basis in ('sin','cos','sinh','cosh','atan','asin') else 1
        finite_radius=basis in ('binomial','ln','atan','asin')
        alternating=(basis=='binomial' and alpha is not None and -1<=alpha<0 and v>0 or
                     basis in ('atan','ln') and (v>0 or basis=='atan'))
        if finite_radius and (peak>1 or peak==1 and not alternating):
            raise Unsupported('Uniform absolute or alternating remainder bound fails on the closed integration interval')
        def coefficients(j):
            d=first+stride*j
            if basis in ('exp','sin','cos','sinh','cosh'):return d,Fraction((-1)**j if basis in ('sin','cos') else 1,factorial(d))
            if basis in ('ln','atan'):return d,Fraction((-1)**j,d)
            if basis=='asin':return d,Fraction(comb(2*j,j),4**j*d)
            c=Fraction(1)
            for i in range(j):c*=Fraction(alpha-i,i+1)
            return d,c
        def integrate_power(k):
            if k==-1:
                if R is None or not L:raise Unsupported('An original moment is not integrable')
                return taylor_enclosure(('ln',q(R/L)),16)[0]
            h=k+1
            if R is None:
                if h>=0:raise Unsupported('A moment does not decay at infinity')
                v=-L**h/h
            else:
                if not L and h<=0:raise Unsupported('A moment is unbounded at zero')
                v=(R**h-L**h)/h
            return v,v
        def moment(j):
            d,c=coefficients(j);m0,m1=integrate_power(s+p*d);scale=C*c*v**d
            return tuple(sorted((scale*m0,scale*m1)))
        def tail(j):
            d,c=coefficients(j);enclosure=moment(j);first_moment=max(map(abs,enclosure))
            if alternating:return first_moment
            if finite_radius:
                ratio=peak**stride
                if basis=='binomial':
                    if -1<=alpha<=1:ratio=peak
                    else:ratio=peak*max(Fraction(1),abs(alpha-j)/(j+1))
            else:
                ratio=peak**stride
                for k in range(1,stride+1):ratio/=d+k
            return first_moment/(1-ratio) if ratio<1 else None
        c=v
    terms=[];lo,hi=bounds
    for j in range(160):
        bound=tail(j)
        if terms and bound is not None and (hi-lo)/2+bound<=eps:
            center=(hi+lo)/2;error=(hi-lo)/2+bound
            plan=dict(theorem='method.termwise_integral_moments',raw_integrand=raw,basis=basis,argument_scale=q(c),
                      argument_exponent=p,weight_exponent=s,argument_bound=q(peak),
                      expansion_exponent=None if alpha is None else q(alpha),transformation=extra,
                      integrated_terms=terms,extra_enclosure=list(map(q,bounds)),tail_bound=q(bound))
            return plan,dict(approximation=q(center),certified_remainder=q(error),enclosure=[q(center-error),q(center+error)],terms=j)
        a,b=moment(j);lo+=a;hi+=b;terms.append([q(a),q(b)])
    raise Unsupported('The requested accuracy needs more certified integral moments')


def series_numeric_bounds(task,library,saved=None):
    """Bind the required expansion and give rational endpoint enclosures."""
    from quadrature import taylor_enclosure
    if not library.data.get('termwise_integration_moments'):raise Unsupported('No admitted series precision law')
    fields={'kind','id','source','expression','absolute_accuracy','terms','method_requirement','requested_output'}
    src=task.get('source',{});heading=src.get('literal_requirement','');method=task.get('method_requirement');expr=task['expression']
    fixed=task.get('terms');eps=Fraction(task.get('absolute_accuracy','1/1000000'))
    headings=('', 'Приближённо вычислить данную величину и оценить соответствующую погрешность.',
              'Вычислить с указанной точностью, пользуясь данным разложением или указанным соотношением.')
    if (set(task)-fields or not isinstance(src,dict)
            or set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
            or task.get('requested_output',['approximation','certified_remainder'])!=['approximation','certified_remainder']
            or (fixed is not None and (type(fixed) is not int or not 1<=fixed<=40)) or eps<=0
            or heading not in headings and (fixed!=3 or method!='Newton_binomial'
                or heading!=f'Пользуясь формулой бинома Ньютона, приближённо вычислить {expr} и оценить ошибку, взяв три члена.')):
        raise Unsupported('The printed expansion, number of terms, or requested accuracy has not been bound')
    # A degree suffix qualifies the whole numeric angle, including its sign
    # and rational denominator. Unrecognized units stay outside this reader.
    angle=r'[+-]?\s*(?:\d+(?:\.\d+)?|\.\d+)(?:\s*/\s*[+-]?\s*\d+(?:\.\d+)?)?'
    degrees=re.compile(r'\b(sin|cos|tan|cot)\s*\(\s*(?:('+angle+r')|\(\s*('+angle+r')\s*\))\s+degrees?\s*\)')
    expr_deg=degrees.sub(lambda h:h[1]+'(('+ (h[2] or h[3]).strip()+')*pi/180)',expr)
    if re.search(r'\bdegrees?\b',expr_deg):
        raise Unsupported('The degree unit must apply to a complete signed numerical angle')
    raw=[]
    def rewrite(e):
        if e[0]=='tan':
            return ('div',('sin',e[1]),('cos',e[1]))
        if e[0]=='atan':
            t=m.num(m.simplify(e[1]))
            if t is not None and t>=1:
                return m.add(m.mul(q(1,4),m.PI),('atan',q((t-1)/(t+1))))
        if e[0]=='ln':
            t=m.num(m.simplify(e[1]))
            if t is not None and t>=2:return positive_rational_log(t)
        return e
    if method in (None,'Newton_binomial','corresponding power expansions'):
        raw=[m.parse(expr_deg,None)]
        # A tangent is reduced to a quotient whose cosine denominator is
        # checked by interval arithmetic at the exact original angle.
        check=raw[0][1] if raw[0][0]=='tan' else raw[0]
        if not m.constant_defined(check,m.context({})):raise Unsupported('The original expression must be defined before reducing its argument')
        if fixed is not None and (method!='Newton_binomial' or raw[0][0] not in ('cbrt','sqrt','rpow')):
            raise Unsupported('Exactly one fixed binomial truncation is required')
        transformed=list(map(rewrite,raw))
    elif expr=='pi' and method=='pi/6=asin(1/2)':
        raw=[m.PI];transformed=[('mul',q(6),('asin',q(1,2)))]
    elif expr=='pi' and isinstance(method,str) and method.startswith('pi/4='):
        right=method.removeprefix('pi/4=')
        parts=re.split(r'(?=[+-])',right)
        re_part=r'([+-]?)(?:(\d+)\*)?atan\((\d+)/([1-9]\d*)\)'
        C=Fraction(1);S=cap=Fraction(0)
        for part in parts:
            mm=re.fullmatch(re_part,part)
            if not mm:raise Unsupported('The required arctangent identity could not be read')
            sign,count,p,d=mm.groups();count=int(count or 1);u=Fraction(int(p),int(d));sg=-1 if sign=='-' else 1
            cap+=count*u
            if count>12 or not 0<u<1:raise Unsupported('An arctangent branch remains unresolved')
            for _ in range(count):C,S=C-sg*u*S,S+sg*u*C
        # |sum angles|<sum u<3/2<pi/2 and tan(sum angles)=1 fix its branch.
        if cap>=Fraction(3,2) or C!=S or C==0:raise Unsupported('An exact tangent addition and branch proof are required')
        raw=[m.PI];transformed=[('mul',q(4),m.parse(right,None))]
    elif method=='ln(n+1)=ln(n)+2*sum_{k>=0} 1/((2*k+1)*(2*n+1)^(2*k+1))':
        raw=[m.parse(t,None) for t in expr.split(',')];transformed=[]
        for t in raw:
            v=m.num(t[1]) if t[0]=='ln' else None
            if v is None or v.denominator!=1 or not 2<=v<=24:raise Unsupported('The logarithmic recurrence needs an integer endpoint')
            g=ZERO
            for j in range(1,int(v)):
                g=('add',g,('ln',q(j+1,j)))
            transformed.append(g)
    else:raise Unsupported('The original numerical expansion method needs its own proof')
    if method=='Newton_binomial' and fixed is None:raise Unsupported('The required binomial count is absent')
    for degree in ([fixed] if fixed is not None else [4,6,9,14,24,36,64]):
        rows=[];vals=[]
        try:
            for e in transformed:
                (lo,hi),steps=taylor_enclosure(e,degree);mid=(lo+hi)/2
                rows.append(steps);vals.append(dict(approximation=q(mid),enclosure=[q(lo),q(hi)],certified_remainder=q((hi-lo)/2)))
        except Unsupported:
            if fixed is not None:raise
            continue
        if fixed is not None and 'absolute_accuracy' not in task or all(m.num(v['certified_remainder'])<=eps for v in vals):
            return dict(theorem='method.series_constant_enclosures',method=method,original=raw,expanded=transformed,terms=degree,steps=rows),vals[0] if len(vals)==1 else vals
    raise Unsupported('The prescribed method did not achieve a certified error')
def integer_sign_runs(poly,lower):
    """Return the first integer of each consecutive run and its exact polynomial sign."""
    from graphs import peval
    def sign(value):
        return (value>0)-(value<0)
    shifted=translated_coefficients(poly,lower)
    if not min(shifted)<0<max(shifted):
        at=sign(shifted[0])
        after=sign(sum(shifted))
        return [(lower,at)] if at==after else [(lower,at),(lower+1,after)]
    # Removing repeated factors for the root count makes V(a)-V(b) valid even
    # when an integer endpoint is a multiple root. Signs are taken on the original.
    variations=distinct_root_counter(poly)
    upper=max(lower,2+int(max(abs(Fraction(c,poly[-1])) for c in poly[:-1])))
    work=[(lower,upper,variations(lower),variations(upper))]
    cuts={lower}
    if not shifted[0]:cuts.add(lower+1)
    while work:
        a,b,left,right=work.pop()
        if left==right:continue
        if b-a==1:
            cuts.add(b)
            if not peval(poly,b):cuts.add(b+1)
            continue
        middle=(a+b)//2
        v=variations(middle)
        work.extend(((a,middle,left,v),(middle,b,v,right)))
    runs=[]
    for point in sorted(cuts):
        s=sign(peval(poly,point))
        if not runs or runs[-1][1]!=s:runs.append((point,s))
    return runs


def rational_on_tail(expr, variable, lower):
    """Prove every raw denominator is nonzero before cancellation on the integer tail."""
    for relation, guard in domain_conditions(expr):
        if relation != 'nonzero':
            raise NotRational()
        for factor in rf(guard, variable):
            if any(s==0 for _,s in integer_sign_runs(factor,lower)):
                raise Unsupported('Знаменатель обращается в нуль в исходном целом индексе')
    return rf(expr, variable)


def discrete_extremum(task,library):
    from graphs import SET_TASK_FIELDS,order_source_method
    g=task['goal'];kind=g.get('goal');assumptions=task.get('assumptions')
    if (not library.data.get('integer_extrema_by_adjacent_terms') or set(task)-SET_TASK_FIELDS-{'method_requirement'} or task.get('transcription_notes')
            or set(g)!={'sequence','goal'} or kind not in ('maximum','minimum') or len(assumptions or [])!=1):
        raise Unsupported('Unbound sequence domain or extremum requirement')
    match=re.fullmatch(r'([a-zA-Z][a-zA-Z0-9_]*) is a positive integer',assumptions[0])
    if not match:raise Unsupported('A positive integer index is required')
    var=match[1];n=('v',var);succ=m.add(n,ONE)
    required=order_source_method(task,f'Найти {kind} член последовательности x_{var}={g["sequence"]}.',
                                 ('integer_extrema_by_adjacent_terms','successive_difference','positive_squared_successive_ratio_minus_one'))
    expr=m.parse(g['sequence'],var,extra_functions={'factorial'})
    def shift(e):return m.substitute(e,{n:succ})
    def positive_rational(e):
        p,d=rational_on_tail(e,var,1)
        if any(sign!=1 for _,sign in integer_sign_runs(pm(p,d),1)):raise Unsupported('Positive terms are required for adjacent ratios')
    def squared_ratio(e):
        if e[0]=='factorial' and e[1]==n:return m.power(succ,2)
        if e[0]=='rpow' and m.num(e[1]) is not None and m.num(e[1])>0:
            step=coefficients(('add',shift(e[2]),('mul',q(-1),e[2])),var,1)
            if len(step)==1 and step[0].denominator==1:return m.power(e[1],2*int(step[0]))
        if e[0] in ('div','mul'):
            return (e[0],squared_ratio(e[1]),squared_ratio(e[2]))
        if e[0]=='sqrt':
            positive_rational(e[1]);return ('div',shift(e[1]),e[1])
        positive_rational(e);return ('pow',('div',shift(e),e),2)
    ratio_mode='positive_squared_successive_ratio_minus_one'
    mode=required if required in ('successive_difference',ratio_mode) else None
    if mode!=ratio_mode:
        try:rational_on_tail(expr,var,1);mode='successive_difference'
        except NotRational:
            if mode=='successive_difference':raise Unsupported('A certified rational first difference for the prescribed method is unavailable')
    if mode=='successive_difference':witness=('add',shift(expr),('mul',q(-1),expr))
    else:witness=('add',squared_ratio(expr),q(-1));mode=ratio_mode
    p,d=rational_on_tail(witness,var,1);runs=integer_sign_runs(pm(p,d),1)
    orientation=1 if kind=='maximum' else -1
    signs=[orientation*s for _,s in runs];candidates=[]
    for i,((start,_),s) in enumerate(zip(runs,signs)):
        if i and signs[i-1]<=0:continue
        if s<0:candidates.append([start,start])
        if s==0 and (i+1==len(runs) or signs[i+1]<0):candidates.append([start,runs[i+1][0] if i+1<len(runs) else '+inf'])
    if not candidates:raise Unsupported('No attained extremum candidate on the positive integers')
    from operations import expression_positions
    def at(i):
        v=m.substitute(expr,{n:q(i)})
        small={z:m.power(z[1],int(m.num(z[2]))) for _,z in expression_positions(v)
               if z[0]=='rpow' and m.num(z[2]) is not None and m.num(z[2]).denominator==1 and abs(m.num(z[2]))<=64}
        return v if any(z[0]=='factorial' for _,z in expression_positions(v)) else m.simplify(m.substitute(v,small))
    ctx=m.context(dict(variable=var));value=at(candidates[0][0]);winning=[candidates[0]]
    for region in candidates[1:]:
        other=at(region[0]);s=m.sign(m.add(other,m.neg(value)),ctx)
        if s is None:raise Unsupported('The values at distinct turning points are not yet ordered')
        if s*orientation>0:value=other;winning=[region]
        elif s==0:winning.append(region)
    plan=dict(comparison=mode,witness=witness,integer_sign_runs=runs,positive_integer_start=1)
    if signs[-1]>0:
        if mode!='successive_difference':raise Unsupported('The increasing final tail needs an independent bound')
        num,den=rational_on_tail(expr,var,1)
        if len(num)>len(den):raise Unsupported('The final monotone tail is unbounded in the requested direction')
        limit=q(num[-1]/den[-1]) if len(num)==len(den) else ZERO
        s=m.sign(m.add(limit,m.neg(value)),ctx)
        if s is None or s*orientation>0:raise Unsupported('The final monotone tail can exceed every attained candidate')
        plan['tail_limit']=limit
    return plan,dict(extremum=kind,value=value,all_attaining_indices=winning[0] if len(winning)==1 else winning)


def coefficients(expr, variable, lower):
    numerator, denominator = rational_on_tail(expr, variable, lower)
    poly, remainder = pdiv(numerator, denominator)
    if any(remainder):
        raise NotRational()
    return poly


def periodic_phases(expr, variable):
    """Recognize exact affine angles on integer indices and integral powers of -1."""
    phases={}
    def visit(e):
        op=e[0]
        if op in ('sin','cos'):
            angle=e[1]
            # Cancellation inside an angle must not erase a point from its original domain.
            if any(m.num(guard) in (None,0) for _,guard in domain_conditions(angle)):
                raise Unsupported('Для фазы нужны только постоянные исходные делители')
            scaled=m.substitute(angle,{m.PI:ONE})
            if m.rational_form(m.add(angle,m.neg(m.mul(m.PI,scaled))))[0]:
                raise Unsupported('Аргумент не является рациональным кратным числа π')
            poly=coefficients(scaled,variable,1)
        elif op=='rpow' and e[1]==q(-1):
            poly=coefficients(e[2],variable,1)
            if any(c.denominator!=1 for c in poly):
                raise Unsupported('Целый показатель знакопеременного множителя не доказан')
        else:
            for child in e[1:]:
                if isinstance(child,tuple):visit(child)
            return
        if len(poly)>2 or any(6%c.denominator for c in poly):
            raise Unsupported('Для этой фазы нет правила аффинного рационального угла')
        slope=poly[1] if len(poly)>1 else 0
        phases[e]=(poly[0],slope,(Fraction(slope)/2).denominator)
    visit(expr)
    return phases


def sequence_envelopes(task, library, request):
    """Combine exact subsequence limits. Full-range bounds require additional evidence."""
    from tasks import source
    kind=task.get('kind',task.get('task_type'))
    all_indices=kind=='sequence_range_and_envelopes'
    tails=['liminf','limsup']
    wanted=(['infimum over all positive integer indices','supremum over all positive integer indices']
            if all_indices else [])+tails
    fields={'id','kind','task_type','source_statement','source_number','source_edition','source_pdf_pages',
            'source_exercise_number','source_subpart','transcription_notes','program_status','goal','assumptions'}
    goal=task.get('goal')
    if (not library.data.get('periodic_sequence_envelopes') or set(task)-fields or task.get('transcription_notes')
            or any(task[k]!=kind for k in ('kind','task_type') if k in task)
            or not isinstance(goal,dict) or set(goal)!={'sequence','goals'} or goal['goals']!=wanted
            or not isinstance(goal['sequence'],str)):
        raise Unsupported('Не подтверждены все исходные требования к граням последовательности')
    assumptions=task.get('assumptions')
    match=re.fullmatch(r'([a-zA-Z][a-zA-Z0-9_]*) is a positive integer',assumptions[0]) if isinstance(assumptions,list) and len(assumptions)==1 and isinstance(assumptions[0],str) else None
    if not match:raise Unsupported('Нужно исходное условие положительного целого индекса')
    var=match[1];m.context({'variable':var})
    expression=goal['sequence'];member='x_'+var
    printed=(f'Для {member}={expression} найти inf {member},sup {member},liminf {member},limsup {member}.'
             if all_indices else f'Найти liminf {member} и limsup {member} для {member}={expression}.')
    if task.get('source_statement',printed)!=printed:
        raise Unsupported('Печатная постановка отличается от выражения или полного списка требуемых граней')
    def order_key(v):
        return (0,0) if v=='-inf' else (2,0) if v=='+inf' else (1,rational(v))
    j='j' if var!='j' else 'i'
    index=('v',j)
    try:
        if all_indices:
            inner=dict(kind='sequence_liminf_limsup',goal={'sequence':expression,'goals':tails},assumptions=assumptions)
            proof=request('tail bounds on the exhaustive positive-index partition',inner)
            ends=[];monotone=[]
            period=proof['compilation']['period']
            for row in proof['compilation']['classes']:
                branch=m.parse(row['expression'],j)
                successor=m.substitute(branch,{index:m.add(index,ONE)})
                p,d=rational_on_tail(('add',successor,('mul',q(-1),branch)),j,1)
                # The sign of a rational difference equals that of its numerator times its denominator.
                polynomial=pm(p,d);coeff=translated_coefficients(polynomial,1)
                if min(coeff)<0<max(coeff) and not library.data.get('monotone_integer_segments'):
                    raise Unsupported('Знак первой разности на всей ветви не доказан')
                runs=integer_sign_runs(polynomial,1)
                endpoints=[]
                for j0,_ in runs:
                    value=m.simplify(m.substitute(branch,{index:q(j0)}))
                    rational(value)
                    endpoints.append((row['first_index']+period*(j0-1),value))
                endpoints.append((None,row['limit']))
                ends.extend(endpoints)
                segments=[dict(first_index=a,last_index=b,first_value=va,last_value=vb,difference_sign=s)
                          for (_,s),(a,va),(b,vb) in zip(runs,endpoints,endpoints[1:])]
                monotone.append(dict(first_index=row['first_index'],segments=segments,
                                     difference_sign_coefficients=[str(c) for c in coeff]))
            values=[v for _,v in ends]
            bounds=dict(infimum=min(values,key=order_key),supremum=max(values,key=order_key))
            witnesses={key:min((n for n,v in ends if n is not None and order_key(v)==order_key(value)),default=None)
                       for key,value in bounds.items()}
            return dict(monotone_classes=monotone,attained_at=witnesses),{**proof['value'],**bounds}
        raw=m.parse(expression,var)
        phases=periodic_phases(raw,var)
        period=lcm(*(p for _,_,p in phases.values()))
        rows=[];limits=[]
        for first in range(1,period+1):
            offset=m.add(q(first),m.mul(q(period),m.add(index,q(-1))))
            mapping={('v',var):offset};values=[]
            for atom,(constant,slope,_) in phases.items():
                phase=(constant+slope*first)%2
                value=(q((-1)**int(phase)) if atom[0]=='rpow' else
                       m.simplify((atom[0],m.mul(q(phase),m.PI))))
                rational(value);mapping[atom]=value
                values.append(dict(atom=source(atom),phase=str(phase),value=value))
            branch=m.substitute(raw,mapping)
            rational_on_tail(branch,j,1)  # check the original expression before any cancellation
            reduced=source(m.simplify(branch))
            sub=dict(kind='limit',expression=reduced,variable=j,variable_domain='positive_integers',
                     approach={'point':'+inf','side':'positive_infinity'})
            end=request(f'limit on indices {first} + {period} * ({j}-1)',sub)['value']
            order_key(end);limits.append(end)
            rows.append(dict(first_index=first,index=source(offset),phase_values=values,expression=reduced,limit=end))
        return dict(period=period,classes=rows),dict(liminf=min(limits,key=order_key),limsup=max(limits,key=order_key))
    except (NotRational,Undefined) as exc:
        raise Unsupported('После выделения фаз не доказана рациональная ветвь на всех исходных индексах') from exc


def polynomial_primitive(poly, ratio, variable):
    """Find Q from P by coefficient matching in Q(j)-Q(j-1)/ratio=P(j)."""
    from integrals import polynomial_expression
    degrees = range(1, len(poly)+1) if ratio == 1 else range(len(poly))
    columns = [tuple((Fraction(i == d) - Fraction((-1)**(d-i)*comb(d,i),1)/ratio)
                     for i in range(d+1)) for d in degrees]
    weights = span_coefficients(poly, columns)
    if weights is None:
        raise Unsupported('Не удалось построить дискретную первообразную')
    return polynomial_expression((0,*weights) if ratio == 1 else weights, variable)


def affine_integer_power(raw, index, lower):
    """Return c,r for b^(s*j+d)=c*r^j after checking the original base and exponent."""
    from polynomial import ResourceBound, trim
    base = coefficients(raw[1],index,lower)
    exponent = coefficients(raw[2],index,lower)
    if len(base)!=1 or not base[0] or len(exponent)>2 or any(v.denominator!=1 for v in exponent):
        raise NotRational()
    shift = int(exponent[0])
    slope = int(exponent[1]) if len(exponent)>1 else 0
    bits=max(abs(base[0].numerator).bit_length(),base[0].denominator.bit_length())
    if (bits-1)*max(abs(shift),abs(slope))>=8192:
        raise ResourceBound('Ограничение точной арифметики целой степени')
    coefficient,ratio=base[0]**shift,base[0]**slope
    trim((coefficient,ratio))
    return coefficient,ratio


def sum_factors(raw, index, outer, lower):
    """Separate a bound index, a scalar depending on the endpoint, and a geometric factor."""
    k, n = ('v',index), ('s',outer)
    if not m.contains(raw,k):
        return ONE, m.substitute(raw,{n:('v',outer)}), Fraction(1)
    if raw[0] in ('mul','div'):
        a, x, u = sum_factors(raw[1],index,outer,lower)
        b, y, v = sum_factors(raw[2],index,outer,lower)
        op = raw[0]
        return (op,a,b), (op,x,y), u*v if op=='mul' else u/v
    if m.contains(raw,n):
        raise Unsupported('Вес с внешней переменной пока не отделяется от слагаемого')
    if raw[0]=='rpow':
        try:coefficient,ratio=affine_integer_power(raw,index,lower)
        except NotRational as exc:
            raise Unsupported('Для геометрического множителя требуется ненулевая постоянная и целочисленный аффинный показатель') from exc
        return q(coefficient), ONE, ratio
    return raw, ONE, Fraction(1)


def shifted_fraction(expr, variable, start):
    """Coefficients in t = variable − start, after checking every original divisor."""
    p,d=rational_on_tail(expr,variable,start)
    common=pgcd(p,d)
    p,d=translated_coefficients(pdiv(p,common)[0],start),translated_coefficients(pdiv(d,common)[0],start)
    if d[-1]<0:return tuple(-x for x in p),tuple(-x for x in d)
    return p,d


def bound_data(summand,index,outer,lower,offset):
    kernel,scale,ratio=sum_factors(m.parse(summand,index,[outer]),index,outer,lower)
    if abs(ratio)!=1:
        raise Unsupported('Сравнение рациональных слагаемых требует единичного модуля геометрического множителя')
    start=max(1,lower-1-offset)
    sp,sd=shifted_fraction(scale,outer,start)
    p,d=shifted_fraction(kernel,index,lower)
    if d[0]<=0 or any(c<0 for c in d):
        raise Unsupported('Не доказан положительный знак знаменателя после сдвига')
    # At t = k−lower the positive difference 1/(t+1)−1/(t+2) is 1/((t+1)(t+2)).
    target=pm(p,(2,3,1))
    positive=(ratio==1 and all(c>=0 for c in p) and sd[0]>0 and all(c>=0 for c in sd+sp))
    return d,target,positive,m.simplify(scale),start


def propose_sum_bound(summand,index,outer,lower,offset):
    """Fit a telescoping majorant from the coefficients of the input, without a target limit."""
    d,target,*_=bound_data(summand,index,outer,lower,offset)
    if len(target)>len(d) or any(c and not den for c,den in zip(target,d)):
        raise Unsupported('Для этой степени или набора коэффициентов телескопическая мажоранта не найдена')
    constant=max((abs(c)/den for c,den in zip(target,d) if den),default=Fraction(0))
    return {'constant':q(constant)}


def verify_sum_bound(summand,index,outer,lower,offset,witness):
    """Verify both coefficient inequalities for the supplied witness; do not select a multiplier."""
    from tasks import source
    if not isinstance(witness,dict) or set(witness)!={'constant'}:
        raise Unsupported('Ожидался коэффициент мажоранты')
    c=rational(witness['constant'])
    d,target,positive,scale,start=bound_data(summand,index,outer,lower,offset)
    cd=pm((c,),d)
    minus=pa(cd,tuple(-x for x in target));plus=pa(cd,target)
    if c<0 or any(x<0 for x in minus+plus):
        raise Unsupported('Предъявленная мажоранта не доказана на всём исходном хвосте')
    # As t≥0, these two nonnegative polynomials establish the absolute term bound.
    # Summing the differences from lower to U gives C−C/(U−lower+2), also zero for U=lower−1.
    k,n=('v',index),('v',outer)
    potential=m.div(q(c),m.add(k,q(1-lower)))
    endpoint=m.div(q(c),m.add(n,q(offset-lower+2)))
    envelope=m.mul(q(c),scale if positive else m.simplify(('abs',scale)))
    plan=dict(constant=q(c),start=lower,scalar=source(scale),potential=source(potential),
              terminal_potential=source(endpoint),difference_minus_coefficients=list(map(str,minus)),
              difference_plus_coefficients=list(map(str,plus)),nonnegative_summands=positive)
    value=dict(valid_from=start,lower=source(ZERO if positive else m.neg(envelope)),upper=source(envelope))
    return plan,value


def contraction_domain(variable, parameters, conditions):
    if (not isinstance(parameters,(list,tuple)) or not all(isinstance(p,str) for p in parameters) or
            not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions)):
        raise Unsupported('Нужны фиксированные вещественные параметры и границы их модулей')
    m.context({'variable':variable,'parameters':parameters})
    guards=[re.fullmatch(r'\s*abs\s*\(\s*([A-Za-z_][A-Za-z_0-9]*)\s*\)\s*<\s*1\s*',c) for c in conditions]
    if not all(guards) or {g[1] for g in guards}!=set(parameters):
        raise Unsupported('Для каждого параметра требуется исходное строгое условие |q|<1')


def geometric_prefix(summand,index,outer,lower,offset,parameters,conditions):
    """Check the empty prefix and its forward step without dividing by the base."""
    from tasks import source
    contraction_domain(outer,parameters,conditions)
    term=m.parse(summand,index,[outer,*parameters])
    if (index==outer or index in parameters or term[0]!='rpow' or term[1][0]!='s' or
            term[1][1] not in parameters or term[2]!=('v',index) or lower<0):
        raise Unsupported('Ожидается натуральная степень постоянного основания с неотрицательной нижней границей')
    base=term[1];den=m.add(ONE,m.neg(base));n=('v',outer)
    # Natural powers in a finite polynomial start with the empty product 1, even at zero.
    initial=ONE if lower==0 else m.power(base,lower)
    def closed(first_omitted):
        return ('div',('add',initial,('mul',q(-1),first_omitted)),den)
    witness=('v',index)  # abstract value of q^j at the first omitted index
    step=m.add(closed(m.mul(base,witness)),m.neg(closed(witness)))
    if m.simplify(closed(initial))!=ZERO or m.simplify(m.add(step,m.neg(witness)))!=ZERO:
        raise Unsupported('Не подтверждены база и переход геометрической суммы')
    formula=closed(('rpow',base,m.add(n,q(offset+1))))
    plan=dict(construction='geometric_prefix_by_induction',ratio=source(base),index=index,outer=outer,
              start=lower,upper_offset=offset,valid_from=max(1,lower-1-offset),empty_at_upper=lower-1,
              initial_power=source(initial),step='q^(j+1)=q*q^j for integer j>=0',
              denominator_positive=f'1-{base[1]}>0 by abs({base[1]})<1',prefix_formula=source(formula))
    return plan,[('all',formula)]


def geometric_endpoint(task,library,request):
    """Certify decay or the nonzero divisor required on the requested index set."""
    from tasks import source
    kind=task.get('kind');variable=task.get('variable');params=task.get('parameters')
    common={'kind','variable','variable_domain','parameters','stated_conditions'}
    fields={'base','offset'} if kind=='contracting_integer_power_limit' else {'expression'}
    scope=task.get('scope','all_indices')
    scoped=kind=='contracting_expression_nonzero' and library.data.get('scoped_sequence_nonzero')
    if (not library.data.get('parametrized_integer_powers') or set(task)-({'id','scope'} if scoped else {'id'})!=common|fields or
            scope not in ('all_indices','eventually') or
            task.get('variable_domain')!='positive_integers'):
        raise Unsupported('Не установлены все исходные условия целочисленной степени')
    contraction_domain(variable,params,task['stated_conditions'])
    if kind=='contracting_integer_power_limit':
        base=task['base'];offset=task['offset']
        if base not in params or type(offset) is not int or offset<0:
            raise Unsupported('Модуль основания или положительность целого показателя на всех индексах не доказаны')
        return dict(base=base,exponent_offset=offset,domain='n>=1 integer',
                    zero_base='every positive power is zero',
                    nonzero_base='d=1/abs(q)-1>0; (1+d)^m>=1+m*d by induction',
                    absolute_upper_bound='1/(1+m*d) -> 0 for m=n+offset'),ZERO
    if kind!='contracting_expression_nonzero':raise Unsupported('Неизвестная цель для степеней')
    if not isinstance(task['expression'],str):raise Unsupported('Нужна исходная формула знаменателя')
    raw=m.parse(task['expression'],variable,params)
    try:
        sign,bounds=strict_sequence_sign(raw,variable,params)
    except Unsupported as exc:
        if scope!='eventually':raise
        all_indices_failure=str(exc)
    else:
        return dict(expression=source(raw),scope=scope,strategy='all_indices',sign=sign,polynomial_bounds=bounds,
                    reason='Each nonconstant monomial has modulus <1 on the original domain.'),{'nonzero':True}
    # The limit of the divisor still requires the domains of its own proper subexpressions.
    # Only the constant limiting value is sent to the strict sign checker.
    context={k:task[k] for k in ('variable','variable_domain','parameters','stated_conditions')}
    child=dict(kind='contracting_power_expression_limit',expression=task['expression'],**context)
    domain_basis='defined on an integer tail by recursive finite-limit arithmetic'
    if not params:
        # rf visits all original divisions and rejects an identically zero divisor.
        # Each of finitely many nonzero polynomial denominators has finitely many roots.
        try:rf(raw,variable)
        except Undefined as exc:raise Unsupported('Исходное деление не определено ни на одном хвосте') from exc
        except NotRational:pass
        else:
            child=dict(kind='limit',expression=task['expression'],variable=variable,variable_domain='positive_integers',
                       approach={'point':'+inf','side':'positive_infinity'})
            domain_basis='all original rational divisions checked before cancellation; finitely many polynomial zeros'
    return eventual_nonzero(raw,context,kind,child,domain_basis,all_indices_failure,request)


def eventual_nonzero(raw,context,kind,child,domain_basis,all_indices_failure,request):
    """The same tail theorem applies to any finite nonzero limit on a full tail."""
    from tasks import source
    limit=freeze(request('limit of the original divisor',child)['value'])
    if not isinstance(limit,tuple):raise Unsupported('В этом правиле нужен конечный ненулевой предел исходного делителя')
    role='strict sign of the divisor limit' if kind=='contracting_expression_nonzero' else 'nonzero limiting value'
    sign=request(role,dict(kind=kind,scope='all_indices',
                                                        expression=source(limit),**context))
    if sign['value']!={'nonzero':True}:raise Unsupported('Не доказано ненулевое предельное значение знаменателя')
    return dict(expression=source(raw),scope='eventually',strategy='nonzero_limit',sign=sign['compilation']['sign'],
                limit_expression=source(limit),epsilon=source(m.div(('abs',limit),q(2))),
                threshold='depends_on_fixed_parameters',domain_basis=domain_basis,
                all_indices_failure=all_indices_failure),{'nonzero':True}


def sequence_domain_guards(expr,variable,ctx):
    """Check the unsimplified domain on a full tail, including every internal divisor."""
    from tasks import known_guard,guard_source
    verified=[]
    for relation,guard in domain_conditions(expr):
        if known_guard((relation,guard),ctx):
            basis='fixed real parameters'
        elif guard[0]=='rpow' and m.constant_defined(guard[1],ctx) and m.sign(guard[1],ctx)==1:
            basis='a positive base to a real exponent is positive'
        elif relation=='nonzero':
            try:p,_=rf(guard,variable)
            except (NotRational,Undefined):p=()
            if not any(p):raise Unsupported('Не подтверждена исходная область на целом хвосте: '+guard_source((relation,guard)))
            basis='a nonzero rational function has finitely many zeros and poles'
        else:raise Unsupported('Не доказано условие исходной области: '+guard_source((relation,guard)))
        verified.append(dict(condition=guard_source((relation,guard)),basis=basis))
    return verified


def sequence_expression_goal(task,library,request):
    """Derive a scalar limit or the domain obligation selected by a quotient rule."""
    from operations import expression_positions
    from tasks import source
    keys={'variable','variable_domain','parameters','stated_conditions'}
    kind=task['kind'];nonzero_goal=kind=='sequence_expression_nonzero'
    if (not nonzero_goal and library.data.get('abstract_integral_transitions') and
        'factorial(' in task.get('expression','')):
        try:return factorial_logarithmic_mean(task)
        except Unsupported:pass
    if (not library.data.get('sequence_nonzero_goal') or set(task)-{'id','kind','expression','scope'}!=keys or
            not isinstance(task.get('expression'),str) or task['variable_domain']!='positive_integers' or
            not isinstance(task['parameters'],(list,tuple)) or not all(isinstance(p,str) for p in task['parameters']) or
            not isinstance(task['stated_conditions'],(list,tuple)) or not all(isinstance(c,str) for c in task['stated_conditions'])):
        raise Unsupported('Требуется выражение на натуральных индексах с объявленными постоянными параметрами')
    scope=task.get('scope','eventually')
    if scope not in ('all_indices','eventually') or ('scope' in task and not nonzero_goal):
        raise Unsupported('Неподдерживаемая область утверждения о последовательности')
    v=task['variable'];params=task['parameters'];conditions=task['stated_conditions']
    context={k:task[k] for k in keys}
    unit_bound=r'\s*abs\s*\(\s*([A-Za-z_][A-Za-z_0-9]*)\s*\)\s*<\s*1\s*'
    scalar_conditions=[re.sub('^'+unit_bound+'$',r'1-abs(\1)>0',c) for c in conditions]
    infinity=dict(point='+inf',side='positive_infinity')
    scalar=dict(variable=v,variable_domain='positive_integers',parameters=params,parameter_conditions=scalar_conditions,approach=infinity)
    ctx=m.context(scalar);raw=m.parse(task['expression'],v,params)
    if nonzero_goal and params and all(re.fullmatch(unit_bound,c) for c in conditions):
        bounded={re.fullmatch(unit_bound,c)[1] for c in conditions}
        if bounded==set(params) and all(e[0] in ('q','s','v','add','mul','div','pow') or
                e[0]=='rpow' and e[1][0]=='s' for _,e in expression_positions(raw)):
            return geometric_endpoint({**task,'kind':'contracting_expression_nonzero','scope':scope},library,request)
    if nonzero_goal:
        if not m.variable_in(raw):
            if not m.constant_defined(raw,ctx) or not m.nonzero(raw,ctx):
                raise Unsupported('Фиксированное значение не доказано отличным от нуля в исходной области')
            return dict(expression=source(raw),scope=scope,strategy='fixed_value',sign=m.sign(raw,ctx)),{'nonzero':True}
        if scope!='eventually':
            raise Unsupported('Ненулевой предел не даёт ненулевость в каждом индексе')
        child=dict(kind='sequence_expression_limit',expression=task['expression'],**context)
        return eventual_nonzero(raw,context,kind,child,'original sequence defined on a full tail',
                                'no pointwise proof assumed',request)
    guards=sequence_domain_guards(raw,v,ctx)
    plan=dict(domain_guards=guards,variable=v)
    # A right-hand real limit applies along any positive mesh tending to zero.
    # Only change coordinates if every occurrence of the index is accounted for.
    powers=dict.fromkeys(e for _,e in expression_positions(raw)
                         if e[0]=='rpow' and e[2]==('v',v) and m.num(e[1]) is not None)
    t='t'
    while t==v or t in params:t+='_'
    for power in powers:
        base=m.num(power[1])
        if base<=0 or base==1:continue
        var=('v',t);replacement=var if base<1 else ('div',ONE,var)
        changed=m.substitute(raw,{power:replacement})
        if m.contains(changed,('v',v)):continue
        # All guards of the raw chart must hold for sufficiently small positive t.
        # These guard proofs work on either punctured tail (finitely many real zeros).
        chart_guards=sequence_domain_guards(changed,t,ctx)
        ratio=min(base,1/base)
        plan.update(strategy='geometric_mesh',mesh_variable=t,mesh_ratio=source(q(ratio)),
                    bernoulli_increment=source(q(1/ratio-1)),chart_domain_guards=chart_guards,
                    raw_chart=source(changed))
        scalar.update(variable=t,variable_domain='real',approach=dict(point='0',side='right'))
        expression=source(m.simplify(changed))
        break
    else:
        plan['strategy']='direct_limit';expression=task['expression']
    value=freeze(request('scalar limit on the proved domain',dict(kind='limit',expression=expression,**scalar))['value'])
    if not isinstance(value,tuple) or not m.constant_defined(value,ctx):
        raise Unsupported('Требуется конечное значение предела при заданных параметрах')
    return plan,value


def strict_sequence_sign(raw,variable,params):
    """Certify the raw domain and strict sign for every positive integer."""
    from tasks import source
    def admitted(e):
        if e[0]=='s' and e[1] in params:return True
        if e[0]=='rpow' and e[1][0]=='s' and e[1][1] in params:
            poly=coefficients(e[2],variable,1)
            return len(poly)<=2 and all(v.denominator==1 for v in poly) and all(v>=0 for v in poly[1:]) and sum(poly)>=1
        return False
    bounds={}
    def polynomial_sign(poly):
        constant=poly.get((),0);terms=[(mon,c) for mon,c in poly.items() if mon]
        radius=sum(abs(c) for _,c in terms)
        if not constant or abs(constant)<radius:return 0
        if not all(all(k>0 and admitted(atom) for atom,k in mon) for mon,_ in terms):return 0
        if terms:bounds[source(m.poly_expr(poly))]={'constant':str(constant),'strict_error_bound':str(radius)}
        return 1 if constant>0 else -1
    def sign(e):
        if e[0] in ('mul','div'):
            left,right=sign(e[1]),sign(e[2])
            if left and right:return left*right
        numerator,denominator=m.rational_form(e)
        return polynomial_sign(numerator)*polynomial_sign(denominator)
    # Check the original tree before taking a rational normal form that can erase poles.
    def domain(e):
        if e[0] in ('q','s','v'):return
        if e[0]=='rpow':
            if not admitted(e):raise Unsupported('Не доказан модуль целочисленной степени на всей области')
        elif e[0] in ('mul','div','add','pow'):
            domain(e[1])
            if e[0]!='pow':domain(e[2])
            if (e[0]=='div' and not sign(e[2])) or (e[0]=='pow' and e[2]<=0 and not sign(e[1])):
                raise Unsupported('Не доказана исходная область вложенного деления или степени')
        else:raise Unsupported('Операция выходит за область проверки геометрических степеней')
    try:
        domain(raw);checked=sign(raw)
    except (ZeroDivisionError,NotRational,Undefined) as exc:
        raise Unsupported('Не удалось установить знак на всей исходной области') from exc
    if not checked:raise Unsupported('Строгий знак знаменателя не следует из границ модулей')
    return checked,bounds


def generated_sum_branches(summand, index, outer, lower, offset, parameters=(), conditions=()):
    """Construct an auxiliary prefix identity, then substitute its actual upper bound."""
    from tasks import source, rational_sum_potential
    if parameters or conditions:
        return geometric_prefix(summand,index,outer,lower,offset,parameters,conditions)
    k, n = ('v',index), ('v',outer)
    term = m.parse(summand,index,[outer])
    kernel, scale, ratio = sum_factors(term,index,outer,lower)
    rational_on_tail(scale,outer,1)
    scale = m.simplify(scale)
    def at(expr, arg):
        return m.simplify(m.substitute(expr,{k:arg}))
    plan = dict(index=index, outer=outer, start=lower, upper_offset=offset,
                valid_from=max(1,lower-1-offset), empty_at_upper=lower-1,
                scalar=source(scale), kernel=source(kernel), ratio=source(q(ratio)))
    try:
        poly = coefficients(kernel,index,lower)
    except NotRational:
        if ratio != 1:
            raise Unsupported('Рациональная амплитуда геометрического множителя требует другого разложения')
        r = rational_sum_potential(kernel,index,lower)
        coeff = m.neg(at(r,m.add(k,ONE)))
        plan.update(construction='rational_antidifference',forward_potential=source(r))
    else:
        coeff = polynomial_primitive(poly,ratio,index)
        difference = m.add(coeff,m.neg(m.div(at(coeff,m.add(k,q(-1))),q(ratio))))
        if coefficients(difference,index,lower) != poly:
            raise Unsupported('Разностное тождество для предложенного многочлена не подтверждено')
        plan.update(construction='geometric_polynomial_antidifference' if ratio!=1 else 'polynomial_antidifference',
                    checked_difference=source(difference))
    initial = m.mul(q(ratio**(lower-1)),at(coeff,q(lower-1)))
    witness = coeff if ratio==1 else m.mul(('rpow',q(ratio),k),coeff)
    closed_form = m.add(witness,m.neg(initial))
    plan.update(coefficient=source(coeff),initial_value=source(initial),
                discrete_primitive=source(witness),prefix_formula=source(closed_form))
    if ratio == 1 and plan['construction']=='polynomial_antidifference':
        plan['identity_task'] = dict(kind='prove', goal={'proposition':
            f'sum({index},{lower},{outer},{source(kernel)})={source(at(closed_form,n))}'},
            assumptions=[f'{outer} is an integer >= {lower}'])
    branches = []
    for label, stride, residue in ([('even',2,0),('odd',2,1)] if ratio<0 else [('all',1,0)]):
        endpoint = m.add(m.mul(q(stride),n),q(residue))
        upper = m.add(endpoint,q(offset))
        base = ratio**stride
        geometric = ONE if base==1 else ('exp',m.mul(n,('ln',q(base))))
        factor = m.mul(q(ratio**(residue+offset)),geometric)
        prefix = m.add(m.mul(factor,at(coeff,upper)),m.neg(initial))
        value = m.mul(m.substitute(scale,{n:endpoint}),prefix)
        branches.append((label,value))
    return plan, branches


def prefix_occurrences(expression):
    """Read independent binders, retaining the surrounding operations verbatim."""
    if not isinstance(expression,str) or len(expression)>4000:
        raise Unsupported('Неверная запись выражения с суммой')
    name=r'[A-Za-z_][A-Za-z_0-9]*'
    start=re.compile(r'\bsum\s*(?:\(|_\{)')
    cursor=0
    while match:=start.search(expression,cursor):
        printed=match[0].endswith('{')
        header=(rf'({name})\s*=\s*(-?\d+)\}}\^({name})\s*\(' if printed else
                rf'\s*({name})\s*,\s*(-?\d+)\s*,\s*({name})\s*([+-]\s*\d+)?\s*,\s*')
        head=re.match(header,expression[match.end():])
        if not head:raise Unsupported('Не распознаны индекс и границы суммы')
        index,lower,outer=head.groups()[:3]
        offset=0 if printed or not head[4] else int(re.sub(r'\s+','',head[4]))
        begin=match.end()+head.end();end=begin;depth=1
        while depth and end<len(expression):
            depth+=(expression[end]=='(')-(expression[end]==')');end+=1
        if depth:raise Unsupported('Нет закрывающей скобки у конечной суммы')
        term=expression[begin:end-1]
        if printed:
            power=re.match(r'\^\d+',expression[end:])
            term='('+term+')'+(power[0] if power else '')
            if power:end+=power.end()
        if start.search(term):raise Unsupported('Вложенные индексы в слагаемом требуют отдельного связывания')
        yield match.start(),end,index,int(lower),outer,offset,term
        cursor=end


def replace_prefixes(expression, outer, request, printed=None, parameters=(), conditions=(), divisor_scope=None):
    """Prove each binder before putting its value into the unmodified outer arithmetic."""
    from tasks import prefix_question,source,project_parameter_context
    substitutions={};parts=[];cursor=0;facts=[]
    if printed is not None:printed=re.sub(r'\s+','',printed)
    for i,(begin,end,index,lower,endpoint,offset,term) in enumerate(prefix_occurrences(expression)):
        if endpoint!=outer or 1+offset<lower-1:raise Unsupported('Граница суммы выходит за исходный диапазон индекса')
        marker='__prefix'+str(i)
        while marker in expression or printed and marker in printed:marker+='_'
        parts.extend([expression[cursor:begin],'('+marker+')']);cursor=end
        if printed is not None:
            # Require an ellipsis to be an entire additive block with the correct end term.
            def at(arg):return re.sub(r'\b'+re.escape(index)+r'\b',lambda _:arg,term).replace(' ','')
            if offset:raise Unsupported('Не сопоставлена печатная граница суммы со сдвигом')
            dots=at(str(lower))+'+'+at(str(lower+1))+'+...+'+at(outer)
            printed=printed.replace('…','...')
            if printed==dots:printed=marker
            elif '('+dots+')' in printed:printed=printed.replace('('+dots+')','('+marker+')',1)
            else:raise Unsupported('Печатный блок с многоточием расходится со слагаемым или границами')
        question=prefix_question(term,index,outer,lower,offset,parameters,conditions) if parameters else prefix_question(term,index,outer,lower,offset)
        result=request('closed form of embedded sum '+str(i+1),question)['value']
        if result['valid_from']!=1 or [b['indices'] for b in result['branches']]!=['all']:
            raise Unsupported('Для подстановки требуется единая формула на всех исходных натуральных индексах')
        canonical_outer=question['variable'];branch=result['branches'][0]
        value=m.substitute(m.parse(branch['expression'],canonical_outer,parameters),{('v',canonical_outer):('v',outer)})
        substitutions['s',marker]=value
        facts.append({'sum':expression[begin:end],'formula':source(value)})
    names=[key[1] for key in substitutions]+list(parameters)
    context=m.parse(''.join(parts)+expression[cursor:],outer,names)
    if printed is not None and m.parse(printed,outer,names)!=context:
        raise Unsupported('Операции над суммами в печатном утверждении отличаются')
    raw=m.substitute(context,substitutions)
    if parameters:
        original={key:'('+fact['sum']+')' for key,fact in zip(substitutions,facts)}
        def visit(e):
            for child in e[1:]:
                if isinstance(child,tuple):visit(child)
            if e[0]=='div' or e[0]=='pow' and e[2]<=0:
                den=e[2] if e[0]=='div' else e[1]
                expanded=m.substitute(den,substitutions)
                original_text=source(den)
                for marker,text in original.items():
                    original_text=re.sub(r'\b'+re.escape(marker[1])+r'\b',lambda _:text,original_text)
                goal=dict(kind='contracting_expression_nonzero',expression=source(expanded),variable=outer,
                          variable_domain='positive_integers',**project_parameter_context(expanded,parameters,conditions))
                if divisor_scope is not None:goal['scope']=divisor_scope
                if request('nonzero original divisor '+original_text,goal)['value']!={'nonzero':True}:
                    raise Unsupported('Отсутствует свидетельство ненулевого исходного знаменателя')
        visit(context)
        return source(raw),facts
    try:rational_on_tail(raw,outer,1)
    except (NotRational,Undefined) as exc:raise Unsupported('Не доказана исходная область после подстановки формулы суммы') from exc
    return source(raw),facts


def cauchy_term_majorant(term,index,lower):
    """Remove bounded numerator factors only after proving their phases exist at every index."""
    from tasks import source
    waves=[]
    def defined(phase):
        if phase[0] in ('sin','cos'):return defined(phase[1])
        if phase[0]=='factorial':
            p=translated_coefficients(coefficients(phase[1],index,lower),lower)
            if not all(c.denominator==1 and c>=0 for c in p):
                raise Unsupported('Аргумент факториала не подтверждён как целый неотрицательный на всех индексах')
            return
        rational_on_tail(phase,index,lower)
    def reduce(t):
        if t[0] in ('sin','cos'):
            defined(t[1])
            waves.append(dict(function=t[0],phase=source(t[1]),valid_from=lower))
            return ONE
        if t[0]=='mul':return ('mul',reduce(t[1]),reduce(t[2]))
        if t[0]=='div':return ('div',reduce(t[1]),t[2])
        return t
    return reduce(term),waves


def check_printed_cauchy(task,term,index,lower,outer,offset,allow_discrete=False):
    """Bind an ellipsis to the given term and verify any printed advice independently."""
    statement=task['source_statement'];goal=task['goal']
    head=f'Критерием Коши доказать сходимость x_{outer}='
    if not isinstance(statement,str) or not statement.startswith(head):
        raise Unsupported('Не связано печатное требование критерия Коши')
    seq,_,advice=statement[len(head):].partition('. Указание:')
    seq=seq.removesuffix('.').replace('…','...')
    hint=goal.get('source_hint')
    if bool(advice)!=('source_hint' in goal):raise Unsupported('Не установлено соответствие печатного указания')
    k=('v',index)
    def numeric_parts(e):
        parts=tuple(numeric_parts(x) if isinstance(x,tuple) else x for x in e[1:])
        value=(e[0],*parts)
        if e[0]=='div' and parts[1]==ZERO or e[0]=='pow' and parts[0]==ZERO and parts[1]<=0:
            raise Undefined()
        if e[0]=='rpow' and parts[0][0]==parts[1][0]=='q' and parts[1][2]==1 and 0<parts[1][1]<=m.MAX_INTEGER_POWER:
            return m.power(parts[0],parts[1][1])
        if e[0] in ('add','mul','div','pow','rpow') and all(not isinstance(p,tuple) or p[0]=='q' for p in parts):
            return m.simplify(value)
        return value
    def same(text,arg):
        if allow_discrete:text=re.sub(r'\b([A-Za-z_]\w*|\d+)!',r'factorial(\1)',text)
        printed=m.parse(text,index,(),('factorial',) if allow_discrete else ())
        actual=m.substitute(term,{k:arg})
        if allow_discrete and numeric_parts(printed)==numeric_parts(actual):return True
        p,d=rational_on_tail(printed,index,lower)
        a,b=rational_on_tail(actual,index,lower)
        return pm(p,b)==pm(a,d)
    if seq!=goal['sequence']:
        initial,dots,last=seq.partition('+...+')
        if not dots or not all(same(s,q(i)) for i,s in enumerate(initial.split('+'),lower)):
            raise Unsupported('Начальные члены печатной последовательности расходятся с формулой')
        if not same(re.sub(r'\b'+re.escape(outer)+r'\b',index,last),m.add(k,q(offset))):
            raise Unsupported('Конечное слагаемое печатной последовательности расходится с формулой')
    if not advice:return
    compact=lambda s:re.sub(r'\s+','',s)
    printed=re.sub(r'\b'+re.escape(outer)+r'\b',index,advice.removesuffix('.').replace('при','for'))
    if not isinstance(hint,str) or compact(printed)!=compact(hint):
        raise Unsupported('Печатная подсказка расходится с записью условия')
    inequality=re.fullmatch(r'(.+?)(<=|<)(.+?)\s+for\s+'+re.escape(index)+r'\s*>=\s*(-?\d+)',hint)
    if not inequality:raise Unsupported('Не разобраны знак, выражения или область исходной подсказки')
    lhs,rel,rhs,start=inequality.groups();start=int(start)
    if start<lower:raise Unsupported('Область подсказки выходит за область слагаемого')
    difference=('add',m.parse(rhs,index),('mul',q(-1),m.parse(lhs,index)))
    p,d=shifted_fraction(difference,index,start)
    if not same(lhs,k) or d[0]<=0 or any(c<0 for c in d+p) or rel=='<' and p[0]<=0:
        raise Unsupported('Печатная оценка не следует на всём заявленном целочисленном хвосте')


def integer_power_form(expr, index, start):
    """Normalize fixed-base powers on an integer tail, checking divisors before simplification."""
    def visit(e):
        op=e[0]
        if op in ('v','q'):return e
        if op=='rpow':
            coefficient,ratio=affine_integer_power(e,index,start)
            atom=ONE if ratio==1 else ('rpow',q(ratio),('v',index))
            return ('mul',q(coefficient),atom)
        if op not in ('add','mul','div','pow'):raise NotRational()
        if op=='div' or op=='pow' and e[2]<=0:
            denominator=e[2] if op=='div' else e[1]
            rational_on_tail(('div',ONE,denominator),index,start)
        return (op,visit(e[1]),e[2] if op=='pow' else visit(e[2]))
    return m.simplify(visit(expr))


def printed_requirement(statement, proposition, index, upper, lower, offset, term, formula):
    """Bind an optional printed method and check its equation against the typed goal."""
    instructions = re.fullmatch(r'(Методом математической индукции доказать|Доказать|Prove)\s*:?\s+(.+?)\.?', statement.strip(), re.I)
    if not instructions:
        raise Unsupported('Не распознано требование исходного утверждения')
    equation = re.sub(r'\s+', '', instructions[2])
    if equation != re.sub(r'\s+', '', proposition):
        parts = equation.split('=')
        first,dots,last=parts[0].replace('…','...').partition('+...+')
        if len(parts) != 2 or not dots or not last:
            raise Unsupported('Печатное равенство не согласовано с формулой суммы')
        def printed(text):
            text=re.sub(r'(?<=\d)(?='+re.escape(upper)+r'\b)', '*', text)
            return m.parse(re.sub(r'(?<=[\w)])(?=\()', '*', text), upper)
        prefixes=[];depth=left=0
        for i,char in enumerate(first):
            if char=='(':depth+=1
            elif char==')':depth-=1
            elif char=='+' and depth==0:
                prefixes.append(first[left:i]);left=i+1
        prefixes.append(first[left:])
        args=[q(n) for n in range(lower,lower+len(prefixes))]+[m.add(('v',upper),q(offset))]
        targets=[m.substitute(term,{('v',index):arg}) for arg in args]+[formula]
        for text, expected in zip([*prefixes,last,parts[1]],targets):
            have=printed(text)
            try:
                p,d = rational_on_tail(have,upper,lower-offset)
                u,v = rational_on_tail(expected,upper,lower-offset)
                equal=pm(p,v)==pm(u,d)
            except NotRational:
                equal=integer_power_form(have,upper,lower-offset)==integer_power_form(expected,upper,lower-offset)
            if not equal:
                raise Unsupported('Печатное равенство отличается от исходной цели')
    return 'induction' if instructions[1].lower().startswith('методом') else None


def compile_sum(task):
    fields = {'id','kind','task_type','goal','assumptions','method_requirement','requested_output',
              'source_number','source_edition','source_pdf_page','source_statement','program_status','transcription_notes'}
    if (set(task) - fields or task.get('transcription_notes') or
            any(task[k] not in ('proof','prove') for k in ('kind','task_type') if k in task) or
            task.get('requested_output',['proof']) != ['proof']):
        raise Unsupported('Остались дополнительные условия или требования к доказательству')
    goal = task.get('goal')
    if not isinstance(goal,dict) or set(goal) != {'proposition'} or not isinstance(goal['proposition'],str):
        raise Unsupported('Нужно явно заданное утверждение')
    proposition = goal['proposition']
    name = r'[A-Za-z_][A-Za-z_0-9]*'
    match = re.fullmatch(rf'\s*sum\(\s*({name})\s*,\s*(-?\d+)\s*,\s*({name})\s*([+-]\s*\d+)?\s*,\s*([^=]+)\)\s*=\s*([^=]+)\s*', proposition)
    if not match or len(proposition)>4000:
        raise Unsupported('В этом правиле ожидается равенство конечной суммы и выражения')
    index, start, upper, shift, summand, expression = match.groups()
    if index == upper:
        raise Unsupported('Связанный индекс суммы должен отличаться от верхней границы')
    for symbol in (index, upper):
        m.context({'variable':symbol})
    lower = int(start)
    offset = int(re.sub(r'\s+','',shift)) if shift else 0
    base_index = lower-offset
    assumptions = task.get('assumptions')
    if not isinstance(assumptions,list) or len(assumptions)!=1 or not isinstance(assumptions[0],str):
        raise Unsupported('Требуется исходная область целого индекса')
    condition = assumptions[0].strip()
    explicit = re.fullmatch(re.escape(upper)+r' is an integer\s*(?:>=|≥)\s*(-?\d+)', condition)
    begin = {upper+' is a positive integer':1, upper+' is a nonnegative integer':0}.get(condition)
    if explicit:
        begin = int(explicit[1])
    if begin is None or begin < base_index:
        raise Unsupported('Не установлена область всех целых индексов начиная с нижней границы')
    term, formula = m.parse(summand,index), m.parse(expression,upper)
    fresh = 'j'
    while fresh in (index, upper):
        fresh += '_'
    method = task.get('method_requirement')
    if method not in (None,'induction','mathematical_induction','telescoping'):
        raise Unsupported('Не поддержан запрошенный метод доказательства')
    if method == 'mathematical_induction':
        method = 'induction'
    try:
        for expr,symbol,first in ((term,index,lower),(formula,upper,base_index)):
            try:rational_on_tail(expr,symbol,first)
            except NotRational:integer_power_form(expr,symbol,first)
        if 'source_statement' in task:
            if not isinstance(task['source_statement'],str):
                raise Unsupported('Неверный текст исходного условия')
            printed = printed_requirement(task['source_statement'],proposition,index,upper,lower,offset,term,formula)
            if printed and method and printed != method:
                raise Unsupported('Противоречивые требования к методу')
            method = printed or method
    except (Undefined, NotRational) as exc:
        raise Unsupported('Не установлена допустимая форма выражений на исходном целочисленном хвосте') from exc
    arg = ('v',fresh)
    ctx = dict(variable=fresh, parameters=[], domain='integer_sum'+('_'+method if method else ''),
               quantified_variable=upper, integer_start=begin, sum_start=base_index)
    return {'context':ctx, 'goal':('finite_sum_identity',m.substitute(term,{('v',index):m.add(arg,q(offset))}),
                                    m.substitute(formula,{('v',upper):arg}),q(base_index))}


def geometric_series_certificate(task):
    """Sum the tail in an invariant real plane, or over a complete period of coefficients."""
    from integrals import affine
    from tasks import source
    from verify import same_value
    index=task['index']; n=('v',index); start=task['start_index']
    params=task.get('parameters',[]); conditions=task.get('stated_conditions',[])
    if start<0:raise Unsupported('The initial integer power may be negative')
    ctx=m.context(dict(variable=index,parameters=params))
    def inside_disk(ratio):
        ratio=m.simplify(ratio)
        q0=m.num(ratio)
        if q0 is not None and abs(q0)<1 and not conditions:return True
        return (m.constant_defined(ratio,ctx) and isinstance(conditions,(tuple,list))
                and list(conditions)==['abs('+source(ratio)+')<1'])
    pattern=r'periodic_sign\(('+re.escape(index)+r'),\[(-?\d+(?:,-?\d+)*)\]\)/([1-9]\d*)\^'+re.escape(index)
    periodic=re.fullmatch(pattern,task['term'].replace(' ',''))
    if periodic:
        cycle=[int(k) for k in periodic[2].split(',')];r=q(1,int(periodic[3]))
        if not inside_disk(r):raise Unsupported('The geometric block must contract')
        block=sum(Fraction(cycle[(start+j)%len(cycle)])*m.num(r)**j for j in range(len(cycle)))
        value=m.num(r)**start*block/(1-m.num(r)**len(cycle))
        return dict(theorem='method.geometric_series_tail',cycle=cycle,ratio=r,start=start,
                    block_sum=q(block),block_ratio=m.power(r,len(cycle)),
                    tail='arbitrary residual block bounded by max|c_j| r^N/(1-r)'),q(value)
    # Split products of floor-indexed powers into residue classes on the original lattice.
    if 'floor(' in task['term']:
        iv=re.escape(index)
        pattern=r'([A-Za-z]\w*)\^floor\((?:'+iv+r'/([1-9]\d*)|\('+iv+r'\+(\d+)\)/([1-9]\d*))\)'
        raw=task['term'].replace(' ','');terms=[re.fullmatch(pattern,t) for t in raw.split('*')]
        if start!=0 or not all(terms):raise Unsupported('Only a common nonnegative residue lattice is proved')
        data=[(t[1],int(t[3] or 0),int(t[2] or t[4])) for t in terms];period=data[0][2]
        if not 1<=period<=64 or any(name not in params or d!=period for name,_,d in data):
            raise Unsupported('Unresolved residue lattice or undeclared base')
        ratio=ONE
        for name,_,_ in data:ratio=m.mul(ratio,('s',name))
        # Reparse the explicit bound to allow different ordering of the factors.
        if len(conditions)!=1:raise Unsupported('A strict geometric contraction of each residue sequence is required')
        given=re.fullmatch(r'abs\(([^()]+)\)<1',conditions[0].replace(' ',''))
        if not given or not re.fullmatch(r'[A-Za-z]\w*(?:\*[A-Za-z]\w*)*',given[1]) or not same_value(ratio,m.parse(given[1],None,params)):
            raise Unsupported('The bound must apply to the actual block ratio')
        initial=[]
        for j in range(period):
            value=ONE
            for name,b,_ in data:value=m.mul(value,m.power(('s',name),(j+b)//period))
            initial.append(value)
        total=ZERO
        for value in initial:total=m.add(total,value)
        return dict(theorem='method.geometric_series_tail',cycle=initial,block_sum=total,block_ratio=ratio,start=start,
                    floors=data,tail='finite residue block, each class bounded by a fixed multiple of |ratio|^N'),m.div(total,m.add(ONE,m.neg(ratio)))
    expr=m.parse(task['term'],index,params)
    if expr[0]=='mul':
        a,b=expr[1:]
        wave,geom=(a,b) if a[0] in ('sin','cos') else (b,a)
        inverse=False
    elif expr[0]=='div':wave,geom=expr[1:];inverse=True
    else:raise Unsupported('No geometric weight and angular character')
    if wave[0] not in ('sin','cos') or geom[0]!='rpow' or geom[2]!=n or m.contains(geom[1],n):
        raise Unsupported('The index must occur as an integer exponent and an affine phase')
    base=geom[1]
    if not m.constant_defined(base,ctx) or inverse and m.sign(base,ctx) not in (-1,1):
        raise Unsupported('Unproved domain of the original geometric weight')
    r=m.div(ONE,base) if inverse else m.simplify(base)
    if not inside_disk(r):raise Unsupported('Need an established strict bound on the geometric ratio')
    if any(m.contains(g,n) or not m.constant_defined(g,ctx) or
           (op=='nonzero' and m.sign(g,ctx) not in (-1,1)) or
           (op=='positive' and m.sign(g,ctx)!=1) or
           (op=='nonnegative' and not m.known_nonnegative(g,ctx)) for op,g in domain_conditions(wave[1])):
        raise Unsupported('The phase must be defined at every source index')
    step,offset=affine(wave[1],index)
    if not all(m.constant_defined(z,ctx) for z in (step,offset)):raise Unsupported('The phase has a singular coefficient')
    c=m.simplify(('cos',step));s=m.simplify(('sin',step));u=m.add(ONE,m.neg(m.mul(r,c)));w=m.mul(r,s)
    determinant=m.add(m.power(u,2),m.power(w,2))
    phi=m.add(m.mul(q(start),step),offset);cos0=m.simplify(('cos',phi));sin0=m.simplify(('sin',phi))
    if wave[0]=='cos':numerator=m.add(m.mul(u,cos0),m.neg(m.mul(w,sin0)))
    else:numerator=m.add(m.mul(u,sin0),m.mul(w,cos0))
    value=m.div(m.mul(m.power(r,start),numerator),determinant)
    return dict(theorem='method.geometric_series_tail',ratio=r,angle_step=step,phase_start=phi,component=wave[0],
                inverse_rotation=[u,w],determinant=determinant,denominator_guard='1-r cos(theta) >= 1-|r| > 0',
                finite_identity='(1-z) sum(z^j,j=0..N-1) = 1-z^N by cancellation',
                tail='the residual vector has norm bounded by |r|^N/(1-|r|)'),m.simplify(value)


def shifted_series_certificate(task,request):
    """Seek a discrete difference among translates of the same elementary function."""
    from integrals import affine
    from tasks import source
    from verify import same_value
    index=task['index'];n=('v',index);start=task['start_index']
    if task.get('parameters') or task.get('stated_conditions') or start<1:raise Unsupported('Starting domain for the translates is unresolved')
    raw=m.parse(task['term'],index);coeffs={};template=None
    def visit(e,c):
        nonlocal template
        if e[0]=='add':visit(e[1],c);visit(e[2],c);return
        if e[0]=='mul' and m.num(e[1]) is not None:visit(e[2],c*m.num(e[1]));return
        if e[0] not in ('sqrt','ln','cbrt'):raise Unsupported('No common family of translates')
        a,b=affine(e[1],index);j=m.num(b)
        if a!=ONE or j is None or j.denominator!=1 or start+j<=0 or domain_conditions(e[1]):
            raise Unsupported('An original translate has an unproved domain')
        if template is not None and template!=e[0]:raise Unsupported('Different translated families')
        template=e[0];coeffs[int(j)]=coeffs.get(int(j),0)+c
    visit(raw,Fraction(1))
    if not coeffs or sum(coeffs.values()) or max(coeffs)-min(coeffs)>128:
        raise Unsupported('The translation coefficients do not give a finite difference')
    prefix=0;witness=ZERO
    for j in range(min(coeffs),max(coeffs)):
        prefix-=coeffs.get(j,0)
        if prefix:witness=m.add(witness,m.mul(q(prefix),(template,m.add(n,q(j)))))
    shift=m.substitute(witness,{n:m.add(n,ONE)})
    if not same_value(m.add(shift,m.neg(witness)),raw):raise Unsupported('Finite antidifference does not match the original term')
    end=request('limit of the discovered finite-difference boundary',dict(kind='limit',variable=index,expression=source(shift),
                variable_domain='positive_integers',approach=dict(point='+inf',side='positive_infinity')))['value']
    if end in ('+inf','-inf'):raise Unsupported('The proposed boundary has no finite limit')
    first=m.simplify(m.substitute(witness,{n:q(start)}))
    return dict(theorem='method.translated_series_difference',witness=witness,initial=first,upper=shift),m.add(freeze(end),m.neg(first))



def check_series_heading(task):
    method=task.get('method_requirement')
    printed=task.get('source',{})
    meta={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','pdf_pages','page_png_sha256','printed_instruction','literal_requirement','method_requirement','explicit_required_method','explicit_imposed_method'}
    if not isinstance(printed,dict) or set(printed)-meta:raise Unsupported('Additional printed information must be bound')
    headings={'Исследовать сходимость рядов':(None,'general_convergence_tests','comparison_or_ratio_or_root'),
              'Пользуясь признаками сравнения, Даламбера или Коши, исследовать сходимость ряда':('comparison_or_ratio_or_root',),
              'Пользуясь признаками Раабе и Гаусса, исследовать сходимость ряда':('raabe_and_gauss',)}
    for k in ('literal_requirement','printed_instruction'):
        if k in printed and method not in headings.get(printed[k].rstrip('.'),()):
            raise Unsupported('Printed criterion and executable choice disagree')


def exceptional_series_comparison(task):
    """Dominate sparse classes by p-series, and finite products by geometric tails."""
    from math import isqrt
    from tasks import source
    index=task['index'];start=task['start_index'];params=task.get('parameters',[])
    if (type(start)!=int or start<1 or task.get('index_domain','integers')!='integers' or task.get('transcription')
            or task.get('method_requirement') not in (None,'general_convergence_tests','comparison_or_ratio_or_root')
            or set(task.get('requested_output',()))-{'convergence_classification','justification','absolute_convergence','conditional_convergence'}):
        raise Unsupported('The comparison does not establish every requested method, domain and conclusion')
    check_series_heading(task)
    conditions=task.get('stated_conditions',[])
    ctx=m.context(dict(variable=index,parameters=params,parameter_conditions=conditions));n=('v',index)
    def limit(expr,var,parameters=(),given=()):
        return dict(kind='limit',variable=var,expression=source(expr),parameters=list(parameters),stated_conditions=list(given),
                    variable_domain='positive_integers',approach=dict(point='+inf',side='positive_infinity'))
    text=task['term']
    sparse=re.fullmatch(r'piecewise\((.+) if (\w+) is perfect square else (.+)\)',text)
    plan=dict(criterion='exceptional_comparison',index=index,start_index=start)
    if sparse:
        if sparse[2]!=index:raise Unsupported('The sparse-index predicate is not bound')
        special,regular=(m.parse(s,index,params) for s in (sparse[1],sparse[3]))
        first=isqrt(start-1)+1
        subsequence=m.substitute(special,{n:m.power(n,2)})
        powers=[]
        try:
            for term,lo in ((regular,start),(subsequence,first)):
                a,b=rational_on_tail(term,index,lo)
                if any(a):powers.append(len(b)-len(a))
        except (NotRational,Undefined) as exc:raise Unsupported('A bound or original domain for a sparse subseries is missing') from exc
        p=min(powers,default=2)
        if p<=1:raise Unsupported('One comparison subseries is not summable by this bound')
        square_sum=m.mul(m.power(n,2*p),m.add(m.power(regular,2),m.power(subsequence,2)))
        return dict(plan,strategy='sparse_subseries',first_square_root=first,comparison_power=p,
                    regular=regular,exceptional=subsequence,scaled_limit_task=limit(square_sum,index))
    product=re.fullmatch(r'(.*?)prod\(([^=]+),([A-Za-z_]\w*)=(-?\d+)\.\.([A-Za-z_]\w*)\)',text.replace(' ',''))
    if not product or product[5]!=index or product[3] in [index,*params]:
        raise Unsupported('No complete bound product in the series term')
    prefix,body,k,lo,_=product.groups();lo=int(lo)
    if lo>start+1:raise Unsupported('The initial product is reversed')
    term=m.parse(body,k,params)
    marker='productFactor'
    while marker in [index,*params]:marker+='_'
    scalar=ONE;degree=0;copies=0
    def multiplier(e):
        nonlocal scalar,degree,copies
        if e[0]=='mul':
            multiplier(e[1]);multiplier(e[2])
        elif e==('s',marker):copies+=1
        elif e==n:degree+=1
        elif e[0]=='pow' and e[1]==n and e[2]>=0:degree+=e[2]
        elif m.constant_defined(e,ctx):scalar=m.mul(scalar,e)
        else:raise Unsupported('An index-dependent prefactor needs its own summable bound')
    multiplier(m.parse(prefix+marker,index,[*params,marker]))
    if copies!=1:raise Unsupported('Expected a single product factor')
    # Check the entire original factor, even if a previous factor or the prefactor vanishes.
    ray='productTail'
    while ray in [k,index,*params]:ray+='_'
    rc=m.context(dict(variable=k,parameters=[*params,ray],parameter_conditions=[*conditions,ray+'>0']))
    if not all(m.constant_defined(m.substitute(term,{('v',k):point}),context) for point,context in
               ((q(lo),ctx),(m.add(q(lo),('s',ray)),rc))):
        try:rational_on_tail(term,k,lo)
        except (NotRational,Undefined) as exc:raise Unsupported('An original product factor may be undefined') from exc
    plan.update(product_start=lo,scalar=scalar,degree=degree,factor=term)
    # A fixed bound for a quotient can remain sharp even when the factor oscillates.
    if term[0]=='div' and term[1][0]=='pow' and term[1][1][0] in ('sin','cos') and term[1][2]>0:
        def lower(e):
            if m.constant_defined(e,ctx):return m.simplify(e)
            if e[0]=='add':return m.add(lower(e[1]),lower(e[2]))
            if e[0]=='pow' and e[2]>0 and e[2]%2==0:return ZERO
            raise Unsupported('A uniform lower bound for the original denominator is missing')
        bound=lower(term[2]);branch=None
        if m.sign(m.add(bound,q(-1)),ctx)!=1:
            for p in params:
                if m.simplify(m.substitute(scalar,{('s',p):ZERO}))!=ZERO:continue
                nonzero=m.context(dict(variable=index,parameters=params,parameter_conditions=[*conditions,p+'!=0']))
                if m.sign(m.add(bound,q(-1)),nonzero)==1:branch=p;break
            if branch is None:raise Unsupported('Strict geometric domination is not established on all parameter branches')
        ratio=m.div(ONE,bound)
        return dict(plan,strategy='uniform_factor_bound',zero_parameter=branch,lower_denominator=bound,ratio=ratio,
                    scaled_limit_task=limit(m.power(m.div(m.add(n,ONE),n),degree),index))
    return dict(plan,strategy='limiting_factor',scaled_limit_task=limit(term,k,params,conditions))


def power_series_boundary(task,library,request):
    """Separate the power coordinate, certify coefficient growth, then decide each boundary independently."""
    from ordinary_series import affine_product_profile,compare_growth_levels,original_series_profiles
    for transition in (affine_product_profile,compare_growth_levels,original_series_profiles):
        try:return transition(task,library)
        except Unsupported:pass
    from integrals import affine
    from tasks import source,guard_source,known_guard
    from verify import same_value
    allowed={'kind','id','source','term','index','variable','start_index','parameters','stated_conditions','requested_output','original_qualifications'}
    start=task.get('start_index');index=task['index'];given=task.get('source',{})
    functional=task['kind']=='functional_series_convergence_set'
    if functional:allowed=(allowed-{'variable'})|{'variables'}
    variable=task['variables'][0] if functional else task['variable']
    ordinary=task['kind']=='power_series_convergence_set'
    wanted=['radius','open_interval','both_endpoint_classifications'] if ordinary else ['complete_convergence_set']
    heading='Определить радиус, интервал сходимости и исследовать обе граничные точки.' if ordinary else 'Найти область сходимости обобщённого степенного ряда.'
    if functional:
        heading='Определить области абсолютной и условной сходимости исходного функционального ряда.'
        wanted=['absolute_convergence_set','conditional_convergence_set','proof']
    if (not library.data.get('power_series_boundary') or set(task)-allowed or task.get('requested_output')!=wanted
            or not isinstance(given,dict) or set(given)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','pdf_pages','literal_requirement'}
            or given.get('literal_requirement',heading)!=heading or type(start)!=int or start<0 or index==variable):
        raise Unsupported('The source range, domain or requested boundary conclusions are not covered')
    raw=task['term'].replace(' ','');frozen={};product_defs={}
    def marker():
        key='sequenceFactor'+str(len(frozen))
        while key in raw:key+='_'
        frozen[key]=None;return key
    def product_input(mt):
        body,j,l,n=mt.groups()
        if n!=index or j in (variable,index):raise Unsupported('The original product indices are not bound')
        key=marker();product_defs[key]=(body,j,int(l));return key
    raw=re.sub(r'product\(([^,]+),(\w+),(-?\d+),(\w+)\)',product_input,raw)
    raw=re.sub(r'(\([^()!]*\)|\b[A-Za-z_]\w*|\b\d+)(!!?)',lambda z:('doublefact' if z[2]=='!!' else 'factorial')+'('+z[1]+')',raw)
    funcs={'factorial','doublefact'}
    freenames=lambda text:set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-funcs-{'pi','e',variable,index}-set(frozen)
    names=freenames(raw)
    for body,j,l in product_defs.values():names|=freenames(body)-{j}
    params=task.get('parameters',sorted(names));ctx=m.context(dict(variable=index,parameters=params))
    if names-set(ctx['parameters']) or variable in ctx['parameters']:raise Unsupported('A fixed parameter is missing or conflicts with the power variable')
    params=ctx['parameters'];conditions=list(task.get('stated_conditions',[]))
    for qualifier in filter(None,task.get('original_qualifications','').replace(' ','').split(',')):
        if qualifier=='start='+str(start):continue
        if (g:=re.fullmatch(r'0<(\w+)<1',qualifier)) and g[1] in params:conditions.extend((g[1]+'>0','1-'+g[1]+'>0'));continue
        if re.fullmatch(r'\w+>[01]',qualifier) and qualifier[:-2] in params:conditions.append(qualifier);continue
        raise Unsupported('An original qualification is not represented in the coefficient proof')
    ctx=m.context(dict(variable=index,parameters=params,parameter_conditions=conditions))
    n=('v',index);x=('s',variable);cert=[];atoms={};coordinates=[];coords_power=set()
    for key,(body,j,l) in product_defs.items():
        if j in params or start<l-1:raise Unsupported('A finite product is not bound on the original range')
        atoms[key]=(m.parse(body,j,params),j,l,0)
    raw_ast=m.parse(raw,index,[*params,variable,*atoms],extra_functions=funcs)
    def extract(e,sign=1):
        if not m.contains(e,x):return e
        if e[0] in ('mul','div'):
            return (e[0],extract(e[1],sign),extract(e[2],sign if e[0]=='mul' else -sign))
        if e[0]=='exp':
            at=m.simplify(m.substitute(e[1],{n:ONE}))
            if domain_conditions(e[1]) or not same_value(e[1],m.mul(n,at)):raise Unsupported('Variable exponential does not have a linear index')
            base=('exp',at);degree=1
        elif e[0]=='rpow' and not m.contains(e[1],n) and (e[2]==n or e[2]==('pow',n,2)):
            base=e[1];degree=1 if e[2]==n else 2
        else:raise Unsupported('No index-independent power coordinate can be separated')
        coordinates.append(base if sign==1 else ('div',ONE,base));coords_power.add(degree);return ONE
    coefficient=extract(raw_ast)
    if len(coords_power)!=1 or not coordinates:raise Unsupported('Different powers of the index require a separate comparison')
    deg=coords_power.pop();coordinate=ONE;domain=[]
    for z in coordinates:
        domain.extend(guard_source(g) for g in domain_conditions(z) if not known_guard(g,ctx));coordinate=m.mul(coordinate,z)
    # Lower factorials to their exact positive consecutive factors. A constant initial
    # value has no influence on a convergence test, but its domain must first be proved.
    gain=quadratic=root_scale=ONE;alternating=False
    def fixed_power(b,h):
        r=m.num(h)
        return m.power(b,int(r)) if r is not None and r.denominator==1 else m.simplify(('rpow',b,h))
    def geometric(base,slope,second,w):
        nonlocal gain,quadratic,alternating
        sign=m.sign(base,ctx)
        if not m.constant_defined(base,ctx) or sign not in (1,-1):raise Unsupported('The fixed geometric base needs a sign and nonzero domain')
        cert.append(dict(fixed_base=base,index_slope=q(slope),index_quadratic=q(second),weight=w))
        if sign<0:
            parity=m.num(m.mul(w,q(slope+second)))
            if parity is None or parity.denominator!=1 or m.num(w) is None or m.num(w).denominator!=1:raise Unsupported('A negative base has a noninteger exponent')
            alternating^=bool(parity%2);base=m.neg(base)
        gain=m.mul(gain,fixed_power(base,m.mul(q(slope),w)))
        quadratic=m.mul(quadratic,fixed_power(base,m.mul(q(second),w)))
    def lower(e,w=ONE):
        nonlocal gain,root_scale
        if e[0] in ('mul','div'):
            return (e[0],lower(e[1],w),lower(e[2],w if e[0]=='mul' else m.neg(w)))
        if e[0] in funcs:
            try:form=coefficients(e[1],index,start)
            except (NotRational,Undefined) as exc:raise Unsupported('The factorial may not exist at an original index') from exc
            if len(form)!=2 or any(c.denominator!=1 for c in form):raise Unsupported('Expected an integer affine factorial argument')
            b,a=map(int,form);step=2 if e[0]=='doublefact' else 1
            if a<=0 or a%step or a*start+b<0:raise Unsupported('The factorial shift fails its starting domain or parity')
            if a//step>m.MAX_INTEGER_POWER:raise Unsupported('Too many exact consecutive factors')
            value=ONE;j='productStep'
            while j in [index,variable,*params]:j+='_'
            for i in range(step,a+1,step):
                label=marker();atoms[label]=(m.add(m.mul(q(a),('v',j)),q(b+i-a)),j,start+1,0)
                value=m.mul(value,('s',label))
            cert.append(dict(factorial=e[0],argument=e[1],first=a*start+b,stride=step));return value
        if e[0]=='add' and all(z[0]=='rpow' and z[2]==n and m.num(z[1]) is not None for z in e[1:]):
            a,b=sorted((m.num(z[1]) for z in e[1:]),key=abs,reverse=True)
            if start<1 or a<=abs(b):raise Unsupported('A unique positive dominant geometric component is required')
            geometric(q(a),1,0,w);cert.append(dict(dominant=q(a),relative_remainder=q(b/a)));return ONE
        if e[0]=='exp' and m.contains(e,n):
            a,b=affine(e[1],index)
            if domain_conditions(e[1]) or not all(m.constant_defined(z,ctx) for z in (a,b)):raise Unsupported('The exponential rate or its intercept is undefined')
            gain=m.mul(gain,m.simplify(('exp',m.mul(w,a))));return ONE
        if e[0] not in ('pow','rpow'):return e
        base=e[1];ex=q(e[2]) if e[0]=='pow' else e[2]
        if not m.contains(ex,n):
            if not m.constant_defined(ex,ctx):raise Unsupported('The exterior exponent is not a fixed real number')
            return (e[0],lower(base,m.mul(w,ex)),e[2])
        root=('sqrt',n)
        if m.contains(ex,root):
            residual=m.substitute(ex,{root:ONE});slope=m.simplify(residual)
            if (domain_conditions(residual) or not m.constant_defined(slope,ctx) or not same_value(ex,m.mul(slope,root))
                    or domain_conditions(base) or not m.constant_defined(base,ctx) or m.sign(base,ctx)!=1):
                raise Unsupported('The square-root scale needs a defined positive fixed base and a linear exponent in sqrt(index)')
            root_scale=m.mul(root_scale,fixed_power(base,m.mul(slope,w)))
            cert.append(dict(positive_base=base,square_root_slope=slope));return ONE
        try:poly=coefficients(ex,index,start)
        except (NotRational,Undefined) as exc:raise Unsupported('A varying exponent has no certified polynomial form') from exc
        if len(poly)>3 or any(z.denominator!=1 for z in poly):raise Unsupported('Only exact quadratic index growth is certified')
        off,slope,second=(*poly,0,0)[:3]
        if m.constant_defined(base,ctx):
            geometric(base,slope,second,w);return ONE
        if base==n and not second and start>=1:return e
        if base[0]=='div' and base[1]==n and m.constant_defined(base[2],ctx) and m.sign(base[2],ctx)==1 and not second and start>=1:
            geometric(base[2],-slope,0,w);return ('rpow',n,ex)
        try:a,b=rational_on_tail(base,index,start)
        except (NotRational,Undefined) as exc:raise Unsupported('The real varying power lacks an all-index positive base') from exc
        if len(a)!=len(b) or any(s!=1 for _,s in integer_sign_runs(pm(a,b),start)):raise Unsupported('A positive finite rational asymptote is required')
        lead=a[-1]/b[-1];correction=(a[-2]/a[-1]-b[-2]/b[-1]) if len(a)>1 else 0
        geometric(q(lead),slope,second,w)
        gain=m.mul(gain,m.simplify(('exp',m.mul(q(second*correction),w))))
        cert.append(dict(rational_base=base,positive_leading=q(lead),first_log_correction=q(correction),exponent=ex))
        return ONE
    reduced=lower(coefficient)
    profile=product_series_ratio(dict(index=index,start_index=start,parameters=params,stated_conditions=conditions,term='1'),(reduced,atoms))
    L=m.mul(gain,profile['leading_ratio']);h=profile['log_coefficient'];order=profile['ratio_degree']
    def direction(value):
        if same_value(value,ONE):return 0
        if value[0]=='div' and value[1]==ONE and m.sign(value[2],ctx)==1:
            cmp=direction(value[2])
            if cmp is not None:return -cmp
        if value[0]=='s' and any(a['symbol']==value[1] and a['relation']=='greater_one' for a in ctx['assumptions']):return 1
        return m.sign(m.add(value,m.neg(ONE)),ctx)
    scale_sign=direction(quadratic);ds=m.sign(order,ctx)
    if scale_sign is None or ds is None:raise Unsupported('Conditional growth of the coefficient needs a parameter split')
    local=dict(kind='limit',variable='u',expression='(ln(1+u)-u+u^2/2)/u^3',approach=dict(point='0',side='both'))
    if not same_value(request('third-order remainder for logarithms of consecutive positive ratios',local)['value'],q(1,3)):
        raise Unsupported('The summable remainder in the normalized coefficient ratio is unproved')
    plan=dict(theorem='method.power_series_boundary',start_index=start,coordinate=source(coordinate),coordinate_index_power=deg,
              source_guards=sorted(set(domain)),coefficient_profile=profile,ratio_multiplier=L,quadratic_base=quadratic,square_root_base=root_scale,
              alternating_coefficient=alternating,lowering_certificates=cert)
    if deg==1:
        growth=scale_sign or ds
        radius='+inf' if growth<0 else ZERO if growth>0 else m.div(ONE,L)
    else:
        radius=m.div(ONE,quadratic)
        if radius==ZERO:raise Unsupported('The quadratic-coordinate threshold is unresolved')
    def algebraic_boundary(phase):
        # With cubic log remainder, the normalized coefficients are equivalent to C*n^H.
        # For H<0 their ratio is 1+H/n+O(n^-2), ensuring eventual monotonicity.
        cmp1=m.sign(m.add(h,ONE),ctx);cmp0=m.sign(h,ctx)
        if cmp1==-1:return 'absolute'
        if cmp1 in (0,1) and (not phase or cmp0 in (0,1)):return 'divergent'
        if cmp1 in (0,1) and cmp0==-1:return 'conditional'
        return dict(absolute_if=source(h)+' < -1',conditional_if='-1 <= '+source(h)+' < 0' if phase else 'never',
                    divergent_if=source(h)+(' >= 0' if phase else ' >= -1'))
    def endpoint(phase):
        if deg==2:
            rate=ds or direction(L)
            if rate is None:raise Unsupported('The endpoint geometric factor needs a parameter split')
            if rate:return 'absolute' if rate<0 else 'divergent'
        root_sign=direction(root_scale)
        if root_sign in (-1,1):return 'absolute' if root_sign<0 else 'divergent'
        boundary=algebraic_boundary(phase)
        if root_sign is None:
            return dict(parameter=source(root_scale),below_one='absolute',above_one='divergent',at_one=boundary)
        return boundary
    if ordinary:
        slope,offset=affine(m.substitute(coordinate,{x:('v',variable)}),variable);sgn=m.sign(slope,ctx)
        if domain or sgn not in (-1,1):raise Unsupported('An affine everywhere-defined power coordinate with a fixed orientation is required')
        center=m.div(m.neg(offset),slope)
        if radius=='+inf':value=dict(radius='+inf',center=source(center),open_interval=['-inf','+inf'],endpoint_classifications={})
        elif radius==ZERO:value=dict(radius='0',center=source(center),open_interval=[],endpoint_classifications={},convergence_set=source(center))
        else:
            r=m.div(radius,slope if sgn==1 else m.neg(slope))
            l,u=m.add(center,m.neg(r)),m.add(center,r)
            value=dict(radius=source(r),center=source(center),open_interval=[source(l),source(u)],
                       endpoint_classifications={source(l):endpoint(alternating^(sgn==1)),source(u):endpoint(alternating^(sgn<0))})
    else:
        if radius in ('+inf',ZERO):raise Unsupported('A degenerate generalized coordinate set needs its original zero and pole branches')
        value=dict(convergence_set=dict(coordinate=source(coordinate),original_domain=sorted(set(domain)),absolute_inside=source(radius),
                   divergent_outside=source(radius),at_negative_boundary=endpoint(not alternating),at_positive_boundary=endpoint(alternating)))
        if functional:
            z=source(coordinate);r=source(radius);c=value['convergence_set']
            for mode in ('absolute','conditional'):
                branches=[f'abs({z}) < {r}'] if mode=='absolute' else []
                for edge,predicate in [('at_negative_boundary',f'{z} = -({r})'),('at_positive_boundary',f'{z} = {r}')]:
                    if not isinstance(c[edge],str):raise Unsupported('Explicit parameter regions on the boundary are still needed')
                    if c[edge]==mode:branches.append(predicate)
                value[mode+'_convergence_set']=dict(original_domain=c['original_domain'],union=branches)
    return plan,value


def product_series_ratio(task,coefficient=None,*,signed_denominator_products=False):
    """Extract affine factors of a positive consecutive ratio, retaining all starting-index conditions."""
    from integrals import affine
    from tasks import source
    index=task['index'];start=task['start_index'];params=task.get('parameters',[])
    method=task.get('method_requirement')
    modes=(None,'general_convergence_tests','comparison_or_ratio_or_root','ratio_test','raabe_and_gauss')
    target=set(task.get('requested_output',['convergence_classification']))
    if method not in modes or not target or target-{'convergence_classification','justification','absolute_convergence'}:
        raise Unsupported('An additional convergence conclusion or prescribed test is required')
    check_series_heading(task)
    ctx=m.context(dict(variable=index,parameters=params,parameter_conditions=task.get('stated_conditions',[])))
    raw=task['term'].replace(' ',''); n=('v',index); atoms={};factors=[];guards=[];zeros=[]
    shifts=[];radicals=[];constant_factors=[];log_constant=ZERO;undefined=[]
    def store_atom(comp):
        key='productAtom'
        while key in raw or key in params or key in atoms or key==index:key+='_'
        atoms[key]=comp; return key
    def bind_product(match):
        expr,k,lower,upper,shift=match.groups()
        if upper!=index or k in [index,*params]:raise Unsupported('A product binder or upper index conflicts with the source')
        lower=int(lower);shift=int(shift or 0)
        if start+shift<lower-1:raise Unsupported('The first product range is reversed')
        body=m.parse(expr,k,params)
        return store_atom((body,k,lower,shift))
    text=re.sub(r'prod\(([^=]*?),([A-Za-z]\w*)=(-?\d+)\.\.([A-Za-z]\w*)([+-]\d+)?\)',bind_product,raw)
    text=re.sub(r'factorial\('+re.escape(index)+r'\)',lambda _:store_atom((('v',index),index,1,0)),text)
    if coefficient is None:
        if not atoms:raise Unsupported('There is no product recurrence to certify')
        outer=m.parse(text,index,[*params,*atoms])
    else:outer,atoms=coefficient
    def record(body,k,lower,shift,weight,strict,allow_signed):
        if body[0] in ('mul','div'):
            record(body[1],k,lower,shift,weight,strict,allow_signed)
            record(body[2],k,lower,shift,weight if body[0]=='mul' else m.neg(weight),strict or body[0]=='div',allow_signed)
            return
        square=('sqrt',('v',k))
        if m.contains(body,square) and lower>=0:
            aux='squareRoot'
            while aux in [index,k,*params]:aux+='_'
            linear=m.substitute(body,{square:('v',aux)})
            if m.contains(linear,('v',k)) or domain_conditions(linear):raise Unsupported('Unresolved domain in a square-root factor')
            a,b=affine(linear,aux);initial=m.add(m.mul(a,m.simplify(('sqrt',q(lower)))),b)
            if m.sign(a,ctx)!=1 or m.sign(initial,ctx)!=1:raise Unsupported('Positive square-root factors are required on the whole index range')
            radicals.append((a,b,shift+1,weight));guards.append(dict(variable=k,lower=lower,factor=body,first=initial,slope_in_root=a))
            return
        if domain_conditions(body):raise Unsupported('Additional domain restrictions in a product factor')
        slope,offset=affine(body,k);initial=m.add(m.mul(slope,q(lower)),offset)
        if slope==ZERO and m.constant_defined(offset,ctx) and m.sign(offset,ctx)==1:
            constant_factors.append((offset,weight));return
        if m.sign(slope,ctx)!=1:raise Unsupported('The eventual affine factor must have positive slope')
        if m.sign(initial,ctx)!=1:
            power=m.num(weight)
            if strict and signed_denominator_products and allow_signed and power is not None and power.denominator==1:
                undefined.append(dict(root=source(m.div(m.neg(offset),slope)),integer_at_least=lower))
            elif strict or power is None or power.denominator!=1 or power<=0:
                raise Unsupported('The original power or denominator needs positive factors from the first index')
            else:zeros.append(dict(root=m.div(m.neg(offset),slope),integer_at_least=lower,
                              effect='a zero makes every subsequent term zero; otherwise the finite prefix has fixed nonzero sign'))
        guards.append(dict(variable=k,lower=lower,factor=body,first=initial,slope=slope))
        factors.append((slope,m.add(offset,m.mul(slope,q(shift+1))),weight))
    extra_order=ZERO;scalar_factors=[]
    def collect(e,weight,strict=False,allow_signed=True):
        nonlocal log_constant,extra_order
        op=e[0]
        if not m.variable_in(e) and not any(m.contains(e,('s',key)) for key in atoms):
            if not m.constant_defined(e,ctx) or not m.nonzero(e,ctx) or not allow_signed and m.sign(e,ctx)!=1:
                raise Unsupported('The fixed scalar requires a defined nonzero value and the original real-power domain')
            if m.sign(e,ctx)!=1:scalar_factors.append(dict(factor=e,weight=weight))
        elif op in ('mul','div'):
            collect(e[1],weight,strict,allow_signed);collect(e[2],weight if op=='mul' else m.neg(weight),strict or op=='div',allow_signed)
        elif op=='sqrt':
            collect(e[1],m.mul(weight,q(1,2)),True,False)
        elif op=='exp':
            a,b=affine(e[1],index)
            if domain_conditions(e[1]) or not all(m.constant_defined(c,ctx) for c in (a,b)):raise Unsupported('Unproved exponential factor')
            log_constant=m.add(log_constant,m.mul(a,weight))
        elif op in ('rpow','pow'):
            exp=q(e[2]) if op=='pow' else e[2]
            if e[1]==n and m.contains(exp,n):
                a,b=affine(exp,index)
                if domain_conditions(exp) or not all(m.constant_defined(c,ctx) for c in (a,b)):raise Unsupported('Invalid index-dependent power')
                shifts.append((m.mul(weight,a),m.mul(weight,b)))
                return
            if not m.constant_defined(exp,ctx) or any(m.contains(exp,('s',s)) for s in atoms):
                raise Unsupported('The exterior exponent must be a defined fixed real parameter')
            power=m.num(exp)
            integral=power is not None and power.denominator==1
            collect(e[1],m.mul(weight,exp),strict or not integral or power<=0,allow_signed and integral)
        elif e==n:
            if (coefficient is not None or signed_denominator_products) and start<=0 and strict:raise Unsupported('A powered index can vanish in the original coefficient')
            factors.extend([(ONE,ONE,weight),(ONE,ZERO,m.neg(weight))])
        elif op=='s' and e[1] in atoms:record(*atoms[e[1]],weight,strict,allow_signed)
        elif coefficient is not None and m.variable_in(e):
            try:a,b=rational_on_tail(e,index,start)
            except (NotRational,Undefined) as exc:raise Unsupported('No proved coefficient ratio for this factor') from exc
            if not any(a) or strict and any(s!=1 for _,s in integer_sign_runs(pm(a,b),start)):
                raise Unsupported('A nonzero positive base is required on the original integer domain')
            extra_order=m.add(extra_order,m.mul(weight,q(len(a)-len(b))))
        elif not m.constant_defined(e,ctx) or m.sign(e,ctx)!=1:raise Unsupported('Unrecognized or nonpositive exterior factor')
    collect(outer,ONE)
    degree=ZERO;exponent=extra_order;slopes={}
    for a,b,w in factors:
        degree=m.add(degree,w);exponent=m.add(exponent,m.mul(w,m.div(b,a)))
        slopes[a]=m.add(slopes.get(a,ZERO),w)
    half_order=ZERO
    for a,b,shift,w in radicals:
        degree=m.add(degree,m.mul(q(1,2),w));slopes[a]=m.add(slopes.get(a,ZERO),w)
        h=m.div(b,a);half_order=m.add(half_order,m.mul(w,h))
        exponent=m.add(exponent,m.mul(m.mul(q(1,2),w),m.add(q(shift),m.neg(m.power(h,2)))))
    half_order=m.simplify(half_order)
    for a,b in shifts:
        degree=m.add(degree,a);log_constant=m.add(log_constant,a)
        exponent=m.add(exponent,m.add(b,m.mul(q(1,2),a)))
    for base,power in constant_factors:slopes[base]=m.add(slopes.get(base,ZERO),power)
    if coefficient is None and m.simplify(degree)!=ZERO:raise Unsupported('A nonconstant polynomial factor remains in the consecutive ratio')
    ratio=m.simplify(('exp',log_constant))
    for a,w in slopes.items():
        w=m.simplify(w)
        if a!=ONE and w!=ZERO:
            number=m.num(w)
            multiplier=m.power(a,int(number)) if number is not None and number.denominator==1 else m.simplify(('rpow',a,w))
            ratio=m.mul(ratio,multiplier)
    ratio=m.simplify(ratio);exponent=m.simplify(exponent);rate=m.sign(m.add(ratio,m.neg(ONE)),ctx)
    if coefficient is not None:
        if zeros or half_order!=ZERO:raise Unsupported('A terminating parameter branch or a root-scale correction needs separate proof')
        return dict(affine_factors=factors,all_index_guards=guards,log_index_powers=shifts,constant_factors=constant_factors,
                    ratio_degree=m.simplify(degree),leading_ratio=ratio,log_coefficient=exponent,**({'nonzero_scalars':scalar_factors} if scalar_factors else {}))
    if rate not in (-1,0,1):raise Unsupported('The leading positive ratio has unresolved parameter cases')
    if method=='ratio_test' and rate==0:raise Unsupported('The prescribed ratio test is inconclusive at one')
    if method=='raabe_and_gauss' and rate!=0:raise Unsupported('The printed Raabe and Gauss classification requires a separate argument')
    plan=dict(criterion='product_ratio_expansion',affine_factors=factors,positivity=guards,constant_factors=constant_factors,terminating_if=zeros,index_dependent_powers=shifts,root_factors=radicals,half_order=half_order,leading_ratio=ratio,log_coefficient=exponent,
              theory='log|a[n+1]/a[n]|=log(C)+G/sqrt(n)+H/n+O(n^(-3/2)); for C=1,G=0 the residual logarithms are summable')
    if scalar_factors:plan['nonzero_scalars']=scalar_factors
    if signed_denominator_products:plan['undefined_if']=undefined
    if rate:conclusion='convergent' if rate<0 else 'divergent'
    elif half_order!=ZERO:
        half_sign=m.sign(half_order,ctx)
        if half_sign not in (-1,1):raise Unsupported('Unresolved sign of the leading square-root correction')
        conclusion='convergent' if half_sign<0 else 'divergent'
    else:
        sign=m.sign(m.add(exponent,ONE),ctx)
        conclusion=('parameter_dependent' if sign is None else 'convergent' if sign<0 else 'divergent')
    plan['classification']=conclusion
    plan['scaled_limit_task']=dict(kind='limit',variable='u',expression='(ln(1+u)-u+u^2/2)/u^3' if shifts or radicals else '(ln(1+u)-u)/u^2',approach=dict(point='0',side='both'))
    return plan


def compile_series_bound(task):
    """Bind a classification question to its original summand, index and domain."""
    fields={'kind','term','index','start_index','index_domain','parameters','stated_conditions','method_requirement','requested_output','schema','id','source','transcription'}
    from tasks import series_outputs
    outputs=series_outputs(task)
    if (set(task)-fields or task.get('method_requirement') not in (None,'general_convergence_tests','comparison_or_ratio_or_root','cauchy_tail_criterion')
            or not isinstance(outputs,(list,tuple)) or not outputs
            or set(outputs)-{'convergence_classification','justification','absolute_convergence','conditional_convergence'}):
        raise Unsupported('The requested method or output needs a different series criterion')
    start=task.get('start_index')
    if type(start) is not int or start<1 or task.get('index_domain','integers')!='integers':
        raise Unsupported('A positive integral starting index is required')
    params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if (not isinstance(task.get('index'),str) or not isinstance(task.get('term'),str)
            or not isinstance(params,(list,tuple)) or not all(isinstance(p,str) for p in params)
            or not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions)):
        raise Unsupported('Named real parameters and explicit original index conditions are required')
    ctx=m.context(dict(variable=task['index'],parameters=params,parameter_conditions=conditions))
    ctx.update(domain='integer_series',variable=task['index'],variable_domain='positive_integers',sum_start=start)
    ctx.update(series_method=task.get('method_requirement'),series_conditions=list(conditions))
    term=m.parse(task['term'],ctx['variable'],ctx['parameters'])
    predicate='cauchy_series_classification' if task.get('method_requirement')=='cauchy_tail_criterion' else 'series_classification'
    return dict(goal=(predicate,term),context=ctx)


def compile_functional_series(task):
    fields={'kind','term','index','start_index','variables','stated_conditions','requested_output','id','source','schema'}
    variables=task.get('variables');start=task.get('start_index')
    outputs=task.get('requested_output',[])
    if (set(task)-fields or task.get('stated_conditions') or not isinstance(variables,list) or len(variables)!=1
            or not isinstance(variables[0],str) or not isinstance(task.get('index'),str) or not isinstance(task.get('term'),str)
            or type(start) is not int or start<1 or not isinstance(outputs,list) or 'absolute_convergence_set' not in outputs
            or set(outputs)-{'absolute_convergence_set','conditional_convergence_set','proof'}):
        raise Unsupported('A single unrestricted real parameter and the printed convergence sets are required')
    index=task['index'];ctx=m.context(dict(variable=index,parameters=variables))
    ctx.update(domain='integer_series',variable=index,variable_domain='positive_integers',sum_start=start)
    return dict(goal=('parameter_series_sets',m.parse(task['term'],index,variables)),context=ctx)


def geometric_factors(term,ctx):
    """Separate A(n) B(x)^n; preserve raw parameter divisors before simplification."""
    var=ctx['variable'];n=('v',var);parameter=('s',ctx['parameters'][0]);guards=[]
    def collect(e):
        op=e[0]
        if op=='rpow' and e[2]==n and not m.variable_in(e[1]):
            guards.extend(domain_conditions(e[1]));return ONE,e[1]
        if op=='exp' and e[1][0]=='mul' and n in e[1][1:]:
            slope=e[1][2] if e[1][1]==n else e[1][1]
            if not m.variable_in(slope):
                guards.extend(domain_conditions(slope));return ONE,('exp',slope)
        if op in ('mul','div'):
            a,b=collect(e[1]);c,d=collect(e[2])
            if op=='div':guards.append(('nonzero',d))
            return (op,a,c),(op,b,d)
        if m.contains(e,parameter):raise Unsupported('Parameter dependence outside the geometric factor')
        return e,ONE
    a,b=collect(term)
    guards=[(g,e) for g,e in dict.fromkeys(guards) if e!=ONE]
    return a,m.simplify(b),tuple(guards)


def progression_weight(term,ctx):
    """Extract c (-1)^(d*n+e) (A*n+B)^(-s), checking each raw factor first."""
    index,start=ctx['variable'],ctx['sum_start']
    if ctx.get('series_method') not in (None,'general_convergence_tests'):
        raise Unsupported('The printed method needs its own premises')
    c=Fraction(1);phase=0;base=None;decay=ZERO
    def collect(node,sign):
        nonlocal c,phase,base,decay
        tag=node[0]
        if tag in ('mul','div'):
            collect(node[1],sign);collect(node[2],sign if tag=='mul' else -sign)
        elif tag=='q':
            c *= rational(node)**sign
        elif tag=='rpow' and node[1]==q(-1):
            form=coefficients(node[2],index,start)
            if len(form)>2 or any(v.denominator!=1 for v in form):
                raise Unsupported('Integer affine phase not proved')
            c *= (-1)**(int(form[0])%2)
            phase ^= int(form[-1])%2 if len(form)==2 else 0
        else:
            kernel=node[1] if tag in ('pow','rpow') else node
            exponent=node[2] if tag=='rpow' else q(node[2]) if tag=='pow' else ONE
            if m.variable_in(exponent) or not m.constant_defined(exponent,ctx):
                raise Unsupported('Exponent not defined for every original parameter')
            form=coefficients(kernel,index,start)
            if len(form)!=2 or form[1]<=0 or form[1]*start+form[0]<=0:
                raise Unsupported('Base must be a positive increasing affine progression from the original start')
            if base is not None and base!=form:raise Unsupported('Distinct progressions require a separate comparison')
            base=form
            decay=m.add(decay,m.mul(q(-sign),exponent))
    collect(term,1)
    if base is None:raise Unsupported('No power progression')
    return (q(c),phase,q(base[1]),q(base[0]),q(base[1]*start+base[0]),m.simplify(decay))


def progression_classes(exponent,absolute,ordinary,ctx):
    """Intervals below are relative to all originally admitted parameter values."""
    from tasks import source
    name=source(exponent)
    def relation(bound,operator):
        if bound=='all':return 'all' if operator=='>' else 'empty'
        threshold=rational(bound)
        difference=m.simplify(m.add(exponent,m.neg(bound)))
        sign=m.sign(difference,ctx)
        if sign in (-1,0,1):return 'all' if (sign>0)==(operator=='>') else 'empty'
        if difference[0]=='pow' and difference[2]>0 and difference[2]%2==0:
            return source(difference[1])+('!=0' if operator=='>' else '=0')
        # Isolate a single affine parameter exactly, reversing the sign when needed.
        if len(ctx['parameters'])==1:
            p=ctx['parameters'][0];e=m.substitute(exponent,{('s',p):('v',p)})
            try:
                num,den=rf(e,p)
                if len(num)==2 and len(den)==1:
                    slope=num[1]/den[0];cut=(threshold-num[0]/den[0])/slope
                    op=operator if slope>0 else {'>':'<','<=':'>='}[operator]
                    return f'{p}{op}{cut}'
            except (NotRational,Undefined):pass
        return f'({name}){operator}{threshold}'
    abs_set=relation(absolute,'>');conv_set=relation(ordinary,'>');div_set=relation(ordinary,'<=')
    fail_abs=relation(absolute,'<=')
    conditional='empty' if ordinary==absolute or 'empty' in (conv_set,fail_abs) else ' and '.join(v for v in (conv_set,fail_abs) if v!='all') or 'all'
    if not ctx['parameters']:
        return dict(criterion='power_progression_thresholds',classification='divergent' if div_set=='all' else 'convergent',
                    absolute_convergence=abs_set=='all',conditional_convergence=conditional=='all',divergence=div_set=='all',domain_conditions=[])
    return dict(criterion='power_progression_thresholds',classification='by_parameter',absolute_convergence=abs_set,
                conditional_convergence=conditional,divergence=div_set,domain_conditions=ctx.get('series_conditions',[]))


def series_bound_step(name,args,ctx):
    """Local certificates for |a_n| ≤ C n^d r^n for n ≥ N, with the original prefix defined."""
    if ctx.get('domain')!='integer_series':return []
    var=ctx['variable'];n=('v',var);start=ctx['sum_start']
    unit=(ONE,0,ONE,start)
    def scalar_order(a,b):
        from ray_proofs import compare_scalar
        return compare_scalar(a,b)
    def magnitude(e):return m.simplify(('abs',e))
    try:
        if name=='sum_bound_progression_weight':return [(progression_weight(args[0],ctx),)]
        if name in ('sum_bound_progression_absolute','sum_bound_progression_ordinary'):
            coefficient,alternates,slope,offset,initial,exponent=args[0]
            if rational(slope)<=0 or rational(initial)!=rational(offset)+start*rational(slope) or rational(initial)<=0:return []
            threshold='all' if coefficient==ZERO else ZERO if alternates and name.endswith('_ordinary') else ONE
            return [(exponent,threshold)]
        if name=='sum_bound_progression_sets':return [(progression_classes(*args,ctx),)]
        if name=='sum_bound_split_geometric':
            return [geometric_factors(args[0],ctx)]
        if name=='sum_bound_rational_asymptote':
            p,d=rational_on_tail(args[0],var,start)
            if not any(p):return []
            order=len(p)-len(d);first=start
            if order==-1:
                # A constant sign and decreasing magnitude on the same tail are
                # necessary for using Leibniz at the negative endpoint.
                pp=translated_coefficients(p,1);dd=translated_coefficients(d,1)
                left=pm(p,dd);right=pm(pp,d)
                gap=pa(pm(left,left),[-c for c in pm(right,right)])
                cut,sgn=integer_sign_runs(gap,start)[-1]
                if sgn!=1:return []
                first=max(cut,integer_sign_runs(pm(p,d),start)[-1][0])
            return [(order,q(Fraction(p[-1],d[-1])),first)]
        if name=='sum_bound_parameter_sets':
            from tasks import source
            base,guards,order=args
            if type(order) is not int:return []
            variable=ctx['parameters'][0]
            absolute='abs('+source(base)+')'+('<=1' if order < -1 else '<1')
            conditional=source(base)+'=-1' if order==-1 else '∅'
            description={'variable':variable,'source_domain':[source(e)+{'nonzero':'!=0','positive':'>0','nonnegative':'>=0'}[g] for g,e in guards],
                         'absolute_convergence_set':absolute,'conditional_convergence_set':conditional}
            # Resolve parameter cells exactly where the existing real sign algebra supports them.
            from graphs import domain_partition
            from polynomial import ResourceBound
            def variable_expr(e):return m.substitute(e,{('s',variable):('v',variable)})
            raw_guards=[(g,variable_expr(e)) for g,e in guards];b=variable_expr(base)
            try:
                abs_guard=('nonnegative' if order < -1 else 'positive',m.add(ONE,m.neg(m.power(b,2))))
                description['absolute_cells']=domain_partition(variable,[*raw_guards,abs_guard],simplify_guards=True)[0]
                if order==-1:
                    diff=m.add(b,ONE)
                    description['conditional_cells']=domain_partition(variable,[*raw_guards,('nonnegative',diff),('nonnegative',m.neg(diff))],simplify_guards=True)[0]
            except (NotRational,Undefined,Unsupported,ResourceBound,ArithmeticError):pass
            return [(description,)]
        if name=='sum_bound_fixed':
            e,=args
            return [((magnitude(e),0,ONE,start),)] if m.constant_defined(e,ctx) else []
        if name=='sum_bound_index':return [((ONE,1,ONE,start),)] if args==(n,) else []
        if name=='sum_bound_unit_wave':
            # A bound on the argument already certifies its domain at every original index.
            return [(unit,)]
        if name=='sum_bound_integer_phase':
            p=coefficients(args[0],var,start)
            from graphs import peval
            # A polynomial is integer-valued here iff its first deg(p)+1 consecutive
            # values are integers (integer forward differences in the Newton basis).
            return [(unit,)] if all(peval(p,j).denominator==1 for j in range(start,start+len(p))) else []
        if name in ('sum_bound_add','sum_bound_mul'):
            (a,d,r,i),(b,e,s,j)=args
            if name=='sum_bound_add':
                rate=r if scalar_order(r,s)>=0 else s
                return [((m.add(a,b),max(d,e),rate,max(i,j)),)]
            return [((m.mul(a,b),d+e,m.mul(r,s),max(i,j)),)]
        if name=='sum_bound_natural_power':
            (a,d,r,i),k=args
            if type(k) is not int or k<1:return []
            return [((m.power(a,k),d*k,m.power(r,k),i),)]
        if name=='sum_bound_power_index':
            (a,d,r,i),exponent=args
            return [((ONE,0,a,i),)] if exponent==n and d==0 and r==ONE else []
        if name=='sum_bound_div_power':
            (a,d,r,i),b,exponent=args
            if exponent!=n or not m.constant_defined(b,ctx) or not m.nonzero(b,ctx):return []
            return [((a,d,m.div(r,magnitude(b)),i),)]
        if name=='sum_bound_div_fixed':
            (a,d,r,i),b=args
            if not m.constant_defined(b,ctx) or not m.nonzero(b,ctx):return []
            return [((m.div(a,magnitude(b)),d,r,i),)]
        if name=='sum_bound_div_index_power':
            (a,d,r,i),base,k=args
            if base!=n or type(k) is not int:return []
            return [((a,d-k,r,i),)]
        if name=='sum_bound_div_geometric_sum':
            (a,d,r,i),base,other,exponent=args
            if exponent!=n or not all(m.constant_defined(b,ctx) and m.sign(b,ctx)==1 for b in (base,other)):return []
            lower=base if scalar_order(base,other)>=0 else other
            return [((a,d,m.div(r,lower),i),)]
        if name=='sum_bound_rational_power':
            e,exponent=args
            if exponent!=n:return []
            p,d=rational_on_tail(e,var,start)
            if len(p)>len(d):return []
            limit=abs(Fraction(p[-1],d[-1])) if len(p)==len(d) else 0
            if limit>=1:return []
            rate=(1+Fraction(limit))/2
            gap=pa([rate**2*c for c in pm(d,d)],[-c for c in pm(p,p)])
            first,sign=integer_sign_runs(gap,start)[-1]
            return [((ONE,0,q(rate),first),)] if sign>=0 else []
        if name=='sum_bound_wave_ratio':
            # (a+u)/(b+u) increases with u for b>a>=1. At rational angles
            # neither sine nor cosine attains -1, by irrationality of pi.
            a,b,w=args
            a=m.num(a);b=m.num(b)
            if a is None or b is None or not b>a>=1 or w[0] not in ('cos','sin'):return []
            coefficients(w[1],var,start)
            return [(q((a+1)/(b+1)),)]
        if name=='sum_bound_at_least_index':
            # Replace log(n) by its upper bound n-1 only when its coefficient is nonpositive.
            e,=args
            log=('ln',n);symbol=('s','__series_log')
            def admissible(t):
                return t==n or t==log or t[0]=='q' or t[0] in ('add','mul') and all(admissible(c) for c in t[1:])
            if not admissible(e):return []
            formal=m.substitute(e,{log:symbol})
            num,den=m.rational_form(formal)
            if den!={():Fraction(1)} or set(num)-{(),((n,1),),((symbol,1),)}:return []
            a=num.get(((n,1),),0);b=num.get(((symbol,1),),0);c=num.get((),0)
            if b>0 or a+b<1 or (a+b-1)*start+c-b<0:return []
            return [()]
        if name=='sum_bound_ceiling_power':
            rate,=args
            value=m.num(rate)
            return [((ONE,0,rate,start),)] if value is not None and 0<value<1 else []
        if name=='sum_bound_decay':
            (a,d,r,i),=args
            return [()] if scalar_order(r,ZERO)>=0 and scalar_order(r,ONE)<0 else []
        if name=='sum_bound_cauchy_tail':
            (a,d,r,i),=args
            if d<=0 and scalar_order(r,ZERO)>=0 and scalar_order(r,ONE)<0:
                return [('geometric_tail',m.div(a,m.add(ONE,m.neg(r))),r,i)]
            if d<=-2 and r==ONE:
                return [('telescoping_tail',a,ONE,max(2,i))]
            return []
        if name=='sum_bound_inverse_square':
            (a,d,r,i),=args
            return [()] if r==ONE and d<=-2 else []
    except (NotRational,Undefined,Unsupported,ArithmeticError,ValueError):return []
    return []


def calculate(name, args, ctx):
    if name.startswith('sum_bound_'):return series_bound_step(name,args,ctx)
    from integrals import polynomial_expression
    var = ctx['variable']
    j = ('v',var)
    def at(expr, point):
        return m.substitute(expr,{j:point})
    if name == 'polynomial_normal_form':
        return [(polynomial_expression(coefficients(args[0],var,ctx['sum_start']),var),)]
    if name == 'sum_integer_power_normal':
        from operations import expression_positions
        if not any(e[0]=='rpow' for _,e in expression_positions(args[0])):return []
        return [(integer_power_form(args[0],var,ctx['sum_start']),)]
    if name == 'sum_clear_denominators':
        (p,d),(u,v) = (rational_on_tail(expr,var,ctx['sum_start']) for expr in args)
        if not any(pdiv(p,d)[1]) and not any(pdiv(u,v)[1]):
            return []  # The existing polynomial rule already handles these sides.
        return [(polynomial_expression(pm(p,v),var),polynomial_expression(pm(u,d),var))]
    if name == 'sum_primitive_candidate':
        poly = coefficients(args[0],var,ctx['sum_start'])
        return [(polynomial_primitive(poly,Fraction(1),var),)]
    if name == 'sum_base_sides':
        term, formula, lower = args
        return [(at(term,lower),at(formula,lower))]
    if name == 'sum_step_sides':
        term, formula = args
        next_j = m.add(j,ONE)
        return [(('add',formula,at(term,next_j)),at(formula,next_j))]
    if name == 'sum_difference_sides':
        witness, term = args
        return [(m.add(witness,m.neg(at(witness,m.add(j,q(-1))))),term)]
    if name == 'sum_boundary_sides':
        witness, formula, lower = args
        return [(m.add(witness,m.neg(at(witness,m.add(lower,q(-1))))),formula)]
    raise Unsupported('Неизвестная операция с конечной суммой')


def proof_text(result, pretty):
    statement = result['task'].get('goal',{})
    lines = [str(statement.get('proposition','')) if isinstance(statement,dict) else '',result['status']]
    if result['status'] != 'SOLVED':
        for _,left,right in result.get('open_equalities',[]):
            var=result['context']['variable']
            lines.append('Осталось доказать '+pretty(left,var)+' = '+pretty(right,var))
        return '\n'.join([*lines, result.get('reason','')])
    ctx = result['context']
    var, start = ctx['variable'], ctx['sum_start']
    upper = ctx['quantified_variable']
    nodes = {node['id']:node for node in result['proof']['nodes']}
    root = nodes[result['proof']['root']]
    def equality(node,label):
        _,left,right=freeze(nodes[node['steps'][-1]['proof']]['goal'])
        return pretty(left,label,simplify=False)+' = '+pretty(right,label,simplify=False)
    if root['rule']=='sum.induction':
        base,step=(nodes[edge['proof']] for edge in root['steps'])
        lines.append(f'База. При {upper}={start} сумма состоит из первого слагаемого. '+equality(base,upper))
        _,term,formula,_=freeze(root['goal'])
        lines.append(f'Переход. Для произвольного целого {var}≥{start} предполагаем S({var}) = '+pretty(formula,var,simplify=False)+'.')
        following=m.substitute(term,{('v',var):m.add(('v',var),ONE)})
        if any(s.get('op')=='sum_clear_denominators' for s in step['steps']):
            lines.append('Знаменатели обеих частей перехода ненулевые при каждом целом индексе на исходном хвосте. Умножим равенство на их произведение.')
        if any(node['rule']=='sum.integer_power_normal' for node in nodes.values()):
            lines.append('У фиксированного ненулевого основания целочисленный сдвиг показателя даёт постоянный множитель. После его выделения складываем подобные слагаемые.')
        lines.append(f'К S({var}) прибавляется '+pretty(following,var)+'. После подстановки гипотезы проверено '+equality(step,var)+'.')
        lines.append('База и переход доказаны. Правило индукции снимает временную гипотезу.')
    else:
        primitive=nodes[root['steps'][0]['proof']]
        diff=nodes[primitive['steps'][-1]['proof']]
        lines.append(f'Из слагаемого построена функция W({var}) = '+pretty(primitive['value'],var)+'.')
        lines.append(f'Проверено W({var})−W({var}−1) = '+pretty(diff['goal'][2],var)+'.')
        lines.append(f'Суммирование оставляет W({upper})−W({start-1}). Проверка заявленной формулы даёт '+equality(root,upper)+'.')
    lines.append(f'Исходное утверждение доказано для всех целых {upper}≥{ctx["integer_start"]}.')
    return '\n'.join(lines)


def sequence_term_at(task,library,request):
    """Evaluate the raw sequence at one integer, retaining the original divisor at any hole."""
    from polynomial import ResourceBound,trim
    from tasks import finite_prefix_limit_input,source
    fields={'kind','sequence_task','index_value','parameter_values'}
    if (not library.data.get('scoped_sequence_nonzero') or set(task)-{'id'}!=fields
            or not isinstance(task['sequence_task'],dict)):
        raise Unsupported('Не установлены исходная последовательность и данные точки')
    outer,expression,params,_=finite_prefix_limit_input(task['sequence_task'])
    n,values=task['index_value'],task['parameter_values']
    if type(n) is not int or n<1 or not isinstance(values,dict) or set(values)!=set(params):
        raise Unsupported('Для этой точки нужен натуральный индекс и значение каждого фиксированного параметра')
    env={outer:Fraction(n)}
    for name,value in values.items():
        if type(value) not in (int,str) or not re.fullmatch(r'[+-]?\d+(?:/\d+|\.\d+)?',str(value)):
            raise Unsupported('Значение фиксированного параметра должно быть точным рациональным числом')
        try:env[name]=Fraction(value)
        except ZeroDivisionError as exc:raise Unsupported('Знаменатель значения параметра в точке равен нулю') from exc
        if abs(env[name])>=1:raise Unsupported('Точка не удовлетворяет исходному ограничению на модуль параметра')
    plan=dict(scope='point',variable=outer,index_value=n,parameter_values={p:q(env[p]) for p in params},sums=[],divisors=[])
    sources={};sums=[];parts=[];cursor=0
    for begin,end,index,lo,endpoint,offset,term in prefix_occurrences(expression):
        if endpoint!=outer or index in env or n+offset<lo-1:
            raise Unsupported('Границы суммы в указанной точке не установлены')
        m.context(dict(variable=index,parameters=[outer,*params]))
        marker='__point_sum'+str(len(sums))
        while marker in expression or marker in env:marker+='_'
        raw=m.parse(term,index,[outer,*params])
        sources[marker]=expression[begin:end]
        sums.append((marker,index,lo,n+offset,raw))
        parts.extend((expression[cursor:begin],'('+marker+')'));cursor=end
    raw=m.parse(''.join(parts)+expression[cursor:],outer,[*params,*sources])

    def guard(e,value,binding):
        text=re.sub(r'[A-Za-z_][A-Za-z_0-9]*',lambda match:sources.get(match[0],match[0]),source(e))
        plan['divisors'].append(dict(expression=text,value=q(value),bound_indices=binding))
        if value==0:raise Undefined(text)

    def evaluate(e,binding,initial_power=False):
        op=e[0]
        if op=='q':return rational(e)
        if op in ('v','s'):return env[e[1]]
        if op not in ('add','mul','div','pow','rpow'):
            raise Unsupported('Точное значение этой операции в указанной точке ещё не установлено')
        left=evaluate(e[1],binding)
        right=Fraction(e[2]) if op=='pow' else evaluate(e[2],binding)
        if op=='add':value=left+right
        elif op=='mul':value=left*right
        elif op=='div':
            guard(e[2],right,binding)
            value=left/right
        else:
            if right.denominator!=1:raise Unsupported('Для вычисления степени требуется целый показатель')
            if abs(right)>m.MAX_INTEGER_POWER:raise ResourceBound('Превышен диапазон точного вычисления целой степени')
            if op=='rpow' and left<=0 and any(m.contains(e[2],('s',p)) for p in params):
                raise Unsupported('Целочисленная область переменного показателя не установлена')
            if right<0 or right==0 and not initial_power:guard(e[1],left,binding)
            value=left**int(right)
        return trim((value,))[0]

    try:
        for marker,index,lo,hi,term in sums:
            if hi-lo+1>4000:raise ResourceBound('Для такой длины суммы требуется формула вместо прямого вычисления в точке')
            total=Fraction(0)
            # The polynomial convention q^0=1 applies to the initial monomial of a geometric sum.
            monomial=(lo==0 and term[0]=='rpow' and term[1][0]=='s' and term[1][1] in params and term[2]==('v',index))
            for k in range(lo,hi+1):
                env[index]=Fraction(k)
                total=trim((total+evaluate(term,{index:k},monomial),))[0]
            env[marker]=total
            plan['sums'].append(dict(expression=sources[marker],lower=lo,upper=hi,value=q(total)))
        value=evaluate(raw,{})
    except Undefined as exc:
        return plan,dict(defined=False,zero_divisor=str(exc))
    return plan,dict(defined=True,value=q(value))


def factorial_weighted_sum(task,saved):
    """Expand P(n) in falling factorials; replay checks the polynomial identity."""
    from graphs import peval
    from math import factorial
    from polynomial import trim
    name,start=task['index'],task['start_index']
    if start<0 or task.get('stated_conditions'):raise Unsupported('Need nonnegative factorial indices and the original parameter domain')
    names=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',task['term']))-{name,'factorial','e','pi'}-set(m.FUNCTIONS)-set(m.ALIASES)
    params=task.get('parameters',sorted(names));ctx=m.context(dict(variable=name,parameters=params))
    raw=m.parse(task['term'],name,params,extra_functions={'factorial'})
    if raw[0]!='div':raise Unsupported('A single factorial denominator is required')
    atom=('factorial',('v',name));count=0;base=ONE
    def peel(e,denominator):
        nonlocal base,count
        if e[0]=='mul':return ('mul',peel(e[1],denominator),peel(e[2],denominator))
        if e==atom and denominator:
            count+=1;return ONE
        if e[0]=='rpow' and e[2]==('v',name) and m.constant_defined(e[1],ctx):
            x=m.simplify(e[1])
            if denominator and not m.nonzero(x,ctx):raise Unsupported('The exponential scale in the source denominator may vanish')
            base=m.div(base,x) if denominator else m.mul(base,x)
            return ONE
        return e
    weight=('div',peel(raw[1],False),peel(raw[2],True))
    if count!=1:raise Unsupported('A factorial with the same running index is required')
    try:poly=coefficients(weight,name,start)
    except (NotRational,Undefined) as exc:raise Unsupported('The remaining factorial weight is not a polynomial') from exc
    values=[peval(poly,i) for i in range(len(poly))]
    if saved is None:
        cs=[]
        while values:
            cs.append(values[0]/factorial(len(cs)));values=[b-a for a,b in zip(values,values[1:])]
    else:
        cs=[rational(freeze(v)) for v in saved.get('falling_coefficients',())]
    if len(cs)!=len(poly):raise Unsupported('Missing falling-factorial coefficient')
    u=(Fraction(1),);rebuilt=(Fraction(0),);exponential_weight=ZERO
    for j,c in enumerate(cs):
        rebuilt=pa(rebuilt,tuple(c*b for b in u));u=pm(u,(-j,Fraction(1)))
        exponential_weight=m.add(exponential_weight,m.mul(q(c),m.power(base,j)))
    if trim(rebuilt)!=trim(poly):raise Unsupported('Falling factorials do not reproduce the source polynomial')
    omitted=ZERO
    for i in range(start):
        omitted=m.add(omitted,m.mul(q(peval(poly,i)/factorial(i)),m.power(base,i)))
    value=m.simplify(m.add(m.mul(exponential_weight,('exp',base)),m.neg(omitted)))
    return dict(theorem='method.factorial_polynomial_series',index=name,start=start,base=base,
                falling_coefficients=list(map(q,cs)),omitted=omitted),value




def rational_product_witness(term,name,numerator,denominator):
    """Find F(n)/F(n-1) from shift-equivalent monic polynomial factors."""
    from integrals import denominator_factors,polynomial_expression
    from tasks import source
    a,b=numerator,denominator
    if len(a)!=len(b) or a[-1]!=b[-1]:return None
    g=pgcd(a,b);a,b=pdiv(a,g)[0],pdiv(b,g)[0]
    top=bottom=(Fraction(1),)
    while len(a)>1:
        candidates=denominator_factors(term,b,name)
        match=None
        for f in denominator_factors(term,a,name):
            for h in candidates:
                if len(f)!=len(h):continue
                step=(f[-2]-h[-2])/(len(f)-1)
                if step.denominator==1 and translated_coefficients(h,int(step))==f:
                    match=f,h,int(step);break
            if match:break
        if not match:return None
        f,h,step=match
        a,b=pdiv(a,f)[0],pdiv(b,h)[0]
        for offset in range(0,step) if step>0 else range(step,0):
            shifted=translated_coefficients(f,-offset)
            if step>0:top=pm(top,shifted)
            else:bottom=pm(bottom,shifted)
    return source(m.div(polynomial_expression(top,name),polynomial_expression(bottom,name)))


def infinite_rational_product(task,library,request,saved=None):
    """Prove the normalized finite product by induction, or test logarithmic convergence."""
    from graphs import peval
    from integrals import polynomial_expression
    from polynomial import trim
    from tasks import source
    allowed={'kind','id','source','factor_or_given','index','start_index','parameters','stated_conditions','method_requirement','claimed_value'}
    origin=task.get('source',{});kind=task['kind'];start=task['start_index'];name=task['index']
    if (set(task)-allowed or not isinstance(origin,dict)
            or set(origin)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
            or type(start)!=int or not isinstance(name,str) or not name.isidentifier()
            or task.get('stated_conditions') or task.get('method_requirement') not in (None,'telescoping')):
        raise Unsupported('Unbound product domain, method, or required output')
    literal=origin.get('literal_requirement');goal=task.get('claimed_value')
    if kind=='infinite_product_identity':
        text=re.fullmatch(r'Доказать равенство =(.+)\.',literal or '') if literal else None
        if literal and not text or text and goal not in (None,text[1]):raise Unsupported('The printed equality is not bound')
        goal=text[1] if text else goal
        if not isinstance(goal,str):raise Unsupported('The requested product identity has no conclusion')
    elif goal is not None or literal not in (None,{'infinite_product_value':'convergence and value','infinite_product_convergence':'investigate convergence'}[kind]):
        raise Unsupported('The printed product requests an additional conclusion')
    text=task['factor_or_given']
    symbols=set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',text))-{name,'pi','e'}-m.FUNCTIONS-set(m.ALIASES)
    params=task.get('parameters',sorted(symbols))
    if not isinstance(params,(list,tuple)) or any(not isinstance(p,str) for p in params):
        raise Unsupported('Unbound real parameters of the product')
    term=m.parse(text,name,params)
    if library.data.get('wave_product_limit') and kind!='infinite_product_convergence' and term[0] in ('cos','cosh'):
        if kind=='infinite_product_value' and literal:
            raise Unsupported('The additional printed convergence classification requires the zero set of the factors')
        return wave_product_limit(task,term,params,goal,request)
    if not library.data.get('rational_partial_product') or task.get('parameters'):
        raise Unsupported('The rational product requires a fixed rational factor on the original index domain')
    if goal is not None:
        claim=m.parse(goal,None)
        if not m.constant_defined(claim,m.context({'variable':name})):raise Unsupported('Undefined right-hand side')
    try:a,b=rational_on_tail(term,name,start)
    except (NotRational,Undefined) as exc:raise Unsupported('The original factor is not a defined rational expression on the integer tail') from exc
    runs=integer_sign_runs(pm(a,b),start);zero=next((k for k,s in runs if s==0),None)
    plan=dict(index=name,start=start,factor_sign_runs=runs)
    witness=(saved.get('witness') if saved is not None else rational_product_witness(term,name,a,b)) if zero is None else None
    if zero is not None:
        if task.get('method_requirement'):raise Unsupported('The requested telescoping proof has a zero factor')
        plan.update(theorem='exact_zero_factor',zero_index=zero);answer=ZERO;classification='converges_to_zero_by_zero_factor'
    elif witness is not None:
        raw=m.parse(witness,name)
        try:p,d=rational_on_tail(raw,name,start-1)
        except (NotRational,Undefined) as exc:raise Unsupported('The saved boundary factor is not rational') from exc
        base=peval(p,start-1)/peval(d,start-1)
        if not base:raise Unsupported('Boundary normalization vanishes at the empty product')
        p,d=trim(p),trim(tuple(c*base for c in d))
        if pm(pm(a,translated_coefficients(p,-1)),d)!=pm(pm(b,p),translated_coefficients(d,-1)):
            raise Unsupported('The proposed boundary factor fails the integer-shift identity')
        prefix=source(m.div(polynomial_expression(p,name),polynomial_expression(d,name)))
        answer=freeze(request('limit of the verified finite product',dict(kind='limit',variable=name,expression=prefix,
                     variable_domain='positive_integers',approach={'point':'+inf','side':'positive_infinity'}))['value'])
        expected=('+inf' if p[-1]/d[-1]>0 else '-inf') if len(p)>len(d) else q(p[-1]/d[-1]) if len(p)==len(d) else ZERO
        if answer!=expected:raise Unsupported('The endpoint limit disagrees with the certified rational leading terms')
        classification='diverges_unbounded' if isinstance(answer,str) else 'diverges_to_zero' if answer==ZERO else 'converges_nonzero'
        plan.update(theorem='method.rational_partial_product',witness=witness,normalized_prefix=prefix,empty_value=ONE,base_index=start-1)
    else:
        if kind!='infinite_product_convergence' or task.get('method_requirement') or any(s!=1 for _,s in runs):
            raise Unsupported('No applicable positive logarithmic comparison or exact boundary quotient')
        delta=pa(a,tuple(-v for v in b))
        # Positive rational factors either stay away from 1 or have log(f) ~ f-1.
        # A nonzero rational asymptote C/n^k has integer order.
        order=len(b)-len(delta);lead=delta[-1]/b[-1]
        if not any(delta) or order>1:answer=None;classification='converges_nonzero'
        else:
            positive=lead>0
            answer='+inf' if positive else ZERO;classification='diverges_unbounded' if positive else 'diverges_to_zero'
        plan.update(theorem='method.rational_product_log_comparison',difference_order=order if any(delta) else None,leading_coefficient=q(lead))
    if kind=='infinite_product_identity':
        from verify import same_value
        if answer is None or isinstance(answer,str) or not same_value(answer,claim):raise Unsupported('The proven limit does not equal the claimed value')
    result=dict(classification=classification)
    if answer is not None:result['partial_product_limit']=answer
    return plan,result


def interpolation_polynomial(task,library):
    """Build the interpolation polynomial and certify its values in the stated space."""
    from graphs import peval
    from verify import same_value
    from uniform import interval_guard
    data=task['description'];wanted=task['requested_output']
    fields={'nodes','parameters','uniform_grid','function','interval','allowed_degrees','evaluate_at','integrate_over'}
    approximation_input(task,library,'polynomial_interpolation',fields,{None,'lagrange_interpolation'})
    if not wanted or len(wanted)!=len(set(wanted)):
        raise Unsupported('A nonempty list of distinct interpolation goals is required')
    parameters=data.get('parameters',[]);X=('v','x')
    ctx=m.context(dict(variable='x',parameters=parameters))
    nodes=[(Fraction(a),m.parse(b,None,parameters)) for a,b in data['nodes']]
    if (not 1<=len(nodes)<=32 or len({a for a,_ in nodes})!=len(nodes) or
            not all(m.constant_defined(y,ctx) for _,y in nodes)):
        raise Unsupported('Distinct abscissas and defined ordinates are required')
    if ('function' in data)!=('interval' in data):
        raise Unsupported('Both the source function and its sampling interval are required')
    if 'function' in data:
        raw=m.parse(data['function'],'x',parameters)
        a,b=map(Fraction,data['interval'])
        if not a<b or not all(a<=x<=b for x,_ in nodes):
            raise Unsupported('An interpolation node lies outside the original interval')
        for relation,g in domain_conditions(raw):
            interval_guard(relation,g,'x',(q(a),q(b),True,True),ctx)
        if any(not same_value(m.simplify(m.substitute(raw,{X:q(a)})),y) for a,y in nodes):
            raise Unsupported('An ordinate is inconsistent with the source function')
    powers=data.get('allowed_degrees')
    if powers is None:
        bases=[]
        for j,(x,_) in enumerate(nodes):
            b=(Fraction(1),);d=Fraction(1)
            for i,(u,_) in enumerate(nodes):
                if i!=j:b=pm(b,(-u,Fraction(1)));d*=x-u
            bases.append(tuple(z/d for z in b))
        if any(peval(b,x)!=int(i==j) for j,b in enumerate(bases) for i,(x,_) in enumerate(nodes)):
            raise Unsupported('A Lagrange basis has incorrect values at the nodes')
        coefficients=[m.dot([q(b[i]) for b in bases],[v for _,v in nodes]) for i in range(len(nodes))]
        witness=dict(basis=[list(map(q,b)) for b in bases])
    else:
        if task.get('method_requirement') or powers!=sorted(set(powers)) or not powers or any(type(k)!=int or not 0<=k<=32 for k in powers):
            raise Unsupported('The requested polynomial space is not compatible with Lagrange interpolation')
        values=[m.num(m.simplify(y)) for _,y in nodes]
        if any(y is None for y in values):raise Unsupported('Numeric constrained interpolation required')
        columns=[tuple(x**k for x,_ in nodes) for k in powers]
        if any(span_coefficients(column,columns[:j]) is not None for j,column in enumerate(columns)):
            raise Unsupported('The prescribed evaluation matrix does not have independent columns')
        coeff=span_coefficients(values,columns)
        if coeff is None:raise Unsupported('There is no unique solution in the prescribed polynomial space')
        coefficients=[ZERO]*(max(powers)+1)
        for i,c in zip(powers,coeff,strict=True):coefficients[i]=q(c)
        witness=dict(powers=powers,evaluation_matrix=[list(map(q,c)) for c in columns])
    coefficients=[m.simplify(c) for c in coefficients]
    while len(coefficients)>1 and coefficients[-1]==ZERO:coefficients.pop()
    P=lambda x:m.simplify(m.dot(coefficients,[m.power(x,i) for i in range(len(coefficients))]))
    if any(not same_value(P(q(x)),y) for x,y in nodes):
        raise Unsupported('The polynomial does not interpolate every original value')
    plan=dict(theorem='method.polynomial_interpolation',nodes=[(q(a),b) for a,b in nodes],
              coefficients=coefficients,source_function=data.get('function'),witness=witness)
    value={}
    for output in wanted:
        if output in ('polynomial','minimal_degree_polynomial'):
            if output=='minimal_degree_polynomial' and (powers is not None or parameters):
                raise Unsupported('The least degree needs a nonzero leading coefficient in every case')
            value[output]=P(X)
        elif output=='point_values' and 'evaluate_at' in data:
            value[output]=[(q(x),P(q(x))) for x in map(Fraction,data['evaluate_at'])]
        elif output=='integral_of_polynomial' and 'integrate_over' in data:
            a,b=map(Fraction,data['integrate_over'])
            value[output]=m.simplify(m.dot(coefficients,[q((b**i-a**i)/i) for i in range(1,len(coefficients)+1)]))
            value['polynomial']=P(X)
        elif output=='parabola_and_degeneracies' and 'uniform_grid' in data and powers is None and len(nodes)==3:
            grid=data['uniform_grid']
            if set(grid)!={'center','step'}:raise Unsupported('An evenly spaced grid needs its center and its step')
            center,step=(m.parse(grid[s],None,parameters) for s in ('center','step'))
            if not all(m.constant_defined(e,ctx) for e in (center,step)):
                raise Unsupported('The original node coordinates are not defined')
            displacement=m.add(X,m.neg(center));scaled=m.div(displacement,step)
            distinct=dict(condition=('nonzero',step),polynomial=P(scaled),
                          parabola_condition=('nonzero',coefficients[2] if len(coefficients)>2 else ZERO))
            initial=nodes[0][1]
            repeated=dict(condition=('zero',step),consistent_when=[('equal',initial,y) for _,y in nodes[1:]],
                          all_parabolas_through=(center,initial),otherwise='no_solution')
            value[output]=dict(distinct_nodes=distinct,coincident_nodes=repeated)
            plan['affine_node_map']=(center,step)
        else:raise Unsupported('A requested interpolation conclusion remains unproved')
    consumed={'evaluate_at':'point_values','integrate_over':'integral_of_polynomial','uniform_grid':'parabola_and_degeneracies'}
    if any((field in data)!=(output in wanted) for field,output in consumed.items()):
        raise Unsupported('The supplied interpolation data and requested goals disagree')
    return plan,value


def approximation_input(task,library,capability,description,methods):
    allowed={'id','kind','source','description','requested_output','method_requirement'}
    provenance={'exercise','printed_subpart','printed_page','pdf_page','pdf_pages','pdf_sha256','page_png_sha256'}
    meta=task.get('source',{})
    if (not library.data.get(capability) or set(task)-allowed or not isinstance(meta,dict) or set(meta)-provenance or
            set(task['description'])-description or task.get('method_requirement') not in methods):
        raise Unsupported('An additional source expression, method or obligation remains')


def bernstein_polynomial(task,library):
    """Apply the binomial weights on a verified affine sampling interval."""
    from ray_proofs import compare_scalar
    from uniform import interval_guard
    from verify import same_value
    data=task['description'];X=('v','x')
    approximation_input(task,library,'bernstein_polynomials',{'function','interval','order','parameters','abstract_function'},
                        {'bernstein_polynomials',None})
    if task['requested_output']!=['bernstein_polynomials']:raise Unsupported('Only the construction of the whole Bernstein polynomial is established')
    params=data.get('parameters',[]);ctx=m.context(dict(variable='x',parameters=params))
    a,b=[m.parse(z,None,params) for z in data['interval']]
    if not all(m.constant_defined(z,ctx) for z in (a,b)):
        raise Unsupported('Undefined original sampling interval endpoint')
    length=m.simplify(m.add(b,m.neg(a)));sign=m.sign(length,ctx)
    if sign is None and not params:sign=compare_scalar(b,a)
    if sign==-1:raise Unsupported('The original sampling interval is reversed')
    degree=data['order']
    if type(degree) is int:
        if not 1<=degree<=128:raise Unsupported('A positive supported degree is required')
        N=q(degree)
    elif degree in ('n','2*n') and 'n' not in params:N=m.mul(q(1 if degree=='n' else 2),('s','n'))
    else:raise Unsupported('A positive integer degree with a fresh index is needed')
    u=('v','__bernstein_u');i=('s','__bernstein_i')
    if {u[1],i[1]}&set(params):raise Unsupported('An auxiliary coordinate would capture a source parameter')
    inputs=data['function'] if isinstance(data['function'],list) else [data['function']]
    if not inputs:raise Unsupported('No original function to approximate')
    rows=[];result=[]
    for text in inputs:
        if data.get('abstract_function'):
            fn=re.fullmatch(r'([A-Za-z][A-Za-z_0-9]*)\(x\)',text)
            if not fn or fn[1] in m.FUNCTIONS or fn[1] in params:raise Unsupported('A source function defined on the whole interval is required')
            raw=('function_value',fn[1],X)
        else:
            raw=m.parse(text,'x',params)
            for predicate,g in domain_conditions(raw):
                interval_guard(predicate,g,'x',(a,b,True,True),ctx)
        sample=lambda t:m.simplify(m.substitute(raw,{X:m.simplify(m.add(a,m.mul(length,t)))}))
        if sign==0:
            result.append(dict(on_singleton=sample(ZERO)));rows.append(dict(method='singleton'));continue
        if type(degree) is int:
            points=[sample(q(k,degree)) for k in range(degree+1)]
            P=m.simplify(m.dot(points,[m.mul(q(comb(degree,k)),m.mul(m.power(u,k),m.power(m.add(ONE,m.neg(u)),degree-k)))
                                      for k in range(degree+1)]))
            rows.append(dict(method='binomial_samples',samples=points))
        else:
            try:p,d=rf(raw,'x')
            except NotRational:p,d=(),()
            if p and len(d)==1 and m.num(a) is not None and m.num(length) is not None and len(p)<=13:
                # Convert the affine pullback to powers of i/N, then convert powers to falling factorials.
                powers=(Fraction(0),)
                for c in reversed(p):powers=pa(pm(powers,(m.num(a),m.num(length))),(c/d[0],))
                stir=[1];terms=[]
                for exponent,c in enumerate(powers):
                    ratio=m.power(N,-exponent) if exponent else ONE;fall=ONE
                    for k,coef in enumerate(stir):
                        if coef and c:terms.append(m.mul(q(c*coef),m.mul(ratio,m.mul(fall,m.power(u,k)))))
                        fall=m.mul(fall,m.add(N,q(-k)))
                    stir=[(stir[k-1] if k else 0)+(k*stir[k] if k<len(stir) else 0) for k in range(len(stir)+1)]
                P=m.simplify(m.dot(terms,[ONE]*len(terms))) if terms else ZERO
                rows.append(dict(method='binomial_falling_factorial_moments',affine_power_coefficients=list(map(q,powers))))
            elif raw[0] in ('exp','sin','cos'):
                phase=raw[1];v0=m.substitute(phase,{X:ZERO});slope=m.simplify(m.add(m.substitute(phase,{X:ONE}),m.neg(v0)))
                if not same_value(phase,m.add(v0,m.mul(slope,X))):raise Unsupported('A binomial generating polynomial needs an affine phase')
                phase0=m.simplify(m.substitute(phase,{X:a}));step=m.div(m.mul(length,slope),N)
                P=dict(operation={'exp':'real_exponential','sin':'imaginary_part','cos':'real_part'}[raw[0]],phase=phase0,
                       generating_polynomial_base=dict(constant=m.add(ONE,m.neg(u)),weight=u,phase_increment=step),power=N)
                rows.append(dict(method='binomial_generating_function',sample_phase=(phase0,step)))
            else:
                P=dict(operation='finite_bernstein_sum',index=i,from_index=0,to_index=N,
                       sample_value=sample(m.div(i,N)),binomial=[N,i],left_weight=(u,i),right_weight=(m.add(ONE,m.neg(u)),m.add(N,m.neg(i))))
                rows.append(dict(method='affine_sample_formula',sample_point=m.add(a,m.mul(length,m.div(i,N)))))
        result.append(dict(polynomial=P,coordinate=u,normalization=m.div(m.add(X,m.neg(a)),length),
                           on_nondegenerate_interval=('positive',length),
                           on_singleton=sample(ZERO) if sign is None else None))
    return dict(theorem='method.bernstein_polynomials',interval=(a,b),degree=N,rows=rows),dict(bernstein_polynomials=result)


def factorial_reduction(data):
    """Normalize exact factorials, parity products, and two elementary integral recurrences."""
    form=data.get('source_form')
    fields={None:{'factorials','twos','pi_power','constant'},
            'binomial':{'upper','lower'},'odd_double_factorial':{'factor_count','inverted'},
            'arithmetic_product':{'first','step','last'},'arithmetic_product_ratio':{'numerator','denominator'},
            'power_weight_integral':{'base','exponent','interval'}}
    if form not in fields or set(data)-fields[form]-{'source_form','mode','outer_order','outer_power','denominator'}:
        raise Unsupported('Unparsed factorial expression')
    if form is None:
        return data['factorials'],data.get('twos',0),data.get('pi_power',0),Fraction(data.get('constant','1')),'direct_factorial_product'
    if form=='binomial':
        a,b=data['upper'],data['lower']
        return [(a,1),(b,-1),(f'({a})-({b})',-1)],0,0,Fraction(1),'binomial_factorials'
    if form=='odd_double_factorial':
        if type(data.get('inverted',False)) is not bool:raise Unsupported('The inversion of the odd product was not bound')
        n=data['factor_count'];power=-1 if data.get('inverted',False) else 1
        return [(f'2*({n})',power),(n,-power)],f'{-power}*({n})',0,Fraction(1),'split_even_from_full_factorial'
    if form in ('arithmetic_product','arithmetic_product_ratio'):
        sequences=[([data[k] for k in ('first','step','last')],1)] if form=='arithmetic_product' else [
            (data['numerator'],1),(data['denominator'],-1)]
        factors=[];twos=0
        for (first,step,last),power in sequences:
            if any(type(v)!=int for v in (first,step,last)) or first not in (1,2) or step!=2 or last<first or (last-first)%2:
                raise Unsupported('The consecutive odd or even product was not established')
            n=(last-first)//2+1
            factors.append((str(n),power if first==2 else -power))
            if first==1:factors.append((str(2*n),power))
            twos+=power*n*(1 if first==2 else -1)
        return factors,twos,0,Fraction(1),'split_even_from_full_factorial'
    k=data['exponent'];base=m.parse(data['base'],'x');a,b=[m.parse(x,None) for x in data['interval']]
    if type(k)!=int or not 0<=k<=2048:raise Unsupported('A finite nonnegative power is required')
    if base==m.parse('1-x^2','x') and (a,b)==(ZERO,ONE):
        return [(str(k),2),(str(2*k+1),-1)],2*k,0,Fraction(1),'parts_recurrence_I(k)/I(k−1)=2k/(2k+1), I(0)=1'
    if base in (('sin',('v','x')),('cos',('v','x'))) and k%2==0 and (a,m.simplify(b))==(ZERO,m.mul(q(2),m.PI)):
        return [(str(k),1),(str(k//2),-2)],-k,1,Fraction(2),'period_symmetry_and_parts_J(k)/J(k−2)=(k−1)/k'
    raise Unsupported('No verified exact integral recurrence on the source interval')


def stirling_factorials(task,library):
    """Compose log-Stirling leading terms and directed remainder intervals."""
    from quadrature import enclose,outward,product,power as interval_power,monotone
    from math import factorial
    data=task['description'];mode=data['mode']
    fields={'source_form','factorials','twos','pi_power','constant','upper','lower','factor_count','inverted','first',
            'step','last','numerator','denominator','base','exponent','interval','mode','outer_order','outer_power'}
    approximation_input(task,library,'stirling_factorials',fields,{'stirling_formula',None})
    if task['requested_output']!=[mode] or mode not in ('approximation','log10_approximation','asymptotic_equivalent','limit','log_ratio_limit'):
        raise Unsupported('Another target of the factorial calculation remains')
    if ('outer_order' in data or 'outer_power' in data) != (mode=='limit') or ('denominator' in data and data.get('source_form')!='arithmetic_product_ratio')!=(mode=='log_ratio_limit'):
        raise Unsupported('Unbound root order, outer power or logarithmic denominator')
    if mode=='log_ratio_limit' and data['denominator']!='n*ln(n)':
        raise Unsupported('The original logarithmic comparison scale is unproved')
    factors,twos,pi,constant,reduction=factorial_reduction(data)
    if constant<=0 or type(pi)!=int or not 1<=len(factors)<=32:raise Unsupported('A positive factorial product is necessary')
    n=('v','n');ln=lambda z:m.simplify(('ln',z))
    def affine_integer(z):
        try:p,d=rf(m.parse(str(z),'n'),'n')
        except (NotRational,Undefined) as exc:raise Unsupported('A factorial argument is not integral affine on the index domain') from exc
        if len(d)!=1 or len(p)>2:raise Unsupported('An affine index of a factorial or scalar power is required')
        p=[v/d[0] for v in p]+[Fraction(0)]*(2-len(p))
        if any(z.denominator!=1 or abs(z)>10**7 for z in p):raise Unsupported('The original factorial indices are out of the exact integer range')
        return tuple(map(int,p))
    constant_twos,linear_twos=affine_integer(twos)
    log_scale=ln(q(2));half_log=m.div(ln(m.mul(q(2),m.PI)),q(2))
    fixed=m.add(ln(q(constant)),m.add(m.mul(q(pi),ln(m.PI)),m.mul(q(constant_twos),log_scale)))
    linear=m.mul(q(linear_twos),log_scale);nlog=Fraction(0);logn=Fraction(0);error_lo=error_hi=Fraction(0)
    arguments=[];remainder=[]
    for expr,weight in factors:
        if type(weight)!=int or abs(weight)>128:raise Unsupported('A factorial needs an integer multiplicity')
        b,a=affine_integer(expr)
        if a<0 or a+b<0:raise Unsupported('Negative factorial argument on the positive integer domain')
        arguments.append(dict(argument=(b,a),multiplicity=weight))
        if not weight or a==b==0:continue
        if a:
            if mode in ('approximation','log10_approximation'):
                raise Unsupported('No fixed integer has been supplied for the numerical approximation')
            scale=ln(q(a));c=Fraction(b)+Fraction(1,2)
            nlog+=weight*a;logn+=weight*c
            linear=m.add(linear,m.mul(q(weight*a),m.add(scale,q(-1))))
            fixed=m.add(fixed,m.mul(q(weight),m.add(m.mul(q(c),scale),half_log)))
            remainder.append(dict(argument=(b,a),bound='O(1/n)',source='Stirling remainder and log(1+B/(A n))'))
        elif mode not in ('approximation','log10_approximation'):
            if b>256:raise Unsupported('The fixed factorial exceeds the exact constant range')
            fixed=m.add(fixed,m.mul(q(weight),ln(q(factorial(b)))))
            arguments[-1]['exact_constant']=q(factorial(b))
        else:
            leading=m.add(m.mul(q(Fraction(b)+Fraction(1,2)),ln(q(b))),m.add(q(-b),half_log))
            fixed=m.add(fixed,m.mul(q(weight),leading))
            error_lo+=min(Fraction(0),Fraction(weight,12*b));error_hi+=max(Fraction(0),Fraction(weight,12*b))
    fixed=m.simplify(fixed);linear=m.simplify(linear)
    plan=dict(theorem='method.stirling_factorials',factorial_arguments=arguments,exact_reduction=reduction,
              twos_power=(constant_twos,linear_twos),pi_power=pi,constant=q(constant),
              logarithm_terms=dict(n_log_n=q(nlog),n=linear,log_n=q(logn),constant=fixed),
              asymptotic_remainders=remainder,constant_log_error=[q(error_lo),q(error_hi)])
    numeric=mode in ('approximation','log10_approximation')
    if numeric:
        if nlog or logn or linear!=ZERO:raise Unsupported('A free index remains in the numerical problem')
        l,h=enclose(fixed,None);bounds=outward(l+error_lo,h+error_hi);logten=enclose(ln(q(10)),None)
        if mode=='log10_approximation':
            app=product((l,h),interval_power(logten,-1))
            answer=dict(approximation=q(sum(app)/2),verified_enclosure=list(map(q,product(bounds,interval_power(logten,-1)))))
        else:
            decade=(sum((l,h))/sum(logten)).__floor__()
            a,b=product((Fraction(decade),)*2,logten)
            app=monotone('exp',outward(l-b,h-a));corrected=monotone('exp',outward(bounds[0]-b,bounds[1]-a))
            answer=dict(mantissa=q(sum(app)/2),decimal_power=decade,verified_mantissa_enclosure=list(map(q,corrected)))
        return plan,answer
    if error_lo or error_hi:
        raise Unsupported('A fixed factorial requires its exact constant in an asymptotic equivalence')
    if mode=='log_ratio_limit':
        return plan,dict(limit=q(nlog),tail_denominator='n*ln(n)>0 for n>=2')
    if mode=='limit':
        order=data.get('outer_order');offset=data.get('outer_power')
        if type(order)!=int or order<1 or type(offset)!=int:raise Unsupported('The printed normalizing powers were not established')
        log_coefficient=nlog+offset if order==1 else offset
        finite=m.simplify(('exp',linear)) if order==1 else ONE
        return plan,dict(limit='+inf' if log_coefficient>0 else ZERO if log_coefficient<0 else finite)
    L=m.add(m.mul(q(nlog),m.mul(n,ln(n))),m.add(m.mul(linear,n),m.add(m.mul(q(logn),ln(n)),fixed)))
    if nlog==0:
        factor=m.simplify(('exp',m.add(m.mul(linear,n),fixed)))
        expr=m.mul(factor,('rpow',n,q(logn))) if logn else factor
    else:expr=('exp',L)
    return plan,dict(asymptotic_equivalent=m.simplify(expr),index_domain='positive integers')


def products_and_approximation(task,library):
    """Bind a mathematical statement to a general proof with its source hypotheses."""
    d=task['description'];form=d['form'];method=task.get('method_requirement')
    approximation_input(task,library,'product_approximation_theorems',set(d),{None,'wallis_formula','wallis_constant'})
    if task['requested_output']!=['prove_printed_claim']:
        raise Unsupported('An additional conclusion of the printed statement remains')
    if method!={'wallis_odd_even':'wallis_formula','stirling_normalization':'wallis_constant'}.get(form):
        raise Unsupported('The obligatory product method has changed')
    def bind(**givens):
        if d!={'form':form,**givens}:raise Unsupported('The mathematical hypotheses, binder or conclusion do not match')
    def proof(*steps,**value):
        return dict(theorem='method.product_approximation_theorems',argument=form,source_hypotheses=d,steps=steps),value
    n=d.get('index','n')
    if not isinstance(n,str) or not n.isidentifier():raise Unsupported('The index is not bound')
    if form=='euler_prime_product':
        bind(index=n,start_index=1,factor=f'1/(1-1/p_{n})',sequence='successive_primes',
             claims=['product_diverges','reciprocal_series_diverges'])
        return proof('Expand each positive geometric factor. Unique factorization puts every integer below the next prime among the denominators.',
                     'The resulting product dominates arbitrarily long harmonic sums.',
                     'For 0≤u≤1/2, −ln(1−u)≤2u. Apply u=1/p to the unbounded logarithms of the partial products.',
                     product_limit='+inf',reciprocal_series='diverges_to_positive_infinity')
    if form=='consecutive_ratio_decay':
        seq,p,eps=d['sequence'],d['linear_exponent'],d['remainder_exponent']
        if not all(isinstance(v,str) and v.isidentifier() for v in (seq,p,eps)) or len({n,seq,p,eps})!=4:
            raise Unsupported('Sequence and real parameters must be independent')
        bind(index=n,start_index=1,sequence=seq,positive=True,ratio=f'{seq}_{n}/{seq}_({n}+1)',
             linear_exponent=p,remainder_exponent=eps,remainder_order=f'O({n}^(-1-{eps}))',
             assumptions=[eps+'>0'],claim=f'finite_positive_limit_of_{seq}_{n}*{n}^{p}')
        return proof('For B(n)=a(n)n^p, expand (1+1/n)^p=1+p/n+O(n^-2) at zero.',
                     'The linear terms cancel in B(n+1)/B(n). This ratio is 1+O(n^(-1-min(1,epsilon))).',
                     'On the positive tail the logarithm has the same summable bound. The telescoping logarithms converge to a real number.',
                     normalized_limit='finite_positive',decay='a(n) ~ C/n^p with C>0')
    if form=='wallis_odd_even':
        bind(index=n,start_index=1,claim=f'equivalent_to_1/sqrt(pi*{n})')
        return proof('Multiply the two Wallis factors at each index. The finite product is 1/((2n+1)r_n²), where r_n is the stated ratio.',
                     'The Wallis product tends to π/2 and r_n>0. Taking the positive square root gives the stated equivalent.',
                     asymptotic_equivalent='1/sqrt(pi*n)')
    if form=='stirling_normalization':
        bind(index=n,start_index=1,sequence=f'{n}!*e^{n}/{n}^({n}+1/2)',
             claims=['finite_positive_limit','stirling_equivalent','constant_sqrt(2*pi)'])
        return proof('ln(a_(n+1)/a_n)=1−(n+1/2)ln(1+1/n). The constant and linear terms cancel, leaving O(1/n²).',
                     'Summing the logarithms gives convergence of a_n to some A>0.',
                     'The exact ratio (2n)!/(4^n(n!)²) is also the Wallis odd/even ratio. Substitution of the two normalizations gives sqrt(2)/(A sqrt(n)).',
                     'Comparing with 1/sqrt(πn) gives A=sqrt(2π). Taking the relative error from a_n/A gives the stated Stirling formula.',
                     normalization_limit=('sqrt',m.mul(q(2),m.PI)),relative_error='a_n/A-1 tends to zero')
    if form=='euler_gamma':
        x=d['argument'];claim=d['claim']
        if not isinstance(x,str) or not x.isidentifier() or x==n:raise Unsupported('The gamma argument and index must be independent')
        bind(argument=x,index=n,ratio=f'{n}!*{n}^{x}/({x}*({x}+1)*...*({x}+{n}))',claim=claim)
        if claim=='defined_for_reals_except_strictly_negative_integers':
            return proof('The argument 0 is real and is not a strictly negative integer.',
                         'The first denominator factor x vanishes at x=0 for every positive integer truncation.',
                         printed_claim_holds=False,counterexample=dict(argument=q(0),denominator_at_every_truncation=q(0)))
        steps=['The valid real set excludes 0,−1,−2,… . Restoring the factors gives (n/(n+1))^x/x times the partial product of (1+1/i)^x/(1+x/i).',
               'For sufficiently large i the factors are positive and ln of each factor is x ln(1+1/i)−ln(1+x/i)=O(1/i²). The remaining finite factors are nonzero.']
        if claim=='infinite_product':
            return proof(*steps,formula='(1/x) product(i>=1,(1+1/i)^x/(1+x/i))',domain='R except nonpositive integers')
        if claim==f'Gamma({x}+1)={x}*Gamma({x})':
            return proof(*steps,'Exact truncations satisfy G_n(x+1)=x n G_n(x)/(x+n+1). Pass to the finite limits.',
                         recurrence=claim,domain='R except nonpositive integers')
        if claim=='value_at_positive_integer_arguments':
            return proof(*steps,'At one the truncation is n/(n+1). The finite recurrence passes to the limit, so induction gives Γ(k)=(k−1)! for every positive integer k.',
                         positive_integer_value='(k-1)!')
        raise Unsupported('Another Gamma conclusion remains')
    if form=='riemann_product':
        f=d['function'];a,b=d['domain']
        if not all(isinstance(v,str) and v.isidentifier() for v in (f,a,b)) or len({f,a,b})!=3:
            raise Unsupported('The function and both interval endpoints must be independent')
        bind(function=f,domain=[a,b],integrable='proper_Riemann',sample='right_endpoint',factor=f'1+delta*{f}({a}+i*delta)',
             delta=f'({b}-{a})/n',claim=f'exp(integral({f},{a},{b}))')
        return proof('Riemann integrability on the closed interval gives a bound |f|≤M. Eventually every increment has absolute value ≤1/2.',
                     'For |u|≤1/2, |ln(1+u)−u|≤u², by integrating t/(1+t). The sum of errors is at most M²(b−a)²/n.',
                     'The first-order terms form the right-endpoint Riemann sums. Continuity of exp gives the limit of the original products.',
                     limit=d['claim'])
    if form=='uniform_positive_product':
        family=d['function_family'];domain=d['domain'];claim=d['claim']
        if not re.fullmatch(r'[A-Za-z]\w*_n',family) or not re.fullmatch(r'\([A-Za-z]\w*,[A-Za-z]\w*\)',domain):
            raise Unsupported('The function sequence or open interval is not bound')
        if claim=='continuous':
            bind(function_family=family,domain=domain,regularity='continuous',envelope=f'abs({family})<=c_n',
                 envelope_sum='convergent',factor_condition=f'abs({family})<1',claim=claim)
            return proof('All factors are positive. After c_n≤1/2, use |ln(1+f_n)|≤2c_n uniformly.',
                         'Each finite initial logarithm is continuous. Uniform convergence of the log tail and composition with exp give continuity.',
                         continuous_on=domain)
        if claim=='derivative_and_sufficient_conditions':
            bind(function_family=family,domain=domain,claim=claim)
            return proof('On each compact subinterval assume C¹ factors, |f_n|<1 and summable suprema of |f_n| and |f_n′|.',
                         'Eventually |f_n|≤1/2. The log derivatives f_n′/(1+f_n) are bounded in modulus by 2 sup|f_n′|.',
                         'Both series converge uniformly on the compact interval. Differentiate the sum of logarithms and use the chain rule for exp.',
                         derivative='F(x) sum(n>=1,f_n′(x)/(1+f_n(x)))',
                         sufficient_conditions=['all f_n are C¹, |f_n|<1', 'suprema of |f_n| and |f_n′| summable on every compact subinterval'])
    if form in ('mean_ratio','affine_factor_ratio'):
        from verify import same_value
        variable=('v',n);start=d['start_index']
        if type(start)!=int or start<0:raise Unsupported('A finite nonnegative lower index is required')
        keys={'start_index','index','assumptions','claimed_limit','form'}
        variants=({'count','term','numerator','denominator'} if form=='mean_ratio' else {'last_index','numerator','denominator'})
        if set(d)!=keys|variants:raise Unsupported('An unintended factor or assertion remains')
        if form=='mean_ratio' and (d['numerator'],d['denominator'],d['count'])!=('geometric_mean','sum','n'):
            raise Unsupported('The arithmetic comparison requires the sum as denominator and n terms')
        if form=='affine_factor_ratio' and d['last_index']!='n':
            raise Unsupported('The number of product factors must grow without bound')
        text=[d['term']] if form=='mean_ratio' else [d['numerator'],d['denominator']]
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join(text)))-{n,'pi','e'}-m.FUNCTIONS-set(m.ALIASES))
        conds=[]
        for c in d['assumptions']:
            ordered=re.fullmatch(r'0<([A-Za-z_]\w*)<([A-Za-z_]\w*)',c)
            conds.extend([ordered[1]+'>0',ordered[2]+'-'+ordered[1]+'>0'] if ordered else [c])
        ctx=m.context(dict(variable=n,parameters=names,parameter_conditions=conds))
        jumps=[]
        for t in text:
            raw=m.parse(t,n,names)
            a=m.simplify(m.substitute(raw,{variable:q(start)}))
            slope=m.simplify(m.add(m.substitute(raw,{variable:q(start+1)}),m.neg(a)))
            if domain_conditions(raw) or not same_value(raw,m.add(a,m.mul(slope,m.add(variable,q(-start))))):
                raise Unsupported('Each original term must be affine throughout the positive integer domain')
            jumps.append((a,slope))
        a,slope=jumps[0]
        if m.sign(a,ctx)!=1 or m.sign(slope,ctx) not in (0,1):raise Unsupported('A positive affine sequence is not established')
        claim=m.parse(d['claimed_limit'],None)
        ctx0=m.context({})
        if not m.constant_defined(claim,ctx0) or m.sign(claim,ctx0) is None:
            raise Unsupported('The printed limit cannot be compared with zero')
        if form=='mean_ratio':
            answer=dict(limit=ZERO,printed_claim_holds=m.sign(claim,ctx0)==0)
            if not answer['printed_claim_holds']:
                from itertools import product
                if len(names)>4:raise Unsupported('No finite witness search is available for this many source parameters')
                accepted={'>':{1},'>=':{0,1},'<':{-1},'<=':{0,-1},'=':{0},'!=':{-1,1}}
                inequalities=[]
                for c in conds:
                    g=re.fullmatch(r'(.+?)(>=|<=|!=|=|>|<)(.+)',c)
                    if not g:raise Unsupported('The original assumptions have no checked witness form')
                    l,r=(m.parse(g[i],None,names) for i in (1,3))
                    inequalities.append((l,r,accepted[g[2]]))
                for values in product((1,2,3,0,-1),repeat=len(names)):
                    subst={('s',k):q(v) for k,v in zip(names,values,strict=True)}
                    def satisfies(l,r,sgn):
                        l,r=(m.substitute(v,subst) for v in (l,r))
                        return all(m.constant_defined(v,ctx0) for v in (l,r)) and m.sign(m.add(l,m.neg(r)),ctx0) in sgn
                    first,step=(m.simplify(m.substitute(v,subst)) for v in (a,slope))
                    if m.sign(first,ctx0)==1 and m.sign(step,ctx0) in (0,1) and all(satisfies(*row) for row in inequalities):
                        answer['counterexample']=dict(parameters=dict(zip(names,values,strict=True)),
                            admissible_sequence=(first,step),claimed=claim,actual=ZERO)
                        break
                else:raise Unsupported('No admissible concrete counterexample was found')
            return proof('The hypotheses make all n terms positive. AM–GM bounds the geometric mean by their sum divided by n.',
                         'The original denominator is the positive sum. The quotient lies in (0,1/n], so its limit is zero.',**answer)
        b,other=jumps[1];gap=m.simplify(m.add(b,m.neg(a)))
        if not same_value(slope,other) or m.sign(slope,ctx)!=1 or m.sign(gap,ctx)!=1 or m.sign(claim,ctx0)!=0:
            raise Unsupported('A strictly positive fixed gap and common growing step are required')
        return proof('Both factors are positive. The fixed gap is positive, so ln((a+j*d)/(b+j*d))≤−(b−a)/(b+j*d).',
                     'The sum of reciprocals of this affine sequence diverges. Exponentiating the log comparison gives zero.',
                     limit=ZERO)
    if form=='binomial_absolute_value':
        bind(interval=['-1','1'],power_argument='1-x^2',coefficient='product(1,3,...,2*i-3)/product(2,4,...,2*i)',
             claim='abs(x)=lim(P_n(x))')
        return proof('For 0≤u<1 the binomial expansion gives sqrt(1−u)=1−sum(c_i u^i), with the positive coefficients in the question.',
                     'Let u increase to 1. Monotone convergence of the nonnegative series gives sum(c_i)=1, so the formula also holds at u=1.',
                     'Use u=1−x². The tail is bounded by the tail of sum(c_i) uniformly on the entire interval.',
                     limit='abs(x)',mode='uniform',domain=['-1','1'])
    if form=='vanishing_polynomial_moments':
        f=d['function'];a,b=d['interval']
        if not all(isinstance(v,str) and v.isidentifier() for v in (f,a,b)) or len({f,a,b})!=3:
            raise Unsupported('Independent real endpoints and continuous function required')
        bind(function=f,interval=[a,b],continuous=True,weights='x^k',indices='all_nonnegative_integers',
             moments='zero',claim='f_identically_zero')
        return proof('On a nondegenerate interval every polynomial integrates against f to zero, by linearity and the moment assumptions.',
                     'Approximate f uniformly by polynomials. The errors in the integrals are bounded by (b−a) sup|f| sup|P−f|.',
                     'Thus the integral of f² is zero. A nonzero value would give a subinterval of positive integral by continuity.',
                     identically_zero_on=[a,b],source_interval_condition='a<b')
    if form=='fejer_uniform_convergence':
        f=d['function']
        if not isinstance(f,str) or not f.isidentifier():raise Unsupported('The continuous periodic function is not bound')
        bind(function=f,interval=['-pi','pi'],continuous=True,period='2*pi',coefficients='Fourier',
             multiplier='1-i/n',last_term='n-1',claim='uniform_convergence')
        return proof('Expanding |sum(k=0..n−1,exp(i k t))|²/n counts n−|j| pairs at frequency j, giving the exact stated coefficient weights.',
                     'The kernel is nonnegative and its integral is 2π since only the constant frequency survives.',
                     'On |t|≥δ within [−π,π], the geometric sum gives the kernel bound 1/(n sin²(δ/2)).',
                     'The convolution error on |t|<δ is bounded uniformly by the modulus of continuity. On the complement it is bounded by a constant times 1/n.',
                     limit=f,mode='uniform',domain=['-pi','pi'])
    if form=='fejer_polynomial':
        bind(function='abs(x)',interval=['-pi','pi'],order='2*n-1')
        return proof('Evenness makes all sine coefficients zero. Integration by parts on [0,π] gives a_j=2((−1)^j−1)/(πj²), and a_0=π.',
                     'Multiply every j<2n−1 cosine coefficient by 1−j/(2n−1). Constant term is π/2.',
                     polynomial='pi/2-(4/pi)*sum(j odd,1<=j<=2*n-2,(1-j/(2*n-1))*cos(j*x)/j^2)',index_domain='n positive integer')
    raise Unsupported('No complete proof of the indicated product or approximation theorem')




def wave_product_limit(task,term,params,goal,request):
    """Reindex at the empty product, prove one universal limit, then specialize with its zero branch."""
    from tasks import source
    from verify import same_value
    name=task['index'];start=task['start_index']
    ctx=m.context(dict(variable=name,parameters=params))
    if term[1][0]!='div' or term[1][2][0]!='rpow':
        raise Unsupported('The factor is not a wave at a geometric mesh')
    amplitude,den=term[1][1:];phase=den[2]
    if m.variable_in(amplitude) or not m.constant_defined(amplitude,ctx):
        raise Unsupported('The original angle is not defined for every admitted parameter')
    if den[1]!=q(2):raise Unsupported('No verified dilation law for this base')
    try:exponent=coefficients(phase,name,start)
    except (NotRational,Undefined) as exc:raise Unsupported('The phase shift is not affine on the index domain') from exc
    if len(exponent)!=2 or exponent[1]!=1 or exponent[0].denominator!=1:
        raise Unsupported('The wave must halve at every index')
    shift=start-1+int(exponent[0])
    if abs(shift)>m.MAX_INTEGER_POWER:raise Unsupported('Exact constant exceeds the supported exponent size')
    angle=m.simplify(m.div(amplitude,m.power(q(2),shift)))
    child=request('limit of the normalized finite products for an arbitrary real angle',
                  dict(kind='limit',variable='N',parameters=['u'],variable_domain='positive_integers',
                       approach=dict(point='+inf',side='positive_infinity'),
                       expression='product_{k=1}^N '+term[0]+'(u/2^k)'))
    zero,general=child['value']['branches']
    if zero['condition']!='u=0' or freeze(zero['value'])!=ONE or general['condition']!='u!=0':
        raise Unsupported('The universal finite-product limit does not cover both branches')
    limit=m.substitute(freeze(general['value']),{('s','u'):angle})
    # Prove the original domain of a claimed formula before evaluating or cancelling it.
    claim=m.parse(goal,None,params) if goal is not None else None
    if angle==ZERO:
        branches=[dict(condition='always',value=ONE)]
        if claim is not None and (not m.constant_defined(claim,ctx) or not same_value(claim,ONE)):
            raise Unsupported('At zero angle the product is one; the claimed expression is undefined or unequal')
    elif m.nonzero(angle,ctx):
        branches=[dict(condition='always',value=m.simplify(limit))]
        if claim is not None and (not m.constant_defined(claim,ctx) or not same_value(claim,limit)):
            raise Unsupported('The claimed constant does not equal the specialized product limit')
    else:
        label=source(angle);at_zero={angle:ZERO}
        nonzero={**ctx,'nonzero_expressions':[angle]}
        if len(params)==1:
            p=params[0];scalar_zero={('s',p):ZERO}
            scalar_ctx=m.context(dict(variable=name,parameters=params,parameter_conditions=[p+'!=0']))
            if m.simplify(m.substitute(angle,scalar_zero))==ZERO and m.nonzero(angle,scalar_ctx):
                label,at_zero,nonzero=p,scalar_zero,scalar_ctx
        branches=[dict(condition=label+'=0',value=ONE),dict(condition=label+'!=0',value=m.simplify(limit))]
        if claim is not None:
            if not m.constant_defined(claim,nonzero) or not same_value(claim,limit):
                raise Unsupported('Equality and its original domain must be verified on the whole nonzero branch')
            at=m.substitute(claim,at_zero)
            if m.constant_defined(at,ctx):
                if not same_value(at,ONE):raise Unsupported('Incorrect claimed value at the zero angle')
            elif any(relation=='nonzero' and m.constant_defined(g,ctx) and m.simplify(g)==ZERO for relation,g in domain_conditions(at)):
                branches[0]['claimed_expression']='undefined'
            else:raise Unsupported('The domain of the claimed expression at zero angle is unresolved')
    plan=dict(theorem='method.wave_product_limit',index=name,base_index=start-1,angle=source(angle),
              wave=term[0],division_scope='eventually',normalized_index='j = '+name+' - ('+str(start-1)+')')
    value=dict(product_domain='all real parameters',branches=branches)
    if claim is not None:
        value['identity_domain']=branches[-1]['condition'] if branches[0].get('claimed_expression')=='undefined' else 'always'
    if len(branches)==1:value['partial_product_limit']=branches[0]['value']
    return plan,value


def product_question(task):
    """Bind the printed product, its running index, and its fixed real parameter."""
    name=r'[A-Za-z_][A-Za-z_0-9]*'
    goal=task.get('goal')
    if goal is not None:
        fields={'id','task_type','kind','goal','source_number','source_exercise_number','source_subpart','source_edition',
                'source_pdf_pages','source_statement','source_assumptions','transcription_notes','main_pass_status','deferred_reason','program_status'}
        if (set(task)-fields or task.get('source_assumptions') or task.get('transcription_notes')
                or any(task[key]!='finite_sum_or_product_sequence_limit' for key in ('kind','task_type') if key in task)
                or not isinstance(goal,dict) or set(goal)!={'expression','parameter','variable_domain','goal'}
                or goal['goal']!='complete original finite sum/product limit' or goal['variable_domain']!='positive_integers'):
            raise Unsupported('Не разобраны требования исходного предела произведения')
        declaration=re.fullmatch(r'fixed real ('+name+')',goal['parameter'])
        if not declaration:raise Unsupported('Требуется фиксированный вещественный параметр')
        params=[declaration[1]];expression=goal['expression']
    else:
        if (set(task)-{'kind','id','expression','variable','parameters','variable_domain','approach'} or task.get('kind','limit')!='limit'
                or task.get('variable_domain')!='positive_integers' or task.get('approach')!={'point':'+inf','side':'positive_infinity'}):
            raise Unsupported('Не установлена область натурального индекса и фиксированных параметров')
        params=task['parameters'];expression=task['expression']
    product=re.fullmatch(r'product_\{('+name+r')=(\d+)\}\^('+name+r')\s+(.+)',expression)
    if not product:raise Unsupported('Требуется конечное произведение с явными границами и множителем')
    index,first,outer,factor=product.groups()
    if goal is not None:
        if task.get('source_statement')!=f'Найти предел при {outer}->infinity {expression}.':
            raise Unsupported('Печатное условие не соответствует пределу данного произведения')
    elif task['variable']!=outer:raise Unsupported('Верхняя граница не совпадает с индексом предела')
    return dict(kind='finite_product_identity',index=index,lower=int(first),variable=outer,factor=factor,parameters=params)


def choose_product_wave(kernel):
    from operations import expression_positions
    waves={node[0] for _,node in expression_positions(kernel)}
    candidates=('cos','sin') if waves & {'cos','sin'} else ()
    return candidates+(('sinh',) if waves & {'cosh','sinh'} else ())


def discover_product_identity(task,library,saved=None):
    """Search for W(d*t)=c*F(t)*W(t), then telescope by multiplication on the whole index range."""
    from operations import expression_positions
    from tasks import source
    if set(task)-{'kind','id','factor','index','variable','lower','parameters'}:
        raise Unsupported('Для поиска тождества нужны только общий множитель, границы и параметры')
    index,outer,lower,params=(task[key] for key in ('index','variable','lower','parameters'))
    m.context(dict(variable=outer,parameters=params))
    ctx=m.context(dict(variable=index,parameters=params))
    if index==outer or type(lower) is not int or not 0<=lower<=m.MAX_INTEGER_POWER:
        raise Unsupported('Не подтверждены независимость индексов или основание индукции')
    term=m.parse(task['factor'],index,params)
    phases={e for _,e in expression_positions(term) if e[0]=='div' and e[2][0]=='rpow'
            and e[2][2]==('v',index) and e[2][1][0]=='q' and rational(e[2][1])>1 and m.constant_defined(e[1],ctx)}
    if len(phases)!=1:raise Unsupported('Не выделен один геометрически меняющийся аргумент множителей')
    phase,=phases
    scale,base=phase[1],phase[2][1]
    label='t'
    while label in [index,outer,*params]:label+='_'
    t=('s',label);kernel=m.substitute(term,{phase:t})
    if not m.constant_defined(kernel,m.context(dict(variable=index,parameters=[*params,label]))):
        raise Unsupported('На всей исходной области множитель не установлен как функция фазы')
    for wave in ((saved.get('multiplier_wave'),) if saved is not None else choose_product_wave(kernel)):
        if wave not in ('sin','cos','sinh'):continue
        lhs=(wave,m.mul(base,t));origin=(wave,ZERO)
        if wave=='sinh':
            from model import instantiate,match
            rule='real_identity.sinh_addition';addition=library.by_id.get(rule);env={}
            if (not library.data.get('wave_product_limit') or base!=q(2) or not addition or
                    not match(addition['head'],('real_identity_step',(wave,('add',t,t))),env)):continue
            if any(instantiate(step['ask'],env)!=('defined',t) for step in addition['steps']):continue
            expansions=[m.simplify(instantiate(addition['result'],env))]
        else:
            rule='rewrite.'+wave+'_difference'
            if rule not in library.by_id:continue
            difference=('add',lhs,('mul',q(-1),origin))
            expansions=[m.add(e,origin) for e,guards in library.compute('rewrite_trig_'+wave+'_difference',(difference,),ctx) if not guards]
        for expanded in expansions:
            pair=m.mul(kernel,(wave,t))
            if pair==ZERO:continue
            ratio=m.num(m.div(expanded,pair))
            # Division here only proposes a numerical coefficient. Check a division-free identity,
            # so zeros of W and F are included in the recurrence.
            if ratio is None or ratio<=0 or m.add(expanded,m.neg(m.mul(q(ratio),pair)))!=ZERO:continue
            c=q(ratio);start=lower-1
            at_start=m.div(scale,m.power(base,start))
            n=('v',outer);endpoint=m.substitute(phase,{('v',index):n})
            coefficient=m.mul(('rpow',c,n),(wave,endpoint))
            boundary=m.mul(m.power(c,start),(wave,at_start))
            return (dict(multiplier_wave=wave,dilation_rule=rule,phase=source(phase),base_index=start,
                         base_product=ONE,base_weight=boundary,phase_variable=label,local_identity=[lhs,m.mul(c,pair)],
                         difference_expansion=expanded,phase_ratio=base,weight_ratio=c,
                         induction='W_n F_n = W_(n-1); P_(L-1)=1; P_n=P_(n-1)*F_n'),
                    dict(coefficient=source(coefficient),boundary=source(boundary),valid_from=start))
    raise Unsupported('Для исходного множителя ни один проверенный закон разности не дал телескопического тождества')


def finite_product(task,library,request,identity=False,saved=None):
    from tasks import source
    if not library.data.get('finite_product_telescoping'):
        raise Unsupported('Не подключено построение тождества для конечного произведения')
    if identity:return discover_product_identity(task,library,saved)
    question=product_question(task)
    found=request('division-free finite product identity discovered from the factor',question)['value']
    params=question['parameters'];outer=question['variable']
    if len(params)!=1:raise Unsupported('Нужно покрытие нулевой и ненулевой ветвей параметров')
    p=params[0];factor=m.parse(question['factor'],question['index'],params)
    # The child already verified the original factor on every index before this substitution.
    zero_factor=m.simplify(m.substitute(factor,{('s',p):ZERO}))
    if zero_factor!=ONE:raise Unsupported('Для нулевой ветви не доказано постоянство произведения')
    condition=p+'!=0'
    tail=request('eventually nonzero coefficient of the finite product',dict(kind='sequence_expression_nonzero',
                 variable=outer,expression=found['coefficient'],variable_domain='positive_integers',
                 parameters=params,stated_conditions=[condition],scope='eventually'))
    if tail['value']!={'nonzero':True} or 'limit_expression' not in tail['compilation']:
        raise Unsupported('Для предела частного нужны ненулевой предел коэффициента и доказательство допустимости деления')
    endpoint=m.parse(tail['compilation']['limit_expression'],None,params)
    ctx=m.context(dict(variable=outer,parameters=params,parameter_conditions=[condition]))
    if not m.constant_defined(endpoint,ctx) or not m.nonzero(endpoint,ctx):
        raise Unsupported('Ненулевость предела делителя на ветви не подтверждена')
    numerator=m.parse(found['boundary'],None,params)
    return (dict(product_identity=found,zero_branch_factor=zero_factor,division_scope='eventually',coefficient_limit=source(endpoint)),
            dict(branches=[dict(condition=p+'=0',value=ONE),dict(condition=condition,value=m.div(numerator,endpoint))]))


def order_certificate(task,library):
    from graphs import SET_TASK_FIELDS
    from level_sets import set_order_identity
    goal=task.get('goal');conditions=task.get('assumptions',[])
    if (set(task)-SET_TASK_FIELDS-{'source_pdf_page'} or not isinstance(goal,dict) or set(goal)-{'sets','proposition'}
            or not isinstance(goal.get('proposition'),str) or not isinstance(conditions,list) or not all(isinstance(c,str) for c in conditions)
            or task.get('source') or any(n!='Natural-number n follows the induction context on the preceding page.' for n in task.get('transcription_notes',[]))):
        raise Unsupported('Additional requirements or evidence of the printed domain are unresolved')
    claim=goal['proposition'];text=task.get('source_statement','')
    if claim.endswith(', by corresponding cuts') or ' in Q:' in claim:
        if conditions or 'sets' in goal or not library.data.get('rational_cut_witnesses'):
            raise Unsupported('The rational cut construction has unresolved premises')
        from level_sets import rational_cut_identity
        if text and claim.endswith(', by corresponding cuts'):
            printed=re.fullmatch(r'Построив соответствующие сечения,\s*доказать\s+(.+?)\.',text)
            if not printed or printed[1].replace(' ','')!=claim.split(',')[0].replace(' ',''):
                raise Unsupported('The printed equality and the two structured sides must agree')
        return rational_cut_identity(claim)
    if (not isinstance(text,str) or re.search(r'методом|метод\s+индукции|по определению|опроверг|либо дока|построив',text,re.I)):
        raise Unsupported('The printed text requires a further method or an additional conclusion')
    if claim.startswith(('sup(','inf(','Every nonempty real set bounded')):
        if not library.data.get('set_image_endpoints'):raise Unsupported('No method for combining set bounds')
        if text and claim.startswith(('sup(','inf(')):
            if text.split('Доказать ')[-1].rstrip('.')!=claim:raise Unsupported('Printed and structured bound identities differ')
        return set_order_identity(task)
    if 'sets' in goal or not library.data.get('finite_order_steps'):raise Unsupported('No applicable finite comparison rule')
    return finite_order_steps(claim,conditions,library.data['finite_order_steps'])


def finite_order_steps(claim,assumptions,enabled):
    """Compare positive prefixes by a local multiplier, a reflected pair or a termwise bound."""
    import ast
    from math import factorial
    from tasks import source
    from verify import same_value
    opts=re.fullmatch(r'(.+?)(>=|<=|>|<)(.+?)(?:, with equality iff (\w+)=0)?',claim)
    if not opts:raise Unsupported('The requested comparison or equality cases have no complete reading')
    left,rel,right,equality=opts.groups()
    def proof(reason,steps,**facts):
        skill={'positive_multiplier':'positive_prefix_comparison','positive_multiplier_strict':'positive_prefix_comparison',
               'monotone_ratio_induction':'positive_prefix_comparison','reverse_triangle':'subadditive_fold',
               'binomial_majorant':'finite_sum_majorization','monotone_summand_bound':'finite_sum_majorization'}.get(reason,reason)
        if skill not in enabled:raise Unsupported('The transition is absent from the current library')
        return dict(theorem='method.'+skill,construction=reason,steps=steps,**facts),dict(proposition=claim,proved=True)
    idx=None;floor=None;conditions=[]
    for c in assumptions:
        mt=re.fullmatch(r'(\w+) is (?:a positive integer|an integer (?:greater than|at least)\s*(\d+))',c)
        if not mt:conditions.append(c);continue
        if idx is not None:raise Unsupported('Repeated independent index condition')
        floor=1 if mt[2] is None else int(mt[2])+int('greater than' in c);idx=mt[1]
    def tree(s):
        try:return ast.parse(s.replace('^','**'),mode='eval').body
        except (SyntaxError,ValueError):raise Unsupported('Unrecognized finite expression')
    l,r=tree(left),tree(right)
    def call(t,name,n):
        return isinstance(t,ast.Call) and isinstance(t.func,ast.Name) and t.func.id==name and len(t.args)==n and not t.keywords
    def name(t):return t.id if isinstance(t,ast.Name) else None
    def fold(t,op):
        if call(t,op,4) and isinstance(t.args[0],ast.Name) and ast.unparse(t.args[1])=='1' and name(t.args[2])==idx and name(t.args[0])!=idx:
            return t.args[0].id,t.args[3]
    def expr(t,var):
        return m.parse(ast.unparse(t).replace('**','^'),var,[])
    def rat_sign(e,var,start,strict):
        from graphs import peval
        num,den=rational_on_tail(e,var,start)
        # Sign is constant between roots of the numerator or denominator.
        cuts=sorted({p for a in (num,den) for p,_ in integer_sign_runs(a,start)})
        return all((z:=peval(num,k)*peval(den,k))>0 or not strict and z==0 and peval(den,k)!=0 for k in cuts)
    def affine(t,var):
        raw=expr(t,var)
        if any(op!='nonzero' or not m.num(m.simplify(arg)) for op,arg in domain_conditions(raw)):
            raise Unsupported('An affine identity must preserve its unsimplified domain')
        p,d=rf(raw,var)
        if len(d)!=1 or not d[0] or len(p)>2:raise Unsupported('An affine factor with an exact midpoint is required')
        return (p[1]/d[0] if len(p)==2 else Fraction(0)),p[0]/d[0]
    def polynomial_identity(a,b):
        return all(op=='nonzero' and m.num(m.simplify(arg)) for e in (a,b) for op,arg in domain_conditions(e)) and same_value(a,b)
    if idx is None:
        if (rel=='>=' and not equality and call(l,'abs',1) and call(r,'abs',1) and
            isinstance(l.args[0],ast.BinOp) and isinstance(l.args[0].op,ast.Sub) and
            isinstance(r.args[0],ast.BinOp) and isinstance(r.args[0].op,ast.Sub)):
            a,b=l.args[0].left,l.args[0].right;u,v=r.args[0].left,r.args[0].right
            if (name(a) and name(b) and conditions==[name(a)+','+name(b)+' are real'] and call(u,'abs',1) and call(v,'abs',1)
                    and ast.dump(u.args[0])==ast.dump(a) and ast.dump(v.args[0])==ast.dump(b)):
                return proof('reverse_triangle',['Из неравенства треугольника |u|≤|u−v|+|v|. Меняя u и v местами, получаем и противоположную оценку разности модулей. Следовательно, ||u|−|v||≤|u−v|.'])
        raise Unsupported('The proof requires an ordered index or the premises of a metric comparison')
    if floor<1:raise Unsupported('An initial positive integer is required')
    n=('v',idx);succ=m.add(n,ONE)
    if rel=='>=' and not equality and (P:=fold(l,'product')) and isinstance(r,ast.BinOp) and isinstance(r.op,ast.Add):
        S=fold(r.right,'sum');j,z=P
        if (ast.unparse(r.left)=='1' and S and S[0]==j and isinstance(z,ast.BinOp) and isinstance(z.op,ast.Add) and ast.unparse(z.left)=='1'
                and ast.dump(z.right)==ast.dump(S[1]) and isinstance(S[1],ast.Subscript) and name(S[1].slice)==j):
            t=ast.unparse(S[1])
            if sorted(conditions)==sorted(['all '+t+'>-1','all '+t+'>=0 or all '+t+'<=0']):
                return proof('positive_multiplier',['При одном множителе обе стороны совпадают.',
                    'Обозначим предыдущее произведение через P, сумму приращений через S, следующее приращение через u. Разность после добавления множителя равна (1+u)(P−1−S)+uS.',
                    'Первое слагаемое неотрицательно по индукции и условию 1+u>0. Второе неотрицательно, поскольку S и u одного знака.'],index=idx,increment=t)
    if rel=='>=' and equality and isinstance(l,ast.BinOp) and isinstance(l.op,ast.Pow) and name(l.right)==idx:
        if isinstance(l.left,ast.BinOp) and isinstance(l.left.op,ast.Add) and ast.unparse(l.left.left)=='1' and len(conditions)==1 and floor>=2:
            t=l.left.right;arg=ast.unparse(t).replace(' ','')
            if conditions==[arg+'>-1']:
                a,b=affine(t,equality)
                expected=m.add(ONE,m.mul(('s',idx),expr(t,equality)))
                if a and not b and polynomial_identity(m.parse(right,equality,[idx]),expected):
                    return proof('positive_multiplier_strict',['Положим u='+arg+'. Отклонение (1+u)^n−1−nu при n=2 равно u².',
                        'При следующем показателе отклонение равно (1+u) умножить на старое отклонение плюс n·u². Поскольку 1+u>0, строгость сохраняется при u≠0. При u=0 обе части равны единице.'],
                        initial=2,source_lower=floor,increment=arg,zero_iff=equality)
    if rel=='<=' and not equality and call(l,'abs',1) and call(l.args[0],'sin',1):
        A=fold(l.args[0].args[0],'sum');B=fold(r,'sum')
        if A and B and A[0]==B[0] and call(B[1],'sin',1) and ast.dump(A[1])==ast.dump(B[1].args[0]):
            term=ast.unparse(A[1])
            if (isinstance(A[1],ast.Subscript) and name(A[1].slice)==A[0] and
                    sorted(conditions)==sorted(['each '+term+' in[0,pi]','angles are radians'])):
                return proof('subadditive_fold',['Для одной дуги |sin u|=sin u, поскольку 0≤u≤π.',
                    'Из формулы сложения синуса и |cos t|≤1 следует |sin(s+u)|≤|sin s|+|sin u|. Применяем это неравенство к очередному углу и используем индукционную оценку частичной суммы.'],index=idx,term=term)
    if rel=='>=' and not equality and call(l,'abs',1) and isinstance(l.args[0],ast.BinOp) and isinstance(l.args[0].op,ast.Add):
        inner=l.args[0];A=fold(inner.right,'sum')
        if A and name(inner.left) and isinstance(r,ast.BinOp) and isinstance(r.op,ast.Sub) and call(r.left,'abs',1) and name(r.left.args[0])==name(inner.left):
            B=fold(r.right,'sum')
            if B and A[0]==B[0] and call(B[1],'abs',1) and ast.dump(A[1])==ast.dump(B[1].args[0]) and isinstance(A[1],ast.Subscript) and name(A[1].slice)==A[0] and conditions==['all variables are real']:
                return proof('subadditive_fold',['Итерируем |s+u|≤|s|+|u| от нулевой частичной суммы. Получаем |Σu|≤Σ|u|.',
                    'Разложение x=(x+Σu)−Σu даёт |x|≤|x+Σu|+|Σu|. Перенос последней оценки даёт требуемую нижнюю границу.'],index=idx,term=ast.unparse(A[1]))
    if conditions or equality:raise Unsupported('The remaining assumptions or equality case have not been discharged')
    # Pair the kth factor with the reflected factor. For factorials, increasing successive quotients give the reversed midpoint bound.
    P=fold(l,'product')
    if call(l,'factorial',1) and name(l.args[0])==idx:P=('j',tree('j'))
    if P and floor>=2 and isinstance(r,ast.BinOp) and isinstance(r.op,ast.Pow) and name(r.right)==idx:
        j,t=P;factorial_mid=call(t,'factorial',1) and call(r.left,'factorial',1)
        if factorial_mid or not call(t,'factorial',1) and not call(r.left,'factorial',1):
            a,b=affine(t.args[0] if factorial_mid else t,j)
            center=m.add(m.mul(q(a/2),succ),q(b));target=expr(r.left.args[0] if factorial_mid else r.left,idx)
            if a>0 and a+b>0 and polynomial_identity(center,target) and ((factorial_mid and a.denominator==b.denominator==1 and a%2==0 and rel=='>') or (not factorial_mid and rel=='<')):
                reason=('Отношение соседних факториалов равно возрастающему целому аргументу. Поэтому произведение двух факториалов с равноудалёнными от целого центра аргументами строго больше квадрата центрального факториала, если аргументы различны.'
                        if factorial_mid else 'Для положительных пар u,v выполняется uv≤((u+v)/2)², со строгостью при u≠v.')
                return proof('reflected_factor_pairs',['Сопоставляем каждому индексу j индекс '+idx+'+1−j. Эта перестановка сохраняет произведение и общий центр аргументов '+source(center)+'.',
                    reason,'Перемножение всех пар даёт квадрат исходного произведения. Крайняя пара различна, поскольку индексов не меньше двух. Извлекаем положительный корень.'],center=center,slope=q(a),offset=q(b),factorial=factorial_mid)
    if rel=='>' and (A:=fold(l,'sum')) and floor>=2:
        j,t=A
        if (isinstance(t,ast.BinOp) and isinstance(t.op,ast.Div) and ast.unparse(t.left)=='1' and call(t.right,'sqrt',1)
                and call(r,'sqrt',1) and name(t.right.args[0])==j and name(r.args[0])==idx):
            return proof('monotone_summand_bound',['Каждое слагаемое не меньше последнего, поскольку квадратный корень возрастает. Первое слагаемое строго больше последнего при n≥2.',
                'Поэтому сумма строго больше n/√n=√n.'],index=idx,source_lower=floor)
    if (rel=='>' and isinstance(l,ast.BinOp) and isinstance(l.op,ast.Pow) and name(l.left)==idx and
            isinstance(r,ast.BinOp) and isinstance(r.op,ast.Pow) and name(r.right)==idx and polynomial_identity(expr(r.left,idx),succ)):
        a,b=affine(l.right,idx)
        if a==1 and b.denominator==1 and b>=1 and floor**b>=3:
            return proof('binomial_majorant',['Делим на положительное n^n. Достаточно оценить (1+1/n)^n.',
                'Биномиальный коэффициент C(n,k) не превосходит n^k/k!. При k≥2 имеем k!≥2^(k−1), поэтому конечная биномиальная сумма строго меньше 1+1+Σ(k≥2)2^(1−k)=3.',
                'По исходной нижней границе индекса оставшаяся степень n не меньше 3.'],index=idx,excess_exponent=q(b),source_lower=floor)
    if rel not in ('<','>','<=','>='):raise Unsupported('No positive comparison applies')
    low,high=(l,r) if rel.startswith('<') else (r,l)
    def square_factor(t,var,lower):
        if call(t,'sqrt',1):
            val=expr(t.args[0],var)
            if rat_sign(val,var,lower,True):return val
        if isinstance(t,ast.BinOp) and isinstance(t.op,(ast.Mult,ast.Div)):
            a=square_factor(t.left,var,lower);b=square_factor(t.right,var,lower)
            return (m.mul if isinstance(t.op,ast.Mult) else m.div)(a,b)
        e=expr(t,var)
        if rat_sign(e,var,lower,True):return m.power(e,2)
        raise Unsupported('A factor can be zero or negative on the original integer tail')
    def prefix(t):
        """Return squared initial value and squared ratio of consecutive positive terms."""
        if (folded:=fold(t,'product')):
            j,g=folded;f=square_factor(g,j,1);var=('v',j);v=ONE
            for k in range(1,floor+1):v=m.mul(v,m.substitute(f,{var:q(k)}))
            return v,m.substitute(f,{var:succ})
        if call(t,'factorial',1):
            a,b=affine(t.args[0],idx);k=a*floor+b
            if a<0 or a.denominator!=1 or k.denominator!=1 or k<0:raise Unsupported('Factorial arguments are not all nonnegative integers')
            e=expr(t.args[0],idx);scale=ONE
            for j in range(1,int(a)+1):scale=m.mul(scale,m.add(e,q(j)))
            return q(factorial(int(k))**2),m.power(scale,2)
        if isinstance(t,ast.BinOp) and isinstance(t.op,(ast.Mult,ast.Div)):
            a,b=prefix(t.left);c,d=prefix(t.right);op=m.mul if isinstance(t.op,ast.Mult) else m.div
            return op(a,c),op(b,d)
        if isinstance(t,ast.BinOp) and isinstance(t.op,ast.Pow):
            if isinstance(t.right,ast.Constant) and type(t.right.value)==int:
                a,b=prefix(t.left);return m.power(a,t.right.value),m.power(b,t.right.value)
            if isinstance(t.left,ast.Constant) and type(t.left.value)==int and t.left.value>0:
                a,b=affine(t.right,idx)
                if a.denominator==b.denominator==1:return m.power(q(t.left.value),int(2*(a*floor+b))),m.power(q(t.left.value),int(2*a))
        e=square_factor(t,idx,floor)
        return m.substitute(e,{n:q(floor)}),m.div(m.substitute(e,{n:succ}),e)
    try:
        lower,u=prefix(low);upper,v=prefix(high);diff=m.num(m.simplify(m.add(upper,m.neg(lower))))
        if diff is None or diff<0 or diff==0 and len(rel)==1 or not rat_sign(m.add(v,m.neg(u)),idx,floor,False):
            raise Unsupported('The initial comparison or monotone ratio of prefixes is insufficient')
    except (ValueError,NotRational,Undefined,ZeroDivisionError) as e:raise Unsupported('No positive rational step certificate applies') from e
    return proof('monotone_ratio_induction',['Обе сравниваемые последовательности положительны. При начальном индексе квадраты меньшей и большей сторон равны '+source(m.simplify(lower))+' и '+source(m.simplify(upper))+'.',
        'При увеличении индекса квадраты сторон умножаются соответственно на '+source(m.simplify(u))+' и '+source(m.simplify(v))+'. Знак их разности проверен на всём целом хвосте. Индукция сохраняет исходное неравенство.'],
        index=idx,start=floor,initial_squares=[m.simplify(lower),m.simplify(upper)],squared_multipliers=[m.simplify(u),m.simplify(v)])


def algebraic_series_goal(task, library):
    """Use nonremovable poles for a radius and coefficient convolution for a reciprocal."""
    from graphs import peval
    from integrals import polynomial_expression
    from tasks import _linear_poles, source

    if not library.data.get('algebraic_series_goals'):
        raise Unsupported('No reusable algebraic series rule is available')
    basic = {'kind', 'id', 'source', 'function', 'variable', 'method_requirement', 'requested_output'}
    x = task.get('variable', 'x')
    fn = task['function']
    method = task.get('method_requirement')
    if task['kind'] == 'rational_series_radius':
        if (set(task) - basic - {'center'} or method not in (None, 'without_computing_expansion') or
                task.get('requested_output', ['convergence_interval']) != ['convergence_interval']):
            raise Unsupported('Only the exact interval and checked pole method are available')
        at = m.parse(task['center'], None)
        a = m.num(at)
        raw = m.parse(fn, x)
        z = ('v', x)
        ctx = m.context(dict(variable=x))
        if a is None or not m.constant_defined(m.substitute(raw, {z: at}), ctx):
            raise Unsupported('The original rational expression is undefined at the requested center')
        try:
            p, d, roots = _linear_poles(raw, x)
        except (NotRational, Undefined) as error:
            raise Unsupported('The original rational factors remain unresolved') from error
        mult = {}
        for root, order, _ in roots:
            mult[root] = max(order, mult.get(root, 0))
        if sum(mult.values()) != len(d) - 1 or any(not peval(p, b) for b in mult):
            raise Unsupported('The reduced rational denominator has unresolved poles')
        rhs = (d[-1],)
        for b, multiplicity in mult.items():
            for _ in range(multiplicity):
                rhs = pm(rhs, (-b, Fraction(1)))
        if rhs != d:
            raise Unsupported('The proposed poles do not reconstruct the reduced denominator')
        plan = dict(theorem='method.radius_from_rational_poles', method=method, coordinate=x, center=at,
                    numerator=polynomial_expression(p, x), denominator=polynomial_expression(d, x),
                    poles=[(q(b), order) for b, order in sorted(mult.items())], source_domain=domain_conditions(raw))
        if not mult:
            return plan, dict(radius='+inf', interval=['-inf', '+inf'], original_domain=plan['source_domain'])
        radius = min(abs(a - b) for b in mult)
        if not radius:
            raise Unsupported('The center is a nonremovable pole')
        nearest = sorted(b for b in mult if abs(a - b) == radius)
        plan.update(frontier_poles=[q(b) for b in nearest], frontier_argument=(
            'The highest-order nearest real poles give a nonzero polynomial leading term on at least one parity subsequence at either endpoint. '
            'All farther pole contributions decay geometrically. No Taylor coefficients are required.'))
        return plan, dict(radius=q(radius), interval=[q(a - radius), q(a + radius)], endpoints=['divergent', 'divergent'],
                          original_domain=plan['source_domain'])

    count = task.get('term_count', 4)
    if (set(task) - basic - {'term_count'} or method not in (None, 'algebra_of_power_series') or type(count) is not int or
            not 1 <= count <= 40 or task.get('requested_output', ['initial_coefficients']) != ['initial_coefficients']):
        raise Unsupported('An explicit finite prefix of a reciprocal series is needed')
    match = re.fullmatch(r'1/\(sum_\{([A-Za-z_]\w*)>=0\}(.+)\)', re.sub(r'\s+', '', fn))
    if not match or match[1] == x:
        raise Unsupported('An inverse of a power series indexed from zero is needed')
    k = match[1]
    power = ('rpow', ('s', x), ('v', k))
    raw = m.parse(match[2], k, [x])

    def coefficient(e):
        if e == power:
            return ONE
        if e[0] in ('mul', 'div'):
            left, right = e[1:]
            if not m.contains(right, ('s', x)):
                return e[0], coefficient(left), right
            if e[0] == 'mul' and not m.contains(left, ('s', x)):
                return 'mul', left, coefficient(right)
        raise Unsupported('The summand is not a rational coefficient times the common power')

    c = coefficient(raw)
    try:
        num, denom = rational_on_tail(c, k, 0)
    except (NotRational, Undefined) as error:
        raise Unsupported('The rational coefficient is not defined on its original integer domain') from error
    values = [peval(num, i) / peval(denom, i) for i in range(count)]
    a0 = values[0]
    if not a0:
        raise Unsupported('The given series vanishes at the expansion center')
    inverse = [1 / a0]
    for i in range(1, count):
        inverse.append(-sum(values[j] * inverse[i - j] for j in range(1, i + 1)) / a0)
    plan = dict(theorem='method.reciprocal_series_convolution', coefficient=source(c), index=k,
                numerator=list(map(q, num)), denominator=list(map(q, denom)), coefficient_prefix=list(map(q, values)),
                growth_bound='the rational coefficient has at most polynomial growth, so the series is analytic for |x|<1',
                center_condition=('nonzero', q(a0)))
    return plan, dict(variable=x, coefficients=list(map(q, inverse)), remainder_order=count,
                      checked_relation='the convolution equals 1 through degree term_count−1')


def uniform_polynomial_sums(task, library):
    """Check uniform convergence by proving that each polynomial error is unbounded."""
    fields = {'kind', 'id', 'source', 'partial_sums', 'candidate', 'domain', 'printed_note', 'source_reference_pages', 'variable'}
    if (not library.data.get('uniform_polynomial_sums') or set(task) - fields or task.get('domain') != 'R'):
        raise Unsupported('Need a uniformly bounded target on the whole real line')
    x = task.get('variable', 'x')
    target = m.parse(task['candidate'], x)
    z = ('v', x)
    if target not in (('sin', z), ('cos', z)):
        raise Unsupported('A global bound on the target has not been established')
    raw = re.sub(r'\s+', '', task['partial_sums'])
    pattern = re.compile(r'sum_\{([A-Za-z_]\w*)=(\d+)\.\.([A-Za-z_]\w*)\}(.+)')
    match = pattern.fullmatch(raw)
    if not match or len({x, match[1], match[3]}) != 3:
        raise Unsupported('Need the exact distinct finite upper index of the partial sums')
    n, start, N, term = match.groups();n_reg = re.escape(n);x_reg = re.escape(x)
    shape = re.fullmatch(r'(?:(\(-1\)\^[^*]+)\*)?'+x_reg+r'\^\(([^()]*)\)/\(([^()]*)\)!', term)
    if not shape:
        raise Unsupported('Need a single monomial with factorial coefficient and known sign')
    a, b = (rational_on_tail(m.parse(t,n),n,int(start)) for t in shape.groups()[1:])
    if (a[1] != (1,) or b[1] != (1,) or len(a[0]) != 2 or len(b[0]) != 2 or
            any(co.denominator != 1 for co in (*a[0], *b[0])) or a[0][1] <= 0 or b[0][1] < 0 or
            a[0][0] + a[0][1]*int(start) <= 0 or b[0][0] + b[0][1]*int(start) < 0):
        raise Unsupported('The highest degree must grow, be positive and have a nonzero factorial coefficient')
    sign_factor = shape[1]
    if sign_factor and not re.fullmatch(r'\(-1\)\^(?:'+n_reg+r'|\('+n_reg+r'[+-]\d+\))',sign_factor):
        raise Unsupported('The sign factor lacks an integer exponent')
    coefficients = list(map(q,a[0]));plan = dict(theorem='method.uniform_unbounded_polynomial_errors',
                bound_on_candidate=q(1), index=n, first=int(start), upper=N, highest_degree=coefficients,
                leading_coefficient_nonzero='factorial of a nonnegative integer and optional sign ±1',
                obstruction='the highest degree term is unique, so the absolute error is unbounded for each partial sum')
    value = dict(uniformly_convergent=False, sup_error='+inf')
    if 'printed_note' in task:
        if (task['printed_note'] != 'The displayed summation has upper infinity despite the printed limit N->infinity.' or
                target != ('sin', z) or start != '1' or a != b or a[0] != (-1, 2) or sign_factor != f'(-1)^({n}-1)'):
            raise Unsupported('The interpretation of the printed upper index remains unresolved')
        plan['literal_argument'] = 'the standard sine power series is absolutely convergent on R and independent of the outer index'
        value['literal_infinite_sum'] = 'sin(x), with no dependence on the indicated upper-limit variable'
    return plan, value


def transformed_power_series(task, library, request):
    """Invert the original series coordinate, then choose a geometric or analytic coefficient proof."""
    from tasks import guard_source, known_guard, source
    from uniform import coefficient_rows
    from verify import same_value

    fields = {'kind', 'id', 'source', 'function', 'variable', 'series_variable', 'base_variable', 'center',
              'parameters', 'conditions', 'requested_output', 'required_powers'}
    if not library.data.get('power_series_coordinate_transport') or set(task) - fields:
        raise Unsupported('An original condition, parameter or method of expansion remains unbound')
    x=task.get('base_variable','x');u='__series'
    coordinate=task.get('series_variable',task.get('variable',x))
    if ('base_variable' not in task and coordinate.isidentifier()
            and coordinate not in task.get('parameters',[])
            and re.search(r'\b'+re.escape(coordinate)+r'\b',task['function'])
            and (x==coordinate or x in task.get('parameters',[]) or not re.search(r'\bx\b',task['function']))):
        x=coordinate
    z,uvar=('v',x),('v',u)
    power_kind = task.get('required_powers')
    if power_kind not in (None, 'positive integer powers', 'negative integer powers') or 'series_variable' in task and 'variable' in task:
        raise Unsupported('The expansion coordinate or sign of powers is ambiguous')
    if power_kind == 'negative integer powers':coordinate = '1/('+coordinate+')'
    center = task.get('center', '0');text = task['function']
    params = sorted(set(re.findall(r'[A-Za-z_]\w*', ' '.join((coordinate, text, center)))) - m.FUNCTIONS - set(m.ALIASES) - {x, 'pi', 'e'})
    if set(task.get('parameters', params)) != set(params) or u in {x, *params}:
        raise Unsupported('The series coordinate and fixed parameters must be distinct')
    assumptions = task.get('conditions', [])
    guards=[]
    for item in assumptions:
        left,sep,right=item.partition('!=')
        guards.append(f'({left})-({right})!=0' if sep and right.strip()!='0' else item)
    ctx = m.context(dict(variable=x, parameters=params, parameter_conditions=guards))
    origin = m.parse(center, None, params)
    chart = m.parse(coordinate, x, params)
    f = m.parse(text, x, params)
    displacement = m.add(chart, m.neg(origin))

    def coefficients(e, v):
        num, denom = m.rational_form(e)
        if any(a != v and m.contains(a, v) for terms in (num, denom) for mon in terms for a, _ in mon):
            raise Unsupported('The transformed expression is not rational in the series coordinate')
        return [coefficient_rows(terms, v) for terms in (num, denom)]

    P, Q = coefficients(displacement, z)
    if max(P.keys() | Q.keys(), default=0) > 1:
        raise Unsupported('The series coordinate has no verified fractional-linear inverse')
    A, B, C, D = P.get(1,ZERO), P.get(0,ZERO), Q.get(1,ZERO), Q.get(0,ZERO)
    det = m.add(m.mul(A,D),m.neg(m.mul(B,C)))
    if not known_guard(('nonzero', det),ctx):
        raise Unsupported('The original coordinate determinant may vanish')
    inverse = m.div(m.add(m.mul(D,uvar),m.neg(B)),m.add(A,m.neg(m.mul(C,uvar))))
    if not same_value(m.substitute(displacement,{z:inverse}),uvar):
        raise Unsupported('The proposed inverse fails the exact coordinate identity')
    transformed = m.substitute(f,{z:inverse})
    wants = task.get('requested_output',['all_coefficients'])
    if wants not in (['all_coefficients'],['all_coefficients','convergence_set']):
        raise Unsupported('An additional requested power series output remains')
    domain = [guard_source(g) for g in (*domain_conditions(chart),*domain_conditions(f))]
    plan = dict(theorem='method.power_series_coordinate_transport', source_coordinate=chart, center=origin,
                nonzero_determinant=det, inverse=inverse, original_conditions=assumptions, original_domain=domain,
                argument='Обращаем исходную замену, переносим выражение в новую координату и сохраняем исходную область.')
    if transformed[0]=='acos' and not assumptions and wants==['all_coefficients']:
        try:num,denom=rf(transformed[1],u)
        except (NotRational,Undefined):num,denom=(),()
        if denom==(1,) and len(num)==3 and num[:2]==(1,0) and num[2]<0:
            scale=m.simplify(('sqrt',q(-num[2]/2)))
            slope=m.mul(q(2),scale)
            p=request('obtain the inner inverse trigonometric limit on the positive side',
                      dict(kind='limit',variable=u,expression=f'asin({u})/{u}',approach=dict(point='0',side='right')))
            if not same_value(freeze(p['value']),ONE):
                raise Unsupported('The one-sided sine inverse limit has not been proved')
            plan.update(argument='Приводим арккосинус к удвоенному арксинусу от модуля. Предел арксинуса даёт разные наклоны справа и слева.',
                        inverse_trig_branch={'identity':'acos(1-2*w^2)=2*asin(w)','local_constraint':'0<=w<1','w':('mul',scale,('abs',uvar))})
            return plan,dict(two_sided_power_series_exists=False,left_derivative=m.neg(slope),right_derivative=slope,
                             original_domain=domain)
    try:
        p,d = coefficients(transformed,uvar)
    except Unsupported:
        p,d = {},{}
    d0,d1=d.get(0,ZERO),d.get(1,ZERO)
    if d and max(d) <= 1 and known_guard(('nonzero',d0),ctx):
        if power_kind == 'positive integer powers' and p.get(0,ZERO)!=ZERO:
            raise Unsupported('A strictly positive power expansion cannot omit the constant term')
        ratio = m.simplify(m.div(m.neg(d1),d0))
        vals = [(j,m.simplify(m.div(w,d0))) for j,w in sorted(p.items())]
        plan.update(geometric_ratio=ratio, coefficient_polynomial=vals)
        val = dict(coordinate=coordinate, centered_coordinate=source(displacement), numerator_coefficients=vals,
                   geometric_factor=ratio, formula='Σ_j numerator_coefficients[j]*u^j * Σ_{n>=0} geometric_factor^n*u^n',
                   valid_on='|geometric_factor*u|<1 and both original expressions defined',original_domain=domain)
        if 'convergence_set' in wants and d1 != ZERO:
            if not known_guard(('nonzero',d1),ctx):
                raise Unsupported('A possibly vanishing leading parameter needs separate radii')
            pole=m.div(m.neg(d0),d1);residue=ZERO
            for j,w in p.items():residue=m.add(residue,m.mul(w,m.power(pole,j)))
            if not known_guard(('nonzero',m.simplify(residue)),ctx):
                raise Unsupported('Possible cancellation at the geometric pole changes the exact radius')
            val['convergence_set']=dict(coordinate=source(displacement),radius=('abs',pole), endpoints=['divergent','divergent'])
            plan['nonremovable_pole']=pole
        elif 'convergence_set' in wants:
            val['convergence_set']='the coefficient series is a polynomial in the new coordinate'
        return plan,val
    if 'convergence_set' in wants or assumptions:
        raise Unsupported('The analytic expansion needs a separate exact range or parameter proof')
    if power_kind == 'positive integer powers' and m.simplify(m.substitute(transformed,{uvar:ZERO})) != ZERO:
        raise Unsupported('The constant term of the transformed expression is not zero')
    child=request('expand the proved expression in the new coordinate',
                  dict(kind='infinite_power_series_expansion',function=source(transformed),variable=u,center='0'))
    return plan,dict(coordinate=coordinate,centered_coordinate=source(displacement),coefficients=child['value'],
                     valid_on='a neighborhood of zero in the new coordinate where the original expression is defined',original_domain=domain)


def source_power_series_calculus(task, library, request):
    """Ask for the coefficient or convergence theorem needed by the original calculus goal."""
    from tasks import source
    from verify import same_value

    if not library.data.get('source_power_series_calculus'):
        raise Unsupported('The relevant termwise calculus transition is unavailable')
    kind=task['kind'];base={'kind','id','source'};x=task.get('variable','x');z=('v',x)
    plan=dict(theorem='method.original_series_calculus')
    if kind=='general_power_series_operation':
        if (set(task)-base-{'f','F'} or
                not (match:=re.fullmatch(r'sum_\{([A-Za-z_]\w*)>=0\}\s+([A-Za-z_]\w*)_\1\*([A-Za-z_]\w*)\^\1',task['f']))):
            raise Unsupported('Need a general power series with its exact coefficient and index')
        n,a,x=match.groups();target=m.parse(task['F'],x,extra_functions={'f'});z=('v',x)
        if target[0]!='div' or target[1]!=('f',z) or domain_conditions(target[2]):
            raise Unsupported('Need a checked linear denominator multiplying the given entire coefficient sequence')
        d,e=rf(target[2],x)
        if len(d)>2 or not d[0] or e!=(1,):
            raise Unsupported('The original denominator is not affine and nonzero at the center')
        r=-(d[1] if len(d)==2 else Fraction(0))/d[0]
        j=next(name for name in ('j','k','i','r') if name not in (n,a,x))
        return dict(plan,argument='Разлагаем обратную аффинную функцию геометрически и проверяем свёртку по общей степени.',
                    scale=q(1/d[0]),ratio=q(r),original_denominator=target[2],coefficient_index=n,summation_index=j),dict(
                    coefficient=f'{1/d[0]} * sum_{{{j}=0..{n}}} {a}_{j}*({r})^({n}-{j})',
                    valid_on='intersection of the original open convergence disk and the geometric disk',geometric_radius=q(1/abs(r)) if r else '+inf')
    if kind=='power_series_radius_theorem':
        pair=task.get('given_radii')
        arg='Сравниваем корни модулей коэффициентов и применяем формулу Коши–Адамара.'
        if pair is not None:
            if set(task)-base-{'given_radii','target'} or len(pair)!=2:
                raise Unsupported('Need the two original power series radii')
            patterns=[re.fullmatch(r'sum\s+([A-Za-z_]\w*)_n\*([A-Za-z_]\w*)\^n has radius ([A-Za-z_]\w*)',row) for row in pair]
            if not all(patterns):raise Unsupported('The two coefficient sequences and their radii are not explicit')
            a,x,R=patterns[0].groups();b,y,S=patterns[1].groups()
            if x!=y or a==b or R==S:raise Unsupported('The two source series must use the same coordinate and distinct labels')
            target=re.sub(r'\s+','',task['target']);aa=a+'_n';bb=b+'_n'
            if target==f'sum_(n>=0)({aa}±{bb})*{x}^n':
                p=dict(plan,argument=arg+' При разных радиусах обратное неравенство следует из восстановления исходного ряда разностью.',
                       example_same_radius='opposite or identical geometric coefficient sequences allow either full cancellation or the unchanged radius')
                return p,dict(radius_when_different=f'min({R},{S})',bound_when_equal=f'R_new >= {R}',can_exceed_bound=True)
            if target==f'sum_(n>=0){aa}*{bb}*{x}^n':
                p=dict(plan,argument=arg+' Чередующиеся непересекающиеся носители дают нулевое произведение при тех же конечных положительных исходных радиусах.',
                       sharp_example='two geometric sequences attain the product radius',
                       zero_times_infinity='weights n! and c^n/n! give arbitrary positive radii; changing the second weight can make the output radius zero or infinite')
                return p,dict(lower_bound=f'{R}*{S} whenever defined for extended nonnegative radii',result_radius_not_determined=True)
            raise Unsupported('The target is not the sum, difference or coefficientwise product of those two series')
        if set(task)-base-{'series','hypotheses'}:
            raise Unsupported('An auxiliary radius condition remains unbound')
        match=re.fullmatch(r'sum_\{n>=0\}\s+([A-Za-z_]\w*)_n\*([A-Za-z_]\w*)\^n',task['series'])
        if not match or task['hypotheses']!=[f'l=liminf abs({match[1]}_n/{match[1]}_(n+1))',f'L=limsup abs({match[1]}_n/{match[1]}_(n+1))']:
            raise Unsupported('The stated bounds must be the lower and upper tail limits of the same consecutive ratios')
        return dict(plan,argument='При |x|<l отношение соседних членов меньше единицы с запасом. При |x|>L оно больше единицы на хвосте.',
                    quotient_domain='successive source ratios are defined on a tail'),dict(radius_relation='l<=R<=L')
    if kind in ('power_series_and_sum','infinite_power_series_expansion'):
        from integrals import affine
        fields={'function','series_variable','variable','method_requirement','additional_series'}
        if set(task)-base-fields or task.get('method_requirement') not in (None,'expand_derivative_then_integrate_termwise'):
            raise Unsupported('The original expansion and endpoint summation method remains unbound')
        match=re.fullmatch(r'sum_\{([A-Za-z_]\w*)>=1\}\(-1\)\^\(([^()]+)\)/\(([^()]+)\)',
                           re.sub(r'\s+','',task['additional_series']))
        if not match:
            compact=re.sub(r'\s+','',task['additional_series'])
            match=re.fullmatch(r'sum_\{([A-Za-z_]\w*)>=1\}\(-1\)\^\(([^()]+)\)/([A-Za-z_]\w*)',compact)
        if not match:
            raise Unsupported('The additional numerical sum has no alternating affine reciprocal term')
        n,exponent,denom=match.groups()
        a,b=rational_on_tail(m.parse(exponent,n),n,1);d,e=rational_on_tail(m.parse(denom,n),n,1)
        if b!=(1,) or e!=(1,) or len(a)!=2 or len(d)!=2 or any(c.denominator!=1 for c in (*a,*d)) or a[1]%2!=1 or (a[0]+a[1])%2 or sum(d)!=1 or d[1]<1:
            raise Unsupported('The first sign and affine denominator do not match an Abel boundary sum')
        k=int(d[1]);u='__series';coordinate=task.get('series_variable',x)
        A,B=affine(m.parse(coordinate,x),x)
        if m.num(A) in (None,0) or m.num(B) is None or x==u:
            raise Unsupported('The centered series coordinate must have a checked affine inverse')
        v=('v',u);origin=m.div(m.neg(B),A);inverse=m.add(origin,m.div(v,A));raw=m.parse(task['function'],x)
        transformed=m.substitute(raw,{z:inverse});ctx=m.context(dict(variable=u));initial=m.substitute(transformed,{v:ZERO})
        if not m.constant_defined(initial,ctx) or not same_value(initial,ZERO):
            raise Unsupported('The new origin is not the zero initial value of the series')
        from tasks import guard_source
        p=request('differentiate the original function in the centered coordinate',dict(kind='differentiate',function=source(transformed),
                  variable=u,method_requirement='table_and_rules',stated_conditions=[guard_source(g) for g in domain_conditions(transformed,True)]))
        kernel=m.div(ONE,m.add(ONE,m.power(v,k)))
        if not same_value(freeze(p['value']),kernel):
            raise Unsupported('The original function does not have the generating derivative of the numerical series')
        endpoint=request('prove the alternating boundary sum by Abel convergence',dict(kind='series_sum',index=n,start_index=0,
                         term=f'(-1)^{n}/({k}*{n}+1)',method_requirement='abel'))['value']
        return dict(plan,argument='Раскладываем проверенную производную в геометрический ряд, интегрируем почленно от нуля и проверяем граничную сумму Абеля.',
                    coordinate=coordinate,inverse=inverse,kernel=kernel,original_domain=domain_conditions(raw)),dict(
                    series_coordinate=coordinate,coefficient_formula=f'(−1)^n/(n*{k}+1) at power n*{k}+1',
                    convergence_interval='[-1,1]' if k%2==0 else '(-1,1]',additional_sum=endpoint)
    if kind=='finite_expansion':
        # The same germ must also agree with the separately assigned center value.
        if set(task)-base-{'expression','variable','degree','approach','parameters','parameter_conditions','variable_domain',
                           'requested_output','extended_value_at_center'}:
            raise Unsupported('An original expansion restriction remains unproved')
        child={k:v for k,v in task.items() if k not in ('extended_value_at_center','id','source')}
        p=request('verify the finite punctured expansion on every original side',child)
        value=m.parse(task['extended_value_at_center'],None,task.get('parameters',[]))
        if not same_value(freeze(p['value'][0]),value):
            raise Unsupported('The assigned value does not equal the constant term of the expansion')
        return dict(plan,argument='Строим разложение в проколотой окрестности и сверяем постоянный член со значением в центре.',
                    center_value=value),dict(coefficients=p['value'],degree=task['degree'])
    if kind=='nth_derivative_from_series':
        if (set(task)-base-{'function','variable','method_requirement'} or
                task.get('method_requirement','uniqueness_of_power_series_coefficients')!='uniqueness_of_power_series_coefficients'):
            raise Unsupported('A different all-orders derivative method remains')
        p=request('construct Taylor coefficients at a point of the original domain',
                  dict(kind='symbolic_order_derivative',function=task['function'],variable=x,order='n'))
        return dict(plan,argument='Из единственности степенного ряда производная порядка n равна n! умноженному на коэффициент при степени n.'),p['value']
    if kind=='simultaneous_infinite_power_series':
        if set(task)-base-{'functions','series_variable','parameter'} or not task['functions']:
            raise Unsupported('The source contains an unbound simultaneous expansion condition')
        var=task['series_variable'];parameter=task.get('parameter')
        if not re.fullmatch(r'[A-Za-z_]\w*',var) or var==parameter:
            raise Unsupported('The expansion coordinate and fixed parameter coincide')
        values=[]
        for f in task['functions']:
            names=set(re.findall(r'[A-Za-z_]\w*',f))-m.FUNCTIONS-set(m.ALIASES)-{var,'pi','e'}
            if names-{parameter}:raise Unsupported('An undeclared fixed parameter occurs in the simultaneous expansion')
            p=request('expand each printed function in the common coordinate',dict(kind='infinite_power_series_expansion',function=f,variable=var))
            values.append(dict(function=f,series=p['value']))
        return dict(plan,argument='Все выписанные функции раскладываем по одной указанной переменной, удерживая остальные параметры.'),dict(series=values)
    if kind=='variable_integral_power_series':
        if set(task)-base-{'integrand','variable','lower','upper','requested_output'} or task['lower'] not in ('0',0):
            raise Unsupported('Need a variable-upper-limit integral with a fixed zero lower end')
        upper=task['upper'];text=task['integrand'];want=task.get('requested_output',['complete_power_series'])
        if not re.fullmatch(r'[A-Za-z_]\w*',upper) or upper==x or want not in (['complete_power_series'],['first_four_nonzero_terms']):
            raise Unsupported('The upper coordinate and requested term count must be bound separately')
        argument='Интегрируем ряд на замкнутых отрезках внутри его области и используем нулевое начальное значение.'
        if want==['first_four_nonzero_terms']:
            p=request('prove the local integrand germ and its finite Peano remainder',dict(kind='finite_expansion',expression=text,
                        variable=x,approach=dict(point='0',side='both'),degree=3,requested_output=['finite_power_expansion']))
            coeffs=[m.div(freeze(c),q(i+1)) for i,c in enumerate(p['value'])]
            if len(coeffs)!=4 or any(c==ZERO for c in coeffs):
                raise Unsupported('The verified germ does not provide four nonzero terms')
            return dict(plan,argument='Интегрируем четыре проверенных члена и остаток Пеано.',
                        endpoint='removable or ordinary; integrable because the integrand has a finite limit'),dict(variable=upper,first_power=1,coefficients=coeffs,remainder='o(upper^4)')
        raw=m.parse(text,x);drop=0
        if raw[0]=='div' and raw[2]==z:
            raw=raw[1]
            ctx=m.context(dict(variable=x))
            at_zero=m.substitute(raw,{z:ZERO})
            if not m.constant_defined(at_zero,ctx) or not same_value(at_zero,ZERO):
                raise Unsupported('The apparent pole at zero has not been made removable')
            drop=1
        p=request('construct the convergent series of the regular integrand or its vanishing numerator',
                  dict(kind='infinite_power_series_expansion',function=source(raw),variable=x))
        return dict(plan,argument=argument,removed_zero_coefficients=drop),dict(variable=upper,source_coefficients=p['value'],
                     first_power=1,formula=f'sum_(k>=0) C_(k+{drop})*{upper}^(k+1)/(k+1)',valid_on=p['value']['valid_on'])
    if kind=='sum_of_power_series_by_method':
        fields={'series','variable','index','start_index','coefficient_term','method_requirement','source_hint'}
        method=task.get('method_requirement')
        if set(task)-base-fields or method not in ('termwise_differentiation','termwise_integration'):
            raise Unsupported('The original termwise method or a coefficient is unbound')
        start=task['start_index'];n=task['index'];term=task['coefficient_term']
        raw=m.parse(term,n,[x],extra_functions={'factorial','prod'}) if 'prod(' not in term else None
        plan.update(argument='Переводим исходное действие над рядом в действие над коэффициентами и восстанавливаем сумму.',
                    method=method,original_ellipsis=task['series'])
        if (method=='termwise_differentiation' and start==0 and raw is not None and raw[0]=='div' and raw[1][0]=='rpow' and
                raw[1][1]==('s',x) and raw[2]==('factorial',raw[1][2])):
            degree=rational_on_tail(raw[1][2],n,start)
            if degree in (((0,2),(1,)),((1,2),(1,))):
                p=request('derive the differential equation by checking every coefficient',
                          dict(kind='series_ode_identity',series=f'sum_{{{n}>=0}}'+term,equation='D^2 y=y',variable=x))
                odd=bool(degree[0][0]);plan.update(ode=p['value'],initial_values=[int(not odd),int(odd)])
                return plan,dict(interior_sum=('sinh' if odd else 'cosh',z),convergence_domain='all_real')
        child=dict(kind='series_sum',term=term,index=n,start_index=start,method_requirement=method,requested_output=['convergence_and_sum'])
        p=request('find and prove a generating function by the required termwise operation',child)
        return plan,p['value']
    raise Unsupported('The source requests another series operation')


def differential_series_identity(task, library):
    """Check a linear differential identity by grouping exact factorial-weighted coefficients."""
    from math import factorial, prod
    from tasks import source

    fields = {'kind', 'id', 'source', 'series', 'equation', 'variable'}
    if not library.data.get('differential_series_identity') or set(task) - fields:
        raise Unsupported('The original series differential obligation is unbound')
    x = task.get('variable', 'x')
    text = re.sub(r'\s+', '', task['series'])
    match = re.fullmatch(r'sum_\{([A-Za-z_]\w*)>=(\d+)\}(.+)', text)
    if not match or match[1] == x:
        raise Unsupported('Need a power series indexed from an explicit integer')
    n, start, term = match[1], int(match[2]), match[3]
    token = re.escape(n)
    text = re.sub(r'(\([^()]+\)|\b' + token + r'\b)!', lambda m: 'factorial(' + m[1] + ')', term)
    raw = m.parse(text, n, [x], extra_functions={'factorial'})
    if raw[0] != 'div' or raw[1][0] != 'rpow' or raw[1][1] != ('s', x):
        raise Unsupported('Need a single progressing power with a factorial weight')
    den = raw[2]
    fact, weight = (den[1], den[2]) if den[0] == 'pow' else (den, 1)
    if fact[0] != 'factorial' or not 1 <= weight <= 6:
        raise Unsupported('Need a positive factorial power in the given term')

    def affine(e):
        try:
            p, q_ = rational_on_tail(e, n, start)
        except (NotRational, Undefined) as err:
            raise Unsupported('The progression or factorial argument is not affine') from err
        if len(p) != 2 or q_ != (1,) or any(v.denominator != 1 for v in p):
            raise Unsupported('Need nonnegative affine integer indices for all terms')
        b, a = map(int, p)
        if not 1 <= a <= 64 or not -64 <= b <= 64 or a * start + b < 0:
            raise Unsupported('The original first exponent or factorial is outside the allowed range')
        return a, b

    a, b = affine(raw[1][2]);g, h = affine(fact[1])
    if start > 32:
        raise Unsupported('The initial factorial exceeds the finite certificate range')
    ode = task['equation']
    pattern = re.compile(r'\bD(?:\^(\d+))?\s+([A-Za-z_]\w*)\b')
    matches = list(pattern.finditer(ode))
    dependents = {m[2] for m in matches}
    if len(dependents) != 1 or x in dependents or n in dependents or ode.count('=') != 1 or '__D' in ode:
        raise Unsupported('Need an equality in a single series and its derivatives')
    dependent = dependents.pop()
    orders = {int(m[1] or 1) for m in matches}
    if not all(1 <= d <= 16 for d in orders):
        raise Unsupported('The indicated derivative order is outside this coefficient certificate')
    names = {d: f'__D{d}' for d in orders | {0}}
    changed = pattern.sub(lambda m: names[int(m[1] or 1)], ode)
    changed = re.sub(r'\b' + re.escape(dependent) + r'\b', names[0], changed)
    left, right = changed.split('=')
    z = ('v', x)
    symbols = {('s', name): d for d, name in names.items()}
    lhs = m.parse(left, x, list(names.values()));rhs = m.parse(right, x, list(names.values()))
    if domain_conditions(lhs) or domain_conditions(rhs):
        raise Unsupported('The original differential equation has an additional domain restriction')
    p, q_ = m.rational_form(('add', lhs, ('mul', q(-1), rhs)))
    if set(q_) != {()} or not q_[()]:
        raise Unsupported('The equation is not a polynomial linear differential identity')
    rows = {}
    for mon, coeff in p.items():
        powers = dict(mon)
        m_x = powers.pop(z, 0)
        if len(powers) != 1 or m_x > 32:
            raise Unsupported('The equation includes a nonlinear or high-order differential term')
        (symbol, exponent), = powers.items()
        if symbol not in symbols or exponent != 1:
            raise Unsupported('The equation is not linear in the indicated function and derivatives')
        d = symbols[symbol]
        first = max(start, (d - b + a - 1) // a)
        shifted, residue = divmod(a * first + b - d + m_x, a)
        rows.setdefault(residue, []).append((coeff / q_[()], d, shifted, first - shifted, m_x))
    k = ('v', '__coefficient_index');proofs = []
    for residue, groups in sorted(rows.items()):
        lower = max(j for _, _, j, _, _ in groups)

        # Extract each present initial coefficient before using an eventual common factorial.
        for j in range(min(t[2] for t in groups), lower):
            total = Fraction(0)
            for c, d, first, shift, _ in groups:
                if j >= first:
                    u = a * (j + shift) + b
                    total += c * prod(u - v for v in range(d)) / factorial(g * (j + shift) + h) ** weight
            if total:
                raise Unsupported('An initial coefficient of the proposed differential identity is nonzero')

        base = min(g * shift + h for _, _, _, shift, _ in groups)
        if g * lower + base < 0 or any((g * shift + h - base) * weight > 128 for _, _, _, shift, _ in groups):
            raise Unsupported('The proposed factorial denominator is not nonnegative on the common tail')
        common = m.add(m.mul(q(g), k), q(base));tail = ZERO
        for c, d, _, shift, _ in groups:
            power = m.add(m.mul(q(a), k), q(a * shift + b))
            num = q(c);denom = ONE
            for j in range(d):
                num = m.mul(num, m.add(power, q(-j)))
            for j in range(1, g * shift + h - base + 1):
                denom = m.mul(denom, m.power(m.add(common, q(j)), weight))
            tail = m.add(tail, m.div(num, denom))
        if m.rational_form(tail)[0]:
            raise Unsupported('An eventual coefficient of the proposed differential identity is nonzero')
        proofs.append(dict(residue=residue, tail_from=lower, common_factorial=source(common),
                           terms=[(q(c), d, j, shift, degree) for c, d, j, shift, degree in groups],
                           rational_tail=source(tail), residual=ZERO))
    plan = dict(theorem='method.factorial_series_differential_coefficients', index=n, first_index=start,
                exponent=[a, b], factorial_argument=[g, h], factorial_power=weight,
                radius_argument='the absolute term ratio tends to zero for every fixed x',
                exact_coefficient_checks=proofs)
    return plan, dict(equation=ode, proven=True, valid_on='all_real')


def cauchy_product_identity(task, library):
    """Use the binomial theorem on the exponential series, then compare derived functions."""
    from math import lcm
    from operations import expression_positions
    from tasks import known_guard, source
    from verify import same_value

    base = {'kind', 'id', 'source', 'method_requirement'}
    if not library.data.get('cauchy_product_identity'):
        raise Unsupported('No absolute Cauchy-product rule is available')
    plan = dict(theorem='method.exponential_cauchy_product', initial='E(0)=1',
                majorant='ratio |z|/(n+1) yields absolute convergence on every finite disk',
                multiplication='the absolute double sum can be grouped by total degree',
                coefficient='Σ_{j=0..n} u^j v^(n−j)/(j!(n−j)!) = (u+v)^n/n! by the binomial theorem')
    if 'definition' in task:
        if set(task) - base - {'definition', 'identity'} or task.get('method_requirement', 'direct_from_series') != 'direct_from_series':
            raise Unsupported('The original direct series identity has an additional obligation')
        definition = re.sub(r'\s+', '', task['definition'])
        match = re.fullmatch(r'([A-Za-z_]\w*)\(([A-Za-z_]\w*)\)=sum_\{([A-Za-z_]\w*)>=0\}(.+)', definition)
        if not match or len(set(match.groups()[:3])) != 3:
            raise Unsupported('The function must be defined by an entire exponential series')
        f, x, n, term = match.groups()
        xz, nz = ('v', x), ('s', n)
        expect = ('div', ('rpow', xz, nz), ('factorial', nz))
        term = re.sub(r'\b' + re.escape(n) + '!', 'factorial(' + n + ')', term)
        if m.parse(term, x, [n], extra_functions={'factorial'}) != expect:
            raise Unsupported('The given coefficients are not an exponential series')
        lhs, rhs = task['identity'].split('=')
        params = sorted(set(re.findall(r'[A-Za-z_]\w*', lhs + ' ' + rhs)) - {f})
        if not params:
            raise Unsupported('The arguments of the original identity are absent')
        left, right = [m.parse(t, None, params, extra_functions={f}) for t in (lhs, rhs)]
        if right[0] == 'mul':left, right = right, left
        if left[0] != 'mul' or any(a[0] != f for a in left[1:]) or right[0] != f:
            raise Unsupported('The requested identity is not a product of two values of the given function')
        u, v = (a[1] for a in left[1:]);w = right[1]
        if (any(not m.constant_defined(a, m.context(dict(variable='__u', parameters=params))) for a in (u, v, w)) or
                not same_value(m.add(u, v), w)):
            raise Unsupported('The requested argument sum or its original domain has not been proved')
        plan.update(source_function=f, arguments=[u, v], composed_argument=w)
        return plan, dict(equality=task['identity'], proven=True)

    if set(task) - base - {'definitions', 'claim'} or task.get('method_requirement', 'from_given_series') != 'from_given_series':
        raise Unsupported('The original trigonometric series proof has an extra obligation')
    names = {}
    for definition in task['definitions']:
        match = re.fullmatch(r'(sin|cos)\s+([A-Za-z_]\w*)\s*=\s*sum_\{([A-Za-z_]\w*)>=0\}\s*(.+)', definition)
        if not match or match[2] == match[3] or match[1] in names:
            raise Unsupported('Need the even and odd entire series from the original definitions')
        trig, x, n, term = match.groups()
        term = re.sub(r'\(([^()]+)\)!', r'factorial(\1)', re.sub(r'\s+', '', term))
        odd = trig == 'sin'
        expected = f'(-1)^{n}*{x}^(2*{n}'+('+1' if odd else '')+f')/factorial(2*{n}'+('+1' if odd else '')+')'
        parse = lambda t: m.parse(t, x, [n], extra_functions={'factorial'})
        if parse(term) != parse(expected):
            raise Unsupported('The given trig function has different coefficients')
        names[trig] = x
    if set(names) != {'sin', 'cos'} or len(set(names.values())) != 1:
        raise Unsupported('Both trig series must bind the same independent variable')
    x = names['sin'];xz = ('v', x)
    raw = [m.parse(t, x) for t in task['claim'].split('=')]
    ctx = m.context(dict(variable=x))
    if len(raw) != 2 or any(not known_guard(g, ctx) for e in raw for g in domain_conditions(e)):
        raise Unsupported('The original equality has unproved domain constraints')
    phases = {}
    for expr in raw:
        for _, e in expression_positions(expr):
            if e[0] in names:
                phase = m.num(m.simplify(m.div(e[1], xz)))
                if phase is None or not same_value(e[1], m.mul(q(phase), xz)):
                    raise Unsupported('The harmonic arguments must be fixed rational multiples of the variable')
                phases[e] = phase
    l = lcm(*(f.denominator for f in phases.values()))
    if not phases or any(abs(f*l)>64 for f in phases.values()):
        raise Unsupported('No bounded common harmonic phase')
    Z = ('v', '__phase');i = ('s', '__imaginary')
    replacements = {}
    for e, f in phases.items():
        k = int(f*l)
        positive, negative = m.power(Z, k), m.power(Z, -k)
        replacements[e] = (m.div(m.add(positive, negative), q(2)) if e[0]=='cos' else
                           m.div(m.add(positive, m.neg(negative)), m.mul(q(2), i)))
    left, right = (m.substitute(t, replacements) for t in raw)
    num, _ = m.rational_form(m.add(left, m.neg(right)))
    reduced = {}
    for mon, a in num.items():
        d = dict(mon);k = d.pop(i, 0)
        d[i] = k % 2
        key = frozenset((atom, degree) for atom, degree in d.items() if degree)
        reduced[key] = reduced.get(key, 0) + (-1)**(k//2)*a
    if any(reduced.values()):
        raise Unsupported('The supplied identity does not follow from the proved Laurent polynomial reduction')
    plan.update(split='the even and odd subseries of E(ix) are cos(x) and i*sin(x)',
                phase=f'E(i*{x}/{l})', phase_nonzero='E(i*x/l)*E(-i*x/l)=1',
                formed_harmonics=[(source(e), q(f)) for e, f in phases.items()],
                checked_relation='zero Laurent numerator after i²=−1')
    return plan, dict(equality=task['claim'], proven=True)


def integer_sign_period(expr, name, start):
    """Prove a periodic sign sequence from an integer-valued polynomial exponent."""
    if expr in (ONE, q(-1)):
        return [int(m.num(expr))]
    if expr[0]!='rpow' or expr[1]!=q(-1):
        raise Unsupported('The source coefficient does not have a proved sign period')
    from graphs import peval
    p,d=rational_on_tail(expr[2],name,start)
    if len(d)!=1 or not d[0] or len(p)>7:
        raise Unsupported('The oscillation is not a fixed integer polynomial phase')
    p=tuple(v/d[0] for v in p)
    common=lcm(*(w.denominator for w in p))
    k=2*common
    if k>128:
        raise Unsupported('The certified phase period is too large')
    residues=[peval(p,j) for j in range(k)]
    if any(x.denominator!=1 for x in residues):
        raise Unsupported('A noninteger exponent of the original negative base remains')
    # The scaled integer polynomial changes by a multiple of 2*common under this shift.
    return [(-1 if int(v)%2 else 1) for v in residues]


def positive_step_amplitude(e, name, start, ctx):
    """Read 1/a(n), with a power or a logarithm as the checked denominator."""
    n=('v',name)
    if e==n and start>=1:return q(1)
    if e==('sqrt',n) and start>=1:return q(1,2)
    if e==('ln',n) and start>=2:return 'reciprocal_log'
    if e[0]=='pow' and e[1]==n and start>=1:return q(e[2])
    if e[0]=='rpow' and e[1]==n and start>=1 and m.constant_defined(e[2],ctx):
        p=m.simplify(e[2])
        if p[0]=='s' or m.num(p) is not None:return p
    raise Unsupported('The perturbation amplitude does not preserve the original index domain')


def product_logarithmic_perturbation(term, name, start, ctx):
    """Classify a small periodic perturbation by its linear and quadratic log terms."""
    def unit_add(e):
        return next((b for a,b in (e[1:],e[1:][::-1]) if a==ONE),None) if e[0]=='add' else None

    u=unit_add(term);multiplier=1
    if u is None and term[0]=='div' and term[2][0]=='add':
        scale=term[1];first,last=term[2][1:]
        u=('div',last,scale) if first==scale else ('div',first,scale) if last==scale else None
        multiplier=-1
    if u is None:
        raise Unsupported('There is no unit factor plus its original perturbation')
    n=('v',name)
    if (u[0]=='div' and u[1][0]==u[2][0]=='rpow' and u[1][2]==u[2][2]==n
            and m.constant_defined(u[1][1],ctx) and m.nonzero(u[2][1],ctx)):
        u=('rpow',m.div(u[1][1],u[2][1]),n)
    if u[0]=='rpow' and u[2]==('v',name) and m.constant_defined(u[1],ctx) and multiplier==1:
        if start==0 and term[0]=='add':
            return dict(theorem='method.product_geometric_perturbation',initial='the original polynomial power at index zero is 1',ratio=u[1]),dict(
                cases=[{'condition':'abs(r)<1','classification':'converges_nonzero','absolute':True},
                       {'condition':'r=-1','classification':'converges_to_zero_by_zero_factor'},
                       {'condition':'abs(r)>=1 and r!=-1','classification':'diverges_nonconvergent'}],ratio=u[1])
        if start>=1:
            return dict(theorem='method.product_geometric_perturbation',ratio=u[1],
                        witness='on |r|<1 the absolute perturbations have a geometric sum, while a nonzero product requires factors tending to one'),dict(
                cases=[{'condition':'abs(r)<1','classification':'converges_nonzero','absolute':True},
                       {'condition':'r=-1','classification':'converges_to_zero_by_zero_factor'},
                       {'condition':'abs(r)>=1 and r!=-1','classification':'diverges_nonconvergent'}],ratio=u[1])
    if (start==0 and u[0]=='mul' and u[1]==q(-1) and u[2][0]=='rpow' and u[2][2]==('v',name)
            and m.constant_defined(u[2][1],ctx) and multiplier==1):
        return dict(theorem='method.product_geometric_perturbation',ratio=u[2][1],zero_index=start,
                    witness='all factors are defined integer polynomial powers; the factor at index zero vanishes'),dict(
                    classification='converges_to_zero_by_zero_factor',partial_product_limit=ZERO)
    if u[0]!='div':raise Unsupported('No periodic-over-power or logarithmic perturbation was found')
    phase=integer_sign_period(u[1],name,start)
    p=positive_step_amplitude(u[2],name,start,ctx)
    average=Fraction(sum(phase),len(phase));indices=[k for k,z in enumerate(phase) if z==-1]
    if start==1 and phase[1%len(phase)]==-1 and p!='reciprocal_log':
        result=dict(classification='undefined_factor' if multiplier<0 else 'converges_to_zero_by_zero_factor',zero_index=1)
        if multiplier==1:result['partial_product_limit']=ZERO
        return dict(theorem='method.product_logarithmic_perturbation',phase=phase,zero_index=1),result
    converge=dict(classification='converges_nonzero')
    def diverge(direction):
        return dict(classification='diverges_unbounded' if direction>0 else 'diverges_to_zero',
                    partial_product_magnitude='+inf' if direction>0 else ZERO)
    plan=dict(theorem='method.product_logarithmic_perturbation',period=phase,mean=q(average),inverse=multiplier<0,
              series='log(1+u)=u-u^2/2+O(abs(u)^3) on an eventual positive tail',
              linear_term='split the sign into its mean and a zero-mean periodic part; Dirichlet handles the latter',
              comparison='for mean zero, the quadratic term decides when it is nonsummable; with nonzero mean the linear term dominates')
    if p=='reciprocal_log':
        plan.update(amplitude='1/ln(n)',initial_domain='n>=2; ln(2)<1<ln(3), all unit factors are nonzero',
                    quadratic_diverges='eventually ln(n)^2<=n')
        return plan,diverge(multiplier*(1 if average>0 else -1))

    tail_direction=multiplier*(1 if average>0 else -1)
    converse_cut=Fraction(1,2) if not average else Fraction(1)
    singular=dict(classification='undefined_factor' if multiplier<0 else 'converges_to_zero_by_zero_factor',zero_phase_residues=indices)
    if indices and multiplier==1:singular['partial_product_limit']=ZERO
    nonshrinking=dict(classification='diverges_nonconvergent',why='the original factors do not tend to one')
    if not indices and len(set(phase))==1 and phase[0]==1:
        nonshrinking=diverge(multiplier)
    weight=m.num(p)
    if weight is not None:
        if weight==0 and indices:return plan,singular
        if weight<=0:return plan,nonshrinking
        if weight<=converse_cut:return plan,diverge(tail_direction)
        return plan,dict(converge,absolute=weight>1)
    symbol=p[1]
    rows=[dict(condition=f'{symbol}>1',**converge,absolute=True)]
    if not average:rows.append(dict(condition=f'1/2<{symbol}<=1',**converge,absolute=False))
    rows.append(dict(condition=f'0<{symbol}<={converse_cut}',**diverge(tail_direction)))
    if indices:rows.append(dict(condition=f'{symbol}=0',**singular));negative=f'{symbol}<0'
    else:negative=f'{symbol}<=0'
    rows.append(dict(condition=negative,**nonshrinking))
    return plan,dict(parameter=symbol,cases=rows)


def compensated_log_product(term, name, start, params, conditions):
    """Build the logarithmic residual and prove a summable upper bound without assuming its exact order."""
    from tasks import known_guard, source
    from uniform import coefficient_rows

    if term[0]!='mul' or start<1:
        raise Unsupported('Need a product of a unit perturbation and a positive compensator')
    b,e=term[1:]
    if b[0]=='exp':b,e=e,b
    if e[0]!='exp' or b[0]!='add' or ONE not in b[1:]:
        raise Unsupported('The compensating exponent and original unit perturbation are not explicit')
    a=b[2] if b[1]==ONE else b[1];g=e[1]
    n=('v',name);variable='__sqrt_index'
    if variable in {name,*params}:raise Unsupported('A fresh integer-root coordinate is needed')
    z=('v',variable);sqrt=('sqrt',n)
    root=2 if m.contains(term,sqrt) else 1
    chart={n:m.power(z,root)}
    if root==2:chart[sqrt]=z
    A,G=(m.substitute(f,chart) for f in (a,g))
    scope=m.context(dict(variable=name,parameters=[*params,variable],parameter_conditions=conditions))
    ray={z:m.add(ONE,m.power(('s',variable),2))}
    for rel,f in (*domain_conditions(A),*domain_conditions(G)):
        if not known_guard((rel,m.substitute(f,ray)),scope):
            raise Unsupported('The original product or exponent is not defined for all printed indices')

    def powers(f):
        p,d=m.rational_form(f)
        if any(w!=z and m.contains(w,z) for form in (p,d) for mon in form for w,_ in mon):
            raise Unsupported('An unsupported factor remains in the regularizing coordinate')
        a0,b0=coefficient_rows(p,z),coefficient_rows(d,z)
        if not b0 or not known_guard(('nonzero',b0[max(b0)]),scope):
            raise Unsupported('The leading denominator coefficient is not proved nonzero')
        return a0,b0

    P,Q=powers(A)
    degree=max(Q)-max(P,default=-1)
    if degree<=0:raise Unsupported('No vanishing bound for the perturbation')
    truncation=root//degree
    residual=G
    for k in range(1,truncation+1):
        residual=m.add(residual,m.mul(q((-1)**(k+1),k),m.power(A,k)))
    l,mden=powers(residual)
    rest_power=Fraction(max(mden)-max(l),root) if l else '+inf'
    if l and rest_power<=1:raise Unsupported('The compensating terms leave a nonsummable residual')
    unit_num,_=powers(m.add(ONE,A))
    if set(unit_num)!={0,1} or not known_guard(('nonzero',unit_num[1]),scope):
        raise Unsupported('The exact finite zero-factor condition needs a separate witness')
    zero=m.simplify(m.div(m.neg(unit_num[0]),unit_num[1]));zero_n=m.power(zero,root)
    plan=dict(theorem='method.compensated_product_logarithm',tail_coordinate=f'{name}^(1/{root})',
              perturbation=A,exponent=G,truncation=truncation,log_residual=residual,perturbation_order=q(degree,root),
              residual_order=q(rest_power) if l else '+inf',remainder_order=q((truncation+1)*degree,root),
              zero_coordinate=zero,proof='surviving terms and the Taylor remainder are absolutely summable on the positive tail')
    return plan,dict(cases=[dict(condition=f'{source(zero)}>0 and {source(zero_n)} is an integer >= {start}',
                                 classification='converges_to_zero_by_zero_factor',partial_product_limit=ZERO),
                            dict(condition='all original factors nonzero',classification='converges_nonzero',absolute_on_tail=True)])


def parameter_rational_product(task):
    """Keep the original positive denominator, then compare the first unequal monic coefficient."""
    from tasks import source
    from uniform import coefficient_rows
    from verify import same_value

    kind=task['kind'];begin=task['start_index'];name=task['index'];text=task['factor_or_given']
    conditions=task.get('stated_conditions',[])
    if kind!='infinite_product_convergence' or len(conditions)!=1:
        raise Unsupported('The original denominator premise is required')
    z=('v',name)
    claim=re.fullmatch(r'(.+)>0 for each integer '+re.escape(name)+r'>='+re.escape(begin),conditions[0])
    products=re.fullmatch(r'prod\((\w+)=1\.\.(\w+),'+re.escape(name)+r'-(\w+)_\1\)/prod\(\1=1\.\.\2,'+re.escape(name)+r'-(\w+)_\1\)',text)
    if claim:
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-{name})
        if task.get('parameters',names)!=names:raise Unsupported('The original coefficient tuples are not bound')
        term=m.parse(text,name,names)
        if term[0]!='div' or not same_value(term[2],m.parse(claim[1],name,names)) or any(domain_conditions(f) for f in term[1:]):
            raise Unsupported('The original positivity premise does not cover the raw denominator')
        P,Q=(coefficient_rows(m.rational_form(t)[0],z) for t in term[1:])
        d=max(P,default=0)
        if d<1 or d!=max(Q,default=0) or P[d]!=ONE or Q[d]!=ONE:
            raise Unsupported('Need original monic polynomials of the same positive degree')
        coefficient=m.add(P.get(d-1,ZERO),m.neg(Q.get(d-1,ZERO)))
        delta=source(coefficient);zero=f'{source(term[1])}=0 at some integer {name}>={begin}'
        plan=dict(numerator=term[1],denominator=term[2],degree=d,coefficient=coefficient)
    elif products:
        i,p,a,b=products.groups()
        if (task.get('parameters') or conditions!=[f'{begin}>{b}_{i} for {i}=1..{p}'] or len({i,p,a,b,name,begin})!=6):
            raise Unsupported('The original finite list or its denominator assumptions are unbound')
        delta=f'sum_(i=1..{p}) ({b}_i-{a}_i)';zero=f'some {a}_i is an integer >= {begin}'
        plan=dict(degree=p,coefficient=delta,coefficient_argument='the next monic coefficient is minus the sum of the roots')
    else:raise Unsupported('The original positive denominator does not have a supported monic form')
    plan.update(theorem='method.monic_parameter_product',original_conditions=conditions,initial_index=begin,
                argument='Compare the first nonconstant term of the logarithm. Equal coefficients leave a summable quadratic bound. An actual zero factor is handled on the original integer index set.')
    return plan,dict(first_coefficient_difference=delta,zero_factor_condition=zero,cases=[
        dict(condition='a zero factor exists',classification='converges_to_zero_by_zero_factor',partial_product_limit=ZERO),
        dict(condition='no zero factor and coefficient difference = 0',classification='converges_nonzero'),
        dict(condition='no zero factor and coefficient difference < 0',classification='diverges_to_zero'),
        dict(condition='no zero factor and coefficient difference > 0',classification='diverges_unbounded')])


def paired_product_diagnostics(text, name, start, summed):
    """Prove an original first zero or paired convergence, and test ordinary and squared increments."""
    from tasks import known_guard, source
    from graphs import peval

    match=re.fullmatch(r'1\+(\w+)_'+re.escape(name)+r',\s*\1_\(2(\w+)-1\)=([^,]+),\s*\1_\(2\2\)=(.+)',text)
    if start!=1 or not match or f'{match[1]}_{name}'!=summed or len({name,match[1],match[2]})!=3:
        raise Unsupported('The original odd and even increments do not give complete pairs')
    k=match[2];original=[m.parse(s,k) for s in match.groups()[2:]]
    t='__paired_root';y=('v',t);index=('v',k);coordinate={index:m.power(y,2),('sqrt',index):y}
    odd,even=(m.substitute(x,coordinate) for x in original)
    ctx=m.context(dict(variable=t,parameters=['u']));ray={y:m.add(ONE,m.power(('s','u'),2))}
    if any(not known_guard((g,m.substitute(x,ray)),ctx) for e in (odd,even) for g,x in domain_conditions(e)):
        raise Unsupported('An original paired factor is undefined on its integer domain')
    def leading(e):
        p,d=rf(e,t)
        if not any(p):return '+inf',Fraction(0)
        return len(d)-len(p),p[-1]/d[-1]
    first=[peval(p,1)/peval(d,1) for p,d in (rf(m.add(ONE,e),t) for e in (odd,even))]
    if all(first):raise Unsupported('The original paired form does not establish the specified early zero')
    product=m.mul(m.add(ONE,odd),m.add(ONE,even));residual=m.add(product,q(-1))
    order,_=leading(residual)
    summand=m.add(odd,even);squared=m.add(m.power(odd,2),m.power(even,2))
    rates=[leading(e) for e in (summand,squared)]
    if ((order!='+inf' and order<=2) or not all(p!='+inf' and 0<p<=2 and c>0 for p,c in rates)
            or not all(p=='+inf' or p>0 for p,_ in map(leading,(odd,even)))):
        raise Unsupported('The requested paired and unpaired tail comparisons are not established')
    tail={y:m.add(q(4,3),m.power(('s','u'),2))}
    nonzero_tail=all(known_guard(('nonzero',m.substitute(m.add(ONE,e),tail)),ctx) for e in (odd,even))
    return (dict(theorem='method.paired_product_increments',coordinate='sqrt(pair_index)',odd_increment=odd,even_increment=even,
                paired_factor=product,first_factors=list(map(q,first)),coefficient_orders=[(p,q(c)) for p,c in rates],paired_residual_order=order,
                nonzero_tail=nonzero_tail,
                argument=('Первый нулевой множитель обнуляет все последующие частичные произведения по определению главы. '
                          'После удаления первой пары свёрнутый множитель имеет суммируемое отклонение от единицы. '
                          'Для двух рядов попарно сложенные члены сравниваются снизу с расходящейся степенной последовательностью.')),
        dict(classification='converges_to_zero_by_zero_factor',partial_product_limit=ZERO,zero_index=first.index(0)+1,
             increments_series='diverges_to_positive_infinity',squared_increments_series='diverges_to_positive_infinity',
             grouped_tail_is_nonzero=nonzero_tail))


def moment_shift_bound(polynomial, lower, upper, power):
    """Certify t·|P(t)|^rho < 1 and θ^(-1)·|P|_+(θ^(-1))^rho < 1."""
    n,d=power.numerator,power.denominator
    cost=sum(abs(c)/lower**j for j,c in enumerate(polynomial))
    if cost**n>=lower**d:return None
    root_counts=[]
    for sign in (-1,1):
        check=pa((Fraction(1),),(Fraction(0),)*d+tuple(sign*c for c in pp(polynomial,n)))
        variations=distinct_root_counter(check)
        count=variations(Fraction(0))-variations(upper)
        if count or sum(c*upper**j for j,c in enumerate(check))<=0:return None
        root_counts.append(count)
    return dict(base_interval=(q(lower),q(upper)),shift_coefficients=tuple(map(q,polynomial)),
                trial_power=q(power),error_norm_upper=q(cost),sturm_root_counts=tuple(root_counts))


def covered_moment_shift_bounds(upper):
    """Build an overlapping cover together with the first-difference range."""
    small=Fraction(161,100);split=Fraction(9,5)
    if not 1<upper<=2 or (2*small-1)**2>=5:return None
    proposals=[(small,split,(1,0,-2,1),Fraction(2,3)),
               (split,Fraction(2),(-2,1,4,-4,1),Fraction(3,8))]
    bounds=[]
    for lower,end,coefficients,power in proposals:
        if upper<=lower:break
        bound=moment_shift_bound(tuple(map(Fraction,coefficients)),lower,min(upper,end),power)
        if bound is None:return None
        bounds.append(bound)
    return bounds


def geometric_cosine_log_product(term, name, start, conditions, *, integer_phase=False, moment_phase=False,
                                 polynomial_shift=False):
    """Classify the bounded geometric base and its unit endpoints."""
    from tasks import source

    if start<1 or term[0]!='mul':return None
    unit,cosine=term[1:]
    if unit[0]=='cos':unit,cosine=cosine,unit
    if cosine[0]!='cos' or unit[0]!='add' or ONE not in unit[1:]:return None
    increment=unit[2] if unit[1]==ONE else unit[1]
    n=('v',name)

    def scaled_ratio(expr):
        if expr[0]!='div':return None
        top,bottom=expr[1:]
        if bottom==n:power=ONE
        elif bottom[0] in ('pow','rpow') and bottom[1]==n:
            power=q(bottom[2]) if bottom[0]=='pow' else bottom[2]
        else:return None
        weight=q(1)
        if top[0]=='mul':
            if m.num(top[2]) is not None:top,weight=top[1:]
            else:weight,top=top[1:]
        if top[0]=='rpow' and top[2]==n and top[1][0]=='s' and m.num(weight):
            return weight,top[1],power
        return None

    linear,phase=scaled_ratio(increment),scaled_ratio(cosine[1])
    if not linear or not phase or linear[1]!=phase[1]:return None
    c,base,p=linear; d,_,r=phase; z=source(base)
    strict=f'abs({z})<1'; bounded=f'abs({z})<=1'; exterior=f'abs({z})>1'
    conditions={cond.replace(' ','').replace('≤','<=') for cond in conditions}
    if not all(e[0] in ('q','s') for e in (p,r)):return None
    ptext,rtext=map(source,(p,r))
    integer_hypotheses={f'{rtext}integer',f'{rtext}inZ'} if integer_phase and r[0]=='s' and r!=base else set()
    fixed=m.num(r)
    integral=integer_phase and (bool(conditions&integer_hypotheses) or fixed is not None and fixed.denominator==1)
    upper=f'abs({z})<(1+sqrt(5))/2'
    bounds=None
    if polynomial_shift and moment_phase and integer_phase and upper not in conditions:
        pattern=rf'abs\({re.escape(z)}\)<=?([0-9]+(?:/[1-9][0-9]*|\.[0-9]+)?)'
        for condition in sorted(conditions):
            match=re.fullmatch(pattern,condition)
            if match:
                bounds=covered_moment_shift_bounds(Fraction(match[1]))
                if bounds is not None:upper=condition
                break
    moment=moment_phase and upper in conditions
    region=next((b for b in (strict,bounded,exterior,upper) if b in conditions),None)
    outside=region in (None,exterior,upper)
    if outside and not (integral or moment):
        if integer_phase and not conditions:
            raise Unsupported('Outside the unit interval, exclusion of a nonzero product still needs a bound on integer approximations to the growing phase for noninteger exponents.')
        return None
    signs={f'{source(e)}>0' for e in (p,r) if e[0]=='s' and e!=base}
    upper_conditions={upper} if moment else set()
    if not conditions<=({region}|signs|integer_hypotheses|upper_conditions):return None
    endpoints=region in (None,bounded,upper)
    if endpoints and 2*m.num(c)==m.num(d)**2:return None
    zero=f'some integer {name}>={start} has {source(increment)}=-1 or {source(cosine[1])}=(k+1/2)*pi for an integer k'
    no_zero='no such zero factor'
    cases=[dict(condition=zero,classification='zero_partial_product_tail',partial_product_limit=ZERO)]
    argument=['Начальные нули проверяются по исходному множителю.']
    if region!=exterior:
        cases.append(dict(condition=f'{strict} and {no_zero}',classification='converges_nonzero',absolute=True))
        argument.append('На положительном хвосте логарифм произведения равен сумме двух логарифмов. При |z|<1 мажорируем отклонение линейного множителя геометрическим рядом, а косинус даёт квадратичное отклонение.')
    if endpoints:
        cases.extend([
            dict(condition=f'{z}=1 and {ptext}>1 and {rtext}>1/2 and {no_zero}',classification='converges_nonzero',absolute=True),
            dict(condition=f'{z}=1 and ({ptext}<=1 or {rtext}<=1/2) and {no_zero}',classification='no_nonzero_convergence'),
            dict(condition=f'{z}=-1 and {ptext}>1/2 and {rtext}>1/2 and {no_zero}',classification='converges_nonzero',absolute_if=f'{ptext}>1'),
            dict(condition=f'{z}=-1 and ({ptext}<=1/2 or {rtext}<=1/2) and {no_zero}',classification='no_nonzero_convergence')])
        argument.extend([
            'При p,q>0 и z=1 ведущие члены логарифма равны c/n^p и −d²/(2n^(2q)). На совпадающей степени проверено, что коэффициент разности ненулевой. В обоих случаях решает признак степенного ряда.',
            'При p,q>0 и z=−1 линейный член c(−1)^n/n^p сходится по Дирихле. Остаток логарифма начинается с −c²/(2n^(2p))−d²/(2n^(2q)), без отмены ведущего члена. Для абсолютной сходимости при p≤1 и q>1/2 косинус и квадратичный остаток на сходящейся ветви суммируемы, а модуль линейного члена имеет расходящуюся сумму.',
            'Для замкнутой границы с неположительным показателем необходимое условие проверяем по чётным индексам. При q>0 и p≤0 линейный множитель имеет предел 1+c или неограничен. При q=0 косинус ненулевой и трансцендентный по теореме Линдемана, поскольку d — ненулевой рациональный аргумент. В обоих случаях произведение факторов не стремится к единице.',
            'При q<0 требовалось бы, чтобы cos(d(2k)^(−q)) стремился к алгебраическому значению 1, 1/(1+c) или 0 по знаку p. Если c=−1 и p=0, чётный множитель нулевой. В допустимом диапазоне значений косинуса получаем приближение с ошибкой o(1) к двум классам углов ±arccos значения по модулю 2π.',
            'Пусть β=−q. Для нецелого β разности порядка floor(β)+1 приближённых углов стремятся к нулю. Каждая разность попадает в один из конечного набора классов по модулю 2π, так что разности точно нулевые на хвосте. Получился многочлен, который отличается от d(2k)^β на o(1), что невозможно. Для целого β разность порядка β стремится к ненулевому рациональному d·2^β·β!. Тот же конечный набор классов вынуждает предел принадлежать одному из них. Косинус каждого класса алгебраичен, поскольку класс целочисленно кратен углу с алгебраическим косинусом. Косинус ненулевого рационального предела трансцендентен.'])
    if outside:
        cases.append(dict(condition=f'{exterior} and {no_zero}',classification='no_nonzero_convergence'))
        argument.append('Если исходные множители стремятся к единице при θ=|z|>1, косинус имеет порядок не больше n^p θ^(−n). У каждого его позднего аргумента есть нечётный целый приближатель aₙ с aₙ=(2|d|/π) θ^n n^(−q)+O(n^p θ^(−n)).')
    if outside and integral:
        argument.extend([
            'Целый q позволяет домножить на n^q при q≥0 и оставить приближатель при q<0. Получаем целое bₙ=λ θ^n n^k+O(n^M θ^(−n)), где k≥0 целое, λ=2|d|/π.',
            'В определителях Ганкеля порядка m главная матрица имеет ранг не больше k+1 по биномиальному разложению (n+i+j)^k. Поэтому при m>2(k+1) каждый ненулевой член полилинейного разложения экспоненциально мал. Целый определитель равен нулю на хвосте.',
            'Для наибольшего размера r с неокончательно нулевым определителем тождество соседних миноров показывает, что он нигде не нулевой на позднем хвосте: один ноль влечёт ноль следующего минора и затем всех остальных. Единственное решение линейной системы даёт r рациональных коэффициентов рекурсии, а нулевой минор размера r+1 переносит их в следующее окно. Поэтому коэффициенты постоянны.',
            'Производящая функция bₙ тогда рациональна над ℚ. Ошибка аналитична в круге радиуса θ. Главная часть имеет полюс в 1/θ порядка k+1 с коэффициентом λ k! в масштабе 1−θz. Для рациональной функции над ℚ положение полюса и этот коэффициент алгебраичны. Это противоречит трансцендентности 2|d|/π для ненулевого рационального d.'])
    if outside and not integral and bounds:
        argument.extend([
            'Ограничение покрыто прежними первыми разностями ниже золотого сечения и проверенными целочисленными многочленами сдвига P. Для каждого интервала Штурм подтверждает 1±t^d P(t)^n>0 на всём отрезке моментов при пробном ρ*=n/d. Норма переноса ошибки оценена суммой модулей коэффициентов при 1/θ. Её степень ρ* строго меньше θ.',
            'Для любого фиксированного θ в таком интервале максимум Gρ(t)=t·|P(t)|^ρ пересекает 1 при 0<ρ<ρ*. На t≥1 модуль P строго меньше единицы, а на t<1 норма меньше единицы для всех этих ρ. Выбираем ρ чуть после пересечения, так что нормированный показатель ошибки θ⁻¹·|P|₊(1/θ)^ρ строго меньше максимума Gρ, который сам строго меньше единицы.',
            'Для q>0 используем гамма-момент с показателем q. При отрицательном нецелом q берём целое k с 0<q+k<1 и вес (ln(θ/t))^(q+k−1). Чётная степень m ближайшая к ρN превращает P(E)^m в множитель P(t)^m, а n^k — в (t d/dt)^k от всего произведения t^N P(t)^m. Неположительные целые q уже исключены доказательством через целочисленные миноры.',
            'Если максимум внутри, отделяем все максимизаторы от концов и переносим k производных на вес интегрированием по частям. Производная веса имеет постоянный ненулевой знак, а граничные члены и вклад вне выбранного отрезка имеют строго меньший экспоненциальный показатель. Если максимум у θ, выбираем ρ без ничьей с внутренними точками и без нулевого наклона. Ничья возможна для не более одного ρ: после равенства с t<θ отношение Gρ(t)/Gρ(θ) строго возрастает и остаётся больше единицы. У края логарифмическая производная положительна, поэтому ведущий член k-й производной имеет фиксированный знак. Выбор ρ возможен сколь угодно близко после пересечения.',
            'В обоих случаях интеграл имеет по модулю показатель максимума Gρ, а ошибка — строго меньший показатель. Поэтому ненулевая целочисленная величина P(E)^m a_N имеет модуль меньше единицы. Это противоречие исключает ненулевую сходимость.'
        ])
    if outside and not integral and not bounds:
        argument.extend([
            'Выбираем фиксированное целое k≥0 с q+k>0. Функция θ^n n^(−q) равна n^k, умноженному на момент t^n с положительным весом (ln(θ/t))^(q+k−1)/(t Γ(q+k)) на 0<t<θ. Это гамма-интеграл после замены t=θ exp(−v).',
            'Берём целую конечную разность Δ^m aₙ, где m — ближайшее чётное число к ρn. Для главной части под интегралом появляется (t d/dt)^k[t^n(t−1)^m]. На 1<t<θ её члены неотрицательны. Сверху интеграл ограничен многочленом от n, умноженным на θ^n(θ−1)^m. Интервал [θ−1/n,θ] даёт нижнюю границу постоянная·n^(−q) θ^n(θ−1)^m.',
            'На 0<t<1 абсолютный вклад экспоненциально мал, поскольку max t(1−t)^ρ<1 при всяком ρ>0. Фиксированное число производных меняет оценку лишь на множители полиномиального порядка и фиксированные сдвиги степеней. Из ошибок приближателей получается O(n^M θ^(−n)(1+1/θ)^m).',
            'При 1<θ<(1+√5)/2 выполняется (θ−1)(1+1/θ)<1. Значит, при ρ₀=ln θ/(−ln(θ−1)) главный показатель равен нулю, а оба побочных строго отрицательны. Выбираем ρ чуть больше ρ₀. Главный вклад сам стремится к нулю, но доминирует над обоими побочными. Поэтому целая разность с некоторого места строго между 0 и 1. Противоречие.'
        ])
    if not outside:theorem='method.product_logarithms_on_bounded_geometric_base'
    elif integral:theorem='method.integer_phase_product_exclusion'
    elif bounds:theorem='method.integer_polynomial_shift_moment_bound'
    else:theorem='method.geometric_phase_moment_differences'
    return dict(theorem=theorem,source_term=term,index=name,
                base=base,exponents=(p,r),weights=(c,d),conditions=sorted(conditions),argument=argument,
                **({'shift_bounds':bounds} if bounds and outside and not integral else {})),dict(cases=cases)


def classified_product(task, library, request, saved=None):
    """Build and verify a general transformation of the actual factors before classification."""
    from tasks import source

    if library.data.get('analytic_coefficient_reductions'):
        try:return analytic_product_reduction(task,library,request)
        except (Unsupported,NotRational,Undefined):pass
    fallback=lambda:infinite_rational_product(task,library,request,saved)
    kind=task['kind'];origin=task.get('source',{});note=origin.get('literal_requirement','');name=task['index'];start=task['start_index']
    if not library.data.get('classified_log_products') or task.get('method_requirement') is not None:
        return fallback()
    allowed={'kind','id','source','factor_or_given','index','start_index','parameters','stated_conditions'}
    if set(task)-allowed or not isinstance(name,str) or not name.isidentifier():
        return fallback()
    if isinstance(start,str) and start.isidentifier():return parameter_rational_product(task)
    if type(start)!=int or not 0<=start:return fallback()
    current=task['factor_or_given'];conditions=task.get('stated_conditions',[]);n=('v',name)
    if kind=='infinite_product_identity' and not conditions:
        claim=re.fullmatch(r'Prove convergence although sum (\w+) and sum \1² both diverge\.',note)
        if claim:return paired_product_diagnostics(current,name,start,claim[1])
        pattern=r'\(1\+1/sqrt\((\d+)\)\+1/\1\)\*\(1-1/sqrt\(\1\)\)'
        blocks=re.fullmatch(pattern+r'\*'+pattern.replace(r'\1',r'\2')+r'\*\.\.\.',current)
        if blocks and note=='Prove convergence although sum of printed perturbations diverges.' and start>=2 and list(map(int,blocks.groups()))==[start,start+1]:
            return dict(theorem='method.paired_product_increments',first_pair=start,
                        argument='В каждой паре (1+r+r²)(1−r)=1−r³, где r=1/√n. Эти положительные множители образуют сходящееся произведение. Неполная пара стремится к единице. Сумма исходных приращений каждой пары равна r²=1/n.'),dict(
                        classification='converges_nonzero',increments_series='diverges_to_positive_infinity')
    if kind=='infinite_product_identity' and not conditions and note=='Prove product=zeta(x)=sum(n>=1,1/n^x), p_n successive primes.':
        if start!=1 or current!=f'(1-1/p_{name}^x)^(-1)' or name=='x':raise Unsupported('Need all prime factors and the matching reciprocal-power series')
        return dict(theorem='method.euler_product_via_prime_factorization',index=name,
                    argument='При x>1 каждый множитель раскрываем геометрически. Конечное произведение суммирует n^(−x) по числам с простыми делителями из конечного набора. Основная теорема арифметики даёт кратность один. При расширении набора все положительные члены включаются, а сходимость степенного ряда даёт предел.'),dict(
                    equality_on='x>1',value='sum_(n>=1) n^(-x)',ordinary_series_for_x_le_1='diverges')
    if re.fullmatch(r'Does convergence of products of \w+ and \w+ imply convergence\?',note):
        pair=re.fullmatch(r'Does convergence of products of (\w+) and (\w+) imply convergence\?',note)
        a,b=pair.groups();relation={f'{a}+{b}':'sum',f'{a}^2':'square',f'{a}*{b}':'multiply',f'{a}/{b}':'divide'}.get(current)
        if kind!='infinite_product_convergence' or relation is None or a==b or conditions:
            raise Unsupported('The source question about two known products remains unbound')
        return dict(theorem='method.product_algebra_of_limits',operation=relation,assumption='both original partial products converge to nonzero values',
                    argument='Each original factor tends to one; for the other operations take the corresponding product of the checked partial products.'),dict(
                    implied=relation!='sum',reason='the factor tends to two' if relation=='sum' else 'limits of partial products obey the same multiplicative operation')
    if kind not in ('infinite_product_convergence','infinite_product_value') or not (
            not note or note.startswith('investigate convergence') or note.startswith('investigate absolute or conditional convergence')
            or note.startswith('investigate absolute/conditional convergence') or note.startswith('convergence and value')
            or note.startswith('Prove convergence for abs(')):
        return fallback()
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',current))-m.FUNCTIONS-set(m.ALIASES)-{name,'pi','e'})
    if task.get('parameters',names)!=names:
        raise Unsupported('The factors and fixed parameters still need exact binding')
    if (kind=='infinite_product_convergence' and len(names)==1 and not task.get('parameters') and start>=1
            and conditions==[f'abs({names[0]})<pi/4 for every n>=1',f'sum {names[0]} absolutely converges']):
        a=names[0];term=m.parse(current,name,names);u=('s',a)
        if term!=('tan',('add',('div',m.PI,q(4)),u)):
            raise Unsupported('The given absolute series does not feed the stated tangent factors')
        return dict(theorem='method.product_log_smooth_composition',term=term,argument='The factors are positive on the original interval. The log of the factor vanishes at zero and has bounded derivative in a smaller neighborhood. Absolute summability puts the tail in that neighborhood.'),dict(
                    classification='converges_nonzero',absolute=True)

    term=m.parse(current,name,names)
    if kind=='infinite_product_convergence' and library.data.get('bounded_geometric_log_products'):
        bounded=geometric_cosine_log_product(term,name,start,conditions,
                     integer_phase=library.data.get('integer_phase_product_exclusion',False),
                     moment_phase=library.data.get('geometric_phase_moment_differences',False),
                     polynomial_shift=library.data.get('integer_polynomial_shift_moment_bound',False))
        if bounded is not None:return bounded
    ctx=m.context(dict(variable=name,parameters=names,parameter_conditions=conditions))
    if (kind=='infinite_product_value' and term[0]=='rpow' and term[2][0]=='div' and term[2][2]==n and start==1
            and m.constant_defined(term[1],ctx) and m.sign(term[1],ctx)==1):
        s=integer_sign_period(term[2][1],name,start)
        if len(s)==2 and sum(s)==0:
            index=name
            eta=freeze(request('prove the alternating log coefficient sum at the Abel boundary',dict(kind='series_sum',index=index,start_index=0,
                               term=f'(-1)^{index}/({index}+1)',method_requirement='abel'))['value'])
            log=m.mul(q(s[1]),eta);base=term[1]
            limit=m.simplify(('rpow',base,log))
            if not (m.constant_defined(log,ctx) and m.constant_defined(limit,ctx)):
                raise Unsupported('The exponent sum and the product limit must be defined independently of the source index')
            return dict(theorem='method.product_log_of_fixed_power',base=base,exponent_sum=log,period=s,
                        source_conditions=conditions,argument='The finite product is a fixed positive base raised to a finite sum. Use the certified alternating series limit.'),dict(
                        classification='converges_nonzero',partial_product_limit=limit)
    if kind!='infinite_product_convergence':return fallback()
    if (term[0]=='rpow' and term[2]==('div',ONE,n) and term[1][0]=='add' and start>=1 and not conditions):
        first,second=term[1][1:]
        if first[0]=='ln' and second==('mul',q(-1),('ln',n)) and first[1][0]=='add' and n in first[1][1:]:
            h=first[1][2] if first[1][1]==n else first[1][1]
            if h[0]=='s':
                x=h[1]
                return dict(theorem='method.product_logarithm_of_small_increment',shift=h,
                            argument='При положительном сдвиге разность логарифмов эквивалентна сдвигу, делённому на индекс. Логарифм n-го корня равен (ln сдвига−ln n+O(1/n))/n, и их сумма уходит в минус бесконечность. Нулевой сдвиг даёт нулевой множитель. При отрицательном сдвиге чётные корни на хвосте не определены над вещественными.'),dict(cases=[
                            dict(condition=f'{x}>0',classification='diverges_to_zero',partial_product_limit=ZERO),
                            dict(condition=f'{x}=0',classification='converges_to_zero_by_zero_factor',partial_product_limit=ZERO),
                            dict(condition=f'{x}<0',classification='undefined_factor')])

    if term[0]=='add' and term[1]==ONE and term[2][0]=='div' and start>=1 and not conditions:
        a,b=term[2][1:]
        if (a[0]=='rpow' and a[2]==('pow',n,2) and b[0]=='rpow' and b[2]==n and b[1][0]=='s'
                and a[1][0]=='add' and a[1][1]==ONE and a[1][2][0]=='div' and a[1][2][2]==n):
            d=a[1][2][1];x=b[1][1]
            if m.constant_defined(d,ctx) and m.sign(d,ctx)==1:
                threshold=source(('exp',d));zero=f'{x}=-(1+({source(d)})/{name})^{name} at some odd integer {name}>={start}'
                return dict(theorem='method.product_exponential_root_frontier',increment=d,rate=m.div(('exp',d),b[1]),
                            remainder='n^2*log(1+d/n)=n*d-d^2/2+O(1/n)', zero_factor_condition=zero,
                            argument='The first two logarithmic orders give the strict geometric regime and a nonzero limiting perturbation on the boundary.'),dict(cases=[
                            dict(condition=f'{x}=0',classification='undefined_factor'),
                            dict(condition=zero,classification='converges_to_zero_by_zero_factor',partial_product_limit=ZERO),
                            dict(condition=f'abs({x})>{threshold}',classification='converges_nonzero',absolute=True),
                            dict(condition=f'0<abs({x})<={threshold} and no zero factor',classification='diverges_nonconvergent')])

    if term[0]=='mul' and any(t[0]=='exp' for t in term[1:]):
        plan,value=compensated_log_product(term,name,start,names,conditions)
        return dict(plan,source_conditions=conditions,argument='The solver cancels the initial logarithmic terms, proves a summable remainder, and checks early zeros.'),value
    if not conditions:
        try:plan,value=product_logarithmic_perturbation(term,name,start,ctx)
        except (Unsupported,NotRational,Undefined):pass
        else:return dict(plan,argument='Separate the eventual logarithmic tail and any exact zero factors.'),value

    if not conditions and start>=1 and (term[0]=='rpow' and (term[1]==n or term[1][0]=='rpow' and term[1][1]==n)):
        if term[1]==n and term[2][0]=='rpow':
            s=integer_sign_period(term[2],name,start)
            return dict(theorem='method.product_log_power_series',period=s,argument='The original powers of positive integers cannot tend to one.'),dict(classification='diverges_nonconvergent')
        if term[1][0]=='rpow' and term[2][0]=='div' and term[2][1]==ONE:
            s=integer_sign_period(term[1][2],name,start);p=m.num(positive_step_amplitude(term[2][2],name,start,ctx))
            if sum(s)==0 and p is not None and p>0:
                return dict(theorem='method.product_log_power_series',period=s,log_powers=q(p),
                            argument='The logarithms have zero-mean periodic signs times ln(n)/n^p, which eventually decreases to zero.'),dict(
                            classification='converges_nonzero',absolute=p>1)

    # Try to remove a positive outer power using the existing exact rational-product route.
    base=power=None
    if term[0]=='sqrt':base,power=term[1],q(1,2)
    elif term[0] in ('pow','rpow'):
        base,power=term[1],q(term[2]) if term[0]=='pow' else term[2]
    elif term[0]=='div' and term[1]==n and term[2][0]=='sqrt' and start>=1:
        base,power=('div',m.power(n,2),term[2][1]),q(1,2)
    if base is None or conditions:return fallback()
    try:B,D=rational_on_tail(base,name,start)
    except (NotRational,Undefined):return fallback()
    if any(s!=1 for _,s in integer_sign_runs(pm(B,D),start)):
        return fallback()
    plan=dict(theorem='method.positive_product_power',positive_base=base,exponent=power,
              argument='A positive base permits an exact logarithm of the power at every index.')
    if not m.contains(power,n):
        if not m.constant_defined(power,ctx):
            raise Unsupported('The original fixed exponent must be a defined real quantity')
        child=request('classify the checked rational factors before applying a fixed power',dict(kind='infinite_product_convergence',factor_or_given=source(base),index=name,start_index=start))
        c=child['value']['classification'];sign=m.sign(power,ctx)
        if c=='converges_nonzero':return plan,dict(classification=c,absolute=True)
        if c not in ('diverges_to_zero','diverges_unbounded'):
            raise Unsupported('The positive rational product has no complete limiting branch')
        change={'diverges_to_zero':'diverges_unbounded','diverges_unbounded':'diverges_to_zero'}
        def result(s):return dict(classification=c if s>0 else change[c] if s<0 else 'converges_nonzero')
        if sign is not None:return plan,result(sign)
        return plan,dict(cases=[dict(condition=source(power)+rel,**result(s)) for s,rel in ((-1,'<0'),(0,'=0'),(1,'>0'))])
    try:E,F=rational_on_tail(power,name,start)
    except (NotRational,Undefined):return fallback()
    d=len(F)-len(E);delta=pa(B,tuple(-x for x in D));same_degree=len(B)==len(D) and B[-1]==D[-1]
    ordinary=(same_degree and d+len(D)-len(delta)>1) or d>1
    if not ordinary:return fallback()
    plan.update(exponent_decay=d,log_bound='O(n^-k) when the positive base tends to one, otherwise O(log n)')
    return plan,dict(classification='converges_nonzero',absolute=True)


def abstract_series_theorem(task, library):
    """Assemble Cauchy, comparison and grouping arguments for quantified series questions."""
    data=task.get('series_statement')
    if data is None and isinstance(task.get('statement'),str) and 'арифметической прогрессии' in task['statement'] and re.fullmatch(
            r'(?:Доказать, что )?ряд чисел, обратных членам арифметической прогрессии, расходится\.?',task['statement']):
        data=dict(sequence='arithmetic_progression',operation='reciprocals',requested='prove divergence')
    if (not library.data.get('abstract_series_theorems') or set(task)-{'kind','id','source','statement','series_statement','requested_output','transcription_note'}
            or not isinstance(data,dict)):
        raise Unsupported('The original quantified series premises still need binding')

    wanted=task.get('requested_output',['proof'])
    def result(theorem,argument,outputs=(),**value):
        if wanted not in (['proof'],['proof_or_counterexample'],list(outputs)):
            raise Unsupported('An additional conclusion is not checked by this theorem')
        return dict(theorem='method.'+theorem,argument=argument,original_premises=data),value
    if data==dict(sequence='arithmetic_progression',operation='reciprocals',requested='prove divergence'):
        return result('series_nonzero_power_limit','Для ненулевой разности прогрессии n/(a+(n−1)d)→1/d. На хвосте сравниваем с гармоническим рядом с постоянным знаком. При нулевой разности ненулевые обратные члены постоянны. Если один исходный член равен нулю, соответствующее обратное число не определено.',
                      when_reciprocals_defined='diverges',otherwise='undefined_original_term')

    terms=data.get('terms',[]);a=data.get('term');out=data.get('requested');h=data.get('restriction')
    if set(data)=={'terms','restriction','domain','hypotheses_to_compare','inquire'} and len(terms)==3:
        a,c,b=terms
        if (len(set(terms))==3 and h==f'{a}<={c}<={b}' and data['domain']=='n>=1' and
                data['hypotheses_to_compare']==['both bounding series converge','both bounding series diverge'] and data['inquire']=='convergence of the middle series'):
            return result('cauchy_ordered_series','Конечный хвост среднего ряда лежит между хвостами двух других. При их сходимости оба хвоста по модулю меньше любого ε, поэтому выполняется критерий Коши.',
                          outputs=('proof','divergent_extremes_analysis'),
                          when_both_bounds_converge='converges',when_both_bounds_diverge='not_determined',
                          witnesses=dict(lower='-1/n',upper='1/n',middle_converges='0',middle_diverges='1/(2*n)'))
    question=data.get('enquire_term')
    if isinstance(question,str) and len(terms)==2 and len(set(terms))==2:
        a,b=terms
        if set(data)=={'terms','restriction','hypotheses_to_compare','enquire_term'} and h==f'{a}>=0 and {b}>=0' and data['hypotheses_to_compare']==['both series diverge']:
            if question==f'max({a},{b})':
                return result('cauchy_ordered_series','Все члены максимума не меньше членов первого неотрицательного расходящегося ряда.',outputs=('decision_with_justification',),convergence='diverges')
            if question==f'min({a},{b})':
                return result('cauchy_ordered_series','Равные гармонические ряды дают расходящийся минимум. Если поместить гармонические ряды с множителем 2 на непересекающиеся чётные и нечётные носители, минимум тождественно нулевой.',
                              outputs=('decision_with_justification',),
                              convergence='not_determined',witnesses=['equal harmonic series','even and odd harmonic subseries on disjoint supports'])
        if set(data)=={'terms','premises','enquire_term'} and question==f'{a}+{b}':
            if data['premises']==[f'sum {a} converges',f'sum {b} diverges']:
                return result('cauchy_ordered_series','Если сумма двух рядов сходится, из неё можно вычесть первый сходящийся ряд. Второй оказался бы сходящимся, вопреки исходному условию.',convergence='diverges')
            if data['premises']==[f'sum {a} diverges',f'sum {b} diverges']:
                return result('cauchy_ordered_series','Берём две копии гармонического ряда для расходимости, либо гармонический ряд и его противоположность для сходимости.',convergence='not_determined',
                              witnesses=['1/n with 1/n','1/n with -1/n'])
    if set(data)=={'term','restriction','proved_assumption','requested'} and isinstance(a,str) and h==a+'>=0' and data['proved_assumption']==f'sum {a} converges':
        if out==[f'sum {a}^2 converges','investigate converse by examples']:
            return result('square_summability','Члены сходящегося ряда стремятся к нулю, поэтому на хвосте 0≤a_n≤1. Тогда a_n²≤a_n. Обратное опровергает гармонический ряд, квадраты которого суммируются.',
                          outputs=('proof','counterexamples'),
                          square_series='converges',converse=False,witness='a_n=1/n')
    if set(data)=={'terms','premise_terms','requested_convergence'} and terms and len(set(terms))==len(terms):
        if data['premise_terms']!=[f'{t}^2' for t in terms] or any(not re.fullmatch(r'[A-Za-z_]\w*',t) for t in terms):
            raise Unsupported('The premise powers are not exactly the original independent terms squared')
        n=('v','n');inverse=('s','__reciprocal_index')
        if {'n','__reciprocal_index'}&set(terms):raise Unsupported('A fresh reciprocal-index term is required')
        atoms={('s',t):t for t in terms}|{inverse:inverse[1]};witnesses=[]
        for t in data['requested_convergence']:
            raw=m.parse(t,'n',terms)
            raw=m.substitute(raw,{('div',ONE,n):inverse})
            # Bring a numerator divided by n into a quadratic product with the reciprocal index.
            if raw[0]=='div' and raw[2]==n:raw=('mul',raw[1],inverse)
            if any(rel!='nonzero' or v!=n for rel,v in domain_conditions(raw)):
                raise Unsupported('The original target has an unbound non-index denominator')
            while raw[0]=='abs':raw=raw[1]
            magnitudes={('abs',atom):('magnitude',atom) for atom in atoms}
            p,d=m.rational_form(m.substitute(raw,magnitudes));weights={}
            coordinates=atoms|{v:atoms[k[1]] for k,v in magnitudes.items()}
            if set(d)!={()} or not d[()]:raise Unsupported('The target is not a quadratic expression')
            for mon,k in p.items():
                if sum(pow_ for _,pow_ in mon)!=2 or any(atom not in coordinates for atom,_ in mon):
                    raise Unsupported('Only homogeneous quadratic products can use the common square majorant')
                for atom,pow_ in mon:
                    v=coordinates[atom];weights[v]=weights.get(v,0)+abs(k/d[()])*Fraction(pow_,2)
            witnesses.append(dict(target=t,square_weights={v:q(w) for v,w in sorted(weights.items())}))
        if not witnesses:raise Unsupported('No target quadratic series was supplied')
        return result('square_summability','Раскрываем каждую квадратичную форму и оцениваем смешанный вклад через 2|uv|≤u²+v². Ряд обратных квадратов задаёт ещё одну суммируемую координату.',
                      outputs=('three_convergence_proofs',) if len(witnesses)==3 else (),
                      all_targets_absolutely_converge=True,majorants=witnesses)
    if isinstance(a,str) and re.fullmatch(r'[A-Za-z_]\w*',a):
        if (set(data)=={'term','known_limit','restriction','requested'} and data['known_limit']==f'lim n*{a}=a' and h=='a!=0' and out=='prove divergence'):
            return result('series_nonzero_power_limit','На хвосте знак совпадает со знаком ненулевого предела, а модуль члена не меньше |a|/(2n). Применяем гармоническое сравнение.',convergence='diverges')
        if set(data)=={'term','restriction','proved_assumption','requested'} and h=='positive nonincreasing' and data['proved_assumption']==f'sum {a} converges' and out==f'lim n*{a}=0':
            return result('cauchy_ordered_series','Для половины хвоста каждый член не меньше a_n. Поэтому n a_n ограничено удвоенным хвостом начиная с целой части n/2, который стремится к нулю.',limit=ZERO)
        if set(data)=={'term','hypothesis','inquire'} and data['inquire']==f'convergence of sum {a}' and data['hypothesis']=='lim_(n->infinity) sum_(k=1..p) a_(n+k)=0 for each fixed positive integer p' and a=='a_n':
            return result('cauchy_ordered_series','Условие при p=1 даёт стремление члена к нулю. Обратно, каждый фиксированный конечный блок тогда стремится к нулю. Полный критерий Коши требует общей оценки для блоков всех длин.',
                          outputs=('decision_with_justification',),
                          implies_convergence=False,witness='1/n')
        if set(data)=={'term','restriction','comparison_term','requested'} and h=='positive nonincreasing' and data['comparison_term']=='2^n*a_(2^n)' and out=='equivalence of convergence' and a=='a_n':
            return result('condensation_by_monotone_blocks','В блоке от 2^j до 2^(j+1)−1 ровно 2^j членов. Их сумма снизу ограничена 2^j a_(2^(j+1)), сверху 2^j a_(2^j). Сдвиг нижней оценки даёт эквивалентность сходимости.',equivalent=True)
        if (set(data)=={'term','restriction','requested'} and a=='a_n' and out=='sum_(k>=n+1) a_k<=a_n0*rho^(n-n0+1)/(1-rho) for n>=n0'
                and h=='a_n>0 and a_(n+1)/a_n<=rho<1 on n>=n0'):
            return result('geometric_tail_iteration','Из положительности и оценки отношения следует 0<ρ<1. Индукцией a_k≤a_n0 ρ^(k−n0). Суммируем мажоранту с k=n+1.',
                          bound='a_n0*rho^(n-n0+1)/(1-rho)',range='n>=n0')
        if set(data)=={'term','restriction','known_limit','requested'} and h==a+'>0' and data['known_limit']=='lim a_(n+1)/a_n=q' and a=='a_n' and out=='a_n=o(r^n) for each r>q':
            return result('geometric_tail_iteration','Выбираем ρ между q и r. Начиная с некоторого индекса a_(n+1)≤ρ a_n. После деления на r^n остаётся убывающая геометрическая оценка.',holds=True)
        if (set(data)=={'term','restriction','known_limit','requested','example_interleaved_terms'} and a=='a_n' and h=='a_n>0'
                and data['known_limit']=='limsup a_(n+1)/a_n=q<1' and out==['prove convergence','investigate converse']
                and data['example_interleaved_terms']==['1/2^k','1/3^k']):
            return result('geometric_tail_iteration','Выбираем ρ между q и 1 и сравниваем хвост с геометрической прогрессией. В печатном примере два геометрических подпотока сходятся, а отношения от чётного места к следующему нечётному неограниченны.',
                          outputs=('proof','specified_counterexample'),
                          convergence='converges',converse=False,example_limsup='+inf')
        if (set(data)=={'term','restriction','known_limit','requested','example_term'} and a=='a_n' and h=='a_n>0' and data['known_limit']=='lim a_(n+1)/a_n=q'
                and out==['lim a_n^(1/n)=q','investigate converse'] and data['example_term']=='(3+(-1)^n)/2^(n+1)'):
            return result('geometric_tail_iteration','Ограничиваем последовательные отношения числами q±ε и перемножаем. Корень степени n устраняет начальные множители. На границах q=0 или ∞ достаточно одной оценки. У печатного примера корни имеют один предел, а отношения имеют два.',
                          outputs=('proof','specified_counterexample'),
                          root_limit='q',converse=False,example_root_limit=q(1,2),example_ratio_limits=[q(1,4),ONE])
        if set(data)=={'term','restriction','known_limit','requested'} and a=='a_n' and h=='a_n>=0':
            if data['known_limit']=='limsup a_n^(1/n)=q<1' and out=='prove convergence':
                return result('geometric_tail_iteration','Выбираем r между q и 1. На хвосте a_n≤r^n, что даёт сходящуюся геометрическую мажоранту.',convergence='converges')
            if data['known_limit']=='limsup a_n^(1/n)=q>1' and out=='prove divergence':
                return result('geometric_tail_iteration','Выбираем r между 1 и q. Бесконечно много раз a_n≥r^n, поэтому члены не стремятся к нулю.',convergence='diverges')
        if (set(data)=={'term','restriction','ratio_expansion','requested'} and a=='a_n' and h=='a_n>0'
                and data['ratio_expansion']=='a_n/a_(n+1)=1+p/n+o(1/n)'
                and out==['a_n=o(n^(-p+epsilon)) for every epsilon>0','when p>0 eventually decreasing to zero']):
            return result('logarithmic_tail_rate','Логарифм отношения равен p/n+o(1/n). Суммирование логарифмов телескопируется, а остаток после любого позднего индекса ограничен ε умножить на гармоническую сумму. Получаем ln a_n=−p ln n+o(ln n). При p>0 сами отношения на хвосте больше единицы.',
                          outputs=('asymptotic_bound','eventual_monotonicity_and_limit'),
                          bound='a_n=n^(-p+o(1))',eventual_decrease_when='p>0')
        if (set(data)=={'term','restriction','sequence_test','claims'} and a=='a_n' and h=='a_n>0'
                and data['sequence_test']=='ln(1/a_n)/ln(n)' and data['claims']==['if eventually >=1+alpha, alpha>0, converges','if eventually <=1, diverges']):
            return result('logarithmic_tail_rate','Поскольку ln n>0, экспоненцирование даёт верхнюю оценку n^(−1−α) либо нижнюю 1/n. Применяем критерий степенного ряда чисел.',
                          outputs=('convergence_proof','divergence_proof'),
                          conclusion=['converges in the first case','diverges in the second case'])
        if (set(data)=={'term','restriction','sequence_test','claims'} and a=='a_n' and h=='a_n>=0'
                and data['sequence_test']=='(1-a_n^(1/n))*n/ln(n)' and data['claims']==['if eventually >=p>1, converges','if eventually <=1, diverges']):
            return result('logarithmic_tail_rate','В первой ветви a_n≤(1−p ln(n)/n)^n≤n^(−p). Во второй a_n≥(1−ln(n)/n)^n~1/n, поскольку n(ln(n)/n)² стремится к нулю.',
                          outputs=('convergence_proof','divergence_proof'),
                          conclusion=['converges in the first case','diverges in the second case'])
    if (set(data)=={'function','restriction','ratio','claims'} and data['function']=='f' and h=='positive nonincreasing' and data['ratio']=='exp(x)*f(exp(x))/f(x)'
            and data['claims']==['limit less than one implies convergence','limit greater than one implies divergence']):
        return result('condensation_by_monotone_blocks','Интегральный критерий переносит вопрос к ∫f. Замена u=e^t даёт сравнение накопленных интегралов при отношении меньше единицы. При отношении больше единицы и предположении сходимости хвост от e^x оказался бы больше хвоста от x, что противоречит положительности.',
                      outputs=('convergence_proof','divergence_proof'),
                      conclusion=['convergence if the limit is less than one','divergence if it is greater than one'])
    if (set(data)=={'terms','hypothesis','inquire','printed_examples'} and terms==['a_n','b_n'] and data['hypothesis']=='sum a_n converges and lim b_n/a_n=1'
            and data['inquire']=='convergence of sum b_n' and data['printed_examples']==['(-1)^n/sqrt(n)','(-1)^n/sqrt(n)+1/n']):
        return result('cauchy_ordered_series','Первый ряд сходится по Лейбницу. Отношение второго члена к первому равно 1+(−1)^n/√n, но их разность образует расходящийся гармонический ряд.',
                      implied=False,witnesses=dict(reference='(-1)^n/sqrt(n)',perturbation='1/n'))
    if (set(data)=={'term','assumption','positive_part_sum_limit','negative_part_sum_limit','requested'} and data==dict(term='a_n',assumption='conditional convergence',
           positive_part_sum_limit='infinity',negative_part_sum_limit='n',requested='lim N_n/P_n=1')):
        return result('cauchy_ordered_series','В буквальном условии сумма положительных частей уже бесконечна. Для знакопеременного гармонического ряда числитель каждого отношения конечен. В редакции с обоими конечными отсечениями разность стремится к сумме исходного ряда, а оба частичных итога неограниченны.',
                      printed_claim_holds=False,counterexample=dict(term='(-1)^(n+1)/n',printed_denominator='+inf',finite_numerator=True),
                      finite_cutoff_version=True)
    if (set(data)=={'term','parameter_conditions','requested'} and data==dict(term='(-1)^(n+1)/n^p',parameter_conditions=['p>0'],requested='the sum lies between 1/2 and 1')):
        return result('cauchy_ordered_series','Лейбниц даёт верхнюю строгую границу 1. Для нижней удваиваем сумму и вычитаем первый член. Получаем знакочередующийся ряд разностей n^(−p)−(n+1)^(−p). Разности положительны и убывают по выпуклости, поэтому новая сумма строго положительна.',
                      lower=q(1,2),upper=ONE,strict=True)
    if (set(data)=={'term','blocks','requested'} and data==dict(term='(-1)^(n+1)/n',blocks='p successive positive terms then q successive negative terms',requested='sum=ln(2)+ln(p/q)/2')):
        return result('condensation_by_monotone_blocks','На границах блоков после m повторений сумма равна H_(2pm)−H_(pm)/2−H_(qm)/2. Общая константа в асимптотике H_n сокращается, а неполный блок даёт исчезающий остаток.',
                      sum='ln(2)+ln(p/q)/2',block_sizes='positive integers')
    if (set(data)=={'amplitude','blocks','requested'} and data==dict(amplitude='1/n',blocks='p plus signs then q minus signs on the original consecutive indices',requested='prove convergence exactly when p=q')):
        return result('condensation_by_monotone_blocks','Разлагаем периодические знаки на постоянное среднее и периодическую часть нулевого среднего. Первая часть даёт кратный гармонический ряд. Вторая сходится по Дирихле.',
                      convergence_condition='p=q',mean_sign='(p-q)/(p+q)')
    if set(data)=={'factors','requested'} and data==dict(factors=['sum_(n>=0) 1/n!','sum_(n>=0) (-1)^n/n!'],requested='product=1'):
        return result('series_convolution_criteria','Оба ряда абсолютно сходятся. Коэффициент свёртки при общем порядке n равен (1−1)^n/n!, поэтому остаётся только постоянный член.',product=ONE)
    if set(data)=={'factors','conditions','requested'} and len(data['factors'])==2 and data['factors'][0]==data['factors'][1]:
        match=re.fullmatch(r'sum_\(n>=0\) (\w+)\^n',data['factors'][0])
        if match and data['conditions']==[f'abs({match[1]})<1'] and out==f'product=sum_(n>=0) (n+1)*{match[1]}^n':
            return result('series_convolution_criteria','Абсолютная сходимость геометрических рядов разрешает группировку по суммарному индексу. Каждое из n+1 слагаемых коэффициента равно q^n.',identity=True)
    if set(data)=={'terms','start_index','requested'} and data==dict(terms=['(-1)^(n+1)/sqrt(n)']*2,start_index=1,requested='prove Cauchy-product divergence'):
        return result('series_convolution_criteria','После выделения общего знака свёртка содержит n−1 положительное слагаемое. Для каждого k выражение √(k(n−k))≤n/2, поэтому модуль свёртки не меньше 2(n−1)/n.',
                      convergence='diverges',term_lower_bound='2*(n-1)/n')
    if (set(data)=={'terms','conditions','start_index','requested'} and data==dict(terms=['(-1)^(n-1)/n^alpha','(-1)^(n-1)/n^beta'],conditions=['alpha>0','beta>0'],
            start_index=1,requested='Cauchy product converges if alpha+beta>1 and diverges if alpha+beta<1')):
        return result('series_convolution_criteria','Модуль свёртки делим посередине. В каждой половине прежние члены убывают с ростом индекса, а сумма вновь добавленных членов конечна при α+β>1. Их суммируемый хвост и нулевой предел каждого фиксированного члена дают нулевой предел модуля. Суммируемые приращения и убывания дают конечную вариацию, поэтому чередование сходится. При α+β<1 центральная треть даёт нижнюю оценку порядка n^(1−α−β).',
                      convergence_when='alpha+beta>1',divergence_when='alpha+beta<1')
    raise Unsupported('The premises do not bind a supported comparison, geometric tail or convolution rule')


def cauchy_series_certificate(task, library):
    """Prove an estimate for arbitrary finite tails, or exhibit blocks bounded away from zero."""
    from verify import same_value

    fields={'kind','id','source','source_hint','requested_output','term','index','start_index','index_domain','parameters','stated_conditions','method_requirement'}
    n=task['index'];i=('v',n);start=task['start_index'];params=task.get('parameters',[]);facts=task.get('stated_conditions',[])
    if (not library.data.get('explicit_cauchy_series') or set(task)-fields or task.get('method_requirement')!='cauchy_tail_criterion'
            or task.get('requested_output',['convergence_classification','justification'])!=['convergence_classification','justification']
            or type(start)!=int or start<0 or task.get('index_domain','integers')!='integers'):
        raise Unsupported('The Cauchy criterion requires fully bound original integer tails')
    text=task['term'];plan=dict(theorem='method.explicit_cauchy_series_tails',index=n,original_start=start,method='cauchy_tail_criterion')
    def classification(converges, absolute=None):
        return dict(classification='convergent' if converges else 'divergent',criterion='cauchy_tail_criterion',
                    absolute_convergence=absolute if converges else False,
                    conditional_convergence=None if converges and absolute is None else converges and not absolute)
    if facts:
        match=re.fullmatch(r'(\w+)\('+re.escape(n)+r'\)/(\d+)\^'+re.escape(n),text)
        if not match or int(match[2])<2 or params!=[match[1]]:
            raise Unsupported('The original bounded coefficient cannot be identified')
        a,B=match.groups();fact=re.fullmatch(r'abs\('+re.escape(a)+r'\('+re.escape(n)+r'\)\)<(\d+) for every '+re.escape(n),facts[0])
        if len(facts)!=1 or not fact:
            raise Unsupported('A uniform bound for every coefficient is required')
        return dict(plan,argument='Модуль произвольного конечного хвоста ограничен полным хвостом геометрической мажоранты.',bound=f'{fact[1]}*{B}^(-N)/(1-1/{B})'),classification(True,True)
    pattern=re.fullmatch(r'piecewise\(1/'+re.escape(n)+r' if '+re.escape(n)+r'%(\d+)!=0, -1/'+re.escape(n)+r' if '+re.escape(n)+r'%\1==0\)',text)
    if pattern and not params and start>=1:
        period=int(pattern[1])
        if period<=2:raise Unsupported('The periodic weight does not have positive mean under the source hypotheses')
        mean=Fraction(period-2,period)
        return dict(plan,argument='Вычитаем среднее периодических знаков. Остаток имеет ограниченные частичные суммы и вклад O(1/N) на блоке. Средняя часть на блоке [N,2N) остаётся отделённой от нуля.',
                    period=period,mean=q(mean),test_block='N..2*N-1'),classification(False)
    if start<1:raise Unsupported('The original reciprocal domain begins at a positive integer')
    raw=m.parse(text,n,params);ctx=m.context(dict(variable=n,parameters=params))
    if raw[0]!='div':raise Unsupported('No checked reciprocal tail estimate applies')
    a,b=raw[1:]
    if b==i and a[0]=='add' and a[2][0]=='mul' and a[2][1]==q(-1):
        bounded=a[1];shifted=a[2][2]
        if (bounded[0] in ('sin','cos') and not domain_conditions(bounded) and
                same_value(m.substitute(bounded,{i:m.add(i,ONE)}),shifted)):
            return dict(plan,argument='Суммируем конечное разностное выражение по частям. Два края и разности весов 1/n дают общую оценку 2/N, не зависящую от второго конца.',
                        bounded_sequence=bounded,bound='2/N'),classification(True)
    if a[0] in ('sin','cos'):
        g=a[1];is_fixed_power=g[0]=='rpow' and g[2]==i and m.constant_defined(g[1],ctx)
        if (is_fixed_power or not domain_conditions(g)) and (decay:=m.num(positive_step_amplitude(b,n,start,ctx))) is not None and decay>=2:
            return dict(plan,argument='Тригонометрический числитель ограничен единицей. Для любого верхнего конца хвост ограничен телескопической суммой 1/[n(n−1)] и потому не превосходит 1/(N−1).',
                        bound='1/(N-1)',valid_from=2),classification(True,True)
    if a==ONE and not params:
        if b==i:scale=ONE
        elif b[0]=='sqrt':
            p,d=rational_on_tail(b[1],n,start)
            if d!=(1,) or len(p)>3 or any(s!=1 for _,s in integer_sign_runs(p,start)):
                raise Unsupported('A positive quadratic bound on the original radical is missing')
            scale=('sqrt',q(sum(map(abs,p))))
        else:raise Unsupported('No common harmonic lower bound has been proved')
        return dict(plan,argument='На блоке из N индексов от N до 2N−1 каждый знаменатель не больше постоянной, умноженной на 2N. Поэтому хвост не может стать сколь угодно малым.',
                    test_block='N..2*N-1',lower_bound=m.div(ONE,m.mul(q(2),scale))),classification(False)
    raise Unsupported('The finite tail of this term has no checked common envelope')


def sufficient_series_prefix(task, library):
    """Find a sufficient cutoff by exact bounds on geometric, alternating or oscillatory tails."""
    from math import ceil,factorial,isqrt,prod

    fields={'kind','id','source','term','index','start_index','error_tolerance','tolerance','requested_output'}
    terms=task['term'];name=task['index'];n=('v',name);start=task['start_index'];kind=task['kind']
    if (not library.data.get('certified_series_prefix') or set(task)-fields or type(start)!=int or not 1<=start<=32
            or task.get('requested_output',['sufficient_term_count','proof_of_error_bound'])!=['sufficient_term_count','proof_of_error_bound']):
        raise Unsupported('A sufficient, certified finite cutoff on the original tail is required')
    tolerance=m.parse(task.get('error_tolerance',task.get('tolerance')),None)
    if not m.constant_defined(tolerance,m.context(dict(variable=name))):raise Unsupported('The printed tolerance is undefined')
    tol=m.num(m.simplify(tolerance))
    if tol is None or tol<=0:raise Unsupported('A strictly positive rational error tolerance is required')
    if kind=='series_tail_accuracy':
        token=re.escape(name)
        match=re.fullmatch(r'double_factorial\((\d+)\*'+token+r'\)\^(\d+)/double_factorial\((\d+)\*'+token+r'\)',terms)
        if not match:raise Unsupported('Unbound original factorial recurrence')
        step,power,den=map(int,match.groups())
        if step%2 or not 2<=step<=10 or not 2<=power<=6 or den!=step*power:raise Unsupported('The even factorial weights do not match')
        step//=2
        def ratio(j):
            return prod(Fraction(step*j+s,power*(step*j+s)-d) for s in range(1,step+1) for d in range(power))
        value=Fraction(factorial(step*start)**power,factorial(den*start//2));ratio_data=None
        for end in range(start,start+512):
            value*=ratio(end);r=ratio(end+1);upper=value/(1-r)
            if upper<tol:ratio_data=(end,r,upper);break
        if ratio_data is None:raise Unsupported('The exact sufficient factorial-tail cutoff remains open')
        end,r,upper=ratio_data
        return dict(theorem='method.geometric_tail_iteration',argument='Отношение выводится из исходных факториалов. Каждый множитель отношения убывает, поэтому первый коэффициент и проверенное отношение дают геометрическую границу остатка.',
                    first_omitted=q(value),upper_ratio=q(r),cutoff=end),dict(sufficient_terms=end-start+1,upper_error=q(upper))
    raw=m.parse(terms,name)
    if raw[0]!='div' or raw[2][0]!='sqrt':raise Unsupported('No verified decreasing radical tail amplitude')
    phase,denom=raw[1],raw[2][1];p,d=rational_on_tail(denom,name,start)
    if d!=(1,) or any(x<0 for x in p) or len(p) not in (2,3) or not p[-1]:
        raise Unsupported('The original radical denominator is not a growing positive polynomial')
    if phase[0]=='sin':
        a,b=rational_on_tail(phase[1],name,start)
        if len(a)!=2 or len(b)!=1 or not b[0] or not 0<abs(a[1]/b[0])<=2:
            raise Unsupported('No positive sine lower bound for the original frequency')
        s=a[1]/b[0]
        y=abs(s)/2;sine=y-y**3/6
    else:
        period=integer_sign_period(phase,name,start)
        if len(period)!=2 or sum(period):raise Unsupported('Strict alternating signs are required for the Leibniz error')
        sine=Fraction(1)
    minimum=1/(p[-1]*(sine*tol)**2)
    # The conservative integer power bound also covers thresholds below the initial index.
    end=max(start,ceil(minimum) if len(p)==2 else isqrt(minimum.numerator//minimum.denominator))
    while p[-1]*(end+1)**(len(p)-1)*(sine*tol)**2<=1:end+=1
    return dict(theorem='method.oscillatory_series_error',argument='Радикальный вес убывает. Оцениваем хвост Лейбницем или суммированием по частям с общей границей тригонометрических сумм.',
                sine_lower_bound=q(sine),cutoff=end,verified_strict_inequality=q(p[-1]*(end+1)**(len(p)-1)*(sine*tol)**2)),dict(
                sufficient_terms=end-start+1,error_less_than=q(tol))


def analytic_series_receipt(theorem,value,*arguments,**evidence):
    return dict(theorem='method.'+theorem,argument=list(arguments),**evidence),value


def lift_affine_factorial_value(task,lib):
    """Build a generating coordinate for a numerical factorial sum, then evaluate it."""
    from derivative_proofs import table
    from operations import expression_positions
    from tasks import source
    index=task['index'];n=('v',index);text=task['term']
    names=set(re.findall(r'\b[A-Za-z_]\w*',text))-{index,'factorial','e','pi'}-m.FUNCTIONS
    if names or task.get('parameters') or task.get('stated_conditions') or 'factorial' not in text:
        raise Unsupported('Need an independently numerical factorial series')
    raw=m.parse(text,index,extra_functions=('factorial',))
    if raw[0]!='div' or raw[2][0]!='factorial':raise Unsupported('No factorial coefficient to lift')
    var='seriesCoordinate'
    while var in (index,*names):var+='_'
    lifted=dict(kind='series_sum',term=f'({source(raw[1])})*{var}^{index}/factorial({source(raw[2][1])})',
                index=index,start_index=task['start_index'],parameters=[var])
    plan,formula=affine_factorial_series(lifted,lib)
    ctx=m.context(dict(variable=var));v=('v',var)
    rate=m.num(m.simplify(m.substitute(m.parse(formula['series_coordinate'],var),{v:ONE})))
    if not rate:raise Unsupported('The lifted point needs a nonzero checked series coordinate')
    stride=plan['factorial_stride'];sign=1 if rate>0 else -1
    u=m.mul(q(sign),m.power(v,stride))
    if stride==1:kernel=('exp',u)
    elif plan['factorial_first']%2==0:kernel=('cosh' if sign>0 else 'cos',v)
    else:kernel=m.div(('sinh' if sign>0 else 'sin',v),v)
    for row in formula['omitted_initial_kernel_terms']:
        kernel=m.add(kernel,m.neg(m.mul(row['coefficient'],m.power(u,row['power']))))
    kernel=m.div(kernel,m.power(u,formula['divide_kernel_by_power']))
    z=q(abs(rate)) if stride==1 else ('sqrt',q(abs(rate)))
    value=ZERO;trees=[];coeffs=formula['euler_operator_coefficients']
    for j,c in enumerate(coeffs):
        value=m.add(value,m.mul(c,kernel))
        if j+1<len(coeffs):
            df,tree=table(kernel,var,lib);trees.extend(tree)
            kernel=m.mul(m.div(v,q(stride)),df)
    pref=m.simplify(m.substitute(m.parse(formula['prefactor'],var),{v:ONE}))
    rawvalue=m.substitute(m.mul(pref,value),{v:z})
    if not m.constant_defined(rawvalue,ctx):raise Unsupported('The lifted sum is not defined at the proposed evaluation point')
    return analytic_series_receipt('analytic_lift_of_numeric_factorial_series',m.simplify(rawvalue),
                'Ввести независимую степенную координату, равную единице в исходной сумме. Аффинный шаг факториала определяет экспоненциальный ряд или его чётную либо нечётную часть.',
                'Многочлен веса переносится в оператор Эйлера. Почленное действие допустимо благодаря бесконечному радиусу. Дифференцировать проверенную элементарную функцию и подставить исходную точку.',
                original_term=raw,lifted_goal=lifted,verified_coefficient_reduction=plan,operator_steps=trees,evaluation=z)


def harmonic_simple_poles(task,raw,names):
    """Derive a boundary value from the shifted harmonic primitives of the rational coefficient."""
    from graphs import peval,rational_roots
    from integrals import affine
    from tasks import known_guard,source
    index=task['index'];start=task['start_index'];n=('v',index);ctx=m.context(dict(variable=index,parameters=names))
    if raw[0]!='div' or not names:raise Unsupported('Need a separated real harmonic coefficient')
    weight=[];wave=None;shift=0;sign=1

    def extract(e):
        nonlocal wave,shift,sign
        if e[0]=='mul':
            extract(e[1]);extract(e[2]);return
        if e[0] in ('sin','cos') and wave is None:
            wave=e;return
        if e[0]=='rpow' and e[1]==q(-1):
            slope,offset=map(m.num,affine(e[2],index))
            if (None in (slope,offset) or slope.denominator!=1 or offset.denominator!=1 or domain_conditions(e[2])):
                raise Unsupported('The signed harmonic factor must have an exact integer phase')
            shift=(shift+int(slope))%2;sign*=(-1)**(int(offset)%2);return
        weight.append(e)

    extract(raw[1])
    if wave is None:raise Unsupported('No trigonometric mode in the source numerator')
    angle=wave[1]
    if any(not known_guard(g,ctx) for g in domain_conditions(angle)):raise Unsupported('An original harmonic phase is undefined')
    slope,offset=affine(angle,index)
    if not all(m.constant_defined(e,ctx) for e in (slope,offset)):raise Unsupported('The index phase must be affine')
    coef=ONE
    for e in weight:coef=('mul',coef,e)
    p,d=rational_on_tail(('div',coef,raw[2]),index,start)
    if not any(p) or len(d)-len(p)<2:raise Unsupported('An absolute boundary majorant is required')
    roots=rational_roots(d)
    if len(roots)!=len(d)-1 or any(r.b or r.a.denominator!=1 or r.a>=start for r in roots):
        raise Unsupported('Need distinct integer poles strictly before the original starting index')
    derivative=[j*c for j,c in enumerate(d) if j]
    residues=[(int(r.a),peval(p,r.a)/peval(derivative,r.a)) for r in roots]
    if sum(c for _,c in residues)!=0 or any(start-r>64 or abs(r)>64 for r,_ in residues):
        raise Unsupported('A cancellation at the common logarithmic singularity is not established')
    def prefix(m):
        return '+'.join(f'z^{j}/{j}' for j in range(1,m)) or '0'
    terms=[f'({c})*z^{r}*(-ln(1-z)-({prefix(start-r)}))' for r,c in residues]
    endpoint=-sum(c*sum(Fraction(1,j) for j in range(1,start-r)) for r,c in residues)
    phase=m.add(slope,m.mul(q(shift),m.PI));projection='Re' if wave[0]=='cos' else 'Im'
    factor=f'{sign}*exp(i*({source(offset)}))'
    return analytic_series_receipt('shifted_harmonic_simple_pole_sum',
                dict(phase_coordinate=f'z=exp(i*({source(phase)}))',nonresonant_sum=f'{projection}({factor}*({"+".join(terms)}))',
                     resonant_sum=m.mul(q(sign*endpoint),(wave[0],offset)),convergence_domain='all admitted real phases'),
                'Разложить рациональный вес по простым целым полюсам. Каждый сдвиг даёт логарифмический ряд с точно вычтенными начальными членами.',
                'На окружности абсолютная мажоранта исходного веса даёт радиальный переход. Применить вещественную или мнимую часть к нужной гармонике.',
                'В резонансной точке общая логарифмическая сингулярность сокращается, поскольку сумма вычетов равна нулю. Остаются конечные гармонические поправки.',
                original_term=raw,residues=[(r,q(c)) for r,c in residues],first_index=start,original_geometric_phase=phase)


def inverse_central_coefficients(task,raw,names):
    from tasks import known_guard,source
    index=task['index'];start=task['start_index'];n=('v',index)
    if (raw[0]!='div' or raw[1][0]!='mul' or raw[2][0]!='factorial'
            or m.simplify(raw[2][1])!=m.mul(q(2),n) or not names):
        raise Unsupported('Need reciprocal central factorial coefficients')
    a,b=raw[1][1:]
    if a[0]=='rpow':a,b=b,a
    if a[0]!='pow' or a[2]!=2 or a[1][0]!='factorial' or b[0]!='rpow':
        raise Unsupported('Need a squared factorial weight and an independent power coordinate')
    offset=m.num(m.add(a[1][1],m.neg(n)))
    ds=rf(b[2],index)
    if offset not in (-1,0) or start!=int(-offset) or ds[0] not in ((0,1),(0,2)) or ds[1]!=(1,) or domain_conditions(b[2]):
        raise Unsupported('The origin of the analytic coefficient sequence or its index stride differs')
    ctx=m.context(dict(variable=index,parameters=names))
    base=b[1]
    if m.variable_in(base) or not m.constant_defined(base,ctx) or any(not known_guard(g,ctx) for g in domain_conditions(base)):
        raise Unsupported('The original power coordinate carries an unresolved domain')
    u=m.div(m.power(base,int(ds[0][1])),q(4));z=source(u)
    if offset==-1:
        positive=f'2*asin(sqrt({z}))^2'
        negative=f'-2*asinh(sqrt(-({z})))^2'
        boundary='absolute at |u|=1'
    else:
        positive=f'1/(1-({z}))+sqrt({z})*asin(sqrt({z}))/(1-({z}))^(3/2)'
        negative=f'1/(1-({z}))-sqrt(-({z}))*asinh(sqrt(-({z})))/(1-({z}))^(3/2)'
        boundary='divergent at |u|=1'
    return analytic_series_receipt('inverse_central_coefficients_from_second_order_equation',
                dict(power_coordinate=z,sum_when_coordinate_nonnegative=positive,sum_when_coordinate_negative=negative,
                     convergence_domain='|u|<=1' if offset==-1 else '|u|<1',boundary=boundary,at_zero=ZERO if offset==-1 else ONE),
                'Рассмотреть квадрат обратного синуса. Его вторая производная удовлетворяет уравнению (1−x²)y″−xy′=2, а начальные значения функции и первой производной нулевые.',
                'Сопоставить коэффициенты уравнения. Отношение соседних ненулевых коэффициентов совпадает с исходным факториальным отношением после извлечения степенной координаты.',
                'В случае веса n!² применить оператор u∂u дважды и вернуть нулевой член. При отрицательном u та же вещественная рекурсия выражается квадратом обратного гиперболического синуса.',
                'Оценка центрального коэффициента Стирлинга проверяет обе границы и область, где общий член не стремится к нулю.',
                source_term=raw,factorial_offset=int(offset),coordinate=u,initial_analytic_coefficient=ONE)


def product_term_telescoping(task):
    from integrals import affine
    from tasks import source
    index=task['index'];n=('v',index);text=task['term'];start=task['start_index']
    match=re.fullmatch(r'(?:factorial\('+re.escape(index)+r'\)/)?prod\((\w+)=1\.\.'+
                       re.escape(index)+r',(.+)\)',text)
    if not match or start!=1 or match[1]==index:raise Unsupported('Need the original finite product from the first index')
    j,body=match.groups()
    if text.startswith('factorial('):
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',body))-{j,index}-m.FUNCTIONS)
        if len(names)!=1 or task.get('parameters',names)!=names or task.get('stated_conditions'):
            raise Unsupported('A single affine product offset is needed')
        ctx=m.context(dict(variable=j,parameters=names))
        factor=m.parse(body,j,names);s,x=affine(factor,j)
        if s!=ONE or not m.constant_defined(x,ctx) or domain_conditions(factor):
            raise Unsupported('The product factor must be defined and increase with unit step')
        z=source(x)
        return analytic_series_receipt('affine_multiplier_for_product_tail',
                   dict(sum=m.div(ONE,m.add(x,q(-1))),convergence_domain=z+'>1',excluded_original_offsets='negative integers'),
                   'Вычислить точное отношение соседних членов u_(n+1)/u_n=(n+1)/(n+1+x). Ищем линейный множитель q(n) из условия q(n)u_n−q(n+1)u_(n+1)=u_n.',
                   'Сопоставление коэффициентов даёт q(n)=(n+x)/(x−1). Сумма логарифмов исходных множителей доказывает |u_n|~C n^(−x) вне исходных полюсов и постоянство знака хвоста.',
                   'При x>1 остаток q(n)u_n стремится к нулю. При x≤1 исходный определённый ряд расходится по сравнению со степенным.',
                   affine_offset=x,multiplier=f'({index}+{z})/({z}-1)',product_index=j)
    a=re.fullmatch(r'(\w+)_'+re.escape(j)+r'/\(\1_\('+re.escape(j)+r'\+1\)\+(\w+)\)',body)
    if not a:raise Unsupported('The consecutive product needs a positive shifted sequence')
    seq,x=a.groups()
    if (len({seq,x,index,j})!=4 or task.get('parameters') not in (None,[x]) or task.get('stated_conditions')!=[
            f'{x}>0',f'{seq}_{index}>0 ({index}>=1)',f'sum({index}>=1,1/{seq}_{index}) diverges']):
        raise Unsupported('All required positivity and divergent reciprocal assumptions must be supplied')
    return analytic_series_receipt('difference_of_offset_positive_products',
                dict(sum=m.div(('s',seq+'_1'),('s',x)),converges=True),
                'Сдвинуть произведение так, чтобы каждый множитель имел вид a_j/(a_j+x), начиная с j=2. Соседние частичные произведения различаются на исходный член, умноженный на x/a₁.',
                'Логарифм обратного множителя ограничен снизу min(x/(2a_j),ln 2). Расходящаяся сумма 1/a_j заставляет сумму логарифмов расходиться, поэтому сдвинутое произведение стремится к нулю.',
                'Разность соседних произведений телескопируется, а начальное пустое произведение равно единице.',
                source_sequence=seq,product_index=j,positive_offset=x)


def analytic_coefficient_reduction(task,lib,request):
    if not lib.data.get('analytic_coefficient_reductions') or generating_series_source(task) is not None:
        raise Unsupported('Need an admitted analytic summation without additional printed method')
    index=task['index'];text=task['term']
    if 'prod(' in text:return product_term_telescoping(task)
    if task.get('stated_conditions'):raise Unsupported('An extra source condition remains')
    try:return lift_affine_factorial_value(task,lib)
    except Unsupported:pass
    names=sorted(set(re.findall(r'\b[A-Za-z_]\w*',text))-{index,'factorial','e','pi'}-m.FUNCTIONS)
    if not names or task.get('parameters',names)!=names:raise Unsupported('The analytic coordinate is not bound')
    raw=m.parse(text,index,names,('factorial',))
    if 'factorial(' in text:return inverse_central_coefficients(task,raw,names)
    return harmonic_simple_poles(task,raw,names)


def balanced_product_blocks(text,index,start,parameters):
    """Recover repeating ordered factor classes and verify cancellation at first order."""
    from tasks import source
    if start!=1 or not text.endswith('...'):raise Unsupported('The original factor prefix and start must be preserved')
    step=re.compile(r'\(1([+-])1/(?:sqrt\((\d+)\)|(\d+)\^([A-Za-z_]\w*))\)(?:\^(\d+))?')
    prefix=text[:-3].replace(' ','')
    matches=list(step.finditer(prefix))
    separations=[prefix[a.end():b.start()] for a,b in zip(matches,matches[1:])]
    if not matches or matches[0].start() or any(s not in ('','*') for s in separations) or prefix[matches[-1].end():] not in ('','*'):
        raise Unsupported('Need a complete prefix of signed reciprocal-power factors')
    rows=[(1 if a=='+' else -1,int(b or c),q(1,2) if b else ('s',d),int(e or 1))
          for a,b,c,d,e in (x.groups() for x in matches)]
    p=rows[0][2]
    expected=[p[1]] if p[0]=='s' else []
    if index in expected or parameters not in (None,expected) or any(
            row[2]!=p or row[1]<1 or row[3]<1 or row[0]<0 and row[1]<=1 for row in rows):
        raise Unsupported('A separate exponent, initial zero, or nonpositive multiplicity changes the product')
    for length in range(1,len(rows)//2+1):
        blocks=[]
        for j in range(length):
            c,first,_,count=rows[j];stride=rows[j+length][1]-first
            seq=rows[j::length]
            if stride<=0 or any((a,b,m)!=(c,first+k*stride,count) for k,(a,b,_,m) in enumerate(seq)):break
            blocks.append((c,first,stride,count))
        else:break
    else:raise Unsupported('No consistent periodic block order has two confirmed starts per class')
    totals={}
    for sign,_,stride,count in blocks:totals[stride]=totals.get(stride,0)+sign*count
    if p[0]=='q':
        lead=ZERO
        for stride,c in totals.items():lead=m.add(lead,m.div(q(c),('sqrt',q(stride))))
        ctx=m.context(dict(variable=index))
        if m.sign(lead,ctx)!=0:raise Unsupported('The leading logarithmic increments do not cancel')
        cls=dict(classification='converges_nonzero' if m.num(p)>Fraction(1,2) else 'diverges_to_zero',
                 absolute=m.num(p)>1,conditional=Fraction(1,2)<m.num(p)<=1)
    else:
        if any(totals.values()) or any(c<0 and count%2 for c,_,_,count in blocks):
            raise Unsupported('Parameter-dependent cancellation or an unproved sign needs more branches')
        power=source(p)
        cls=dict(classification='by_parameter',branches=[
            dict(condition=f'{power}<0',classification='diverges_to_infinity'),
            dict(condition=f'{power}=0',classification='converges_to_zero',zero_factor=True),
            dict(condition=f'0<{power}<=1/2',classification='diverges_to_zero'),
            dict(condition=f'1/2<{power}<=1',classification='converges_nonzero',conditional=True),
            dict(condition=f'{power}>1',classification='converges_nonzero',absolute=True)])
    return analytic_series_receipt('balanced_logarithmic_product_blocks',cls,
                'Восстановить повторяющиеся позиции из полного напечатанного префикса. В каждой позиции знаменатели образуют свою арифметическую прогрессию.',
                'После логарифмирования первый порядок блока сокращается. Ошибка линейного сравнения O(k⁻ᵖ⁻¹) суммируема при p>0, суммарный квадратичный член отрицателен и имеет порядок k⁻²ᵖ.',
                'Каждый исходный фактор стремится к единице, поэтому незаконченный блок сохраняет классификацию. Абсолютная сходимость исходных факторов требует p>1.',
                'Нулевая и отрицательная степенные ветви проверяются по исходным множителям до логарифмирования.',
                inferred_period=length,ordered_block_factors=blocks,leading_totals_by_stride=sorted(totals.items()),power=p)


def analytic_product_reduction(task,lib,request):
    from ordinary_series import constant_sign
    from tasks import known_guard,source
    from verify import same_value
    origin=task.get('source',{});kind=task['kind'];text=task['factor_or_given'];index=task['index'];start=task['start_index']
    if (set(task)-{'kind','id','source','factor_or_given','index','start_index','parameters','stated_conditions','method_requirement','claimed_value'}
            or not isinstance(origin,dict) or set(origin)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
            or not isinstance(index,str) or not index.isidentifier() or type(start) is not int or start<1
            or not isinstance(text,str) or task.get('stated_conditions') or task.get('method_requirement')):
        raise Unsupported('Unbound source hypotheses or product method')
    label=origin.get('literal_requirement');n=('v',index)
    if kind=='infinite_product_convergence':
        if task.get('claimed_value'):raise Unsupported('This method does not calculate a claimed product value')
        if label in ('investigate absolute or conditional convergence in printed order','investigate absolute or conditional convergence'):
            return balanced_product_blocks(text,index,start,task.get('parameters'))
        if label not in (None,'investigate convergence'):raise Unsupported('Missing original convergence scope')
        names=sorted(set(re.findall(r'\b[A-Za-z_]\w*',text))-{index,'pi','e'}-m.FUNCTIONS)
        if task.get('parameters',names)!=names or not names:raise Unsupported('The real parameters are not bound')
        ctx=m.context(dict(variable=index,parameters=names));raw=m.parse(text,index,names)
        if raw[0]!='rpow' or m.variable_in(raw[2]) or not m.constant_defined(raw[2],ctx) or raw[1][0]!='div':
            raise Unsupported('This route requires a fixed real power of a sinc factor')
        base=raw[1];angle=base[2]
        if (base[1]!=('sin',angle) or angle[0]!='div' or angle[2]!=n or
                not m.constant_defined(angle[1],ctx) or domain_conditions(angle[1])):
            raise Unsupported('The same independently defined argument must occur in the numerator and denominator')
        z=source(angle[1]);cutoff=f'max({start}, floor(abs({z})/pi)+1)'
        return analytic_series_receipt('sinc_log_tail_and_finite_source_domain',
                    dict(classification='by_original_factor_domains',branches=[
                        dict(condition=f'{z}=0 or an initial printed power is undefined',classification='undefined'),
                        dict(condition=f'{z}!=0, all printed powers defined, and an initial factor is zero',classification='converges_to_zero'),
                        dict(condition=f'{z}!=0 and all initial factors are defined and nonzero',classification='converges_nonzero',
                             absolute=True)],initial_domain_check_ends_before=cutoff),
                    'Сохраняем исходное исключение нулевого аргумента. После указанного порога |x/n|<π, отношение синуса к аргументу строго положительно.',
                    'Логарифм исходной фиксированной степени на хвосте имеет порядок n⁻², поэтому хвост сходится абсолютно к ненулевому пределу.',
                    'Проверяем все предшествующие факторы как исходные вещественные степени. Неопределённость исключает весь продукт. Определённый нулевой фактор даёт сходимость к нулю по напечатанной конвенции.',
                    original_factor=raw,tail_begins_at=cutoff)
    if kind!='infinite_product_identity' or start!=1 or task.get('parameters'):
        raise Unsupported('An exact starting index and claimed product identity are required')
    claim=re.fullmatch(r'Доказать равенство =(.+)\.',label or '')
    goal=claim[1] if claim else task.get('claimed_value')
    if not goal or task.get('claimed_value') not in (None,goal):
        raise Unsupported('The original right-hand side is not bound')
    ctx=m.context(dict(variable=index));target=m.parse(goal,None)
    if not m.constant_defined(target,ctx):raise Unsupported('The claimed product value is undefined')
    r=re.fullmatch(r'2/(\w+)_'+re.escape(index)+r' where \1_1=(.+), \1_\('+
                   re.escape(index)+r'\+1\)=sqrt\(2\+\1_'+re.escape(index)+r'\)',text)
    if r:
        base=m.parse(r[2],None,());theta=m.simplify(('acos',m.div(base,q(2))))
        if not m.constant_defined(base,ctx) or constant_sign(base,ctx)!=1 or constant_sign(m.add(q(2),m.neg(base)),ctx)!=1:
            raise Unsupported('The initial positive branch must lie strictly below two')
        if theta[0]=='acos':
            for f in (Fraction(1,6),Fraction(1,4),Fraction(1,3)):
                ang=m.mul(q(f),m.PI)
                if same_value(('cos',ang),m.div(base,q(2))):
                    theta=ang;break
        value=m.div(m.mul(q(2),theta),('sin',m.mul(q(2),theta)))
        if not same_value(value,target):raise Unsupported('The derived radical product differs from the claimed value')
        return analytic_series_receipt('half_angle_nested_radical_product',m.simplify(value),
                    'Предложить угол θ=arccos(r₁/2). Формула половинного угла с положительным корнем доказывает r_n=2cos(θ/2^(n−1)).',
                    'Переписать каждый обратный множитель как секанс. Формула двойного угла телескопирует конечное произведение, а замечательный предел даёт 2θ/sin(2θ).',
                    verified_initial_angle=theta,source_recurrence=text)
    raw=m.parse(text,index)
    a,b=rational_on_tail(raw,index,start)
    if (len(a)!=3 or len(b)!=3 or a[0] or a[1] or b[1] or a[2]!=b[2] or b[0]/b[2]>=0):
        raise Unsupported('No normalized Euler sine product factor')
    square=-b[0]/b[2];root=m.simplify(('sqrt',q(square)));theta=m.mul(m.PI,root)
    if not 0<square<1 or m.sign(('sin',theta),ctx)!=1:
        raise Unsupported('The inverted sine product must have a nonzero limit and no zero factor')
    value=m.div(theta,('sin',theta))
    if not same_value(value,target):raise Unsupported('The exact computed product differs from the claimed value')
    return analytic_series_receipt('reciprocal_euler_sine_product',m.simplify(value),
                'На исходной области рациональный множитель равен обратному к 1−(θ/(πn))². Все такие делители строго положительны.',
                'Подставить проверенный угол в разложение Эйлера для sin θ/θ. Его предел ненулевой, поэтому обратный переход допустим.',
                factor=raw,generated_angle=theta,verified_coordinate_square=q(square))


COEFFICIENT_TRANSPORT_KINDS={'series_coefficient_recurrence','analyticity_theorem','abel_converse_positive_coefficients'}


def coefficient_transport_routing(task,kind):
    if kind in COEFFICIENT_TRANSPORT_KINDS:return True
    if kind=='sum_of_power_series_by_method':
        return task.get('method_requirement')=='termwise_differentiation' and 'coefficient_term' in task
    if kind!='infinite_power_series_expansion':return False
    f=task.get('function');name=task.get('series_variable');method=task.get('method_requirement');conditions=task.get('printed_conditions',[])
    keys={'kind','id','source','function','series_variable','variable','center','requested_output','printed_conditions','parameters','method_requirement'}
    if not isinstance(f,str) or not isinstance(name,str) or not name.isidentifier() or set(task)-keys or task.get('center','0')!='0':
        return False
    x=re.escape(name);f=f.replace(' ','')
    if method=='algebra_of_power_series' and not conditions:
        return f==f'(asin({name})/{name})^2' or bool(re.fullmatch(r'[^/]+\*cosh\(sqrt\((?:[1-9]\d*\*)?'+x+r'\)\)',f))
    if method is None:
        if conditions==[name+'>0']:
            return bool(re.fullmatch(r'[A-Za-z_]\w*\^'+x,f))
        if conditions==[f'abs({name})<1']:
            return bool(re.fullmatch(r'1/sqrt\(1-2\*[A-Za-z_]\w*\*'+x+r'\+'+x+r'\^2\)',f))
        if not conditions:
            return bool(re.fullmatch(r'(?:sin|cos)\([A-Za-z_]\w*\*asin\('+x+r'\)\)',f))
    return False


def transport_expansion(task,lib,request):
    from integrals import affine
    from tasks import known_guard,power_series_headings,source
    from verify import same_value
    x=task.get('series_variable',task.get('variable'))
    fields={'kind','id','source','function','series_variable','variable','center','requested_output','printed_conditions','parameters','method_requirement'}
    literal=task.get('source',{}).get('literal_requirement')
    heads=power_series_headings(x)
    reading,algebra=heads['any'],heads['algebra_of_power_series']
    if (set(task)-fields or not isinstance(x,str) or not x.isidentifier() or task.get('center','0')!='0'
            or task.get('requested_output',['all_coefficients','convergence_set'])!=['all_coefficients','convergence_set']
            or literal not in (None,reading,algebra,f'Разложить в степенной ряд для |{x}|<1.')):
        raise Unsupported('Need all original coefficients at the original zero center')
    f=task['function'];z=('v',x);method=task.get('method_requirement');conditions=task.get('printed_conditions',[])
    names=sorted(set(re.findall(r'\b[A-Za-z_]\w*',f))-{x,'pi','e'}-m.FUNCTIONS-set(m.ALIASES))
    if task.get('parameters',names)!=names:raise Unsupported('The source fixed parameters are not bound')
    ctx=m.context(dict(variable=x,parameters=names));raw=m.parse(f,x,names)
    if raw[0]=='rpow' and raw[2]==z and raw[1][0]=='s' and conditions==[x+'>0'] and method is None:
        a=raw[1][1]
        return analytic_series_receipt('exponential_series_at_a_positive_power_base',
                   dict(branches=[dict(condition=a+'>0',coefficient=f'ln({a})^n/n!',convergence_domain='R'),
                                  dict(condition=a+'=0',coefficient='0',convergence_domain='R'),
                                  dict(condition=a+'<0',classification='no real function on the whole printed interval')],
                        original_function_domain=x+'>0'),
                   'Для положительного основания переписать степень как exp(x ln a) и взять весь экспоненциальный ряд. Он сходится при каждом конечном x.',
                   'Нулевое основание на исходном положительном интервале задаёт нулевую функцию. Отрицательное основание не даёт вещественных значений для всех напечатанных показателей.',
                   coordinate=z,base=raw[1],retained_source_conditions=conditions)
    if raw[0] in ('sin','cos') and raw[1][0]=='mul' and method is None and not conditions:
        a,b=raw[1][1:]
        if a==('asin',z):a,b=b,a
        if b!=('asin',z) or not m.constant_defined(a,ctx) or domain_conditions(a):
            raise Unsupported('Need an independently defined real frequency of arcsine')
        a0=source(a);sine=raw[0]=='sin';parity='odd' if sine else 'even'
        return analytic_series_receipt('parity_recurrence_for_inverse_angle_composition',
                   dict(recurrence=f'c_(n+2)=(n^2-({a0})^2)*c_n/((n+1)*(n+2))',
                        initial=[ZERO,a] if sine else [ONE,ZERO],source_domain=f'abs({x})<=1',
                        terminating=f'{a0}=0 or |{a0}| is a positive {parity} integer',
                        otherwise=dict(radius=ONE,endpoints='both absolute')),
                   'Положить θ=arcsin x. Закон второй производной по θ переносится в уравнение (1−x²)y″−xy′+a²y=0. Начальные значения выбирают чётную или нечётную ветвь.',
                   'Сравнение коэффициентов даёт рекурсию с шагом два. Нулевой множитель на активной чётности завершает ряд.',
                   'Для нетерминирующего хвоста отношение модулей равно 1−3/n+O(n⁻²) на шагах длины два. Сумма логарифмов даёт коэффициенты порядка n⁻³ᐟ², радиус единица и абсолютную сходимость на обеих границах.',
                   original=raw,frequency=a,derivative_equation='(1-x^2)y\'\'-xy\'+a^2*y=0')
    if raw[0]=='pow' and raw[2]==2 and raw[1]==('div',('asin',z),z) and method=='algebra_of_power_series' and not conditions:
        n='coefficientIndex'
        while n==x:n+='_'
        child=dict(kind='series_sum',term=f'factorial({n}-1)^2*(2*{x})^(2*{n})/factorial(2*{n})',index=n,start_index=1)
        known=request('проверить коэффициенты квадрата обратного синуса перед делением',child)
        if known['compilation']['theorem']!='method.inverse_central_coefficients_from_second_order_equation':
            raise Unsupported('The child does not verify the intended recurrence')
        return analytic_series_receipt('stationary_coefficient_shift_at_removable_origin',
                   dict(coefficient_even='2^(2*n+1)*(n!)^2/(2*n+2)!',coefficient_odd='0',
                        radius=ONE,endpoints='both absolute',original_domain=f'0<abs({x})<=1',continuous_extension_at_zero=ONE),
                   'Использовать отдельно проверенный ряд квадрата обратного синуса. Он начинается со второй степени и имеет сходящиеся концы.',
                   'Деление на квадрат переменной сдвигает все степени на два. Исходную дробь сохраняем на проколотой области, а ряд задаёт её устранимое продолжение.',
                   original=raw,coefficient_goal=child)
    if raw[0]=='mul' and method=='algebra_of_power_series' and not conditions and not names:
        a,b=raw[1:]
        if a[0]=='cosh':a,b=b,a
        if b[0]=='cosh' and b[1][0]=='sqrt' and not domain_conditions(a) and not domain_conditions(b[1][1]):
            c,d=affine(b[1][1],x);p,q0=rf(a,x)
            if m.num(c) is not None and m.num(c)>0 and d==ZERO and q0==(1,):
                return analytic_series_receipt('finite_coefficient_convolution_of_even_kernel',
                           dict(coefficient=f'sum(j=0..min(n,{len(p)-1}),p_j*({source(c)})^(n-j)/(2*(n-j))!)',
                                polynomial_coefficients=list(map(q,p)),convergence_domain='R',original_domain=x+'>=0'),
                           'В чётном ряде гиперболического косинуса после подстановки корня остаются только целые неотрицательные степени.',
                           'Конечный полиномиальный множитель даёт свёртку коэффициентов. Ряд сходится на всей прямой и совпадает с исходной функцией на её вещественной области.',
                           original=raw,root_scale=c)
    if (raw[0]=='div' and raw[1]==ONE and raw[2][0]=='sqrt' and len(names)==1 and
            conditions==[f'abs({x})<1'] and method is None):
        t=('s',names[0]);w=raw[2][1];wanted=m.add(ONE,m.add(m.mul(q(-2),m.mul(t,z)),m.power(z,2)))
        if domain_conditions(w) or not same_value(w,wanted):raise Unsupported('Need a normalized reciprocal quadratic radical')
        label=names[0]
        return analytic_series_receipt('reciprocal_quadratic_coefficient_transport',
                  dict(recurrence=f'(n+1)P_(n+1)=(2*n+1)*{label}*P_n-n*P_(n-1)',initial=[ONE,t],
                       source_interval=f'abs({x})<1',branches=[
                        dict(condition=f'abs({label})<=1',radius=ONE,convergence_within_source=f'abs({x})<1'),
                        dict(condition=f'abs({label})>1',radius=f'1/(abs({label})+sqrt({label}^2-1))',
                             convergence_within_source=f'abs({x})<radius or {x}=-sign({label})*radius',
                             opposite_boundary='conditional',nearest_boundary='undefined source and divergent series')]),
                  'Логарифмическая производная исходного радикала даёт линейное уравнение и трёхчленную рекурсию.',
                  'Разложить квадратный знаменатель на два линейных множителя и использовать биномиальные ряды обратных квадратных корней. Ближайший корень задаёт радиус, поскольку радикальная особенность в нём неустранима. При модуле параметра не больше единицы радиус равен единице.',
                  'При большем модуле выделить ближайший действительный полюс. На противоположном конце первый биномиальный ряд условно сходится, второй абсолютно. Их произведение сохраняет сходимость, а нижняя центральная биномиальная оценка исключает абсолютную сходимость.',
                  original=raw,source_conditions=conditions)
    raise Unsupported('No checked analytic coefficient transport for this source expression')


def factorial_taylor_transport(task):
    h=task.get('hypotheses');meta=task.get('source',{});goal=meta.get('literal_requirement')
    fields={'kind','id','source','hypotheses','f','source_hint'}
    if set(task)-fields:raise Unsupported('An extra analytic premise must be bound')
    domains=(['f smooth on (a,b)','abs(f^(n)(x))<=c^n for each n>=0 and x in (a,b)'],
             ['f smooth on [-1,1]','f^(n)(x)>=0 for each n>=0 on [-1,1]'])
    if task.get('f')=='sum_{n>=0} a_n*x^n' and h==['abs(n!*a_n)<M for n>=1, constant M'] and not task.get('source_hint'):
        claims={'Доказать бесконечную дифференцируемость функции в любой точке a.',
                'Доказать разложение f(x)=sum f^(n)(a)*(x-a)^n/n! для всех конечных x.'}
        if goal not in claims|{None}:raise Unsupported('The analytic conclusion differs')
        return analytic_series_receipt('factorial_majorants_for_derivatives_and_taylor',
                   dict(smooth_everywhere=True,taylor_identity_all_finite_x=True,positive_order_bound='M*exp(abs(x))'),
                   'Для каждого положительного порядка производной факториал знаменателя сдвигается точно. Исходное ограничение даёт экспоненциальную мажоранту на каждом компакте.',
                   'На отрезке между центром и точкой все положительные производные ограничены одной и той же константой. Факториальный знаменатель остатка Тейлора делает его нулевым в пределе.',
                   original_hypotheses=h)
    if h==domains[0] and not task.get('f') and not task.get('source_hint') and goal in (
            None,'Доказать сходимость степенного разложения около каждого x0 на всём интервале (a,b).'):
        return analytic_series_receipt('factorial_majorants_for_derivatives_and_taylor',dict(taylor_identity_on='(a,b) for each center in (a,b)'),
                   'Весь отрезок между выбранным центром и исходной точкой лежит в данном интервале. Остаток Лагранжа ограничен степенью c·|x−x₀|, делённой на факториал.',
                   'Отношения соседних мажорант стремятся к нулю, поэтому остаток исчезает в каждой допустимой точке.',original_hypotheses=h)
    if h==domains[1] and not task.get('f') and goal in (None,'Доказать, что f разлагается по степеням x на (-1,1).') and task.get('source_hint') in (
            None,'Используя монотонность производных, получить оценку abs(R_n(x))<=abs(x)^(n+1)*f(1).'):
        return analytic_series_receipt('scaled_integral_taylor_remainder',dict(taylor_identity_on='(-1,1)',bound='|x|^(n+1)*f(1)'),
                   'Записать интегральный остаток Тейлора и заменить переменную интегрирования t на x*u. Для обоих знаков x имеем x*u≤u.',
                   'Неотрицательность следующей производной даёт монотонность нужной производной. Оценить остаток через |x|^(n+1) раз остаток в единице.',
                   'Все коэффициенты Тейлора неотрицательны, поэтому остаток в единице ограничен f(1). При |x|<1 мажоранта стремится к нулю.',original_hypotheses=h)
    raise Unsupported('No matching original factorial or Taylor bound')


def coefficient_transport_goal(task,lib,request):
    from verify import same_value
    if not lib.data.get('coefficient_and_limit_transport'):raise Unsupported('The transport transitions are absent')
    k=task['kind'];meta=task.get('source',{})
    if not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256',
                                               'pdf_pages','page_png_sha256','literal_requirement'}:
        raise Unsupported('A retained source condition has not been bound')
    if k=='infinite_power_series_expansion':return transport_expansion(task,lib,request)
    if k=='analyticity_theorem':return factorial_taylor_transport(task)
    if k=='series_coefficient_recurrence':
        identity=task.get('identity','')
        a=re.fullmatch(r'sec (\w+)=sum_\{(\w+)>=0\} (\w+)_\2\*\1\^\(2\*\2\)/\(2\*\2\)!',identity)
        if (set(task)-{'kind','id','source','identity'} or not a or len(set(a.groups()))!=3 or
                meta.get('literal_requirement') not in (None,'Вывести рекуррентное соотношение для чисел Эйлера в напечатанном разложении.')):
            raise Unsupported('No matching reciprocal cosine coefficient sequence')
        x,n,E=a.groups()
        return analytic_series_receipt('reciprocal_even_coefficient_convolution',
                   dict(initial=ONE,recurrence=f'{E}_{n}=-sum(j=0..{n}-1, (-1)^({n}-j)*binomial(2*{n},2*j)*{E}_j)'),
                   'В исходном центре косинус равен единице. Его обратная функция аналитична на малой окрестности.',
                   'Умножить неизвестный чётный ряд на ряд косинуса и сравнить коэффициенты единицы. Умножение на полный факториал даёт биномиальные множители.',
                   printed_identity=identity)
    if k=='abel_converse_positive_coefficients':
        if (set(task)-{'kind','id','source','hypotheses','target'} or task.get('hypotheses')!=[
                'a_n>=0','lim_(x->R-) sum_{n>=0} a_n*x^n=S'] or task.get('target')!='sum_{n>=0} a_n*R^n=S' or
                meta.get('literal_requirement') not in (None,'Доказать сходимость в правой граничной точке с той же суммой.')):
            raise Unsupported('The right boundary and source coefficient sign need independent verification')
        return analytic_series_receipt('finite_truncation_at_positive_abel_boundary',dict(boundary_sum='S',convergent=True),
                   'На положительном радиусе каждая конечная частичная сумма при x<R не превосходит полной суммы. Перейти к правому пределу для каждой фиксированной конечной суммы.',
                   'При R все члены неотрицательны, поэтому ограниченные частичные суммы сходятся. Обратное неравенство получается сравнением всех внутренних сумм с суммой в R.',
                   'Если R неположителен и левое приближение существует, в области сходимости есть отрицательная точка с модулем больше |R|. Тогда R находится внутри круга сходимости и равенство следует из непрерывности.',
                   hypothesis='nonnegative coefficients and finite left limit')
    if k=='sum_of_power_series_by_method':
        x=task.get('variable');index=task.get('index');n=('v',index);z=('s',x)
        if (set(task)-{'kind','id','source','series','variable','method_requirement','index','start_index','coefficient_term'} or
                task.get('method_requirement')!='termwise_differentiation' or task.get('start_index')!=1 or
                not all(isinstance(s,str) and s.isidentifier() for s in (x,index)) or x==index or
                meta.get('literal_requirement') not in (None,'Вычислить сумму указанного ряда предписанным методом.')):
            raise Unsupported('The printed series and differentiation method must be bound')
        raw=m.parse(task['coefficient_term'],index,[x])
        expected=('div',('rpow',z,n),('mul',n,('add',n,ONE)))
        prefix=task['series'].removesuffix('+...').split('+')
        if raw!=expected or not task['series'].endswith('+...') or len(prefix)<2 or any(
                not same_value(m.parse(expr,None,[x]),m.div(m.power(z,i),q(i*(i+1)))) for i,expr in enumerate(prefix,1)):
            raise Unsupported('The printed coefficients differ from the stated positive-index harmonic weights')
        return analytic_series_receipt('euler_derivative_of_shifted_harmonic_weights',
                   dict(interior_sum=f'1+(1-{x})*ln(1-{x})/{x}',at_zero=ZERO,at_one=ONE,
                        at_minus_one=m.add(ONE,m.neg(m.mul(q(2),('ln',q(2))))),convergence_interval='[-1,1]'),
                   'Умножить исходный ряд на x. Почленное дифференцирование внутри радиуса сокращает n+1 и даёт −ln(1−x).',
                   'Восстановить произведение с нулевым начальным значением, затем учесть исходный нулевой член и разделить на x вне нуля.',
                   'На обоих концах исходный вес имеет порядок n⁻², поэтому непрерывное радиальное продолжение даёт точные суммы.',
                   original_coefficient=raw,method_verified='termwise_differentiation')
    raise Unsupported('No verified coefficient transport for this mathematical goal')


def factorial_logarithmic_mean(task):
    from tasks import domain_conditions,known_guard
    from verify import same_value
    fields={'kind','id','source','goal','expression','index','index_domain','approach','method_requirement'}
    source_info=task.get('source',{})
    if (set(task)-fields or task.get('goal') not in (None,'Find the printed limit.')
            or task.get('index_domain') not in ('positive integers','positive_integers') or task.get('approach')!='+infinity'
            or task.get('method_requirement') not in (None,'any')
            or not isinstance(source_info,dict) or set(source_info)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256'}):
        raise Unsupported('The factorial growth proof requires the original positive integer limit and no extra prescribed method')
    index=task['index'];N=('v',index);raw=m.parse(task['expression'],index,extra_functions=('factorial',))
    if raw[0]!='div' or raw[1][:2]!=('rpow',('factorial',N)):
        raise Unsupported('A factorial root over the matching integer scale is required')
    power=raw[2]
    k=ONE if power==N else q(power[2]) if power[:2]==('pow',N) else power[2] if power[:2]==('rpow',N) else None
    if k is None or m.num(m.simplify(k)) is None or not same_value(raw[1][2],m.div(k,N)):
        raise Unsupported('The factorial exponent and denominator scale do not match')
    ctx=m.context(dict(variable=index))
    for relation,e in domain_conditions(raw):
        if e in (N,('factorial',N),power):continue
        if not known_guard((relation,e),ctx):
            raise Unsupported('An original denominator or exponent restriction was not proved')
    value=('exp',m.neg(k))
    return (dict(theorem='method.logarithmic_factorial_mean_by_integral',strategy='logarithmic_integral_bounds',
                variable=index,original=raw,scale=k,
                argument=['Сравниваем сумму ln k с интегралом возрастающей функции ln t от 1 до n. Разница лежит между нулём и ln n.',
                          'Интеграл равен n ln n−n+1. После деления на n и вычитания ln n предел равен −1.',
                          'Учитываем исходный множитель показателя и возвращаемся из логарифмической координаты непрерывной экспонентой.']),
            value)


def abstract_riemann_profile(task):
    """Recover the mesh and distinguish an integrable profile from arbitrary samples."""
    from quadrature import riemann_weight,uniform_sum_source
    from verify import same_value
    n,parameters,conditions=uniform_sum_source(task)
    text=riemann_weight(task['expression'],n,parameters,as_prefix=True)
    entries=list(prefix_occurrences(text))
    if len(entries)!=1:raise Unsupported('Exactly one original uniform prefix is required')
    begin,end,k,start,top,offset,body=entries[0]
    if start!=1 or top!=n or offset or k==n or {k,n}&set(parameters):
        raise Unsupported('The prefix must use every original right endpoint at positive integer indices')
    hit=re.fullmatch(r'(\w+)\((.+)\)',body)
    if not hit or hit[1] not in parameters or hit[1] in m.FUNCTIONS or len(parameters)!=3:
        raise Unsupported('The original named profile and two independent endpoints are required')
    f=hit[1];names=[a for a in parameters if a!=f];K,N=('s',k),('s',n)
    mark='__mesh_sum'
    if mark in [k,n,*parameters]:raise Unsupported('Expected a fresh prefix marker')
    S=('s',mark);surround=m.parse(text[:begin]+mark+text[end:],None,[n,mark,*names])
    if not same_value(surround,m.div(S,N)) or any(rel!='nonzero' or g!=N for rel,g in domain_conditions(surround)):
        raise Unsupported('The original prefix is not averaged with its natural positive mesh size')
    arg=m.parse(hit[2],None,[n,k,*names])
    start_value=m.simplify(m.substitute(arg,{K:ZERO,N:ONE}))
    end_value=m.simplify(m.substitute(arg,{K:ONE,N:ONE}))
    if ({start_value,end_value}!={('s',p) for p in names} or
            any(relation!='nonzero' or e!=N for relation,e in domain_conditions(arg)) or
            not same_value(arg,m.add(start_value,m.mul(m.div(K,N),m.add(end_value,m.neg(start_value)))))):
        raise Unsupported('No exact affine right-endpoint mesh of the named profile')
    a,b=start_value[1],end_value[1]
    if conditions not in ([],[f+' continuous'],[f+' Riemann integrable on original interval']):
        raise Unsupported('The source profile assumptions need a separate proof')
    plan=dict(theorem='method.affine_riemann_samples',outer=n,strategy='abstract_riemann_profile',
              endpoints=[],exact_profile=f,arguments=(start_value,end_value),original_argument=arg,steps=[
        'Получаем точно правые концы равномерного разбиения. Сумма является средним выборочных значений.',
        'На вырожденном отрезке все члены равны f(a). На невырожденном отрезке для интегрируемой по Риману функции предел равен ориентированному интегралу, делённому на b−a.'])
    value=dict(degenerate=dict(condition=a+'='+b,value=f+'('+a+')'),
               integrable_case=dict(condition=a+'!='+b+' and f is Riemann integrable',
                                    value=f'int_{a}^{b} {f}(t)dt/({b}-{a})'))
    if not conditions:
        plan['steps'].append('Без условия интегрируемости предел не гарантирован. Берём индикатор рациональных нормированных координат с чётным сокращённым знаменателем. На нечётных n все члены нулевые. При n — степени двойки все члены, кроме последнего, равны единице.')
        value.update(classification='not determined without profile regularity on a nondegenerate interval',
                     counterexample=dict(odd_indices=ZERO,powers_of_two='1−1/n',limits=[ZERO,ONE]))
    return plan,value


def sequence_source_scope(task):
    from fractions import Fraction as F
    # The reported premise is tested on both the ordinary and unbounded branches.
    from integrals import affine
    from verify import same_value
    kind=task.get('task_type',task.get('kind'));goal=task.get('goal',{})
    provenance={'id','source','source_statement','source_number','source_exercise_number','source_subpart','source_edition',
                'source_pdf_page','source_pdf_pages','transcription_notes','program_status','pending_obligations','main_pass_status'}
    if set(task)-provenance-{'kind','task_type','goal','index_domain','assumptions'} or not isinstance(goal,dict):
        raise Unsupported('The full source sequence premise and output must be identified')
    if kind=='characterize_convergence_by_envelope_algebra':
        wanted=dict(hypothesis='for every y, at least one of the printed limsup equalities holds',conclusion='x[n] converges',
                    source_alternatives=['limsup(x+y)=limsup(x)+limsup(y)','limsup(x*y)=limsup(x)*limsup(y), with x[n]>=0'])
        stated=task.get('assumptions',[])
        if (goal!=wanted or task.get('index_domain')!='positive_integers' or stated not in ([],['x[n] bounded'])):
            raise Unsupported('The alternative, quantifier and the nonnegative index sequence must be retained')
        value=dict(bounded_case='convergent',separating_sequence='1/(1+x[n])')
        if not stated:
            value.update(printed_claim_holds=False,counterexample=dict(x='x[n]=n',convergence='no finite limit',
                sum_equality='whenever limsup(y)>-infinity',product_equality='whenever limsup(y)=-infinity'))
        return dict(theorem='method.envelope_inverse_separator',argument=[
            'Для ограниченной неотрицательной x с разными нижним a и верхним b пределами выбираем y=1/(1+x).',
            'Функции x+y и x·y возрастают по x. Их верхние пределы равны значениям при b, а limsup y=1/(1+a). При a<b обе напечатанные равенства строго нарушаются.',
            'Сходимость ограниченной x следует из совпадения граней хвоста. Без ограниченности x[n]=n даёт равенство суммы, если limsup y больше −∞, и равенство произведения, если y стремится к −∞.'
        ]),value
    if kind!='finite_sum_or_product_sequence_limit' or set(goal)!={'first_root_indices','literal_last_root_index','radicand','variable','approach'}:
        raise Unsupported('The original pattern and terminal root index need full binding')
    prefix=goal['first_root_indices'];radicand=goal['radicand'];n=goal['variable']
    if (not isinstance(prefix,list) or len(prefix)<3 or any(type(k) is not int or k<=0 for k in prefix)
            or goal['approach']!='positive_integer_index_to_infinity' or not re.fullmatch(r'[A-Za-z]\w*',n)
            or task.get('assumptions') not in ([n+' is a positive integer'],
                    [n+' is a positive integer','root indices form a geometric progression'])):
        raise Unsupported('Positive integer index and at least three observed positive roots are required')
    x=('v',n);b=m.simplify(m.parse(str(radicand),None));ratio=F(prefix[1],prefix[0])
    if m.num(b) in (None,0,1) or m.num(b)<1 or ratio.denominator!=1 or ratio<=1 or any(
        v!=ratio*u for u,v in zip(prefix,prefix[1:])):
        raise Unsupported('A positive nonconstant root product with a verified candidate geometric stride is required')
    last=m.parse(goal['literal_last_root_index'],n)
    terminal=f'{prefix[0]}*{int(ratio)}^({n}-1)'
    factor=F(1,prefix[0])*ratio/(ratio-1)
    value=dict(geometric_pattern=dict(terminal_index=terminal,exponent=q(factor),limit=('rpow',b,q(factor))))
    if same_value(last,m.parse(terminal,n)):
        if 'root indices form a geometric progression' not in task['assumptions']:
            raise Unsupported('Geometric interior indices need an explicit reading')
        argument=['Из постоянного отношения индексов получаем конечную геометрическую сумму обратных индексов. Её предел даёт показатель степени исходного основания.']
    else:
        k,d=affine(last,n);a,c=m.num(k),m.num(d)
        if a is None or a.denominator!=1 or a<2 or c is None or c.denominator!=1:
            raise Unsupported('The literal endpoint needs a positive affine index for contrasting completions')
        prefix_sum=sum((F(1,k) for k in prefix),F(0))
        value.update(printed_claim_holds=False,counterexample=dict(
            sparse_completion_exponent=f'{prefix_sum}+ln({a}/{a-1})',
            dense_completion_exponent='+inf',same_printed_terminal=goal['literal_last_root_index']))
        argument=[
            'Первые индексы предлагают геометрическую прогрессию, но её конечный индекс не совпадает с напечатанной аффинной формулой.',
            'Даже при n множителях есть два продолжения. После известного начала можно взять последние n−k последовательных индексов до заданного конца. Их обратные дают конечный логарифмический предел.',
            'Можно вместо этого выбрать n−k−1 последовательных индексов сразу после начала и отдельно последний заданный индекс. Сумма обратных в этом случае растёт без границы. Печатные данные допускают разные пределы.'
        ]
    return dict(theorem='method.terminal_index_consistency',argument=argument),value
