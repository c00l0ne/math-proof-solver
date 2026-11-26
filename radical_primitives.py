"""Exact differentials on the real branches of y² = Q(x)."""
from fractions import Fraction as F

import expressions as m
from model import ONE, ZERO, Unsupported, freeze, q
from polynomial import pa, pm, pp, pdiv, quotient_derivative_numerator, rf, span_coefficients
from tasks import domain_conditions,source

METHOD = 'quadratic_radical_differential'
REQUIREMENTS = {'quadratic_radical_polynomial_reduction', 'partial_fractions_of_rational_factor'}
ADMITTED = REQUIREMENTS | {'quadratic_canonical_form', 'table_and_rules', 'appropriate_integrand_transformation'}
O = (F(1),)


def data(task):
    from graphs import domain_partition
    from integrals import integral_source
    name, parameters, _, expr = integral_source(task)
    method = task.get('method_requirement', 'table_and_rules')
    if parameters or method not in ADMITTED:
        raise Unsupported('A parameter or a different prescribed construction needs a proof')
    radicals = []

    def detach(node, sign):
        if node[0] == 'sqrt':
            radicals.append((node[1], sign))
            return ONE
        if node[0] in ('mul', 'div'):
            return node[0], detach(node[1], sign), detach(node[2], sign if node[0] == 'mul' else -sign)
        return node

    coefficient = detach(expr, 1)
    if len(radicals) != 1:
        raise Unsupported('Expected one multiplicative quadratic radical')
    (radicand, sign), = radicals
    Q, scalar = rf(radicand, name)
    if len(Q) != 3 or len(scalar) != 1:
        raise Unsupported('Expected a quadratic polynomial')
    Q = tuple(z/scalar[0] for z in Q)
    if Q[1]**2 == 4*Q[0]*Q[2]:
        raise Unsupported('A double root requires separate component primitives')
    p, d = rf(coefficient, name)
    if sign == 1:
        p = pm(p, Q)
    guards=tuple(domain_conditions(expr))
    chart, domain = domain_partition(name, guards)
    if not any(chart['open_cells']):
        raise Unsupported('No nondegenerate real interval')
    return name, coefficient, Q, p, d, domain, expr, guards


def derivative_product(A, Q, exponent=F(1,2)):
    # (A Q^p)' = Q^(p-1) (Q A' + p A Q') on a valid real branch.
    return pa(pm(Q, quotient_derivative_numerator(A, O)),
              pm(A, tuple(x*exponent for x in quotient_derivative_numerator(Q, O))))


def translated(Q, h):
    c, b, a = Q
    return pa((a, b+2*a*h), (0, 0, c+b*h+a*h*h))


def reduction(P, Q):
    degree = len(P)-len(Q)+1
    monomials = [(F(0),)*i+O for i in range(degree+1)]
    columns = [derivative_product(v, Q) for v in monomials]
    # A linear radicand absorbs even the constant into A sqrt Q.
    weights = span_coefficients(P, columns+([O] if len(Q)==3 else []))
    if weights is None:
        raise Unsupported('No polynomial differential identity')
    A = weights[:len(monomials)] or (F(0),)
    return dict(multiplier=[q(a) for a in A], residual=q(weights[-1] if len(Q)==3 else 0))


def propose(task):
    from integrals import denominator_factors
    name, coefficient, Q, p, d, *_ = data(task)
    whole, rest = pdiv(p, d)
    addresses, columns = [], []
    for factor in denominator_factors(coefficient, d, name):
        if len(factor) != 2:
            continue
        for j in range(1, len(d)):
            col, rem = pdiv(d, pp(factor, j))
            if any(rem):
                break
            addresses.append((-factor[0], j))
            columns.append(col)
    weights = span_coefficients(rest, columns)
    if weights is None:
        raise Unsupported('Remaining rational factor has no decomposition in supported real poles')
    terms = []
    for (h, j), w in zip(addresses, weights):
        if w:
            target = (F(0),)*(j-1)+(w,)
            terms.append(dict(pole=q(h), power=j, coefficient=q(w), **reduction(target, translated(Q,h))))
    c,b,a=Q
    return dict(method=METHOD, polynomial=[q(c) for c in whole], regular=reduction(whole, Q), poles=terms,
                canonical_square=dict(linear=[q(b),q(2*a)],discriminant=q(b*b-4*a*c)))


def checked_primitive(entry, target, Q, u):
    from integrals import polynomial_expression
    A = tuple(m.num(freeze(x)) for x in entry['multiplier'])
    residue = m.num(freeze(entry['residual']))
    if not A or None in A or residue is None or pa(derivative_product(A,Q), (residue,)) != target:
        raise Unsupported('Polynomial derivative does not give the stated numerator')
    def evaluate(p):
        return m.substitute(polynomial_expression(p,'s'), {('v','s'):u})
    root = ('sqrt',evaluate(Q))
    primitive = m.mul(evaluate(A),root)
    if not residue:
        return primitive
    if len(Q) != 3:
        raise Unsupported('A logarithmic or circular seed needs a nondegenerate quadratic')
    c,b,a = Q
    disc = b*b-4*a*c
    z = evaluate((b,2*a))
    scale = m.simplify(('sqrt',q(abs(a))))
    # z²-4aQ=disc. For a>0 the two conjugate factors have nonzero
    # product; for a<0 the arcsine argument is strictly interior on Q>0.
    if not disc or a<0 and disc<0:
        raise Unsupported('No real canonical seed on this component')
    if a>0:
        seed = ('ln',('abs',m.add(z, m.mul(q(2),m.mul(scale,root)))))
    else:
        seed = m.neg(('asin',m.div(z,m.simplify(('sqrt',q(disc))))))
    return m.add(primitive,m.mul(q(residue),m.div(seed,scale)))


def check(task, plan):
    name, _, Q, p, d, domain, expr, guards = data(task)
    x = ('v',name)
    c,b,a=Q
    square=plan['canonical_square']
    linear=tuple(m.num(freeze(v)) for v in square['linear'])
    disc=m.num(freeze(square['discriminant']))
    if linear!=(b,2*a) or disc is None or pa(pm(linear,linear),(-disc,))!=pm((4*a,),Q):
        raise Unsupported('The completed square does not reproduce the source quadratic')
    whole = tuple(m.num(freeze(z)) for z in plan['polynomial'])
    if not whole or None in whole:
        raise Unsupported('Invalid polynomial part')
    reconstructed = pm(whole,d)
    answer = checked_primitive(plan['regular'],whole,Q,x)
    poles = set()
    for item in plan['poles']:
        h,w = (m.num(freeze(item[k])) for k in ('pole','coefficient'))
        j = item['power']
        if h is None or not w or type(j) is not int or not 1<=j<len(d) or (h,j) in poles:
            raise Unsupported('Invalid partial fraction')
        poles.add((h,j))
        col, rem = pdiv(d,pp((-h,F(1)),j))
        if any(rem):
            raise Unsupported('Proposed pole is not excluded by the original denominator')
        reconstructed = pa(reconstructed,pm((w,),col))
        shift = m.add(x,q(-h))
        # t=1/(x-h), sqrt Q = |x-h| sqrt(Q(h)t²+Q'(h)t+a).
        term = checked_primitive(item,(F(0),)*(j-1)+(w,),translated(Q,h),m.div(ONE,shift))
        answer = m.add(answer,m.neg(m.mul(m.div(shift,('abs',shift)),term)))
    if plan.get('method')!=METHOD or reconstructed != p:
        raise Unsupported('Partial fractions do not reconstruct the source differential')
    if task.get('method_requirement')=='partial_fractions_of_rational_factor' and len(poles)+bool(any(whole))<2:
        raise Unsupported('The requested partial fraction step needs a displayed decomposition')
    return dict(representative=answer, real_domain=domain, original_domain=('and',guards),
                identity=dict(derivative_ast=expr,integrand_ast=expr),family='F|J + C_J',
                component_scope='each connected component of the original real domain',
                constant_policy='independent real C_J on each component',
                endpoints='one_sided_derivative_at_included_endpoints'), 5+3*len(plan['poles'])


def report(result):
    from app import pretty
    v = result['value']
    x = result['task'].get('variable','x')
    lines = ['Выделяем квадратный корень y = √Q и представляем интеграл в виде ∫R(x) dx/y.']
    if result['compilation']['poles']:
        lines.append('Разлагаем R на простые дроби. Для полюса h берём t = 1/(x−h) и сохраняем знак x−h на каждом промежутке.')
    plan=result['compilation']
    from integrals import polynomial_expression
    A=polynomial_expression(tuple(m.num(freeze(a)) for a in plan['regular']['multiplier']),x)
    linear=polynomial_expression(tuple(m.num(freeze(a)) for a in plan['canonical_square']['linear']),x)
    lines.extend(['Проверяем P = QA′ + Q′A/2 + c. Для полиномиальной части A = '+pretty(A,x)+', c = '+pretty(plan['regular']['residual'],x)+'.',
                  'Каноническая форма даёт 4aQ = ('+pretty(linear,x)+')² − ('+pretty(plan['canonical_square']['discriminant'],x)+').',
                  'На каждой компоненте исходной области первообразная равна '+pretty(v['representative'],x,simplify=False)+' + C.'])
    return '\n'.join(lines)


CHARTS=('radical_conic','radical_pair','radical_power','radical_scale','parts_power_kernel')
CHART_METHODS={'table_and_rules','appropriate_integrand_transformation','rationalizing_substitution',
               'appropriate_substitution','euler_substitution','quadratic_canonical_form','trigonometric_substitution','hyperbolic_substitution',
               'partial_fractions_of_rational_factor'}


def chart_source(task,methods):
    from integrals import kernel_symbol
    fields={'kind','integrand','variable','parameters','schema','id','source','transcription',
            'stated_conditions','stated_domain','method_requirement','requested_output'}
    method=task.get('method_requirement','table_and_rules')
    printed=task.get('source',{})
    want=task.get('requested_output',[])
    if (set(task)-fields or task.get('kind')!='integrate' or method not in methods
            or task.get('stated_domain') not in (None,[],()) or not isinstance(printed,dict)
            or any(printed.get(k) not in (None,method) for k in ('explicit_imposed_method','explicit_required_method','method_requirement'))
            or not isinstance(want,(tuple,list)) or set(want)-{'primitive_family','natural_domain_components','constant_per_component'}):
        raise Unsupported('The prescribed primitive or its original domain is different')
    v=task.get('variable','x');params=task.get('parameters',[])
    if not isinstance(params,list) or not all(isinstance(p,str) for p in params):
        raise Unsupported('The radical chart needs explicit real parameters')
    return v,kernel_symbol(task),method,m.parse(task['integrand'],v,params)


def radical_chart_options(task):
    text=task.get('integrand','')
    method=task.get('method_requirement','table_and_rules')
    if not isinstance(text,str):return ()
    parts=('parts_power_kernel',) if (method in ('table_and_rules','integration_by_parts')
          and ('ln(' in text or 'exp(' in text and '^' in text)) else ()
    if task.get('parameters'):
        return ('radical_scale',) if (method in CHART_METHODS|{'quadratic_radical_polynomial_reduction'}
            and ('sqrt(' in text or '^2)' in text)) else parts
    if method not in CHART_METHODS or task.get('stated_conditions'):
        return parts
    if not any(token in text for token in ('sqrt(','cbrt(','^(1/','^(2/')):return parts
    if method in ('euler_substitution','quadratic_canonical_form','trigonometric_substitution',
                  'hyperbolic_substitution','partial_fractions_of_rational_factor'):return CHARTS[:1]
    return CHARTS[:3]+parts


def conic_chart(f,v,t,method,radicals):
    from math import isqrt
    from integrals import denominator_factors,polynomial_expression
    from polynomial import NotRational,Undefined
    if len(radicals)!=1 or radicals[0][0]!='sqrt':raise Unsupported('One quadratic radical is required')
    root=radicals[0];x=('v',v)
    P,D=rf(root[1],v)
    if len(P)!=3 or len(D)!=1:raise Unsupported('The source radical is not quadratic')
    c,b,a=(z/D[0] for z in P);disc=b*b-4*a*c
    if not disc:raise Unsupported('A double root requires a signed linear reduction')
    def square_root(y):
        if y<0:return None
        n,j=isqrt(y.numerator),isqrt(y.denominator)
        return F(n,j) if n*n==y.numerator and j*j==y.denominator else None
    leading=square_root(a)
    if a>0 and leading:
        # u=y+sqrt(a)x, quadratic reconstruction by difference of squares.
        s=q(leading)
        den=m.add(m.mul(q(2),m.mul(s,t)),q(b))
        coord=m.add(root,m.mul(s,x))
        X=m.div(m.add(m.power(t,2),q(-c)),den)
        Y=m.add(t,m.neg(m.mul(s,X)))
        jac=m.div(m.mul(q(2),Y),den)
        projection=dict(type='Euler line of the positive leading slope',slope=s)
    else:
        # Secant through a rational point. The forward slope is rationalized
        # to avoid a spurious hole at the base point.
        found=None
        for j in (0,1,-1,2,-2,3,-3,F(1,2),F(-1,2),F(3,2),F(-3,2)):
            y=square_root(a*j*j+b*j+c)
            if y:
                found=q(j),q(y),q(2*a*j+b)
                break
        if found is None:raise Unsupported('The conic has no admitted rational projection point')
        h,w,k=found
        den=m.add(m.power(t,2),q(-a))
        coord=m.div(m.add(k,m.mul(q(a),m.add(x,m.neg(h)))),m.add(root,w))
        X=m.add(h,m.div(m.add(k,m.neg(m.mul(q(2),m.mul(w,t)))),den))
        Y=m.add(w,m.mul(t,m.add(X,m.neg(h))))
        jac=m.div(m.mul(q(-2),Y),den)
        projection=dict(type='Euler secant through a rational conic point',point=(h,w))
    y2=m.power(Y,2)
    if any(rf(m.add(m.substitute(root[1],{x:X}),m.neg(y2)),t[1])[0]):
        raise Unsupported('The positive radical has not been recovered by the chart')
    closure=[('nonnegative',Y),('nonzero',den)]
    argument=['Use the real conic y²=Q(x), y≥0. The rational forward and inverse expressions cover this branch.',
              'The reconstruction denominator cannot vanish at a source point because that would make the discriminant zero.',
              'On Q>0 the inverse derivative has no zero. Points with Q=0 are retained exactly where the original expression is defined.']
    plan=dict(projection=projection,quadratic=list(map(q,(c,b,a))),discriminant=q(disc))
    if method in ('trigonometric_substitution','hyperbolic_substitution','quadratic_canonical_form'):
        center=-b/(2*a);peak=c-b*b/(4*a)
        if a<0 and peak<=0:raise Unsupported('There is no real open branch of the quadratic')
        if method=='hyperbolic_substitution' and a<0:raise Unsupported('The requested hyperbolic chart needs a positive leading coefficient')
        r=m.simplify(('sqrt',q(abs(peak/a))))
        height=m.simplify(('sqrt',q(abs(peak))))
        if method=='hyperbolic_substitution':wave=('sinh','cosh') if peak>0 else ('cosh','sinh')
        else:wave=('sin','cos') if a<0 else ('tan','sec') if peak>0 else ('sec','tan')
        plan['canonical_coordinate']=dict(center=q(center),radius=r,radical_scale=height,waves=wave,
            parameter_range='nonnegative parameter, both outer signs' if a>0 and peak<0 else 'central real sheet')
        argument.insert(0,'Complete the square and use the stated circular or hyperbolic coordinate with its nonnegative radical. '
                          'The displayed rational projection reparametrizes the same branch.')
    if method=='partial_fractions_of_rational_factor':
        def separate(e):
            if e==root:return ONE,1
            if e[0] in ('mul','div'):
                R,j=separate(e[1]);S,k=separate(e[2])
                return (m.mul(R,S),j+k) if e[0]=='mul' else (m.div(R,S),j-k)
            if m.contains(e,root):raise Unsupported('The requested rational coefficient is not a multiplicative factor')
            return e,0
        coefficient,power=separate(f)
        if power not in (-1,1):raise Unsupported('The rational factor requires one numerator or denominator radical')
        if power==1:coefficient=m.mul(coefficient,root[1])
        p,d=rf(coefficient,v)
        factors=denominator_factors(coefficient,d,v)
        whole,rest=pdiv(p,d)
        columns=[];addresses=[]
        product_check=O
        for factor in factors:
            if len(factor)<=1:continue
            rate=1
            while True:
                power=pp(factor,rate);col,rem=pdiv(d,power)
                if any(rem):break
                for j in range(len(factor)-1):
                    columns.append(pm(col,(F(0),)*j+O))
                    addresses.append((factor,rate,j))
                rate+=1
            product_check=pm(product_check,pp(factor,rate-1))
        if pdiv(d,product_check)[1]!=(F(0),) or len(pdiv(d,product_check)[0])!=1:
            raise Unsupported('The requested rational factorization is incomplete')
        weights=span_coefficients(rest,columns)
        if weights is None:raise Unsupported('No proof of the requested partial fractions')
        plan['rational_factor_decomposition']=dict(polynomial=polynomial_expression(whole,v),
            parts=[(polynomial_expression(factor,v),rate,j,q(w)) for (factor,rate,j),w in zip(addresses,weights) if w])
        argument.insert(0,'Put the differential over the common quadratic root, then resolve its rational factor into exact partial fractions.')
    return coord,X,{root:Y},jac,closure,plan,argument


def paired_radicals(f,v,t,radicals):
    from integrals import affine
    from polynomial import NotRational,Undefined
    x=('v',v);ctx=m.context(dict(variable=v))
    affine_roots=[]
    for node in radicals:
        if node[0]!='sqrt':raise Unsupported('Paired variables need principal square roots')
        try:A,B=affine(node[1],v)
        except Unsupported:continue
        a,b=(m.num(m.simplify(z)) for z in (A,B))
        if a and b is not None:affine_roots.append((a,b,node))
    if len(affine_roots)!=2:raise Unsupported('Two different linear square roots are needed')
    (a,b,U),(c,d,V)=sorted(affine_roots,key=lambda z:z[1])
    if a!=c or b==d:raise Unsupported('The selected positive roots do not have equal slopes')
    gap=q(d-b)
    Y=m.div(m.add(t,m.neg(m.div(gap,t))),q(2))
    Z=m.div(m.add(t,m.div(gap,t)),q(2))
    X=m.div(m.add(m.power(Y,2),q(-b)),q(a))
    extra={U:Y,V:Z}
    for root in radicals:
        if root in extra:continue
        try:diff=rf(m.add(root[1],m.neg(m.mul(U[1],V[1]))),v)[0]
        except (NotRational,Undefined):raise Unsupported('Another independent radical remains')
        if any(diff):raise Unsupported('The combined root needs the product of the two nonnegative radicals')
        extra[root]=m.mul(Y,Z)
    jac=m.div(m.mul(Y,m.add(ONE,m.div(gap,m.power(t,2)))),q(a))
    return m.add(U,V),X,extra,jac,[('positive',t),('nonnegative',Y),('nonnegative',Z)],dict(gap=gap),[
        'Let the new coordinate be the sum of the two nonnegative roots. Their difference is the constant difference of the radicands divided by the sum.',
        'Recover the original coordinate from the square of the first root. Nonnegative images of both roots and a positive sum describe precisely the original real branch.',
    ]


def common_power_chart(f,v,t,radicals):
    from integrals import affine
    from math import lcm
    x=('v',v);data=[]
    for root in radicals:
        e=F(1,2) if root[0]=='sqrt' else F(1,3) if root[0]=='cbrt' else m.num(m.simplify(root[2]))
        if e is None or e<=0:raise Unsupported('A variable or nonpositive algebraic degree needs a separate branch proof')
        a,b=map(lambda z:m.num(m.simplify(z)),affine(root[1],v))
        if not a or b is None:raise Unsupported('An affine real base is needed')
        data.append(((a,b),e,root))
    if not data or len({pair for pair,_,_ in data})!=1:raise Unsupported('The original powers have no common affine base')
    (a,b),_,example=data[0];base=example[1]
    n=lcm(*(e.denominator for _,e,_ in data))
    if n==1:raise Unsupported('There is no radical to remove')
    signed=n%2 and all(root[0]=='cbrt' for _,_,root in data)
    coordinate=('sqrt',base) if n==2 else ('cbrt',base) if signed and n==3 else ('rpow',base,q(1,n))
    if not signed and n%2 and any(root[0]=='cbrt' for _,_,root in data):
        raise Unsupported('Mixed signed and principal roots need an explicit convention')
    X=m.div(m.add(m.power(t,n),q(-b)),q(a));jac=m.div(m.mul(q(n),m.power(t,n-1)),q(a))
    extra={root:m.power(t,int(n*e)) for _,e,root in data}
    return coordinate,X,extra,jac,[] if signed else [('nonnegative',t)],dict(common_degree=n),[
        'Use the least common multiple of the root degrees and substitute the corresponding power of the new coordinate.',
        'The positive branch or signed odd-root branch covers the original interval. Check each original restriction before cancelling a common factor.',
        'If the inverse derivative vanishes at a regular original point, continuity and the mean-value theorem extend the primitive there.',
    ]


def monomial_degree(f,x,root):
    if f==x:return F(1),1,0
    if f==root:return F(1),0,1
    if f[0]=='pow':
        c,k,d=monomial_degree(f[1],x,root)
        return c**f[2],k*f[2],d*f[2]
    if f[0] in ('mul','div'):
        c,k,d=monomial_degree(f[1],x,root);e,l,j=monomial_degree(f[2],x,root)
        return (c*e,k+l,d+j) if f[0]=='mul' else (c/e,k-l,d-j)
    if f[0]=='q':return m.num(f),0,0
    raise Unsupported('A homogeneous monomial in the coordinate and the principal root is required')


def normalized_radical_family(t,s,c,k,d,method):
    """Lower monomial numerators with the differentiated product x^j sqrt Q."""
    from math import comb
    r=m.add(q(c),m.mul(q(s),m.power(t,2)));w=('sqrt',r)
    if d==-4 and k==0 and s==c==1:
        result=m.div(m.add(m.div(t,r),('atan',t)),q(2))
        recurrence='differentiate x/(1+x²), then add the arctangent seed'
    elif d==-3 and k==0:
        result=m.div(t,m.mul(q(c),w))
        recurrence='differentiate x/sqrt Q, where Q−x Q′/2=c'
    elif d>=-1 and d%2:
        seed=('asin',t) if s==-1 else ('ln',('abs',m.add(t,w)))
        moments=[seed,m.div(w,q(s))]
        n=(d+1)//2;top=k+2*n
        for j in range(2,top+1):
            moments.append(m.div(m.add(m.mul(m.power(t,j-1),w),
                                        m.mul(q(-(j-1)*c),moments[j-2])),q(j*s)))
        result=ZERO
        for j in range(n+1):
            result=m.add(result,m.mul(q(comb(n,j)*c**(n-j)*s**j),moments[k+2*j]))
        recurrence='J_j= integral x^j/sqrt Q. Differentiating x^(j-1) sqrt Q gives j*s J_j + (j-1)*c J_(j-2) after integration.'
    else:return None
    if method=='hyperbolic_substitution':
        if s<0:return None
        chart=('sinh','cosh') if c>0 else ('signed cosh','sinh')
    elif method=='trigonometric_substitution':
        chart=('sin','cos') if s<0 else ('tan','sec') if c>0 else ('signed sec','tan')
    else:chart=('quadratic recurrences',)
    intervals=('all real coordinates' if s==c==1 else
        ('[-1,1]' if d>0 else '(-1,1)') if s<0 else
        ('(-inf,-1] and [1,+inf)' if d>0 else '(-inf,-1) and (1,+inf)'))
    return dict(representative=result,real_domain=intervals,canonical_chart=chart,recurrence=recurrence)


def scaled_fractional_radical(f,root,x,t,scale,method,request):
    from integrals import family,integrate_child
    from verify import same_value
    if root[1][0]!='div' or method not in ('trigonometric_substitution','hyperbolic_substitution'):
        raise Unsupported('The assigned method needs a fractional-linear square root')
    num,den=root[1][1:]
    if domain_conditions(num) or domain_conditions(den):
        raise Unsupported('The original affine forms must be real at every finite point')
    coef,k,d=monomial_degree(f,x,root)
    if not coef or k<0 or d<1 or max(k,d)>16:
        raise Unsupported('A regular polynomial weight and positive root order are needed')
    normalized=m.substitute(root[1],{x:m.mul(scale,t)})
    P,Q=rf(m.simplify(normalized),t[1])
    if len(P)>2 or len(Q)>2:raise Unsupported('The scaled radicand is not fractional linear')
    b,a=(*P,*([F(0)]*(2-len(P))));e,c=(*Q,*([F(0)]*(2-len(Q))))
    det=a*e-b*c
    if not det:raise Unsupported('A degenerate fractional-linear map has no inverse')
    if method=='hyperbolic_substitution' and (not c or a!=c):
        raise Unsupported('The unit level must be excluded from both source sheets')
    T=m.power(t,2)
    divisor=m.add(m.mul(q(c),T),q(-a))
    u=m.div(m.add(q(b),m.mul(q(-e),T)),divisor)
    jac=m.div(m.mul(q(2*det),t),m.power(divisor,2))
    reconstructed=m.div(m.add(m.mul(q(a),u),q(b)),m.add(m.mul(q(c),u),q(e)))
    if not same_value(reconstructed,T):raise Unsupported('The inverse does not reproduce the original root level')
    u_top,u_den=rf(u,t[1]);j_top,j_den=rf(jac,t[1])
    delta=pa(pm(quotient_derivative_numerator(u_top,u_den),j_den),
             tuple(-z for z in pm(j_top,pm(u_den,u_den))))
    if any(delta):raise Unsupported('The inverse derivative was not verified')
    if method=='trigonometric_substitution':
        angle=dict(branch='0<=θ<π/2',coordinate='t=tan θ',derivative='dt/dθ=1+t²')
    else:
        angle=dict(branches=[('0<=t<1','t=tanh θ for θ>=0'),('t>1','t=coth θ for θ>0')],
                   derivative='dt/dθ=1-t² on each sheet')
    reduced=m.mul(q(coef),m.mul(m.mul(m.power(u,k),m.power(t,d)),jac))
    H=integrate_child(request,reduced,t[1])
    result=m.mul(m.power(scale,k+1),m.substitute(H,{t:root}))
    region=dict(coordinate=root,range='t>=0 and chart denominator!=0',inverse=m.mul(scale,u),
                simultaneous_source_guards=domain_conditions(f))
    return dict(theorem='method.scaled_radical_primitive',chart='radical_scale',angular_coordinate=angle,
                inverse=m.mul(scale,u),inverse_jacobian=m.mul(scale,jac),kernel=reduced,argument=[
        'Разбираем дробно-линейный подкоренной множитель после положительного масштабирования.',
        'Берём требуемую угловую или гиперболическую замену на действительных ветвях. В её тангенсе дифференциал рационален.',
        'Нули исходного делителя и полюс обратной карты сохраняем. У нуля корня производная совпадает по непрерывности исходного ядра.',
    ]),family(f,result,region=region)


def scaled_radical_primitive(task,request):
    from integrals import learned_nodes
    from verify import same_value
    v,name,method,f=chart_source(task,CHART_METHODS|{'quadratic_radical_polynomial_reduction'})
    params=task['parameters'];facts=task.get('stated_conditions',[])
    x=('v',v);t=('v',name);X=m.power(x,2)
    known_positive=facts==[n+'>0' for n in params]
    if len(params) not in (1,2) or (facts and not known_positive) or len(set(params+[v]))!=len(params)+1:
        raise Unsupported('The original parameter signs need separate proof')
    roots=list(dict.fromkeys(z for z in learned_nodes(f) if isinstance(z,tuple) and z[0]=='sqrt'))
    root=roots[0] if len(roots)==1 else None
    if not roots and f[0]=='div' and f[2][0]=='pow' and type(f[2][2]) is int:
        # View the integer power Q^j as a power 2j of its nonnegative root.
        root=('sqrt',f[2][1]);body=('div',f[1],('pow',root,2*f[2][2]))
    else:body=f
    if root is None:raise Unsupported('One parameter-dependent quadratic root is required')
    if known_positive and len(params)==1 and root[1][0]=='div' and method in ('trigonometric_substitution','hyperbolic_substitution'):
        from polynomial import NotRational,Undefined
        try:return scaled_fractional_radical(f,root,x,t,('s',params[0]),method,request)
        except (NotRational,Undefined) as exc:raise Unsupported('No exact fractional-linear inverse was verified') from exc
    coefficient,k,d=monomial_degree(body,x,root)
    if not d or k<0:raise Unsupported('A nonnegative polynomial weight and a nonzero root degree are required')
    A=('s',params[0]);center=ZERO
    if len(params)==2:
        B=('s',params[1]);difference=m.add(B,m.neg(A));scale=m.div(('abs',difference),q(2))
        unequal=params[0]+'!='+params[1];zero=params[0]+'='+params[1]
        if k:raise Unsupported('A shifted polynomial weight is not homogeneous')
        if same_value(root[1],m.mul(m.add(x,m.neg(A)),m.add(B,m.neg(x)))):
            center=m.div(m.add(A,B),q(2));cases=[(unequal,-1,1,scale)]
            zero_slope=-1
        elif same_value(root[1],m.mul(m.add(x,A),m.add(x,B))):
            center=m.neg(m.div(m.add(A,B),q(2)));cases=[(unequal,1,-1,scale)]
            zero_slope=1
        elif d==1 and same_value(root[1],m.mul(m.add(x,m.neg(A)),difference)) and method=='trigonometric_substitution':
            answer=m.div(m.mul(q(2*coefficient,3),m.power(root,3)),difference)
            plan=dict(chart='radical_scale',theorem='method.scaled_radical_primitive',argument=[
                'For a nonzero slope let the signed displacement from the linear root be tan²(u), u≥0.',
                'The nonnegative square root equals the positive square root of the absolute slope times tan(u).',
                'Substitution gives the derivative of 2Q^(3/2)/(3 slope). At zero slope the source is identically zero.',
            ])
            return plan,dict(original_domain=('and',domain_conditions(f)),family='F|J + C_J',parameter_cases=[
                dict(condition=unequal,representative=answer,components='the closed half-line Q≥0'),
                dict(condition=zero,representative=q(0),components='all real x')])
        else:raise Unsupported('The two source parameters do not give a symmetric pair of roots')
    else:
        scale=A if known_positive else ('abs',A)
        zero=params[0]+'=0'
        unequal='all stated parameters' if known_positive else params[0]+'!=0'
        if same_value(root[1],m.add(m.power(A,2),X)):cases=[(unequal,1,1,scale)];zero_slope=1
        elif same_value(root[1],m.add(m.power(A,2),m.neg(X))):cases=[(unequal,-1,1,scale)];zero_slope=-1
        elif same_value(root[1],m.add(A,X)):
            cases=[(params[0]+'>0',1,1,('sqrt',A))]
            if not known_positive:cases.append((params[0]+'<0',1,-1,('sqrt',m.neg(A))))
            zero_slope=1
        else:raise Unsupported('The original quadratic does not have a parameter scale that can be removed')
    power=k+d+1;branches=[];normalizations=[]
    coords=m.add(x,m.neg(center))
    for condition,slope,offset,scale in cases:
        rad=m.add(q(offset),m.mul(q(slope),m.power(t,2)))
        normalized=m.mul(m.power(t,k),m.power(('sqrt',rad),d))
        need=method if method in ('trigonometric_substitution','hyperbolic_substitution','quadratic_radical_polynomial_reduction') else 'table_and_rules'
        val=normalized_radical_family(t,slope,offset,k,d,need)
        if val is None:
            goal=dict(kind='integrate',variable=name,integrand=source(normalized),method_requirement=need,
                      requested_output=['primitive_family','natural_domain_components','constant_per_component'])
            val=request('primitive of normalized root differential '+condition,goal)['value']
        forward=m.div(coords,scale)
        H=m.substitute(freeze(val['representative']),{t:forward})
        representative=m.mul(m.mul(q(coefficient),m.power(scale,power)),H)
        branches.append(dict(condition=condition,representative=representative,
                             components=val.get('real_domain') or val['original_domain'],
                             x_from_coordinate=m.add(center,m.mul(scale,t))))
        normalizations.append(dict(condition=condition,scale=scale,coordinate=forward,pullback=normalized,radicand=rad,
                                   canonical_chart=val.get('canonical_chart'),recurrence=val.get('recurrence')))
    if len(params)==2 or not known_positive:
        if zero_slope<0:
            branches.append(dict(condition=zero,components='no open component',
                                 isolated_source_points=[center] if d>0 else []))
        else:
            absolute=('abs',coords)
            if power:
                answer=m.mul(q(coefficient/power),m.mul(m.power(coords,k+1),m.power(absolute,d)))
                if d<0 and k+d>=0:
                    # The excluded source point is not restored by the formula.
                    components='two open rays separated by the original root'
                else:components='all reals' if d>0 else 'two open rays separated by the original root'
            else:
                answer=m.mul(q(coefficient),m.mul(m.power(m.div(coords,absolute),k+1),('ln',absolute)))
                components='two open rays separated by the original root'
            branches.append(dict(condition=zero,representative=answer,components=components))
    value=dict(original_domain=('and',domain_conditions(f)),family='F|J + C_J',parameter_cases=branches,
               constant_policy='one independent constant per original component and fixed parameter tuple')
    if len(branches)==1:
        value.update(representative=branches[0]['representative'],real_domain=branches[0]['components'])
    return dict(chart='radical_scale',theorem='method.scaled_radical_primitive',normalizations=normalizations,
                argument=['Separate each zero or sign branch before normalizing the quadratic.',
                          'Translate to the center and scale by the positive radius. The root contributes the same positive scale.',
                          'Replay the verified normalized primitive with its required method and transport every original component.']),value


def radical_coordinate_primitive(task,request,chart):
    """Verify an algebraic chart and replay an ordinary rational primitive."""
    from graphs import domain_partition
    from integrals import learned_nodes,polynomial_expression
    from polynomial import pgcd,NotRational,Undefined
    if chart==CHARTS[3]:return scaled_radical_primitive(task,request)
    if chart==CHARTS[4]:return power_kernel_parts(task)
    v,name,method,f=chart_source(task,CHART_METHODS)
    if task.get('parameters') or task.get('stated_conditions'):
        raise Unsupported('A free parameter needs a sign and component proof')
    x=('v',v);t=('v',name)
    roots=list(dict.fromkeys(z for z in learned_nodes(f) if isinstance(z,tuple) and z[0] in ('sqrt','cbrt','rpow')))
    try:
        if chart==CHARTS[0]:
            coord,X,images,jac,limits,proof,argument=conic_chart(f,v,t,method,roots)
        elif chart==CHARTS[1]:
            coord,X,images,jac,limits,proof,argument=paired_radicals(f,v,t,roots)
        else:
            coord,X,images,jac,limits,proof,argument=common_power_chart(f,v,t,roots)
        def pull(e):return m.substitute(e,{x:X,**images})
        for node,image in images.items():
            exponent=F(1,2) if node[0]=='sqrt' else F(1,3) if node[0]=='cbrt' else m.num(m.simplify(node[2]))
            if any(rf(m.add(m.power(pull(node[1]),exponent.numerator),m.neg(m.power(image,exponent.denominator))),name)[0]):
                raise Unsupported('The chart changes an original algebraic generator')
        px,dx=rf(X,name);pj,dj=rf(jac,name)
        if any(pa(pm(quotient_derivative_numerator(px,dx),dj),tuple(-r for r in pm(pj,pm(dx,dx))))):
            raise Unsupported('The displayed Jacobian is not the derivative of the inverse coordinate')
        guards=domain_conditions(f)
        intrinsic={r[1] for r in images if r[0]=='sqrt'}
        def pull_guard(rel,e):
            if rel=='nonnegative' and e in intrinsic:return
            if rel=='nonzero':
                if e[0] in ('mul','div'):
                    for child in e[1:]:yield from pull_guard(rel,child)
                    return
                if e[0]=='pow':
                    yield from pull_guard(rel,e[1])
                    return
                if e in images and e[0]=='sqrt':
                    yield 'positive',images[e]
                    return
                if e[0]=='add' and any(m.num(z) is not None and m.num(z)>0 and other in images and other[0]=='sqrt'
                                       for z,other in (e[1:],tuple(reversed(e[1:])))):
                    return
                try:p0,d0=rf(e,v)
                except (NotRational,Undefined):pass
                else:
                    if len(d0)==1 and len(p0)<=3 and (len(p0)==1 and p0[0]
                            or len(p0)==3 and p0[1]**2<4*p0[0]*p0[2]):return
            yield rel,pull(e)
        induced=[g for rel,e in guards for g in pull_guard(rel,e)]
        extra=[g for e in (X,jac,*images.values()) for g in domain_conditions(e)]
        partition,domain=domain_partition(name,[*limits,*induced,*extra],simplify_guards=True)
        if not any(partition['open_cells']):raise Unsupported('No open component survives the original real restrictions')
        p,d=rf(m.mul(pull(f),jac),name);g=pgcd(p,d)
        reduced=m.div(polynomial_expression(pdiv(p,g)[0],name),polynomial_expression(pdiv(d,g)[0],name))
    except (NotRational,Undefined) as exc:raise Unsupported('Rationality or the exact chart-domain partition remains unproved') from exc
    target=dict(kind='integrate',variable=name,integrand=source(reduced),requested_output=['primitive_family'])
    H=freeze(request('rational primitive in the verified chart',target)['value']['representative'])
    answer=m.substitute(H,{t:coord})
    plan=dict(theorem='method.real_radical_coordinate',chart=chart,coordinate=coord,inverse=X,radical_images=list(images.items()),
              jacobian=jac,domain_partition=partition,image_components=domain,rational_differential=reduced,
              argument=argument,**proof)
    return plan,dict(representative=answer,original_domain=('and',guards),
                     real_domain=dict(coordinate=name,intervals=domain,image=X),
                     identity=dict(derivative_ast=f,integrand_ast=f),family='F|J + C_J',
                     constant_policy='independent real C_J on each original connected component, for fixed source parameters')


def power_kernel_parts(task):
    """Repeated integration by parts on a polynomial in the appropriate coordinate."""
    from integrals import learned_nodes
    from math import factorial
    v,_,method,f=chart_source(task,{'table_and_rules','integration_by_parts'})
    params=task.get('parameters',[]);facts=task.get('stated_conditions',[])
    x=('v',v);log=('ln',x)
    nodes=list(learned_nodes(f))
    guards=domain_conditions(f)
    family=dict(original_domain=('and',guards),family='F|J + C_J',
                constant_policy='one independent constant per original component and fixed parameter tuple')
    plan=dict(theorem='method.power_kernel_parts',chart='parts_power_kernel')
    if log in nodes:
        if len(params)>1 or facts and (not params or facts!=[params[0]+'!=1']):
            raise Unsupported('A parameter restriction beyond the original log-power branches is unresolved')
        ctx=m.context(dict(variable=v,parameters=params))
        def degrees(e):
            if e==x:return F(1),ONE,0
            if e==('sqrt',x):return F(1),q(1,2),0
            if e==log:return F(1),ZERO,1
            if e[0]=='q':return m.num(e),ZERO,0
            if e[0]=='rpow' and e[1]==x and m.constant_defined(e[2],ctx):return F(1),e[2],0
            if e[0]=='pow':
                c,a,j=degrees(e[1]);n=e[2]
                return c**n,m.mul(q(n),a),j*n
            if e[0] in ('div','mul'):
                c,a,j=degrees(e[1]);d,b,k=degrees(e[2])
                return (c*d,m.add(a,b),j+k) if e[0]=='mul' else (c/d,m.add(a,m.neg(b)),j-k)
            raise Unsupported('The source is not a log power times a monomial')
        c,a,n=degrees(f);alpha=m.simplify(m.add(a,ONE))
        if n<1 or any(g[0]=='nonzero' and m.contains(g[1],log) for g in guards):
            raise Unsupported('The required logarithm power and original positive domain are unresolved')
        singular=m.mul(q(c/(n+1)),m.power(log,n+1))
        regular=ZERO;terms=[]
        if alpha!=ZERO:
            for j in range(n+1):
                weight=q(F((-1)**j*factorial(n),factorial(n-j)))
                term=m.div(m.mul(weight,m.power(log,n-j)),m.power(alpha,j+1))
                terms.append(term);regular=m.add(regular,term)
            exponent=m.num(alpha)
            weight=m.power(x,int(exponent)) if exponent is not None and exponent.denominator==1 else ('rpow',x,alpha)
            regular=m.mul(m.mul(q(c),weight),regular)
        plan.update(exponent=a,log_power=n,recurrence_terms=terms,argument=[
            'Take u=(ln x)^n and dv=x^a dx. The original logarithm requires x>0.',
            'For a+1 nonzero, integration by parts lowers n by one. End the recurrence with the power integral.',
            'For a+1=0 take v=ln x. The residual is n times the original integral, giving (ln x)^(n+1)/(n+1).',
        ])
        if params and any(m.contains(a,('s',p)) for p in params):
            family['parameter_cases']=[dict(condition=source(alpha)+'!=0',representative=regular,components='x>0'),
                                       dict(condition=source(alpha)+'=0',representative=singular,components='x>0')]
        else:family.update(representative=singular if alpha==ZERO else regular,real_domain='x>0')
        return plan,family
    if params or facts:raise Unsupported('Exponential moments need a proved nonzero rate')
    waves=list(dict.fromkeys(z for z in nodes if isinstance(z,tuple) and z[0]=='exp'))
    if len(waves)!=1:raise Unsupported('One exponential generator is needed')
    wave,=waves
    c,k,d=monomial_degree(f,x,wave)
    p,e=rf(wave[1],v)
    n=len(p)-1
    if d!=1 or n<1 or len(e)!=1 or any(p[:-1]) or not p[-1] or k<0 or (k+1)%n or guards:
        raise Unsupported('The source differential is not a whole polynomial moment in the exponential coordinate')
    j=(k+1)//n-1
    if method=='integration_by_parts' and j==0:raise Unsupported('The required reduction needs a nonconstant polynomial factor')
    rate=p[-1]/e[0];u=m.power(x,n);series=ZERO;terms=[]
    for i in range(j+1):
        weight=F((-1)**i*factorial(j),factorial(j-i))/rate**(i+1)
        term=m.mul(q(weight),m.power(u,j-i));terms.append(term);series=m.add(series,term)
    answer=m.mul(q(c/n),m.mul(series,wave))
    plan.update(coordinate=u,degree=j,rate=q(rate),recurrence_terms=terms,
                argument=['Move the monomial differential to a polynomial in the exponent coordinate.',
                          'Integrate the polynomial times the exponential by parts, lowering its degree by one.',
                          'The reconstructed primitive is differentiable at stationary points of the substitution as well.'])
    family.update(representative=answer,real_domain='all real x')
    return plan,family
