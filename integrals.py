"""General primitive compilation through the existing derivative Engine/replay.

No exercise registry, controls, parser, derivative tables or arithmetic engine.
"""
from fractions import Fraction
from contextvars import ContextVar
from itertools import chain
from math import comb
from time import perf_counter
import re
import expressions as m
import radical_primitives as radicals
from model import Unsupported, ZERO, ONE, q, freeze, canonical, match, instantiate
from polynomial import (rf, pa, pdiv, pgcd, pm, trim, valuation, proper_factor, span_coefficients, univariate_coefficients,
                        composition_coefficients, quotient_derivative_numerator, NotRational, Undefined, ResourceBound)
from tasks import source, guard_source, domain_conditions, known_guard, compile_derivative, entailed_domain_guards
from operations import version, CONTINUOUS_FUNCTIONS

METHODS = {'table_and_rules','elementary_table_and_algebra','elementary_table_and_affine_change','appropriate_integrand_transformation','integration_by_parts','rational_decomposition','product_to_sum','integrand_decomposition','appropriate_substitution'}
QUADRATIC_METHOD = 'quadratic_canonical_form'
METHODS.add(QUADRATIC_METHOD)
HERMITE_METHOD='ostrogradsky_reduction'
METHODS.add(HERMITE_METHOD)
METHODS.update(radicals.REQUIREMENTS)


def unique(values):
    return tuple({canonical(v): freeze(v) for v in values}.values())


def affine(e, variable):
    if not m.variable_in(e, variable): return ZERO, e
    if e == ('v', variable): return ONE, ZERO
    if e[0] == 'add':
        a,b = affine(e[1],variable); c,d = affine(e[2],variable)
        return m.add(a,c), m.add(b,d)
    if e[0] == 'mul':
        fixed, other = (e[1],e[2]) if not m.variable_in(e[1],variable) else (e[2],e[1])
        if not m.variable_in(fixed,variable):
            a,b = affine(other,variable); return m.mul(fixed,a),m.mul(fixed,b)
    if e[0] == 'div' and not m.variable_in(e[2],variable):
        a,b = affine(e[1],variable); return m.div(a,e[2]),m.div(b,e[2])
    raise Unsupported('No affine argument')


def power_form(e, variable):
    if e[0] == 'pow':
        base,p,guards = power_form(e[1],variable); return base,p*e[2],guards
    if e[0] in ('sqrt','cbrt'):
        base,p,guards = power_form(e[1],variable)
        return (base,p/2,guards+(('positive',base),)) if e[0]=='sqrt' else (base,p/3,guards)
    try:
        affine(e,variable)
        return e,Fraction(1),()
    except Unsupported:pass
    if e[0] in ('mul','div'):
        other,k,guards=power_form(e[2],variable)
        if e[0]=='div':k=-k
        if e[1]==ONE:return other,k,guards
        base,p,more=power_form(e[1],variable)
        if base!=other:raise Unsupported('Distinct bases in power product')
        return base,p+k,more+guards
    raise Unsupported('No supported common power base')


def propose(e, variable, depth=0):
    """A bounded candidate only. Later domain and derivative checks are mandatory."""
    if depth > 10: raise Unsupported('Primitive proposal recursion bound')
    fixed = lambda x: not m.variable_in(x,variable)
    recur = lambda x: propose(x,variable,depth+1)
    if fixed(e): return m.mul(e,('v',variable)),()
    if e[0] == 'add':
        a,g = recur(e[1]); b,h = recur(e[2]); return m.add(a,b),unique(g+h)
    if e[0] == 'mul' and (fixed(e[1]) or fixed(e[2])):
        c,u = (e[1],e[2]) if fixed(e[1]) else (e[2],e[1])
        F,g = recur(u); return m.mul(c,F),g
    if e[0] == 'div' and fixed(e[2]):
        F,g = recur(e[1]); return m.div(F,e[2]),g
    if e[0]=='ln':
        u=e[1];slope,_=affine(u,variable)
        return m.div(m.mul(u,m.add(e,q(-1))),slope),(('positive',u),('nonzero',slope))
    if e[0]=='div' and fixed(e[1]) and e[2][0]=='sqrt':
        try:p,d=rf(e[2][1],variable)
        except (NotRational,Undefined):p,d=(),()
        if len(p)==3 and len(d)==1 and p[2]/d[0]<0:
            c,b,a=(v/d[0] for v in p);center=-b/(2*a);height=c+b*center/2
            if height>0:
                argument=m.mul(m.simplify(('sqrt',q(-a/height))),m.add(('v',variable),q(-center)))
                return m.div(m.mul(e[1],('asin',argument)),m.simplify(('sqrt',q(-a)))),()
    if e[0] in ('exp','sin','cos','sinh','cosh'):
        a,_ = affine(e[1],variable)
        F = {'exp':e,'sin':m.neg(('cos',e[1])),'cos':('sin',e[1]),
             'sinh':('cosh',e[1]),'cosh':('sinh',e[1])}[e[0]]
        return m.div(F,a),(('nonzero',a),)
    if e[0] == 'rpow' and fixed(e[1]):
        a,_ = affine(e[2],variable); denominator = m.mul(a,('ln',e[1]))
        return m.div(e,denominator),(('positive',e[1]),('nonzero',denominator))
    if e[0] == 'pow' and e[2] == 2 and e[1][0] in ('tan','cot','tanh'):
        fn,u = e[1]; a,_ = affine(u,variable)
        F = {'tan':m.add(('tan',u),m.neg(u)), 'cot':m.add(m.neg(('cot',u)),m.neg(u)),
             'tanh':m.add(u,m.neg(('tanh',u)))}[fn]
        return m.div(F,a),(('nonzero',a),)
    if e[0] == 'div' and fixed(e[1]) and e[2][0] == 'pow' and e[2][2] == 2 and e[2][1][0] in ('sinh','cosh'):
        fn,u = e[2][1]; a,_ = affine(u,variable)
        F = ('tanh',u) if fn == 'cosh' else m.neg(('div',('cosh',u),('sinh',u)))
        return m.div(m.mul(e[1],F),a),(('nonzero',a),)
    try:
        p,d = rf(e,variable)
        if d == (Fraction(1),) and len(p) <= 25:
            F = ZERO
            for n,c in enumerate(p):
                if c: F = m.add(F,m.mul(q(c/Fraction(n+1)),('pow',('v',variable),n+1)))
            return F,()
        if len(p)==1 and len(d)==3:
            center=m.add(('v',variable),q(d[1]/(2*d[2])))
            residual=d[0]-d[1]**2/(4*d[2])
            if not residual:return m.div(q(-p[0]/d[2]),center),(('nonzero',center),)
            beta=d[2]/residual;scale=m.simplify(('sqrt',q(abs(beta))))
            u=m.mul(scale,center)
            if beta>0:return m.mul(q(p[0]/residual),m.div(('atan',u),scale)),()
            plus,minus=m.add(ONE,u),m.add(ONE,m.neg(u))
            logs=m.add(('ln',('abs',plus)),m.neg(('ln',('abs',minus))))
            F=m.div(logs,m.mul(q(2),scale))
            return m.mul(q(p[0]/residual),F),(('nonzero',plus),('nonzero',minus))
        quotient,remainder = pdiv(p,d)
        if any(quotient) and len(quotient) <= 25:
            Q,g = recur(polynomial_expression(quotient,variable))
            R,h = recur(('div',polynomial_expression(remainder,variable),polynomial_expression(d,variable))) if any(remainder) else (ZERO,())
            return m.add(Q,R),unique(g+h)
    except (NotRational,Undefined): pass
    try:
        numerator,u,sign = (e[1],e[2],-1) if e[0] == 'div' and fixed(e[1]) else (ONE,e,1)
        base,p,guards = power_form(u,variable); p *= sign; a,_ = affine(base,variable)
        if p == -1: F = ('ln',('abs',base))
        elif (p+1).denominator == 1: F = m.div(('pow',base,int(p+1)),q(p+1))
        elif (p+1).denominator == 2: F = m.div(('pow',('sqrt',base),(p+1).numerator),q(p+1))
        elif (p+1).denominator == 3: F = m.div(('pow',('cbrt',base),(p+1).numerator),q(p+1))
        else: raise Unsupported('Power convention not covered')
        return m.div(m.mul(numerator,F),a),unique(guards+(('nonzero',a),))
    except Unsupported: pass
    simple = m.simplify(e)
    if simple != e: return recur(simple)
    raise Unsupported('No supported primitive proposal')


TRANSFORMATION_METHODS = {'table_and_rules','appropriate_integrand_transformation'}
SUBSTITUTION_METHODS = TRANSFORMATION_METHODS|{'appropriate_substitution'}


PARTS_METHODS = {'integration_by_parts','table_and_rules'}
RECIPE_REQUIRED = {'appropriate_integrand_transformation','integration_by_parts','rational_decomposition','product_to_sum','integrand_decomposition','appropriate_substitution'}
RECIPE_REQUIRED.update({QUADRATIC_METHOD,HERMITE_METHOD})
RECIPE_REQUIRED.update(radicals.REQUIREMENTS)
PLAN_FAILURES = (Unsupported, NotRational, Undefined, ResourceBound, ZeroDivisionError)


def polynomial_expression(coefficients,variable):
    return m.poly_expr({() if n==0 else ((('v',variable),n),):c for n,c in enumerate(coefficients) if c})


def hermite_reduction(f,variable,max_degree):
    """Write P/D = H' + V/S where S is square-free; no factorisation into linear factors."""
    p,d=rf(f,variable)
    common=pgcd(p,d);p=pdiv(p,common)[0];d=pdiv(d,common)[0]
    if len(d)-1>max_degree or len(p)-1>max_degree:raise Unsupported('Hermite coefficient system exceeds the rational degree allowance')
    def derivative(poly):return tuple(i*c for i,c in enumerate(poly) if i) or (Fraction(0),)
    g=pgcd(d,derivative(d));s=pdiv(d,g)[0]
    if len(g)<2:raise Unsupported('The reduced source denominator has no repeated factor')
    polynomial,remaining=pdiv(p,d)
    # Multiply the equation (U/g)' + V/s = remaining/d by d*g².
    monomial=lambda i:(Fraction(0),)*i+(Fraction(1),)
    cols=[pm(d,quotient_derivative_numerator(monomial(i),g)) for i in range(len(g)-1)]
    g3=pm(g,pm(g,g))
    cols.extend(pm(g3,monomial(i)) for i in range(len(s)-1))
    weights=span_coefficients(pm(remaining,pm(g,g)),cols)
    if weights is None:raise Unsupported('No exact Hermite reduction')
    split=len(g)-1
    u,v=weights[:split],weights[split:] or (Fraction(0),)
    integrated=(Fraction(0),*(c/(i+1) for i,c in enumerate(polynomial)))
    h=pa(pm(integrated,g),u)
    if (pm(p,pm(g,g))!=pa(pm(d,quotient_derivative_numerator(h,g)),pm(g3,v))
            or len(pgcd(s,derivative(s)))!=1):
        raise Unsupported('Hermite identity or square-free check failed')
    expr=lambda z:polynomial_expression(z,variable)
    return {'rational_part':m.div(expr(h),expr(g)),'remainder':m.div(expr(v),expr(s)),
            'repeated_part':expr(g),'squarefree_denominator':expr(s),'original_domain':domain_conditions(f)}


def rational_algebraic_part(task,library):
    allowed={'id','source','kind','integrand','variable','requested_output'}
    if (not library.data.get(HERMITE_METHOD) or set(task)-allowed or task.get('requested_output')!=['rational_part_of_primitive']):
        raise Unsupported('Expected a rational-part goal without additional assumptions')
    variable=task.get('variable','x')
    try:plan=hermite_reduction(m.parse(task['integrand'],variable),variable,library.data['rational_primitive_plan']['max_degree'])
    except (NotRational,Undefined) as exc:raise Unsupported('Expected a defined rational expression') from exc
    return plan,{'rational_part':plan['rational_part'],'remaining_integrand':plan['remainder'],'original_domain':plan['original_domain']}


def rational_primitive_criterion(task,library):
    """A rational derivative has zero simple-pole coefficients, including at complex poles."""
    if (not library.data.get('rational_primitive_obstructions') or task.get('method_requirement') is not None
            or set(task)-{'id','kind','schema','source','integrand','variable','parameters','stated_conditions','requested_output'}
            or task.get('requested_output')!=['necessary_and_sufficient_parameter_condition']):
        raise Unsupported('Expected a necessary and sufficient criterion for a rational primitive')
    x,raw,ctx,_=guarded_input({**task,'kind':'integrate','requested_output':[]},{'table_and_rules'})
    if raw[0]!='div':raise Unsupported('Expected an original rational quotient')
    numerator,denominator=raw[1:]
    coeff=real_polynomial_coefficients(numerator,x[1],ctx)
    den=real_polynomial_coefficients(denominator,x[1],ctx)
    evidence={}
    if all(m.num(u) is not None for u in den):
        d=tuple(m.num(u) for u in den)
        if not any(d):raise Unsupported('The original denominator is identically zero')
        # Put all monomial remainders over the same square-free denominator.
        squarefree=pdiv(d,pgcd(d,tuple(i*c for i,c in enumerate(d) if i) or (Fraction(0),)))[0]
        sums=[ZERO]*(len(squarefree)-1)
        terms=[]
        for degree,weight in enumerate(coeff):
            if weight==ZERO:continue
            mono=m.power(x,degree)
            p,base=rf(('div',mono,denominator),x[1]);g=pgcd(p,base)
            p=pdiv(p,g)[0];base=pdiv(base,g)[0]
            if len(pgcd(base,tuple(i*c for i,c in enumerate(base) if i) or (Fraction(0),)))>1:
                residue=hermite_reduction(('div',mono,denominator),x[1],8)['remainder']
            else:
                residue=m.div(polynomial_expression(pdiv(p,base)[1],x[1]),polynomial_expression(base,x[1]))
            r,s=rf(residue,x[1]);scale,extra=pdiv(squarefree,s)
            if any(extra):raise Unsupported('The Hermite residual denominator did not divide the square-free part')
            r=pm(r,scale)
            for i,c in enumerate(r[:len(sums)]):sums[i]=m.add(sums[i],m.mul(q(c),weight))
            if any(r[len(sums):]):raise Unsupported('Hermite residual is not a proper fraction')
            terms.append((degree,weight,residue))
        evidence={'squarefree_denominator':polynomial_expression(squarefree,x[1]),'monomial_residuals':terms}
        cases=[dict(when=(),zeros=tuple(m.simplify(u) for u in sums if m.simplify(u)!=ZERO))]
    elif denominator[0]=='pow' and denominator[2]==2 and len(coeff)<=3:
        c,b,a=(*real_polynomial_coefficients(denominator[1],x[1],ctx,2),ZERO,ZERO)[:3]
        C,B,A=(*coeff,ZERO,ZERO)[:3]
        disc=m.add(m.power(b,2),m.neg(m.mul(q(4),m.mul(a,c))))
        # For two distinct roots the rational part of a proper fraction is (u*x+v)/Q.
        # Matching the x² and x coefficients fixes u and v. The constant term is the only obstruction.
        defect=m.add(m.mul(a,C),m.add(m.mul(c,A),m.neg(m.div(m.mul(b,B),q(2)))))
        linear_defect=m.add(m.mul(b,B),m.neg(m.mul(q(2),m.mul(A,c))))
        cases=[dict(when=(('nonzero',a),('nonzero',disc)),zeros=(m.simplify(defect),)),
               dict(when=(('nonzero',a),('zero',disc)),zeros=()),
               dict(when=(('zero',a),('nonzero',b)),zeros=(m.simplify(linear_defect),)),
               dict(when=(('zero',a),('zero',b),('nonzero',c)),zeros=()),
               dict(when=(('zero',a),('zero',b),('zero',c)),undefined=True)]
        evidence={'quadratic_coefficients':(c,b,a),'discriminant':disc}
    else:raise Unsupported('Expected a fixed polynomial denominator or the square of a polynomial of degree at most two')
    feasible=[]
    for case in cases:
        if any((sign==0)!=(relation=='zero')
               for relation,u in case['when'] if (sign:=m.sign(u,ctx)) is not None):continue
        when=tuple((relation,u) for relation,u in case['when'] if m.sign(u,ctx) is None)
        feasible.append({**case,'when':when})
    return {'theorem':'method.rational_primitive_obstructions',**evidence},dict(cases=feasible,original_domain=domain_conditions(raw))


def partial_fraction_symmetry(task,library):
    token=r'[A-Za-z_]\w*'
    text=task.get('given','').replace('²','^2').replace(' ','')
    match=re.fullmatch(rf'({token})\(({token})\)=({token})\(\2\^2\),\3rational',text)
    if (not library.data.get('partial_fraction_reflection') or set(task)-{'id','kind','source','given','requested_output'}
            or task.get('requested_output')!=['properties of partial fractions'] or not match or len(set(match.groups()))!=3
            or task.get('source',{}).get('method_heading') not in (None,'Describe the structure of the partial fraction decomposition of an even rational function.')):
        raise Unsupported('Expected the decomposition of a rational function in a squared variable')
    R,x,G=match.groups()
    return dict(theorem='method.partial_fraction_reflection',source_function=R,coordinate=x,squared_argument_function=G,argument=[
        f'Подстановка −{x} сохраняет {x}² и исходную область, поэтому {R}(−{x})={R}({x}).',
        'Отражаем разложение на простые дроби. Единственность выделяет чётную полиномиальную часть, пары противоположных полюсов и возможный полюс в нуле.',
        'У противоположных полюсов совпадают кратности. Коэффициент при степени j умножается на (−1)^j. В нуле поэтому остаются только чётные степени.',
        'Над вещественными числами сопряжённые полюса объединяются. Для чётного неприводимого квадратичного знаменателя числитель постоянен. У пары отражённых квадратичных знаменателей числители получаются заменой x на −x.'
    ]),dict(polynomial_part='even',opposite_poles='equal multiplicities; coefficient at -p is (-1)^j times coefficient at p for order j',
            pole_at_origin='even orders only',real_quadratic_factors='reflected numerators for paired factors; constant numerator for each self-reflected factor')


def hermite_proposal(task,library):
    variable,_,_,f=integral_source(task)
    contract=library.data['rational_primitive_plan']
    plan=hermite_reduction(f,variable,contract['max_degree'])
    rest=plan['remainder'];candidate=plan['rational_part']
    if rest!=ZERO:
        child={'kind':'integrate','variable':variable,'integrand':source(rest),'method_requirement':'rational_decomposition'}
        reduced=rational_proposal(child,contract)
        candidate=m.add(candidate,m.parse(reduced['candidate_source'],variable))
        plan['residual_proposal']=reduced
    return {'candidate_source':source(candidate),'recipe':{'method':HERMITE_METHOD,**plan}}


def quadratic_proposal(task):
    """Put Q(u) into completed-square form; separate a multiple of Q' from the numerator."""
    x,_,_,f=integral_source(task)
    if f[0]=='div':
        numerator,den=f[1:]
        power=-1 if den[0]=='sqrt' else -2
        radicand=den[1] if power==-1 else den
    elif f[0]=='sqrt':
        numerator,radicand,power=ONE,f[1],1
    elif f[0]=='mul' and f[2][0]=='sqrt':
        numerator,radicand,power=f[1],f[2][1],1
    else:raise Unsupported('Expected a quadratic denominator or radical')
    coordinate=('v',x); independent=x
    transformed_Q=radicand; transformed_P=numerator
    if numerator in (('sin',coordinate),('cos',coordinate)):
        direct='sin' if numerator[0]=='cos' else 'cos'
        independent=kernel_symbol(task)
        t=('v',independent)
        transformed_P=ONE if direct=='sin' else q(-1)
        coordinate=(direct,coordinate)
        transformed_Q=m.substitute(radicand,{coordinate:t,('pow',numerator,2):m.add(ONE,m.neg(m.power(t,2)))})
    def polynomial(raw):
        n,d=rf(raw,independent)
        if len(d)!=1 or domain_conditions(raw):raise Unsupported('Expected an everywhere-defined polynomial')
        return tuple(v/d[0] for v in n)
    coeff=polynomial(transformed_Q);p=polynomial(transformed_P)
    degree=len(coeff)-1
    if degree<2 or degree%2:raise Unsupported('No quadratic after a monomial substitution')
    k=degree//2
    if any(v and i not in (0,k,2*k) for i,v in enumerate(coeff)):raise Unsupported('More than one quadratic coordinate')
    if any(v and i not in (k-1,2*k-1) for i,v in enumerate(p)):raise Unsupported('Numerator does not split into the derivative and a constant')
    c,b,a=coeff[0],coeff[k],coeff[2*k]
    m1=(p[2*k-1] if len(p)>=2*k else 0)/(2*k*a)
    m0=(p[k-1] if len(p)>=k else Fraction(0))/k-b*m1
    u=m.power(coordinate,k); Q=radicand
    z=m.add(m.mul(q(2*a),u),q(b)); delta=4*a*c-b*b
    sqrt=lambda v:m.simplify(('sqrt',v))
    logabs=lambda v:('ln',('abs',v))
    R=sqrt(Q)
    if power==-2:
        if delta>0:
            h=sqrt(q(delta));J=m.div(m.mul(q(2),('atan',m.div(z,h))),h)
        elif delta<0:
            h=sqrt(q(-delta));J=m.div(logabs(m.div(m.add(z,m.neg(h)),m.add(z,h))),h)
        else:J=m.div(q(-2),z)
        F=m.add(m.mul(q(m1),logabs(Q)),m.mul(q(m0),J))
    else:
        if a<0 and delta<0:
            # atan is defined throughout Q>0; choose asin on closed radical endpoints.
            angle=(('atan',m.div(z,m.mul(q(2),m.mul(sqrt(q(-a)),R)))) if power==-1
                   else ('asin',m.div(z,sqrt(q(-delta)))))
            J=m.neg(m.div(angle,sqrt(q(-a))))
        elif a>0 and delta:
            J=m.div(logabs(m.add(z,m.mul(q(2),m.mul(sqrt(q(a)),R)))),sqrt(q(a)))
        else:raise Unsupported('Degenerate quadratic or empty radical domain')
        if power==1:
            J=m.div(m.add(m.mul(z,R),m.mul(q(delta/2),J)),q(4*a))
        first=m.mul(q(2),R) if power==-1 else m.mul(q(2,3),m.mul(Q,R))
        F=m.add(m.mul(q(m1),first),m.mul(q(m0),J))
    return {'candidate_source':source(F),'recipe':{'method':QUADRATIC_METHOD,'coordinate':source(u),'quadratic':source(Q),
        'coefficients':[q(a),q(b),q(c)],'centered_numerator':source(z),'discriminant_complement':q(delta),
        'power_in_halves':power,'derivative_weight':q(m1),'constant_weight':q(m0)}}


def reciprocal_substitution(f,variable,symbol):
    """Find t=x+c/x when the rational differential f dx is invariant under x→c/x."""
    try:num,den=rf(f,variable)
    except (NotRational,Undefined):return None
    lowest=valuation(num)
    if lowest is None:return None
    pole=valuation(den);order=lowest-pole
    # If f~A*x^m at zero and f~B*x^n at infinity, invariance of f dx forces
    # m+n=-2 and c^(m+1)=-B/A. A simple pole does not determine c this way.
    tail_order=len(num)-len(den)
    if order+tail_order!=-2 or order==-1:return None
    head,tail=num[lowest]/den[pole],num[-1]/den[-1]
    ratio=-tail/head
    exponent=order+1
    if exponent<0:ratio,exponent=1/ratio,-exponent
    n=m.perfect_root(ratio.numerator,exponent);d=m.perfect_root(ratio.denominator,exponent)
    if n is None or d is None:return None
    root=Fraction(n,d)

    def reduce_pair(poly,c):
        # Horner reduction to a(t)+x*b(t) using x²=t*x−c.
        a=b=(Fraction(0),)
        for coefficient in reversed(poly):
            a,b=pa((coefficient,),pm((-c,),b)),pa(a,(0,*b))
        return a,b

    for c in ((root,) if exponent%2 else (-root,root)):
        p0,p1=reduce_pair((0,0,*num),c)
        q0,q1=reduce_pair(pm((-c,0,1),den),c)
        if pm(p0,q1)!=pm(p1,q0):continue
        # f/(dt/dx) is independent of x precisely when its two coefficients agree in ratio.
        p,r=(p0,q0) if any(q0) else (p1,q1)
        common=pgcd(p,r)
        kernel=m.div(polynomial_expression(pdiv(p,common)[0],symbol),
                     polynomial_expression(pdiv(r,common)[0],symbol))
        x=('v',variable)
        discovery={'at_zero':(q(head),order),'at_infinity':(q(tail),tail_order),'scale':q(c)}
        return ('add',x,('div',q(c),x)),kernel,discovery
    return None


def denominator_factors(expr, denominator, variable):
    """Propose exact factors, also recognizing a polynomial in one power of x."""
    factors = set()
    def offer(p):
        if len(p)<2: return
        p = tuple(c/p[-1] for c in p)
        if p in factors or any(pdiv(denominator,p)[1]): return
        factors.add(p)
        factor=proper_factor(p)
        for extra in reciprocal_factors(p):offer(extra)
        if factor is not None:
            quotient,rem=pdiv(p,factor)
            if not any(rem):offer(factor);offer(quotient)
    offer(denominator)
    pending=[expr]
    while pending:
        e=pending.pop()
        p,d=rf(e,variable)
        if len(d)==1: offer(p)
        pending.extend(c for c in e[1:] if isinstance(c,tuple))
    return sorted(factors,key=lambda p:(len(p),p))


def rational_component(form,variable,max_degree):
    """Reconstruct one proposed antiderivative and its denominator guards."""
    if not isinstance(form,(tuple,list)) or len(form) not in (2,3):
        raise Unsupported('Malformed rational primitive form')
    kind,u,*powers=freeze(form)
    p,d=rf(u,variable)
    if max(len(p),len(d))>max_degree+1: raise Unsupported('Rational component degree exceeded')
    if kind=='table' and not powers and (len(d)==1 or len(p)==1 and len(d)==3):
        primitive,guards=propose(u,variable)
        return u,primitive,guards
    if kind!='factor_power' or d!=(Fraction(1),) or len(p)<2 or len(powers)!=1:
        raise Unsupported('Unknown rational component')
    k,=powers
    if type(k) is not int or not 1<=k<=max_degree: raise Unsupported('Invalid rational factor exponent')
    derivative=polynomial_expression(tuple(i*c for i,c in enumerate(p) if i),variable)
    integrand=m.div(derivative,('pow',u,k))
    primitive=('ln',('abs',u)) if k==1 else m.div(('pow',u,1-k),q(1-k))
    return integrand,primitive,(('nonzero',u),)


def rational_proposal(task, contract):
    """Match the residual numerator against derivatives of reusable primitive forms."""
    variable,_,_,f=integral_source(task)
    numerator,denominator=rf(f,variable)
    if max(len(denominator),len(numerator))-1>contract['max_degree']:
        raise ResourceBound('Rational decomposition degree budget')
    algebraic_split=task.get('method_requirement') in ('integrand_decomposition','elementary_table_and_algebra')
    if len(denominator)==1 and not algebraic_split: raise Unsupported('No rational denominator to decompose')
    quotient,remainder=pdiv(numerator,denominator)
    columns=[]; forms=[]
    def offer(n,d,form):
        multiplier,rest=pdiv(denominator,d)
        if any(rest): return
        col=pm(n,multiplier)
        if col in columns: return
        columns.append(col)
        forms.append(form)
    for factor in denominator_factors(f,denominator,variable):
        g=polynomial_expression(factor,variable)
        derivative=tuple(k*c for k,c in enumerate(factor) if k)
        power=factor; k=1
        while len(power)<=len(denominator) and not any(pdiv(denominator,power)[1]):
            offer(derivative,power,('factor_power',g,k))
            k+=1;power=pm(power,factor)
        if len(factor)==3:
            offer((Fraction(1),),factor,('table',('div',ONE,g)))
    weights=span_coefficients(remainder,columns)
    if weights is None: raise Unsupported('Residual numerator outside span of available primitive forms')
    selected=[(q(w),form) for w,form in zip(weights,forms) if w]
    if any(quotient) and algebraic_split:
        terms=[(q(c),('table',m.power(('v',variable),i))) for i,c in enumerate(quotient) if c]
        selected=terms+selected
    elif any(quotient):
        u=polynomial_expression(quotient,variable)
        selected.insert(0,(ONE,('table',u)))
    if not selected: raise Unsupported('No nonzero term in rational decomposition')
    candidate=ZERO;terms=[]
    for w,form in selected:
        u,F,_=rational_component(form,variable,contract['max_degree'])
        terms.append({'weight':w,'form':form,'integrand':u,'primitive':F})
        candidate=m.add(candidate,m.mul(w,F))
    return {'candidate_source':source(candidate),
            'recipe':{'method':'rational_decomposition','terms':terms}}


def polynomial_affine_kernels(f,variable):
    """Identify a rational polynomial factor and one affine elementary kernel on the raw expression."""
    factors = []
    def collect(e):
        if e[0]=='mul': collect(e[1]);collect(e[2])
        else: factors.append(e)
    collect(f)
    for position,kernel in enumerate(factors):
        if kernel[0] not in ('exp','sin','cos','sinh','cosh'): continue
        raw_polynomial = ONE
        for index,factor in enumerate(factors):
            if index!=position: raw_polynomial = ('mul',raw_polynomial,factor)
        try:
            p,d = rf(raw_polynomial,variable); p,remainder = pdiv(p,d)
            slope,_ = affine(kernel[1],variable)
        except (NotRational,Undefined,Unsupported): continue
        if any(remainder) or slope==ZERO: continue
        yield p,kernel,slope,raw_polynomial


def finite_parts_proposal(task):
    """Finite polynomial recurrence and existing anti-kernel table; no search."""
    variable,params,base,f = integral_source(task)
    symbol = kernel_symbol(task); z = ('v',symbol)
    for p,kernel,slope,raw_polynomial in polynomial_affine_kernels(f,variable):
        if len(p)>13:continue
        initial = tuple(q(c) for c in p); anti = (kernel[0],z); terms = []; guards = [('nonzero',slope)]
        for order in range(len(p)):
            anti,extra = propose(anti,symbol)
            guards.extend((r,m.substitute(e,{z:kernel[1]})) for r,e in extra)
            term = ('div',('mul',q((-1)**order),('mul',polynomial_expression(p,variable),
                    m.substitute(anti,{z:kernel[1]}))),('pow',slope,order+1))
            terms.append(term)
            p = tuple((n+1)*p[n+1] for n in range(len(p)-1)) or (Fraction(0),)
        if any(p): raise Unsupported('Parts polynomial did not terminate')
        F = ZERO
        for term in terms: F = ('add',F,term)
        return {'candidate_source':source(m.simplify(F)),
                'recipe':{'method':'finite_polynomial_parts','coefficients':initial,'kernel':source(kernel),
                          'raw_polynomial':source(raw_polynomial),'terms':tuple(terms),'guards':unique(guards)}}
    raise Unsupported('Parts family requires a rational polynomial of degree at most12 and one affine elementary kernel')


def verify_parts_recipe(task,plan,proposal,library):
    from verify import same_value
    if library.data.get('finite_parts_contract',{}).get('method_requirement')!='integration_by_parts': raise Unsupported('Finite parts method is not admitted')
    if task.get('method_requirement','table_and_rules') not in PARTS_METHODS: raise Unsupported('Parts do not fulfill the requested method')
    expected = finite_parts_proposal(task)
    if canonical(proposal)!=canonical(expected): raise Unsupported('Finite parts recipe or candidate changed')
    recipe = expected['recipe']; terms = recipe['terms']
    conditions = list(recipe['guards'])
    for term in terms: conditions.extend(domain_conditions(term,True))
    if not all(covers_on_domain(plan,r,e) for r,e in conditions): raise Unsupported('Parts table, slope or raw-term conditions do not cover original D')
    product = ('mul',m.parse(recipe['raw_polynomial'],plan['variable'],plan['source_parameters']),
               m.parse(recipe['kernel'],plan['variable'],plan['source_parameters']))
    if not all(covers_on_domain(plan,r,e) for r,e in domain_conditions(product)) or not same_value(product,plan['integrand_ast']):
        raise Unsupported('Original integrand is not the certified parts product on D')
    total = ZERO
    for term in terms: total = ('add',total,freeze(term))
    if not same_value(total,plan['primitive_ast']): raise Unsupported('Finite parts sum changed')
    return 0


def kernel_symbol(task):
    names = [p if isinstance(p,str) else p['symbol'] for p in task.get('parameters',[])]
    symbol = '__primitive_u'
    while symbol in names or symbol == task.get('variable','x'): symbol += '_'
    return symbol


def primitive_kernels(expression,variable,symbol,*,divisor_factors=False):
    z = ('v',symbol); found = {}
    def offer(u,kernel):
        if u != ('v',variable) and m.variable_in(u,variable): found.setdefault(canonical((u,kernel)),(u,kernel))
    def walk(e):
        if e[0] == 'div':
            d = e[2]
            if d[0] == 'sqrt': offer(d[1],('div',ONE,('sqrt',z)))
            if d[0] == 'pow': offer(d[1],('pow',z,-d[2]))
            offer(d,('div',ONE,z))
        if e[0] == 'pow': offer(e[1],('pow',z,e[2]))
        if e[0] in ('exp','sin','cos','sinh','cosh','sqrt','cbrt'): offer(e[1],(e[0],z))
        if e[0] in ('sqrt','cbrt'):offer(e[1],('div',ONE,(e[0],z)))
        if e[0] in m.FUNCTIONS:offer(e,z)
        for child in e[1:]:
            if isinstance(child,tuple): walk(child)
    walk(expression)
    if divisor_factors:
        def factors(e,degree=1):
            if e[0]=='mul':
                for part in e[1:]:factors(part,degree)
            elif e[0]=='pow' and e[2]:factors(e[1],degree*e[2])
            else:offer(e,('pow',z,-degree))
        for atom in learned_nodes(expression):
            if not isinstance(atom,tuple):continue
            if atom[0]=='div':factors(atom[2])
            if atom[0]=='ln':offer(atom[1],('ln',z))
    for u,_ in tuple(found.values()):offer(u,z)
    return list(found.values())


def substitution_kernel(residual,inner,kernel,symbol):
    """Recover a polynomial residual in the inner variable, then reuse the table."""
    z=('v',symbol)
    direct=m.simplify(m.substitute(residual,{inner:z,m.simplify(inner):z}))
    if not any(t[0]=='v' and t!=z for t in learned_nodes(direct) if isinstance(t,tuple)):
        return m.mul(direct,kernel)
    r,rd=m.rational_form(residual);u,ud=m.rational_form(inner)
    atoms={a for p in (r,u) for mon in p for a,k in mon}
    if len(atoms)!=1 or rd!={():Fraction(1)} or ud!={():Fraction(1)}:
        raise Unsupported('Residual is not a univariate polynomial in the proposed substitution')
    atom,=atoms
    target,base=univariate_coefficients(r,atom),univariate_coefficients(u,atom)
    coeffs=composition_coefficients(target,base) if target is not None and base is not None else None
    if coeffs is None:raise Unsupported('Residual lies outside polynomials in the proposed substitution')
    z=('v',symbol); terms=[]
    for k,c in enumerate(coeffs):
        if c:
            monomial=('mul',('pow',z,k),kernel) if k else kernel
            terms.append(monomial if c==1 else ('mul',q(c),monomial))
    result=terms[0]
    for term in terms[1:]:result=('add',result,term)
    return result


def trig_power_proposal(task,library):
    """Reduce integer powers at one affine angle, preserving the raw domain at verification."""
    variable,_,ctx,f=integral_source(task)
    numerator,denominator=m.rational_form(m.simplify(f))
    if len(numerator)!=1 or len(denominator)!=1:raise Unsupported('Requires one trigonometric monomial')
    terms={}
    coefficient=ONE
    angle=None
    for polynomial,sgn in ((numerator,1),(denominator,-1)):
        (mon,weight),=polynomial.items()
        coefficient=m.mul(coefficient,q(weight**sgn))
        for atom,degree in mon:
            degree*=sgn
            if not m.variable_in(atom,variable):
                coefficient=m.mul(coefficient,m.power(atom,degree))
                continue
            if atom[0] not in ('sin','cos') or angle is not None and atom[1]!=angle:
                raise Unsupported('Requires a common sine and cosine argument')
            angle=atom[1]
            terms[atom[0]]=terms.get(atom[0],0)+degree
    if angle is None:raise Unsupported('No trigonometric factor')
    slope,_=affine(angle,variable)
    if not m.nonzero(slope,ctx):raise Unsupported('The affine angle needs a nonzero slope')
    s,c=('sin',angle),('cos',angle)
    a,b=terms.get('sin',0),terms.get('cos',0)
    recipe={'method':'trigonometric_power_reduction','angle':source(angle),'slope':source(slope),
            'coefficient':source(coefficient),'sine_power':a,'cosine_power':b}
    if (a>0 and a%2) or (b>0 and b%2):
        use_sine=a>0 and a%2 and not (b>0 and b%2 and b<a)
        odd,other,u,sign=(a,b,c,-1) if use_sine else (b,a,s,1)
        recipe.update(rule='odd_substitution',substitution=source(u))
        half=(odd-1)//2
        value=ZERO
        for i in range(half+1):
            degree=other+2*i+1
            primitive=m.div(m.power(u,degree),q(degree)) if degree else ('ln',('abs',u))
            value=m.add(value,m.mul(q(sign*(-1)**i*comb(half,i)),primitive))
    elif min(a,b)<0:
        symbol=kernel_symbol(task);z=('v',symbol)
        if (a+b)%2:
            odd,other,u,sign=(a,b,c,-1) if a%2 else (b,a,s,1)
            kernel=m.mul(m.power(z,other),m.power(m.add(ONE,m.neg(m.power(z,2))),(odd-1)//2))
        else:
            # Choose a tangent chart only where its denominator is already excluded by the source.
            other,u,sign=(a,m.div(s,c),1) if b<0 else (b,m.div(c,s),-1)
            kernel=m.mul(m.power(z,other),m.power(m.add(ONE,m.power(z,2)),-(a+b)//2-1))
        subtask={'kind':'integrate','integrand':source(kernel),'variable':symbol,'method_requirement':'rational_decomposition'}
        contract=library.data.get('rational_primitive_plan',{})
        if 'rational_decomposition' not in contract.get('methods',()):raise Unsupported('A rational kernel needs an admitted decomposition method')
        recipe.update(rule='rational_substitution',substitution=source(u),kernel_task=subtask)
        try:
            rational=rational_proposal(subtask,contract)
            inner=m.parse(rational['candidate_source'],symbol,[])
            recipe['rational']=rational
        except (Unsupported,ResourceBound):
            inner,guards=propose(kernel,symbol)
            subtask['method_requirement']='table_and_rules'
            recipe['table_guards']=[(r,m.substitute(e,{z:u})) for r,e in guards]
        value=m.mul(q(sign),m.substitute(inner,{z:u}))
    else:
        recipe['rule']='even_recurrence'
        value=angle
        for j in range(2,b+1,2):
            term=m.mul(s,m.power(c,j-1))
            value=m.div(m.add(m.mul(q(j-1),value),term),q(j))
        for i in range(2,a+1,2):
            term=m.mul(m.power(s,i-1),m.power(c,b+1))
            value=m.div(m.add(m.mul(q(i-1),value),m.neg(term)),q(i+b))
    return {'candidate_source':source(m.mul(m.div(coefficient,slope),value)),'recipe':recipe}


def inner_derivative_task(task,function):
    return {'kind':'differentiate','function':function,'variable':task.get('variable','x'),
            'parameters':task.get('parameters',[]),'method_requirement':'table_and_rules'}


# Nested parts searches must shorten the product. Other methods remain available
# to every child, including a larger rational remainder created by the product rule.
_parts_size = ContextVar('parent_parts_product_size',default=None)


def rational_class(e,variable):
    try:_,den=rf(e,variable)
    except (NotRational,Undefined,ResourceBound):return None
    return 'polynomial' if len(den)==1 else 'rational'


def induce_parts_roles(verified_sources):
    """Generalize the observed roles of u, dv and du in independently verified parts proofs."""
    from model import digest
    observations={}
    for label,result in verified_sources:
        recipe=(result.get('proposal') or {}).get('recipe',{})
        if result.get('schema')!='integral-chain-run/v1' or recipe.get('method')!='factor_parts':continue
        task=result['task'];v=task['variable'];names=result['compilation']['source_parameters']
        u,dv=(m.parse(recipe[k],v,names) for k in ('u','dv'))
        if u[0] not in m.FUNCTIONS:continue
        forms=(rational_class(dv,v),rational_class(freeze(recipe['derivative_u']['value']),v))
        if None in forms:continue
        coordinate={('s',name):('s',str(i)) for i,name in enumerate(names)}
        coordinate[('v',v)]=('v','coordinate')
        origin=m.substitute(m.simplify(result['compilation']['integrand_ast']),coordinate)
        role=(u[0],origin)
        observations.setdefault(forms,{}).setdefault(role,set()).add(label)
    patterns=[];support={}
    for (dv,du),roles in sorted(observations.items()):
        if len({origin for _,origin in roles})<2:continue
        heads={head for head,_ in roles}
        pattern=dict(u_head=heads.pop() if len(heads)==1 else 'unary',dv_class=dv,du_class=du)
        patterns.append(pattern);support[digest(pattern)]=sorted(set.union(*roles.values()))
    return patterns,support


def learned_parts_factors(f,variable,patterns):
    """Expose multiplicative factors including an implicit unit, without dividing by a selected u."""
    def factors(e,cofactor):
        if e[0]=='mul':
            yield from factors(e[1],('mul',e[2],cofactor))
            yield from factors(e[2],('mul',e[1],cofactor))
        elif e[0]=='div':yield from factors(e[1],('div',cofactor,e[2]))
        elif e[0] in m.FUNCTIONS and m.variable_in(e,variable):yield e,cofactor
    for u,dv in factors(f,ONE):
        for pattern in patterns:
            if pattern['u_head'] in ('unary',u[0]) and rational_class(dv,variable)==pattern['dv_class']:
                yield u,dv,pattern


def parts_splits(f,variable):
    if f[0]!='mul':return
    def factors(e):
        return factors(e[1])+factors(e[2]) if e[0]=='mul' else [e]
    def product(terms):
        value=terms[0]
        for term in terms[1:]:value=('mul',value,term)
        return value
    terms=factors(f)
    pairs=[(f[1],f[2])]
    if len(terms)>2:
        pairs.extend((term,product(terms[:i]+terms[i+1:])) for i,term in enumerate(terms))
    seen=set()
    for left,right in pairs:
        for u,dv in ((left,right),(right,left)):
            if (u,dv) not in seen and all(m.variable_in(m.simplify(e),variable) for e in (u,dv)):
                seen.add((u,dv))
                yield u,dv


def quotient_parts_splits(f,variable):
    if f[0]!='div' or not m.variable_in(f[2],variable):return
    def numerator_roles(e,cofactor):
        if e[0]=='mul':
            yield from numerator_roles(e[1],('mul',e[2],cofactor))
            yield from numerator_roles(e[2],('mul',e[1],cofactor))
        elif (e[0] in ('ln','asin','acos','atan','acot','v') or e[0]=='pow' and e[1]==('v',variable) and e[2]>0
              ) and m.variable_in(e,variable):
            yield e,('div',cofactor,f[2])
    yield from numerator_roles(f[1],ONE)


def compose_factor_parts(task,u,u_source,dv_source,request,normalize=False,require_guard=None):
    """F = uv − G, with separate proofs for v′=dv, u′ and G′=vu′."""
    def primitive(role,expression):
        t={'kind':'integrate','integrand':expression,'variable':task.get('variable','x'),
           'parameters':task.get('parameters',[]),'requested_output':['primitive_family']}
        return freeze(request(role,t)['value']['representative'])
    v=primitive('primitive_v',dv_source)
    derivative=request('derivative_u',inner_derivative_task(task,u_source))
    remainder=('mul',v,freeze(derivative['value']))
    if normalize:
        reduced=m.polynomial_quotient(m.simplify(remainder))
        if reduced==remainder:
            raise Unsupported('The remainder has no algebraic reduction')
        if require_guard is not None:
            for guard in domain_conditions(remainder)+domain_conditions(reduced):
                require_guard(guard)
        remainder=reduced
    G=primitive('primitive_remainder',source(remainder))
    return m.add(m.mul(u,v),m.neg(G))


def factor_parts_plans(task,library,limits,order,attempts):
    from app import solve
    if not library.data.get('general_factor_parts') or task.get('method_requirement','table_and_rules') not in PARTS_METHODS:
        return
    variable,_,_,f=integral_source(task)
    size=m.tree_size(f);parent=_parts_size.get()
    if parent is not None and size>=parent:return
    cache={}
    patterns=library.data.get('learned_parts_roles',())
    explicit=list(parts_splits(f,variable))
    normalize=library.data.get('factor_parts_remainder_normalization')
    if library.data.get('quotient_parts_factors'):explicit.extend(quotient_parts_splits(f,variable))
    if normalize:
        explicit.sort(key=lambda pair: (pair[0][0] not in ('ln','asin','acos','atan','acot'),m.tree_size(pair[0])))
    candidates=((u,dv,None) for u,dv in explicit)
    seen={(u,m.simplify(dv)) for u,dv in explicit} if patterns else set()
    learned=((u,dv,p) for u,dv,p in learned_parts_factors(f,variable,patterns)
             if (u,m.simplify(dv)) not in seen) if patterns else ()
    for u,dv,pattern in chain(candidates,learned):
        recipe={'method':'factor_parts','u':source(u),'dv':source(dv)}
        if pattern is not None:recipe['learned_roles']=dict(pattern)
        def request(role,t):
            key=canonical(t)
            if key not in cache:
                token=_parts_size.set(size)
                try:cache[key]=solve(t,library,limits,order)
                finally:_parts_size.reset(token)
            child=cache[key]
            accepted=('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN') if role=='derivative_u' else ('SOLVED',)
            if child['status'] not in accepted:raise Unsupported(role+' remains '+child['status'])
            if role=='derivative_u' and pattern is not None and rational_class(freeze(child['value']),variable)!=pattern['du_class']:
                raise Unsupported('The derivative does not match the learned factor role')
            recipe[role]=child
            return child
        for mode in (True,False) if normalize else (False,):
            try:
                candidate=compose_factor_parts(task,u,recipe['u'],recipe['dv'],request,mode)
            except PLAN_FAILURES as exc:
                attempts.append({'method':'factor_parts','u':recipe['u'],'dv':recipe['dv'],'stage':'subgoal','reason':str(exc)})
                continue
            packed={**recipe,'normalize_remainder':True} if mode else dict(recipe)
            yield 'factor_parts',{'candidate_source':source(candidate),'recipe':packed},None


def verify_factor_parts(task,plan,proposal,library):
    from verify import verify,same_value
    recipe=proposal['recipe']
    roles=('primitive_v','derivative_u','primitive_remainder')
    if (not library.data.get('general_factor_parts') or task.get('method_requirement','table_and_rules') not in PARTS_METHODS
            or set(recipe)-{'learned_roles','normalize_remainder'}!={'method','u','dv',*roles}
            or 'normalize_remainder' in recipe and
            (recipe['normalize_remainder'] is not True or not library.data.get('factor_parts_remainder_normalization'))):
        raise Unsupported('Factor integration by parts is not admitted for this request')
    variable=plan['variable'];names=plan['source_parameters']
    u,dv=(m.parse(recipe[k],variable,names) for k in ('u','dv'))
    product=('mul',u,dv)
    if 'learned_roles' in recipe:
        pattern=recipe['learned_roles']
        if (pattern not in library.data.get('learned_parts_roles',()) or
                not any(recipe['u']==source(a) and recipe['dv']==source(b) for a,b,_ in learned_parts_factors(plan['integrand_ast'],variable,[pattern])) or
                rational_class(freeze(recipe['derivative_u']['value']),variable)!=pattern['du_class']):
            raise Unsupported('The selected roles are not applicable to the original integrand')
    elif not all(m.variable_in(m.simplify(e),variable) for e in (u,dv)):
        raise Unsupported('Incomplete factor selection')
    if not same_value(product,plan['integrand_ast']):
        raise Unsupported('The parts factors do not give the original product')
    guards=domain_conditions(product)+domain_conditions(u,True)
    count=0
    def request(role,t):
        nonlocal count
        child=recipe[role]
        count+=verify(child,library,expected_task=t)['checked_nodes']
        if role=='derivative_u':
            scope=compile_derivative(t)['formula_scope']['quantified_symbol']
            derivative_on_domain(plan,child,scope)
        elif child['status']=='SOLVED':
            guards.extend(child['value']['original_domain'][1])
        else:raise Unsupported('Incomplete parts primitive')
        return child
    candidate=compose_factor_parts(task,u,recipe['u'],recipe['dv'],request,recipe.get('normalize_remainder',False),guards.append)
    if source(candidate)!=proposal['candidate_source'] or not all(covers_on_domain(plan,r,e) for r,e in guards):
        raise Unsupported('The parts result or its coverage of the original domain changed')
    return count


def product_sum_proposal(task):
    """Apply the real product-to-sum formulas, collect frequencies, then integrate the terms."""
    variable,_,ctx,f=integral_source(task)
    num,den=m.rational_form(f);den=m.poly_expr(den)
    if m.variable_in(den,variable):raise Unsupported('An integral of a quotient needs another method')
    def collect(terms,wave,phase,weight):
        if phase==ZERO and wave=='sin':return
        negative=m.neg(phase)
        if canonical(negative)<canonical(phase):
            phase=negative
            if wave=='sin':weight=m.neg(weight)
        key=(wave,phase);terms[key]=m.add(terms.get(key,ZERO),weight)
    total={};used=False
    for mon,c in num.items():
        coeff=m.div(q(c),den);waves={('cos',ZERO):ONE};factors=0
        for atom,power in mon:
            if not m.variable_in(atom,variable):coeff=m.mul(coeff,m.power(atom,power));continue
            if atom[0] not in ('sin','cos'):raise Unsupported('A factor is outside the sine/cosine product')
            wave,u=atom;affine(u,variable)
            for _ in range(power):
                used=used or factors>0;factors+=1;terms={}
                for (v,t),w in waves.items():
                    if w==ZERO:continue
                    if v=='cos' and t==ZERO:
                        collect(terms,wave,u,w);continue
                    half=m.div(w,q(2));out='cos' if wave==v else 'sin'
                    collect(terms,out,m.add(t,u),m.neg(half) if wave==v=='sin' else half)
                    collect(terms,out,m.add(t,m.neg(u)),m.neg(half) if v=='cos' and wave=='sin' else half)
                waves=terms
        for (wave,phase),w in waves.items():
            collect(total,wave,phase,m.mul(coeff,w))
    if not used:raise Unsupported('No trigonometric product to transform')
    expanded=primitive=ZERO;terms=[]
    for (wave,phase),w in sorted(total.items(),key=lambda i:canonical(i[0])):
        if w==ZERO:continue
        term=m.simplify((wave,phase));H,guards=propose(term,variable)
        if any(not known_guard(g,ctx) for g in guards):raise Unsupported('A frequency can vanish for the source parameters')
        terms.append((w,term));expanded=m.add(expanded,m.mul(w,term));primitive=m.add(primitive,m.mul(w,H))
    return {'candidate_source':source(primitive),'recipe':{'method':'product_to_sum','terms':terms,'expanded_integrand':source(expanded)}}


def rationalizing_integral(variable,lower,upper,integrand,request):
    """Pull a closed real fiber back by a monotone inverse with rational Jacobian.

    The caller certifies the original integrand on the whole fiber before any
    cancellation. Its transformed integral is a separate, replayable subgoal.
    """
    from verify import same_value
    x=('v',variable);name='__rational' if variable!='__rational' else '__rational_'
    t=('v',name);f=m.substitute(integrand,{('s',variable):x})
    def nodes(e,op):
        if e[0]==op:yield e
        for arg in e[1:]:
            if isinstance(arg,tuple):yield from nodes(arg,op)
    def charts(root):
        rad=root[1]
        try:p,d=rf(rad,variable)
        except (NotRational,Undefined):p=d=()
        if len(p)==3 and len(d)==1 and p[2]/d[0]>0:
            slope=m.num(m.simplify(('sqrt',q(p[2]/d[0]))))
            if slope:
                shift=p[1]/(2*slope*d[0]);k=p[0]/d[0]-shift*shift
                if k>0:
                    # t=y+sqrt(y²+k)>0; y=(t−k/t)/2 with y=slope*x+shift.
                    y=m.add(m.mul(q(slope),x),q(shift))
                    half_t=m.div(t,q(2));other=m.div(q(k),m.mul(q(2),t))
                    inverse=m.div(m.add(m.add(half_t,m.neg(other)),q(-shift)),q(slope))
                    image=m.add(half_t,other);jac=m.div(image,m.mul(q(slope),t))
                    yield 'euler_quadratic',m.add(y,root),inverse,image,jac,{},'t>0, k>0'
        for exponential in dict.fromkeys(nodes(rad,'exp')):
            try:
                slope,shift=affine(exponential[1],variable)
                amplitude,offset=affine(m.substitute(rad,{exponential:t}),name)
            except Unsupported:continue
            if not m.num(slope) or not m.num(amplitude) or any(m.num(k) is None for k in (shift,offset)):continue
            # On the principal branch t>=0 and E=(t²−offset)/amplitude.
            # E is monotone there. Its two endpoint values are positive exponentials.
            square=m.add(m.power(t,2),m.neg(offset));E=m.div(square,amplitude)
            inverse=m.div(m.add(('ln',E),m.neg(shift)),slope)
            jac=m.div(m.mul(q(2),t),m.mul(slope,square))
            yield 'exponential_radical',root,inverse,t,jac,{exponential:E},'t>=0, exp(slope*x+shift)>0'
    for root in dict.fromkeys(nodes(f,'sqrt')):
        for chart,forward,inverse,image,jac,extra,branch in charts(root):
            image_bounds=tuple(m.simplify(m.substitute(forward,{x:b})) for b in (lower,upper))
            if not all(same_value(m.substitute(inverse,{t:i}),b) for i,b in zip(image_bounds,(lower,upper))):continue
            if not same_value(m.substitute(root[1],{x:inverse,**extra}),m.power(image,2)):continue
            changed=m.substitute(f,{x:inverse,root:image,**extra})
            kernel=m.simplify(('mul',changed,jac))
            try:rf(kernel,name)
            except (NotRational,Undefined):continue
            derived=request('chart derivative',dict(kind='differentiate',variable=name,function=source(inverse),
                            method_requirement='table_and_rules'))['value']
            if not same_value(derived,jac):raise Unsupported('The rationalizing Jacobian was not established')
            child={'kind':'iterated_integral','integrand':source(kernel),'requested_output':['exact_integral'],
                   'integration_order':[dict(variable=name,lower=source(image_bounds[0]),upper=source(image_bounds[1]))]}
            value=freeze(request('rational/'+variable,child)['value'])
            return {'method':'rationalizing_substitution','variable':variable,'bounds':(lower,upper),'integrand':integrand,
                    'chart':chart,'chart_variable':name,'forward':forward,'inverse':inverse,'radicand':root[1],'radical_image':image,
                    'jacobian':jac,'kernel':kernel,'substituted_bounds':image_bounds,'branch':branch,'difference':value},value
    return None


def primitive_plans(task,library,limits,attempts):
    from app import solve
    method=task.get('method_requirement','table_and_rules')
    specializations=library.data.get('primitive_method_specializations',{}).get(method,())
    variable,_,_,f=integral_source(task)
    def rejected(name,stage,exc):
        attempts.append({'method':name,'stage':stage,'reason':str(exc) or type(exc).__name__})
    if method in TRANSFORMATION_METHODS|{QUADRATIC_METHOD} and library.data.get('quadratic_canonical_primitive'):
        try:yield QUADRATIC_METHOD,quadratic_proposal(task),None
        except PLAN_FAILURES as exc:rejected(QUADRATIC_METHOD,'completion_of_the_square',exc)
    expanded=method=='elementary_table_and_algebra' and 'rational_decomposition' in specializations
    if expanded:
        try:
            proposal=rational_proposal(task,library.data['rational_primitive_plan'])
            if len(proposal['recipe']['terms'])>=2:yield 'rational_decomposition',proposal,None
        except PLAN_FAILURES as exc:rejected('rational_decomposition','coefficient_matching',exc)
    if method not in RECIPE_REQUIRED:
        try: yield 'elementary',None,propose(f,variable)
        except PLAN_FAILURES as exc: rejected('elementary','proposal',exc)
    if method in radicals.ADMITTED and library.data.get(radicals.METHOD):
        try: yield radicals.METHOD,radicals.propose(task),None
        except PLAN_FAILURES as exc: rejected(radicals.METHOD,'quadratic_differential',exc)
    contract=library.data.get('rational_primitive_plan',{})
    single_term=None
    if not expanded and (method in contract.get('methods',[]) or 'rational_decomposition' in specializations):
        try:
            candidate=rational_proposal(task,contract)
            if method=='table_and_rules' and len(candidate['recipe']['terms'])==1:
                single_term=candidate  # Give the existing one-substitution proof its usual priority.
            else: yield 'rational_decomposition',candidate,None
        except PLAN_FAILURES as exc: rejected('rational_decomposition','coefficient_matching',exc)
    if method in TRANSFORMATION_METHODS|{HERMITE_METHOD} and library.data.get(HERMITE_METHOD):
        try:yield HERMITE_METHOD,hermite_proposal(task,library),None
        except PLAN_FAILURES as exc:rejected(HERMITE_METHOD,'squarefree_reduction',exc)
    if method in PARTS_METHODS and library.data.get('finite_parts_contract',{}).get('method_requirement')=='integration_by_parts':
        try: yield 'finite_polynomial_parts',finite_parts_proposal(task),None
        except PLAN_FAILURES as exc: rejected('finite_polynomial_parts','proposal',exc)
    if method not in SUBSTITUTION_METHODS|{'product_to_sum'} and 'product_to_sum' not in specializations: return
    symbol = kernel_symbol(task)
    derivatives={}
    kernels=primitive_kernels(f,variable,symbol,divisor_factors=library.data.get('divisor_factor_differentials')) if method in SUBSTITUTION_METHODS else ()
    for u,kernel in kernels:
        try:
            H,_ = propose(kernel,symbol)
            if u not in derivatives:derivatives[u]=solve(inner_derivative_task(task,source(u)),library,limits,order=2)
            artifact=derivatives[u]
            if artifact['status'] not in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'):
                raise Unsupported('Inner derivative incomplete for '+source(u))
            K = m.substitute(kernel,{('v',symbol):u})
            coefficient = m.simplify(('div',f,('mul',artifact['value'],K)))
            if m.variable_in(coefficient,variable):
                kernel=substitution_kernel(coefficient,u,kernel,symbol)
                H,_=propose(kernel,symbol)
                coefficient=ONE
            F = ('mul',coefficient,m.substitute(H,{('v',symbol):u}))
            yield 'reverse_chain',{'candidate_source':source(F),'recipe':{'u':source(u),'kernel':source(kernel),
                   'coefficient':source(coefficient),'H':source(H),'inner_derivative':artifact}},None
        except PLAN_FAILURES as exc: rejected('reverse_chain','substitution',exc)
    if method in TRANSFORMATION_METHODS and library.data.get('trigonometric_power_reduction'):
        try: yield 'trigonometric_power_reduction',trig_power_proposal(task,library),None
        except PLAN_FAILURES as exc: rejected('trigonometric_power_reduction','reduction',exc)
    if library.data.get('product_to_sum') and method!='appropriate_substitution':
        try: yield 'product_to_sum',product_sum_proposal(task),None
        except PLAN_FAILURES as exc: rejected('product_to_sum','harmonic_expansion',exc)
    if single_term: yield 'rational_decomposition',single_term,None


def learned_nodes(e):
    pending=[e]
    while pending:
        node=pending.pop()
        yield node
        if isinstance(node,tuple):pending.extend(reversed(node[1:]))


def learned_kernel_matches(f,variable,symbol,templates):
    """Bind shared coordinates and scalar slots using structural anchors in the original differential."""
    forms=[node for expr in (f,m.simplify(f)) for node in learned_nodes(expr)
           if isinstance(node,tuple) and m.variable_in(node,variable)]
    by_op={}
    for node in dict.fromkeys(forms):by_op.setdefault(node[0],[]).append(node)
    for index,template in enumerate(templates):
        kernel,primitive=(freeze(template[tag]) for tag in ('kernel','primitive'))
        slots={p for p in learned_nodes(kernel) if isinstance(p,str) and p.startswith('?')}
        seen=set()
        def bind(env):
            if env.keys()!=slots or '?u' not in env:return
            u=env['?u'];bindings={k:v for k,v in env.items() if k!='?u'}
            if not m.variable_in(u,variable) or any(not isinstance(v,tuple) or m.variable_in(v) for v in bindings.values()):return
            key=canonical(env)
            if key not in seen:
                seen.add(key); formal={**bindings,'?u':('v',symbol)}
                yield index,bindings,u,instantiate(kernel,formal),instantiate(primitive,formal)
        for anchor in learned_nodes(kernel):
            if not isinstance(anchor,tuple) or not slots.issubset(set(learned_nodes(anchor))):continue
            for node in by_op.get(anchor[0],()):
                env={}
                if match(anchor,node,env):yield from bind(env)
        if slots=={'?u'}:yield from bind({'?u':('v',variable)})


TABLE_METHODS={'elementary_table_and_algebra','elementary_table_and_affine_change'}
LEARNED_METHODS=SUBSTITUTION_METHODS|TABLE_METHODS


def learned_coordinate_allowed(method,u,variable):
    if method=='elementary_table_and_algebra':return u==('v',variable)
    if method=='elementary_table_and_affine_change':affine(u,variable)
    return m.variable_in(u,variable)


def learned_differential_plans(task,library,limits):
    from app import solve
    templates=library.data.get('learned_differentials',())
    method=task.get('method_requirement','table_and_rules')
    if not templates or method not in LEARNED_METHODS:return
    variable,_,_,f=integral_source(task);symbol=kernel_symbol(task);z=('v',symbol);derivatives={}
    for index,bindings,u,K,H in learned_kernel_matches(f,variable,symbol,templates):
        try:
            if not learned_coordinate_allowed(method,u,variable) or method=='appropriate_substitution' and u==('v',variable):continue
            if u not in derivatives:derivatives[u]=solve(inner_derivative_task(task,source(u)),library,limits)
            proof=derivatives[u]
            if proof['status'] not in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'):continue
            du=freeze(proof['value'])
            coefficient=m.div(f,('mul',du,m.substitute(K,{z:u})))
            if m.variable_in(coefficient):continue
            F=('mul',coefficient,m.substitute(H,{z:u}))
            yield 'learned_differential',{'candidate_source':source(F),'recipe':dict(method='learned_differential',
                   template=index,bindings=bindings,u=source(u),kernel=source(K),H=source(H),
                   coefficient=source(coefficient),inner_derivative=proof)},None
        except PLAN_FAILURES:continue


def verify_recipe(task,plan,proposal,library):
    from verify import verify,same_value
    if not isinstance(proposal,dict) or set(proposal)!={'candidate_source','recipe'} or not isinstance(proposal['recipe'],dict):
        raise Unsupported('Unknown primitive proposal fields')
    recipe=proposal['recipe']
    if recipe.get('method')==HERMITE_METHOD:
        if not library.data.get(HERMITE_METHOD) or task.get('method_requirement','table_and_rules') not in TRANSFORMATION_METHODS|{HERMITE_METHOD}:
            raise Unsupported('The Hermite method does not meet the source requirement')
        if canonical(hermite_proposal(task,library))!=canonical(proposal):raise Unsupported('The rational part, residual or its primitive changed')
        if 'residual_proposal' in recipe:
            reduced=recipe['residual_proposal']
            child={'kind':'integrate','variable':plan['variable'],'integrand':source(freeze(recipe['remainder'])),'method_requirement':'rational_decomposition'}
            return verify_recipe(child,compile_integral(child,reduced['candidate_source']),reduced,library)
        return 0
    if recipe.get('method')==QUADRATIC_METHOD:
        if not library.data.get('quadratic_canonical_primitive') or task.get('method_requirement','table_and_rules') not in TRANSFORMATION_METHODS|{QUADRATIC_METHOD}:
            raise Unsupported('Completing the square does not meet the requested method')
        if canonical(quadratic_proposal(task))!=canonical(proposal):raise Unsupported('Completed square, numerator reduction or primitive changed')
        args=(plan['variable'],plan['source_parameters'])
        a,b,c=map(freeze,recipe['coefficients'])
        z=m.parse(recipe['centered_numerator'],*args);Q=m.parse(recipe['quadratic'],*args)
        if not same_value(m.mul(m.mul(q(4),a),Q),m.add(m.power(z,2),freeze(recipe['discriminant_complement']))):
            raise Unsupported('The claimed square does not represent the original quadratic')
        return 0
    method=task.get('method_requirement')
    if method=='integrand_decomposition' or method=='elementary_table_and_algebra' and recipe.get('method')=='rational_decomposition':
        choices=library.data.get('primitive_method_specializations',{}).get(method,())
        if recipe.get('method') not in choices or len(recipe.get('terms',()))<2:
            raise Unsupported('The requested decomposition needs a verified sum of at least two terms')
        if recipe['method']=='rational_decomposition' and canonical(rational_proposal(task,library.data['rational_primitive_plan']))!=canonical(proposal):
            raise Unsupported('The certified rational decomposition terms changed')
        task={**task,'method_requirement':recipe['method']}
    if recipe.get('method')=='product_to_sum':
        if not library.data.get('product_to_sum') or task.get('method_requirement','table_and_rules') not in TRANSFORMATION_METHODS|{'product_to_sum'}:
            raise Unsupported('Product-to-sum does not fulfill the source method')
        if canonical(product_sum_proposal(task))!=canonical(proposal):raise Unsupported('The harmonic expansion or primitive changed')
        return len(recipe['terms'])
    if recipe.get('method')=='rational_decomposition':
        contract=library.data.get('rational_primitive_plan',{})
        if task.get('method_requirement','table_and_rules') not in contract.get('methods',[]):
            raise Unsupported('Rational decomposition does not meet the requested method')
        if set(recipe)!={'method','terms'} or not 1<=len(recipe['terms'])<=contract['max_degree']+1:
            raise Unsupported('Invalid rational decomposition length')
        rhs=total=ZERO
        for term in recipe['terms']:
            w=freeze(term['weight'])
            if not isinstance(w,tuple) or len(w)!=3 or w[0]!='q' or type(w[1]) is not int or type(w[2]) is not int or w[2]<=0:
                raise Unsupported('Expected an exact rational coefficient')
            u,F,guards=rational_component(term['form'],plan['variable'],contract['max_degree'])
            if freeze(term['integrand'])!=u or freeze(term['primitive'])!=F:
                raise Unsupported('Term does not match the primitive form')
            if not all(covers_on_domain(plan,r,e) for r,e in (*guards,*domain_conditions(u),*domain_conditions(F,True))):
                raise Unsupported('A decomposition term has an extra domain condition')
            rhs=m.add(rhs,m.mul(w,u))
            total=m.add(total,m.mul(w,F))
        if not same_value(rhs,plan['integrand_ast']): raise Unsupported('Rational decomposition identity failed')
        if not same_value(total,plan['primitive_ast']): raise Unsupported('Weighted sum of primitives changed')
        return 0
    if recipe.get('method')=='trigonometric_power_reduction':
        if not library.data.get('trigonometric_power_reduction') or task.get('method_requirement','table_and_rules') not in TRANSFORMATION_METHODS:
            raise Unsupported('Trigonometric reduction does not meet the requested method')
        if canonical(trig_power_proposal(task,library))!=canonical(proposal):raise Unsupported('Trigonometric reduction or candidate changed')
        if not all(covers_on_domain(plan,r,freeze(e)) for r,e in recipe.get('table_guards',())):
            raise Unsupported('A substituted table condition fails on the original trigonometric domain')
        if 'rational' in recipe:
            child=recipe['kernel_task'];rational=recipe['rational']
            return verify_recipe(child,compile_integral(child,rational['candidate_source']),rational,library)
        return 0
    if recipe.get('method')=='finite_polynomial_parts': return verify_parts_recipe(task,plan,proposal,library)
    if recipe.get('method')=='factor_parts':return verify_factor_parts(task,plan,proposal,library)
    learned=recipe.get('method')=='learned_differential'
    method=task.get('method_requirement','table_and_rules')
    if method not in (LEARNED_METHODS if learned else SUBSTITUTION_METHODS):raise Unsupported('Reverse chain does not meet the requested method')
    fields={'u','kernel','coefficient','H','inner_derivative'}
    if set(recipe)!=fields|({'method','template','bindings'} if learned else set()):raise Unsupported('Unknown transformation fields')
    variable = plan['variable']; names = plan['source_parameters']; symbol = kernel_symbol(task)
    u = m.parse(recipe['u'],variable,names); kernel = m.parse(recipe['kernel'],symbol,names)
    if task.get('method_requirement')=='appropriate_substitution' and (not m.variable_in(u,variable) or same_value(u,('v',variable))):
        raise Unsupported('A nonconstant change distinct from the original variable is required')
    coefficient = m.parse(recipe['coefficient'],None,names)
    if learned:
        if method=='appropriate_integrand_transformation' and same_value(u,('v',variable)) and same_value(coefficient,ONE):
            raise Unsupported('The source asks for an explicit transformation')
        templates=library.data.get('learned_differentials',());index=recipe['template']
        if type(index) is not int or not 0<=index<len(templates):raise Unsupported('Unknown learned differential')
        template=templates[index];env=recipe['bindings']
        slots={p for p in learned_nodes(freeze(template['kernel'])) if isinstance(p,str) and p.startswith('?')}
        if not isinstance(env,dict) or set(env)!=slots-{'?u'}:raise Unsupported('Learned scalar bindings changed')
        for value in env.values():
            if not isinstance(value,(tuple,list)) or not value or m.variable_in(freeze(value)):raise Unsupported('Invalid learned scalar')
            m.parse(source(value),None,names)
        bind={**env,'?u':('v',symbol)}
        H=freeze(instantiate(template['primitive'],bind));extra=()
        if recipe['kernel']!=source(instantiate(template['kernel'],bind)):raise Unsupported('Learned differential changed')
        if not learned_coordinate_allowed(method,u,variable):raise Unsupported('The learned substitution does not meet the requested method')
        if method in TABLE_METHODS:
            table_H,extra=propose(kernel,symbol)
            if not same_value(H,table_H):raise Unsupported('This learned kernel is outside the requested primitive table')
    else:H,extra=propose(kernel,symbol)
    if recipe['H'] != source(H): raise Unsupported('Primitive table recipe changed')
    expected = inner_derivative_task(task,recipe['u']); artifact = recipe['inner_derivative']
    checked = verify(artifact,library,expected_task=expected)
    scope = compile_derivative(expected)['formula_scope']['quantified_symbol']
    derivative = derivative_on_domain(plan,artifact,scope)
    if not all(covers_on_domain(plan,r,m.substitute(e,{('v',symbol):u})) for r,e in extra):
        raise Unsupported('Primitive table conditions do not cover original D')
    K = m.substitute(kernel,{('v',symbol):u})
    product = ('mul',coefficient,('mul',derivative,K))
    if not all(covers_on_domain(plan,r,e) for r,e in domain_conditions(u,True)+domain_conditions(product)):
        raise Unsupported('Transformation has a hole or missing differentiability on original D')
    if not same_value(plan['integrand_ast'],product): raise Unsupported('Integrand transformation identity failed')
    F = ('mul',coefficient,m.substitute(H,{('v',symbol):u}))
    if not all(covers_on_domain(plan,r,e) for r,e in domain_conditions(F,True)): raise Unsupported('Table composition has an extra hole on original D')
    if not same_value(plan['primitive_ast'],F): raise Unsupported('Transformation candidate changed')
    return checked['checked_nodes']


def elementary(e):
    if e[0] not in CONTINUOUS_FUNCTIONS|{'q','pi','s','v','add','mul','div','pow','rpow'}:
        raise Unsupported('Continuity outside the declared elementary language')
    for c in e[1:]:
        if isinstance(c,tuple): elementary(c)


def integral_source(task):
    fields = {'kind','integrand','variable','parameters','schema','id','source','transcription',
              'stated_conditions','stated_domain','method_requirement','requested_output','source_root_conventions'}
    if not isinstance(task,dict) or set(task)-fields or task.get('kind') != 'integrate':
        raise Unsupported('Unknown integral goal fields')
    if (task.get('stated_domain') not in (None,[],()) or task.get('source_root_conventions') not in (None,[],()) or
        not isinstance(task.get('stated_conditions',[]),(list,tuple)) or task.get('stated_conditions')):
        raise Unsupported('Source restrictions/notation need a separate domain proof')
    if task.get('method_requirement','table_and_rules') not in METHODS:
        raise Unsupported('Unimplemented integral method requirement')
    printed=task.get('source',{})
    if not isinstance(printed,dict) or any(printed.get(k) not in (None,task.get('method_requirement','table_and_rules'))
            for k in ('explicit_imposed_method','explicit_required_method','method_requirement')):
        raise Unsupported('The source prescribes a different integration method')
    requested = task.get('requested_output',[])
    if not isinstance(requested,(list,tuple)) or set(requested)-{'primitive_family','natural_domain_components','constant_per_component'}:
        raise Unsupported('Unimplemented output requirement')
    variable = task.get('variable','x'); params = task.get('parameters',[])
    if not isinstance(params,(list,tuple)) or any(not isinstance(p,str) and
            (not isinstance(p,dict) or set(p)-{'symbol','domain','independent_of'}) for p in params):
        raise Unsupported('Unknown parameter conditions')
    base = m.context({'variable':variable,'parameters':params})
    names = base['parameters']
    f = m.parse(task['integrand'],variable,names); elementary(f)
    return variable,params,base,f


def guard_witness_candidates(variable,base,facts):
    """Use proved changes and real algebraic cells to propose points for the raw domain."""
    from graphs import domain_partition,ordered_cuts
    import intervals as line
    cuts=[]
    for relation,e in facts:
        term=e;value=q(2);depth=0
        while term[0]=='ln':
            term=term[1];value=('exp',value);depth+=1
        if depth:
            try:a,b=affine(term,variable)
            except Unsupported:pass
            else:
                if m.constant_defined(a,base) and m.nonzero(a,base):yield m.div(m.add(value,m.neg(b)),a)
        try:partition,_=domain_partition(variable,[(relation,e)],simplify_guards=True)
        except (Unsupported,line.Unsupported,NotRational,Undefined,KeyError):continue
        cuts.extend(line.read_quadratic_term(c) for c in partition['cuts'])
    if cuts:
        edges=['-inf',*ordered_cuts(cuts),'+inf']
        for a,b in zip(edges,edges[1:]):
            mid=line.between(a,b)
            yield q(mid)
            yield q(line.between(a,line.Quadratic(mid)))
            yield q(line.between(line.Quadratic(mid),b))


def domain_witness(f,variable,base,domain,facts):
    witnesses = [ZERO,ONE,q(-1),('mul',q(1,2),m.PI)]
    for _,e in facts:
        trig = e[0] in ('sin','cos','sinh'); u = e[1] if trig else e
        try:
            a,b = affine(u,variable)
            if m.constant_defined(a,base) and m.nonzero(a,base):
                phases=(m.mul(q(1,2),m.PI),m.mul(q(1,4),m.PI)) if e[0]=='sin' else (ZERO,m.mul(q(1,4),m.PI)) if e[0]=='cos' else (ONE,)
                witnesses.extend(m.div(m.add(phase,m.neg(b)),a) for phase in phases)
        except Unsupported: pass
    witness = next((w for w in witnesses if m.constant_defined(w,base) and
                    m.constant_defined(m.substitute(f,{('v',variable):w}),base)),None)
    if witness is None:
        # Outside the Cauchy root bound the signs of rational guards are fixed.
        bound=1
        for _,e in facts:
            try:
                for p in rf(e,variable):
                    if len(p)>1:bound=max(bound,2+int(max(abs(c/p[-1]) for c in p[:-1])))
            except (NotRational,Undefined):continue
        witness=next((q(k) for k in (bound,-bound) if m.constant_defined(m.substitute(f,{('v',variable):q(k)}),base)),None)
    if witness is None and all(relation=='nonzero' for relation,_ in domain):
        # Finitely many excluded rational-polynomial roots cannot exhaust d+1 distinct integers.
        try:
            degree=sum(len(p)-1 for _,e in domain for p in rf(e,variable))
            witness=next((q(k) for k in range(degree+1) if m.constant_defined(m.substitute(f,{('v',variable):q(k)}),base)),None)
        except (NotRational,Undefined):pass
    if witness is None:
        witness=next((w for w in guard_witness_candidates(variable,base,facts) if m.constant_defined(w,base) and
                      m.constant_defined(m.substitute(f,{('v',variable):w}),base)),None)
    if witness is None: raise Unsupported('Empty or unknown nonempty original domain')
    return witness


def compile_integral(task,candidate_source=None,*,direct=None):
    variable,params,base,f = integral_source(task)
    names = base['parameters']; point = '__integral_at'
    while point in names or point == variable: point += '_'
    lifted = lambda e: m.substitute(e,{('v',variable):('s',point)})
    point_base = m.context({'variable':variable,'parameters':names+[point]})
    if direct is None:
        direct=propose(f,variable) if candidate_source is None else (m.parse(candidate_source,variable,names),())
    F,extra=direct; elementary(F)
    domain = tuple(domain_conditions(f)); facts = entailed_domain_guards(domain)
    def context(guards):
        return m.context({'variable':variable,'parameters':names+[point],
                          'parameter_conditions':[guard_source((r,lifted(e))) for r,e in guards]})
    ctx = context(facts); promoted = []
    for r,e in domain:
        if r != 'nonnegative' or known_guard((r,lifted(e)),point_base): continue
        if m.constant_defined(lifted(e),ctx) and m.nonzero(lifted(e),ctx): promoted.append(('positive',e))
        else: raise Unsupported('Included boundary or unknown domain openness')
    facts = unique(facts+tuple(promoted)); ctx = context(facts)
    sufficient = unique(extra+tuple(domain_conditions(F,True))); checked = ()
    for r,e in sufficient:
        if not known_guard((r,lifted(e)),ctx):
            raise Unsupported('Candidate join, extra hole, or added condition is not covered on all D')
        checked = unique(checked+((r,e),)); ctx = context(unique(facts+checked))
    witness=domain_witness(f,variable,base,domain,facts)
    guards = unique(facts+sufficient)
    child = {'kind':'differentiate','function':source(F),'variable':variable,'parameters':params,
             'stated_conditions':[guard_source(g) for g in guards],'method_requirement':'table_and_rules'}
    compiled = compile_derivative(child)
    return {'method':'primitive_derivative_family','integrand_ast':f,'primitive_ast':F,'variable':variable,
            'natural_domain':domain,'domain_context':ctx,'domain_point':point,'domain_witness':witness,
            'source_parameters':names,'derivative_task':child,'derivative_point':compiled['formula_scope']['quantified_symbol']}


def contexts(obj):
    if isinstance(obj,dict):
        if isinstance(obj.get('context'),dict): yield obj['context']
        for value in obj.values(): yield from contexts(value)
    elif isinstance(obj,(list,tuple)):
        for value in obj: yield from contexts(value)


def covers_on_domain(plan,relation,expr,scope=None):
    variable = plan['variable']; at = plan['domain_point']
    if relation not in ('zero','nonzero','positive','nonnegative'): return False
    expr = freeze(expr)
    if scope is not None: expr = m.substitute(expr,{('s',scope):('v',variable)})
    expr = m.substitute(expr,{('v',variable):('s',at)})
    if relation == 'zero': return m.constant_defined(expr,plan['domain_context']) and m.sign(expr,plan['domain_context']) == 0
    return known_guard((relation,expr),plan['domain_context'])

def derivative_on_domain(plan,child,scope):
    """Caller must replay child against its exact derivative task before acceptance."""
    if child.get('status') not in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN') or child.get('value') is None:
        raise Unsupported('Derivative remains incomplete')
    actual = []
    for ctx in contexts(child):
        for assumption in ctx['assumptions']:
            r,e = assumption['relation'],('s',assumption['symbol'])
            if r == 'negative': r,e = 'positive',m.neg(e)
            if r == 'greater_one': r,e = 'positive',m.add(e,m.neg(ONE))
            actual.append((r,e))
        actual.extend(('nonzero',freeze(e)) for e in ctx['nonzero_expressions'])
        actual.extend(('positive',freeze(e)) for e in ctx['positive_expressions'])
    if not all(covers_on_domain(plan,r,e,scope) for r,e in actual): raise Unsupported('Actual derivative assumptions do not cover all D')
    value = freeze(child['value'])
    if value in ('+inf','-inf'): raise Unsupported('No finite derivative value')
    if not all(covers_on_domain(plan,r,e,scope) for r,e in domain_conditions(value)): raise Unsupported('Raw derivative value has extra holes')
    return value


def conclusion(plan,child,proposal=None):
    from verify import same_value
    value = derivative_on_domain(plan,child,plan['derivative_point'])
    target=plan['integrand_ast']
    if proposal and proposal['recipe'].get('method')=='product_to_sum':
        target=m.parse(proposal['recipe']['expanded_integrand'],plan['variable'],plan['source_parameters'])
    if not same_value(value,target): raise Unsupported('Derivative identity not established exactly')
    return {'representative':plan['primitive_ast'],'original_domain':('and',plan['natural_domain']),
            'component_scope':'each maximal connected open component J of D',
            'family':'F|J + C_J','constant_policy':'independent real C_J for each original component, for each fixed parameter tuple',
            'identity':{'derivative_ast':value,'integrand_ast':plan['integrand_ast']},
            'basis':'pointwise derivative identity and mean-value uniqueness on each J'}


def linear_primitive(task,library,request):
    """Apply finite linearity on the intersection of the raw domains, including zero weights."""
    from verify import same_value
    x,params,ctx,raw=integral_source(task)
    if (library.data.get('task_compilers',{}).get('linear_primitive')!='linear_combination_on_source_components'
            or task.get('method_requirement','table_and_rules')!='table_and_rules'):
        raise Unsupported('Primitive linearity does not satisfy this method')
    def product(a,b):return b if a==ONE else a if b==ONE else ('mul',a,b)
    def factor(e):
        if not m.variable_in(e,x):return e,ONE
        if e[0]=='mul':
            a,g=factor(e[1]);b,h=factor(e[2]);return product(a,b),product(g,h)
        if e[0]=='div' and not m.variable_in(e[2],x):
            a,g=factor(e[1]);return ('div',a,e[2]),g
        return ONE,e
    def terms(e):
        if e[0]=='add':return terms(e[1])+terms(e[2])
        return [factor(e)]
    pieces=terms(raw)
    if len(pieces)==1 and pieces[0][1]==raw:raise Unsupported('No smaller primitive kernel')
    domain=tuple(domain_conditions(raw));witness=domain_witness(raw,x,ctx,domain,entailed_domain_guards(domain))
    F=derivative=original_sum=ZERO;rows=[]
    for i,(coefficient,kernel) in enumerate(pieces):
        if not m.constant_defined(coefficient,ctx):raise Unsupported('An independent coefficient has an unresolved parameter domain')
        t={'kind':'integrate','integrand':source(kernel),'variable':x,'parameters':params,'method_requirement':'table_and_rules','requested_output':['primitive_family']}
        child=request('kernel/'+str(i),t)['value']
        c=m.simplify(coefficient);K=freeze(child['representative']);g=freeze(child['identity']['derivative_ast'])
        F=m.add(F,m.mul(c,K));derivative=m.add(derivative,m.mul(c,g))
        original_sum=m.add(original_sum,m.mul(c,freeze(child['identity']['integrand_ast'])))
        rows.append({'coefficient':coefficient,'kernel':kernel,'primitive':K})
    if not same_value(original_sum,raw):raise Unsupported('Linear combination does not reproduce the source')
    return {'terms':rows,'source_witness':witness},{'representative':F,'original_domain':('and',domain),
        'component_scope':'each maximal connected open component J of D','family':'F|J + C_J',
        'constant_policy':'independent real C_J for each original component, for each fixed parameter tuple',
        'identity':{'derivative_ast':derivative,'integrand_ast':raw},'basis':'linearity of verified primitive identities restricted to each original component'}


def exact_form(task,library,request):
    """Construct a candidate by integration along coordinate axes, then prove its full gradient."""
    from verify import same_value
    fields={'kind','id','source','variables','coefficients','parameters','stated_conditions','start','end','closed','method_requirement','requested_output'}
    wanted=task.get('requested_output');closed=task.get('closed',False);endpoint='start' in task and 'end' in task
    if (set(task)-fields or type(closed) is not bool or ('start' in task)!=('end' in task) or closed and endpoint
            or wanted!=(['exactness_proof','line_integral'] if closed or endpoint else ['potential_and_domain'])
            or task.get('method_requirement','full_differential')!='full_differential'
            or library.data.get('task_compilers',{}).get('exact_form')!='recover_and_verify_potential'):
        raise Unsupported('Unknown path, method, domain or output for a potential')
    coords=task['variables'];forms=task['coefficients'];params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if (not all(isinstance(z,(list,tuple)) for z in (coords,forms,params,conditions)) or not coords or len(coords)!=len(forms)
            or not all(isinstance(z,str) for z in [*coords,*forms,*params,*conditions])):
        raise Unsupported('Expected one component per named real coordinate')
    names=[*coords,*params];dummy='__field'
    while dummy in names:dummy+='_'
    def context(symbols):return m.context({'variable':dummy,'parameters':symbols,'parameter_conditions':conditions})
    fixed=context(params);whole=context(names)
    raw=[m.parse(f,None,names) for f in forms]
    if not all(known_guard(g,whole) for f in raw for g in domain_conditions(f)):
        raise Unsupported('A global primitive requires a validated common coordinate domain')
    contributions=[];potential=ZERO
    for i,v in enumerate(coords):
        restricted=m.substitute(raw[i],{('s',w):ZERO for w in coords[i+1:]})
        t={'kind':'integrate','integrand':source(restricted),'variable':v,'parameters':[*coords[:i],*params],
           'method_requirement':'table_and_rules','requested_output':['primitive_family']}
        F=freeze(request('axis_primitive/'+v,t)['value']['representative'])
        F=m.substitute(F,{('v',v):('s',v)})
        if not all(known_guard(g,whole) for g in domain_conditions(F)):raise Unsupported('A proposed primitive has an extra hole')
        increment=m.add(F,m.neg(m.substitute(F,{('s',v):ZERO})))
        contributions.append(increment);potential=m.add(potential,increment)
    gradient=[]
    for i,v in enumerate(coords):
        t={'kind':'differentiate','function':source(potential),'variable':v,'parameters':[w for w in names if w!=v],
           'stated_conditions':conditions,'method_requirement':'table_and_rules'}
        derivative=freeze(request('gradient/'+v,t)['value'])
        g=m.substitute(derivative,{('v',v):('s',v)})
        if not same_value(g,raw[i]):raise Unsupported('The proved gradient differs from the original one-form')
        gradient.append(g)
    value={'potential':potential,'domain':'all_real_coordinates','constant':'one_additive_constant'}
    if closed:value['line_integral']=ZERO
    if endpoint:
        def at(p):
            if not isinstance(p,(list,tuple)) or len(p)!=len(coords):raise Unsupported('Wrong endpoint dimension')
            z=[m.parse(str(w),None,params) for w in p]
            if not all(m.constant_defined(w,fixed) for w in z):raise Unsupported('Undefined endpoint')
            return m.substitute(potential,dict(zip((('s',v) for v in coords),z)))
        value['line_integral']=m.add(at(task['end']),m.neg(at(task['start'])))
    return {'coordinate_increments':contributions,'verified_gradient':gradient},value


HARMONIC_ZERO=(ZERO,ZERO)
HARMONIC_ONE=(ONE,ZERO)
def harmonic_add(u,v):
    return (m.add(u[0],v[0]),m.add(u[1],v[1]))
def harmonic_scale(u,c):
    return (m.mul(u[0],c),m.mul(u[1],c))
def harmonic_product(u,v):
    a,b=u;c,d=v
    return (m.add(m.mul(a,c),m.neg(m.mul(b,d))),m.add(m.mul(a,d),m.mul(b,c)))
def harmonic_equal(u,v):
    from verify import same_value
    return all(same_value(a,b) for a,b in zip(u,v))
def harmonic_key(A,B,j):
    return (m.simplify(A),m.simplify(B),j)
def harmonic_union(lhs,rhs):
    result=dict(lhs)
    for key,v in rhs.items():result[key]=harmonic_add(result.get(key,HARMONIC_ZERO),v)
    return {k:v for k,v in result.items() if v!=HARMONIC_ZERO}
def harmonic_convolution(lhs,rhs):
    result={}
    for (a,b,j),u in lhs.items():
        for (c,d,k),v in rhs.items():
            key=harmonic_key(m.add(a,c),m.add(b,d),j+k)
            result[key]=harmonic_add(result.get(key,HARMONIC_ZERO),harmonic_product(u,v))
    return {k:v for k,v in result.items() if v!=HARMONIC_ZERO}

def harmonic_modes(t,parameter_conditions=()):
    x,_,ctx,raw=integral_source(t)
    if parameter_conditions:
        ctx=m.context(dict(variable=x,parameters=ctx['parameters'],parameter_conditions=parameter_conditions))
    method=t.get('method_requirement','table_and_rules')
    if method not in ('table_and_rules','integrand_decomposition','product_to_sum'):
        raise Unsupported('Coefficient synthesis does not establish the printed method')
    z=('v',x)
    for guard in domain_conditions(raw):
        if not known_guard(guard,ctx):raise Unsupported('source has a pole, a restriction, or an unproved real branch')
    log=[]
    def one(value):
        return {harmonic_key(m.ZERO,m.ZERO,0):(value,m.ZERO)}
    def walk(e):
        tag=e[0]
        if not m.contains(e,z):
            if not m.constant_defined(e,ctx):raise Unsupported('undefined fixed coefficient')
            return one(m.simplify(e))
        if e==z:return {harmonic_key(m.ZERO,m.ZERO,1):HARMONIC_ONE}
        if tag=='add':return harmonic_union(walk(e[1]),walk(e[2]))
        if tag=='mul':
            left,right=walk(e[1]),walk(e[2])
            if len(left)*len(right)>1:log.append('multiply_and_collect_modes')
            return harmonic_convolution(left,right)
        if tag=='div' and not m.contains(e[2],z) and m.nonzero(e[2],ctx):return harmonic_convolution(walk(e[1]),one(m.div(m.ONE,e[2])))
        if tag=='pow' and type(e[2]) is int and e[2]>=0:
            base=walk(e[1]);result=one(m.ONE)
            for _ in range(e[2]):result=harmonic_convolution(result,base)
            if e[2]>=2 and len(base)>1:log.append('multiply_and_collect_modes')
            return result
        if tag not in ('exp','sin','cos','sinh','cosh'):raise Unsupported('weight is outside the finite polynomial/harmonic algebra')
        a,c=affine(e[1],x)
        if not all(m.constant_defined(k,ctx) for k in (a,c)):raise Unsupported('the affine phase is not real on the whole source')
        if tag=='exp':return {harmonic_key(a,m.ZERO,0):(m.simplify(('exp',c)),m.ZERO)}
        result={}
        for sign in (1,-1):
            sg=q(sign)
            if tag in ('cosh','sinh'):
                v=(m.mul(q(sign if tag=='sinh' else 1,2),m.simplify(('exp',m.mul(sg,c)))),m.ZERO);key=harmonic_key(m.mul(sg,a),m.ZERO,0)
            else:
                v=harmonic_scale((m.simplify(('cos',c)),m.mul(sg,m.simplify(('sin',c)))),q(1,2))
                if tag=='sin':v=harmonic_product(v,(m.ZERO,q(-sign)))
                key=harmonic_key(m.ZERO,m.mul(sg,a),0)
            result=harmonic_union(result,{key:v})
        return result
    rows=walk(raw);modes={}
    for (a,b,j),v in rows.items():
        co=modes.setdefault((a,b),{})
        co[j]=v
    if method in ('product_to_sum','integrand_decomposition') and 'multiply_and_collect_modes' not in log:
        raise Unsupported('the requested product/decomposition step has not been produced')
    return {k:[p.get(j,HARMONIC_ZERO) for j in range(max(p)+1)] for k,p in modes.items()},ctx,log

def real_harmonic_sum(modes,variable):
    """Write Re(sum) using real elementary functions; collect the opposite Fourier frequencies."""
    grouped={};x=('v',variable)
    for (a,b),P in modes.items():
        neg=m.neg(b)
        flip=b!=m.ZERO and (source(neg).count('-'),source(neg))<(source(b).count('-'),source(b))
        freq=neg if flip else b;key=a,freq
        for j,(u,v) in enumerate(P):
            sin=m.ZERO if freq==m.ZERO else v if flip else m.neg(v)
            k=key+(j,);grouped[k]=harmonic_add(grouped.get(k,HARMONIC_ZERO),(u,sin))
    value=m.ZERO
    for (a,b,j),(u,v) in grouped.items():
        angle=m.mul(b,x);wave=m.add(m.mul(u,m.simplify(('cos',angle))),m.mul(v,m.simplify(('sin',angle))))
        value=m.add(value,m.mul(m.power(x,j),m.mul(m.simplify(('exp',m.mul(a,x))),wave)))
    return value


def harmonic_plans(task,library,attempts):
    if library.data.get('finite_harmonic_primitive') and task.get('method_requirement','table_and_rules') in ('table_and_rules','product_to_sum','integrand_decomposition'):
        try:yield 'finite_harmonic_primitive',harmonic_proposal(task),None
        except PLAN_FAILURES as exc:attempts.append(dict(method='finite_harmonic_primitive',stage='harmonic_decomposition',reason=str(exc)))


def harmonic_proposal(task,parameter_conditions=()):
    """Solve Q' + (a+ib)Q=P by descending polynomial degree."""
    modes,_,actions=harmonic_modes(task,parameter_conditions);rows=[]
    for (a,b),P in sorted(modes.items(),key=lambda pair:canonical(pair[0])):
        d=len(P)-1;D=m.add(m.power(a,2),m.power(b,2))
        row=dict(rate=a,frequency=b,zero_primitive=[HARMONIC_ZERO]+[harmonic_scale(p,q(1,j+1)) for j,p in enumerate(P)])
        if (a,b)!=HARMONIC_ZERO:
            # Numerators share D^(d+1). Each derivative of P lowers its degree once.
            N=[HARMONIC_ZERO]*(d+1)
            for j,p in enumerate(P):
                w=harmonic_product(p,(a,m.neg(b)))
                for k in range(j+1):
                    N[j-k]=harmonic_add(N[j-k],harmonic_scale(w,m.power(D,d-k)))
                    w=harmonic_scale(harmonic_product(w,(a,m.neg(b))),q(k-j))
            row['nonzero_numerators']=N
        rows.append(row)
    return dict(method='finite_harmonic_primitive',decomposition=source(real_harmonic_sum(modes,task['variable'])),actions=actions,modes=rows)


def verify_harmonic_family(task,plan,parameter_conditions=()):
    """Differentiate the submitted coefficients. Nothing in this verifier calls the proposal routine."""
    modes,ctx,actions=harmonic_modes(task,parameter_conditions);x=task.get('variable','x');names=ctx['parameters']
    if (set(plan)!={'method','decomposition','actions','modes'} or plan['method']!='finite_harmonic_primitive' or
            list(plan['actions'])!=actions):raise Unsupported('The requested source transformation is incomplete')
    shown,_,_=harmonic_modes(dict(task,integrand=plan['decomposition'],method_requirement='table_and_rules'),parameter_conditions)
    for key in set(modes)|set(shown):
        left,right=modes.get(key,[]),shown.get(key,[])
        if any(not harmonic_equal(left[j] if j<len(left) else HARMONIC_ZERO,right[j] if j<len(right) else HARMONIC_ZERO)
               for j in range(max(len(left),len(right)))):raise Unsupported('The real decomposition differs from the original integrand')
    def vector(values,n):
        if not isinstance(values,(list,tuple)) or len(values)!=n:raise Unsupported('A polynomial coefficient is missing')
        result=[]
        for pair in values:
            if not isinstance(pair,(list,tuple)) or len(pair)!=2:raise Unsupported('A coefficient must be a real and imaginary pair')
            terms=tuple(m.parse(source(freeze(v)),None,names) for v in pair)
            if not all(m.constant_defined(v,ctx) for v in terms):raise Unsupported('An unguarded coefficient has an extra pole')
            result.append(tuple(map(m.simplify,terms)))
        return result
    fixed={};conditional={};seen=set();checked=0
    for row in plan['modes']:
        key=freeze(row['rate']),freeze(row['frequency']);a,b=key
        if key in seen or key not in modes:raise Unsupported('Missing or duplicate source frequency')
        seen.add(key);P=modes[key];d=len(P)-1;Z=vector(row['zero_primitive'],d+2)
        if any(not harmonic_equal(harmonic_scale(Z[j+1],q(j+1)),p) for j,p in enumerate(P)):
            raise Unsupported('The derivative on the zero-frequency branch differs')
        checked+=d+1
        if key==HARMONIC_ZERO:
            if set(row)!={'rate','frequency','zero_primitive'}:raise Unsupported('An identically zero rate cannot be inverted')
            fixed[key]=Z;continue
        if set(row)!={'rate','frequency','zero_primitive','nonzero_numerators'}:raise Unsupported('An entire parameter branch was omitted')
        N=vector(row['nonzero_numerators'],d+1);D=m.add(m.power(a,2),m.power(b,2));den=m.power(D,d+1)
        for j,p in enumerate(P):
            derivative=harmonic_scale(N[j+1],q(j+1)) if j<d else HARMONIC_ZERO
            if not harmonic_equal(harmonic_add(derivative,harmonic_product(key,N[j])),harmonic_scale(p,den)):
                raise Unsupported('Differentiation of a proposed polynomial-exponential term fails')
            checked+=1
        if m.nonzero(a,ctx) or m.nonzero(b,ctx):fixed[key]=[harmonic_scale(v,m.div(ONE,den)) for v in N]
        else:
            # D>0 on the complement of the simultaneous zero set of real a,b.
            group=conditional.setdefault(D,dict(squared_rate=D,if_zero=ZERO,otherwise=ZERO))
            group['if_zero']=m.add(group['if_zero'],real_harmonic_sum({HARMONIC_ZERO:Z},x))
            group['otherwise']=m.add(group['otherwise'],m.div(real_harmonic_sum({key:N},x),den))
    if seen!=set(modes):raise Unsupported('The candidate omits an original frequency')
    regular=real_harmonic_sum(fixed,x)
    value=dict(original_domain=('and',()),component_scope='all real x for each fixed real parameter tuple',family='F + C',
               constant_policy='one independent real constant for each fixed parameter tuple',
               identity=dict(derivative_ast=m.parse(task['integrand'],x,names),integrand_ast=m.parse(task['integrand'],x,names)),
               basis='all coefficients in the derivative match on the simultaneous-zero and nonzero branches; uniqueness by the mean value theorem')
    if conditional:
        if task.get('requested_output')==['primitive_family']:
            raise Unsupported('This scalar subgoal needs transport of parameter-conditional primitives')
        value.update(fixed_terms=regular,parameter_terms=list(conditional.values()))
    else:value['representative']=regular
    return value,checked


def harmonic_report(result):
    from app import pretty
    x=result['task'].get('variable','x');p=result['compilation'];v=result['value'];names=integral_source(result['task'])[2]['parameters']
    fmt=lambda z:pretty(z,x)
    lines=['Раскрываем произведения. Подынтегральное выражение равно '+fmt(m.parse(p['decomposition'],x,names))+'.',
           'Ищем многочлены при экспонентах, синусах и косинусах. Дифференцирование и сравнение коэффициентов подтверждают каждое слагаемое на всей вещественной оси.']
    if 'representative' in v:return '\n'.join(lines+['Первообразная равна '+fmt(v['representative'])+' + C.'])
    if freeze(v['fixed_terms'])!=ZERO:lines.append('Постоянно действующая часть формулы F₀ = '+fmt(v['fixed_terms'])+'.')
    for j,row in enumerate(v['parameter_terms'],1):
        lines.extend(['F'+str(j)+' = '+fmt(row['if_zero'])+' при '+fmt(row['squared_rate'])+' = 0.',
                      'F'+str(j)+' = '+fmt(row['otherwise'])+' при '+fmt(row['squared_rate'])+' > 0.'])
    summands=(['F₀'] if freeze(v['fixed_terms'])!=ZERO else [])+['F'+str(j+1) for j in range(len(v['parameter_terms']))]
    return '\n'.join(lines+['Первообразная равна '+' + '.join(summands+['C'])+'.'])


def solve_integral(task,library,limits=None,order=None):
    from app import solve
    start = perf_counter()
    result = {'schema':'integral-chain-run/v1','task':task,'library_hash':library.hash,
              'operation_hash':version(),'knowledge_source':library.origin,
              'status':'INTEGRAL_PENDING','value':None,'verification':{'status':'incomplete'}}
    if 'signed_laurent_chart' in library.data.get('source_primitive_charts',()):
        from source_primitives import chart_options
        text=task.get('integrand','')
        if 'signed_laurent_chart' in chart_options(task) and re.search(r'\^\d{3,}(?!\d)',text):
            from app import solve_composed
            proof=solve_composed(task,library,limits,order,preferred_charts=('signed_laurent_chart',))
            if proof['status']=='SOLVED':return proof
    if library.data.get('primitive_foundation_transitions') and task.get('method_requirement')=='integrand_decomposition':
        preferred=('verified_integrand_split',)
    else:
        preferred=preferred_elementary_charts(task) if library.data.get('elementary_primitive_transitions') else ()
    if library.data.get('exact_partial_fraction_replay'):
        preferred=partial_fraction_options(task)+preferred
        if 'exact_partial_fractions' in preferred:
            try:
                proposal=rational_proposal(task,library.data['rational_primitive_plan'])
                plan,value=replay_partial_fractions(task,library,proposal)
                result.update(compilation=plan,proposal=proposal,value=value,status='SOLVED',
                              elapsed_seconds=round(perf_counter()-start,6))
                result['verification']=verify_integral(result,library,task)
                return result
            except PLAN_FAILURES:pass
            preferred=tuple(c for c in preferred if c!='exact_partial_fractions')
    if library.data.get('guarded_quadratic_differentials'):
        preferred=guarded_differential_options(task)+preferred
    if library.data.get('real_root_periodic_coordinate'):
        preferred=periodic_root_options(task)+preferred
    if library.data.get('source_primitive_charts'):
        from source_primitives import chart_options
        scope={'common_symbolic_power','signed_integer_affine_power','odd_root_rational_coordinate',
               'positive_affine_inverse_chart','regular_harmonic_root','hyperbolic_quadratic_pullback',
               'positive_binomial_projective','diagonal_projective_quadratics','shifted_symbolic_trig_ratio',
               'reciprocal_inverse_parts','quadratic_weight_coordinate','odd_binomial_square_coordinate',
               'inverse_parts_weight_span','circular_log_parts','hyperbolic_log_parts','affine_log_ratio_parts'}
        preferred+=tuple(c for c in chart_options(task) if c in scope and c in library.data['source_primitive_charts'])
    if preferred:
        from app import solve_composed
        proof=solve_composed(task,library,limits,order,preferred_charts=preferred)
        if proof['status']=='SOLVED':return proof
    try:
        if library.data.get('task_compilers',{}).get('integrate') != 'primitive_derivative_family':
            raise Unsupported('Primitive method is not admitted in this library')
        attempts=result['plan_attempts']=[]
        plans=chain(primitive_plans(task,library,limits,attempts),harmonic_plans(task,library,attempts),factor_parts_plans(task,library,limits,order,attempts),
                    [('linearity',None,None)],learned_differential_plans(task,library,limits))
        for method,proposal,direct in plans:
            if method==radicals.METHOD:
                try:family,_=radicals.check(task,proposal)
                except PLAN_FAILURES as exc:
                    attempts.append(dict(method=method,stage='differential_identity',reason=str(exc)));continue
                result.update(compilation=proposal,value=family,status='SOLVED')
                result['verification']=verify_integral(result,library,task)
                attempts.append(dict(method=method,stage='verified'));break
            if method=='finite_harmonic_primitive':
                try:family,checked=verify_harmonic_family(task,proposal)
                except PLAN_FAILURES as exc:
                    attempts.append(dict(method=method,stage='harmonic_derivative',reason=str(exc)));continue
                result.update(compilation=proposal,value=family,status='SOLVED',verification=dict(status='passed',complete=True,checked_nodes=checked,
                              scope='original method and independent coefficient identities on all real x and all source parameter branches'))
                attempts.append(dict(method=method,stage='verified'));break
            if method=='linearity':
                from app import solve_composed
                if library.data.get('task_compilers',{}).get('linear_primitive'):
                    linear=solve_composed(task,library,limits,order)
                    if linear['status']=='SOLVED':
                        linear['elapsed_seconds']=round(perf_counter()-start,6);return linear
                    attempts.append({'method':method,'stage':'composition','reason':linear['reason'],
                                     'charts':linear.get('chart_attempts',{})})
                continue
            stage='domain'
            try:
                plan=compile_integral(task,proposal['candidate_source'] if proposal else None,direct=direct)
                if proposal:
                    stage='identity'; verify_recipe(task,plan,proposal,library)
                stage='derivative'
                child=solve(plan['derivative_task'],library,limits,order=2 if order is None else order)
                family=conclusion(plan,child,proposal)
            except PLAN_FAILURES as exc:
                attempts.append({'method':method,'stage':stage,'reason':str(exc)})
                continue
            if proposal: result['proposal']=proposal
            result.update(compilation=plan,child_result=child,value=family,status='SOLVED')
            result['verification']=verify_integral(result,library,expected_task=task)
            attempts.append({'method':method,'stage':'verified'})
            break
        else:raise Unsupported('No verified primitive plan')
    except (Unsupported,KeyError,TypeError,ResourceBound,ZeroDivisionError) as exc:
        result.update(status='INTEGRAL_PENDING',value=None,reason=str(exc))
    extra_charts=(library.data.get('real_radical_coordinates') and radicals.radical_chart_options(task)
                  or library.data.get('elementary_primitive_transitions') and elementary_chart_options(task))
    if (result['status']!='SOLVED' and extra_charts
            and not any(row['method']=='linearity' for row in result.get('plan_attempts',[]))):
        from app import solve_composed
        trial=solve_composed(task,library,limits,order)
        if trial['status']=='SOLVED':
            trial['elapsed_seconds']=round(perf_counter()-start,6)
            return trial
        result['coordinate_proof_failures']=trial.get('chart_attempts',{})
    result['elapsed_seconds'] = round(perf_counter()-start,6)
    return result


def verify_integral(result,library,expected_task=None):
    from verify import verify,require
    require(result.get('schema') == 'integral-chain-run/v1','Wrong primitive schema')
    require(result['library_hash'] == library.hash and result['operation_hash'] == version(),'Primitive basis changed')
    task = result['task']
    if expected_task is not None: require(canonical(task) == canonical(expected_task),'Primitive source changed')
    require(library.data.get('task_compilers',{}).get('integrate') == 'primitive_derivative_family','Primitive method not admitted')
    if (result.get('compilation') or {}).get('method')==radicals.METHOD:
        require(library.data.get(radicals.METHOD) and result.get('status')=='SOLVED','Quadratic radical rule unavailable')
        try:family,nodes=radicals.check(task,result['compilation'])
        except PLAN_FAILURES+(KeyError,TypeError,IndexError,ValueError) as exc:
            require(False,'Invalid quadratic differential: '+str(exc))
        require(canonical(family)==canonical(result['value']),'Quadratic primitive or its domain changed')
        return dict(status='passed',complete=True,checked_nodes=nodes,scope='quadratic differential identity on every original real component with endpoint continuity')
    if (result.get('compilation') or {}).get('method')=='finite_harmonic_primitive':
        require(library.data.get('finite_harmonic_primitive') and result.get('status')=='SOLVED','Harmonic method not available')
        try:family,nodes=verify_harmonic_family(task,result['compilation'])
        except (Unsupported,NotRational,Undefined,ResourceBound,KeyError,TypeError,IndexError,ZeroDivisionError) as exc:
            require(False,'Invalid harmonic primitive: '+str(exc))
        require(canonical(family)==canonical(result['value']),'Submitted harmonic formula or domain changed')
        return dict(status='passed',complete=True,checked_nodes=nodes,scope='original method and independent coefficient identities on all real x and all source parameter branches')
    if (result.get('compilation') or {}).get('method')=='exact_rational_decomposition':
        require(library.data.get('exact_partial_fraction_replay') and result['status']=='SOLVED'
                and isinstance(result.get('proposal'),dict),'Exact rational replay or its submitted recipe is unavailable')
        try:plan,value=replay_partial_fractions(task,library,result['proposal'])
        except PLAN_FAILURES+(KeyError,IndexError,TypeError,ValueError) as exc:
            require(False,'Invalid rational decomposition: '+str(exc))
        require(canonical(plan)==canonical(result['compilation']) and canonical(value)==canonical(result['value']),
                'The rational decomposition or original domain changed')
        return dict(status='passed',complete=True,checked_nodes=len(plan['terms']),
                    scope='primitive_derivative_identity_exact_open_domain_and_component_universal_family')
    proposal = result.get('proposal'); recipe_checked = 0
    try:
        plan = compile_integral(task,proposal['candidate_source'] if proposal is not None else None)
        if proposal is not None: recipe_checked = verify_recipe(task,plan,proposal,library)
        elif task.get('method_requirement') in RECIPE_REQUIRED: raise Unsupported('Method recipe missing')
    except (Unsupported,KeyError,TypeError,ResourceBound,ZeroDivisionError,NotRational,Undefined) as exc:
        require(False,'Primitive domain or candidate no longer admitted: '+str(exc))
    require(canonical(plan) == canonical(result['compilation']),'Primitive candidate/domain changed')
    require(result['status'] == 'SOLVED','Incomplete primitive artifact')
    checked = verify(result['child_result'],library,expected_task=plan['derivative_task'])
    try: family = conclusion(plan,result['child_result'],proposal)
    except Unsupported as exc: require(False,str(exc))
    require(canonical(family) == canonical(result['value']),'Primitive family or constants changed')
    return {**checked,'checked_nodes':checked['checked_nodes']+recipe_checked,'scope':'primitive_derivative_identity_exact_open_domain_and_component_universal_family'}


def rational_power_coordinate(f,x,symbol,request):
    if f[0]!='div':raise Unsupported('An exponential quotient is required')
    v=x[1];z=('v',symbol)
    def monomial(e):
        number=m.num(e)
        if number is not None:return number,Fraction(1)
        if e[0] in ('mul','div'):
            a,b=monomial(e[1]);c,d=monomial(e[2])
            if e[0]=='mul':return a*c,b*d
            if not c:raise Unsupported('A divided exponential monomial vanishes identically')
            return a/c,b/d
        if e[0]=='rpow' and not domain_conditions(e[1]) and not domain_conditions(e[2]):
            base=m.num(m.simplify(e[1]));a,b=affine(e[2],v);slope=m.num(a)
            if base is not None and base>0 and slope is not None and slope.denominator==1 and b==ZERO and abs(slope)<=24:
                return Fraction(1),base**int(slope)
        raise Unsupported('A real exponential monomial needs fixed positive rational bases and zero offset')
    def terms(e):
        if e[0]=='add':return [*terms(e[1]),*terms(e[2])]
        if e[0]=='mul' and m.num(e[1]) is not None and e[2][0]=='add':
            return [(m.num(e[1])*c,b) for c,b in terms(e[2])]
        return [monomial(e)]
    top,bottom=map(terms,f[1:])
    origin=min(b for _,b in bottom);ratios={b/origin for _,b in top+bottom}
    anchor=next((r for r in sorted(ratios) if r!=1),None)
    if anchor is None:raise Unsupported('No varying relative exponential scale')
    for n in range(24,0,-1):
        a=m.perfect_root(anchor.numerator,n);b=m.perfect_root(anchor.denominator,n)
        if a is not None and b is not None:
            base=Fraction(a,b)
            break
    ranks={base**j:j for j in range(-40,41)}
    if ratios-set(ranks):raise Unsupported('The relative exponential scales do not span one rational base')
    from functools import reduce
    def polynomial(rows):
        return reduce(m.add,(m.mul(q(c),m.power(z,ranks[b/origin])) for c,b in rows),ZERO)
    R,S=map(polynomial,(top,bottom))
    if S==ZERO:raise Unsupported('The original denominator is identically zero')
    inner=m.div(R,m.mul(z,S))
    H=integrate_child(request,inner,symbol);coordinate=('rpow',q(base),x)
    answer=m.div(m.substitute(H,{z:coordinate}),('ln',q(base)))
    return dict(theorem='method.primitive_coordinate_lift',chart='exponential_coordinate',
                common_factor_origin=q(origin),base=q(base),exponents=sorted((q(r),ranks[r]) for r in ratios),
                coordinate=coordinate,kernel=inner,argument=[
        'Разделяем числитель и знаменатель на одну строго положительную экспоненту. Все относительные основания — целые степени общего положительного основания.',
        'Подстановка монотонно отображает прямую на положительную полуось. Её дифференциал оставляет рациональный интеграл и множитель 1/ln основания.',
        'Исходные нули знаменателя остаются исключёнными. Возвращаем проверенную первообразную в исходную переменную.',
    ]),family(f,answer)


def rational_primitive_charts(task):
    text=task.get('integrand','')
    methods=('table_and_rules','appropriate_substitution','appropriate_integrand_transformation')
    printed=task.get('source',{})
    if (not isinstance(text,str) or task.get('method_requirement','table_and_rules') not in methods
            or not isinstance(printed,dict) or any(printed.get(key) not in (None,*methods)
                    for key in ('explicit_required_method','method_requirement'))):
        return ()
    if any(op+'(' in text for op in ('exp','sinh','cosh','tanh','coth')) or re.search(r'\d\s*\^\s*\(?'+re.escape(task.get('variable','x'))+r'\b',text):
        return ('exponential_coordinate',)
    if any(op+'(' in text for op in ('sin','cos','tan','cot','sec','csc')):return ('tangent_half_angle_coordinate',)
    return ()


def common_phase_rate(rates):
    from math import gcd,lcm
    rates=tuple(rates)
    denominator=lcm(*(k.denominator for k in rates))
    return Fraction(gcd(*(int(k*denominator) for k in rates)),denominator)


def join_periodic_integral(H,F,phase,symbol,ctx,request,seam_value):
    if seam_value is None:return F,dict(kind='source_pole',phase='(2*j+1)*pi')
    ends=[]
    for side,sign in (('positive_infinity','+inf'),('negative_infinity','-inf')):
        limit=request('primitive at '+sign,{'variable':symbol,'expression':source(H),'approach':{'point':sign,'side':side}})
        end=freeze(limit['value'])
        if not isinstance(end,tuple) or not m.constant_defined(end,ctx):raise Unsupported('A finite real join value is required')
        ends.append(end)
    jump=m.add(ends[0],m.neg(ends[1]))
    seam=dict(kind='continuous_join',phase='(2*j+1)*pi',source_value=seam_value,
              left_primitive_limit=ends[0],right_primitive_limit=ends[1],per_period_increment=jump)
    # Matching finite limits and continuity of f give the original derivative at a regular join.
    return ('joined_periodic_primitive',phase,F,jump,ends[0]),seam


def rational_coordinate_primitive(task,request,chart):
    """Transport one proved rational primitive, retaining the source poles and joining regular seams."""
    from math import gcd
    x,_,ctx,f=integral_source(task)
    symbol=kernel_symbol(task);z=('v',symbol)
    exponential=chart=='exponential_coordinate'
    if exponential and any(e[0]=='rpow' and e[1][0]=='q' for e in learned_nodes(f) if isinstance(e,tuple)):
        return rational_power_coordinate(f,('v',x),symbol,request)
    functions={'exp','sinh','cosh','tanh'} if exponential else {'sin','cos','tan','cot','sec','csc'}
    rates={}
    def collect(e):
        if e[0] in functions:
            if any(m.variable_in(g,x) or not known_guard((relation,g),ctx) for relation,g in domain_conditions(e[1])):
                raise Unsupported('A phase restriction must be checked before replacing its function')
            slope,offset=affine(e[1],x)
            rate=m.num(m.simplify(slope))
            if not rate or m.simplify(offset)!=ZERO:raise Unsupported('The chart needs commensurable unshifted arguments')
            rates[e]=rate
        elif e[0] not in ('q','add','mul','div','pow'):
            raise Unsupported('An independent coordinate, parameter or nonrational kernel remains')
        else:
            for child in e[1:]:
                if isinstance(child,tuple):collect(child)
    collect(f)
    if not rates:raise Unsupported('No coordinate generator occurs')
    unit=common_phase_rate(rates.values())
    phase=m.mul(q(unit),('v',x));coord=('exp',phase) if exponential else ('tan',m.div(phase,q(2)))
    replacements={};seam={}
    for atom,rate in rates.items():
        k=int(rate/unit);op=atom[0]
        if abs(k)>32:raise Unsupported('Harmonic exceeds the exact polynomial degree supported here')
        if exponential:
            pos=m.power(z,k);neg=m.power(z,-k)
            sh=m.div(m.add(pos,m.neg(neg)),q(2));ch=m.div(m.add(pos,neg),q(2))
            replacements[atom]={'exp':pos,'sinh':sh,'cosh':ch,'tanh':('div',sh,ch)}[op]
        else:
            # Real and imaginary parts of (1+i*z)^(2|k|)/(1+z^2)^|k|.
            def component(parity):
                coeff=[comb(2*abs(k),j)*(-1)**(j//2)*(1 if k>0 or parity==0 else -1) if j%2==parity else 0
                       for j in range(2*abs(k)+1)]
                return ('div',polynomial_expression(coeff,symbol),m.power(m.add(ONE,m.power(z,2)),abs(k)))
            sin,cos=component(1),component(0)
            def element(s,c):
                return {'sin':s,'cos':c,'tan':('div',s,c),'cot':('div',c,s),'csc':('div',ONE,s),'sec':('div',ONE,c)}[op]
            replacements[atom]=element(sin,cos);seam[atom]=element(ZERO,q((-1)**abs(k)))
    jac=m.div(ONE,m.mul(q(unit),z)) if exponential else m.div(q(2),m.mul(q(unit),m.add(ONE,m.power(z,2))))
    transformed=('mul',m.substitute(f,replacements),jac)
    try:
        p,d=rf(transformed,symbol);g=pgcd(p,d)
        p=pdiv(p,g)[0];d=pdiv(d,g)[0]
        inner=m.div(polynomial_expression(p,symbol),polynomial_expression(d,symbol))
        primary=inner;inner_coord=coord;secondary=None
        if exponential and any(p):
            i,j=valuation(p),valuation(d);shift=i-j+1
            k=gcd(shift,*(n-v for poly,v in ((p,i),(d,j)) for n,c in enumerate(poly) if c))
            if k>1:
                # R(z) dz = S(z^k) d(z^k); z>0 makes this a global coordinate.
                inner=m.div(m.mul(m.power(z,shift//k-1),polynomial_expression(p[i::k],symbol)),
                            m.mul(q(k),polynomial_expression(d[j::k],symbol)))
                u=m.power(z,k)
                check=m.mul(m.substitute(inner,{z:u}),m.mul(q(k),m.power(z,k-1)))
                if any(rf(('add',check,('mul',q(-1),primary)),symbol)[0]):raise Unsupported('Power descent changed the differential')
                secondary=u;inner_coord=m.power(coord,k)
    except (NotRational,Undefined) as exc:raise Unsupported('No rational pullback on a nonempty source component') from exc
    inner_task={'kind':'integrate','variable':symbol,'integrand':source(inner),'method_requirement':'table_and_rules'}
    proof=request('rational differential',inner_task)
    H=freeze(proof['value']['representative'])
    F=m.substitute(H,{z:inner_coord});domain=tuple(domain_conditions(f))
    plan={'chart':chart,'coordinate':coord,'phase':phase,'image':'positive reals' if exponential else 'real line on each open sheet',
          'dx_dcoordinate':jac,'identities':[(a,replacements[a]) for a in rates],'source_domain':domain,
          'primary_differential':primary,'secondary_coordinate':secondary,'inner_coordinate':inner_coord,'rational_differential':inner,'inner_primitive':H}
    if not exponential:
        try:seam_num,seam_den=rf(m.substitute(f,seam),symbol)
        except Undefined:seam_value=None
        else:
            if len(seam_num)!=1 or len(seam_den)!=1:raise Unsupported('Undecided source value at the half-angle seam')
            seam_value=q(seam_num[0]/seam_den[0])
        F,plan['seam']=join_periodic_integral(H,F,phase,symbol,ctx,request,seam_value)
    return plan,{'representative':F,'original_domain':('and',domain),'component_scope':'each maximal connected open component J of D',
        'family':'F|J + C_J','constant_policy':'independent real C_J for each original component, for each fixed parameter tuple',
        'identity':{'derivative_ast':f,'integrand_ast':f},'basis':'chain rule on chart sheets, continuity at each regular join and mean-value uniqueness'}


F=Fraction
TRIG_METHODS={'table_and_rules','trigonometric_difference_identities','logarithmic_trigonometric_denominator',
              'quadratic_canonical_form'}


def input_data(task,methods):
    fields={'kind','id','source','schema','transcription','integrand','variable','parameters','stated_conditions',
            'stated_domain','method_requirement','requested_output'}
    method=task.get('method_requirement','table_and_rules')
    requirements=task.get('source',{})
    wanted=task.get('requested_output',[])
    if (set(task)-fields or task.get('kind')!='integrate' or method not in methods
            or not isinstance(requirements,dict) or any(requirements.get(k) not in (None,method)
                for k in ('explicit_imposed_method','explicit_required_method','method_requirement'))
            or task.get('stated_domain') not in (None,[],()) or not isinstance(wanted,(tuple,list))
            or set(wanted)-{'primitive_family','natural_domain_components','constant_per_component'}):
        raise Unsupported('The requested primitive, original region or prescribed method is different')
    v=task.get('variable','x');p=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    ctx=m.context(dict(variable=v,parameters=p,parameter_conditions=conditions))
    return ('v',v),m.parse(task['integrand'],v,ctx['parameters']),ctx,method


def exact_sign(e,ctx):
    from ray_proofs import compare_scalar
    sign=m.sign(e,ctx)
    if sign is None:
        for orientation in (1,-1):
            for bound in ctx['positive_expressions']:
                gap=m.num(m.simplify(m.add(m.mul(q(orientation),e),m.neg(bound))))
                if gap is not None and gap>=0:return orientation
    if (sign is None and m.constant_defined(e,ctx)
            and not any(m.contains(e,('s',n)) for n in ctx['parameters'])):
        try:sign=compare_scalar(e,ZERO)
        except Unsupported:pass
    return sign


def family(raw,answer=None,*,branches=None,region=None):
    guards=domain_conditions(raw)
    result=dict(original_domain=('and',guards),real_domain=region or ('and',guards),family='F|J + C_J',
                constant_policy='independent real C_J on each original component, for fixed source parameters')
    if branches is not None:return dict(result,parameter_cases=branches)
    return dict(result,representative=answer,identity=dict(derivative_ast=raw,integrand_ast=raw))


def lnabs(e):
    return ('ln',('abs',e))


def difference_phase(task):
    from verify import same_value
    x,f,ctx,method=input_data(task,TRIG_METHODS)
    if method=='logarithmic_trigonometric_denominator' or task.get('stated_conditions'):
        raise Unsupported('A different printed trigonometric transition is required')
    v=x[1];coeff=ONE;rest=ZERO
    def phase(a):
        if a[0]=='sin':return a[1]
        if a[0]=='cos':return m.add(a[1],m.div(m.PI,q(2)))
        raise Unsupported('Two shifted sine or cosine factors are needed')
    if f[0]=='mul' and all(z[0]=='tan' for z in f[1:]):
        g,h=(z[1] for z in f[1:])
        k,c=affine(g,v);l,d=affine(h,v)
        if not same_value(k,l):raise Unsupported('The two phase rates must be equal')
        coeff=('cos',m.add(c,m.neg(d)));rest=m.neg(x)
        u,w=(phase(('cos',z)) for z in (g,h))
    elif f[0]=='div' and f[1]==ONE and f[2][0]=='mul':
        u,w=map(phase,f[2][1:])
    elif f[0]=='div' and f[1]==ONE and f[2][0]=='add':
        g,h=f[2][1:]
        if not m.variable_in(g,v):g,h=h,g
        if g[0]=='sin' and h[0]=='mul' and h[1]==q(-1) and h[2][0]=='sin':
            a,b=g[1],h[2][1]
            u=phase(('cos',m.div(m.add(a,b),q(2))))
            w=m.div(m.add(a,m.neg(b)),q(2))
        elif g[0]=='cos' and h[0]=='cos':
            a,b=g[1],h[1]
            u,w=(phase(('cos',m.div(m.add(a,z),q(2)))) for z in (b,m.neg(b)))
        else:raise Unsupported('No printed sum-to-product identity applies')
        if not m.constant_defined(b,ctx):raise Unsupported('The second original angle must be fixed and real')
        coeff=q(1,2)
    else:raise Unsupported('No shifted trigonometric ratio appears in the original')
    k,c=affine(u,v);j,d=affine(w,v)
    if (not same_value(k,j) or exact_sign(k,ctx) not in (-1,1)
            or not all(m.constant_defined(z,ctx) for z in (c,d)) or any(domain_conditions(z) for z in (u,w))):
        raise Unsupported('A common nonzero rate and everywhere defined affine angles are required')
    delta=m.simplify(m.add(c,m.neg(d)));s=('sin',delta)
    b=m.div(m.add(lnabs(('sin',w)),m.neg(lnabs(('sin',u)))),m.mul(k,s))
    repeated=m.neg(m.div(m.mul(('cos',delta),('cot',w)),k))
    combine=lambda e:m.add(rest,m.mul(coeff,e))
    region=dict(excluded_phases=[u,w],condition='sin(u)*sin(w)!=0',
                components='open intervals between the original consecutive pole locations')
    case_value=None;sign=exact_sign(s,ctx)
    if sign is None:
        case_value=[dict(condition=source(s)+'!=0',representative=combine(b),components=region),
                    dict(condition=source(s)+'=0',representative=combine(repeated),components=region)]
    answer=combine(repeated if sign==0 else b)
    plan=dict(theorem='method.trig_phase_difference',chart='phase_difference',phases=(u,w),rate=k,delta=delta,
              coalescence=s,argument=[
        'Bring the required product or difference to the product of two sine phases with the same rate.',
        'The sine of the phase difference gives cot(w)−cot(u) after division by the original product.',
        'If the sine of the phase difference is zero, the two sine factors differ only by a sign. Integrate the remaining cosecant square.',
    ])
    return plan,family(f,answer,branches=case_value,region=region)


def trig_polynomial(e,x):
    """Collect the exact coefficients of sin(x) and cos(x) powers."""
    S,C=('sin',x),('cos',x)
    p,d=m.rational_form(e)
    if set(d)!={()} or not d[()]:raise Unsupported('The trigonometric coefficient must be polynomial')
    rows={}
    for mon,c in p.items():
        powers=dict(mon);degree=(powers.pop(S,0),powers.pop(C,0))
        const=m.poly_expr({tuple(powers.items()):c/d[()]})
        if m.variable_in(const,x[1]):raise Unsupported('An unsupported phase occurs in the trigonometric polynomial')
        rows[degree]=m.add(rows.get(degree,ZERO),const)
    return {k:m.simplify(z) for k,z in rows.items() if z!=ZERO}


def trig_linear_seed(x,ctx,a,b,c,k=ONE):
    """A logarithmic seed or a half-angle map with quantified regular joins."""
    x0=m.mul(k,x);S,C=('sin',x0),('cos',x0)
    H=m.add(m.mul(a,S),m.mul(b,C));J=m.add(m.mul(a,C),m.neg(m.mul(b,S)))
    R2=m.add(m.power(a,2),m.power(b,2));D=m.add(c,H);delta=m.simplify(m.add(m.power(c,2),m.neg(R2)))
    if c==ZERO:
        R=('sqrt',R2);left=m.add(R,m.neg(J));right=m.add(R,J)
        answer=m.div(('ln',m.div(left,right)),m.mul(q(2),m.mul(k,R)))
        return answer,dict(denominator=D,phase_derivative=J,amplitude_squared=R2,branch='R²>0, D!=0',
                           identity='R²=H²+J² implies R±J>0 at H!=0')
    t=('tan',m.div(x0,q(2)))
    A=m.simplify(m.add(c,m.neg(b)));B=m.simplify(m.add(c,b));U=m.add(m.mul(A,t),a)
    sign=exact_sign(delta,ctx);leading=exact_sign(A,ctx)
    if sign is None:
        # A real nonzero amplitude bounds the linear half-angle quadratic
        # whenever c and b are the same proved positive/negative phase.
        if a==ZERO and (other:=exact_sign(B,ctx)) in (-1,1) and leading in (-1,1):
            sign=leading*other
        else:raise Unsupported('The quadratic discriminant needs a proved parameter branch')
    if leading==0:
        if a==ZERO:
            if exact_sign(B,ctx) not in (-1,1):raise Unsupported('No nonzero half-angle denominator')
            seed=m.div(m.mul(q(2),t),B)
        else:
            seed=m.div(lnabs(m.add(m.mul(q(2),m.mul(a,t)),B)),a)
        answer=m.div(seed,k);left=None;join=None
    else:
        if leading not in (-1,1):raise Unsupported('The seam value needs a proved nonzero sign')
        if sign==1:
            L=('sqrt',delta);seed=m.div(m.mul(q(2),('atan',m.div(U,L))),m.mul(k,L))
            left=m.div(m.mul(q(leading),m.PI),m.mul(k,L));join=m.mul(q(2),left)
        elif sign==-1:
            L=('sqrt',m.neg(delta))
            seed=m.div(lnabs(m.div(m.add(U,m.neg(L)),m.add(U,L))),m.mul(k,L))
            left=join=ZERO
        else:
            seed=m.div(q(-2),m.mul(k,U));left=join=ZERO
        answer=('joined_periodic_primitive',x0,seed,join,left)
    return answer,dict(denominator=D,quadratic_coefficients=(B,m.mul(q(2),a),A),discriminant_complement=delta,
                       seam_value=A,seam_is_original_pole=leading==0,limit_from_left_sheet=left,per_turn_increment=join)


def trig_quotient_decomposition(P,D):
    a,b,c=(D.get(key,ZERO) for key in ((1,0),(0,1),(0,0)))
    R2=m.add(m.power(a,2),m.power(b,2))
    if R2==ZERO:raise Unsupported('The denominator has no trigonometric amplitude')
    def resolve(p,r):
        return (m.div(m.add(m.mul(p,a),m.mul(r,b)),R2),
                m.div(m.add(m.mul(r,a),m.neg(m.mul(p,b))),R2))
    if set(P)<={(0,0),(1,0),(0,1)}:
        p,r,s=(P.get(key,ZERO) for key in ((1,0),(0,1),(0,0)))
        A,B=resolve(p,r)
        return 'linear',A,B,m.add(s,m.neg(m.mul(A,c)))
    if c==ZERO and set(P)<={(0,0),(2,0),(1,1),(0,2)}:
        p,cross,r=(P.get(key,ZERO) for key in ((2,0),(1,1),(0,2)))
        A,B=resolve(m.add(p,m.neg(r)),cross)
        return 'quadratic',A,B,m.add(m.add(p,m.neg(m.mul(a,A))),P.get((0,0),ZERO))
    raise Unsupported('The original numerator needs another trigonometric decomposition')


def trig_linear_primitive(task):
    x,f,ctx,method=input_data(task,TRIG_METHODS)
    if method=='trigonometric_difference_identities' or f[0]!='div':
        raise Unsupported('The requested source proof is not a linear trigonometric quotient')
    top,den=f[1:];n=1
    if m.contains(f,('tan',x)):
        raw=m.substitute(f,{('tan',x):m.div(('sin',x),('cos',x))})
        top_pol,den_pol=m.rational_form(raw)
        top,den=m.poly_expr(top_pol),m.poly_expr(den_pol)
    if den[0]=='pow' and type(den[2]) is int and den[2]>1:
        den,n=den[1:]
    D=trig_polynomial(den,x);P=trig_polynomial(top,x)
    if set(D)-{(0,0),(1,0),(0,1)} or not set(D)&{(1,0),(0,1)}:
        raise Unsupported('One linear trigonometric denominator is needed')
    if method=='logarithmic_trigonometric_denominator' and (top!=ONE or n!=1 or (0,0) in D):
        raise Unsupported('The printed logarithmic denominator method needs a homogeneous first power')
    a,b,c=(D.get(key,ZERO) for key in ((1,0),(0,1),(0,0)))
    S,C=('sin',x),('cos',x);R2=m.add(m.power(a,2),m.power(b,2))
    if not all(m.constant_defined(z,ctx) for z in (*D.values(),*P.values())):
        raise Unsupported('Every trigonometric coefficient must be real on the stated parameter set')
    delta=m.simplify(m.add(m.power(c,2),m.neg(R2)))
    H=m.add(m.mul(a,S),m.mul(b,C));J=m.add(m.mul(a,C),m.neg(m.mul(b,S)))
    base,record=trig_linear_seed(x,ctx,a,b,c)
    moments=[x,base];proof=[]
    for j in range(2,n+1):
        if not (c==ZERO or exact_sign(delta,ctx) in (-1,1)
                or a==ZERO and all(exact_sign(z,ctx) in (-1,1) for z in (m.add(c,b),m.add(c,m.neg(b))))):
            raise Unsupported('The reduction divides by a possibly zero discriminant complement')
        term=m.div(J,m.power(den,j-1))
        term=m.add(term,m.mul(q(2-j),moments[j-2]))
        term=m.add(term,m.mul(m.mul(q(2*j-3),c),moments[j-1]))
        moments.append(m.div(term,m.mul(q(j-1),delta)))
        proof.append(j)
    mode,A,B,residue=trig_quotient_decomposition(P,D)
    if mode=='linear':
        derivative=lnabs(den) if n==1 else m.div(m.power(den,1-n),q(1-n))
        answer=m.add(m.add(m.mul(A,moments[n-1]),m.mul(B,derivative)),m.mul(residue,moments[n]))
        decomposition=dict(linear=(A,B,residue),identity='numerator=A*D+B*D′+residue')
    elif n==1:
        answer=m.add(m.add(m.neg(m.mul(A,C)),m.mul(B,S)),m.mul(residue,base))
        decomposition=dict(quadratic=(A,B,residue),identity='numerator=(A sin x+B cos x)D+residue')
    else:raise Unsupported('The quadratic numerator requires a denominator of order one')
    plan=dict(theorem='method.trig_linear_rational',chart='trig_linear',seed=record,numerator=sorted(P.items()),denominator=sorted(D.items()),
              decomposition=decomposition,reduction_orders=proof,argument=[
        'Resolve the numerator using the denominator, its derivative and a constant or a linear trigonometric quotient.',
        'Integrate the residual kernel with its logarithmic identity or the half-angle quadratic. Join consecutive regular charts by the matching one-sided limits.',
        'For higher powers differentiate D′/D^(n−1), using D″=−(D−c) and (D′)²=R²−(D−c)².',
    ])
    region=dict(denominator=den,condition='D!=0',
                components='every open interval between consecutive zeros of D, joined at artificial chart seams')
    sign=1 if any(exact_sign(z,ctx) in (-1,1) for z in (a,b)) else exact_sign(R2,ctx)
    if sign==1 or not ctx['parameters']:return plan,family(f,answer,region=region)
    if c!=ZERO:raise Unsupported('The zero-amplitude parameter branch also needs proof')
    branches=[dict(condition=source(R2)+'>0',representative=answer,components=region),
              dict(condition=source(R2)+'=0',components='no real source point')]
    return plan,family(f,branches=branches,region=region)


def symmetric_coefficients(rows):
    """Lower symmetric even powers to the product p=sin²(x) cos²(x)."""
    from polynomial import pa,pm
    if any(i%2 or j%2 or m.num(c) is None or c!=rows.get((j,i)) for (i,j),c in rows.items()):
        raise Unsupported('This polynomial is not symmetric in the squared trigonometric coordinates')
    result=(F(0),)
    max_degree=max((abs(i-j)//2 for i,j in rows),default=0)
    sums=[(F(2),),(F(1),)]
    for n in range(2,max_degree+1):sums.append(pa(sums[-1],pm((F(0),F(-1)),sums[-2])))
    for (i,j),coefficient in rows.items():
        if i<j:continue
        c=m.num(coefficient)
        monomial=(F(0),)*(j//2)+(c,)
        result=pa(result,monomial if i==j else pm(monomial,sums[(i-j)//2]))
    return result


def integrate_child(request,term,v):
    t=dict(kind='integrate',variable=v,integrand=source(term),requested_output=['primitive_family'])
    return freeze(request('primitive in the verified new coordinate',t)['value']['representative'])


def trig_symmetry(task,request):
    from verify import same_value
    from graphs import rational_roots
    from plane_domains import yterm
    from polynomial import pdiv
    x,f,ctx,method=input_data(task,{'table_and_rules'})
    if ctx['parameters'] or task.get('stated_conditions') or f[0]!='div':
        raise Unsupported('The symmetry reduction has no proved parameter branch')
    name=kernel_symbol(task);t=('v',name);S,C=('sin',x),('cos',x)
    numerator,denominator=f[1:]
    P=trig_polynomial(numerator,x);Q=trig_polynomial(denominator,x)
    dy=m.mul(q(2),m.mul(S,C));double=m.mul(q(2),x)
    antisymmetric=m.add(P.get((2,0),ZERO),P.get((0,0),ZERO))
    reverse=m.add(P.get((0,2),ZERO),P.get((0,0),ZERO))
    if set(P)=={(1,1)} and all(not j and i%2==0 for i,j in Q):
        degree=max((i//2 for i,j in Q),default=0)
        radical=polynomial_expression(tuple(m.num(Q.get((2*i,0),ZERO)) for i in range(degree+1)),name)
        sub=m.div(P[1,1],m.mul(q(2),radical));u=m.power(S,2)
        H=integrate_child(request,sub,name);answer=m.substitute(H,{t:u})
        evidence=dict(coordinate=u,coordinate_derivative=dy,kernel=sub)
        argument=['The product sin x cos x is half of the derivative of sin²x. Use a polynomial in that squared coordinate.',
                  'Apply the chain rule also at stationary points, and keep all original denominator exclusions.']
    elif set(P)<={(2,0),(0,2),(0,0)} and antisymmetric!=ZERO and same_value(antisymmetric,m.neg(reverse)):
        row=symmetric_coefficients(Q);u=('sin',double)
        kernel=m.substitute(polynomial_expression(row,name),{t:m.div(m.power(t,2),q(4))})
        sub=m.div(m.div(m.neg(antisymmetric),q(2)),kernel)
        if len(row)==2 and all(row):
            c,a=row[0],row[1]/4;delta=q(a*c)
            L=('sqrt',delta if a*c>0 else m.neg(delta));w=m.mul(q(a),u)
            seed=m.div(('atan',m.div(w,L)),L) if a*c>0 else m.div(lnabs(m.div(m.add(w,m.neg(L)),m.add(w,L))),m.mul(q(2),L))
            answer=m.mul(m.div(m.neg(antisymmetric),q(2)),seed)
        else:
            H=integrate_child(request,sub,name);answer=m.substitute(H,{t:u})
        evidence=dict(coordinate=u,kernel=sub,product_identity='sin²x cos²x = sin²(2x)/4')
        argument=['The difference of squared sine and cosine is minus the cosine of the double angle.',
                  'Use the sine of the double angle as the coordinate and integrate its rational polynomial.']
    else:
        pn=symmetric_coefficients(P);dn=symmetric_coefficients(Q)
        W,R=pdiv(pn,dn)
        if len(W)!=1 or not 2<=len(dn)<=3:raise Unsupported('This reciprocal product needs a higher polynomial decomposition')
        roots=rational_roots(dn);slopes=tuple(j*c for j,c in enumerate(dn) if j)
        if len(roots)!=len(dn)-1 or len({yterm(r) for r in roots})!=len(roots):
            raise Unsupported('The scalar quotient needs all its simple real poles')
        evaluate=lambda row,z:m.substitute(polynomial_expression(row,name),{t:z})
        answer=m.mul(q(W[0]),x);components=[]
        for r in roots:
            point=yterm(r);D=evaluate(slopes,point)
            if exact_sign(D,ctx) not in (-1,1):raise Unsupported('A simple partial fraction was not established')
            weight=m.div(evaluate(R,point),D)
            seed,record=trig_linear_seed(x,ctx,ZERO,q(-1,8),m.add(q(1,8),m.neg(point)),k=q(4))
            answer=m.add(answer,m.mul(weight,seed));components.append(dict(root=point,weight=weight,seed=record))
        evidence=dict(numerator=tuple(map(q,pn)),denominator=tuple(map(q,dn)),partial_fractions=components)
        argument=['Use p=sin²x cos²x and sin²x+cos²x=1. Symmetric power sums satisfy Pₙ=Pₙ₋₁−pPₙ₋₂.',
                  'Decompose the resulting quotient in p. Then p=(1−cos(4x))/8 gives simple linear wave denominators.',
                  'On regular half-angle seams use the equal primitive limits after adding the per-turn increment.']
    plan=dict(theorem='method.trig_symmetric_coordinate',chart='trig_symmetry',argument=argument,**evidence)
    return plan,family(f,answer,region=dict(guards=domain_conditions(f),components='intervals between consecutive original real poles'))


def diagonal_trig_primitive(task,request):
    """Use orthogonal coordinates on the unit circle before integrating the linear numerator."""
    x,f,ctx,method=input_data(task,{'table_and_rules'})
    if ctx['parameters'] or task.get('stated_conditions') or f[0]!='div':
        raise Unsupported('A fixed quadratic trigonometric denominator is required')
    P,D=f[1:];S,C=('sin',x),('cos',x);wrapped=D[0]=='sqrt'
    Q=D[1] if wrapped else D
    Q=m.substitute(Q,{('sin',m.mul(q(2),x)):m.mul(q(2),m.mul(S,C)),
                      ('cos',m.mul(q(2),x)):m.add(m.power(C,2),m.neg(m.power(S,2)))})
    p=trig_polynomial(P,x);d=trig_polynomial(Q,x)
    if not p or not d or set(p)-{(1,0),(0,1)} or set(d)-{(2,0),(1,1),(0,2),(0,0)}:
        raise Unsupported('The numerator and denominator do not supply the quadratic form and linear projection')
    a,b,c,e=(m.num(d.get(z,ZERO)) for z in ((2,0),(1,1),(0,2),(0,0)))
    if None in (a,b,c,e):raise Unsupported('The quadratic form needs exact fixed coefficients')
    a+=e;c+=e;b/=2
    if b:
        diff=m.simplify(('sqrt',q((a-c)**2+4*b*b)));dg=m.num(diff)
        if dg is None:raise Unsupported('Exact rational eigenvalues are needed for the present primitive kernel')
        l=(a+c-dg)/2;h=(a+c+dg)/2
        u,v=q(b),q(l-a);norm=('sqrt',q(b*b+(l-a)**2))
        u=m.div(u,norm);v=m.div(v,norm)
    else:l,h=a,c;u,v=ONE,ZERO
    U=m.add(m.mul(u,S),m.mul(v,C));V=m.add(m.neg(m.mul(v,S)),m.mul(u,C))
    u_weight=m.add(m.mul(u,p.get((1,0),ZERO)),m.mul(v,p.get((0,1),ZERO)))
    v_weight=m.add(m.neg(m.mul(v,p.get((1,0),ZERO))),m.mul(u,p.get((0,1),ZERO)))
    name=kernel_symbol(task);t=('v',name);answer=ZERO;reductions=[]
    for y,scale,offset,coefficient in ((V,h-l,l,m.neg(u_weight)),(U,l-h,h,v_weight)):
        if m.simplify(coefficient)==ZERO:continue
        g=m.add(q(offset),m.mul(q(scale),m.power(t,2)))
        regular=('sqrt',g) if wrapped else g
        kernel=m.div(ONE,regular);F0=integrate_child(request,kernel,name)
        answer=m.add(answer,m.mul(coefficient,m.substitute(F0,{t:y})))
        reductions.append(dict(coordinate=y,kernel=kernel,weight=coefficient))
    plan=dict(theorem='method.trig_symmetric_coordinate',chart='trig_diagonal',
              orthogonal_frame=((u,v),(m.neg(v),u)),eigenvalues=(q(l),q(h)),reductions=reductions,argument=[
        'Diagonalize the exact quadratic form on the unit circle. Its coordinates satisfy U′=V and V′=−U.',
        'Split the numerator into U and V. Use the other coordinate in each integral to obtain a quadratic kernel.',
        'The substitutions preserve the original denominator signs and do not cut the domain at stationary points.',
    ])
    return plan,family(f,answer,region=dict(guards=domain_conditions(f),components='maximal original real intervals'))


def tangent_quadratic_primitive(task):
    """Compare even numerator coefficients in the ordinary tangent coordinate."""
    x,f,ctx,method=input_data(task,{'table_and_rules'})
    if task.get('stated_conditions') or f[0]!='div':raise Unsupported('The even quadratic rule needs complete parameter branches')
    top,den=f[1:];n=1
    if den[0]=='pow' and den[2]==2:den,n=den[1:]
    P=trig_polynomial(top,x);Q=trig_polynomial(den,x);degrees={(0,0),(2,0),(0,2)}
    if set(P)-degrees or set(Q)-degrees:raise Unsupported('The tangent rule needs an even quadratic quotient')
    def coefficients(rows):
        return [m.simplify(m.add(rows.get(k,ZERO),rows.get((0,0),ZERO))) for k in ((2,0),(0,2))]
    p,r=coefficients(P);a,b=coefficients(Q)
    def nonnegative(z):
        return exact_sign(z,ctx) in (0,1) or (z[0]=='pow' and z[2]==2 and m.constant_defined(z[1],ctx))
    if not all(nonnegative(z) for z in (a,b)):
        raise Unsupported('The original quadratic weights must be positive or genuine squares')
    t=('tan',x);cot=('cot',x);S,C=('sin',x),('cos',x);ar,br=('sqrt',a),('sqrt',b)
    mode1=m.div(('atan',m.div(m.mul(ar,t),br)),m.mul(ar,br))
    left=m.div(m.PI,m.mul(q(2),m.mul(ar,br)))
    J=('joined_periodic_primitive',m.mul(q(2),x),mode1,m.mul(q(2),left),left)
    if n==1 and p==r:
        ans=m.mul(p,J);zero_a=m.div(m.mul(r,t),b);zero_b=m.neg(m.div(m.mul(p,cot),a))
    elif n==1:
        if not all(m.num(z) is not None for z in (a,b,p,r)) or exact_sign(a,ctx)!=1 or exact_sign(b,ctx)!=1:
            raise Unsupported('The nonconstant even numerator needs verified fixed quadratic weights')
        if a==b:
            mean=m.div(m.add(p,r),q(2));osc=m.div(m.add(r,m.neg(p)),q(4))
            ans=m.div(m.add(m.mul(mean,x),m.mul(osc,('sin',m.mul(q(2),x)))),a)
        else:
            mean=m.div(m.add(p,m.neg(r)),m.add(a,m.neg(b)))
            ans=m.add(m.mul(mean,x),m.mul(m.add(r,m.neg(m.mul(mean,b))),J))
        zero_a=zero_b=None
    elif n==2 and p==ZERO:
        kernel=m.add(m.mul(a,m.power(t,2)),b)
        ans=m.div(m.mul(r,m.add(m.div(t,kernel),J)),m.mul(q(2),b))
        zero_a=m.div(m.mul(r,t),m.power(b,2));zero_b=m.neg(m.div(m.mul(r,m.power(cot,3)),m.mul(q(3),m.power(a,2))))
    elif n==2 and p==r and exact_sign(a,ctx)==1 and exact_sign(b,ctx)==1:
        kernel=m.add(m.mul(a,m.power(t,2)),b)
        scale=m.div(p,a);residue=m.add(p,m.neg(m.mul(scale,b)))
        ans=m.add(m.mul(scale,J),m.mul(m.div(residue,m.mul(q(2),b)),m.add(m.div(t,kernel),J)))
        zero_a=zero_b=None
    else:raise Unsupported('This even numerator has no one-coordinate quadratic reduction')
    plan=dict(theorem='method.trig_symmetric_coordinate',chart='trig_tangent',quadratic_weights=(a,b),
              numerator_weights=(p,r),power=n,argument=[
        'Use sin²x+cos²x=1 to separate the two diagonal quadratic coefficients.',
        'On each tangent sheet the differential is rational. With both coefficients positive, arctangent has finite limits which determine the additive period increment.',
        'If one coefficient vanishes, the corresponding secant or cosecant expression supplies all original components without changing their excluded points.',
    ])
    region=dict(guards=domain_conditions(f),components='maximal open intervals between the original poles')
    if exact_sign(a,ctx)==1 and exact_sign(b,ctx)==1:return plan,family(f,ans,region=region)
    if zero_a is None or zero_b is None:raise Unsupported('The zero-weight branches remain unresolved')
    branches=[dict(condition=source(a)+'>0 and '+source(b)+'>0',representative=ans,components='all real x'),
              dict(condition=source(a)+'=0 and '+source(b)+'>0',representative=zero_a,components='cos x != 0'),
              dict(condition=source(a)+'>0 and '+source(b)+'=0',representative=zero_b,components='sin x != 0'),
              dict(condition=source(a)+'=0 and '+source(b)+'=0',components='no defined source points')]
    return plan,family(f,branches=branches,region=region)


def separate_weight(e,weight):
    """Split an explicit multiplicative generator without cancelling its guards."""
    if e==weight:return ONE,1
    if e[0] in ('mul','div'):
        R,j=separate_weight(e[1],weight);S,k=separate_weight(e[2],weight)
        return (m.mul(R,S),j+k) if e[0]=='mul' else (m.div(R,S),j-k)
    if m.contains(e,weight):raise Unsupported('The proposed weight is not multiplicative in the original expression')
    return e,0


def exponential_primitive(task):
    """Compare exact coefficients of G′+kG and the remaining simple poles."""
    from graphs import rational_roots
    from polynomial import rf,pp,pdiv,pgcd,pm,pa,span_coefficients,NotRational,Undefined
    x,f,ctx,method=input_data(task,{'table_and_rules'})
    if ctx['parameters'] or task.get('stated_conditions'):raise Unsupported('The exponential rate must be fixed')
    v=x[1];waves=list(dict.fromkeys(e for e in learned_nodes(f) if isinstance(e,tuple) and e[0]=='exp'))
    if len(waves)!=1:raise Unsupported('One exponential weight is required')
    wave,=waves;rate,offset=affine(wave[1],v);k=m.num(m.simplify(rate))
    if not k or not m.constant_defined(offset,ctx) or domain_conditions(wave):
        raise Unsupported('The original exponential rate must be nonzero and its arguments defined')
    R,n=separate_weight(f,wave)
    if n!=1:raise Unsupported('One factor of the original exponential is required')
    try:p,d=rf(R,v)
    except (NotRational,Undefined):
        return exponential_half_angle(x,f,wave,k,R,ctx)
    common=pgcd(p,d);p,d=pdiv(p,common)[0],pdiv(d,common)[0]
    quotient,_=pdiv(p,d)
    if len(d)==1 and len(quotient)<2:raise Unsupported('A nonconstant rational weight is required for this transition')
    roots=rational_roots(d)
    if any(z.b for z in roots):raise Unsupported('The residual exponential terms need rational real poles')
    columns=[];basis=[];pole_count=0
    def add_column(column,term,special=False):
        columns.append(column);basis.append((term,special))
    for j in range(len(quotient)) if any(quotient) else ():
        P=(F(0),)*j+(k,)
        if j:P=pa(P,(F(0),)*(j-1)+(F(j),))
        add_column(pm(d,P),m.power(x,j))
    for root in roots:
        r=root.a;linear=(-r,F(1));shift=m.add(x,q(-r));j=1
        while not any(pdiv(d,pp(linear,j))[1]):
            j+=1
        multiplicity=j-1;pole_count+=multiplicity
        for j in range(1,multiplicity):
            core=pa((F(-j),),pm((k,),linear))
            add_column(pm(core,pdiv(d,pp(linear,j+1))[0]),m.power(shift,-j))
        add_column(pdiv(d,linear)[0],q(r),True)
    if pole_count!=len(d)-1:raise Unsupported('The rational denominator needs all its real pole factors')
    weights=span_coefficients(p,columns)
    if weights is None:raise Unsupported('The coefficient identities do not reconstruct the source rational field')
    G=ZERO;extra=ZERO;residues=[]
    for w,(term,special) in zip(weights,basis,strict=True):
        if not w:continue
        if special:
            t=m.mul(rate,m.add(x,m.neg(term)))
            value=('logarithmic_integral',('exp',t))
            scale=m.mul(q(w),('exp',m.add(offset,m.mul(rate,term))))
            extra=m.add(extra,m.mul(scale,value))
            residues.append(dict(pole=term,residual=q(w),special_argument=('exp',t)))
        else:G=m.add(G,m.mul(q(w),term))
    answer=m.add(m.mul(wave,G),extra)
    plan=dict(theorem='method.exponential_rational_poles',chart='exponential_poles',rate=rate,
              rational_coefficient=R,rational_part=G,residues=residues,argument=[
        'Compare coefficients in G′+kG plus a sum of simple fractions with the original rational weight.',
        'The rational part is the derivative of e^(kx+c)G. A simple pole at r uses li(e^(k(x−r))) with the fixed exponential scale.',
        'On each source interval the logarithmic integral has derivative 1/ln t, with independent constants across t=1.',
    ])
    return plan,family(f,answer,region=dict(guards=domain_conditions(f),components='intervals between all original real poles'))


def exponential_half_angle(x,f,wave,k,R,ctx):
    """Use the same coefficient comparison in a half-angle polynomial."""
    from polynomial import rf,pa,pgcd,pdiv,span_coefficients,NotRational,Undefined
    v=x[1];t=('v','__half_angle');S,C=('sin',x),('cos',x)
    den=m.add(ONE,m.power(t,2));s=m.div(m.mul(q(2),t),den);c=m.div(m.add(ONE,m.neg(m.power(t,2))),den)
    try:p,d=rf(m.substitute(R,{S:s,C:c}),t[1])
    except (NotRational,Undefined) as exc:raise Unsupported('No polynomial rational weight in the half-angle coordinate') from exc
    g=pgcd(p,d);p,d=pdiv(p,g)[0],pdiv(d,g)[0]
    if len(d)!=1:raise Unsupported('The half-angle weight has an unresolved rational pole')
    p=tuple(z/d[0] for z in p);degree=len(p)-1;columns=[]
    for j in range(max(1,degree)):
        P=(F(0),)*j+(k,)
        if j:P=pa(P,(F(0),)*(j-1)+(F(j,2),F(0),F(j,2)))
        columns.append(P)
    weights=span_coefficients(p,columns)
    if weights is None:raise Unsupported('The half-angle polynomial derivative system has no matching coefficients')
    seam=m.substitute(R,{S:ZERO,C:q(-1)})
    if any(weights[1:]) and m.constant_defined(seam,ctx):
        raise Unsupported('A genuine original pole at the half-angle seam has not been proved')
    G=polynomial_expression(weights,t[1]);coordinate=('tan',m.div(x,q(2)))
    answer=m.mul(wave,m.substitute(G,{t:coordinate}))
    plan=dict(theorem='method.exponential_rational_poles',chart='exponential_poles',half_angle=coordinate,
              rational_part=G,rate=q(k),coefficients=list(map(q,weights)),argument=[
        'Rationalize the wave part by t=tan(x/2), retaining the original exclusions at chart ends.',
        'Compare coefficients in kG+(1+t²)G′/2 to verify the derivative of e^(kx+c)G(t).',
    ])
    return plan,family(f,answer)


def lifted_scales(task,request):
    """Transport a primitive through a real square-root or exponential coordinate."""
    from verify import same_value
    x,f,ctx,method=input_data(task,{'table_and_rules'})
    if ctx['parameters'] or task.get('stated_conditions'):raise Unsupported('The original real shape has an unproved parameter')
    v=x[1];name=kernel_symbol(task);t=('v',name)
    nodes=list(learned_nodes(f));root=('sqrt',x)
    waves=list(dict.fromkeys(e for e in nodes if isinstance(e,tuple) and e[0]=='exp'))
    if root in nodes:
        coordinate=root;X=m.power(t,2);jac=m.mul(q(2),t);image='t>=0'
        kernel=m.simplify(m.mul(m.substitute(f,{x:X,root:t}),jac))
        if any(g!=('nonnegative',x) for g in domain_conditions(f)):
            raise Unsupported('A further original guard is not known on the entire square-root branch')
    elif len(waves)==1 and any(isinstance(e,tuple) and e[0] in ('sqrt','asin','atan') and m.contains(e,waves[0]) for e in nodes):
        wave,=waves;rate,offset=affine(wave[1],v)
        changed=m.substitute(f,{wave:t})
        if m.variable_in(changed,v) or not m.num(m.simplify(rate)) or domain_conditions(wave):
            raise Unsupported('The exponential coordinate does not cover every original occurrence and restriction')
        jac=m.div(ONE,m.mul(rate,t));kernel=m.mul(changed,jac)
        H=integrate_child(request,kernel,name)
        answer=m.substitute(H,{t:wave})
        X=m.div(m.add(('ln',t),m.neg(offset)),rate)
        region=dict(image='t>0 with the transported original guards',coordinate=wave,inverse=X)
        return dict(theorem='method.primitive_coordinate_lift',chart='lifted_scales',coordinate=wave,inverse=X,
                    jacobian=jac,kernel=kernel,argument=[
            'The real exponential coordinate maps the line monotonically to the positive half-line.',
            'Divide by the verified derivative of the new coordinate, replay the inner primitive, and restrict it to the actual image.',
        ]),family(f,answer,region=region)
    elif f[0]=='mul' and any(e[0]=='rpow' for e in f[1:]):
        power=next(e for e in f[1:] if e[0]=='rpow');outer=f[2] if power==f[1] else f[1]
        base,exponent=power[1:];a,_=affine(base,v);k,_=affine(exponent,v)
        rate=m.add(m.mul(k,('ln',base)),m.div(m.mul(a,exponent),base))
        if not same_value(rate,outer) or any(g[1]!=base for g in domain_conditions(f)):
            raise Unsupported('The original differential does not match the logarithmic derivative of the real power')
        return dict(theorem='method.primitive_coordinate_lift',chart='lifted_scales',argument=[
            'Rewrite the real power on its positive base as exp(exponent·ln(base)).',
            'The product rule verifies the full logarithmic derivative supplied in the integrand.',
        ],logarithmic_rate=rate),family(f,power)
    else:raise Unsupported('No admissible lifted square-root or power coordinate')
    H=integrate_child(request,kernel,name)
    answer=m.substitute(H,{t:coordinate})
    return dict(theorem='method.primitive_coordinate_lift',chart='lifted_scales',coordinate=coordinate,inverse=X,
                jacobian=jac,kernel=kernel,image=image,argument=[
        'The nonnegative square-root coordinate covers the original half-line and its inverse has Jacobian 2t.',
        'Replay the primitive in the lifted coordinate and return via the chain rule.',
        'The original field is continuous at the stationary endpoint, which supplies the one-sided derivative.',
    ]),family(f,answer,region=dict(image=image,inverse=X))


ELEMENTARY_CHARTS=('phase_difference','trig_linear','trig_symmetry','trig_diagonal','trig_tangent',
                   'exponential_poles','lifted_scales','indexed_logarithm','regular_piecewise','algebraic_lift')


def elementary_chart_options(task):
    text=task.get('integrand','');method=task.get('method_requirement','table_and_rules')
    if not isinstance(text,str):return ()
    if method=='trigonometric_difference_identities':return ('phase_difference',)
    if method=='logarithmic_trigonometric_denominator':return ('trig_linear',)
    if method=='quadratic_canonical_form' and '/' in text and any(s in text for s in ('sin(','cos(','tan(')):
        return ('trig_linear','trig_tangent')
    if method=='appropriate_integrand_transformation' and text.count('sqrt(')>=2:return ('algebraic_lift',)
    if method!='table_and_rules':return ()
    options=[]
    if task.get('kind')=='integrate' and ('abs(' in text or text.startswith('max(')):
        options.append('regular_piecewise')
    if 'sqrt(' in text or 'cbrt(' in text or 'ln(' in text and '^' in text:
        options.append('algebraic_lift')
    if '/' in text and any(s in text for s in ('sin(','cos(','tan(')):
        options.extend(('trig_linear','trig_symmetry','trig_tangent','trig_diagonal'))
    if 'exp(' in text:options.append('exponential_poles')
    if 'sqrt(' in text or 'ln(' in text and '^' in text:options.append('lifted_scales')
    if 'ln(' in text and any(s.endswith(' is a natural number') for s in task.get('stated_conditions',[]) if isinstance(s,str)):
        options.insert(0,'indexed_logarithm')
    return tuple(options)


def preferred_elementary_charts(task):
    options=elementary_chart_options(task)
    if task.get('method_requirement') in ('trigonometric_difference_identities','logarithmic_trigonometric_denominator'):
        return options
    if 'regular_piecewise' in options and ('/' not in task['integrand'] and 'ln(' not in task['integrand']):
        return ('regular_piecewise',)
    if 'indexed_logarithm' in options:return ('indexed_logarithm',)
    v=task.get('variable','x');text=task.get('integrand','')
    if options and ('/' in text and any(z+'('+v+')' in text for z in ('sin','cos','tan','exp'))
                    or 'sqrt('+v+')' in text and any(z in text for z in ('sin(','cos(','exp('))
                    or '^'+v in text and 'ln(' in text):
        return options
    return ('algebraic_lift',) if 'algebraic_lift' in options else ()


def elementary_primitive_transition(task,request,chart):
    if chart=='regular_piecewise':return piecewise_primitive(task,request)
    if chart=='algebraic_lift':
        try:return algebraic_lift_primitive(task,request)
        except (NotRational,Undefined) as exc:raise Unsupported('An exact polynomial kernel was not identified') from exc
    if chart=='phase_difference':return difference_phase(task)
    if chart=='trig_linear':return trig_linear_primitive(task)
    if chart=='trig_symmetry':return trig_symmetry(task,request)
    if chart=='trig_diagonal':return diagonal_trig_primitive(task,request)
    if chart=='trig_tangent':return tangent_quadratic_primitive(task)
    if chart=='exponential_poles':return exponential_primitive(task)
    if chart=='lifted_scales':return lifted_scales(task,request)
    if chart=='indexed_logarithm':return indexed_logarithmic_primitive(task)
    raise Unsupported('Unrecognized primitive transition')


def nested_radical_lift(raw,x):
    if raw[0]!='div' or raw[2][0]!='sqrt':
        raise Unsupported('One reciprocal nested square root is required')
    v=x[1];total=raw[2][1]
    roots={e for e in learned_nodes(total) if isinstance(e,tuple) and e[0]=='sqrt'}
    if len(roots)!=1:raise Unsupported('A single inner square root is required')
    inner,=roots
    if domain_conditions(raw[1]) or domain_conditions(inner[1]):
        raise Unsupported('The nested radical has an extra source restriction')
    P=m.add(total,m.neg(inner))
    if m.contains(P,inner) or domain_conditions(P):
        raise Unsupported('The polynomial part of the outer radicand must be explicit')
    p,d=rf(P,v)
    if len(d)!=1 or not d[0] or len(p)<2:raise Unsupported('A nonconstant polynomial generator is required')
    scale=m.num(m.div(inner[1],m.power(P,3)))
    derivative=polynomial_expression(tuple(j*c/d[0] for j,c in enumerate(p) if j),v)
    ratio=m.num(m.div(raw[1],derivative))
    if scale is None or scale<=0 or ratio is None:
        raise Unsupported('The inner cubic and exact polynomial differential were not recovered')
    rate=m.simplify(('sqrt',q(scale)))
    shifted=('sqrt',m.add(ONE,m.mul(rate,('sqrt',P))))
    answer=m.mul(m.div(q(4*ratio),rate),shifted)
    return dict(theorem='method.algebraic_primitive_coordinates',chart='algebraic_lift',
                coordinate=('sqrt',P),inner_scale=q(scale),differential_ratio=q(ratio),argument=[
        'Куб под внутренним корнем требует неотрицательного полинома. На его нулях исходный внешний делитель обращается в ноль.',
        'При положительном полиноме выносим его корень и заменяем им переменную. Числитель пропорционален точной производной полинома.',
        'В новой переменной остаётся обратный квадратный корень аффинного выражения, который интегрируем непосредственно.',
    ]),family(raw,answer)


def algebraic_lift_primitive(task,request):
    """Propose a simpler differential from a reciprocal or powered generator."""
    x,raw,ctx,method=input_data(task,{'table_and_rules','appropriate_integrand_transformation'})
    if task.get('stated_conditions'):raise Unsupported('The algebraic coordinate has an additional domain restriction')
    if method=='appropriate_integrand_transformation':
        return nested_radical_lift(raw,x)
    if task['integrand'].count('sqrt(')>=2:
        try:return nested_radical_lift(raw,x)
        except (Unsupported,NotRational,Undefined):pass
    v=x[1];name=kernel_symbol(task);u=('v',name)
    def sqrt(e):return 'sqrt',e
    def denote(expr,F,steps,**data):
        return dict(theorem='method.algebraic_primitive_coordinates',chart='algebraic_lift',coordinate=expr,
                    argument=steps,**data),family(raw,F)
    if raw[0]=='div' and raw[1][0]=='ln':
        log=raw[1][1]
        if log[0]=='mul' and all(p[0]=='rpow' and p[1]==p[2] for p in log[1:]):
            A,B=(p[1] for p in log[1:])
            k,c=affine(A,v);h,d=affine(B,v)
            if (m.num(k) not in (None,0) and k==h and all(m.constant_defined(z,ctx) for z in (c,d))
                    and m.simplify(m.add(raw[2],m.neg(m.mul(A,B))))==ZERO and not domain_conditions(raw[2])):
                answer=m.div(m.mul(('ln',A),('ln',B)),k)
                return denote((A,B),answer,[
                    'Both original variable real powers require their own positive affine bases.',
                    'On this domain expand the logarithm into A ln A+B ln B and divide by AB.',
                    'The product rule for ln A ln B gives the original kernel after division by the common nonzero rate.',
                ],rate=k)
    if ctx['parameters']:raise Unsupported('The algebraic coordinate needs fixed coefficients')
    if raw[0]=='sqrt' and raw[1][0]=='tanh':
        phase=raw[1][1];k,c=affine(phase,v)
        if m.num(k) in (None,0) or not m.constant_defined(c,ctx) or domain_conditions(phase):
            raise Unsupported('The affine hyperbolic phase requires a fixed nonzero rate')
        kernel=m.div(m.mul(m.div(q(2),k),m.power(u,2)),m.add(ONE,m.neg(m.power(u,4))))
        H=integrate_child(request,kernel,name)
        return denote(raw,m.substitute(H,{u:raw}),[
            'The original real domain is the nonnegative half of the affine phase. The coordinate t=√tanh(phase) takes [0,1).',
            'The inverse is artanh(t²) in the phase. Multiply t by its Jacobian 2t/[k(1−t⁴)].',
            'Compose the rational primitive with t. Continuity of the source field gives the inward derivative at t=0.',
        ],kernel=kernel)
    if raw[0]=='sqrt' and raw[1][0]=='div' and raw[1][1]==x:
        D=raw[1][2];t=m.mul(x,sqrt(x))
        coeff=univariate_coefficients(m.rational_form(m.substitute(D,{('mul',x,sqrt(x)):u,t:u}))[0],u)
        expected=(m.add(q(coeff[0]),m.mul(q(coeff[1]),t)) if coeff and len(coeff)==2 and coeff[0]>0 else None)
        if (expected is not None and m.simplify(m.add(D,m.neg(expected)))==ZERO
                and all(g==('nonnegative',x) or known_guard(g,ctx) for g in domain_conditions(D))):
            return denote(t,m.mul(q(4/(3*coeff[1])),sqrt(D)),[
                'Let t=x√x, which is increasing on x≥0. The source is √x/√(A+Bt) wherever defined.',
                'The original quotient enforces A+Bt>0 for x>0. At x=0 this is also true because A>0.',
                'Use dt=(3/2)√x dx and integrate the reciprocal affine square root. The one-sided derivative at zero follows by continuity.',
            ],positive_affine_radicand=expected)
    factors=raw[1:] if raw[0]=='mul' else (ONE,raw)
    for W,R in (factors,factors[::-1]):
        if R[0]!='sqrt' or R[1][0]!='div' or R[1][1]!=x or domain_conditions(W):continue
        D=R[1][2]
        try:b,a=affine(D,v)
        except Unsupported:continue
        if (m.num(a) is not None and m.num(a)>0 and m.num(b) is not None and m.num(b)<0
                and not domain_conditions(D)):
            S=m.add(ONE,m.mul(m.neg(b),m.power(u,2)));inverse=m.div(m.mul(a,m.power(u,2)),S)
            jac=m.div(m.mul(m.mul(q(2),a),u),m.power(S,2))
            kernel=m.mul(m.mul(u,m.substitute(W,{x:inverse})),jac)
            H=integrate_child(request,kernel,name)
            return denote(R,m.substitute(H,{u:R}),[
                'The affine denominator and source square root restrict x to 0≤x<−a/b for a>0 and b<0.',
                'The nonnegative coordinate t=√(x/(a+b x)) covers [0,∞). Solve x=a t²/(1−b t²) and differentiate this inverse.',
                'The checked rational kernel is t times the original weight at the inverse times its Jacobian. Match the inward derivative at x=0 by continuity.',
            ],inverse=inverse,jacobian=jac,kernel=kernel)
    if raw[0]=='div' and m.num(raw[1]) is not None and raw[2][0]=='cbrt':
        W=raw[2][1];p,d=rf(W,v)
        if len(p)==4 and len(d)==1 and p[0]==p[1]==0 and p[2] and not domain_conditions(W):
            a,b=p[2]/d[0],p[3]/d[0]
            t=('cbrt',m.add(m.div(q(a),x),q(b)))
            kernel=m.div(m.mul(q(-3*m.num(raw[1])),u),m.add(m.power(u,3),q(-b)))
            H=integrate_child(request,kernel,name)
            return denote(t,m.substitute(H,{u:t}),[
                'The radicand is x³(a/x+b). The real cube root is x t for all signs of both factors.',
                'The source excludes x=0 and t=0. Its inverse x=a/(t³−b) applies on every image component without adding points to the original domain.',
                'Multiply the reciprocal cube root by the Jacobian to get a rational kernel; then compose the verified primitive.',
            ],kernel=kernel)
    if raw[0]=='div' and m.num(raw[1]) is not None and raw[2][0]=='mul' and x in raw[2][1:]:
        root=raw[2][2] if raw[2][1]==x else raw[2][1]
        if root[0]=='sqrt':
            p,d=rf(root[1],v);indices=[j for j,z in enumerate(p) if j and z]
            if (len(d)==1 and len(indices)==2 and indices[1]==2*indices[0]
                    and p[0] and not domain_conditions(root[1])):
                n=indices[0];A,B,C=(p[j]/d[0] for j in (0,n,2*n))
                t=m.power(x,-n);Q=m.add(m.add(m.mul(q(A),m.power(u,2)),m.mul(q(B),u)),q(C))
                delta=B*B-4*A*C
                if A>0 and delta:
                    z=m.add(m.mul(m.mul(q(2),sqrt(q(A))),sqrt(Q)),m.add(m.mul(q(2*A),u),q(B)))
                    H=m.div(lnabs(z),sqrt(q(A)))
                elif A<0 and delta>0:
                    z=m.div(m.add(m.mul(q(2*A),u),q(B)),sqrt(q(delta)))
                    H=m.neg(m.div(('asin',z),sqrt(q(-A))))
                else:raise Unsupported('The reciprocal chart needs a nondegenerate quadratic branch')
                sign=ONE if n%2==0 else m.div(x,('abs',x))
                answer=m.mul(m.mul(q(-m.num(raw[1])/n),sign),m.substitute(H,{u:t}))
                return denote(t,answer,[
                    'The original divisor requires x≠0 and a strictly positive radicand.',
                    'Put t=x^(−n). The original square root equals √Q(t)/|t|. Since dx/x=−dt/(n t), retain the sign of t on each original component.',
                    'Complete the square in Q and integrate its positive reciprocal root. The logarithmic or inverse-sine formula is valid everywhere Q>0.',
                ],quadratic=Q,reciprocal_power=n)
    raise Unsupported('No guarded compound root or log-product coordinate was identified')


def primitive_predicates(text,v):
    fields=re.split(r'(<=|>=|<|>)',text.replace(' ',''))
    if len(fields) not in (3,5):raise Unsupported('Polynomial interval comparisons are required')
    values=[m.parse(s,v) for s in fields[::2]]
    result=[]
    for A,sign,B in zip(values,fields[1::2],values[1:]):
        if sign.startswith('<'):A,B=B,A
        E=m.add(A,m.neg(B))
        result.append((E,'=' in sign))
    return result


def piecewise_primitive(task,request):
    """Separate every branch switch and glue primitives on the original connected domain."""
    from functools import cmp_to_key
    from graphs import rational_roots
    from plane_domains import yterm
    from ray_proofs import compare_scalar
    v=task.get('variable','x');x=('v',v);ctx=m.context(dict(variable=v))
    t=task.get('integrand','')
    fields={'id','kind','source','integrand','variable','pieces','requested_output'}
    if task['kind']=='piecewise_integral':
        if set(task)-fields or task.get('requested_output')!=['primitive_on_all_real_numbers'] or 'integrand' in task:
            raise Unsupported('The finite branch field must be specified on the entire real line')
        rows=[(primitive_predicates(p['if'],v),m.parse(p['value'],v)) for p in task['pieces']
              if set(p)=={'if','value'}]
        if len(rows)!=len(task['pieces']):raise Unsupported('Incomplete original branch')
    else:
        if task.get('parameters') or task.get('stated_conditions') or task.get('method_requirement','table_and_rules')!='table_and_rules':
            raise Unsupported('A finite global piecewise field is required')
        if re.fullmatch(r'max\(([^,]+),([^,]+)\)',t):
            a,b=re.fullmatch(r'max\(([^,]+),([^,]+)\)',t).groups()
            _,A,_,_=input_data(dict(task,integrand=a),{'table_and_rules'})
            B=m.parse(b,v)
            rows=[([(m.add(A,m.neg(B)),True)],A),([(m.add(B,m.neg(A)),False)],B)]
        else:
            _,raw,_,_=input_data(task,{'table_and_rules'})
            rows=[([],raw)]
    if any(not known_guard(g,ctx) for conditions,raw in rows for E in [raw,*(s for s,_ in conditions)]
           for g in domain_conditions(E)):
        raise Unsupported('The original expression may have a pole or nonreal branch')
    atoms=list(dict.fromkeys(z for conditions,raw in rows for e in [raw,*(s for s,_ in conditions)]
                             for z in learned_nodes(e) if isinstance(z,tuple) and z[0]=='abs' and m.variable_in(z,v)))
    if len(atoms)>5:raise Unsupported('Too many interacting absolute-value branches')
    if not atoms and all(not conditions for conditions,_ in rows):
        raise Unsupported('The original expression has no finite piecewise structure')
    def roots(E):
        try:p,d=rf(E,v)
        except (NotRational,Undefined) as exc:raise Unsupported('A polynomial switch needs complete root isolation') from exc
        if len(d)!=1:raise Unsupported('A pole in an original branch predicate')
        return [yterm(y) for y in rational_roots(p)] if len(p)>1 else []
    if any(any(m.contains(a[1],b) for b in atoms) for a in atoms):
        raise Unsupported('Nested absolute values require another branch decomposition')
    cuts=[z for a in atoms for z in roots(a[1])]
    from itertools import product
    for signs in product((-1,1),repeat=len(atoms)):
        bind={a:m.mul(q(sign),a[1]) for a,sign in zip(atoms,signs,strict=True)}
        cuts.extend(z for conditions,_ in rows for E,_ in conditions for z in roots(m.substitute(E,bind)))
    ordered=[]
    for z in sorted(cuts,key=cmp_to_key(compare_scalar)):
        if not ordered or compare_scalar(z,ordered[-1])!=0:ordered.append(z)
    def at(E,p):
        return m.simplify(m.substitute(E,{x:p}))
    def branch(sample):
        signs={a:a[1] if compare_scalar(at(a[1],sample),ZERO)>=0 else m.neg(a[1]) for a in atoms}
        chosen=[]
        for conditions,raw in rows:
            tests=[compare_scalar(at(m.substitute(E,signs),sample),ZERO) for E,_ in conditions]
            if all(z>0 or z==0 and closed for z,(_,closed) in zip(tests,conditions,strict=True)):
                chosen.append(m.simplify(m.substitute(raw,signs)))
        if len(chosen)!=1:raise Unsupported('Branch predicates do not cover exactly once')
        return chosen[0]
    cuts=[None,*ordered,None];pieces=[];primitives={}
    for L,R in zip(cuts,cuts[1:]):
        sample=(m.div(m.add(L,R),q(2)) if L is not None and R is not None else
                m.add(L,ONE) if L is not None else m.add(R,q(-1)) if R is not None else ZERO)
        field=branch(sample)
        if field not in primitives:primitives[field]=integrate_child(request,field,v)
        primitive=primitives[field]
        if L is not None:
            past=pieces[-1]
            if not all(compare_scalar(at(e,L),at(branch(L),L))==0 for e in (past['field'],field)):
                raise Unsupported('The source function is discontinuous at an interval join')
            endpoint=at(primitive,L);left=at(past['primitive'],L)
            if not all(m.constant_defined(z,ctx) for z in (endpoint,left)):
                raise Unsupported('The glued primitives must have finite endpoint values')
            primitive=m.add(primitive,m.add(left,m.neg(endpoint)))
        pieces.append(dict(bounds=(L,R),field=field,primitive=primitive))
    answer=('piecewise_primitive',tuple((p['bounds'],p['primitive']) for p in pieces))
    plan=dict(theorem='method.piecewise_primitives_on_source',chart='regular_piecewise',pieces=pieces,argument=[
        'Isolate every real root of every switching polynomial. The source conditions determine exactly one smooth branch in each cell.',
        'Use a checked primitive for each branch. Align the integration constants where the branches meet.',
        'Both one-sided derivatives equal the original field at the join because its two branch values agree there.',
    ])
    return plan,dict(representative=answer,original_domain='all real numbers',family='F+C',constant_policy='one real constant')


def trig_primitive_representation(task):
    from verify import same_value
    if set(task)-{'kind','id','source','variable','integrand','claimed_primitive','requested_output'} or task.get('requested_output')!=['proof_of_representation']:
        raise Unsupported('The printed representation and all requests must be bound')
    headings=('Доказать формулу с постоянными','Доказать представление')
    if task.get('source',{}).get('literal_requirement') and not task['source']['literal_requirement'].startswith(headings):
        raise Unsupported('The full statement must request a representation with constant coefficients')
    v=task.get('variable','x');x=('v',v)
    identifier=r'[A-Za-z_]\w*'
    kernel,claim=(task[k] for k in ('integrand','claimed_primitive'))
    names=lambda t:set(re.findall(identifier,t))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e',v,'integral'}
    source_names=names(kernel);all_names=sorted(source_names|names(claim))
    raw=m.parse(kernel,v,all_names)
    if raw[0]!='div' or domain_conditions(raw[1]) or domain_conditions(raw[2]):
        raise Unsupported('One trigonometric quotient without extra holes is required')
    top,den=raw[1:]
    D=trig_polynomial(den,x);P=trig_polynomial(top,x)
    if set(D)-{(1,0),(0,1),(0,0)} or not set(D)&{(1,0),(0,1)}:
        raise Unsupported('The denominator is not a linear trigonometric polynomial')
    mode,A,B,R=trig_quotient_decomposition(P,D)
    remainder=R
    if claim.count('integral(')>1:
        raise Unsupported('Only one residual primitive is permitted')
    compact=claim
    if 'integral(' in claim:
        start=claim.index('integral(')+len('integral(')
        depth=1;comma=None
        for j,char in enumerate(claim[start:],start):
            if char=='(':depth+=1
            if char==',' and depth==1:
                if comma is not None:raise Unsupported('The residual primitive must have one coordinate binder')
                comma=j
            if char==')':
                depth-=1
                if not depth:break
        if depth or comma is None or claim[comma+1:j].strip()!=v:
            raise Unsupported('The residual primitive must use the original coordinate')
        compact=claim[:comma]+claim[j:]
    ast=m.parse(compact,v,all_names,['integral'])
    def summands(e):
        if e[0]=='add':
            yield from summands(e[1])
            yield from summands(e[2])
        else:yield e
    sin,cos=('sin',x),('cos',x)
    bases={x:A,lnabs(den):B} if mode=='linear' else {sin:B,cos:m.neg(A)}
    got={}
    for e in summands(ast):
        if e[0]=='s' and e[1] not in source_names:
            c,b=e,ONE
        elif e[0]=='mul':
            c,b=e[1:]
            if c[0]!='s' or c[1] in source_names:c,b=b,c
        else:raise Unsupported('Each proposed basis term must have a free constant coefficient')
        if c[0]!='s' or c[1] in source_names or c[1] in got:
            raise Unsupported('The proposed coefficients must be independent of the source and each other')
        if b==ONE:value=ZERO
        elif b[0]=='integral':
            if claim==compact or b[1][0]!='div' or b[1][1]!=ONE or domain_conditions(b[1][2]) or not same_value(b[1][2],den):
                raise Unsupported('The retained primitive must have the reciprocal original kernel and the same binder')
            value=R;R=ZERO
        elif b[0]=='ln' and b[1][0]=='abs' and not domain_conditions(b[1][1]) and same_value(b[1][1],den) and lnabs(den) in bases:
            value=bases.pop(lnabs(den))
        elif b in bases:value=bases.pop(b)
        else:raise Unsupported('One asserted basis term is not justified')
        got[c[1]]=value
    if R!=ZERO or any(val!=ZERO for val in bases.values()):
        raise Unsupported('The displayed basis omits a nonzero component')
    a,b,c=(D.get(i,ZERO) for i in ((1,0),(0,1),(0,0)))
    amplitude=m.add(m.power(a,2),m.power(b,2))
    J=m.add(m.mul(a,cos),m.neg(m.mul(b,sin)))
    differentiated=(m.add(m.mul(A,den),m.mul(B,J)) if mode=='linear'
                    else m.mul(m.add(m.mul(A,sin),m.mul(B,cos)),den))
    if not same_value(top,m.add(differentiated,remainder)):
        raise Unsupported('Differentiating the claimed decomposition did not recover the numerator')
    result=dict(representation_coefficients=got,valid_when=source(amplitude)+'>0',
                source_domain=domain_conditions(raw),constant_policy='one arbitrary additive constant on each source component')
    if c!=ZERO:
        result['zero_amplitude_case']='When a=b=0 and D is nonzero, the specified basis has constant derivative. It works precisely when the numerator is constant.'
        if {a,b,c}<= {('s',name) for name in source_names} and len({a,b,c})==3:
            aa,bb,cc=[e[1] for e in (a,b,c)]
            for coefficient in (P.get((1,0),ZERO),P.get((0,1),ZERO)):
                if coefficient[0]=='s' and coefficient not in (a,b,c):
                    vals={name:ZERO for name in source_names}
                    vals[cc]=vals[coefficient[1]]=ONE
                    substitutions={('s',name):value for name,value in vals.items()}
                    den_at=m.simplify(m.substitute(den,substitutions))
                    num_at=m.simplify(m.substitute(top,substitutions))
                    if den_at==ONE and m.variable_in(num_at,v):
                        result.update(printed_claim_holds=False,counterexample_parameters=vals,
                                      counterexample_kernel=num_at,counterexample=dict(parameters=vals,
                                          original_kernel=num_at,claimed_derivative_class='constant'))
                        break
    else:
        result['zero_amplitude_case']='The homogeneous denominator vanishes everywhere.'
    return dict(theorem='method.trig_linear_rational',amplitude_squared=amplitude,numerator=top,
                reconstructed_numerator=m.add(differentiated,remainder),argument=[
        'Разложить числитель в базисе, который получается дифференцированием заявленной формы.',
        'Разрешить коэффициенты из двух независимых синусоидальных направлений. Их квадрат амплитуды должен быть положительным.',
        'Проверить восстановление числителя и сохранить все компоненты, на которых исходный знаменатель не равен нулю.',
    ]),result


def rational_coordinate_theorem(task):
    from cartesian_fields import vector_source
    kind=task['kind'];heading=task.get('source',{}).get('method_heading')
    name=r'([A-Za-z_]\w*)'
    def proof(steps,**facts):
        return dict(theorem='method.primitive_coordinate_lift',argument=steps,**facts)
    if kind=='prove_integral_elementary':
        vector_source(task,{'source_statement','requested_output'},())
        text=task['source_statement']
        hit=re.fullmatch(r'Доказать, что если '+name+r' — рациональная функция и числа ([A-Za-z])1,\.\.\.,\2n соизмеримы, то интеграл \1\(exp\((?:\2)1\*'+name+r'\),\.\.\.,exp\((?:\2)n\*\3\)\) d\3 выражается в виде элементарной функции\.',text)
        if not hit or task['requested_output']!=['complete_proof']:
            raise Unsupported('A rational function of a commensurate family of exponential rates is required')
        R,a,x=hit.groups()
        return proof([
            'Из соизмеримости берём один ненулевой общий масштаб d и целые показатели m_j, такие что a_j=d m_j.',
            'Подстановка t=e^(d x) покрывает положительную полуось, а каждое исходное экспоненциальное выражение становится t^(m_j). Дифференциал добавляет рациональный множитель 1/(d t).',
            'Интегрируем полученную рациональную функцию на каждой исходной компоненте. Если все скорости нулевые, исходное ядро постоянно всюду, где определено.',
        ],parameter_family=a,source_coordinate=x,rational_function=R),dict(elementary=True,keeps_original_exclusions=True)

    if kind=='real_indexed_root_primitive':
        vector_source(task,{'integrand','variable','assumptions','requested_output'},(),('method_heading',))
        x=task['variable']
        hit=re.fullmatch(r'1/nth_root\((.+),'+name+r'\)',task['integrand'])
        if (not hit or task.get('assumptions')!=[hit[2]+' positive integer'] or
                task['requested_output']!=['primitive family on real branches'] or
                heading not in (None,'Reduce the algebraic integrand to rational form.')):
            raise Unsupported('The original root order and real branch obligation must be present')
        n=hit[2];names=sorted(set(re.findall(r'[A-Za-z_]\w*',hit[1]))-{x})
        raw=m.parse(hit[1],x,names)
        if raw[0]!='mul' or any(z[0]!='rpow' for z in raw[1:]):
            raise Unsupported('Need two original powers of affine factors with the stated integer order')
        shifts={}
        for _,factor,exponent in raw[1:]:
            slope,offset=affine(factor,x);symbol=m.neg(offset)
            extra=m.num(m.add(exponent,m.neg(('s',n))))
            if slope!=ONE or symbol[0]!='s' or symbol[1]==n or extra not in (1,-1) or extra in shifts or domain_conditions(factor):
                raise Unsupported('The two exponents must differ from the index by +1 and -1')
            shifts[extra]=symbol[1]
        a,b=shifts[1],shifts[-1]
        F=f'-{n}/(({a}-{b})*t)'
        statement=proof([
            'При различающихся сдвигах выделяем из радиканда n-ю степень произведения двух линейных множителей и отношение этих множителей.',
            'Для нечётного индекса используем вещественный знаковый корень, для чётного сохраняем только допустимую положительную ветвь произведения. В обоих случаях новая координата t есть n-й корень отношения.',
            'Логарифмическая производная отношения равна (a−b)/((x−a)(x−b)). Поэтому исходный дифференциал равен n/(a−b)·dt/t².',
            'При равных сдвигах или индексе один исходный корень проверяется непосредственно. Сохраняем исходные исключения и произвольную постоянную на каждой связной компоненте.',
        ],original_root_index=n,relative_coordinate=f'nth_root(({x}-{a})/({x}-{b}),{n})',
             differential=f'{n}/({a}-{b})*dt/t^2')
        return statement,dict(cases=[dict(condition=f'{n}=1 or {a}={b}',representative=f'-1/({x}-{a})'),
                                     dict(condition=f'{n}>1 and {a}!={b}',representative=F)],
                              constants='one per original real component')

    vector_source(task,{'integrand','condition','assumptions','requested_output'},(),('method_heading',))
    raw=task['integrand']
    if task.get('requested_output') not in (None,['complete_proof']):raise Unsupported('There is another source conclusion')
    binomial=re.fullmatch(name+r'\('+name+r',\(\2-'+name+r'\)\^\('+name+r'/'+name+r'\)\*\(\2-'+name+r'\)\^\('+name+r'/\5\)\)',raw)
    if binomial:
        R,x,a,p,n,b,j=binomial.groups()
        condition=re.fullmatch(re.escape(p+'+'+j)+r'='+name+r'\*'+re.escape(n)+r', integer '+re.escape(','.join((p,j)))+r',\1,'+re.escape(n)+r' and '+re.escape(n)+r'!=0',task.get('condition',''))
        if not condition or task.get('assumptions') or heading not in (None,'Prove elementarity for rational R and integer p,q,n with p+q=k*n.'):
            raise Unsupported('The exponent sum and integer assumptions do not match')
        k=condition[1]
        return proof([
            'Нормируем знак общего знаменателя показателей. На каждом допустимом листе фиксируем знаки двух линейных множителей.',
            'Вводим положительный корень модуля их отношения. Условие суммы показателей оставляет целую степень второго множителя и целую степень новой координаты. Постоянный знак листа сохраняется.',
            'Уравнение t^|n|=±(x−a)/(x−b) решается дробно-линейно относительно x, поэтому якобиан и весь исходный рациональный подынтегральный множитель рациональны. При совпадении сдвигов рациональность следует непосредственно из той же суммы показателей.',
        ],exponent_sum=f'{p}+{j}={k}*{n}',rational_family=R,forward_scope=f'fixed real branches of {x}-{a} and {x}-{b}'),dict(elementary=True,local_on_original_components=True)

    two_roots=re.fullmatch(name+r'\('+name+r',sqrt\((.+)\),sqrt\((.+)\)\)',raw)
    if not two_roots or task.get('condition') or heading not in (
            None,'Prove reduction of the two-affine-square-root integral to an integral of a rational function.'):
        raise Unsupported('Both affine square roots and the rational outer function must be explicit')
    R,x,A,C=two_roots.groups()
    if task.get('assumptions')!=[R+' rational']:
        raise Unsupported('The stated rational function must be the actual outer function')
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',A+' '+C))-{x})
    coeff=[]
    for text in (A,C):
        raw_axis=m.parse(text,x,names)
        pair=affine(raw_axis,x)
        if domain_conditions(raw_axis) or any(z[0]!='s' for z in pair):
            raise Unsupported('The two affine forms must use real declared coefficients')
        coeff.extend(z[1] for z in pair)
    a,b,c,d=coeff
    return proof([
        'Обозначаем корни U,V и исключаем x, получая конику cU²−aV²=cb−ad.',
        'На любом непустом невырожденном листе берём действительную точку и проводим через неё прямую V−V₀=t(U−U₀). После сокращения известного пересечения вторые координаты рациональны по t.',
        'Восстанавливаем x и его производную, сохраняем оба неотрицательных радикала и все исходные полюсы. Пропуск отдельной точки карты закрывается другой прямой или проверкой непрерывности.',
        'При нулевом наклоне одного исходного корня он постоянен. При вырожденной конике её прямолинейные ветви позволяют непосредственно взять оставшийся корень.',
    ],conic=f'{c}*U^2-{a}*V^2={c}*{b}-{a}*{d}',source_coordinate=x,
         projection='secant through an admitted real point'),dict(rational_reduction=True,real_branches_preserved=True)




def binomial_elementarity(task):
    """Apply Chebyshev's criterion, keeping the constant phase as a separate case."""
    name=task.get('variable','x');x=('v',name);params=task.get('parameters',[])
    if (set(task)-{'id','kind','integrand','variable','parameters','stated_conditions','source','requested_output'}
            or len(params)!=1 or not isinstance(params[0],str) or params[0]==name
            or task.get('stated_conditions')!=[params[0]+' rational']
            or task.get('requested_output',[]) not in ([],['elementary_parameter_set'])
            or task.get('source',{}).get('method_heading') not in (None,'Find all rational '+params[0]+' making the given integral elementary.')):
        raise Unsupported('The rational exponent and its elementarity goal must be bound')
    n=('s',params[0]);raw=m.parse(task['integrand'],name,params)
    roots=[]
    def collect(e):
        return collect(e[1])+collect(e[2]) if e[0]=='mul' else [e]
    def power(e):
        if e==x:return ONE
        if e[0] in ('pow','rpow') and e[1]==x:
            return q(e[2]) if e[0]=='pow' else m.simplify(e[2])
        raise Unsupported('A pure coordinate power was expected')
    for factor in collect(raw):
        if factor[0]=='sqrt':roots.append((factor,factor[1],Fraction(1,2)))
        elif factor[0] in ('pow','rpow') and factor[1][0]=='add':
            p=Fraction(factor[2]) if factor[0]=='pow' else m.num(m.simplify(factor[2]))
            if p is not None:roots.append((factor,factor[1],p))
    if len(roots)!=1:raise Unsupported('There must be one rational power of a binomial')
    factor,base,p=roots[0];weight=Fraction(0);scale=Fraction(1)
    other=list(collect(raw));other.remove(factor)
    for term in other:
        v=m.num(term)
        if v is not None:scale*=v
        else:
            mon=m.num(power(term))
            if mon is None:raise Unsupported('The outer exponent must be a fixed rational number')
            weight+=mon
    if base[0]!='add' or not scale:
        raise Unsupported('Both binomial terms and the outer coefficient must be nondegenerate')
    constant,monomial=base[1:]
    if m.num(constant) is None:constant,monomial=monomial,constant
    A=m.num(constant);B=Fraction(1);inner=[]
    for term in collect(monomial):
        v=m.num(term)
        if v is None:inner.append(term)
        else:B*=v
    if A is None or A<=0 or B<=0 or len(inner)!=1 or power(inner[0])!=n:
        raise Unsupported('Positive fixed binomial coefficients and one symbolic rational power are required')
    r=weight+1;d=p.denominator
    result=dict(scope='on open intervals of the real rational-power domain; test necessity on x>0',
                parameter=params[0],constant_exponent=ZERO,
                admissible_nonzero='all nonzero rationals' if r==0 or d==1 else
                dict(form='numerator/k',numerator=q(r*d),k_domain='nonzero integer',modulus=d,
                     residues=sorted({0,(-p.numerator)%d})))
    return dict(theorem='method.binomial_elementarity',powers=[q(weight),n,q(p)],coefficients=[q(scale),q(A),q(B)],
                reference='https://www.numdam.org/item/JMPA_1853_1_18__87_0.pdf',
                argument=[
                    'При нулевом внутреннем показателе остаётся постоянный биномиальный множитель и степенной дифференциал.',
                    'Для ненулевого показателя применяем критерий Чебышёва: хотя бы одно из чисел p, (r+1)/m, p+(r+1)/m должно быть целым. Теорема даёт и необходимость на положительной вещественной ветви.',
                    'Если r+1=0 или p целое, ограничений больше нет. Иначе приводим обе альтернативы к целому ненулевому знаменателю с двумя допустимыми классами остатков.',
                    'На отрицательной вещественной ветви, если она существует, отражаем координату. Знак внутреннего коэффициента может измениться, а критерий показателей сохраняется на каждой регулярной ветви.'
                ]),result


def declared_integral_reading(task,request):
    """Only evaluate a disputed differential when the source declares a reading."""
    if (set(task)-{'kind','id','source','printed','ordinary_reading','requested_output'}
            or task.get('requested_output')!=['primitive_family_under_declared_interpretation']):
        raise Unsupported('An explicit interpretation is needed for the ambiguous integral')
    reading=re.fullmatch(r'integrate (.+) with respect to ([A-Za-z][A-Za-z0-9_]*)',str(task.get('ordinary_reading','')))
    if not reading:raise Unsupported('The declared interpretation must identify a single differential')
    integrand,name=reading.groups();d=re.escape('d'+name)
    form=re.fullmatch(fr'∫ \((.+)\) {d}',str(task.get('printed','')))
    if form is None or len(re.findall(fr'\b{d}\b',form[1]))!=1:
        raise Unsupported('The two printed occurrences of the same differential are not bound')
    body=re.sub(fr'\s+{d}\b','',form[1]).replace(' ','')
    body=re.sub(r'(sin|cos|tan|cot)([²³])'+re.escape(name),
                lambda found:found[1]+'('+name+')^'+{'²':'2','³':'3'}[found[2]],body)
    raw=m.parse(integrand,name);observed=m.parse(body,name)
    if raw!=observed:
        raise Unsupported('Removing the repeated differential yields a different integrand or domain')
    child=dict(kind='integrate',integrand=integrand,variable=name,
               requested_output=['primitive_family','natural_domain_components','constant_per_component'])
    proof=request('primitive_under_declared_reading',child)
    if proof.get('status')!='SOLVED':raise Unsupported('The stated reading has no fully verified primitive')
    return dict(theorem='method.declared_differential_interpretation',printed=task['printed'],reading=child,argument=[
        'Фиксируем обе напечатанные записи дифференциала. Дальнейший вывод относится к указанному однозначному прочтению.',
        'После удаления одного повторного дифференциала проверяем точное совпадение выражений и применяем найденную первообразную к исходным компонентам.'
    ]),dict(interpreted_primitive=proof['value'],scope='under the declared interpretation')


def affine_primitive_claim(task,recognition=False):
    if (set(task)-{'schema','kind','id','source','variables','parameters','function_symbols','premises','claim','requested_output','transcription'}
            or task.get('transcription') not in (None,'Source proof statement and its given target only; no completed argument or exercise-specific route.')
            or task.get('requested_output')!=['proof','conditions_and_scope']):
        raise Unsupported('A source affine primitive and its scope are required')
    variables,parameters,functions=(task.get(k,[]) for k in ('variables','parameters','function_symbols'))
    if len(variables)!=1 or len(parameters)!=2 or len(functions)!=2:
        raise Unsupported('One coordinate, two affine constants and two functions are required')
    x=variables[0].get('symbol');a,b=(v.get('symbol') for v in parameters);f,F=functions
    names=(x,a,b,f,F)
    if (not all(isinstance(v,str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',v) for v in names)
            or len(set(names))!=len(names) or variables != [dict(symbol=x,domain='real')]
            or parameters!=[dict(symbol=v,domain='real',independent_of=x) for v in (a,b)]
            or not any(set(task.get('premises',[]))==
                       {f'{F} is {article} primitive of {f}: integral {f}({x}) d{x} = {F}({x})+C',a+'!=0'}
                       for article in ('a',a))):
        raise Unsupported('The declared primitive pair or fixed nonzero slope is absent')
    primitive=f'{F}({a}*{x}+{b})/{a}'
    if re.sub(r'\s+','',str(task.get('claim','')))!=f'integral{f}({a}*{x}+{b})d{x}={primitive}+C':
        raise Unsupported('The stated formula differs from the affine primitive')
    if recognition:return True
    return dict(theorem='method.formal_primitive_transport',argument=[
        'На прообразе области F дифференцируем композицию с аффинным аргументом. По цепному правилу производная умножается на фиксированный наклон.',
        'Наклон ненулевой, поэтому после деления производная совпадает с исходной плотностью. Теорема о среднем даёт одну произвольную постоянную на компоненту.'
    ]),dict(proved=True,representative=primitive,conditions=[a+'!=0'],
            domain='preimage of the original primitive domain under the stated affine argument',
            constant='one per connected component')


def affine_primitive_claim_goal(task):
    try:return affine_primitive_claim(task,recognition=True)
    except (Unsupported,AttributeError,KeyError,TypeError):return False


def primitive_from_function(task,library,request):
    """Choose the conditions for a piecewise, inverse, or formal primitive."""
    if not library.data.get('composition_primitive_skills'):raise Unsupported('The functional primitive rules are unavailable')
    if any(k in task.get('source',{}) for k in ('explicit_imposed_method','explicit_required_method','method_requirement')):
        raise Unsupported('A different printed method is not satisfied by this certificate')
    common={'kind','id','source','requested_output','variable'}
    kind=task['kind'];v=task.get('variable','x');x=('v',v);wanted=task.get('requested_output')
    if kind in ('rational_substitution_theorem','real_indexed_root_primitive','prove_integral_elementary'):
        return rational_coordinate_theorem(task)
    if kind=='elementarity_criterion_for_binomial_integral':
        if not library.data.get('binomial_elementarity'):
            raise Unsupported('The binomial elementarity theorem is unavailable')
        return binomial_elementarity(task)
    if kind=='integral_source_notation':
        return declared_integral_reading(task,request)
    if kind=='prove':
        return affine_primitive_claim(task)
    if kind=='primitive_formula_proof':
        return trig_primitive_representation(task)
    if kind in ('prove_integral_representation','characterize_elementary_integrability'):
        return exponential_primitive_theorem(task)
    if kind=='piecewise_integral':
        if 'pieces' in task:return piecewise_primitive(task,request)
        if set(task)-common-{'integrand','stated_conditions'}:
            raise Unsupported('Unbound source requirement')
        text=task['integrand']
        s=re.fullmatch(r'distance\((.+),integers\)',text)
        grid=re.fullmatch(r'floor\((.*)\)\*abs\(sin\(pi\*(.*)\)\)',text)
        if s and wanted==['primitive_on_all_real_numbers'] and not task.get('stated_conditions'):
            phase=m.parse(s[1],v);factor,shift=affine(phase,v)
            if m.num(factor) in (None,0) or m.num(shift) is None:
                raise Unsupported('The integer grid must have a fixed nonzero affine coordinate')
            answer=dict(coordinate=phase,cell='n=floor(t), r=t-n',constant='one real constant',
                        representative='[n/4 + (r^2/2 if r<=1/2 else 1/4-(1-r)^2/2)]/slope',
                        slope=factor)
            steps=['The distance to the nearest integer is min(r,1−r) on each unit cell.',
                   'Each complete cell has integral 1/4, including cells to the left of zero with orientation.',
                   'Integrate the two linear halves and match the function values and derivatives at the joins.']
        elif grid and grid[1]==grid[2] and wanted==['primitive_on_stated_interval'] and task.get('stated_conditions')==[v+'>=0']:
            phase=m.parse(grid[1],v);factor,shift=affine(phase,v)
            if m.num(factor) is None or m.num(factor)<=0 or shift!=ZERO:
                raise Unsupported('The nonnegative source needs a positive grid rate and a cell boundary at zero')
            answer=dict(coordinate=phase,cell='n=floor(t), r=t-n',constant='one real constant',
                        representative='[n(n−1)+n(1−cos(πr))]/(π*slope)',slope=factor)
            steps=['On the nonnegative nth cell the original product is n sin(πr), since sin(πr) is nonnegative.',
                   'Complete cell j contributes 2j/(π slope). Sum the arithmetic progression and add the partial cell integral.',
                   'At every integer boundary the neighboring values agree and both directional derivatives vanish.']
        else:raise Unsupported('The original periodic or weighted cell field is not proved')
        return dict(theorem='method.piecewise_primitives_on_source',argument=steps),answer
    if kind=='formal_function_primitive':
        if set(task)-common-{'integrand'}:raise Unsupported('Unbound assumptions on the arbitrary function')
        name=r'[A-Za-z_]\w*';text=task['integrand'];v_re=re.escape(v)
        p=re.fullmatch(fr'(.+)\*D2\(({name}),{v_re}\)',text)
        c=re.fullmatch(fr'D\(({name})\)\((.+)\)',text)
        if p and wanted==['primitive_family_for_arbitrary_twice_differentiable_function']:
            W=m.parse(p[1],v);k,b=affine(W,v)
            if None in (m.num(k),m.num(b)):raise Unsupported('The formal multiplier must have a fixed affine expression')
            formula=f'({source(W)})*D({p[2]})({v})-({source(k)})*{p[2]}({v})'
            steps=['The derivative of the affine multiplier is the constant k.',
                   'The product rule gives W f″+k f′. Subtract the derivative of k f.']
        elif c and wanted==['primitive_family_for_arbitrary_differentiable_function']:
            W=m.parse(c[2],v);k,b=affine(W,v)
            if m.num(k) in (None,0) or m.num(b) is None:raise Unsupported('The affine source argument needs a nonzero rate')
            formula=f'{c[1]}({source(W)})/({source(k)})'
            steps=['The affine argument has a constant nonzero derivative k.',
                   'The chain rule gives k f′(W). Divide by k on the original preimage of the function domain.']
        else:raise Unsupported('A checked formal product or affine composition is required')
        return dict(theorem='method.formal_primitive_transport',argument=steps),dict(representative=formula,constant='one per original component')
    if kind=='inverse_function_primitive_theorem':
        if (set(task)-common-{'function','stated_conditions','theorem_assumptions'}
                or task['theorem_assumptions']!=['f continuous and monotone on interval','f invertible']
                or wanted!=['proof_without_differentiability_of_inverse','stated_example']):
            raise Unsupported('The original inverse and continuous monotone hypotheses must hold')
        conditions=task.get('stated_conditions',[]);text=task['function'];y=('v','y')
        def unary(op):return op,y
        if (power:=re.fullmatch(fr'{re.escape(v)}\^([A-Za-z_]\w*)',text)) and conditions==[power[1]+'>0']:
            n=('s',power[1]);p=m.div(ONE,n)
            example=dict(inverse=('rpow',y,p),representative=m.div(('rpow',y,m.add(ONE,p)),m.add(ONE,p)),domain='y>=0 on the real nonnegative branch')
        elif conditions==[] and text in (f'exp({v})',f'asin({v})',f'atanh({v})'):
            t=text.split('(',1)[0]
            if t=='exp':F=m.add(m.mul(y,unary('ln')),m.neg(y));g=unary('ln');domain='y>0'
            elif t=='asin':F=m.neg(unary('cos'));g=unary('sin');domain='-pi/2<=y<=pi/2'
            else:F=('ln',unary('cosh'));g=unary('tanh');domain='all real y'
            example=dict(inverse=g,representative=F,domain=domain)
        else:raise Unsupported('The inverse example requires a certified monotone coordinate')
        return dict(theorem='method.formal_primitive_transport',argument=[
            'Put g=f⁻¹, Q(y)=y g(y)−F(g(y)), with F′=f. Subtract Q(y) from Q(y+h).',
            'The result equals h g(y+h) minus the oriented integral of f(t)−y from g(y) to g(y+h).',
            'Monotonicity bounds the integral in absolute value by |h| |g(y+h)−g(y)|. After dividing by h its contribution tends to zero by continuity of the inverse.',
            'Thus Q′=g on the original image interval, with one-sided derivatives at included endpoints.',
        ]),dict(identity='Q(y)=y*g(y)-F(g(y))+C',example=example)
    if kind!='recover_from_composite_derivative' or set(task)-common-{'argument','derivative_value','stated_conditions','derivative_values','initial'}:
        raise Unsupported('Unsupported prescribed derivative')
    raw=m.parse(task['argument'],v);conditions=task.get('stated_conditions',[])
    if wanted==['all_functions_on_determined_argument_range'] and 'derivative_values' not in task and 'initial' not in task:
        derivative=m.parse(task['derivative_value'],v);y=('v','y')
        if raw[0]=='pow' and raw[1]==x and raw[2]>0 and conditions==[v+'>0']:
            numerator,denominator=rf(derivative,v)
            if not any(numerator) or sum(bool(c) for c in numerator)!=1 or sum(bool(c) for c in denominator)!=1:
                raise Unsupported('The image derivative does not have a single verified power')
            exponent=q(Fraction(len(numerator)-len(denominator),raw[2]));scale=q(numerator[-1]/denominator[-1])
            exponent1=m.add(ONE,exponent)
            representative=m.mul(scale,('ln',y) if exponent1==ZERO else m.div(('rpow',y,exponent1),exponent1))
            image='y>0';reason='The positive power is a bijection of the positive half-axis with the stated inverse power.'
        elif raw==m.power(('sin',x),2) and derivative==m.power(('cos',x),2) and not conditions:
            representative=m.add(y,m.mul(q(-1,2),m.power(y,2)));image='0<=y<=1'
            reason='The squared sine takes every value y∈[0,1]; 1−y equals the squared cosine at every preimage.'
        else:raise Unsupported('No full image-fiber identity for the supplied derivative')
        return dict(theorem='method.formal_primitive_transport',argument=[reason,'Integrate the resulting function of y on the original image.']),dict(representative=representative,domain=image,constant='one real constant')
    if raw!=('ln',x) or conditions or wanted!=['unique_function_with_initial_value'] or 'derivative_value' in task:
        raise Unsupported('The original logarithmic image and initial condition are required')
    rows=task['derivative_values'];initial=task['initial']
    if len(rows)!=2 or initial!={'at':'0','value':'0'} or any(set(p)!={'if','value'} for p in rows):
        raise Unsupported('The source partition and its anchoring data are incomplete')
    first,second=rows
    if first['if'].replace(' ','')!='0<'+v+'<=1' or second['if'].replace(' ','')!=v+'>1':
        raise Unsupported('The two source pieces must cover the full positive logarithm domain')
    y=('v','y');field=[m.simplify(m.substitute(m.parse(row['value'],v),{x:('exp',y)})) for row in rows]
    if compare_constant_pair(field,y)!=0:raise Unsupported('The two derivative traces do not agree at zero')
    terms=[]
    for g in field:
        H=integrate_child(request,g,'y')
        terms.append(m.add(H,m.neg(m.simplify(m.substitute(H,{y:ZERO})))))
    return dict(theorem='method.formal_primitive_transport',argument=[
        'The logarithm maps (0,1] onto the nonpositive half-line and (1,∞) onto the positive half-line.',
        'Transport the derivative by x=exp(y). Integrate each field and fix the constants using the given common value at zero.',
        'The equal derivative traces ensure differentiability at zero.',
    ]),dict(representative=('piecewise_primitive',(((None,ZERO),terms[0]),((ZERO,None),terms[1]))),domain='all real y',value_at_zero=ZERO)


def compare_constant_pair(fields,y):
    from ray_proofs import compare_scalar
    return compare_scalar(*(m.simplify(m.substitute(g,{y:ZERO})) for g in fields))


def exponential_primitive_theorem(task):
    """Derive the general exponential pole reduction or its elementary criterion."""
    if set(task)-{'kind','id','source','source_statement','requested_output'} or task.get('requested_output')!=['complete_proof']:
        raise Unsupported('The whole abstract exponential primitive claim is required')
    statement=task['source_statement']
    pole_steps=[
        'Divide the rational function into its polynomial part and parts at each real pole. For nonzero rate a, solve G′+aG for the polynomial part by decreasing degrees.',
        'At a pole r, differentiate e^(ax)/(x−r)^j. The leading term −j e^(ax)/(x−r)^(j+1) reduces every order above one.',
        'The simple residual term has primitive e^(ar) li(e^(a(x−r))) on each original component.',
    ]
    if task['kind']=='prove_integral_representation' and re.fullmatch(
            r'Доказать, что интеграл R\(x\) exp\(a\*x\) dx, где R — рациональная функция, знаменатель которой имеет лишь действительные корни, выражается через элементарные функции и трансцендентную функцию ∫exp\(a\*x\)/x dx=li\(exp\(a\*x\)\)\+C, где li\(x\)=∫dx/ln\(x\)\.',statement):
        return (dict(theorem='method.exponential_rational_poles',argument=[*pole_steps,
            'When a=0 the original integrand is rational and has an elementary primitive. The notation li(e^(a x)) only applies to a≠0; the limit branch is handled by the ordinary logarithm.']),
            dict(representation='elementary terms plus the residual li terms',zero_rate='rational partial fractions',domain='every component avoiding original real poles'))
    if task['kind']=='characterize_elementary_integrability' and re.fullmatch(
            r'В каком случае интеграл P\(1/x\) exp\(x\) dx, где P\(1/x\)=a0\+a1/x\+\.\.\.\+an/x\^n и a0,\.\.\.,an постоянны, представляет собой элементарную функцию\?',statement):
        return dict(theorem='method.exponential_elementarity_criterion',argument=[*pole_steps,
            'At unit rate a pole x^(−j) reduces to x^(−j+1)/(j−1) modulo a derivative. Therefore the coefficient of the remaining simple pole is Σ_(j=1)^n a_j/(j−1)!.',
            'For necessity apply the Liouville theorem in C(x,t), t=e^x, with t′=t. Taking normalized trace and norm reduces the elementary derivative to a rational derivative plus logarithmic derivatives in this field.',
            'A rational logarithmic derivative has no positive powers in its Laurent expansion at t=∞. Comparing coefficients of t in the rational derivative would therefore give a rational G with G′+G=1/x if a nonzero residue remained.',
            'Any finite pole of G of order j≥1 gives a pole of order j+1 in G′+G. A polynomial G has no finite poles. Neither case yields the single simple pole at zero.',
        ]),dict(elementary_if_and_only_if='Σ_(j=1)^n a_j/[(j−1)!] = 0',domain='components of the original domain')
    raise Unsupported('The original rationality, pole and coefficient conditions are not all bound')


def indexed_logarithmic_primitive(task):
    conditions=task.get('stated_conditions',[]);parameters=task.get('parameters',[])
    if len(parameters)!=1 or conditions!=[parameters[0]+' is a natural number']:
        raise Unsupported('A fixed natural index is required')
    x,raw,ctx,method=input_data(dict(task,stated_conditions=[]),{'table_and_rules'})
    n=('s',parameters[0]);log=('ln',x);weight=('rpow',log,n)
    coeff,count=separate_weight(raw,weight)
    if count!=1:raise Unsupported('One indexed logarithm is required')
    p,d=rf(coeff,x[1])
    if not any(p) or sum(bool(c) for c in p)!=1 or sum(bool(c) for c in d)!=1:
        raise Unsupported('The indexed logarithm must have a single known power weight')
    a=len(p)-len(d);k=q(p[-1]/d[-1]);rho=q(a+1)
    guard=domain_conditions(raw,positive_integer_exponents=(n,))
    if any(g[1]!=x for g in guard):raise Unsupported('A different original logarithm domain is unresolved')
    answer=m.mul(k,('indexed_log_primitive',x,n,rho)) if rho!=ZERO else m.mul(k,('div',('rpow',log,m.add(n,ONE)),m.add(n,ONE)))
    val=family(raw,answer,region='x>0')
    val['original_domain']=('and',guard)
    return dict(theorem='method.power_kernel_parts',chart='indexed_logarithm',fixed_weight_power=q(a),index=n,
                argument=['Use the positive real base x>0 and the stated natural logarithm index.',
                          'Integration by parts lowers the index by one. For nonzero weight exponent plus one, repeat to the zero-index power integral.',
                          'The finite falling-factorial expansion telescopes on differentiation. If the weight is 1/x, integrate the logarithm power directly.']),val


def trig_primitive_recurrence(task,library):
    """Derive the printed symbolic recurrence by a single differentiated product."""
    if not library.data.get('elementary_primitive_transitions') or set(task)-{'id','kind','source','family','relation','stated_conditions','requested_output'}:
        raise Unsupported('The symbolic primitive recurrence is unavailable')
    if (task['family']=='I(n)=integral(1/(a+b*cos(x))^n,x)'
            and task.get('relation')=='I(n)=A*sin(x)/(a+b*cos(x))^(n-1)+B*I(n-1)+C*I(n-2)'
            and task.get('stated_conditions')==['n integer','n>1','abs(a)!=abs(b)']
            and task.get('requested_output')==['coefficients','proof_of_recurrence']):
        denom='((n-1)*(b^2-a^2))'
        answer=dict(A='b/'+denom,B='-(2*n-3)*a/'+denom,C='(n-2)/'+denom,
                    required_domain='a+b*cos(x)!=0')
        steps=['Set D=a+b cos x and differentiate b sin(x)/D^(n−1).',
               'Substitute b cos(x)=D−a and b²sin²(x)=b²−(D−a)².',
               'The result is (n−1)(b²−a²)/Dⁿ+(2n−3)a/D^(n−1)+(2−n)/D^(n−2).',
               'Divide only by (n−1)(b²−a²), which is nonzero by the original conditions. The derivation allows b=0.']
    elif (task['family']=='I(n)=integral((sin((x-a)/2)/sin((x+a)/2))^n,x)'
          and 'relation' not in task and task.get('stated_conditions')==['n natural']
          and task.get('requested_output')==['derive_reduction_formula']):
        answer=dict(coordinate='t=sin((x-a)/2)/sin((x+a)/2)',
                    general='I(n)=2*sin(a)*t^(n-1)/(n-1)+2*cos(a)*I(n-1)-I(n-2), n>1',
                    initial=['I(0)=x','I(1)=cos(a)*x-2*sin(a)*ln(abs(sin((x+a)/2)))'],
                    required_domain='sin((x+a)/2)!=0')
        steps=['The ratio t equals cos a−sin a cot((x+a)/2).',
               'Its derivative satisfies 2 sin(a)t′=t²−2cos(a)t+1 by 1+cot²=1/sin².',
               'Multiply by t^(n−2), integrate, and identify the initial integrals. The argument also holds at sin a=0.']
    else:raise Unsupported('The original recurrence lacks an admitted index or denominator condition')
    return dict(theorem='method.trig_linear_rational',argument=steps),answer


FOUNDATION_CHARTS=('verified_integrand_split','monomial_differential','conjugate_quadratics',
                   'exact_partial_fractions','parametric_partial_fractions','symbolic_quadratic_kernel',
                   'folded_periodic_differential','positive_radical_product','hyperbolic_square','rescaled_exponential_radical',
                   'real_root_periodic_coordinate','rational_factor_division','parameter_linear_split')


def foundation_options(task):
    method=task.get('method_requirement','table_and_rules')
    if method=='integrand_decomposition':
        return ('verified_integrand_split','monomial_differential',*partial_fraction_options(task))
    options=()
    if method in ('table_and_rules','appropriate_integrand_transformation','appropriate_substitution','quadratic_canonical_form'):
        options+=('monomial_differential',)
    if method in ('table_and_rules','rational_decomposition',HERMITE_METHOD):
        options+=('conjugate_quadratics',)
    return (options+partial_fraction_options(task)+guarded_differential_options(task)+periodic_root_options(task)
            +rational_division_options(task)+parameter_linear_options(task))


def foundation_transition(task,library,request,chart):
    if (not library.data.get('primitive_foundation_transitions') or chart not in foundation_options(task)):
        raise Unsupported('The prescribed method does not admit this transition')
    try:
        if chart=='parameter_linear_split':
            if not library.data.get('rational_factor_division'):raise Unsupported('The parameter split is unavailable')
            return parameter_linear_split(task,request)
        if chart=='rational_factor_division':
            if not library.data.get('rational_factor_division'):raise Unsupported('The rational factor division is unavailable')
            return rational_factor_division(task,request)
        if chart=='real_root_periodic_coordinate':
            if not library.data.get('real_root_periodic_coordinate'):raise Unsupported('The periodic root coordinate is unavailable')
            return real_root_periodic_coordinate(task,request)
        if chart in guarded_differential_options(task):
            if not library.data.get('guarded_quadratic_differentials'):raise Unsupported('The guarded differential transition is unavailable')
            handler={'symbolic_quadratic_kernel':symbolic_quadratic_kernel,'folded_periodic_differential':folded_periodic_differential,
                     'positive_radical_product':positive_radical_product,'hyperbolic_square':hyperbolic_square,
                     'rescaled_exponential_radical':rescaled_exponential_radical}[chart]
            return handler(task)
        if chart in ('exact_partial_fractions','parametric_partial_fractions'):
            if not library.data.get('exact_partial_fraction_replay'):raise Unsupported('Exact partial fraction replay is unavailable')
            if chart=='exact_partial_fractions':return replay_partial_fractions(task,library)
            return parametric_partial_fractions(task)
        if chart=='monomial_differential':return monomial_differential(task,request)
        if chart=='conjugate_quadratics':return conjugate_quadratic_primitive(task,library,request)
        if chart=='verified_integrand_split':return certified_integrand_split(task,request)
    except (NotRational,Undefined) as exc:
        raise Unsupported('An exact source field was not identified') from exc
    raise Unsupported('Unknown primitive transition')


def fixed_integral_source(task):
    v,params,ctx,raw=integral_source(task)
    if params:raise Unsupported('Coefficients must be fixed here')
    return v,raw


def monomial_differential(task,request):
    """Pull back a rational kernel using the common stride of actual exponents."""
    from math import gcd
    v,raw=fixed_integral_source(task)
    rational=raw;root=None;root_power=0;radicand=()
    try:P,D=rf(raw,v)
    except NotRational:
        roots={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0] in ('sqrt','cbrt')}
        if len(roots)!=1:raise Unsupported('A single multiplicative algebraic generator is required')
        root,=roots
        def separate(e):
            if e==root:return ONE,1
            if e[0]=='pow':
                part,power=separate(e[1])
                return m.power(part,e[2]),power*e[2]
            if e[0] in ('mul','div'):
                a,i=separate(e[1]);b,j=separate(e[2])
                return (('mul',a,b),i+j) if e[0]=='mul' else (('div',a,b),i-j)
            return e,0
        rational,root_power=separate(raw)
        P,D=rf(rational,v)
        R,S=rf(root[1],v)
        if not root_power or len(S)!=1 or domain_conditions(root[1]) or len(R)<2:
            raise Unsupported('The original algebraic generator needs a regular polynomial base')
        radicand=tuple(r/S[0] for r in R)
    if not any(P) or len(D)<2 and not radicand:
        raise Unsupported('No rational denominator or nonconstant radical to reduce')
    shift=valuation(D)
    stride=gcd(*(i+1-shift for i,c in enumerate(P) if c),*(j-shift for j,c in enumerate(D) if c),
               *(j for j,c in enumerate(radicand) if j and c))
    if stride<2 or stride>24:raise Unsupported('No supported strict monomial reduction')
    name=kernel_symbol(task);w=('v',name);x=('v',v)
    top=[((i+1-shift)//stride-1,q(c/stride)) for i,c in enumerate(P) if c]
    bottom=[((j-shift)//stride,q(c)) for j,c in enumerate(D) if c]
    lift=max(0,-min(j for j,_ in top))
    if lift and not shift:raise Unsupported('An artificial zero at the original origin would be introduced')
    def polynomial(terms):
        result=ZERO
        for j,c in terms:result=m.add(result,m.mul(c,m.power(w,j+lift)))
        return result
    kernel=m.div(polynomial(top),polynomial(bottom));coordinate=m.power(x,stride)
    jac=m.mul(q(stride),m.power(x,stride-1))
    from verify import same_value
    if not same_value(m.mul(jac,m.substitute(kernel,{w:coordinate})),rational):
        raise Unsupported('Monomial pullback does not reconstruct the integrand')
    image=None
    if root is not None:
        image=(root[0],polynomial_expression(radicand[::stride],name))
        if not same_value(m.substitute(image[1],{w:coordinate}),root[1]):
            raise Unsupported('The chart alters the original root argument')
        kernel=m.mul(kernel,m.power(image,root_power))
    method=task.get('method_requirement','table_and_rules')
    child=dict(kind='integrate',integrand=source(kernel),variable=name,
               method_requirement=method if method in ('quadratic_canonical_form','integrand_decomposition') else 'table_and_rules',
               requested_output=['primitive_family'])
    H=freeze(request('primitive of the exact monomial kernel',child)['value']['representative'])
    return dict(theorem='method.monomial_differential_stride',chart='monomial_differential',coordinate=coordinate,
                jacobian=jac,kernel=kernel,radical_image=image,original_denominator=tuple(map(q,D)),argument=[
        'All surviving source exponents satisfy a common residue relation modulo the proposed stride.',
        'Multiply the transformed rational part by the power derivative and compare exact coefficients. A radical keeps its exact argument and real branch.',
        'The pulled-back kernel denominator has no new finite zeros on the original domain. If the origin is regular, the derivative identity extends there by continuity.',
    ]),family(raw,m.substitute(H,{w:coordinate}))


def conjugate_quadratic_primitive(task,library,request):
    """Decompose a reciprocal quartic into positive conjugate quadratics exactly over Q."""
    from math import isqrt
    v,raw=fixed_integral_source(task);x=('v',v)
    if task.get('method_requirement')==HERMITE_METHOD:
        contract=library.data.get('rational_primitive_plan',{})
        if not library.data.get(HERMITE_METHOD):raise Unsupported('The required Ostrogradsky reduction is unavailable')
        split=hermite_reduction(raw,v,contract['max_degree'])
        rest=split['remainder']
        child=dict(kind='integrate',integrand=source(rest),variable=v,method_requirement='rational_decomposition',
                   requested_output=['primitive_family'])
        H=freeze(request('partial fractions of the certified square-free remainder',child)['value']['representative']) if rest!=ZERO else ZERO
        return dict(theorem='method.conjugate_quadratic_factors',chart='conjugate_quadratics',hermite=split,argument=[
            'Carry out the original Ostrogradsky reduction by coefficient matching. Check the derivative identity and that the remainder has a square-free denominator.',
            'Integrate the verified remainder and restore the rational part of the primitive.',
        ]),family(raw,m.add(split['rational_part'],H))
    P,D=rf(raw,v);common=pgcd(P,D);P,D=pdiv(P,common)[0],pdiv(D,common)[0]
    if not any(P):raise Unsupported('No nonzero source field to decompose')
    P,D=(tuple(c/D[-1] for c in poly) for poly in (P,D))
    if library.data.get('even_quartic_algebraic_coefficients'):
        from polynomial import quotient_derivative_numerator
        repeated=pgcd(D,quotient_derivative_numerator(D,(F(1),)))
        squarefree=pdiv(D,repeated)[0]
        power=valuation(squarefree); quartic=squarefree[power:]
        if (len(quartic)==5 and quartic[-1]==1 and quartic[0]>0 and quartic[1]==quartic[3]==0
                and quartic[2]**2<4*quartic[0]):
            if len(repeated)>1:
                split=hermite_reduction(raw,v,library.data['rational_primitive_plan']['max_degree'])
                rest=split['remainder'];H=integrate_child(request,rest,v) if rest!=ZERO else ZERO
                return dict(theorem='method.even_quartic_algebraic_coefficients',chart='conjugate_quadratics',hermite=split,argument=[
                    'Редукция Эрмита удаляет кратные полюсы, сохраняя точно проверенное рациональное слагаемое.',
                    'Оставшийся бескратный знаменатель даёт отдельный рациональный интеграл. Складываем доказанные части на исходной области.'
                ]),family(raw,m.add(split['rational_part'],H))
            return even_quartic_algebraic_primitive(raw,v,P,D,quartic,power,request)
    whole,rest=pdiv(P,D)
    for Q in denominator_factors(raw,D,v):
        if len(Q)!=5 or Q[0]<=0:continue
        a,b=isqrt(Q[0].numerator),isqrt(Q[0].denominator)
        c=F(a,b)
        if c*c!=Q[0] or Q[1]!=c*Q[3]:continue
        u=Q[3]/2;d=2*c+u*u-Q[2];head=4*c-u*u-d
        if d<=0 or head<=0 or head*head<=4*u*u*d:continue
        M,rem=pdiv(D,Q)
        if any(rem) or len(pgcd(M,Q))!=1:continue
        base=(c,u,F(1));twice=pm((F(2),),base)
        columns=[pm(M,z) for z in (twice,(F(0),*twice),(F(0),-2*d),(F(0),F(0),-2*d))]
        columns.extend((F(0),)*n+Q for n in range(len(M)-1))
        weights=span_coefficients(rest,columns)
        if weights is not None:break
    else:raise Unsupported('No exact positive conjugate quadratic factorization')
    a0,a1,b0,b1,*aux=weights
    sqrt=lambda e:('sqrt',e)
    scale=sqrt(q(d));answer=ZERO;pairs=[]
    for sign in (-1,1):
        t=m.mul(q(sign),scale);L=m.add(q(u),t)
        linear=m.add(q(a1),m.mul(q(b1),t));constant=m.add(q(a0),m.mul(q(b0),t))
        denominator=m.add(m.add(m.power(x,2),m.mul(L,x)),q(c))
        disc=m.add(q(4*c),m.neg(m.power(L,2)));root=sqrt(disc)
        atan=m.div(m.mul(q(2),('atan',m.div(m.add(m.mul(q(2),x),L),root))),root)
        term=m.add(m.mul(m.div(linear,q(2)),('ln',denominator)),
                   m.mul(m.add(constant,m.neg(m.div(m.mul(linear,L),q(2)))),atan))
        answer=m.add(answer,term)
        pairs.append(dict(denominator=denominator,numerator=m.add(m.mul(linear,x),constant),primitive=term))
    polynomial=polynomial_expression(whole,v)
    residual=polynomial_expression(aux or (F(0),),v)
    G=m.add(polynomial,m.div(residual,polynomial_expression(M,v)))
    if G!=ZERO:answer=m.add(answer,integrate_child(request,G,v))
    return dict(theorem='method.conjugate_quadratic_factors',chart='conjugate_quadratics',rational_factor=tuple(map(q,Q)),cofactor=tuple(map(q,M)),
                discriminant_bounds=(q(head),q(4*u*u*d)),terms=pairs,rational_remainder=G,argument=[
        'Write the degree-four factor as the product of monic quadratics with linear coefficients u±√d and equal positive constant c.',
        'The positive discriminant complements follow from 4c−u²−d>2|u|√d. No factor has a real pole.',
        'Compare exact rational coefficients after pairing conjugates. Integrate each linear numerator against the completed square by a logarithm and an arctangent.',
    ]),family(raw,answer)


def even_quartic_algebraic_primitive(raw,v,P,D,Q,power,request):
    """Integrate over two real conjugate quadratics, with a possible pole at zero."""
    x=('v',v);whole,rest=pdiv(P,D)
    monomial=(F(0),)*power+(F(1),)
    columns=[(F(0),)*j+monomial for j in range(4)]+[(F(0),)*j+Q for j in range(power)]
    weights=span_coefficients(rest,columns)
    if weights is None:raise Unsupported('The quartic and monomial numerator identity failed')
    W=polynomial_expression(whole,v)
    if any(weights[4:]):W=m.add(W,m.div(polynomial_expression(weights[4:],v),m.power(x,power)))
    answer=integrate_child(request,W,v) if W!=ZERO else ZERO
    n0,n1,n2,n3=map(q,weights[:4]);c,b=q(Q[0]),q(Q[2]);s=('sqrt',c)
    two_s=m.mul(q(2),s);d=('sqrt',m.add(two_s,m.neg(b)));delta=('sqrt',m.add(two_s,b))
    # The sums and the differences of the two linear numerators determine all four coefficients.
    A=n3;B=m.div(n0,s);Ad=m.div(m.add(B,m.neg(n2)),d);Bd=m.div(m.add(m.mul(s,A),m.neg(n1)),d)
    factors=[]
    for sign in (-1,1):
        L=m.mul(q(sign),d);a=m.div(m.add(A,m.mul(q(sign),Ad)),q(2));b0=m.div(m.add(B,m.mul(q(sign),Bd)),q(2))
        denominator=m.add(m.add(m.power(x,2),m.mul(L,x)),s)
        H=m.div(m.mul(q(2),('atan',m.div(m.add(m.mul(q(2),x),L),delta))),delta)
        primitive=m.add(m.mul(m.div(a,q(2)),('ln',denominator)),m.mul(m.add(b0,m.neg(m.div(m.mul(a,L),q(2)))),H))
        answer=m.add(answer,primitive);factors.append(dict(denominator=denominator,numerator=m.add(m.mul(a,x),b0)))
    return dict(theorem='method.even_quartic_algebraic_coefficients',chart='conjugate_quadratics',quartic=tuple(map(q,Q)),
                linear_numerators=factors,quadratic_discriminant_complement=m.power(delta,2),argument=[
                    'Выделяем возможный полюс в нуле и делим правильную дробь по взаимно простым множителям.',
                    'Четвёртая степень распадается на два положительных квадратных трёхчлена. Коэффициенты линейных числителей определяются из суммы и разности.',
                    'Производная логарифма и арктангенс дают первообразные обоих квадратных знаменателей.'
                ]),family(raw,answer)


def trigonometric_split(raw,v):
    """Provide an explicit split of a Laurent monomial by its unit relation."""
    angles=set();families=set()
    powers={'sin':(1,0),'cos':(0,1),'tan':(1,-1),'cot':(-1,1),'sec':(0,-1),'csc':(-1,0),
            'sinh':(1,0),'cosh':(0,1),'tanh':(1,-1)}
    def collect(E,n=1):
        if E[0]=='pow':return collect(E[1],n*E[2])
        if E[0] in ('mul','div'):
            c,a,b=collect(E[1],n);d,p,r=collect(E[2],n if E[0]=='mul' else -n)
            return c*d,a+p,b+r
        if E[0] in powers and m.variable_in(E,v):
            angles.add(E[1]);families.add(E[0] in ('sinh','cosh','tanh'))
            a,b=powers[E[0]];return F(1),n*a,n*b
        c=m.num(m.simplify(E))
        if c is None or not c and n<=0:raise Unsupported('Not a Laurent monomial in one trigonometric phase')
        return c**n,0,0
    try:C,a,b=collect(raw)
    except Unsupported:return None
    if not C or len(angles)!=1 or len(families)!=1:return None
    angle,=angles;hyper,=families;e=-1 if hyper else 1
    rate,_=affine(angle,v)
    if not m.num(rate) or domain_conditions(angle):return None
    if a<0 and b<0 and (a<=-2 or b<=-2):indices=[(1,a,b+2),(e,a+2,b)]
    elif a>=2 and b<0:indices=[(e,a-2,b),(-e,a-2,b+2)]
    elif b>=2 and a<0:indices=[(1,a,b-2),(-e,a+2,b-2)]
    elif not hyper and a==0 and b<=-4:indices=[(1,0,b+2),(1,2,b)]
    elif not hyper and b==0 and a<=-4:indices=[(1,a+2,0),(1,a,2)]
    else:return None
    from polynomial import pp
    relation=(F(1),F(0),F(-e))
    rows=[(-1,a,b),*indices]
    p0=min(j for _,j,_ in rows);q0=min(k for _,_,k in rows)
    parts=[(F(0),),(F(0),)]
    for w,j,k in rows:
        power,parity=divmod(k-q0,2)
        coefficient=pm((F(0),)*(j-p0)+(F(w),),pp(relation,power))
        parts[parity]=pa(parts[parity],coefficient)
    if any(any(p) for p in parts):raise Unsupported('Cleared trigonometric decomposition identity failed')
    S=('sinh' if hyper else 'sin',angle);C0=('cosh' if hyper else 'cos',angle)
    # Build the monomials without replacing positive powers by additional reciprocal factors.
    terms=[m.mul(q(C*w),m.mul(m.power(S,j),m.power(C0,k))) for w,j,k in indices]
    return terms,dict(coordinate=angle,source_exponents=(a,b),split_exponents=indices,identity='C²+εS²=1',epsilon=e)


def affine_power_split(raw,v):
    """Expand a polynomial multiplier in the argument already present in a root or power."""
    if raw[0]=='div' and raw[2][0] in ('sqrt','cbrt','pow'):
        P,R=raw[1:];k=-1
    elif raw[0]=='mul':
        def factors(e):
            return factors(e[1])+factors(e[2]) if e[0]=='mul' else [e]
        factors=factors(raw)
        radicals=[e for e in factors if e[0] in ('sqrt','cbrt')]
        if len(radicals)!=1:return None
        R,=radicals;k=1;P=ONE
        for e in factors:
            if e!=R:P=m.mul(P,e)
    else:return None
    base=R[1];s,h=map(m.num,affine(base,v))
    if not s or h is None:return None
    p,d=rf(P,v)
    if len(d)!=1 or len(p)>17 or domain_conditions(P) or domain_conditions(base):return None
    coeff=[F(0)]*len(p)
    for degree,value in enumerate(p):
        for j in range(degree+1):coeff[j]+=value*comb(degree,j)*(-h)**(degree-j)/s**degree/d[0]
    from polynomial import pp
    check=(F(0),)
    for j,c in enumerate(coeff):check=pa(check,pm((c,),pp((h,s),j)))
    if check!=tuple(c/d[0] for c in p):raise Unsupported('Affine expansion does not reconstruct the source weight')
    terms=[];direct=[]
    for i,c in enumerate(coeff):
        if not c:continue
        if R[0]=='pow':
            power=i+k*R[2];degree=power+1
            terms.append(('mul',q(c),('pow',base,power)))
            direct.append(('mul',q(c/s),lnabs(base)) if not degree else
                          ('mul',q(c/(s*degree)),('pow',base,degree)))
        else:
            z=m.mul(q(c),m.power(base,i))
            terms.append(m.mul(z,R) if k==1 else m.div(z,R))
    return (terms,dict(coordinate=base,coefficient_expansion=tuple(map(q,coeff)),identity='x=(y−h)/s',
                       affine_power_primitives=direct)) if len(terms)>1 else None


def exponential_split(raw,v):
    """Recognize a polynomial quotient in one common positive exponential."""
    if raw[0]!='div':return None
    atoms={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0]=='exp'}
    if not atoms:return None
    rates={}
    for z in sorted(atoms,key=repr):
        rate,shift=affine(z[1],v);k=m.num(rate)
        if not k or shift!=ZERO or domain_conditions(z[1]):return None
        rates[z]=k
    stride=common_phase_rate(rates.values());x=('v',v)
    name=next(n for n in ('_exp_coordinate','_exp_coordinate2') if n!=v)
    y=('v',name)
    exponents={z:int(k/stride) for z,k in rates.items()}
    if any(not 1<=j<=16 for j in exponents.values()):return None
    repl={z:m.power(y,j) for z,j in exponents.items()}
    n,den=rf(m.substitute(raw[1],repl),name);d,scale=rf(m.substitute(raw[2],repl),name)
    if len(den)!=1 or len(scale)!=1 or len(d)<=1 or len(n) not in (1,len(d)):return None
    n,d=tuple(c/den[0] for c in n),tuple(c/scale[0] for c in d)
    constant=(n[-1]/d[-1] if len(n)==len(d) else n[0]/d[0] if d[0] else F(0))
    residual=pa(n,tuple(-constant*c for c in d))
    if not constant or not any(residual):return None
    E=('exp',m.mul(q(stride),x))
    rem=m.substitute(polynomial_expression(residual,name),{y:E})
    return ([q(constant),m.div(rem,raw[2])],dict(identity='division plus exact source remainder',coordinate=E,
                  polynomial_numerator=tuple(map(q,n)),polynomial_denominator=tuple(map(q,d))))


def certified_integrand_split(task,request):
    """Expose a checked nontrivial sum before requesting its primitive terms."""
    v,raw=fixed_integral_source(task)
    result=trigonometric_split(raw,v)
    if result is None:
        try:result=affine_power_split(raw,v)
        except (Unsupported,NotRational,Undefined):pass
    if result is None and raw[0]=='div' and raw[2][0]=='add' and all(z[0]=='sqrt' for z in raw[2][1:]):
        U,V=raw[2][1:];gap=m.num(m.simplify(m.add(U[1],m.neg(V[1]))))
        if gap and not domain_conditions(raw[1]) and not domain_conditions(U[1]) and not domain_conditions(V[1]):
            result=([m.div(m.mul(raw[1],U),q(gap)),m.div(m.neg(m.mul(raw[1],V)),q(gap))],
                    dict(identity='(√A+√B)(√A−√B)=A−B',radicand_gap=q(gap)))
    if result is None:result=exponential_split(raw,v)
    if result is None:raise Unsupported('No verified two-term split from the original field')
    terms,evidence=result
    value=ZERO;children=[]
    direct=evidence.get('affine_power_primitives',[])
    for i,term in enumerate(terms):
        primitive=direct[i] if direct else integrate_child(request,term,v)
        value=('add',value,primitive) if direct and value!=ZERO else primitive if direct else m.add(value,primitive)
        children.append(dict(integrand=term,primitive=primitive))
    return dict(theorem='method.certified_integrand_decomposition',chart='verified_integrand_split',decomposition=evidence,
                terms=children,argument=[
        'Expand the source identity. The resulting integrand is '+' + '.join(source(term) for term in terms)+' on the original domain.',
        'Check separate primitives for all terms; linearity gives the sum with one constant on each original component.',
    ]),family(raw,value)


def reciprocal_factors(poly):
    """Offer exact monic factors of a reciprocal quartic, possibly in one power."""
    from math import gcd,isqrt
    def root(t):
        if t<0:return None
        h,k=isqrt(t.numerator),isqrt(t.denominator)
        return Fraction(h,k) if h*h==t.numerator and k*k==t.denominator else None
    def roots(s,p):
        radical=root(s*s-4*p)
        return () if radical is None else ((s+radical)/2,(s-radical)/2)
    if poly[0]!=1 or poly!=poly[::-1] or len(poly)<5:return ()
    stride=gcd(*(i for i,c in enumerate(poly) if i and c))
    lifted_stride=stride//2 if len(poly[::stride])==3 and stride%2==0 else 1
    small=poly[::lifted_stride]
    if len(small)!=5:return ()
    _,b,c,_,_=small
    cases=[(l,1) for l in roots(b,c-2)]
    for u in roots(c-2,b*b-2*c):
        if u<=2:continue
        cases.extend((b*k/(k+1),k) for k in roots(u,Fraction(1)) if k>0)
    return tuple((Fraction(k),)+(Fraction(0),)*(lifted_stride-1)+(l,)
                 +(Fraction(0),)*(lifted_stride-1)+(Fraction(1),) for l,k in cases)


def replay_partial_fractions(task,library,proposal=None):
    """Certify poles, numerator span and primitive terms on the unsimplified domain."""
    variable,_,_,raw=integral_source(task)
    P,D=rf(raw,variable)
    if len(D)<2:raise Unsupported('There is no rational denominator to decompose')
    contract=library.data['rational_primitive_plan'];limit=contract['max_degree']
    method=task.get('method_requirement','table_and_rules')
    specializations=library.data.get('primitive_method_specializations',{}).get(method,())
    if method not in contract['methods'] and 'rational_decomposition' not in specializations:
        raise Unsupported('The exact fractions do not meet the requested method')
    if proposal is None:proposal=rational_proposal(task,contract)
    if set(proposal)!={'candidate_source','recipe'} or set(proposal['recipe'])!={'method','terms'} or proposal['recipe']['method']!='rational_decomposition':
        raise Unsupported('Malformed rational decomposition recipe')
    terms=proposal['recipe']['terms']
    if not (1 if method=='rational_decomposition' else 2)<=len(terms)<=limit+1:
        raise Unsupported('A general rational primitive needs a nontrivial decomposition')
    total=(Fraction(0),);answer=ZERO;replay=[]
    for term in terms:
        if set(term)!={'weight','form','integrand','primitive'}:raise Unsupported('Malformed partial fraction term')
        weight=freeze(term['weight'])
        if not isinstance(weight,tuple) or len(weight)!=3 or weight[0]!='q' or type(weight[1]) is not int or type(weight[2]) is not int or weight[2]<=0:
            raise Unsupported('Expected an exact rational weight')
        coefficient=m.num(weight)
        basis,H,_=rational_component(term['form'],variable,limit)
        if not coefficient or basis!=freeze(term['integrand']) or H!=freeze(term['primitive']):
            raise Unsupported('The primitive summand does not match its table form')
        numerator,denominator=rf(basis,variable)
        scale,rest=pdiv(D,denominator)
        if any(rest) or not scale or coefficient is None:
            raise Unsupported('The primitive summand adds a forbidden pole')
        total=pa(total,pm(pm(numerator,scale),(coefficient,)))
        answer=m.add(answer,m.mul(q(coefficient),H))
        replay.append(dict(weight=term['weight'],basis=basis,primitive=H,denominator_quotient=tuple(map(q,scale))))
    if total!=P or source(answer)!=proposal['candidate_source']:
        raise Unsupported('Partial fractions do not reconstruct the original numerator and primitive')
    result=family(raw,answer)
    result['component_scope']='each maximal connected open component J of D'
    return dict(theorem='method.exact_partial_fraction_replay',chart='exact_partial_fractions',terms=replay,
                method='exact_rational_decomposition',variable=variable,source_parameters=[],integrand_ast=raw,
                primitive_ast=answer,natural_domain=domain_conditions(raw),
                full_denominator=tuple(map(q,D)),cleared_numerator=tuple(map(q,total)),argument=[
        'Найти точные делители исходного знаменателя и сравнить коэффициенты после приведения к этому знаменателю.',
        'Каждый появившийся полюс уже исключён исходными условиями. Производная степенной, логарифмической или арктангенсной части возвращает указанное простое слагаемое.',
        'Суммировать первообразные и оставить отдельную постоянную на каждой исходной компоненте.'
    ]),result


def parametric_partial_fractions(task):
    """Compare two moving pole factors without dividing by an unproved parameter."""
    from verify import same_value
    x,raw,ctx,_=input_data(task,{'integrand_decomposition'})
    if raw[0]!='div' or raw[1]!=ONE or raw[2][0]!='mul':
        raise Unsupported('Two denominator factors and constant numerator are required')
    U,V=raw[2][1:]
    formal=('s',x[1]);all_real={**ctx,'parameters':[*ctx['parameters'],x[1]]}
    if not all(m.constant_defined(m.substitute(z,{x:formal}),all_real) for z in (U,V)):
        raise Unsupported('The unsimplified pole factors must be real-defined for real inputs')
    def pole(z):
        base,k=z[1:] if z[0]=='pow' else (z,1)
        slope,gap=affine(base,x[1])
        if slope!=ONE or not 1<=k<=6 or not m.constant_defined(gap,ctx):
            raise Unsupported('The linear poles must be real and monic')
        return base,k,gap
    try:a,r,h=pole(U);b,s,j=pole(V)
    except Unsupported:
        if any(z[0]!='add' for z in (U,V)):
            raise Unsupported('No supported pair of moving denominator factors')
        xp=m.power(x,2);p,q_=[z[2] if z[1]==xp else z[1] if z[2]==xp else ZERO for z in (U,V)]
        if any(z[0]!='pow' or z[2]!=2 or not m.constant_defined(z[1],ctx) or m.variable_in(z[1],x[1]) for z in (p,q_)):
            raise Unsupported('Each quadratic factor must have a fixed real square shift')
        gap=m.add(p,m.neg(q_))
        if not m.nonzero(gap,ctx):raise Unsupported('Need a proof that the two squared shifts are unequal')
        split=m.div(m.add(m.div(ONE,V),m.neg(m.div(ONE,U))),gap)
        if not same_value(split,raw):raise Unsupported('The quadratic partial fractions failed coefficient checking')
        def base(z,case):
            if case:return m.neg(m.div(ONE,x))
            a=('abs',z[1]);return m.div(('atan',m.div(x,a)),a)
        branches=[]
        for left,right in ((False,False),(True,False),(False,True)):
            conditions=[('zero' if c else 'nonzero',z[1]) for c,z in zip((left,right),(p,q_))]
            H=m.div(m.add(base(q_,right),m.neg(base(p,left))),gap)
            clause=' и '.join(source(z)+('=0' if rel=='zero' else '≠0') for rel,z in conditions)
            branches.append(dict(condition=clause,conditions=conditions,representative=H))
        return dict(theorem='method.exact_partial_fraction_replay',chart='parametric_partial_fractions',gap=gap,split=split,argument=[
            'Вычесть два квадратичных знаменателя. Деление на разность квадратов оправдывает условие задачи.',
            'Для ненулевого параметра применить арктангенс с его модулем. Нулевой параметр даёт −1/x на исходных компонентах. Оба параметра не могут обращаться в ноль одновременно.'
        ]),family(raw,branches=branches)
    gap=m.add(j,m.neg(h))
    if not m.nonzero(gap,ctx):raise Unsupported('Need a proof that the two original poles stay distinct')
    answer=ZERO;numerator=(Fraction(0),);terms=[]
    from polynomial import pp
    for z,length,other,orientation in ((a,r,s,1),(b,s,r,-1)):
        for k in range(1,length+1):
            j=length-k; coefficient=(-1)**(j if orientation==1 else other)*comb(other+j-1,j)
            w=('div',q(coefficient),('pow',gap,other+j))
            u=('pow',z,-k);H=lnabs(z) if k==1 else ('div',('pow',z,1-k),q(1-k))
            term=('mul',w,H);answer=term if answer==ZERO else ('add',answer,term);terms.append((w,u,H))
            origin,shifted=(j,other) if orientation==1 else (other,j)
            numerator=pa(numerator,(Fraction(0),)*origin+tuple(Fraction(coefficient)*c for c in pp((Fraction(1),Fraction(1)),shifted)))
    if numerator!=(Fraction(1),):raise Unsupported('The moving linear partial fractions failed coefficient checking')
    return dict(theorem='method.exact_partial_fraction_replay',chart='parametric_partial_fractions',gap=gap,terms=terms,cleared_scaled_numerator=tuple(map(q,numerator)),argument=[
        'Разложить оставшийся множитель по степеням около каждого исходного полюса. Исходное условие допускает деление на разность полюсов.',
        'После приведения к общему знаменателю точно совпадают коэффициенты исходного числителя.',
        'Применить степенное правило или логарифм модуля на каждой исходной компоненте.'
    ]),family(raw,answer)



def partial_fraction_options(task):
    method=task.get('method_requirement','table_and_rules')
    text=task.get('integrand','');v=task.get('variable','x')
    if not isinstance(text,str) or '/' not in text:return ()
    if task.get('parameters'):
        return ('parametric_partial_fractions',) if method=='integrand_decomposition' else ()
    if method in ('rational_decomposition','integrand_decomposition'):
        return ('exact_partial_fractions',)
    if method=='table_and_rules' and re.search(re.escape(v)+r'\^[4-9]',text):
        return ('exact_partial_fractions','conjugate_quadratics')
    return ()


def guarded_differential_options(task):
    method=task.get('method_requirement','table_and_rules');text=task.get('integrand','')
    if not isinstance(text,str):return ()
    if method=='quadratic_canonical_form' and task.get('parameters'):
        return ('symbolic_quadratic_kernel',)
    if method not in {'elementary_table_and_algebra','appropriate_integrand_transformation','appropriate_substitution','table_and_rules'}:
        return ()
    routes=()
    if 'sqrt(' in text and '/' in text:
        if any(tag in text for tag in ('sin(','cos(','sinh(','cosh(')):routes+=('folded_periodic_differential',)
        if numerator_roots(text):routes+=('positive_radical_product',)
        if 'exp(' in text:routes+=('rescaled_exponential_radical',)
    if re.search(r'\b(?:tanh|coth)\(.+\)\^2',text):routes+=('hyperbolic_square',)
    if '/' in text and 'sin(' in text and 'cos(' in text and 'folded_periodic_differential' not in routes:
        routes+=('folded_periodic_differential',)
    return routes


def numerator_roots(text):
    return text.partition('/')[0].count('sqrt(')>=2


def real_polynomial_coefficients(expr,variable,context,max_degree=8):
    """Read a polynomial in one real coordinate before dropping any original factor."""
    x=('v',variable);formal=('s',variable)
    ctx={**context,'parameters':[*context['parameters'],variable]}
    if not m.constant_defined(m.substitute(expr,{x:formal}),ctx):
        raise Unsupported('The unsimplified polynomial must be defined on the original real axis')
    top,bottom=m.rational_form(expr)
    if any(m.variable_in(g,variable) for term in bottom for g,k in term):
        raise Unsupported('A polynomial generator was requested, not a quotient with an extra pole')
    den=m.poly_expr(bottom);out=[ZERO]*(max_degree+1)
    for term,w in top.items():
        deg=next((k for g,k in term if g==x),0)
        rest=tuple((g,k) for g,k in term if g!=x)
        if not 0<=deg<=max_degree or any(m.variable_in(g,variable) for g,k in rest):
            raise Unsupported('The original field exceeds the polynomial degree or has another generator')
        out[deg]=m.add(out[deg],m.div(m.poly_expr({rest:w}),den))
    while len(out)>1 and out[-1]==ZERO:out.pop()
    return tuple(out)


def guarded_input(task,methods):
    variable=task.get('variable','x')
    ctx=m.context(dict(variable=variable,parameters=task.get('parameters',[]),parameter_conditions=task.get('stated_conditions',[])))
    return input_data(dict(task,parameters=ctx['parameters']),methods)


def quadratic_radical_primitive_proof(task,library):
    from verify import same_value

    fields={'id','kind','schema','source','integrand','variable','parameters','stated_conditions','requested_output'}
    if (not library.data.get('quadratic_radical_primitive_proofs') or set(task)-fields-{'claimed_primitive'}
            or task.get('kind') not in ('algebraic_primitive_parameter_condition','verify_parameterized_primitive')):
        raise Unsupported('Expected a quadratic radical primitive goal with all conditions given')
    integral={k:v for k,v in task.items() if k not in ('claimed_primitive','requested_output')}
    integral.update(kind='integrate',integrand=task['integrand'].replace('²','^2'))
    x,raw,ctx,_=guarded_input(integral,{'table_and_rules'})
    if raw[0]!='div' or raw[2][0]!='sqrt':raise Unsupported('Expected a polynomial divided by a square root')
    Q=raw[2][1]; name=x[1]
    def coefficients(e):
        return (*real_polynomial_coefficients(e,name,ctx,2),ZERO,ZERO)[:3]
    c,b,a=coefficients(Q)
    discriminant=m.add(m.power(b,2),m.neg(m.mul(q(4),m.mul(a,c))))
    if task['kind']=='verify_parameterized_primitive':
        if raw[1]!=ONE or task.get('requested_output')!=['proof_on_original_real_components']:
            raise Unsupported('Expected a claimed primitive of the inverse square root')
        H=m.parse(task['claimed_primitive'],name,ctx['parameters'])
        if H[0]!='div' or H[1][0]!='asin' or H[2][0]!='sqrt':
            raise Unsupported('Expected an arcsine divided by a fixed square root')
        u=H[1][1];T=H[2][1]
        if u[0]!='div' or u[2][0]!='sqrt':raise Unsupported('Expected an affine arcsine argument with a fixed radical scale')
        L,S=u[1],u[2][1];slope,_=affine(L,name)
        if (domain_conditions(L) or not all(m.constant_defined(t,ctx) for t in (T,S)) or m.sign(a,ctx)!=-1
                or m.sign(slope,ctx)!=1 or m.sign(T,ctx)!=1):
            raise Unsupported('The source hypotheses do not determine the real branch and the sign of the differential')
        K=m.div(m.power(slope,2),m.neg(a))
        if not (same_value(m.add(S,m.neg(m.power(L,2))),m.mul(K,Q)) and same_value(m.mul(T,K),m.power(slope,2))):
            raise Unsupported('The claimed formula fails the squared differential identity')
        return dict(theorem='method.quadratic_radical_primitive_proofs',affine_argument=L,argument_scale=S,
                    outside_scale=T,identity_factor=K,argument=[
                        'Из точного равенства S − L² = K·Q с K>0 следуют S>0 и |L/√S|<1 на всей исходной области Q>0.',
                        'Дифференцирование арксинуса даёт L′/(√T·√K·√Q). Точное равенство T·K=(L′)² и положительность L′ дают 1/√Q.',
                        'У нисходящей параболы область Q>0 непуста ровно при положительном дискриминанте.'
                    ]),dict(identity=True,primitive=H,original_domain=domain_conditions(raw),nonempty_when=('positive',discriminant))
    if 'claimed_primitive' in task or task.get('requested_output') not in (None,['necessary_and_sufficient_parameter_condition']):
        raise Unsupported('Expected only the necessary and sufficient condition for algebraicity')
    C,B,A=coefficients(raw[1]); eight_a_squared=m.mul(q(8),m.power(a,2))
    U=m.mul(q(4),m.mul(a,A));V=m.add(m.mul(q(8),m.mul(a,B)),m.mul(q(-6),m.mul(b,A)))
    linear=m.add(m.mul(U,x),V); dQ=m.add(m.mul(q(2),m.mul(a,x)),b)
    residue=m.simplify(m.add(m.mul(eight_a_squared,C),m.neg(m.add(m.mul(c,U),m.div(m.mul(b,V),q(2))))))
    if not same_value(m.mul(eight_a_squared,raw[1]),m.add(m.add(m.mul(U,Q),m.div(m.mul(linear,dQ),q(2))),residue)):
        raise Unsupported('The cleared radical reduction did not reconstruct the entire numerator')
    return dict(theorem='method.quadratic_radical_primitive_proofs',clearing_factor=eight_a_squared,scaled_multiplier=linear,
                scaled_residue=residue,argument=[
                    'При a≠0 выделяем производную произведения линейной функции и √Q. Сравнение коэффициентов оставляет постоянный остаток, умноженный на 1/√Q.',
                    'Комплексное продолжение dx/√Q имеет ненулевой вычет на бесконечности. Он остаётся ненулевым при конечном разветвлении, а дифференциал алгебраической функции вычетов не имеет.',
                    'Поэтому при a≠0 алгебраическая первообразная существует ровно при нулевом остатке. Для линейного Q замена √Q даёт многочлен. Постоянный положительный Q также даёт многочлен.'
                ]),dict(degree_two={'leading_nonzero':a,'zero_residue':residue,'real_component_if':[[('positive',a)],[('negative',a),('positive',discriminant)]]},
                        degree_at_most_one={'leading_zero':a,'real_component_if':[[('nonzero',b)],[('zero',b),('positive',c)]],
                                            'algebraic_on_each_component':True},original_domain=domain_conditions(raw))


def parameter_nonzero(expr,ctx):
    if m.nonzero(expr,ctx):return True
    if expr[0]!='s':return False
    for fact in ctx['nonzero_expressions']:
        form,den=m.rational_form(fact)
        if len(form)==1 and any(atom==expr and power>0 for atom,power in next(iter(form))):
            return True
    return False


def stationary_quadratic_kernel(u,coeff,root,ctx):
    """All real branches for ∫1/Q or ∫1/√Q, with no division by a vanished parameter."""
    c,b,a=(*coeff,*(ZERO for _ in range(3-len(coeff))))
    sqrt=lambda z:m.simplify(('sqrt',z))
    if a==ZERO:
        cases=[]
        if b!=ZERO:
            line=m.add(c,m.mul(b,u))
            H=m.mul(q(2),sqrt(line)) if root else lnabs(line)
            cases.append(((('nonzero',b),),m.div(H,b)))
        if c!=ZERO and not m.nonzero(b,ctx):
            conditions=(('zero',b),('positive' if root else 'nonzero',c))
            cases.append((conditions,m.div(u,sqrt(c) if root else c)))
        return cases
    if not parameter_nonzero(a,ctx):raise Unsupported('Need a nonzero quadratic leading coefficient')
    y=m.add(u,m.div(b,m.mul(q(2),a)));d=m.add(c,m.neg(m.div(m.power(b,2),m.mul(q(4),a))))
    if not root:
        cases=[]
        if d!=ZERO:
            p=m.mul(a,d);s=sqrt(m.div(a,d));t=sqrt(m.neg(m.div(a,d)))
            plus=m.add(ONE,m.mul(t,y));minus=m.add(ONE,m.neg(m.mul(t,y)))
            cases=[((('positive',p),),m.div(('atan',m.mul(s,y)),m.mul(d,s))),
                   ((('negative',p),),m.div(m.add(lnabs(plus),m.neg(lnabs(minus))),m.mul(q(2),m.mul(d,t))))]
        if not parameter_nonzero(d,ctx):cases.append(((('zero',d),),m.neg(m.div(ONE,m.mul(a,y)))))
        return cases
    Q=m.add(m.mul(a,m.power(y,2)),d);p=sqrt(a);n=sqrt(m.neg(a));cases=[]
    if d!=ZERO:
        cases.extend([((('positive',a),('nonzero',d)),m.div(lnabs(m.add(m.mul(p,y),sqrt(Q))),p)),
                      ((('negative',a),('positive',d)),m.div(('asin',m.mul(sqrt(m.div(m.neg(a),d)),y)),n))])
    if not parameter_nonzero(d,ctx):
        cases.append(((('positive',a),('zero',d)),m.div(m.mul(m.div(y,('abs',y)),lnabs(y)),p)))
    return cases


def collect_kernel(raw,cases,ctx):
    """Preserve the original real domain, keeping only feasible parameter formulas."""
    alternatives=[]
    labels={'positive':'>0','negative':'<0','zero':'=0','nonzero':'≠0'}
    for conditions,H in cases:
        unresolved=[]
        for rel,t in conditions:
            sign=m.sign(t,ctx)
            if sign is None:
                if rel=='nonzero' and parameter_nonzero(t,ctx):continue
                if rel=='zero' and parameter_nonzero(t,ctx):break
                unresolved.append((rel,t));continue
            if not {'positive':sign>0,'negative':sign<0,'nonzero':sign!=0,'zero':sign==0}[rel]:break
        else:
            if not unresolved:return family(raw,H)
            alternatives.append(dict(condition=' и '.join(source(t)+labels[rel] for rel,t in unresolved),conditions=unresolved,representative=H))
    if not alternatives:raise Unsupported('No nonempty real primitive branch')
    return family(raw,branches=alternatives)


def symbolic_quadratic_kernel(task):
    x,raw,ctx,method=guarded_input(task,{'quadratic_canonical_form'})
    if raw[0]!='div':raise Unsupported('A quadratic denominator is required')
    denom=raw[2];root=denom[0]=='sqrt';Q=denom[1] if root else denom
    coeff=real_polynomial_coefficients(Q,x[1],ctx,2)
    if len(coeff)!=3:raise Unsupported('A genuine quadratic is required')
    P=real_polynomial_coefficients(raw[1],x[1],ctx,1)
    if root and P!=(ONE,):raise Unsupported('This quadratic root rule takes a constant unit numerator')
    c,b,a=coeff
    if not parameter_nonzero(a,ctx):raise Unsupported('A nonzero quadratic leading coefficient must follow from the task')
    k=m.div(P[1],m.mul(q(2),a)) if len(P)>1 else ZERO
    rest=m.add(P[0],m.neg(m.mul(k,b)))
    from verify import same_value
    if not same_value(raw[1],m.add(m.mul(k,m.add(m.mul(q(2),m.mul(a,x)),b)),rest)):
        raise Unsupported('The completed square numerator does not reconstruct the original')
    cases=[(g,m.add(m.mul(k,lnabs(Q)),m.mul(rest,H))) for g,H in stationary_quadratic_kernel(x,coeff,root,ctx)]
    return dict(theorem='method.guarded_quadratic_differential',chart='symbolic_quadratic_kernel',quadratic=coeff,
                derivative_coefficient=k,residual=rest,argument=[
        'Выделить полный квадрат с проверенным ненулевым старшим коэффициентом. В рациональном числителе отделить кратное производной квадратичного знаменателя.',
        'В оставшемся табличном интеграле выбрать действительную ветвь по знаку коэффициентов. При исчезновении свободного члена использовать степень или логарифм модуля на исходных компонентах.',
        'Аргументы полученных корней и обратных функций допустимы на соответствующей исходной ветви.'
    ]),collect_kernel(raw,cases,ctx)


def folded_periodic_poly(expr,phase,U,V,ctx,coords,relation):
    """Exact polynomial in U and V modulo V²=A+B U²."""
    S,C,S2,C2=coords;left,right=relation
    p=m.power(S,2);r=m.power(C,2)
    mappings={S2:m.mul(q(2),m.mul(S,C)),C2:m.add(r,m.mul(q(1 if S[0]=='sinh' else -1),p))}
    x=('v',ctx['original_variable']);base={**ctx,'parameters':[*ctx['parameters'],x[1]]}
    if not m.constant_defined(m.substitute(expr,{x:('s',x[1])}),base):
        raise Unsupported('The folded numerator and radicand must be real-defined before simplification')
    reduced=m.substitute(m.substitute(expr,mappings),{U:('v','_unit_u'),V:('v','_unit_v')})
    top,bottom=m.rational_form(reduced)
    if not bottom or set(bottom)!={()}:raise Unsupported('The proposed kernel still has a variable denominator')
    result=[{},{}]
    for term,w in top.items():
        exps=dict(term);i=exps.pop(('v','_unit_u'),0);k=exps.pop(('v','_unit_v'),0)
        if max(i,k)>12 or any(m.variable_in(a,x[1]) for a in exps):
            raise Unsupported('Higher harmonics or another source variable remain in the kernel')
        coefficient=m.poly_expr({tuple(exps.items()):w/bottom[()]});h,parity=divmod(k,2)
        for j in range(h+1):
            power=i+2*j;weight=comb(h,j)*left**(h-j)*right**j
            result[parity][power]=m.add(result[parity].get(power,ZERO),m.mul(q(weight),coefficient))
    return tuple({i:w for i,w in branch.items() if w!=ZERO} for branch in result)


def folded_periodic_differential(task):
    methods={'table_and_rules','appropriate_integrand_transformation','appropriate_substitution','elementary_table_and_algebra'}
    x,raw,ctx,_=guarded_input(task,methods)
    if raw[0]!='div':raise Unsupported('A rational or radical periodic denominator is required')
    if x[1] in ('_unit_u','_unit_v'):raise Unsupported('The proof coordinates must be fresh')
    numerator,base=raw[1:];root=base[0]=='sqrt';Q=base[1] if root else base
    phases={(g[0] in ('sinh','cosh'),g[1]) for g in learned_nodes(raw) if isinstance(g,tuple) and g[0] in ('sin','cos','sinh','cosh')}
    for hyper,phase in sorted(phases,key=lambda p:len(repr(p[1]))):
        try:rate,_=affine(phase,x[1])
        except Unsupported:continue
        if not m.num(rate) or domain_conditions(phase):continue
        st,ct=('sinh','cosh') if hyper else ('sin','cos')
        S,C=(st,phase),(ct,phase);double=m.mul(q(2),phase);coords=(S,C,(st,double),(ct,double))
        for U,V,relation,sign in ((S,C,(1,1 if hyper else -1),1),(C,S,(-1 if hyper else 1,1 if hyper else -1),1 if hyper else -1)):
            poly=lambda E:folded_periodic_poly(E,phase,U,V,ctx,coords,relation)
            try:(P0,P1),(R0,R1)=poly(numerator),poly(Q)
            except Unsupported:continue
            if P0 or R1 or not R0 or len(P1)!=1:continue
            power,weight=next(iter(P1.items()))
            stride=power+1
            if stride not in (1,2) or any(i%stride for i in R0):continue
            target=tuple(R0.get(j,ZERO) for j in range(0,max(R0)+1,stride));coordinate=m.power(U,stride)
            ratio=m.div(weight,m.mul(q(sign*stride),rate))
            if len(target)==4 and target[:3]==(ZERO,ZERO,ZERO) and target[3]==ONE and root:
                cases=[((),m.div(q(-2),('sqrt',coordinate)))]
            elif len(target)<=3:
                try:cases=stationary_quadratic_kernel(coordinate,target,root,ctx)
                except Unsupported:continue
            else:continue
            try:value=collect_kernel(raw,[(cond,m.mul(ratio,a)) for cond,a in cases],ctx)
            except Unsupported:continue
            return dict(theorem='method.guarded_quadratic_differential',chart='folded_periodic_differential',
                        phase=phase,coordinate=coordinate,unit_relation=relation,jacobian_scale=ratio,quadratic=target,argument=[
                'Раскрыть двойные углы и заменить квадрат второй функции единичным тождеством. Сравнить коэффициенты в исходном числителе и знаменателе.',
                'Числитель после этого равен кратному производной найденной координаты. Тождество умножения остаётся верным в её стационарных точках.',
                'В новой координате применить табличную первообразную с исходным условием на радиканд или знаменатель.'
            ]),value
    raise Unsupported('No checked common phase and quadratic differential were found')


def positive_radical_product(task):
    x,raw,ctx,_=guarded_input(task,{'elementary_table_and_algebra','appropriate_integrand_transformation','table_and_rules'})
    if raw[0]!='div' or raw[2][0]!='sqrt':raise Unsupported('The original denominator must be a principal square root')
    def root_sum(node):
        return node[0] in ('q','sqrt') or node[0] in ('add','mul') and all(root_sum(e) for e in node[1:])
    if not root_sum(raw[1]):raise Unsupported('No separate factor with an unproved condition may be erased')
    P,D=m.rational_form(raw[1]);Q=raw[2][1]
    real_polynomial_coefficients(Q,x[1],ctx,4)
    if set(D)!={()} or len(P)!=2 or any(len(row)!=1 or row[0][0][0]!='sqrt' or row[0][1]!=1 for row in P):
        raise Unsupported('The numerator must contain exactly two first powers of original square roots')
    parts=[(row[0][0][1],w/D[()]) for row,w in P.items()]
    from verify import same_value
    if not same_value(m.mul(parts[0][0],parts[1][0]),Q):raise Unsupported('The radicand is not the product of the two original radicands')
    if len({a for a in learned_nodes(raw[1]) if isinstance(a,tuple) and a[0]=='sqrt'})!=2:
        raise Unsupported('A hidden radical term would have a separate real condition')
    # On the original domain A,B are nonnegative and AB>0, hence both positive.
    answer=ZERO
    for (A,_),(_,weight) in zip(parts,reversed(parts)):
        data=real_polynomial_coefficients(A,x[1],ctx,2)
        local=collect_kernel(('div',ONE,('sqrt',A)),stationary_quadratic_kernel(x,data,True,ctx),ctx)
        if 'representative' not in local:raise Unsupported('The two original roots need additional parameter branches')
        answer=m.add(answer,m.mul(q(weight),local['representative']))
    return dict(theorem='method.guarded_quadratic_differential',chart='positive_radical_product',radicands=[(z,q(w)) for z,w in parts],argument=[
        'Оба корня числителя требуют неотрицательных радикандов, а произведение под корнем знаменателя строго положительно. Значит, оба множителя положительны и произведение корней допустимо.',
        'Сократить положительные множители, сложить две первообразные и сохранить исходные компоненты.'
    ]),family(raw,answer)


def hyperbolic_square(task):
    x,raw,ctx,_=guarded_input(task,{'elementary_table_and_algebra','appropriate_integrand_transformation','table_and_rules'})
    if raw[0]!='pow' or raw[2]!=2:raise Unsupported('A hyperbolic square was required')
    T=raw[1]
    if T[0]=='tanh':angle=T[1]
    elif T[0]=='div' and T[1][0]=='cosh' and T[2]==('sinh',T[1][1]):angle=T[1][1]
    else:raise Unsupported('The square is not a hyperbolic tangent or cotangent')
    slope,_=affine(angle,x[1])
    if not m.nonzero(slope,ctx) or domain_conditions(angle):raise Unsupported('The phase must be real affine with nonzero slope')
    return dict(theorem='method.guarded_quadratic_differential',chart='hyperbolic_square',derivative_identity='D tanh or coth = 1−(tanh or coth)^2',
                rate=slope,argument=['Равенство cosh²−sinh²=1 и правило частного дают производную 1−T². Вычесть T, делённое на скорость фазы, из x. Полюсы coth сохраняются.']),family(raw,m.add(x,m.neg(m.div(T,slope))))


def rescaled_exponential_radical(task):
    x,raw,ctx,_=guarded_input(task,{'table_and_rules','appropriate_integrand_transformation','appropriate_substitution'})
    if raw[0]!='div' or raw[1]!=ONE or raw[2][0]!='sqrt':raise Unsupported('Expected a constant numerator over the exponential radical')
    E={a for a in learned_nodes(raw[2][1]) if isinstance(a,tuple) and a[0]=='exp'}
    if len(E)!=1:raise Unsupported('A single real exponential scale is required')
    E,=E;angle=E[1];rate,_=affine(angle,x[1]);v='_known_exp'
    if x[1]==v or not m.num(rate) or domain_conditions(angle):raise Unsupported('The exponential scale requires a real affine phase and a fresh binder')
    c=real_polynomial_coefficients(m.substitute(raw[2][1],{E:('v',v)}),v,ctx,1)
    if len(c)!=2 or any(m.sign(z,ctx)!=1 for z in c):raise Unsupported('The constant and exponential coefficients must be positive')
    coordinate=('exp',m.mul(q(-1,2),angle))
    result=collect_kernel(raw,[(cond,m.mul(m.div(q(-2),rate),H)) for cond,H in stationary_quadratic_kernel(coordinate,(c[1],ZERO,c[0]),True,ctx)],ctx)
    return dict(theorem='method.guarded_quadratic_differential',chart='rescaled_exponential_radical',coordinate=coordinate,
                dual_coefficients=c,argument=['Вынести строго положительный экспоненциальный множитель из корня. Производная обратного масштаба поглощает этот множитель и оставляет квадратный радиканд.']),result


def periodic_root_options(task):
    text=task.get('integrand','')
    allowed={'table_and_rules','appropriate_substitution','appropriate_integrand_transformation'}
    if (isinstance(text,str) and task.get('method_requirement','table_and_rules') in allowed and not task.get('parameters')
            and any(f in text for f in ('sqrt(','cbrt(')) and any(f in text for f in ('sin(','cos(','tan('))):
        return ('real_root_periodic_coordinate',)
    return ()


def real_root_periodic_coordinate(task,request):
    """Rationalize a trigonometric Laurent monomial without splitting signed radicals."""
    x,raw,ctx,_=input_data(task,{'table_and_rules','appropriate_substitution','appropriate_integrand_transformation'})
    if ctx['parameters'] or task.get('stated_conditions'):
        raise Unsupported('This coordinate needs a fixed affine phase on the original real domain')
    roots={z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0] in ('sqrt','cbrt')}
    if len(roots)!=1:raise Unsupported('A single original real square or cube root is required')
    radical,=roots;r=2 if radical[0]=='sqrt' else 3;angles=set();waves=set()
    def exponents(e,n=1,allow_root=False):
        if allow_root and e==radical:return Fraction(1),0,0,n
        if e[0]=='pow' and type(e[2]) is int and abs(e[2]*n)<=24 and e[2]:
            return exponents(e[1],n*e[2],allow_root)
        if e[0] in ('mul','div'):
            a,b,c,j=exponents(e[1],n,allow_root)
            d,h,k,i=exponents(e[2],n if e[0]=='mul' else -n,allow_root)
            return a*d,b+h,c+k,j+i
        powers={'sin':(1,0),'cos':(0,1),'tan':(1,-1)}
        if e[0] in powers:
            angles.add(e[1]);waves.add(e[0]);p,q_=powers[e[0]]
            return Fraction(1),p*n,q_*n,0
        a=m.num(e)
        if not a:raise Unsupported('Unexpected raw factor, extra pole or zero scalar in the trigonometric monomial')
        return a**n,0,0,0
    factor,p,q_,j=exponents(raw,allow_root=True);a,s,c,_=exponents(radical[1])
    if abs(j)!=1 or a<=0 or len(angles)!=1:
        raise Unsupported('A positive radical scale and one original phase are needed')
    phase,=angles;rate,offset=affine(phase,x[1]);k=m.num(rate)
    if not k or not m.constant_defined(offset,ctx) or domain_conditions(phase):
        raise Unsupported('The original phase must be globally real and affine with nonzero rate')
    a_root=m.num(m.simplify((radical[0],q(a))))
    if not a_root:raise Unsupported('A rational positive scale is required for the rational kernel')
    symbol=kernel_symbol(task);z=('v',symbol)
    coords=[]
    if r==3 or s%2:
        # sqrt(C^(s+c)) is a power of C only when that power is even.
        if (s+c)%(2*r if r==2 else r)==0 and ('tan' in waves or j<0 and s>0 and c>0):
            net=p+q_+j*((s+c)//r)
            if net%2==0:coords.append(('tan',p,s,-net//2-1,1,k))
        if 'tan' not in waves:
            if not c and (q_-1)%2==0:coords.append(('sin',p,s,(q_-1)//2,-1,k))
            if not s and (p-1)%2==0 and (r==3 or c%2):coords.append(('cos',q_,c,(p-1)//2,-1,-k))
    if not coords:raise Unsupported('Real signs prevent division into a rational periodic chart')
    for wave,weight,radical_degree,unit_degree,unit_sign,slope in coords:
        power=r*weight+j*radical_degree+r-1
        constant=q(factor*r*a_root**j/slope)
        from math import gcd
        descent=gcd(power+1,2*r)
        kernel=m.mul(m.div(constant,q(descent)),m.mul(m.power(z,(power+1)//descent-1),
                     m.power(m.add(ONE,m.mul(q(unit_sign),m.power(z,2*r//descent))),unit_degree)))
        coordinate=m.power((radical[0],(wave,phase)),descent)
        H=integrate_child(request,kernel,symbol)
        F=m.substitute(H,{z:coordinate})
        return dict(theorem='method.real_root_periodic_coordinate',chart='real_root_periodic_coordinate',coordinate=coordinate,
                    kernel=kernel,root_index=r,angular_wave=wave,phase_rate=q(slope),source_exponents=(p,q_,s,c,j),argument=[
            'Из исходных степеней выделить одну круговую координату. Проверить знак перед вынесением степени косинуса из квадратного корня. Кубический корень сохраняет обе знаковые ветви.',
            'Возвести новую координату в степень корня и умножить на точный дифференциал. Степени полученной функции целые, поэтому подзадача рациональна.',
            'Сохранить все исходные полюсы. Если корень равен нулю в допустимой точке, производная составной первообразной продолжается по непрерывности исходного ядра.'
        ]),family(raw,F)
    raise Unsupported('No checked trigonometric root coordinate')


def rational_division_split(raw,variable):
    """Divide the rational cofactor of one nonrational kernel into polynomial and proper parts."""
    def factors(e,n=1):
        if e[0]=='mul':return factors(e[1],n)+factors(e[2],n)
        if e[0]=='div':return factors(e[1],n)+factors(e[2],-n)
        if e[0]=='pow' and type(e[2]) is int and e[2]:return factors(e[1],n*e[2])
        return [(e,n)]
    P=(Fraction(1),);D=(Fraction(1),);kernel=ONE;found=False
    for base,n in factors(raw):
        try:a,b=rf(base,variable)
        except (NotRational,Undefined):
            found=True;kernel=m.mul(kernel,m.power(base,n) if n>0 else m.div(ONE,m.power(base,-n)));continue
        if n<0:a,b=b,a
        if not any(a) or not any(b):raise Unsupported('A zero rational factor is not a division kernel')
        for _ in range(abs(n)):P=pm(P,a);D=pm(D,b)
    if not found or len(trim(D))<2:raise Unsupported('A nonrational kernel with a rational denominator is required')
    g=pgcd(P,D)
    if len(trim(g))>1:raise Unsupported('Cancelling a common factor would remove an original pole')
    quotient,rest=pdiv(P,D)
    if not any(quotient) or not any(rest):raise Unsupported('The rational cofactor has no separate polynomial and proper parts')
    x=('v',variable)
    whole=m.mul(polynomial_expression(tuple(quotient),variable),kernel)
    proper=m.mul(m.div(polynomial_expression(tuple(rest),variable),polynomial_expression(tuple(D),variable)),kernel)
    return [whole,proper],dict(identity='N=Q*D+R with deg R<deg D',quotient=tuple(map(q,quotient)),remainder=tuple(map(q,rest)),
                               denominator=tuple(map(q,D)),kernel=kernel)


def rational_division_options(task):
    text=task.get('integrand','')
    if (isinstance(text,str) and task.get('method_requirement','table_and_rules') in ('table_and_rules','integration_by_parts')
            and not task.get('parameters') and '/' in text and any(f in text for f in ('atan(','ln(','asin(','acos(','acot('))):
        try:
            v,raw=fixed_integral_source(task);rational_division_split(raw,v)
        except (Unsupported,NotRational,Undefined,ValueError,KeyError,TypeError):return ()
        return ('rational_factor_division',)
    return ()


def rational_factor_division(task,request):
    """Integrate a nonrational kernel times an improper rational cofactor by exact polynomial division."""
    from verify import same_value
    v,raw=fixed_integral_source(task)
    terms,evidence=rational_division_split(raw,v)
    for condition in domain_conditions(m.add(terms[0],terms[1])):
        if not any(canonical(condition)==canonical(c) for c in domain_conditions(raw)):
            raise Unsupported('The divided terms would need a restriction absent from the original integrand')
    value=ZERO;children=[]
    for term in terms:
        primitive=integrate_child(request,term,v);value=m.add(value,primitive)
        children.append(dict(integrand=term,primitive=primitive))
    return dict(theorem='method.rational_factor_division',chart='rational_factor_division',decomposition=evidence,terms=children,argument=[
        'Разделить числитель рационального множителя на знаменатель с остатком. Нерациональное ядро и все исходные полюсы сохраняются.',
        'Интеграл равен сумме интегралов целой и правильной частей: '+' + '.join(source(t) for t in terms)+'.',
        'Производная суммы проверяется на исходной области, постоянная своя на каждой её компоненте.',
    ]),family(raw,value)


def parameter_linear_terms(task):
    """Write the integrand as a sum of fixed parameters times parameter-free kernels with the original denominator."""
    v,params,ctx,raw=integral_source(task)
    names={p['symbol'] if isinstance(p,dict) else p for p in task.get('parameters',[])}
    if not names or task.get('stated_conditions'):raise Unsupported('Free real parameters without side conditions are required')
    def parameter(atom):return atom[0]=='s' and atom[1] in names
    def inside(e):return isinstance(e,tuple) and (parameter(e) or any(inside(z) for z in e[1:]))
    def transcendental_parameter(e):
        if not isinstance(e,tuple) or e[0] in ('q','v','s'):return False
        if e[0] in ('add','mul','div'):return any(transcendental_parameter(z) for z in e[1:])
        if e[0]=='pow':return transcendental_parameter(e[1])
        return inside(e)
    if transcendental_parameter(raw):raise Unsupported('A parameter inside a function or power needs its own branches')
    numerator,denominator=m.rational_form(raw)
    if not numerator:raise Unsupported('A vanishing integrand is not separated by parameters')
    if any(inside(atom) for mon in denominator for atom,_ in mon):raise Unsupported('A parameter in the denominator needs its own branches')
    groups={}
    for mon,c in numerator.items():
        own=[(atom,n) for atom,n in mon if parameter(atom)];rest=tuple((atom,n) for atom,n in mon if not parameter(atom))
        if len(own)>1 or own and own[0][1]!=1 or any(inside(atom) for atom,_ in rest):
            raise Unsupported('The integrand is not linear in separate parameters')
        groups.setdefault(own[0][0] if own else None,{})[rest]=c
    if len(groups)<2 and None in groups:raise Unsupported('No parameter coefficient to separate')
    bottom=m.poly_expr(denominator);terms=[]
    for coefficient,part in sorted(groups.items(),key=lambda z:canonical(z[0])):
        kernel=m.poly_expr(part);kernel=kernel if bottom==ONE else ('div',kernel,bottom)
        terms.append((coefficient,kernel))
    allowed={canonical(c) for c in domain_conditions(raw)}
    for _,kernel in terms:
        if any(canonical(c) not in allowed for c in domain_conditions(kernel)):
            raise Unsupported('A separated kernel would need a restriction absent from the original integrand')
    return v,raw,terms


def parameter_linear_options(task):
    if task.get('parameters') and task.get('method_requirement','table_and_rules') in ('table_and_rules','integration_by_parts'):
        try:parameter_linear_terms(task)
        except (Unsupported,NotRational,Undefined,ResourceBound,ValueError,KeyError,TypeError,ZeroDivisionError):return ()
        return ('parameter_linear_split',)
    return ()


def parameter_linear_split(task,request):
    v,raw,terms=parameter_linear_terms(task)
    value=ZERO;children=[]
    for coefficient,kernel in terms:
        primitive=integrate_child(request,kernel,v)
        value=m.add(value,primitive if coefficient is None else m.mul(coefficient,primitive))
        children.append(dict(coefficient=coefficient,integrand=kernel,primitive=primitive))
    return dict(theorem='method.rational_factor_division',chart='parameter_linear_split',terms=children,argument=[
        'Подынтегральная функция линейна по фиксированным параметрам, а знаменатель от них не зависит. Выделить ядро при каждом параметре.',
        'Найти первообразную каждого ядра без параметров и сложить с исходными коэффициентами.',
        'Производная суммы проверяется на исходной области при любых значениях параметров.',
    ]),family(raw,value)
