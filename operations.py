"""Finite exact operations used by declared general-analysis rules.

A jet is P(t)+o(t^r), t->0+, or an exact expression if r='exact'.
Operations preserve the remainder order; an unresolved remainder cannot
be silently treated as zero. Mathematical schemas live in the active common-library manifest.
"""
from fractions import Fraction as F
from math import factorial, comb, ceil
from pathlib import Path
import hashlib

from model import freeze, q, ZERO, ONE, canonical, Unsupported
from polynomial import ResourceBound, NotRational, Undefined, rf, valuation
import expressions as m
import intervals as real_intervals


class Unavailable(Exception): pass

WINDOW_SIDES={'prefix_inf':'prefix','prefix_sup':'prefix','suffix_inf':'suffix','suffix_sup':'suffix'}

def finite_endpoint_symbol(s):
    return (isinstance(s,str) and s.isascii() and s.isidentifier() and s[0].isalpha()
            and s.lower() not in ('inf','infty','infinity','nan'))

def closed_function_interval(ctx):
    ends=ctx.get('interval_endpoints')
    if (ctx.get('domain')!='function_continuity' or ctx.get('source_domain')!='closed_real_interval'
            or not isinstance(ends,(list,tuple)) or len(ends)!=2):
        return False
    # A named segment declares two ordered finite real endpoints. Numeric bounds are checked directly.
    return (all(finite_endpoint_symbol(s) for s in ends)
            or all(type(s) is int for s in ends) and ends[0]<=ends[1])

CONTINUOUS_FUNCTIONS=frozenset({'sin','cos','tan','cot','sqrt','cbrt','asin','acos',
    'atan','acot','sec','csc','ln','exp','sinh','cosh','tanh','abs'})


def version():
    h=hashlib.sha256();base=Path(__file__).parent
    for name in ('model.py','polynomial.py','expressions.py','operations.py','library.py','verify.py','search.py','tasks.py','intervals.py','integrals.py','radical_primitives.py','quadrature.py','planar_integrals.py','graphs.py','plane_domains.py','level_sets.py','uniform.py','finite_sums.py','cartesian_fields.py','ray_proofs.py','scalar_proofs.py','plane_geometry.py','limit_proofs.py','real_functions.py','derivative_proofs.py','ordinary_series.py','scalar_families.py','elementary_proofs.py','surface_fields.py','source_primitives.py','geometric_domains.py'):
        h.update(name.encode());h.update((base/name).read_bytes())
    return h.hexdigest()


def unpack(j):
    if j[0]!='jet':raise Unsupported('Ожидалось локальное разложение')
    return {m.num(p):m.simplify(c) for p,c in j[1]},None if j[2]=='exact' else m.num(j[2])


GERM_GOALS=('finite_expansion','leading_asymptotic_term')


def germ_conclusion(j,ctx):
    """Project a proven one-sided germ to the requested result in the signed source coordinate."""
    if not ctx.get('leading_asymptotic_term'):return expansion_coefficients(j,ctx)
    terms,remainder=unpack(freeze(j))
    if not terms:return ('zero_germ',) if remainder is None else None
    p=min(terms);c=terms[p]
    if remainder is not None and remainder<p or not m.constant_defined(c,ctx) or not m.nonzero(c,ctx):return None
    if ctx['evaluation_side']=='left' or ctx['point']=='-inf':
        if p.denominator%2==0:return None
        if p.numerator%2:c=m.neg(c)
    return ('leading_monomial',q(p),c)


def expansion_coefficients(j,ctx):
    """Coefficients in h=x-a (or h=1/x at infinity) with a Peano remainder."""
    terms,remainder=unpack(freeze(j));degree=ctx['expansion_degree']
    if remainder is not None and remainder<degree:return None
    if any(p<0 or p.denominator!=1 for p in terms if p<=degree):return None
    values=tuple(terms.get(k,ZERO) for k in range(degree+1))
    if not all(m.constant_defined(c,ctx) for c in values):return None
    negative=ctx['evaluation_side']=='left' or ctx['point']=='-inf'
    return tuple(m.neg(c) if k%2 and negative else c for k,c in enumerate(values))


def rmin(a,b):return b if a is None else a if b is None else min(a,b)
def radd(a,b):return None if a is None or b is None else a+b


def jet(terms, remainder=None, order=6):
    terms={F(p):m.simplify(c) for p,c in terms.items()}
    terms={p:c for p,c in terms.items() if c!=ZERO}
    bound=rmin(F(order),remainder)
    if any(p>bound for p in terms):
        terms={p:c for p,c in terms.items() if p<=bound};remainder=rmin(remainder,bound)
    if len(terms)>64:raise ResourceBound('Слишком много членов локального разложения')
    return ('jet',tuple((q(p),c) for p,c in sorted(terms.items())), 'exact' if remainder is None else q(remainder))


def jc(c,ctx):return jet({F(0):c},order=ctx['order'])


def lower(j):
    terms,r=unpack(j)
    return min(terms) if terms else r


def jadd(a,b,ctx):
    aa,ra=unpack(a);bb,rb=unpack(b)
    for p,c in bb.items():aa[p]=m.add(aa.get(p,ZERO),c)
    return jet(aa,rmin(ra,rb),ctx['order'])


def jscale(a,c,ctx):
    aa,ra=unpack(a)
    c=m.simplify(c)
    if c==ZERO:return jc(ZERO,ctx)
    return jet({p:m.mul(v,c) for p,v in aa.items()},ra,ctx['order'])


def jshift(a,p,ctx):
    aa,ra=unpack(a)
    return jet({k+p:c for k,c in aa.items()},None if ra is None else ra+p,ctx['order'])


def jmul(a,b,ctx):
    aa,ra=unpack(a);bb,rb=unpack(b)
    if not aa and ra is None or not bb and rb is None:return jc(ZERO,ctx)
    terms={}
    for p,c in aa.items():
        for k,d in bb.items():terms[p+k]=m.add(terms.get(p+k,ZERO),m.mul(c,d))
    r=rmin(radd(ra,lower(b)),radd(rb,lower(a)))
    return jet(terms,r,ctx['order'])


def leading(j):
    terms,r=unpack(j)
    if not terms:raise Unavailable()
    p=min(terms)
    if r is not None and r<=p:  # o(t^p) still permits a coefficient at p.
        if r<p:raise Unavailable()
    return p,terms[p]


def scalar_power(c,alpha):
    if alpha.denominator==1:return m.power(c,alpha.numerator)
    if alpha.denominator not in (2,3):raise Unavailable()
    root=m.simplify(('sqrt' if alpha.denominator==2 else 'cbrt',c))
    return m.power(root,alpha.numerator)


def jpower(a,alpha,ctx):
    if alpha.denominator==1 and alpha>=0:
        result=jc(ONE,ctx)
        for _ in range(alpha.numerator):result=jmul(result,a,ctx)
        return result
    p,c=leading(a)
    if not m.nonzero(c,ctx):raise Unavailable()
    if alpha.denominator%2==0 and m.sign(c,ctx)!=1:raise Unavailable()
    terms,r=unpack(a)
    base=scalar_power(c,alpha)
    if len(terms)==1 and r is None:return jet({p*alpha:base},order=ctx['order'])
    normalized=jshift(jscale(a,m.div(ONE,c),ctx),-p,ctx)
    delta=jadd(normalized,jc(q(-1),ctx),ctx)
    nu=lower(delta)
    if nu is None:return jet({p*alpha:base},order=ctx['order'])
    if nu<=0:raise Unavailable()
    n=max(0,ceil((F(ctx['order'])-p*alpha)/nu))
    if n>24:raise ResourceBound('Порядок биномиального разложения превышает 24')
    term=jc(ONE,ctx);result=term;coef=F(1)
    for k in range(1,n+1):
        term=jmul(term,delta,ctx);coef*= (alpha-k+1)/k
        result=jadd(result,jscale(term,q(coef),ctx),ctx)
    result=jshift(jscale(result,base,ctx),p*alpha,ctx)
    tt,rr=unpack(result)
    error=rmin(F(ctx['order']),None if r is None else r+(alpha-1)*p)
    return jet(tt,rmin(rr,error),ctx['order'])


def finite_center(a):
    terms,r=unpack(a)
    if any(p<0 for p in terms) or r is not None and r<=0:raise Unavailable()
    return terms.get(F(0),ZERO)


def analytic(a,kind,ctx):
    center=finite_center(a)
    if kind=='asin':
        interior=m.add(ONE,m.neg(m.power(center,2)))
        if m.sign(interior,ctx)!=1:raise Unavailable()
    if kind=='ln' and m.sign(center,ctx)!=1:raise Unavailable()
    terms,r=unpack(a);terms.pop(F(0),None)
    delta=jet(terms,r,ctx['order'])
    nu=lower(delta)
    if nu is None:return jc(m.simplify((kind,center)),ctx)
    if nu<=0:raise Unavailable()
    n=max(1,ceil(F(ctx['order'])/nu))
    if n>24:raise ResourceBound('Порядок локального разложения превышает 24')
    s=m.simplify(('sin',center));c=m.simplify(('cos',center))
    sh=m.simplify(('sinh',center));ch=m.simplify(('cosh',center))
    exponential=m.simplify(('exp',center))
    atan_coefficients=[]
    if kind=='atan':
        denominator=m.add(ONE,m.power(center,2))
        a=m.div(m.mul(q(2),center),denominator);b=m.div(ONE,denominator)
        for k in range(n):
            value=b if k==0 else m.neg(m.mul(a,atan_coefficients[-1]))
            if k>=2:value=m.add(value,m.neg(m.mul(b,atan_coefficients[-2])))
            atan_coefficients.append(value)
    if kind=='asin' and center!=ZERO:
        # Taylor coefficients in a formal increment u. Its degree n can be
        # larger than the output order when the actual increment is Puiseux.
        formal={**ctx,'order':n}
        density=jet({0:interior,1:m.mul(q(-2),center),2:q(-1)},order=n)
        asin_density,_=unpack(jpower(density,F(-1,2),formal))
    result=jc(ZERO,ctx);term=jc(ONE,ctx)
    for k in range(n+1):
        if kind in ('sin','cos'):
            cycle=(s,c,m.neg(s),m.neg(c)) if kind=='sin' else (c,m.neg(s),m.neg(c),s)
            coefficient=m.mul(q(F(1,factorial(k))),cycle[k%4])
        elif kind=='exp':coefficient=m.mul(exponential,q(F(1,factorial(k))))
        elif kind in ('sinh','cosh'):
            cycle=(sh,ch) if kind=='sinh' else (ch,sh)
            coefficient=m.mul(cycle[k%2],q(F(1,factorial(k))))
        elif kind=='ln':
            coefficient=m.simplify(('ln',center)) if k==0 else m.div(q(F((-1)**(k+1),k)),m.power(center,k))
        elif kind=='atan':
            coefficient=m.simplify(('atan',center)) if k==0 else m.mul(q(F(1,k)),atan_coefficients[k-1])
        elif kind=='asin' and center!=ZERO:
            coefficient=m.simplify(('asin',center)) if k==0 else m.mul(q(F(1,k)),asin_density.get(F(k-1),ZERO))
        elif k%2==0:coefficient=ZERO
        else:
            j=(k-1)//2;coefficient=q(F(comb(2*j,j),4**j*(2*j+1)))
        result=jadd(result,jscale(term,coefficient,ctx),ctx)
        if k<n:term=jmul(term,delta,ctx)
    tt,rr=unpack(result)
    return jet(tt,rmin(rr,rmin(F(ctx['order']),r)),ctx['order'])


def jet_limit(a,ctx):
    terms,r=unpack(a)
    if terms:
        p=min(terms);c=terms[p]
        if p<0:
            if r is not None and r<p:raise Unavailable()
            sign=m.sign(c,ctx)
            if sign in (-1,1):return '+inf' if sign==1 else '-inf'
            raise Unavailable()
    if r is not None and r<0:raise Unavailable()
    return m.simplify(terms.get(F(0),ZERO))


def near_sign(a,ctx):
    terms,r=unpack(a)
    if not terms:return 0 if r is None else None
    p,c=leading(a)
    return m.sign(c,ctx)


def map_subtrees(e, transform):
    outputs=[]
    for changed,guards in transform(e):
        if changed!=e:outputs.append((changed,guards))
    for i,c in enumerate(e[1:],1):
        if isinstance(c,tuple):
            for changed,guards in map_subtrees(c,transform):
                out=list(e);out[i]=changed;outputs.append((tuple(out),guards))
                if len(outputs)>=24:return outputs
    return outputs


def negative_term(e):
    return e[2] if e[0]=='mul' and e[1]==q(-1) else None


def radical_candidates(e,kind):
    def transform(node):
        if node[0]!='add':return []
        a,b=node[1:]
        if a[0]!=kind:
            if b[0]==kind:a,b=b,a
            else:
                nb=negative_term(b)
                if a[0]!=kind or nb is None:return []
        if kind=='sqrt':
            v=negative_term(b)
            if v is None:return []
            denominator=('add',a,v)
            numerator=('add',a[1],('mul',q(-1),('pow',v,2)))
        else:
            denominator=('add',('add',('pow',a,2),('mul',q(-1),('mul',a,b))),('pow',b,2))
            numerator=('add',a[1],('pow',b,3))
        return [(('div',numerator,denominator),(denominator,))]
    return map_subtrees(e,transform)


def trig_candidates(e,kind):
    def transform(node):
        op=node[0]
        if kind=='quotients' and op in ('tan','cot'):
            s,c=('sin',node[1]),('cos',node[1])
            return [(('div',s,c),(c,))] if op=='tan' else [(('div',c,s),(s,))]
        if kind in ('sin_difference','cos_difference') and op=='add':
            a=node[1];b=negative_term(node[2]);fn='sin' if kind=='sin_difference' else 'cos'
            if b is None or a[0]!=fn or b[0]!=fn:return []
            mean=('div',('add',a[1],b[1]),q(2))
            half=('div',('add',a[1],('mul',q(-1),b[1])),q(2))
            value=('mul',('mul',q(2 if fn=='sin' else -2),('cos' if fn=='sin' else 'sin',mean)),('sin',half))
            return [(value,())]
        if kind=='half_angle' and op=='add' and node[1]==ONE:
            b=negative_term(node[2])
            if b is not None and b[0]=='cos':return [(('mul',q(2),('pow',('sin',('div',b[1],q(2))),2)),())]
        if kind=='abs_product' and op=='abs' and node[1][0] in ('mul','div'):
            tag,a,b=node[1]
            return [((tag,('abs',a),('abs',b)),(b,) if tag=='div' else ())]
        if kind=='tan_minus_sin' and op=='add':
            a=node[1];b=negative_term(node[2])
            if b is not None and a[0]=='tan' and b[0]=='sin' and a[1]==b[1]:
                f=a[1];c=('cos',f)
                return [(('div',('mul',('sin',f),('add',ONE,('mul',q(-1),c))),c),(c,))]
        return []
    return map_subtrees(e,transform)


def normalize_ratio_candidates(e):
    def transform(node):
        if node[0]!='div':return []
        a,b=node[1:];out=[]
        if a[0] in ('sin','asin','atan') and a[1]!=b:
            f=a[1]
            out.append((('mul',('div',f,b),('div',a,f)),(f,)))
        if b[0]=='sin' and b[1]!=a:
            f=b[1]
            out.append((('div',('div',a,f),('div',b,f)),(f,)))
        return out
    return map_subtrees(e,transform)


def direct_sum_allowed(e):
    if e[0]!='add':return True
    a,b=e[1:];negative=negative_term(b)
    if a[0]=='sqrt' and negative is not None:return False
    if a[0]=='cbrt' or b[0]=='cbrt':return False
    if negative is not None:
        if a[0] in ('sin','cos') and negative[0]==a[0]:return False
        if a==ONE and negative[0]=='cos':return False
        if a[0]=='tan' and negative[0]=='sin' and a[1]==negative[1]:return False
    return True


def constant_domain(e,ctx):
    try:return m.constant_defined(e,ctx)
    except (ZeroDivisionError,Unavailable):return False


def slow_regular(a,ctx):
    """Convert ordinary powers of t into the scale u=-1/ln(t), u->0+."""
    terms,r=unpack(a)
    if any(p<0 for p in terms) or r is not None and r<=0:raise Unavailable()
    c=terms.get(F(0),ZERO)
    if all(p==0 for p in terms) and r is None:return jc(c,ctx)
    return jet({F(0):c},F(ctx['order']),ctx['order'])


def slow_log(a,ctx):
    p,c=leading(a);terms,r=unpack(a)
    if m.sign(c,ctx)!=1:raise Unavailable()
    exact=len(terms)==1 and r is None
    if not exact and r is not None and r<=p:raise Unavailable()
    # All retained higher exponents and the input remainder have a strictly
    # positive gap from p. Their logarithmic correction is flat in u.
    return jet({F(-1):q(-p),F(0):m.simplify(('ln',c))},None if exact else F(ctx['order']),ctx['order'])


def elementary_candidates(e,kind):
    def change(node):
        tag=node[0]
        if kind=='power' and tag=='rpow':return [(('exp',('mul',node[2],('ln',node[1]))),())]
        if kind=='hyperbolic' and tag in ('sinh','cosh'):
            u=node[1];positive=('exp',u);negative=('exp',('mul',q(-1),u))
            numerator=('add',positive,negative if tag=='cosh' else ('mul',q(-1),negative))
            return [(('div',numerator,q(2)),())]
        if kind=='hyperbolic' and tag=='tanh':return [(('div',('sinh',node[1]),('cosh',node[1])),())]
        if (kind,tag) in (('secant','sec'),('cosecant','csc')):
            return [(('div',ONE,('cos' if tag=='sec' else 'sin',node[1])),())]
        if kind=='acot' and tag=='acot':return [(('add',m.mul(q(1,2),m.PI),('mul',q(-1),('atan',node[1]))),())]
        if kind=='acos' and tag=='acos':return [(('add',m.mul(q(1,2),m.PI),('mul',q(-1),('asin',node[1]))),())]
        return []
    return map_subtrees(e,change)


def exponential_phases(poly):
    return sorted({a[1] for mon in poly for a,n in mon if a[0]=='exp'},key=canonical)[:6]


def scale_polynomial(poly,phase):
    result=ZERO
    for mon,c in poly.items():
        exponent=m.neg(phase);rest={}
        for atom,n in mon:
            if atom[0]=='exp':exponent=m.add(exponent,m.mul(q(n),atom[1]))
            else:rest[atom]=n
        term=m.poly_expr({tuple(sorted(rest.items(),key=lambda item:canonical(item[0]))):c})
        result=m.add(result,m.mul(term,m.simplify(('exp',exponent))))
    return result


def exponential_scale_candidates(e,logarithm=False):
    def change(node):
        if logarithm and node[0]!='ln' or not logarithm and node[0]!='div':return []
        p,d=m.rational_form(node[1] if logarithm else node)
        phases=exponential_phases(p if logarithm else d)
        outputs=[]
        for phase in phases:
            if phase==ZERO:continue
            if logarithm:
                scaled=m.div(scale_polynomial(p,phase),m.poly_expr(d))
                result=('add',phase,('ln',scaled))
            else:result=('div',scale_polynomial(p,phase),scale_polynomial(d,phase))
            if result!=node:outputs.append((result,(phase,)))
        return outputs
    # map_subtrees carries the required growing phase as its second field;
    # unlike ordinary rewrites this phase is proved to tend to +infinity.
    return [(guard[0],changed) for changed,guard in map_subtrees(e,change)]


def exponential_factor_candidates(e):
    p,d=m.rational_form(e)
    return [(phase,('div',scale_polynomial(p,phase),m.poly_expr(d)))
            for phase in exponential_phases(p) if phase!=ZERO]


def product_splits(e):
    factors=[]
    def collect(node):
        if node[0]=='mul':collect(node[1]);collect(node[2])
        else:factors.append(node)
    collect(e)
    for i,factor in enumerate(factors):
        if not m.variable_in(factor):continue
        rest=ONE
        for j,other in enumerate(factors):
            if i!=j:rest=('mul',rest,other)
        yield factor,m.simplify(rest)


def split_exp_factor(e,variable):
    """Construct a,u with e=a*exp(-u); domain is a separate rule premise."""
    def contains(node):return node[0]=='exp' or any(contains(c) for c in node[1:] if isinstance(c,tuple))
    def split(node):
        if node[0]=='exp':return ONE,node[1]
        if not contains(node):
            rf(node,variable)
            return node,None
        if node[0] not in ('mul','div'):raise NotRational()
        a,v=split(node[1]);b,w=split(node[2])
        if v is not None and w is not None:raise NotRational()
        return (node[0],a,b),v if v is not None else w if node[0]=='mul' else m.neg(w)
    if not contains(e):return []
    a,v=split(e)
    return [(m.simplify(a),m.neg(v))]


def exponential_orders(a,u,variable):
    """Choose a finite estimate order; the resulting bound still needs proof."""
    try:
        p,d=rf(a,variable);r,s=rf(u,variable)
        if p==(F(0),):return [(1,)]
        if r==(F(0),):return []
        ka=valuation(p)-valuation(d);ku=valuation(r)-valuation(s)
        if ku<0:
            n=max(1,(-ka)//(-ku)+1)
            if n>256:raise ResourceBound('Порядок оценки превышает 256')
            return [(n,)]
    except NotRational:pass
    return [(1,),(2,),(4,)]


def expression_children(e):
    """Argument positions in the binder-free real-expression language (zero-based)."""
    if e[0] in m.FUNCTIONS or e[0] in ('add','mul','div','rpow','pow'):
        return [(i,child) for i,child in enumerate(e[1:]) if isinstance(child,tuple)]
    return []


def expression_positions(e,path=()):
    yield path,e
    for i,child in expression_children(e):
        yield from expression_positions(child,(*path,i))


def expression_replace(e,path,value):
    if not path:return value
    index=path[0]
    if type(index) is not int or index<0:raise Unavailable
    for i,child in expression_children(e):
        if i==index:
            return (*e[:i+1],expression_replace(child,path[1:],value),*e[i+2:])
    raise Unavailable


def formal_polynomial_form(e):
    """Collect rational coefficients without using identities of the opaque expressions."""
    if e[0] not in ('add','mul','div','pow'):
        return []
    atoms={}

    def encode(t):
        op=t[0]
        if op=='q':
            return t
        if op in ('add','mul') or op=='div' and t[2][0]=='q' and t[2]!=ZERO:
            return (op,encode(t[1]),encode(t[2]))
        if op=='pow' and t[2]>=0:
            return (op,encode(t[1]),t[2])
        atom=('formal_atom',t)
        atoms[atom]=t
        return atom

    numerator,denominator=m.rational_form(encode(e))
    if denominator!={():F(1)}:
        return []
    result=m.substitute(m.poly_expr(numerator),atoms)
    return [(result,)] if result!=e else []


def chord_step(name,args,ctx):
    """Finite endpoint and phase facts; inference via concavity is declared in the library."""
    I=args[-1]
    if ctx.get('domain')!='ordered_interval' or freeze(ctx.get('comparison_interval'))!=I:return []
    _,left,right,_,_=I
    if isinstance(right,str) or isinstance(left,str):return []
    if name=='chord_endpoints':return [(left,right)] if m.sign(m.add(right,m.neg(left)),ctx)==1 else []
    expr=args[0];x=('v',ctx['variable'])
    if name=='chord_right_continuity':
        # The admitted elementary operations are continuous relative to their real domains.
        # Continuity from within the interval also needs definedness there (a distinct premise).
        def continuous_form(e):
            return e[0] in ('q','pi','v') or (e[0] in m.FUNCTIONS|{'add','mul','div','pow'} and
                   all(continuous_form(c) for c in e[1:] if isinstance(c,tuple)))
        return [()] if continuous_form(expr) and m.constant_defined(m.substitute(expr,{x:right}),ctx) else []
    if name!='chord_trig_half_period' or args[1] not in ('>','>='):return []
    scale=q(1)
    if expr[0]=='mul':
        scale,expr=expr[1:]
        if m.variable_in(scale):expr,scale=scale,expr
    sign=m.sign(scale,ctx)
    if sign not in (-1,1) or m.variable_in(scale) or not m.constant_defined(scale,ctx) or expr[0] not in ('sin','cos'):return []
    angle=expr[1]
    def affine(e):
        if not m.variable_in(e):return m.constant_defined(e,ctx)
        if e==x:return True
        if e[0]=='add':return affine(e[1]) and affine(e[2])
        if e[0]=='mul':return not (m.variable_in(e[1]) and m.variable_in(e[2])) and affine(e[1]) and affine(e[2])
        if e[0]=='div':return not m.variable_in(e[2]) and affine(e[1]) and affine(e[2]) and m.nonzero(e[2],ctx)
        return False
    if not affine(angle):return []
    endpoints=[m.pi_multiple(m.simplify(m.substitute(angle,{x:z}))) for z in (left,right)]
    if any(z is None for z in endpoints) or endpoints[0]==endpoints[1]:return []
    shift=(F(1,2) if expr[0]=='cos' else 0)+(1 if sign<0 else 0)
    low,high=sorted(z+shift for z in endpoints)
    return [()] if high<=2*(low//2)+1 else []


def compute(name,args,ctx):
    args=freeze(args)
    try:
        if name.startswith('chord_'):return chord_step(name,args,ctx)
        if name.startswith('interval_') and ctx.get('domain')=='ordered_interval':
            from ray_proofs import primitive
            return primitive(name,args,ctx)
        if name=='cartesian_component_form':
            from cartesian_fields import component_form
            return [(component_form(args[0],ctx),)] if ctx.get('domain')=='cartesian_field_identity' and args[0] in ('left','right') else []
        if name.startswith('sum_') or name=='polynomial_normal_form':
            from finite_sums import calculate
            return calculate(name,args,ctx)
        if name=='formal_polynomial_form':return formal_polynomial_form(args[0])
        if name=='expression_positions':return list(expression_positions(args[0]))
        if name=='corresponding_arguments':
            a,b=args
            if len(a)!=len(b) or a[0]!=b[0]:return []
            left,right=dict(expression_children(a)),dict(expression_children(b))
            if not left or left.keys()!=right.keys():return []
            if any(x!=y for i,(x,y) in enumerate(zip(a[1:],b[1:])) if i not in left):return []
            return [tuple(value for i in left for value in (left[i],right[i]))]
        if name=='expression_replace':
            e,path,value=args
            if not isinstance(path,tuple):return []
            return [(expression_replace(e,path,value),)]
        if name=='pointwise_guard':
            if ctx.get('domain') not in ('pointwise_real','real_equality') or ctx.get('point_symbol') not in ctx['parameters']:return []
            relation,e=args;at=m.substitute(e,{('v',ctx['variable']):('s',ctx['point_symbol'])})
            if not m.constant_defined(at,ctx):return []
            return [()] if relation=='defined' or relation=='nonzero' and m.nonzero(at,ctx) or relation=='positive' and m.sign(at,ctx)==1 else []
        if name=='polynomial_difference_quotient':
            numerator,denominator=args;t=('v',ctx['variable'])
            if denominator not in (t,('mul',q(-1),t)):return []
            def degree(e):
                if not m.variable_in(e):return 0 if m.constant_defined(e,ctx) else 99
                if e==t:return 1
                if e[0]=='add':return max(degree(e[1]),degree(e[2]))
                if e[0]=='mul':return degree(e[1])+degree(e[2])
                if e[0]=='pow' and 1<=e[2]<=8:return degree(e[1])*e[2]
                if e[0]=='div' and not m.variable_in(e[2]) and m.nonzero(e[2],ctx):return degree(e[1])
                return 99
            if degree(numerator)>8:return []
            reduced=m.simplify(('div',numerator,denominator))
            _,bottom=m.rational_form(reduced)
            if any(m.variable_in(atom) for monomial in bottom for atom,power in monomial):return []
            if m.simplify(m.add(numerator,m.neg(m.mul(denominator,reduced))))!=ZERO:return []
            return [(reduced,)]
        if name=='continuous_at_origin':
            def continuous_syntax(e):
                if e[0] in ('q','pi','s','v'):return True
                return e[0] in CONTINUOUS_FUNCTIONS|{'add','mul','div','pow','rpow'} and all(
                    continuous_syntax(c) for c in e[1:] if isinstance(c,tuple))
            if ctx.get('domain')!='real' or not continuous_syntax(args[0]):return []
            at=m.substitute(args[0],{('v',ctx['variable']):ZERO})
            # The raw origin AST must have its original domain before any tidy.
            return [(m.simplify(at),)] if m.constant_defined(at,ctx) else []
        if name in ('exact_real_partition','partition_solution'):
            if ctx.get('domain')!='global_real_line':return []
            try:
                if name=='exact_real_partition':return [(real_intervals.build_certificate(args[0],args[1],ctx['variable']),)]
                real_intervals.validate_partition(args[0],ctx['variable'])
                return [(args[0][7],)]
            except real_intervals.ResourceBound as exc:raise ResourceBound(str(exc)) from exc
            except real_intervals.Unsupported:return []
        if name=='tidy':
            if ctx.get('domain')=='ordered_interval':
                from ray_proofs import order_tidy
                return [(order_tidy(args[0]),)]
            return [(m.simplify(args[0]),)]
        if name=='minus_one':return [(args[0]-1,)]
        if name=='finite':return [()] if args[0] not in ('+inf','-inf') and constant_domain(args[0],ctx) else []
        if name=='negative_limit':return [()] if args[0]=='-inf' or (args[0]!='+inf' and m.sign(args[0],ctx)==-1) else []
        if name=='zero_times_infinity':return [()] if (args[0]==ZERO and args[1] in ('+inf','-inf')) or (args[1]==ZERO and args[0] in ('+inf','-inf')) else []
        if name=='rational_nonzero':return [()] if rf(args[0],ctx['variable'])[0]!=(F(0),) else []
        if name=='defined_rational':
            rf(args[0],ctx['variable'])
            return [()]
        if name=='rational_leading':
            # rf checks every original divisor before any zero cancellation.
            p,d=rf(args[0],ctx['variable'])
            if p==(F(0),):return [(ZERO,ZERO)]
            vp,vd=valuation(p),valuation(d)
            return [(q(vp-vd),q(p[vp]/d[vd]))]
        if name=='monomial_limit':
            k,c=map(m.num,args)
            if k is None or c is None or k.denominator!=1:return []
            value=ZERO if c==0 or k>0 else q(c) if k==0 else '+inf' if c>0 else '-inf'
            return [(value,)]
        if name=='lh_zero':return [()] if args==(ZERO,ZERO) else []
        if name=='lh_infinite':return [()] if all(a in ('+inf','-inf') for a in args) else []
        if name=='factor_splits':return list(product_splits(args[0]))
        if name=='split_exp_factor':return split_exp_factor(args[0],ctx['variable'])
        if name=='exponential_orders':return exponential_orders(*args,ctx['variable'])
        if name=='build_exp_bound':
            a,u,n=args
            if type(n) is not int or not 1<=n<=256:return []
            return [(('mul',q(factorial(n)),('abs',('div',a,('pow',u,n)))),)]
        if name=='contains_log':
            def contains(e):return e[0]=='ln' or any(contains(c) for c in e[1:] if isinstance(c,tuple))
            return [()] if contains(args[0]) else []
        if name=='jet_slow_regular':return [(slow_regular(args[0],ctx),)]
        if name=='jet_slow_log':return [(slow_log(args[0],ctx),)]
        if name=='jet_positive':return [()] if near_sign(args[0],ctx)==1 else []
        if name=='jet_nonpositive':return [()] if near_sign(args[0],ctx) in (-1,0) else []
        if name=='jet_exp_flat':
            p,c=leading(args[0])
            return [(jet({},F(ctx['order']),ctx['order']),)] if p<0 and m.sign(c,ctx)==-1 else []
        if name=='function_limit':
            fn,value=args
            if fn=='exp' and value in ('+inf','-inf'):return [(ZERO if value=='-inf' else '+inf',)]
            if fn=='ln' and value in ('+inf',ZERO):return [('+inf' if value=='+inf' else '-inf',)]
            if fn in ('atan','acot') and value in ('+inf','-inf'):
                v=m.mul(q(1 if value=='+inf' else -1,2),m.PI)
                return [(v if fn=='atan' else m.add(m.mul(q(1,2),m.PI),m.neg(v)),)]
            if value in ('+inf','-inf') or not constant_domain((fn,value),ctx):return []
            return [(m.simplify((fn,value)),)]
        if name.startswith('rewrite_elementary_'):return elementary_candidates(args[0],name.removeprefix('rewrite_elementary_'))
        if name=='rewrite_exponential_scale':return exponential_scale_candidates(args[0])
        if name=='rewrite_logarithmic_scale':return exponential_scale_candidates(args[0],True)
        if name=='exponential_factor':return exponential_factor_candidates(args[0])
        if name=='constant_defined':return [()] if constant_domain(args[0],ctx) else []
        if name=='is_constant':return [()] if not m.variable_in(args[0]) else []
        if name=='is_variable':return [()] if args[0]==('v',ctx['variable']) else []
        if name=='is_positive_integer':return [()] if type(args[0]) is int and args[0]>0 else []
        if name=='is_nonpositive_integer':return [()] if type(args[0]) is int and args[0]<=0 else []
        if name=='eq':return [()] if canonical(args[0])==canonical(args[1]) else []
        if name=='direct_sum_allowed':return [()] if direct_sum_allowed(args[0]) else []
        if name in ('extended_add','extended_mul'):
            infinite=('+inf','-inf')
            if any(a in infinite for a in args):
                a,b=args if args[0] in infinite else args[::-1]
                if b not in infinite and not constant_domain(b,ctx):return []
                if name=='extended_add':return [(a,)] if b not in infinite or a==b else []
                sign=1 if b=='+inf' else -1 if b=='-inf' else m.sign(b,ctx)
                if sign not in (-1,1):return []
                return [('+inf' if (a=='+inf')==(sign==1) else '-inf',)]
            name='finite_add' if name=='extended_add' else 'finite_mul'
        if name in ('finite_add','finite_mul','finite_div'):
            if any(a in ('+inf','-inf') for a in args):return []
            fn={'finite_add':m.add,'finite_mul':m.mul,'finite_div':m.div}[name]
            if not all(constant_domain(a,ctx) for a in args):return []
            if name=='finite_div' and not m.nonzero(args[1],ctx):return []
            return [(fn(*args),)]
        if name=='continuous_value':
            fn,c=args
            if c in ('+inf','-inf') or not constant_domain((fn,c),ctx):return []
            return [(m.simplify((fn,c)),)]
        if name=='constant_nonzero':return [()] if m.nonzero(args[0],ctx) and constant_domain(args[0],ctx) else []
        if name=='constant_positive':return [()] if m.sign(args[0],ctx)==1 and constant_domain(args[0],ctx) else []
        if name=='jet_constant':return [(jc(m.simplify(args[0]),ctx),)]
        if name=='jet_variable':return [(jet({F(1):ONE},order=ctx['order']),)]
        if name=='jet_add':return [(jadd(*args,ctx),)]
        if name=='jet_mul':return [(jmul(*args,ctx),)]
        if name=='jet_div':return [(jmul(args[0],jpower(args[1],F(-1),ctx),ctx),)]
        if name=='jet_pow':return [(jpower(args[0],F(args[1]),ctx),)]
        if name in ('jet_sqrt','jet_cbrt'):return [(jpower(args[0],F(1,2 if name=='jet_sqrt' else 3),ctx),)]
        if name.startswith('jet_analytic_'):return [(analytic(args[0],name.removeprefix('jet_analytic_'),ctx),)]
        if name=='jet_abs':
            sign=near_sign(args[0],ctx)
            if sign is None:return []
            return [(args[0] if sign>=0 else jscale(args[0],q(-1),ctx),)]
        if name=='leading_coefficient':return [(leading(args[0])[1],)]
        if name=='jet_limit':return [(jet_limit(args[0],ctx),)]
        if name=='jet_nonnegative':return [()] if near_sign(args[0],ctx) in (0,1) else []
        if name=='jet_negative':return [()] if near_sign(args[0],ctx)==-1 else []
        if name=='jet_exact_zero':return [()] if unpack(args[0])==({},None) else []
        if name=='jet_inside_unit':
            v=jet_limit(args[0],ctx)
            return [()] if isinstance(v,tuple) and constant_domain(v,ctx) and m.sign(m.add(ONE,m.neg(m.power(v,2))),ctx)==1 else []
        if name=='jet_outside_unit':
            v=jet_limit(args[0],ctx)
            f=m.num(v) if isinstance(v,tuple) else None
            return [()] if f is not None and abs(f)>1 else []
        if name=='children':return [(c,) for c in args[0][1:] if isinstance(c,tuple)]
        if name=='closed_real_ray':
            return [()] if (ctx.get('source_domain')=='closed_real_ray' and ctx.get('ray_side') in ('left','right')
                            and finite_endpoint_symbol(ctx.get('ray_endpoint'))) else []
        if name=='assumed_finite_end_limit':return [()] if args[0] in ctx.get('finite_end_limits',()) else []
        if name=='assumed_continuous':return [()] if args[0] in ctx.get('continuous_functions',()) else []
        if name=='closed_function_interval':return [()] if closed_function_interval(ctx) else []
        if name=='running_window_components':
            term=args[0]
            return [(term[1],WINDOW_SIDES[term[0]])] if isinstance(term,tuple) and len(term)==2 and term[0] in WINDOW_SIDES else []
        if name=='list_empty':return [()] if args[0]==() else []
        if name=='list_uncons':return [(args[0][0],args[0][1:])] if args[0] else []
        if name=='rewrite_sqrt':return radical_candidates(args[0],'sqrt')
        if name=='rewrite_cbrt':return radical_candidates(args[0],'cbrt')
        if name.startswith('rewrite_trig_'):return trig_candidates(args[0],name.removeprefix('rewrite_trig_'))
        if name=='rewrite_normalize_ratio':return normalize_ratio_candidates(args[0])
        if name=='rewrite_algebra':
            candidate=m.simplify(args[0])
            return [(candidate,())] if candidate!=args[0] else []
        if name=='rational_expression':
            def rational(e):return e[0] in ('q','v','s','pi') or e[0] in ('add','mul','div','pow') and all(rational(c) for c in e[1:] if isinstance(c,tuple))
            return [()] if rational(args[0]) else []
        if name=='absolute_expression':return [(('abs',args[0]),)]
        if name=='bound_product':return [(('mul',args[0],args[1]),)]
        if name=='bound_sum':return [(('add',args[0],args[1]),)]
        if name=='bound_quotient':return [(('div',args[0],('abs',args[1])),)]
        raise Unsupported('Неизвестная операция: '+name)
    except (Unavailable,NotRational,Undefined,ZeroDivisionError):
        return []

def comparable_tail_scale(task, *, recorded=None):
    """Check f(x) ~ c exp(a y) y^b (log y)^d, y -> +infinity, on the original side."""
    fields={'kind','expression','variable','variable_domain','approach','parameters','stated_conditions','parameter_conditions','method_requirement'}
    if (set(task)-fields or task.get('kind')!='limit' or task.get('method_requirement') is not None
            or not isinstance(task.get('expression'),str) or not any(s in task['expression'] for s in ('ln','exp','^'))):
        raise Unsupported('Не задан свободный скалярный предел')
    ctx,targets=m.limit_directions(task,[],'equal_signed_scalar_limits')
    if len(targets)!=1:raise Unsupported('Требуется одна доказанная сторона')
    point=freeze(ctx['point']);side=targets[0][1]
    if point not in ('+inf','-inf') and (point!=ZERO or side not in ('left','right')):
        raise Unsupported('Положительная шкала рассматривается у нуля или на бесконечности')
    direction=-1 if point=='-inf' or point==ZERO and side=='left' else 1
    var=('v',ctx['original_variable']);raw=m.parse(task['expression'],var[1],ctx['parameters'])
    def uses_scale(u):
        return u[0] in ('ln','exp','rpow') or any(uses_scale(t) for t in u[1:] if isinstance(t,tuple))
    if not uses_scale(raw):raise Unsupported('Нет степенной или логарифмической шкалы')
    zero_rates=(ZERO,ZERO,ZERO)
    steps=[];memo={};cursor=iter(recorded) if recorded is not None else None

    def rates(p,r):
        for left,right in zip(p,r):
            diff=m.add(left,m.neg(right));d=m.sign(diff,ctx)
            if d is None:
                # An integer combination of logs of positive rationals is the log of their product.
                terms,den=m.rational_form(diff);product=F(1)
                if den=={():F(1)} and len(terms)<=8:
                    for mon,k in terms.items():
                        if len(mon)!=1 or mon[0][1]!=1 or mon[0][0][0]!='ln' or k.denominator!=1 or abs(k)>32:break
                        base=m.num(mon[0][0][1])
                        if base is None or base<=0:break
                        product*=base**int(k)
                    else:d=(product>1)-(product<1)
            if d is None:raise Unsupported('Не установлено сравнение показателей при исходных условиях')
            if d:return d
        return 0

    def scalar(u):
        if m.variable_in(u) or not m.constant_defined(u,ctx):raise Unsupported('Коэффициент не определён на всей исходной области')
        return m.simplify(u)

    def affine(u):
        """An exact affine exponent; an asymptotic equivalent cannot replace it in exp."""
        if u==var:return (q(direction),ZERO) if point!=ZERO else (None,None)
        if not m.variable_in(u):return ZERO,scalar(u)
        if u[0]=='add':
            a,b=affine(u[1]);c,d=affine(u[2])
            if a is not None and c is not None:return m.add(a,c),m.add(b,d)
        if u[0]=='mul' and (not m.variable_in(u[1]) or not m.variable_in(u[2])):
            const,arg=(u[1],u[2]) if not m.variable_in(u[1]) else (u[2],u[1])
            c=scalar(const);a,b=affine(arg)
            if a is not None:return m.mul(a,c),m.mul(b,c)
        if u[0]=='div' and not m.variable_in(u[2]):
            c=scalar(u[2]);a,b=affine(u[1])
            if a is not None and m.nonzero(c,ctx):return m.div(a,c),m.div(b,c)
        return None,None

    def derive(u):
        if not m.variable_in(u):return 'constant_on_original_domain',scalar(u),zero_rates
        if u==var:return 'original_coordinate',q(direction),(ZERO,q(-1 if point==ZERO else 1),ZERO)
        op=u[0]
        if op in ('div','mul','add'):
            a,p=visit(u[1]);b,r=visit(u[2])
            if op=='add':
                d=rates(p,r)
                if d:return ('dominant_summand',a,p) if d>0 else ('dominant_summand',b,r)
                return 'equal_orders_add',m.add(a,b),p
            if op=='div':return 'divide_nonzero_equivalents',m.div(a,b),tuple(m.add(i,m.neg(j)) for i,j in zip(p,r))
            return 'multiply_equivalents',m.mul(a,b),tuple(m.add(i,j) for i,j in zip(p,r))
        if op in ('pow','sqrt','rpow') and (op!='rpow' or not m.variable_in(u[2])):
            a,p=visit(u[1]);exponent=q(u[2]) if op=='pow' else q(1,2) if op=='sqrt' else scalar(u[2])
            if op!='pow' and m.sign(a,ctx)!=1:raise Unsupported('Положительность основания степени не доказана на хвосте')
            c=ONE if a==ONE else m.power(a,u[2]) if op=='pow' else m.simplify(('rpow',a,exponent))
            return 'fixed_power_on_its_domain',c,tuple(m.mul(i,exponent) for i in p)
        if op=='ln':
            base=u[1]
            if base[0] in ('cos','cosh'):
                c,p=visit(base[1])
                if rates(p,zero_rates)<0:
                    return 'log_cosine_quadratic' if base[0]=='cos' else 'log_cosh_quadratic',m.mul(q(-1 if base[0]=='cos' else 1,2),m.power(c,2)),tuple(m.mul(q(2),i) for i in p)
            if base[0]=='add' and ONE in base[1:]:
                other=base[2] if base[1]==ONE else base[1]
                c,p=visit(other)
                if rates(p,zero_rates)<0:return 'log_one_plus_infinitesimal',c,p
            c,p=visit(base)
            if m.sign(c,ctx)!=1:raise Unsupported('Аргумент логарифма не доказан положительным на хвосте')
            if m.nonzero(p[0],ctx):return 'log_exponential_order',p[0],(ZERO,ONE,ZERO)
            if p[0]==ZERO and m.nonzero(p[1],ctx):return 'log_algebraic_order',p[1],(ZERO,ZERO,ONE)
            if p==zero_rates:return 'log_at_positive_limit',m.simplify(('ln',c)),zero_rates
        if op in ('exp','rpow'):
            # Variable powers are exp(exponent * log(base)); the logarithm's own
            # derivation supplies eventual positivity before forming that product.
            exponent=u[1] if op=='exp' else ('mul',u[2],('ln',u[1]))
            a,b=affine(exponent)
            if a is not None:return 'exact_affine_exponential',m.simplify(('exp',b)),(a,ZERO,ZERO)
            c,p=visit(exponent);d=rates(p,zero_rates)
            if d<=0:return 'exponential_at_finite_limit',ONE if d<0 else m.simplify(('exp',c)),zero_rates
        raise Unsupported('Не построена сравнимая шкала для вложенной функции')

    def visit(u):
        if u not in memo:
            rule,c,p=derive(u)
            if not m.constant_defined(c,ctx) or not m.nonzero(c,ctx):raise Unsupported('Главный коэффициент может обратиться в ноль')
            row=(u,rule,c,p)
            if cursor is not None and freeze(next(cursor,()))!=row:raise Unsupported('Изменено основание, порядок или коэффициент эквивалента')
            steps.append(row);memo[u]=(c,p)
        return memo[u]

    c,p=visit(raw);order=rates(p,zero_rates)
    if order>0 and m.sign(c,ctx) not in (-1,1):raise Unsupported('Не установлен знак бесконечного предела')
    if cursor is not None and next(cursor,None) is not None:raise Unsupported('Лишние шаги в доказательстве')
    return {'variable':var[1],'point':point,'side':side,'coordinate_sign':direction,'steps':steps},(
        ZERO if order<0 else c if order==0 else '+inf' if m.sign(c,ctx)==1 else '-inf')
