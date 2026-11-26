"""Bounded exact polynomial arithmetic shared by simplification and estimates."""
from fractions import Fraction as F
from math import gcd, isqrt, lcm
from model import rational


class NotRational(Exception):
    pass

class Undefined(Exception):
    pass

class ResourceBound(Exception):
    pass

def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    if len(p) > 513 or any(max(abs(c.numerator).bit_length(), c.denominator.bit_length()) > 8192 for c in p):
        raise ResourceBound("Ограничение точной арифметики")
    return tuple(p)

def pa(a, b):
    return trim([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
                 for i in range(max(len(a), len(b)))])

def pm(a, b):
    if len(a) + len(b) > 514:
        raise ResourceBound("Степень многочлена превышает 512")
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)

def quotient_derivative_numerator(p, d):
    def derivative(t):
        return trim([i*c for i,c in enumerate(t) if i] or [F(0)])
    return pa(pm(derivative(p),d),tuple(-v for v in pm(p,derivative(d))))

def pp(a, n):
    c = (F(1),)
    for _ in range(n):
        c = pm(c, a)
    return c

def pdiv(a, b):
    if b == (F(0),):
        raise Undefined("Нулевой многочлен в знаменателе")
    a = list(a)
    out = [F(0)] * max(1, len(a)-len(b)+1)
    while len(a) >= len(b) and any(a):
        i = len(a)-len(b)
        v = a[-1]/b[-1]
        out[i] += v
        for j, w in enumerate(b):
            a[i+j] -= v*w
        a = list(trim(a))
    return trim(out), trim(a)

def univariate_coefficients(poly, atom, max_degree=512):
    """Dense rational coefficients if every monomial uses just the given atom."""
    if any(a!=atom for mon in poly for a,k in mon):return None
    degree=max((dict(mon).get(atom,0) for mon in poly),default=0)
    if degree>max_degree:return None
    values=[F(0)]*(degree+1)
    for mon,c in poly.items():values[dict(mon).get(atom,0)]=c
    return tuple(values)

def composition_coefficients(target, inner):
    """Read P in target=P(inner) by successive exact division."""
    if len(inner)<2:return None
    coefficients=[]
    while len(target)>1:
        target,remainder=pdiv(target,inner)
        if len(remainder)>1:return None
        coefficients.append(remainder[0])
    return (*coefficients,target[0])

def pgcd(a, b):
    while b != (F(0),):
        _, r = pdiv(a, b)
        a, b = b, r
    return tuple(x/a[-1] for x in a)


def sturm_chain(p):
    """Signed remainder sequence of a nonconstant polynomial and its derivative."""
    chain=[p,tuple(i*c for i,c in enumerate(p) if i)]
    while True:
        _,r=pdiv(chain[-2],chain[-1])
        if r==(0,):break
        chain.append(tuple(-c/abs(r[-1]) for c in r))
    return chain

def distinct_root_counter(p):
    """V(x) for the square-free part; V(a)-V(b) counts roots in (a,b]."""
    chain=sturm_chain(p)
    if len(chain[-1])>1:chain=sturm_chain(pdiv(p,chain[-1])[0])
    def variations(x):
        signs=[]
        for f in chain:
            value=F(0)
            for c in reversed(f):value=value*x+c
            if value:signs.append(value>0)
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    return variations


def no_real_roots(p):
    """Equal sign variations at the two infinities exclude every real root by Sturm's theorem."""
    p=trim(p)
    if len(p)==1:return bool(p[0])
    if len(p)%2==0:return False
    if len(p)==3:return p[1]**2<4*p[0]*p[2]
    chain=sturm_chain(p)
    def variations(left):
        signs=[(f[-1]>0) != (left and len(f)%2==0) for f in chain]
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    return variations(True)==variations(False)

def proper_factor(p):
    """Find a proper divisor of a monic polynomial via repeated factors or rational roots in x^k."""
    if len(p)<=2:return None
    if p[0]==0:return (F(0),F(1))
    multiple=pgcd(p,tuple(i*c for i,c in enumerate(p) if i))
    if len(multiple)>1:return multiple
    def divisors(n):
        return {v for i in range(1,isqrt(n)+1) if n%i==0 for v in (i,n//i)}
    powers=gcd(*(i for i,c in enumerate(p) if i and c))
    for step in sorted(divisors(powers),reverse=True):
        small=p[::step]
        if len(small)<=2:continue
        if len(small)==3:
            disc=small[1]**2-4*small[0]
            if disc<0:continue
            n,d=isqrt(disc.numerator),isqrt(disc.denominator)
            if n*n!=disc.numerator or d*d!=disc.denominator:continue
            root=(-small[1]+F(n,d))/2
        else:
            scale=lcm(*(c.denominator for c in small))
            first=abs(int(small[0]*scale))
            if max(first,scale)>65536:continue
            candidates={F(a,b)*sign for a in divisors(first) for b in divisors(scale) for sign in (-1,1)}
            root=next((r for r in sorted(candidates) if sum(c*r**i for i,c in enumerate(small))==0),None)
            if root is None:continue
        return (-root,)+(F(0),)*(step-1)+(F(1),)
    return None


def span_coefficients(target, columns):
    """Express a polynomial in the given columns over Q, or return None."""
    pivots = {}
    # Each pivot carries its combination of columns. Reducing the target
    # accumulates the negative of the same combination in weights.
    for i, poly in enumerate([*columns, target]):
        row = {j:c for j,c in enumerate(poly) if c}
        weights = {i: F(1)} if i < len(columns) else {}
        while row:
            degree = max(row)
            if degree not in pivots:
                if i == len(columns): return None
                scale = row[degree]
                pivots[degree] = ({j:c/scale for j,c in row.items()},
                                  {j:c/scale for j,c in weights.items()})
                break
            scale = row[degree]
            for dest, pivot in zip((row,weights),pivots[degree]):
                for j,c in pivot.items():
                    dest[j] = dest.get(j,0)-scale*c
                    if not dest[j]: del dest[j]
                if dest: trim(list(dest.values()))
        if i == len(columns): return tuple(-weights.get(j,0) for j in range(i))

def rf(e, variable):
    op = e[0]
    if op == "q":
        return (rational(e),), (F(1),)
    if op == "v" and e[1] == variable:
        return (F(0), F(1)), (F(1),)
    if op in ("add", "mul", "div"):
        a, b = rf(e[1], variable)
        c, d = rf(e[2], variable)
        if op == "add":
            return pa(pm(a,d), pm(c,b)), pm(b,d)
        if op == "mul":
            return pm(a,c), pm(b,d)
        if c == (F(0),):
            raise Undefined("Исходный делитель тождественно нулевой")
        return pm(a,d), pm(b,c)
    if op == "pow":
        a, b = rf(e[1], variable)
        n = e[2]
        if n <= 0 and a == (F(0),):
            raise Undefined("Нулевая основа в неположительной степени")
        return (pp(a,n), pp(b,n)) if n >= 0 else (pp(b,-n), pp(a,-n))
    raise NotRational()

def valuation(p):
    if p == (F(0),):
        return None
    return next(i for i,c in enumerate(p) if c)
