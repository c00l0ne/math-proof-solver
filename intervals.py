"""Exact real-line inequalities for degree<=2 piecewise rational polynomials.

The caller supplies the existing expression AST.
No exercise numbers, answers, floating-point arithmetic, text parser or external packages.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key
from math import isqrt


class Unsupported(ValueError):pass
class ResourceBound(Unsupported):pass

MAX_BITS=4096
MAX_BRANCHES=256
MAX_POLYNOMIALS=1024

def sign(q):return (q>0)-(q<0)
def checked(q):
    q=F(q)
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>MAX_BITS:
        raise ResourceBound('Exact rational bit bound exceeded')
    return q
def sign_radical(a,b,d):
    """Sign of a+b*sqrt(d); all squaring is guarded by signs."""
    a,b=F(a),F(b)
    if d<0:raise Unsupported('Negative real radicand')
    if not b or not d:return sign(a)
    sa,sb=sign(a),sign(b)
    if not sa:return sb
    if sa==sb:return sa
    return sa*sign(a*a-b*b*d)


@dataclass(frozen=True)
class Quadratic:
    a:F
    b:F=F(0)
    d:int=0

    def __post_init__(self):
        a,b=checked(self.a),checked(self.b);d=self.d
        if type(d) is not int or d<0:
            raise Unsupported('Unsupported real quadratic radicand')
        if d.bit_length()>MAX_BITS:raise ResourceBound('Quadratic radicand bit bound exceeded')
        r=isqrt(d)
        if not b or r*r==d:a,b,d=checked(a+b*r),F(0),0
        object.__setattr__(self,'a',a);object.__setattr__(self,'b',b);object.__setattr__(self,'d',d)

    def sign(self):return sign_radical(self.a,self.b,self.d)
    def neg(self):return Quadratic(-self.a,-self.b,self.d)
    def field(self,other):
        if not self.b:return other.d
        if not other.b:return self.d
        if self.d!=other.d:raise Unsupported('Arithmetic crosses quadratic fields')
        return self.d
    def add(self,other):
        d=self.field(other);return Quadratic(self.a+other.a,self.b+other.b,d)
    def mul(self,other):
        d=self.field(other)
        return Quadratic(self.a*other.a+self.b*other.b*d,self.a*other.b+self.b*other.a,d)
    def scale(self,q):return Quadratic(self.a*q,self.b*q,self.d)
    def bounds(self,bits):
        if not self.b:return self.a,self.a
        denominator=1<<bits
        low=F(isqrt(self.d<<(2*bits)),denominator)
        high=low+F(1,denominator)
        lo,hi=(low,high) if self.b>0 else (high,low)
        return self.a+self.b*lo,self.a+self.b*hi


def compare(a,b):
    """Compare different quadratic fields without approximating their values.

    Write a-b=r+w*sqrt(f), r=u+v*sqrt(d). If the two summands
    have opposite signs, compare their squares and retain sign(r).
    The resulting sign is again one guarded single-radical comparison.
    """
    if isinstance(a,str) or isinstance(b,str):
        if a==b:return 0
        if a=='-inf' or b=='+inf':return -1
        if a=='+inf' or b=='-inf':return 1
        raise Unsupported('Unknown infinite endpoint')
    u,v,w=a.a-b.a,a.b,-b.b
    sr=sign_radical(u,v,a.d)
    st=sign(w) if b.d else 0
    if not sr:return st
    if not st:return sr
    if sr==st:return sr
    return sr*sign_radical(u*u+v*v*a.d-w*w*b.d,2*u*v,a.d)


def between(left,right):
    if compare(left,right)>=0:raise Unsupported('Cell endpoints are not ordered')
    if left=='-inf' and right=='+inf':return F(0)
    if left=='-inf':
        lo,_=right.bounds(0);return F(lo.numerator//lo.denominator-1)
    if right=='+inf':
        _,hi=left.bounds(0);return F(-((-hi.numerator)//hi.denominator)+1)
    for bits in [0,1,2,4,8,16,32,64,128,256,512,1024,2048]:
        _,lo=left.bounds(bits);hi,_=right.bounds(bits)
        if lo<=hi:
            sample=(lo+hi)/2
            if compare(left,Quadratic(sample))<0 and compare(Quadratic(sample),right)<0:return checked(sample)
    raise ResourceBound('Exact separation needs more dyadic precision')


def trim(values):
    values=[checked(v) for v in values]
    while len(values)>1 and not values[-1]:values.pop()
    if len(values)>3:raise Unsupported('Polynomial degree exceeds two')
    return tuple(values)
def padd(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def pscale(a,q):return trim([c*q for c in a])
def pmul(a,b):
    values=[F(0)]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):values[i+j]+=c*d
    return trim(values)
def peval(p,x):
    result=Quadratic(0)
    for c in reversed(p):result=result.mul(x).add(Quadratic(c))
    return result


def roots(p):
    if len(p)==1:return []
    if len(p)==2:return [Quadratic(-p[0]/p[1])]
    c,b,a=p;delta=b*b-4*a*c
    if delta<0:return []
    d=delta.numerator*delta.denominator
    center=-b/(2*a);coefficient=F(1)/(2*a*delta.denominator)
    values=[Quadratic(center,-coefficient,d),Quadratic(center,coefficient,d)]
    values.sort(key=cmp_to_key(compare))
    return values[:1] if compare(*values)==0 else values


def constant(e):
    tag=e[0]
    if tag=='q':return e[1]
    if tag=='v':raise Unsupported('A variable divisor or exponent needs another domain method')
    if tag=='add':return checked(constant(e[1])+constant(e[2]))
    if tag=='mul':return checked(constant(e[1])*constant(e[2]))
    if tag=='pow':return checked(constant(e[1])**e[2])
    if tag=='abs':return abs(constant(e[1]))
    raise Unsupported('Not a rational constant')


def evaluate(e,x):
    tag=e[0]
    if tag=='q':return Quadratic(e[1])
    if tag=='v':return x
    if tag=='add':return evaluate(e[1],x).add(evaluate(e[2],x))
    if tag=='mul':return evaluate(e[1],x).mul(evaluate(e[2],x))
    if tag=='pow':
        value=evaluate(e[1],x);return value if e[2]==1 else value.mul(value)
    if tag=='abs':
        value=evaluate(e[1],x);return value.neg() if value.sign()<0 else value
    raise Unsupported('Unknown expression node')


def branches(expression):
    polynomials=set()
    def remember(poly):
        polynomials.add(poly)
        if len(polynomials)>MAX_POLYNOMIALS:raise ResourceBound('Polynomial inventory bound exceeded')
    def walk(e):
        tag=e[0]
        if tag=='q':out=[((e[1],),())]
        elif tag=='v':out=[((F(0),F(1)),())]
        elif tag in ('add','mul'):
            a,b=walk(e[1]),walk(e[2]);out=[]
            if len(a)*len(b)>MAX_BRANCHES:raise ResourceBound('Cartesian branch bound exceeded')
            for p,g in a:
                for q,h in b:out.append(((padd if tag=='add' else pmul)(p,q),tuple(dict.fromkeys(g+h))))
        elif tag=='pow':out=[(p if e[2]==1 else pmul(p,p),g) for p,g in walk(e[1])]
        elif tag=='abs':
            out=[]
            for p,g in walk(e[1]):
                if p==(F(0),):out.append((p,g))
                else:out.extend([(p,tuple(dict.fromkeys(g+((p,1),)))),(pscale(p,-1),tuple(dict.fromkeys(g+((p,-1),))))])
        else:raise Unsupported('Unknown branch node')
        out=list(dict.fromkeys(out))
        if len(out)>MAX_BRANCHES:raise ResourceBound('Absolute-value branch bound exceeded')
        for p,g in out:
            remember(p)
            for q,_ in g:remember(q)
        return out
    result=walk(expression)
    return result,sorted(polynomials,key=lambda p:tuple(qterm(c) for c in p))


RELATIONS={'<':lambda s:s<0,'<=':lambda s:s<=0,'>':lambda s:s>0,'>=':lambda s:s>=0,
           '=':lambda s:s==0,'==':lambda s:s==0,'!=':lambda s:s!=0}
SCHEMA='quadratic_abs_partition/v1'


def freeze_data(value,max_nodes=200000):
    count=0
    def walk(x,depth):
        nonlocal count
        count+=1
        if count>max_nodes or depth>256:raise ResourceBound('Canonical-term size bound exceeded')
        if isinstance(x,(tuple,list)):return tuple(walk(v,depth+1) for v in x)
        if x is None or type(x) in (str,int,bool):return x
        raise Unsupported('A certificate contains a noncanonical value')
    return walk(value,0)


def same_data(a,b):
    # Python treats True==1 and False==0. Proof terms must not coerce those types.
    if type(a) is not type(b):return False
    if isinstance(a,tuple):return len(a)==len(b) and all(same_data(x,y) for x,y in zip(a,b))
    return a==b


def qterm(value):
    value=checked(value);return ('q',value.numerator,value.denominator)


def read_qterm(term):
    if not isinstance(term,tuple) or len(term)!=3 or term[0]!='q' or any(type(v) is not int for v in term[1:]) or term[2]<=0:
        raise Unsupported('Malformed canonical rational term')
    value=checked(F(term[1],term[2]))
    if qterm(value)!=term:raise Unsupported('Noncanonical rational term')
    return value


def quadratic_term(value):
    return ('quadratic_real',qterm(value.a),qterm(value.b),value.d)


def read_quadratic_term(term):
    if not isinstance(term,tuple) or len(term)!=4 or term[0]!='quadratic_real':
        raise Unsupported('Malformed quadratic endpoint')
    value=Quadratic(read_qterm(term[1]),read_qterm(term[2]),term[3])
    if quadratic_term(value)!=term:raise Unsupported('Noncanonical quadratic endpoint')
    return value


def endpoint_term(value):return value if isinstance(value,str) else quadratic_term(value)
def read_endpoint(term):
    if term in ('-inf','+inf'):return term
    return read_quadratic_term(term)


def adapt_ast(expression,variable):
    """Consume the declared model.q/v/add/mul/div/pow/abs AST, not text."""
    if not isinstance(variable,str) or not variable.isidentifier():raise Unsupported('Invalid variable identity')
    def walk(e):
        if not isinstance(e,tuple) or not e:raise Unsupported('Expected an expression AST')
        tag=e[0]
        if tag=='q':return ('q',read_qterm(e))
        if tag=='v' and len(e)==2 and e[1]==variable:return e
        if tag in ('add','mul') and len(e)==3:return (tag,walk(e[1]),walk(e[2]))
        if tag=='div' and len(e)==3:
            left,right=walk(e[1]),walk(e[2]);divisor=constant(right)
            if not divisor:raise Unsupported('An original rational divisor is zero')
            return ('mul',left,('q',1/divisor))
        if tag=='pow' and len(e)==3 and type(e[2]) is int and 0<=e[2]<=2:
            base=walk(e[1])
            if e[2]==0:
                if not constant(base):raise Unsupported('Zero to the zeroth power is undefined')
                return ('q',F(1))
            return ('pow',base,e[2])
        if tag=='abs' and len(e)==2:return ('abs',walk(e[1]))
        raise Unsupported('Outside the global quadratic/absolute-value AST language')
    return walk(expression)


def make_union(cuts,cell_truth,point_truth):
    atoms=[];extended=['-inf',*cuts,'+inf']
    for i,selected in enumerate(cell_truth):
        if selected:atoms.append((extended[i],extended[i+1],False,False))
        if i<len(cuts) and point_truth[i]:atoms.append((cuts[i],cuts[i],True,True))
    merged=[]
    for atom in atoms:
        if merged and compare(merged[-1][1],atom[0])==0 and (merged[-1][3] or atom[2]):
            previous=merged.pop();merged.append((previous[0],atom[1],previous[2],atom[3]))
        else:merged.append(atom)
    return ('real_set',tuple((endpoint_term(a),endpoint_term(b),lc,rc) for a,b,lc,rc in merged))


def validate_real_set(value):
    """Validate endpoint types, ordering and maximally merged interval form."""
    value=freeze_data(value)
    if not isinstance(value,tuple) or len(value)!=2 or value[0]!='real_set' or not isinstance(value[1],tuple) or len(value[1])>2*MAX_POLYNOMIALS+1:
        raise Unsupported('Malformed real-set value')
    previous=None
    for interval in value[1]:
        if not isinstance(interval,tuple) or len(interval)!=4 or any(type(v) is not bool for v in interval[2:]):
            raise Unsupported('Malformed interval')
        left,right=map(read_endpoint,interval[:2]);lc,rc=interval[2:]
        if left=='+inf' or right=='-inf' or left=='-inf' and lc or right=='+inf' and rc:
            raise Unsupported('Infinite endpoint cannot be closed')
        order=compare(left,right)
        if order>0 or order==0 and not (lc and rc):raise Unsupported('Empty or reversed interval')
        if previous is not None:
            boundary=compare(previous[1],left)
            if boundary>0 or boundary==0 and (previous[3] or lc):
                raise Unsupported('Intervals overlap or were not maximally merged')
        previous=(left,right,lc,rc)
    return True


def build_certificate(expr,relation,var):
    """Partition the entire real line for the claim expr relation 0."""
    if not isinstance(relation,str) or relation not in RELATIONS:raise Unsupported('Unknown real relation')
    expr=freeze_data(expr,max_nodes=512)
    source=adapt_ast(expr,var);pieces,polys=branches(source)
    all_roots=[r for p in polys for r in roots(p)];all_roots.sort(key=cmp_to_key(compare))
    cuts=[]
    for root in all_roots:
        if not cuts or compare(cuts[-1],root):cuts.append(root)
    extended=['-inf',*cuts,'+inf'];cells=[];points=[]
    for i in range(len(extended)-1):
        sample=between(extended[i],extended[i+1]);x=Quadratic(sample)
        value=evaluate(source,x);active=[]
        for j,(poly,guards) in enumerate(pieces):
            signs=tuple(peval(p,x).sign() for p,_ in guards)
            if all(s*direction>=0 for s,(_,direction) in zip(signs,guards)):
                if compare(peval(poly,x),value):raise AssertionError('Invalid absolute-value branch')
                active.append((j,signs,peval(poly,x).sign()))
        if not active:raise AssertionError('No branch covers an open real cell')
        cells.append((i-1 if i else '-inf',i if i<len(cuts) else '+inf',qterm(sample),
                      quadratic_term(value),bool(RELATIONS[relation](value.sign())),tuple(active)))
    for i,x in enumerate(cuts):
        value=evaluate(source,x)
        points.append((i,quadratic_term(value),bool(RELATIONS[relation](value.sign()))))
    polynomial_certificates=[]
    for poly in polys:
        indices=tuple(next(i for i,r in enumerate(cuts) if compare(r,t)==0) for t in roots(poly))
        discriminant=qterm(poly[1]*poly[1]-4*poly[2]*poly[0]) if len(poly)==3 else None
        polynomial_certificates.append((tuple(qterm(c) for c in poly),discriminant,indices,poly==(F(0),)))
    solution=make_union(cuts,[c[4] for c in cells],[p[2] for p in points])
    validate_real_set(solution)
    return (SCHEMA,(var,relation,expr,'global_real_line'),
      tuple((tuple(qterm(c) for c in p),tuple((tuple(qterm(c) for c in q),direction) for q,direction in guards)) for p,guards in pieces),
      tuple(polynomial_certificates),tuple(quadratic_term(r) for r in cuts),tuple(cells),tuple(points),solution)


def verify_certificate(expr,relation,var,certificate):
    """Bind to the original AST and replay exact finite operations, without search."""
    certificate=freeze_data(certificate)
    expected=build_certificate(expr,relation,var)
    if not same_data(certificate,expected):raise Unsupported('Partition source/roots/cells/endpoints/solution replay mismatch')
    return {'status':'passed','root_count':len(expected[4]),'cell_count':len(expected[5]),
            'scope':'Exact deterministic replay relative to admitted global real-line arguments.'}


def validate_partition(value,variable=None):
    value=freeze_data(value)
    if not isinstance(value,tuple) or len(value)!=8 or value[0]!=SCHEMA:
        raise Unsupported('Malformed partition certificate')
    claim=value[1]
    if not isinstance(claim,tuple) or len(claim)!=4 or claim[3]!='global_real_line':
        raise Unsupported('A partition needs the declared global real-line scope')
    var,relation,expr,_=claim
    if variable is not None and var!=variable:raise Unsupported('Partition variable identity changed')
    verify_certificate(expr,relation,var,value)
    return True


def solution_intervals(certificate):
    certificate=freeze_data(certificate)
    validate_partition(certificate)
    return certificate[7]
