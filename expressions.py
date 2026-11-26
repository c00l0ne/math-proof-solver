"""Exact expressions and scalar algebra for general rule applications.

No exercise identities, limit evaluator or numeric approximation occur here.
"""
from fractions import Fraction as F
from math import gcd,isqrt
import re

from model import Unsupported, canonical, freeze, q, ZERO, ONE, size
from polynomial import ResourceBound, pgcd, pdiv, univariate_coefficients

PI = ('pi',)
MAX_INTEGER_POWER = 256
FUNCTIONS = {'sin','cos','tan','cot','sqrt','cbrt','asin','atan','abs','acos','acot','sec','csc','ln','exp','sinh','cosh','tanh'}
ALIASES = {'arcsin':'asin','arccos':'acos','arctan':'atan','arctg':'atan','arcctg':'acot','arccot':'acot',
           'tg':'tan','ctg':'cot','cosec':'csc','sh':'sinh','ch':'cosh','th':'tanh'}
TOKEN = re.compile(r'\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_][A-Za-z_0-9]*)|([+*/^(),\-]))')


def num(e):
    if isinstance(e, tuple) and len(e)==3 and e[0]=='q':
        return F(e[1],e[2])
    return None


def variable_in(e, name=None):
    return isinstance(e,tuple) and (e[0]=='v' and (name is None or e[1]==name)
        or any(variable_in(c,name) for c in e[1:] if isinstance(c,tuple)))


def contains(e,atom):
    return e==atom or any(contains(c,atom) for c in e[1:] if isinstance(c,tuple))


def tree_size(e):
    return 1+sum(tree_size(c) for c in e[1:] if isinstance(c,tuple)) if isinstance(e,tuple) else 1


class Parser:
    def __init__(self, text, variable, parameters, extra_functions=()):
        if len(text)>4000: raise Unsupported('Формула слишком длинная')
        self.tokens=[]; offset=0
        while offset<len(text):
            if not text[offset:].strip(): break
            m=TOKEN.match(text,offset)
            if not m: raise Unsupported('Неизвестный символ формулы')
            self.tokens.append(next(s for s in m.groups() if s is not None));offset=m.end()
        self.tokens.append('<end>');self.i=0
        self.variable=variable;self.parameters=set(parameters);self.functions=FUNCTIONS.union(extra_functions)

    def take(self, expected=None):
        token=self.tokens[self.i]
        if expected is not None and token!=expected: raise Unsupported('Ожидалось '+expected)
        self.i+=1;return token

    def peek(self): return self.tokens[self.i]

    def add(self):
        e=self.product()
        while self.peek() in ('+','-'):
            op=self.take();b=self.product()
            e=('add',e,b if op=='+' else ('mul',q(-1),b))
        return e

    def product(self):
        e=self.unary()
        while self.peek() in ('*','/'):
            op=self.take();e=('mul' if op=='*' else 'div',e,self.unary())
        return e

    def unary(self):
        if self.peek() in ('+','-'):
            sign=self.take();a=self.unary()
            if sign=='+':return a
            if a[0]=='q':return q(-a[1],a[2])
            return ('mul',q(-1),a)
        a=self.atom()
        if self.peek()=='^':
            self.take();exponent=self.unary()
            # Preserve the exponent's domain before folding numerical integers.
            n=num(simplify(exponent)) if constant_defined(exponent,{'parameters':self.parameters,'assumptions':[]}) else None
            if n is not None and n.denominator==1:
                if abs(n)>MAX_INTEGER_POWER:raise Unsupported(f'Целая степень превышает ограничение {MAX_INTEGER_POWER}')
                a=('pow',a,int(n))
            else:a=('rpow',a,exponent)
        return a

    def atom(self):
        t=self.take();t=ALIASES.get(t,t)
        if t=='(':
            a=self.add();self.take(')');return a
        if t in self.functions or t in ('lg','coth') and self.peek()=='(':
            self.take('(');a=self.add()
            if t in ('min','max'):
                self.take(',');b=self.add();self.take(')');return (t,a,b)
            self.take(')')
            if t=='coth' and t not in self.functions:return ('div',('cosh',a),('sinh',a))
            return ('div',('ln',a),('ln',q(10))) if t=='lg' and t not in self.functions else (t,a)
        if t=='pi':return PI
        if t=='e':return ('exp',ONE)
        if t==self.variable:return ('v',t)
        if t in self.parameters:return ('s',t)
        if re.fullmatch(r'\d+(?:\.\d+)?',t):return q(F(t))
        raise Unsupported('Необъявленный символ: '+t)


def parse(text, variable, parameters=(),extra_functions=()):
    p=Parser(text,variable,parameters,extra_functions)
    try:
        e=p.add()
        if p.peek()!='<end>':raise Unsupported('Лишний элемент формулы')
        if tree_size(e)>256:raise Unsupported('Слишком большое выражение')
    except (IndexError,RecursionError) as exc:raise Unsupported('Неполная или слишком глубокая формула') from exc
    return e


def substitute(e, replacements):
    if e in replacements:return replacements[e]
    return (e[0],*(substitute(c,replacements) if isinstance(c,tuple) else c for c in e[1:]))


def context(task, assumptions=()):
    var=task.get('variable','x')
    if not isinstance(var,str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',var) or var in FUNCTIONS|set(ALIASES)|{'pi','e'}:
        raise Unsupported('Недопустимая переменная')
    params=[]
    for p in task.get('parameters',[]):
        if isinstance(p,str):p={'symbol':p,'domain':'real','independent_of':var}
        name=p.get('symbol')
        if not isinstance(name,str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name) or name in FUNCTIONS|set(ALIASES)|{'pi','e',var}:
            raise Unsupported('Недопустимый постоянный параметр')
        if p.get('domain','real')!='real' or p.get('independent_of',var)!=var:
            raise Unsupported('Параметр должен быть действительным и постоянным относительно переменной предела')
        if name in params:raise Unsupported('Повтор параметра')
        params.append(name)
    approach=task.get('approach',{'point':'0','side':'both'})
    point=approach.get('point','0');side=approach.get('side','both')
    if side not in ('both','left','right','positive_infinity','negative_infinity'):raise Unsupported('Неизвестная сторона подхода')
    if side=='positive_infinity' and point!='+inf' or side=='negative_infinity' and point!='-inf':
        raise Unsupported('Сторона подхода не согласована с точкой предела')
    domain=task.get('variable_domain','real')
    if domain not in ('real','positive_integers'):raise Unsupported('Неподдерживаемая область переменной')
    if domain=='positive_integers' and point!='+inf':raise Unsupported('Последовательности пока поддерживаются при n -> +inf')
    if point not in ('+inf','-inf'):
        point_expr=parse(str(point),None,params)
        if variable_in(point_expr):raise Unsupported('Точка предела не должна зависеть от переменной')
    else:point_expr=point
    internal='__t'
    while internal in params or internal==var:internal+='_'
    declared=[];guards=[]
    for condition in task.get('parameter_conditions',[]):
        match=re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)\s*(>|<|!=|=)\s*(0|1)',condition)
        if not match or match[1] not in params:
            guard=re.fullmatch(r'(.+?)\s*(!=|>)\s*0',condition)
            if not guard:raise Unsupported('Неизвестный вид условия параметра')
            guards.append(('nonzero' if guard[2]=='!=' else 'positive',parse(guard[1],None,params)));continue
        symbol,op,bound=match.groups()
        relation={('>','0'):'positive',('>','1'):'greater_one',('<','0'):'negative',('!=','0'):'nonzero',('=','0'):'zero'}.get((op,bound))
        if relation is None:raise Unsupported('Неизвестный вид условия параметра')
        declared.append({'symbol':symbol,'relation':relation})
    clean=[]
    for a in [*declared,*assumptions]:
        if a['symbol'] not in params or a['relation'] not in ('zero','nonzero','positive','greater_one','negative'):
            raise Unsupported('Неподдерживаемое предположение')
        value={'symbol':a['symbol'],'relation':a['relation']}
        if value not in clean:clean.append(value)
    for p in params:
        relations={a['relation'] for a in clean if a['symbol']==p}
        if 'zero' in relations and len(relations)>1 or 'negative' in relations and relations.intersection({'positive','greater_one'}):
            raise Unsupported('Противоречивые условия')
    ctx={'original_variable':var,'variable':internal,'parameters':params,'point':point_expr,'side':side,
         'variable_domain':domain,'domain':'real','angle_unit':'radian','assumptions':clean,'order':6,
         'nonzero_expressions':[],'positive_expressions':[]}
    zeros={('s',a['symbol']):ZERO for a in clean if a['relation']=='zero'}
    pending=[(relation,substitute(g,zeros)) for relation,g in guards]
    while pending:
        ready=[(relation,g) for relation,g in pending if constant_defined(g,ctx)]
        if not ready:raise Unsupported('Не установлена область определения условия параметра')
        for relation,raw in ready:
            # Check the original domain before cancellation, e.g. a/a != 0.
            g=simplify(raw)
            if sign(g,ctx)==0 or relation=='positive' and (sign(g,ctx)==-1 or known_nonnegative(neg(g),ctx) or neg(g) in ctx['positive_expressions']):
                raise Unsupported('Противоречивые условия')
            target=ctx[relation+'_expressions']
            if g not in target:target.append(g)
            pending.remove((relation,raw))
    return ctx


def limit_directions(task,assumptions,contract):
    """Canonical scalar targets for every direction required by the original statement."""
    a=task.get('approach',{});kind=task.get('kind',task.get('task_type','limit'))
    fields={'kind','task_type','variable','expression','approach','parameters','variable_domain','parameter_conditions',
            'stated_conditions','method_requirement','requested_output','degree','remainder','schema','id','source',
            'source_number','source_edition','source_pdf_page','source_pdf_pages','transcription','transcription_note',
            'derived_by','original_task_type','compilation_scope'}
    unused={'assumptions','source_assumptions','conditions','domain','stated_domain'}
    if (set(task)-fields-unused or any(task.get(k) for k in unused)
            or kind=='limit' and (task.get('requested_output',['limit_value']) not in ([],['limit_value']) or {'degree','remainder'}.intersection(task))
            or not isinstance(a,dict) or set(a)-{'point','side','mode'} or 'mode' in a and a['mode']!='magnitude_infinity'
            or not isinstance(task.get('variable','x'),str)
            or not isinstance(task.get('parameters',[]),(list,tuple)) or any(not isinstance(p,str) and
                (not isinstance(p,dict) or set(p)-{'symbol','domain','independent_of'}) for p in task.get('parameters',[]))
            or not isinstance(task.get('parameter_conditions',[]),(list,tuple)) or not all(isinstance(c,str) for c in task.get('parameter_conditions',[]))):
        raise Unsupported('Неподдерживаемое условие, направление или требование к результату предела')
    bounds=[]
    conditions=task.get('stated_conditions',[])
    if not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions):
        raise Unsupported('Неверный список исходных условий предела')
    if conditions:
        var=task.get('variable','x')
        parameters=list(task.get('parameter_conditions',[]))
        for c in conditions:
            bound=re.fullmatch(r'\s*'+re.escape(var)+r'\s*(<=|>=|!=|<|>)\s*(.+?)\s*',c)
            if bound:bounds.append(bound.groups())
            else:parameters.append(c)
        task={**task,'parameter_conditions':parameters}
    if a.get('mode')=='magnitude_infinity':
        if (contract!='equal_signed_scalar_limits' or kind!='limit'
                or a!={'point':'infinity','side':'both','mode':'magnitude_infinity'} or task.get('variable_domain','real')!='real'):
            raise Unsupported('A magnitude limit requires two real signed directions and the admitted scalar method')
        targets=[({**task,'approach':{'point':p,'side':s}},'right') for p,s in (('-inf','negative_infinity'),('+inf','positive_infinity'))]
    else:
        ctx=context(task,assumptions)
        if ctx['point'] not in ('+inf','-inf') and not constant_defined(ctx['point'],ctx):
            raise Unsupported('Не доказана определённость исходной точки предела')
        sides=['right'] if ctx['point'] in ('+inf','-inf') else ['right','left'] if ctx['side']=='both' else [ctx['side']]
        targets=[(task,s) for s in sides]
        if not bounds:return ctx,targets
    if bounds:
        def approaches_from_domain(target,side):
            ctx=context(target,assumptions);point=ctx['point']
            for relation,endpoint in bounds:
                bound=parse(endpoint,None,ctx['parameters'])
                if not constant_defined(bound,ctx):raise Unsupported('Не доказана определённость границы условия')
                if relation=='!=':continue  # Excluding one fixed point preserves a punctured approach.
                if point in ('+inf','-inf'):direction=1 if point=='+inf' else -1
                else:
                    direction=sign(add(point,neg(bound)),ctx)
                    if direction is None:raise Unsupported('Не установлено положение точки относительно границы условия')
                    if direction==0:direction=1 if side=='right' else -1
                if direction!=(1 if relation.startswith('>') else -1):return False
            return True
        targets=[(t,s) for t,s in targets if approaches_from_domain(t,s)]
        if not targets:raise Unsupported('В указанном направлении нет допустимого подхода из исходной области')
    return context(targets[0][0],assumptions),targets


def normalized(task, ctx, side):
    e=parse(task['expression'],ctx['original_variable'],ctx['parameters'])
    t=('v',ctx['variable'])
    if ctx['point']=='+inf':replacement=('div',ONE,t)
    elif ctx['point']=='-inf':replacement=('div',q(-1),t)
    else:
        increment=t if side=='right' else ('mul',q(-1),t)
        replacement=increment if freeze(ctx['point'])==ZERO else ('add',freeze(ctx['point']),increment)
    substitutions={('v',ctx['original_variable']):replacement}
    substitutions.update({('s',a['symbol']):ZERO for a in ctx['assumptions'] if a['relation']=='zero'})
    result=substitute(e,substitutions)
    result=substitute(result,{('s',a['symbol']):ZERO for a in ctx['assumptions'] if a['relation']=='zero'})
    return result,{'rule':'context.substitute','original':e,'substitution':replacement,'result':result,
                   'original_side':side,'internal_side':'right','sequence_restriction':ctx['variable_domain']=='positive_integers',
                   'assumptions':ctx['assumptions']}


def clean_poly(p):
    p={m:c for m,c in p.items() if c}
    if len(p)>256 or any(max(abs(c.numerator).bit_length(),c.denominator.bit_length())>4096 for c in p.values()):
        raise ResourceBound('Ограничение точной символьной арифметики')
    return p


def addp(a,b):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,F(0))+c
    return clean_poly(r)


def mulp(a,b):
    r={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            powers=dict(ma)
            for atom,n in mb:powers[atom]=powers.get(atom,0)+n
            mon=tuple(sorted(powers.items(),key=lambda x:canonical(x[0])))
            r[mon]=r.get(mon,F(0))+ca*cb
    return clean_poly(r)


def powp(a,n):
    r={():F(1)}
    for _ in range(n):r=mulp(r,a)
    return r


def common_mon(p):
    if not p:return {}
    result=dict(next(iter(p)))
    for m in p:
        d=dict(m)
        result={k:min(n,d.get(k,0)) for k,n in result.items() if d.get(k,0)}
    return result


def polynomial_quotient(expr):
    """Reduce an exactly divisible symbolic polynomial ratio on its original domain."""
    p,d=rational_form(expr)
    if not any(d):return expr
    atoms=sorted({a for poly in (p,d) for mon in poly for a,_ in mon},key=canonical)
    def degree(mon):
        powers=dict(mon)
        return sum(powers.values()),tuple(powers.get(a,0) for a in atoms)
    leading=max(d,key=degree);base=dict(leading);quotient={}
    while p:
        top=max(p,key=degree);powers=dict(top)
        if any(powers.get(a,0)<n for a,n in base.items()):return expr
        term=tuple((a,n-base.get(a,0)) for a,n in top if n>base.get(a,0))
        coeff=p[top]/d[leading]
        quotient[term]=coeff
        p=addp(p,mulp({term:-coeff},d))
    return poly_expr(quotient)


def rat(p,d):
    p,d=radical_poly(p),radical_poly(d)
    p,d=trig_reduce(p),trig_reduce(d)
    if not d:raise ZeroDivisionError('Нулевой символьный знаменатель')
    if not p:return {},{():F(1)}
    common=common_mon(p);other=common_mon(d)
    common={k:min(n,other.get(k,0)) for k,n in common.items() if other.get(k,0)}
    if common:
        def remove(poly):return {tuple((a,n-common.get(a,0)) for a,n in m if n-common.get(a,0)):c for m,c in poly.items()}
        p,d=remove(p),remove(d)
    atoms={a for poly in (p,d) for mon in poly for a,n in mon}
    if len(atoms)==1 and any(mon for mon in p) and any(mon for mon in d):
        atom=next(iter(atoms))
        pp,dd=univariate_coefficients(p,atom,256),univariate_coefficients(d,atom,256)
        if pp is not None and dd is not None:
            g=pgcd(pp,dd)
            if len(g)>1:
                pp,rp=pdiv(pp,g);dd,rd=pdiv(dd,g)
                if rp!=(F(0),) or rd!=(F(0),):raise AssertionError('Exact polynomial division failed')
                def restore(values):return {(() if n==0 else ((atom,n),)):c for n,c in enumerate(values) if c}
                p,d=restore(pp),restore(dd)
    lead=d[min(d,key=canonical)]
    p={m:c/lead for m,c in p.items()};d={m:c/lead for m,c in d.items()}
    if set(p)==set(d):
        factor=p[next(iter(d))]/d[next(iter(d))]
        if all(p[m]==factor*c for m,c in d.items()):return {():factor},{():F(1)}
    return p,d


def radical_poly(poly):
    """Reduce integral powers of real root atoms on their original domain."""
    result={}
    for mon,coefficient in poly.items():
        for atom,n in mon:
            degree={'sqrt':2,'cbrt':3,'abs':2}.get(atom[0])
            if degree is None or n<degree:continue
            p,d=rational_form(atom[1])
            if d!={():F(1)}:continue
            powers=dict(mon);powers[atom]=n%degree
            rest=tuple((a,powers[a]) for a,_ in mon if powers[a])
            exponent=(n//degree)*(2 if atom[0]=='abs' else 1)
            expanded=mulp({rest:coefficient},powp(p,exponent))
            result=addp(result,radical_poly(expanded));break
        else:result=addp(result,{mon:coefficient})
    return clean_poly(result)


def trig_reduce(poly, *, complete=False):
    """Combine paired monomials using sin(u)^2 + cos(u)^2 = 1.

    For an equality test, complete reduction is allowed at angles where both
    sine and cosine occur. Ordinary expression construction keeps paired terms.
    Each step lowers the sine degree of the eliminated monomial.
    """
    poly=dict(poly)
    angles={atom[1] for mon in poly for atom,_ in mon if atom[0]=='cos'} if complete else set()
    while True:
        pair=None
        for mon,coefficient in poly.items():
            for atom,n in mon:
                if atom[0]!='sin' or n<2:continue
                powers=dict(mon);powers[atom]-=2
                base=tuple((a,powers[a]) for a,_ in mon if powers[a])
                cosine=('cos',atom[1]);powers[cosine]=powers.get(cosine,0)+2
                partner=tuple(sorted(((a,k) for a,k in powers.items() if k),key=lambda item:canonical(item[0])))
                if partner in poly or atom[1] in angles:pair=(mon,base,partner,coefficient);break
            if pair:break
        if not pair:return clean_poly(poly)
        mon,base,partner,c=pair
        del poly[mon]
        poly[base]=poly.get(base,F(0))+c
        poly[partner]=poly.get(partner,F(0))-c
        poly=clean_poly(poly)


_RATIONAL_FORMS={}


def rational_form(e):
    """Memoize the pure normal form of an immutable expression; callers receive private copies."""
    try:hit=_RATIONAL_FORMS.get(e)
    except TypeError:return rational_form_uncached(e)
    if hit is None:
        hit=rational_form_uncached(e)
        if len(_RATIONAL_FORMS)>=200000:_RATIONAL_FORMS.clear()
        _RATIONAL_FORMS[e]=hit
    return dict(hit[0]),dict(hit[1])


def rational_form_uncached(e):
    op=e[0]
    if op=='q':return ({():num(e)} if num(e) else {}),{():F(1)}
    if op in ('add','mul','div'):
        a,b=rational_form(e[1]);c,d=rational_form(e[2])
        if op=='add':
            if b==d:return rat(addp(a,c),b)
            return rat(addp(mulp(a,d),mulp(c,b)),mulp(b,d))
        if op=='mul':return rat(mulp(a,c),mulp(b,d))
        return rat(mulp(a,d),mulp(b,c))
    if op=='pow':
        a,b=rational_form(e[1]);n=e[2]
        return rat(powp(a,n),powp(b,n)) if n>=0 else rat(powp(b,-n),powp(a,-n))
    return {((e,1),):F(1)},{():F(1)}


def poly_expr(p):
    if not p:return ZERO
    atoms={a for mon in p for a,n in mon};running=[a for a in atoms if a[0]=='v']
    if (len(p)>8 and len(running)==1 and len(atoms)>1 and
        all(not variable_in(a) for a in atoms if a!=running[0]) and
        max(dict(mon).get(running[0],0) for mon in p)<=32):
        t=running[0];groups={}
        for mon,c in p.items():
            n=dict(mon).get(t,0);key=tuple((a,k) for a,k in mon if a!=t)
            group=groups.setdefault(n,{});group[key]=group.get(key,F(0))+c
        top=max(groups);out=poly_expr(groups[top])
        for n in range(top-1,-1,-1):
            out=('mul',out,t)
            if n in groups:out=('add',out,poly_expr(groups[n]))
        return out
    terms=[]
    for mon,coef in sorted(p.items(),key=lambda item:canonical(item[0])):
        factors=[] if coef==1 and mon else [q(coef)]
        for atom,n in mon:factors.append(atom if n==1 else ('pow',atom,n))
        term=factors[0]
        for x in factors[1:]:term=('mul',term,x)
        terms.append(term)
    out=terms[0]
    for term in terms[1:]:out=('add',out,term)
    return out


def perfect_root(k,n):
    if k<0:
        root=perfect_root(-k,n) if n%2 else None
        return -root if root is not None else None
    if n==2:r=isqrt(k);return r if r*r==k else None
    lo,hi=0,1
    while hi**n<k:hi*=2
    while lo<=hi:
        mid=(lo+hi)//2;v=mid**n
        if v==k:return mid
        if v<k:lo=mid+1
        else:hi=mid-1
    return None


def pi_multiple(e):
    try:
        p,d=rational_form(e)
        if d!={():F(1)}:return None
        if not p:return F(0)
        return p.get(((PI,1),)) if len(p)==1 else None
    except (ZeroDivisionError,ResourceBound):return None


def simple_function(op,a):
    f=num(a)
    if a[0]=='mul' and num(a[1]) is not None and num(a[1])<0:
        if op in ('cos','cosh','abs'):return simple_function(op,neg(a))
        if op in ('sin','sinh','tan','tanh','atan','asin','cbrt'):return neg(simple_function(op,neg(a)))
    if op in ('sqrt','cbrt') and a[0]=='pow':
        degree=2 if op=='sqrt' else 3
        if a[2]%degree==0:
            value=power(a[1],a[2]//degree)
            return simple_function('abs',value) if op=='sqrt' else value
    if op in ('tan','cot','sec','csc'):
        s,c=simple_function('sin',a),simple_function('cos',a)
        numerator,denominator={'tan':(s,c),'cot':(c,s),'sec':(ONE,c),'csc':(ONE,s)}[op]
        if simplify(denominator)!=ZERO:return ('div',numerator,denominator)
    if op=='exp':
        if a==ZERO:return ONE
        if a[0]=='ln':return a[1]
    if op=='ln':
        if a==ONE:return ZERO
        if a[0]=='exp':return a[1]
        if f is not None and 0<f<1:return ('mul',q(-1),('ln',q(1/f)))
        if a[0]=='div' and a[1]==ONE:return ('mul',q(-1),('ln',a[2]))
    if op in ('sinh','tanh') and a==ZERO:return ZERO
    if op=='cosh' and a==ZERO:return ONE
    if op=='atan' and f in (F(1),F(-1)):return ('mul',q(f/4),PI)
    if op=='atan' and a[0] in ('sqrt','div','mul') and constant_defined(a,{'parameters':(), 'assumptions':()}):
        # On the principal branch cos(theta)>0. Compare with the exact sine and cosine table.
        for k in (F(1,6),F(1,3)):
            angle=('mul',q(k),PI)
            sine=simplify(simple_function('sin',angle))
            scaled=mul(a,simple_function('cos',angle))
            if scaled==sine:return angle
            if scaled==neg(sine):return neg(angle)
    if op=='acot':return ('add',('mul',q(1,2),PI),('mul',q(-1),('atan',a)))
    if op=='acos' and f is not None:
        values={F(1):ZERO,F(1,2):('mul',q(1,3),PI),F(0):('mul',q(1,2),PI),F(-1,2):('mul',q(2,3),PI),F(-1):PI}
        if f in values:return values[f]
    if op in ('asin','acos') and a[0] in ('q','div','mul'):
        for value,angle in ((q(1,2),F(1,6)),(div(('sqrt',q(2)),q(2)),F(1,4)),(div(('sqrt',q(3)),q(2)),F(1,3))):
            for direction in (1,-1):
                if a==mul(q(direction),value):
                    k=direction*angle
                    return ('mul',q(k if op=='asin' else F(1,2)-k),PI)
    if op in ('sqrt','cbrt') and f is not None:
        n=2 if op=='sqrt' else 3
        if f<0 and n==2:return (op,a)
        if f<0 and n==3:return neg(simple_function(op,q(-f)))
        u=perfect_root(f.numerator,n);v=perfect_root(f.denominator,n)
        if u is not None and v is not None:return q(F(u,v))
        if n==2 and f.denominator>1:
            return ('div',('sqrt',q(f.numerator if v is not None else f.numerator*f.denominator)),q(v if v is not None else f.denominator))
    if op in ('sqrt','cbrt') and f is None:
        p,d=rational_form(a)
        if len(p)==1 and d=={():F(1)}:
            mon,coefficient=next(iter(p.items()));n=2 if op=='sqrt' else 3
            if coefficient!=1 and (coefficient>0 or n==3):
                numerator=perfect_root(coefficient.numerator,n);denominator=perfect_root(coefficient.denominator,n)
                if numerator is not None and denominator is not None:
                    return ('mul',q(F(numerator,denominator)),(op,poly_expr({mon:F(1)})))
    if op=='abs':
        if f is not None:return q(abs(f))
        if a[0]=='abs':return a
    if op in ('sin','cos'):
        k=pi_multiple(a)
        if k is not None:
            k=k%2
            sine={F(0):ZERO,F(1,6):q(1,2),F(1,4):('div',('sqrt',q(2)),q(2)),
                  F(1,3):('div',('sqrt',q(3)),q(2)),F(1,2):ONE}
            if op=='cos':k=(k+F(1,2))%2
            sign=1
            if k>1:k-=1;sign=-1
            if k>F(1,2):k=1-k
            if k in sine:
                value=sine[k]
                return value if sign==1 else ('mul',q(-1),value)
    if op in ('asin','atan') and a==ZERO:return ZERO
    if op=='asin' and a in (ONE,q(-1)):return ('mul',q(num(a)/2),PI)
    return (op,a)


_SIMPLIFIED={}


def simplify(e):
    """Memoize the pure simplification of immutable expressions."""
    e=freeze(e)
    try:hit=_SIMPLIFIED.get(e)
    except TypeError:return simplify_uncached(e)
    if hit is None:
        hit=simplify_uncached(e)
        if len(_SIMPLIFIED)>=400000:_SIMPLIFIED.clear()
        _SIMPLIFIED[e]=hit
    return hit


def simplify_uncached(e):
    if e[0]=='pow' and e[1][0]=='abs' and e[2]%2==0:
        return simplify(('pow',e[1][1],e[2]))
    if e[0]=='cbrt' and e[1][0]=='pow':
        return simplify(('pow',('cbrt',e[1][1]),e[1][2]))
    if e[0]=='rpow':
        base,power=simplify(e[1]),simplify(e[2]);half=num(power)
        if half is not None and half.denominator==2 and abs(half.numerator)<=24:
            # A half-integer real power is an integer power of the principal square root on the same domain.
            root=('pow',('sqrt',base),abs(half.numerator))
            return simplify(root if half>0 else ('div',ONE,root))
        return ('rpow',base,power)
    if e[0] in FUNCTIONS:
        a=simplify(e[1]);value=simple_function(e[0],a)
        if value[0] in ('add','mul','div','pow'):return simplify(value)
        return value
    if e[0]=='pow' and e[1][0] in ('sqrt','cbrt') and e[2]>0:
        n=2 if e[1][0]=='sqrt' else 3
        if e[2]%n==0:return simplify(('pow',e[1][1],e[2]//n))
    if e[0] in ('add','mul','div','pow'):
        children=(simplify(e[1]),e[2]) if e[0]=='pow' else (simplify(e[1]),simplify(e[2]))
        p,d=rational_form((e[0],*children))
        a,b=poly_expr(p),poly_expr(d)
        return a if b==ONE else ('div',a,b)
    return e


def add(a,b):return simplify(('add',a,b))
def mul(a,b):return simplify(('mul',a,b))
def div(a,b):return simplify(('div',a,b))
def power(a,n):return simplify(('pow',a,n))
def neg(a):return mul(q(-1),a)


def combine_rational_logs(value):
    """Collect linear logarithms of positive rationals using pairwise coprime integer bases."""
    numerator,denominator=rational_form(value)
    if denominator!={():F(1)}:return value
    bases={};rest=dict(numerator)
    def collect(n,c):
        if n>1:bases[n]=bases.get(n,0)+c
    for mon,c in numerator.items():
        if len(mon)!=1:continue
        atom,power=mon[0]
        arg=num(atom[1]) if atom[0]=='ln' and power==1 else None
        if arg is not None and arg>0:
            del rest[mon];collect(arg.numerator,c);collect(arg.denominator,-c)
    if not bases:return value
    while True:
        pair=next(((a,b,gcd(a,b)) for a in bases for b in bases if a<b and gcd(a,b)>1),None)
        if pair is None:break
        a,b,g=pair;u,v=bases.pop(a),bases.pop(b)
        collect(a//g,u);collect(b//g,v);collect(g,u+v)
    for n,c in bases.items():
        if c:rest[((('ln',q(n)),1),)]=c
    return poly_expr(rest)


def dot(a,b):
    total=ZERO
    for x,y in zip(a,b,strict=True):total=add(total,mul(x,y))
    return total


def nonzero(e,ctx):
    e=simplify(e);f=num(e)
    if e in [freeze(g) for g in ctx.get('nonzero_expressions',[])+ctx.get('positive_expressions',[])]:return True
    if f is not None:return f!=0
    if e==PI:return True
    if e[0]=='s' and any(a['symbol']==e[1] and a['relation'] in ('nonzero','positive','greater_one','negative') for a in ctx['assumptions']):return True
    if e[0] in ('exp','cosh'):return True
    if e[0] in ('sqrt','cbrt','abs'):return nonzero(e[1],ctx) or polynomial_nonzero(e,ctx)
    if e[0] in ('mul','div'):return nonzero(e[1],ctx) and nonzero(e[2],ctx)
    if e[0]=='pow':return nonzero(e[1],ctx)
    return sign(e,ctx) in (-1,1) or polynomial_nonzero(e,ctx)


def polynomial_nonzero(e,ctx):
    """Certify fixed polynomial powers or one-atom factors from admitted guards.

    Each nonconstant gcd divides an already nonzero polynomial, so it is also
    nonzero. Remove such factors until only a nonzero constant remains.
    Expanded powers preserve nonzeroness; unmatched multivariate factors remain
    unresolved. Running variables never acquire a scalar guard from this check.
    """
    guards=[freeze(g) for g in ctx.get('nonzero_expressions',[])+ctx.get('positive_expressions',[])]
    guards += [('s',a['symbol']) for a in ctx.get('assumptions',[]) if a['relation'] in ('nonzero','positive','negative','greater_one')]
    if not guards and (e[0]!='add' or variable_in(e) or size(e)>48):return False
    def bounded_powers(expr):
        pending=[(expr,1)]
        while pending:
            node,scale=pending.pop()
            if node[0]=='pow':scale*=max(1,abs(node[2]))
            if scale>512:return False
            pending.extend((c,scale) for c in node[1:] if isinstance(c,tuple))
        return True
    if not bounded_powers(e):return False
    guards=[g for g in guards if bounded_powers(g)]
    try:
        p,d=rational_form(e)
        if d!={():F(1)}:return False
        atoms={a for mon in p for a,k in mon}
        if not atoms:return bool(p.get((),F(0)))
        degree=max(sum(k for a,k in mon) for mon in p)
        if degree>512:return False
        if len(atoms)!=1:
            if variable_in(e) or any(not constant_defined(a,ctx) for a in atoms):return False
            common=common_mon(p)
            if common and all(nonzero(a,ctx) for a in common):
                rest={tuple((a,k-common.get(a,0)) for a,k in mon if k-common.get(a,0)):c for mon,c in p.items()}
                if nonzero(poly_expr(rest),ctx):return True
            def monic(poly):
                scale=poly[min(poly,key=repr)]
                return {mon:c/scale for mon,c in poly.items()}
            target=monic(p)
            for guard in guards:
                for known in rational_form(guard):
                    power=known;guard_degree=max((sum(k for a,k in mon) for mon in known),default=0)
                    if not guard_degree:continue
                    for n in range(1,min(8,degree//guard_degree)+1):
                        if monic(power)==target:return True
                        if n<min(8,degree//guard_degree):
                            power,den=rat(mulp(power,known),{():F(1)})
                            if den!={():F(1)}:break
            # If the product with a conjugate is nonzero, so is the given factor.
            for root in sorted((a for a in atoms if a[0]=='sqrt'),key=canonical):
                conjugate={mon:(-c if dict(mon).get(root,0)%2 else c) for mon,c in p.items()}
                norm=radical_poly(mulp(p,conjugate))
                if all(root not in dict(mon) for mon in norm) and nonzero(poly_expr(norm),ctx):return True
            return False
        atom=next(iter(atoms))
        if variable_in(atom) or not constant_defined(atom,ctx):return False
        remaining=univariate_coefficients(p,atom)
        if remaining is None:return False
        for guard in guards:
            # context() admitted the original guard only after its domain was
            # established. Thus numerator AND denominator are nonzero here.
            top,bottom=rational_form(guard)
            for poly in (top,bottom):
                known=univariate_coefficients(poly,atom)
                if known is None and atom[0] in ('sin','cos'):
                    other=('cos' if atom[0]=='sin' else 'sin',atom[1])
                    if other in common_mon(poly):
                        known=(F(1),F(0),F(-1))  # The complementary square is nonzero.
                if known is None or len(known)<=1:continue
                while len(remaining)>1:
                    common=pgcd(remaining,known)
                    if len(common)<=1:break
                    remaining,remainder=pdiv(remaining,common)
                    if remainder!=(F(0),):raise AssertionError('Non-exact certified factor division')
                if len(remaining)==1:return remaining[0]!=0
        if len(remaining)==3 and remaining[1]**2<4*remaining[0]*remaining[2]:return True
        residual={(() if i==0 else ((atom,i),)):c/remaining[-1] for i,c in enumerate(remaining) if c}
        return sign(poly_expr(residual),ctx) in (-1,1)
    except (ZeroDivisionError,ResourceBound):return False


def rational_exp_sign(e):
    """Sign of c+k*exp(r) when a rational Taylor enclosure separates it from zero."""
    for i,j in ((1,2),(2,1)):
        c=num(e[i]);p=e[j];k=F(1)
        if p[0]=='mul':k,p=num(p[1]),p[2]
        if c is None or k is None or p[0]!='exp':continue
        r=num(p[1])
        if r is None or not 0<abs(r)<=4:continue
        u=abs(r);term=lo=F(1)
        for n in range(1,13):term*=u/n;lo+=term
        hi=lo+term*u/13/(1-u/14)
        if r<0:lo,hi=1/hi,1/lo
        a,b=sorted((c+k*lo,c+k*hi))
        if a>0:return 1
        if b<0:return -1
    return None


def sign(e,ctx):
    raw=freeze(e)
    if isinstance(raw,tuple) and raw[0]=='rpow' and size(raw)<=48 and not variable_in(raw):return 1 if constant_defined(raw,ctx) else None
    e=simplify(e);f=num(e)
    if e[0]=='rpow' and raw!=e and size(e)<=48 and not variable_in(raw) and constant_defined(raw,ctx):return 1
    if f is not None:return (f>0)-(f<0)
    positive=[freeze(g) for g in ctx.get('positive_expressions',[])]
    if e in positive:return 1
    if positive and neg(e) in positive:return -1
    if e==PI:return 1
    if e[0]=='s':
        relations={a['relation'] for a in ctx['assumptions'] if a['symbol']==e[1]}
        return 0 if 'zero' in relations else 1 if relations.intersection({'positive','greater_one'}) else -1 if 'negative' in relations else None
    if e[0] in ('exp','cosh'):return 1
    if e[0]=='ln':
        arg=e[1];n=num(arg)
        if n is not None and n>0:return (n>1)-(n<1)
        if arg[0]=='s' and any(a['symbol']==arg[1] and a['relation']=='greater_one' for a in ctx['assumptions']):return 1
        if size(arg)<=48 and not variable_in(arg) and sign(arg,ctx)==1:return sign(add(arg,q(-1)),ctx)
    if e[0] in ('sinh','tanh','atan'):return sign(e[1],ctx)
    if e[0]=='asin' and constant_defined(e,ctx):return sign(e[1],ctx)
    if e[0] in ('sqrt','abs'):
        return 1 if nonzero(e[1],ctx) else 0 if sign(e[1],ctx)==0 else None
    if e[0]=='cbrt':return sign(e[1],ctx)
    if e[0]=='pow':
        if e[2]%2==0:return 1 if nonzero(e[1],ctx) else 0 if e[2]>0 and sign(e[1],ctx)==0 else None
        return sign(e[1],ctx)
    if e[0] in ('mul','div'):
        a,b=sign(e[1],ctx),sign(e[2],ctx)
        if a is None or b is None:return None
        return a*b if e[0]=='mul' or b else None
    if e[0]=='add':
        a,b=sign(e[1],ctx),sign(e[2],ctx)
        if a==1 and known_nonnegative(e[2],ctx) or b==1 and known_nonnegative(e[1],ctx):return 1
        if a==b:return a
        if a==0:return b
        if b==0:return a
        return rational_exp_sign(e)
    return None


def known_nonnegative(e,ctx,*,defined=False):
    e=freeze(e)
    if e[0]=='pow' and e[2]>0 and e[2]%2==0 and not variable_in(e[1]):
        # Expansion can hide an even power or cancel a hole in its scalar base.
        return defined or constant_defined(e[1],ctx)
    e=simplify(e);n=num(e)
    if n is not None:return n>=0
    if e in [freeze(g) for g in ctx.get('positive_expressions',[])]:return True
    if e==PI or e[0] in ('sqrt','abs','exp','cosh'):return True
    if e[0]=='pow' and e[2]>0:return e[2]%2==0 or known_nonnegative(e[1],ctx)
    if e[0]=='s':return any(a['symbol']==e[1] and a['relation'] in ('zero','positive','greater_one') for a in ctx['assumptions'])
    if e[0] in ('add','mul'):return all(known_nonnegative(c,ctx) for c in e[1:])
    return False


def constant_defined(e,ctx):
    if variable_in(e):return False
    op=e[0]
    if op in ('q','pi'):return True
    if op=='s':return e[1] in ctx['parameters']
    if op in ('add','mul'):return all(constant_defined(c,ctx) for c in e[1:])
    if op=='rpow':return constant_defined(e[1],ctx) and sign(e[1],ctx)==1 and constant_defined(e[2],ctx)
    if op=='div':return constant_defined(e[1],ctx) and constant_defined(e[2],ctx) and nonzero(e[2],ctx)
    if op=='pow':return constant_defined(e[1],ctx) and (e[2]>0 or nonzero(e[1],ctx))
    if not constant_defined(e[1],ctx):return False
    if op in ('sin','cos','cbrt','atan','abs','exp','sinh','cosh','tanh','acot'):return True
    if op=='ln':return sign(e[1],ctx)==1
    if op=='sqrt':return known_nonnegative(e[1],ctx,defined=True) or sign(e[1],ctx) in (0,1)
    if op in ('tan','sec'):return nonzero(simple_function('cos',simplify(e[1])),ctx)
    if op in ('cot','csc'):return nonzero(simple_function('sin',simplify(e[1])),ctx)
    if op in ('asin','acos'):
        return sign(add(ONE,neg(power(e[1],2))),ctx) in (0,1)
    return False


def scalar_limit_conclusion(value,ctx):
    return value if value in ('+inf','-inf') or constant_defined(value,ctx) else None


def render(e):
    if e in ('+inf','-inf'):return '+∞' if e=='+inf' else '−∞'
    if not isinstance(e,(tuple,list)):return str(e)
    e=freeze(e);op=e[0]
    if op=='q':return str(e[1]) if e[2]==1 else f'({e[1]}/{e[2]})'
    if op=='pi':return 'π'
    if op in ('v','s'):return e[1]
    if op=='pow':return f'({render(e[1])})^{e[2]}'
    if op=='rpow':return f'({render(e[1])})^({render(e[2])})'
    if op in ('min','max'):return f'{op}({render(e[1])}, {render(e[2])})'
    if op in FUNCTIONS:return f'{op}({render(e[1])})'
    if op in ('add','mul','div'):return '('+render(e[1])+{'add':' + ','mul':' · ','div':' / '}[op]+render(e[2])+')'
    return str(e)
