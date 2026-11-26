"""Uniform norm of rational families on a fixed real interval via exact critical fibers."""
import re
from fractions import Fraction as F
from math import ceil

import expressions as m
import intervals as line
import polynomial as poly
from graphs import rational_roots
from model import ONE,ZERO,Unsupported,freeze,q
from plane_domains import decomposition,factors_and_conditions,fiber,projection,yterm
from tasks import domain_conditions,known_guard,source


def functional_characterization(task,lib,saved=None):
    """Transport a homomorphism to the real additive group and descend its linear solutions."""
    fields={'kind','id','source','equation','assumptions','printed_claim','requested_output'}
    provenance={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','page_png_sha256'}
    if (not lib.data.get('regular_real_homomorphism') or set(task)-fields or
            not isinstance(task.get('source',{}),dict) or set(task.get('source',{}))-provenance or
            task.get('requested_output')!=['prove_characterization']):
        raise Unsupported('The original characterization has additional requirements')
    name=r'[A-Za-z]\w*'
    eq=re.fullmatch(fr'({name})\(({name})([+*])({name})\)=\1\(({name})\)([+*])\1\(({name})\)',
                    re.sub(r'\s','',task.get('equation','')))
    if not eq:raise Unsupported('No binary homomorphism law for the two independent arguments')
    f,x,domain_op,y,left,value_op,right=eq.groups()
    if len({f,x,y})!=3 or {left,right}!={x,y}:raise Unsupported('The law must bind two distinct arguments')
    printed=task.get('printed_claim')
    if isinstance(printed,str):
        binder=re.match(re.escape(f)+r'\(('+name+r')\)=',printed.replace(' ',''))
        if binder and binder[1]==y:x,y=y,x
    if {f,x,y}&{'H','c','ln','exp'} or f in ('t','s'):
        raise Unsupported('Rename symbols that would capture a proof variable or an elementary function')
    # The default domain of a real functional equation is R. Restrictions must come from the source.
    domains=set();facts=[];nonzero=False
    for text in task.get('assumptions',[]):
        for clause in re.split(r';\s*|,\s+(?=not identically|bounded on|monotone on|continuous on)',text):
            clause=clause.removeprefix(f+' ')
            if clause=='not identically zero':nonzero=True;continue
            if clause in (x+','+y+'>0',y+','+x+'>0'):domains.add('positive');continue
            regular=re.fullmatch(r'(continuous|monotone) on (R|\(0,\+inf\))',clause)
            if regular:
                domains.add('real' if regular[2]=='R' else 'positive')
                facts.append((regular[1],None));continue
            bound=re.fullmatch(r'bounded on (?:a neighborhood )?\(([^,]+),([^,]+)\)',clause)
            if not bound:raise Unsupported('Unproved or additional hypothesis: '+clause)
            a,b=bound.groups()
            if (a,b) not in (('-epsilon','epsilon'),('0','epsilon')):
                try:
                    if F(a)>=F(b):raise Unsupported('The boundedness interval must have interior')
                except (ValueError,ZeroDivisionError) as exc:raise Unsupported('Unverified boundedness interval') from exc
            facts.append(('bounded',(a,b)))
    expected='real' if domain_op=='+' else 'positive'
    if (domains or {'real'})!={expected} or len(facts)!=1:
        raise Unsupported('Need one supported regularity hypothesis on the entire source group or a bounded interval')
    regular,bound=facts[0]
    zero_boundary=False
    if bound and expected=='positive':
        try:left=F(bound[0])
        except (ValueError,ZeroDivisionError):raise Unsupported('The bounded interval needs real endpoints in the source group')
        if left<0:raise Unsupported('The asserted interval crosses the source group boundary')
        zero_boundary=left==0
    rules={'+':'identity','*':'log'}
    desired=[rules[domain_op],rules[value_op]]
    coordinates=desired if saved is None else saved['coordinates']
    if coordinates!=desired:raise Unsupported('The coordinates do not turn both source operations into addition')
    use_exp,use_log=(c=='log' for c in coordinates)
    arg='exp(t)' if use_exp else 't'
    core=f+'('+arg+')';steps=[]
    if use_log:
        unit='1' if use_exp else '0'
        half='sqrt('+x+')' if use_exp else x+'/2'
        inv='1/'+x if use_exp else '−'+x
        steps.append(f'Если функция не тождественно нулевая, то {f}({unit})=1 по закону для нейтрального элемента. '
                     f'Из {f}({x}){f}({inv})=1 и {f}({x})={f}({half})² следует строгая положительность.')
        core='ln('+core+')'
    steps.append('Положим H(t)='+core+'. Исходное равенство даёт H(s+t)=H(s)+H(t) для любых вещественных s,t.')
    steps.append('При c=H(1) аддитивность даёт H(0)=0, H(−t)=−H(t) и H(mt)=mH(t) по индукции. '
                 'Следовательно, H(p/q)=pc/q для целых p и q>0.')
    if regular=='bounded':
        steps.append('На внутреннем подотрезке исходного интервала H ограничена сверху числом M: '
                     'логарифм сохраняет верхнюю оценку положительной функции, экспонента переносит интервал. '
                     'Для середины u и |v| меньше полудлины обе точки u±v лежат в интервале. '
                     'По аддитивности |H(v)|≤M−H(u). Применяя оценку к Nv и деля на N, получаем непрерывность в нуле.')
    if regular=='monotone':
        steps.append('Координаты возрастают. Для двух рациональных последовательностей, приближающих t снизу и сверху, '
                     'монотонность заключает H(t) между значениями, сходящимися к ct.')
    else:
        steps.append('Непрерывность переносится на H и из нуля на каждую точку по аддитивности. '
                     'Предел рациональных приближений к t даёт H(t)=ct.')
    basis='ln('+x+')' if use_exp else x
    formula=f+'('+x+')='+(x+'^c' if use_log and use_exp else 'exp(c*'+x+')' if use_log else 'c*'+basis)
    branches=[formula];parameter='c ∈ R'
    if use_log and not nonzero:branches.append(f+'('+x+')=0')
    if not use_log and nonzero:parameter='c ∈ R, c ≠ 0'
    steps.append('Обратное преобразование H(t)=ct даёт '+formula+'. Подстановка использует аддитивность линейной функции '
                 'и взаимную обратимость exp и ln на положительных значениях. Полученные функции непрерывны, '
                 'монотонны и ограничены на внутренних ограниченных отрезках своей области.')
    if use_log and not nonzero:steps.append('Отдельная нулевая функция удовлетворяет исходному произведению и условию регулярности.')
    if not use_log and nonzero:steps.append('Тождественный нуль исключён условием задачи, поэтому c≠0.')
    if zero_boundary:
        if use_log:
            parameter='c ∈ R, c ≥ 0'
            steps.append('На x=2^(−n), начиная с достаточно большого n, степень x^c неограниченно растёт при c<0. '
                         'При c≥0 она ограничена на всём исходном интервале с конечным правым концом.')
        else:
            branches=[] if nonzero else [f+'('+x+')=0']
            parameter='no free parameter'
            steps.append('При c≠0 значения |c ln(2^(−n))|=|c|n ln 2 растут без границы. '
                         'Остаётся тождественный нуль, если он допускается исходными условиями.')
    if task.get('printed_claim') is not None:
        if zero_boundary:raise Unsupported('The printed claim must explicitly match the restriction at zero')
        claim=task['printed_claim'].replace(' ','')
        lhs=re.escape(f+'('+x+')=');v=re.escape(x)
        if not use_exp and not use_log and not nonzero:
            rhs=fr'([a-zA-Z])\*{v}(?:,\1={f}\(1\)arbitrary)?'
        elif not use_exp and use_log and nonzero:
            rhs=fr'([a-zA-Z])\^{v}(?:with\1={f}\(1\)>0)?'
            steps.append('Основание показательной функции равно exp(c)='+f+'(1)>0. Каждое положительное основание допустимо.')
        elif use_exp and not use_log and nonzero:
            rhs=fr'log_([a-zA-Z])\({v}\)'
            steps.append('При c≠0 положим a=exp(1/c)>0, a≠1. Тогда c ln('+x+')=log_a('+x+').')
        elif use_exp and use_log and nonzero:rhs=fr'{v}\^([a-zA-Z])'
        else:raise Unsupported('The proposed complete family omits or adds a parameter or exceptional branch')
        printed=re.fullmatch(lhs+rhs,claim)
        if not printed or printed[1] not in 'abckmp' or printed[1] in (f,x,y):
            raise Unsupported('The printed conclusion is not the derived family with a free parameter')
    return (dict(theorem='method.regular_real_homomorphism',coordinates=coordinates,source_group=expected,
                 regularity=regular,bounded_interval=bound,additive_function=core,steps=steps),
            dict(solutions=branches,parameter_domain=parameter))


def gaussian_affine(expr,atom):
    """Coefficients of B+A*t over Q[i]; preserve the source domain before taking a normal form."""
    def polynomial_term(e):
        if e[0] in ('s','q'):return True
        if e[0]=='pow':return e[2]>=0 and polynomial_term(e[1])
        return e[0] in ('mul','add') and all(polynomial_term(k) for k in e[1:])
    if not polynomial_term(expr):raise Unsupported('A complex factor has an unverified domain or singularity')
    p,_=m.rational_form(expr);rows=[[F(0),F(0)],[F(0),F(0)]];unit=('s','i')
    for mon,c in p.items():
        powers=dict(mon);j=powers.pop(atom,0);k=powers.pop(unit,0)%4
        if powers or j>1:raise Unsupported('An exact affine complex factor is required')
        rows[j][k%2]+=(-1 if k>=2 else 1)*c
    return rows


def complex_series_disk(task,lib):
    import ast
    fields={'kind','source','id','term','index','variable','printed_assumptions','requested_output'}
    keys={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
    src=task.get('source',{});literal='Определить радиус и круг сходимости в комплексной области, z=x+iy.'
    var=re.fullmatch(r'([a-zA-Z]\w*) complex',task.get('variable',''))
    idx=re.fullmatch(r'([a-zA-Z]\w*)>=(\d+)',task.get('index',''))
    if (not lib.data.get('complex_coefficient_ratio') or set(task)-fields or not isinstance(src,dict) or set(src)-keys or
            src.get('literal_requirement',literal)!=literal or task.get('requested_output',['radius','open_disk'])!=['radius','open_disk']
            or task.get('printed_assumptions','none')!='none' or not var or not idx or int(idx[2])<1):
        raise Unsupported('A different complex source domain, requested boundary, or printed condition remains')
    z,n,start=('s',var[1]),('s',idx[1]),int(idx[2])
    if len({z,n,('s','i')})!=3:raise Unsupported('The complex variable, imaginary unit and index must be independent')
    text=task['term'];product=re.compile(r'product_\{([a-zA-Z]\w*)=1\.\.'+re.escape(idx[1])+r'\}\(')
    if re.search(r'\bprefix\b',text):raise Unsupported('Internal product notation cannot introduce a source binder')
    dummies=product.findall(text)
    if len(set(dummies))>1 or any(('s',k) in (z,n,('s','i')) for k in dummies):raise Unsupported('A distinct product index is required')
    text=product.sub('prefix(',text);text=re.sub(r'\b'+re.escape(idx[1])+r'!',r'factorial('+idx[1]+')',text)
    # Real-domain exponent simplification must never erase a pole such as 1/(1+i²).
    try:syntax=ast.parse(text.replace('^','**'),mode='eval')
    except (SyntaxError,ValueError) as exc:raise Unsupported('Unsupported complex term syntax') from exc
    for power in (p for p in ast.walk(syntax) if isinstance(p,ast.BinOp) and isinstance(p.op,ast.Pow)):
        if any(not isinstance(a,(ast.Name,ast.Load,ast.Constant,ast.BinOp,ast.UnaryOp,ast.Add,ast.Sub,ast.Mult,ast.USub,ast.UAdd))
               for a in ast.walk(power.right)):
            raise Unsupported('The original complex exponent has an unverified domain')
    term=m.parse(text,None,re.findall(r'[a-zA-Z]\w*',text),('factorial','prefix'))
    rate=F(1);degree=0;center=None;parts=[];ratio_start=start
    def norm(v):return sum(a*a for a in v)
    def record(e,sgn,case,order,weight):
        nonlocal rate,degree
        if not weight:raise Unsupported('A zero complex factor requires a separate branch')
        parts.append(dict(factor=e,orientation=sgn,rule=case,squared_ratio_order=order,leading_squared=q(weight)))
        rate*=weight**sgn;degree+=sgn*order
    def affine_nonzero(e,k,lo,finite_numerator=False):
        nonlocal ratio_start
        b,a=gaussian_affine(e,k);scale=norm(a)
        if not scale:
            if not norm(b):raise Unsupported('An original coefficient factor vanishes')
        else:
            j=-(a[0]*b[0]+a[1]*b[1])/scale
            if j.denominator==1 and j>=lo and all(c+j*d==0 for c,d in zip(b,a)):
                if not finite_numerator:
                    raise Unsupported('An original coefficient factor vanishes at index '+str(j))
                ratio_start=max(ratio_start,int(j)+1)
        return a,b
    def fixed_exponent(e):
        if e[0]=='s':return e not in (n,z) and e[1] not in dummies
        if e[0]=='q':return True
        if e[0]=='pow':return e[2]>=0 and fixed_exponent(e[1])
        return e[0] in ('mul','add') and all(fixed_exponent(c) for c in e[1:])
    def visit(e,sgn,denominator=False):
        nonlocal center
        op=e[0]
        if op in ('mul','div'):
            if op=='div' and m.contains(e[2],z):raise Unsupported('The original term divides by a function of the complex variable')
            visit(e[1],sgn,denominator)
            visit(e[2],sgn if op=='mul' else -sgn,denominator or op=='div');return
        if op=='rpow' and e[2]==n:
            b,a=gaussian_affine(e[1],z);scale=norm(a)
            if scale:
                if center is not None or sgn!=1:raise Unsupported('The original series needs a single affine power')
                center=[q(-(a[0]*b[0]+a[1]*b[1])/scale),q((a[1]*b[0]-a[0]*b[1])/scale)]
            record(e,sgn,'affine_power' if scale else 'constant_geometric_power',0,scale or norm(b));return
        if m.contains(e,z):raise Unsupported('A complex abscissa occurs outside the common power')
        if op=='factorial' and e[1]==n:record(e,sgn,'successive_factorial',2,F(1));return
        if op=='prefix' and dummies:
            a,b=affine_nonzero(e[1],('s',dummies[0]),1)
            record(e,sgn,'last_factor_of_finite_product',2 if norm(a) else 0,norm(a) or norm(b));return
        if op=='rpow' and e[1]==n and fixed_exponent(e[2]):
            record(e,sgn,'positive_integer_to_fixed_complex_power',0,F(1));return
        affine_nonzero(e,n,start,not denominator);record(e,sgn,'successive_affine_coefficients',0,F(1))
    visit(term,1)
    if center is None:raise Unsupported('No power of the displaced complex variable')
    radius2=ZERO if degree>0 else '+inf' if degree<0 else q(1/rate)
    return (dict(theorem='method.complex_coefficient_ratio',source_index=[idx[1],start],ratio_start=ratio_start,factors=parts,
                 squared_ratio_degree=degree,leading_squared=q(rate),center=center),
            dict(variable=var[1],center=center,radius_squared=radius2,radius=radius2 if degree else m.simplify(('sqrt',radius2)),
                 disk='center_only' if degree>0 else 'whole_plane' if degree<0 else 'open_disk'))


def coefficient_rows(p,atom):
    rows={}
    for mon,c in p.items():
        powers=dict(mon);k=powers.pop(atom,0)
        rows.setdefault(k,{})[tuple(powers.items())]=c
    return {k:m.poly_expr(parts) for k,parts in rows.items()}


def rational_tail(e,atom):
    """Finite value when the leading coefficient does not vanish; None means unbounded magnitude."""
    form=m.rational_form(e)
    if any(k!=atom and m.contains(k,atom) for part in form for mon in part for k,_ in mon):raise poly.NotRational()
    p,d=(coefficient_rows(part,atom) for part in form);j=max(d);i=max(p,default=-1)
    return (q(0) if i<j else m.div(p[i],d[j]) if i==j else None),d[j]


def evaluate_boundary(expr,x,a,dummy):
    if isinstance(a,str):return rational_tail(expr,x)[0]
    return rational_tail(m.substitute(expr,{x:m.add(a,m.div(q(1),dummy))}),dummy)[0]


def guards_on(x,a,b,lc=False,rc=False):
    guards=[]
    if a!='-inf':guards.append(('nonnegative' if lc else 'positive',m.add(x,m.neg(a))))
    if b!='+inf':guards.append(('nonnegative' if rc else 'positive',m.add(b,m.neg(x))))
    return guards


def prove_original_domain(raw,variables,constraints):
    n,x=tuple(('s',v) for v in variables)
    domain_proofs=[]
    for kind,g in domain_conditions(raw):
        if kind not in ('nonzero','nonnegative','positive'):raise Unsupported('A different raw-domain predicate must be verified')
        invalid=('zero',g) if kind=='nonzero' else ('nonnegative' if kind=='positive' else 'positive',m.neg(g))
        for part in m.rational_form(g):
            if any(atom not in (n,x) for mon in part for atom,_ in mon):raise Unsupported('Unproved rational source restriction')
        region,proj=decomposition([*constraints,invalid],variables)
        if any(s['fibers'] for s in region['slabs']+region['sections']):raise Unsupported('Domain for every positive integer and original abscissa is unproved')
        domain_proofs.append(dict(required=(kind,g),projection=proj,excluded_cells=region))
    return domain_proofs


def rational_uniform(t,v,raw,interval,request):
    from graphs import ordered_cuts
    index,var=v;n,x=(('s',k) for k in v);a,b,lc,rc=interval
    P,D=m.rational_form(raw)
    if any(atom not in (n,x) for part in (P,D) for mon in part for atom,_ in mon):raise Unsupported('Expected a rational function of the index and abscissa')
    original=guards_on(x,a,b,lc,rc);original.append(('nonnegative',m.add(n,q(-1))))
    domain_proofs=prove_original_domain(raw,v,original)
    generic,leading=rational_tail(raw,n)
    if generic is None:raise Unsupported('The generic finite pointwise limit does not exist')
    coefficients=poly.univariate_coefficients(m.rational_form(leading)[0],x)
    if coefficients is None:raise Unsupported('The exceptional pointwise set remains unresolved')
    endpoints=[line.read_endpoint(k) if isinstance(k,str) else line.Quadratic(m.num(k)) for k in (a,b)]
    extra=ordered_cuts(rational_roots(coefficients))
    if any(k.b for k in extra):raise Unsupported('An algebraic exceptional abscissa is outside this rational certificate')
    exceptional=[q(k.a) for k in extra if line.compare(endpoints[0],k)<=0 and line.compare(k,endpoints[1])<=0]
    special=[]
    for k in exceptional:
        if k==a and not lc or k==b and not rc:continue
        value,_=rational_tail(m.substitute(raw,{x:k}),n)
        if value is None:raise Unsupported('No finite pointwise limit at an exceptional point')
        special.append(dict(x=k,value=value))
    error=m.simplify(m.add(raw,m.neg(generic)))
    p,d=m.rational_form(error)
    def diff(part):
        return m.poly_expr({tuple((a,k-int(a==x)) for a,k in mon if a!=x or k>1):c*dict(mon)[x]
                            for mon,c in part.items() if x in dict(mon)})
    deriv=m.add(m.mul(diff(p),m.poly_expr(d)),m.neg(m.mul(m.poly_expr(p),diff(d))))
    candidate_values={};stages=[];dummy=('s','__uniform_boundary')
    while dummy in (n,x):dummy=('s',dummy[1]+'_')
    def check(position,value):
        if value not in candidate_values:
            if value is None:limit='+inf'
            else:
                try:result,_=rational_tail(value,n)
                except poly.NotRational:result=value
                if result is None:limit='+inf'
                elif m.num(m.simplify(result)) is not None:limit=q(abs(m.num(m.simplify(result))))
                else:
                    job=dict(kind='limit',expression=source(value),variable=index,variable_domain='positive_integers',approach={'point':'+inf','side':'positive_infinity'})
                    proved=freeze(request('limiting error along an endpoint or critical branch',job)['value'])
                    if proved in ('+inf','-inf'):limit='+inf'
                    elif m.num(proved) is not None:limit=q(abs(m.num(proved)))
                    else:raise Unsupported('The certified error values cannot yet be compared exactly')
            candidate_values[value]=limit
        return dict(position=position,signed_error=value,limit_magnitude=candidate_values[value])
    edges=[a,*[k for k in exceptional if k!=a and k!=b],b]
    for lo,hi in zip(edges,edges[1:]):
        if lo==hi:continue
        checks=[check(k,evaluate_boundary(error,x,k,dummy)) for k in (lo,hi)]
        basis=[];requirements=factors_and_conditions([*guards_on(x,lo,hi),('zero',deriv)],v,basis)
        polys=projection(basis)
        bound=max([1]+[1+ceil(max(abs(c/p[-1]) for c in p[:-1])) for p in polys])
        stationary=fiber(basis,[requirements],F(bound+1),False,index)
        for l,h,_,_ in stationary['fibers']:
            if l==h:checks.append(check(l,m.simplify(m.substitute(error,{x:l}))))
            elif deriv!=q(0):raise Unsupported('The stationary set includes an unresolved open component')
        stages.append(dict(interval=(lo,hi),projection=[list(map(q,p)) for p in polys],index_after=bound,critical_fibers=stationary,tests=checks))
    isolated=[]
    for row in special:
        k=row['x'];isolated.append(check(k,m.add(m.substitute(raw,{x:k}),m.neg(row['value']))))
    if a==b and not special and lc and rc:isolated.append(check(a,m.substitute(error,{x:a})))
    if not candidate_values:raise Unsupported('The original interval has no points')
    limits=list(candidate_values.values());largest='+inf' if '+inf' in limits else q(max(map(m.num,limits)))
    return dict(method='rational_stationary_fibers',domain_proofs=domain_proofs,leading_denominator=leading,derivative_numerator=deriv,
                open_pieces=stages,isolated_points=isolated),dict(pointwise_limit=dict(generic=generic,exceptional=special),
                limit_of_supremum_error=largest,uniform=(largest==q(0)))


def power_profile(t,v,raw,interval):
    """Compact graph closure for R(x,x^n) on a nondegenerate subinterval of [0,1]."""
    from graphs import graph_curve
    from ray_proofs import compare_scalar
    name,var=v;n,x=(('s',k) for k in v);a,b,lc,rc=interval
    if (isinstance(a,str) or isinstance(b,str) or compare_scalar(a,ZERO)<0 or
            compare_scalar(a,b)>=0 or compare_scalar(b,ONE)>0):
        raise Unsupported('A nondegenerate subinterval of [0,1] is required for the power-profile argument')
    u=('s','__profile')
    while u in (x,n):u=('s',u[1]+'_')
    exps=[]
    def rewrite(e):
        if e[0]=='rpow':
            p,d=m.rational_form(e[2]);c=poly.univariate_coefficients(p,n)
            if e[1]!=x or d!={():F(1)} or c is None or len(c)!=2 or min(c)<0 or any(k.denominator!=1 for k in c):raise Unsupported('Expected a positive integer affine exponent of the coordinate')
            shift,factor=map(int,c)
            if not factor:raise Unsupported('Expected a positive index coefficient')
            if max(shift,factor)>m.MAX_INTEGER_POWER:raise poly.ResourceBound('Profile exponent exceeds the scalar integer-power grammar')
            guards=guards_on(x,a,b,lc,rc)+[('nonnegative',m.add(n,q(-1)))]
            exps.append(dict(original=e[2],factor=factor,shift=shift,minimum=factor+shift,
                             domain=prove_original_domain(e[2],v,guards)))
            return ('mul',('pow',u,factor),('pow',x,shift)) if shift else ('pow',u,factor)
        if e==n or e[0] not in ('s','q','add','mul','div','pow'):raise Unsupported('The remaining power profile must be rational and independent of the index')
        return (e[0],*(rewrite(c) if isinstance(c,tuple) else c for c in e[1:]))
    profile=rewrite(raw)
    if not exps:raise Unsupported('An actual positive integer power profile is required')
    domain=prove_original_domain(profile,(var,u[1]),guards_on(x,a,b,True,True)+guards_on(u,q(0),q(1),True,True))
    generic=m.simplify(m.substitute(profile,{u:q(0)}));special=[];curve=None;values=[]
    if compare_scalar(b,ONE)==0:
        endpoint=m.simplify(m.substitute(profile,{u:q(1),x:q(1)}))
        if rc:special.append(dict(x=q(1),value=endpoint))
        boundary=m.add(m.substitute(profile,{x:q(1)}),m.neg(m.substitute(generic,{x:q(1)})))
        curve=graph_curve(m.substitute(boundary,{u:('v',u[1])}),u[1])
        values=[dict(position=q(i),signed_error=m.simplify(m.substitute(boundary,{u:q(i)}))) for i in (0,1)]
        for cut in curve['cuts']:
            point=line.read_endpoint(cut['x'])
            if point.sign()>0 and line.compare(point,line.Quadratic(1))<0:
                values.append(dict(position=yterm(point),signed_error=cut['y']))
    maximum=line.Quadratic(0)
    for row in values:
        z=row['signed_error'];y=line.Quadratic(m.num(z)) if m.num(z) is not None else line.read_endpoint(z)
        row['signed_error']=yterm(y);y=y.neg() if y.sign()<0 else y
        if line.compare(y,maximum)>0:maximum=y
    return dict(method='power_profile',profile=profile,profile_coordinate=u[1],positive_integer_exponents=exps,
                closed_rectangle_domain=domain,power_base_interval=(a,b),critical_boundary_graph=curve,
                boundary_error_values=values),dict(pointwise_limit=dict(generic=generic,exceptional=special),
                limit_of_supremum_error=yterm(maximum),uniform=not maximum.sign())


def affine_profile(raw,n,x,u):
    value=raw;amplitude=q(1)
    while value[0] in ('mul','div'):
        a,b=value[1:]
        if value[0]=='mul' and not m.contains(a,x):amplitude=m.mul(amplitude,a);value=b
        elif not m.contains(b,x):
            amplitude=(m.mul if value[0]=='mul' else m.div)(amplitude,b);value=a
        else:break
    nodes=[value]
    while nodes:
        arg=nodes.pop();nodes.extend(c for c in arg[1:] if isinstance(c,tuple))
        if not m.contains(arg,x) or not m.contains(arg,n):continue
        profile=m.substitute(value,{arg:u})
        if m.contains(profile,n) or m.contains(profile,x):continue
        p,d=m.rational_form(arg)
        if any(atom not in (n,x) for part in (p,d) for mon in part for atom,_ in mon):continue
        P,D=coefficient_rows(p,x),coefficient_rows(d,x)
        if set(D)!={0} or max(P,default=0)!=1:continue
        return profile,amplitude,m.div(P[1],D[0]),m.div(P.get(0,q(0)),D[0])
    raise Unsupported('No single affine argument with an independent scalar multiplier')


def rational_asymptote(e,n,ctx):
    form=m.rational_form(e);allowed={n,*(('s',p) for p in ctx.get('parameters',()))}
    if any(atom not in allowed for part in form for mon in part for atom,_ in mon):raise Unsupported('A rational index scale or offset is required')
    p,d=(coefficient_rows(z,n) for z in form)
    if not p:return q(0),0
    j,k=max(p),max(d);head=m.div(p[j],d[k]);sign=m.sign(head,ctx)
    if j<=k:return (q(0) if j<k else head),sign
    if sign not in (-1,1):raise Unsupported('The sign of a leading index coefficient is unproved')
    return ('+inf' if sign>0 else '-inf'),sign


def affine_uniform(t,v,raw,interval,request,param_ctx):
    index,var=v;n,x=(('s',z) for z in v);lo,hi,lc,rc=interval;u=('s','__profile')
    while u in (n,x):u=('s',u[1]+'_')
    if lo==hi:raise Unsupported('A nondegenerate source interval is required')
    H,A,a,b=affine_profile(raw,n,x,u)
    restricted=() if t.get('parameters') else guards_on(x,lo,hi,lc,rc)
    domain=prove_original_domain(raw,v,[*restricted,('nonnegative',m.add(n,q(-1)))])
    amplitude,_=rational_asymptote(A,n,param_ctx);scale,orientation=rational_asymptote(a,n,param_ctx);shift,_=rational_asymptote(b,n,param_ctx)
    if isinstance(amplitude,str) or not orientation:raise Unsupported('A finite amplitude and a nonzero eventual dilation are required')
    def endpoint(e):
        if isinstance(e,str):return e if orientation>0 else '-inf' if e=='+inf' else '+inf'
        return m.add(m.mul(a,e),b)
    def limit(e):return e if isinstance(e,str) else rational_asymptote(e,n,param_ctx)[0]
    L,R=(endpoint(lo),endpoint(hi)) if orientation>0 else (endpoint(hi),endpoint(lo))
    left,right=limit(L),limit(R)
    plan=dict(method='moving_affine_profile',profile=H,profile_coordinate=u[1],amplitude=A,slope=a,offset=b,
              limiting_amplitude=amplitude,moving_open_interval=(L,R),limiting_open_interval=(left,right),domain_proofs=domain)
    ctx=m.context({'variable':u[1]})
    def point(arg):
        if not isinstance(arg,str):
            at=m.substitute(H,{u:arg})
            if m.constant_defined(at,ctx):return m.simplify(at)
            def side(e,unbounded):
                if isinstance(e,str):return unbounded
                return rational_asymptote(m.add(e,m.neg(arg)),n,param_ctx)[1]
            approach='right' if side(L,-1)>=0 else 'left' if side(R,1)<=0 else 'both'
        else:approach='positive_infinity' if arg=='+inf' else 'negative_infinity'
        task=dict(kind='limit',variable=u[1],expression=source(H),approach={'point':arg if isinstance(arg,str) else source(arg),'side':approach})
        value=freeze(request('scalar limit of the continuous profile',task)['value'])
        if isinstance(value,str):raise Unsupported('The limiting profile value must be finite')
        return value
    def output(g,sup,special=()):
        return plan,dict(pointwise_limit=dict(generic=g,exceptional=list(special)),limit_of_supremum_error=sup,uniform=sup==q(0))
    def bounds(l,h):
        if H in (('sin',u),('cos',u)) and (isinstance(l,str) or isinstance(h,str)):
            return q(-1),q(1),True,True
        if any(not isinstance(z,str) and m.num(z) is None for z in (l,h)):raise Unsupported('Symbolic image bounds require another comparison')
        interval='('+','.join(k if isinstance(k,str) else source(k) for k in (l,h))+')'
        task=dict(kind='function_bounds',variable=u[1],function=source(H),given_domain=interval,requested_output=['infimum','supremum'])
        proof=request('sharp function bounds on the limiting argument interval',task)['value']
        low,high=(proof[key] for key in ('infimum','supremum'))
        return freeze(low['value']),freeze(high['value']),low['attained'],high['attained']
    if amplitude==q(0):
        spread=bounds('-inf','+inf')
        if any(isinstance(z,str) for z in spread[:2]):raise Unsupported('A bounded profile is required for the vanishing multiplier')
        plan.update(reason='bounded_profile_and_vanishing_amplitude',profile_bounds=spread)
        return output(q(0),q(0))
    if left==right:
        plan['reason']='entire_interval_approaches_one_argument'
        return output(m.mul(amplitude,point(left)),q(0))
    special=[]
    if not isinstance(scale,str) and not isinstance(shift,str):
        if scale!=q(0):
            if isinstance(lo,str) or isinstance(hi,str):raise Unsupported('Uniform continuity of a varying affine argument on an unbounded interval is unproved')
            if domain_conditions(H):raise Unsupported('Uniform continuity on a compact neighborhood of the argument must be verified')
            plan['reason']='compact_affine_convergence_and_continuity'
            return output(m.mul(amplitude,m.substitute(H,{u:m.add(m.mul(scale,x),shift)})),q(0))
        fixed=shift
    elif not isinstance(scale,str):fixed=shift
    else:
        pivot=limit(m.div(m.neg(b),a))
        def ordered(e):
            if isinstance(e,str):return e
            if m.num(e) is None:raise Unsupported('A parameter-dependent transition abscissa requires case analysis')
            return line.Quadratic(m.num(e))
        if line.compare(ordered(pivot),ordered(lo))<=0:fixed=scale
        elif line.compare(ordered(pivot),ordered(hi))>=0:fixed='-inf' if scale=='+inf' else '+inf'
        else:raise Unsupported('Different pointwise regimes on the two sides of an interior pivot')
        if (pivot==lo and lc or pivot==hi and rc) and not isinstance(pivot,str):
            special.append(dict(x=pivot,value=m.mul(amplitude,point(limit(endpoint(pivot))))))
    if domain_conditions(H):raise Unsupported('The moving image needs continuity through its finite limiting endpoints')
    p=m.mul(amplitude,point(fixed));low,high,at_low,at_high=spread=bounds(left,right)
    plan.update(reason='limiting_argument_interval_image',fixed_argument_limit=fixed,profile_bounds=spread)
    if any(isinstance(z,str) for z in (low,high)):return output(p,'+inf',special)
    distances=[m.add(m.mul(amplitude,end),m.neg(p)) for end in (low,high)]
    if q(0) in distances:
        # A nonempty range with an unattained bound has strictly positive width.
        width=m.mul(q(abs(m.num(amplitude))),m.add(high,m.neg(low)))
        if not (at_low and at_high) or m.sign(width,ctx) in (0,1):return output(p,width,special)
    largest=q(0)
    for d in distances:
        s=m.sign(d,ctx)
        if s is None:raise Unsupported('The distance from the profile bound to the pointwise limit is undecided')
        if s<0:d=m.neg(d)
        larger=m.sign(m.add(d,m.neg(largest)),ctx)
        if larger is None:raise Unsupported('The endpoint errors cannot be ordered')
        if larger>0:largest=d
    return output(p,largest,special)


def uniform_sequence(t,lib,request):
    from graphs import interval_terms
    fields={'id','kind','schema','source','function','variable','index','interval','requested_output','conditions','parameters'}
    if (not lib.data.get('uniform_error_supremum') or set(t)-fields or
        set(t.get('requested_output',()))!={'pointwise_limit','uniform_convergence_classification','proof'}):
        raise Unsupported('Further requested conclusions require a separate argument')
    v=(t['index'],t.get('variable','x'));params=t.get('parameters',[])
    if v[0]==v[1] or set(v)&set(params):raise Unsupported('The index, evaluation coordinate and parameters must be distinct')
    for name in v:m.context({'variable':name})
    conditions=[]
    for rel in t.get('conditions',[]):
        match=re.fullmatch(r'finite interval ([A-Za-z_]\w*)<([A-Za-z_]\w*)',rel)
        if match and all(s in params for s in match.groups()):rel='('+match[2]+'-'+match[1]+')>0'
        conditions.append(rel)
    ctx=m.context({'variable':v[0],'parameters':params,'parameter_conditions':conditions})
    interval=interval_terms(t['interval'],ctx);raw=m.parse(t['function'],None,v)
    if not params and not conditions:
        if all(atom in [('s',name) for name in v] for part in m.rational_form(raw) for mon in part for atom,_ in mon):
            return rational_uniform(t,v,raw,interval,request)
        try:return power_profile(t,v,raw,interval)
        except Unsupported:
            if not lib.data.get('affine_uniform_profile'):raise
    if lib.data.get('affine_uniform_profile'):return affine_uniform(t,v,raw,interval,request,ctx)
    raise Unsupported('Parameter-dependent uniform convergence is unproved')


def uniform_report(r):
    t=r['task'];lines=['Равномерная сходимость   '+(t.get('function') or 'Кусочная функция')+', '+str(t.get('interval','')),r['status']]
    if r.get('value') is None:return '\n'.join(lines+[r.get('reason','')])+'\n'
    v=r['value'];p=r['compilation'];g=v['pointwise_limit'];show=lambda e:m.render(freeze(e)) if e is not None else 'неограниченная ошибка'
    if p['method']=='elementary_uniform_error':
        lines.append(p['argument'])
        if not isinstance(g,dict):lines.append('Поточечный предел '+show(g)+'.')
        if v['uniform_error_bound']:lines.append('Граница ошибки '+v['uniform_error_bound']+'.')
        if not p.get('original_domain_failure'):
            lines.append('Сходимость равномерная.' if v['uniform'] else 'Сходимость неравномерная.')
        return '\n'.join(lines)+'\n'
    lines.append('Поточечный предел равен '+show(g['generic'])+'.')
    for k in g['exceptional']:lines.append('При '+t.get('variable','x')+' = '+show(k['x'])+' значение предела '+show(k['value'])+'.')
    if p['method']=='moving_affine_profile':
        lines.append('Профиль '+show(p['profile'])+' в аргументе '+show(p['slope'])+'·'+t.get('variable','x')+' + '+show(p['offset'])+', множитель '+show(p['amplitude'])+'.')
        lines.append('Предельные концы промежутка аргумента '+', '.join(map(show,p['limiting_open_interval']))+'.')
        reasons={'bounded_profile_and_vanishing_amplitude':'Множитель стремится к нулю, профиль ограничен на всей области.',
                 'entire_interval_approaches_one_argument':'Весь промежуток входит в окрестность одного предельного аргумента.',
                 'compact_affine_convergence_and_continuity':'Аффинные аргументы сходятся равномерно на ограниченном промежутке, а профиль равномерно непрерывен на его компактной окрестности.',
                 'limiting_argument_interval_image':'Каждое внутреннее значение предельного промежутка достижимо на хвосте. Исходная непрерывность даёт значения на конечных границах.'}
        lines.append(reasons[p['reason']])
        if 'profile_bounds' in p:
            a,b,lc,rc=p['profile_bounds'];lines.append('Границы профиля '+('[' if lc else '(')+show(a)+', '+show(b)+(']' if rc else ')')+'.')
    elif p['method']=='power_profile':
        lines.append('Целые положительные показатели дают профиль '+show(p['profile'])+' в координате '+p['profile_coordinate']+'.')
        if p['critical_boundary_graph'] is None:lines.append('Весь промежуток отделён от 1. Степень стремится к нулю равномерно, а профиль непрерывен на замкнутом прямоугольнике.')
        else:
            lines.append('Внутри промежутка степень стремится к нулю. При приближении к 1 возможны все предельные значения степени от 0 до 1. Максимум ошибки вычислен по концам и критическим точкам граничного профиля.')
            for row in p['boundary_error_values']:lines.append('Координата '+show(row['position'])+'   ошибка '+show(row['signed_error']))
    else:
        lines.append('Пределы степенных коэффициентов определяют поточечный предел. На каждом открытом промежутке проверены граничные значения и все критические точки ошибки.')
        for part in p['open_pieces']:
            lines.append('Промежуток ('+', '.join(map(show,part['interval']))+'). При индексе больше '+str(part['index_after'])+' число и порядок критических точек постоянны.')
            for row in part['tests']:lines.append(show(row['position'])+'   ошибка '+show(row['signed_error'])+'   предел модуля '+show(row['limit_magnitude']))
    lines.append('Предел верхней грани модуля ошибки равен '+show(v['limit_of_supremum_error'])+'.')
    lines.append('Последовательность сходится равномерно.' if v['uniform'] else 'Последовательность сходится неравномерно.')
    return '\n'.join(lines)+'\n'


def uniform_series_source(task,character=False,majorant=False):
    origin=task.get('source',{})
    keys={'exercise','pdf_page','printed_page','pdf_sha256','page_png_sha256','printed_subpart','literal_requirement','printed_hint','explicit_required_method'}
    if not isinstance(origin,dict) or set(origin)-keys:return False
    if origin.get('explicit_required_method') not in ((None,'weierstrass_majorant') if majorant else (None,)):return False
    text=origin.get('literal_requirement')
    if text is None:return True
    if not isinstance(text,str):return False
    text=re.sub(r'\s*\(стр\.\s*\d+\)\s*\.$','.',text)
    if character:return text=='Исследовать характер сходимости следующих рядов.'
    return text in ('Исследовать на равномерную сходимость в указанных промежутках следующие функциональные ряды.',
                    'Исследовать равномерную сходимость на указанном промежутке.') or (majorant and
            text=='Пользуясь признаком Вейерштрасса, доказать равномерную сходимость в указанных промежутках следующих функциональных рядов.')


def uniform_series_majorant(task,library):
    """Bound the absolute term by C/n^p using homogeneous monomials and weighted AM–GM."""
    from itertools import combinations
    from graphs import rational_interval
    fields={'kind','id','source','term','index','variable','start_index','interval','parameters','conditions','method_requirement','requested_output'}
    n,x=task['index'],task['variable'];start=task['start_index']
    if (library.data.get('task_compilers',{}).get(task['kind'])!='weierstrass_power_majorant' or set(task)-fields
        or task.get('requested_output')!=['uniform_convergence','proof'] or task.get('method_requirement','weierstrass_majorant')!='weierstrass_majorant'
        or not uniform_series_source(task,majorant=True) or task.get('parameters') or task.get('conditions') or type(start) is not int or start<1 or n==x):
        raise Unsupported('Unrecognized index, interval, method or uniform-series obligation')
    lo,hi,lc,rc=rational_interval(task['interval'])
    if lo==hi and not (lc and rc):raise Unsupported('A nonempty interval is required')
    pos=lo!='-inf' and lo.sign()>=0
    conditions=[n+'>0']+([x+'>0'] if pos else [])
    dummy='__majorant_dummy'
    while dummy in (n,x):dummy+='_'
    ctx=m.context({'variable':dummy,'parameters':[n,x],'parameter_conditions':conditions})
    raw=m.parse(task['term'],None,[n,x]);guards=domain_conditions(raw)
    if not all(known_guard(g,ctx) for g in guards):raise Unsupported('The original term has an unproved domain on the comparison set')
    if pos and not lo.sign() and lc and not all(known_guard((r,m.substitute(e,{('s',x):ZERO})),ctx) for r,e in guards):
        raise Unsupported('The original term is not proved defined at the included origin')
    def monomials(e,lower):
        # Each lower term is a separate bound. An upper bound has a single term.
        op=e[0]
        if op=='q':
            c=m.num(e)
            if lower and c<=0:raise Unsupported('Strictly positive monomial coefficient required')
            return [(abs(c),0,0)]
        if e==('s',n):return [(1,1,0)]
        if e==('s',x):return [(1,0,1)]
        if not lower and op in ('sin','cos'):return [(1,0,0)]
        if not lower and op=='abs':return monomials(e[1],False)
        if not lower and op=='add':
            (a,p,j),=monomials(e[1],False);(b,r,h),=monomials(e[2],False)
            if j!=h:raise Unsupported('No uniform monomial envelope for this sum')
            return [(a+b,max(p,r),j)]
        if lower and op=='add':
            if not all(known_guard(('nonnegative',t),ctx) for t in e[1:]):raise Unsupported('The denominator summands need global signs')
            return monomials(e[1],True)+monomials(e[2],True)
        if op=='mul':
            return [(a*b,i+j,h+k) for a,i,h in monomials(e[1],lower) for b,j,k in monomials(e[2],lower)]
        if op in ('pow','sqrt','cbrt'):
            power=F(e[2]) if op=='pow' else F(1,2 if op=='sqrt' else 3)
            if power<0:raise Unsupported('A negative power needs a nonvanishing lower envelope')
            def scale(c):
                if power.denominator==1:return c**int(power)
                return (min(1,c) if lower else max(1,c))**ceil(power)
            return [(scale(c),p*power,j*power) for c,p,j in monomials(e[1],lower)]
        raise Unsupported('No certified monomial envelope for '+op)
    value=raw[1] if raw[0]=='atan' else raw
    num,den=value[1:] if value[0]=='div' else (value,ONE)
    try:upper,=monomials(num,False)
    except Unsupported:upper,=monomials(m.simplify(num),False)
    lower=monomials(den,True)
    C,s,k=upper;choices=[]
    for a,p,j in lower:
        if j==k:choices.append((p-s,F(C,a),(a,p,j),None,F(0)))
    for left,right in combinations(sorted(lower,key=lambda z:z[2]),2):
        a,p,j=left;b,r,h=right
        if j<k<h:
            w=F(k-j,h-j)
            choices.append(((1-w)*p+w*r-s,F(C,min(a,b)),left,right,w))
    if not choices:raise Unsupported('The spatial factor cannot be bounded independently of the source point')
    p,C,left,right,w=max(choices,key=lambda choice:(choice[0],-choice[1]))
    if p<=1:raise Unsupported('The available numerical majorant does not prove summability')
    code=lambda mon:[q(z) for z in mon]
    proof=dict(original_domain=guards,comparison_interval=task['interval'],index_lower_bound=start,
               absolute_numerator_envelope=code(upper),denominator_envelopes=[code(left)]+([code(right)] if right else []),
               geometric_weight=q(w),outer_bound='absolute_arctangent_le_absolute_argument' if raw[0]=='atan' else 'identity',
               comparison_at_zero='continuity of the original term and constant spatial majorant',
               tail_integral_coefficient=q(F(C,p-1)),tail_integral_exponent=q(1-p))
    return proof,dict(classification='absolutely_and_uniformly_convergent',criterion='weierstrass_majorant',
                      majorant_coefficient=q(C),majorant_decay_power=q(p),from_index=start)


def uniform_periodic_tail(task,library,receipt=None):
    """Sum by parts with a bounded discrete primitive and a positive monotone amplitude."""
    from finite_sums import coefficients,periodic_phases
    from graphs import interval_terms
    from math import lcm
    output=task.get('requested_output')
    allowed={'id','kind','source','term','variable','index','interval','start_index','printed_conditions','requested_output'}
    start=task['start_index'];n=task['index'];x=task['variable']
    if (not library.data.get('uniform_periodic_tail') or set(task)-allowed or
            not uniform_series_source(task) or
            output not in (['uniform_convergence_classification','proof'],['uniform_convergence','proof']) or
            type(start)!=int or start<1 or n==x or
            task.get('printed_conditions',f'lower index {start}.')!=f'lower index {start}.'):
        raise Unsupported('Uncovered source conditions or a prescribed test for the functional series')
    for name in (n,x):m.context(dict(variable=name))
    raw=m.parse(task['term'],n,[x]);idx=('v',n);spatial=('s',x)
    if raw[0]!='div':raise Unsupported('The original term has no separated numerator and denominator')
    wave,base=raw[1:];root=2 if base[0]=='sqrt' else 3 if base[0]=='cbrt' else 1
    if root>1:base=base[1]
    if base[0]!='add':raise Unsupported('No growing polynomial plus a spatial offset in the denominator')
    dependent=[e for e in base[1:] if m.variable_in(e,n)]
    if len(dependent)!=1:raise Unsupported('The spatial offset must be independent of the index')
    polynomial=dependent[0];offset=base[2] if polynomial==base[1] else base[1]
    co=coefficients(polynomial,n,start)
    if len(co)<2 or any(c<0 for c in co[1:]):raise Unsupported('No increasing polynomial on the source index tail')
    notation=task['interval']
    match=re.fullmatch(r'abs\('+re.escape(x)+r'\)<=([0-9]+)',notation)
    if match:notation='[-'+match[1]+','+match[1]+']'
    ctx=m.context(dict(variable=n,parameters=[x]));lo,hi,lc,rc=interval_terms(notation,ctx)
    def on_interval(predicate,expr):
        if known_guard((predicate,expr),ctx):return True
        try:return interval_guard(predicate,m.substitute(expr,{spatial:('v',x)}),x,(lo,hi,lc,rc),ctx)
        except Unsupported:return False
    if not all(on_interval(op,g) for op,g in domain_conditions(offset)):
        raise Unsupported('A spatial offset has an original pole on the given interval')
    if offset==spatial and lo!='-inf' and m.num(lo) is not None:floor=m.num(lo)
    elif m.known_nonnegative(offset,ctx) or on_interval('nonnegative',offset):floor=F(0)
    elif offset[0] in ('sin','cos'):floor=F(-1)
    else:raise Unsupported('No lower bound uniform in the original spatial variable')
    initial=sum(c*start**i for i,c in enumerate(co))+floor
    if initial<=0:raise Unsupported('The original denominator can vanish at the initial index')
    if wave[0]=='rpow' and wave[1]==q(-1):
        co_phase=coefficients(wave[2],n,start)
        if len(co_phase)>3 or any(2%c.denominator for c in co_phase):
            raise Unsupported('A parity period is not certified for this index polynomial')
        period=2*lcm(*(c.denominator for c in co_phase))
        def phase(j):
            p=sum(c*j**i for i,c in enumerate(co_phase))
            if p.denominator!=1:raise Unsupported('The phase is not integral on every residue')
            return F((-1)**(p.numerator%2))
    else:
        phases=periodic_phases(wave,n)
        if wave not in phases:raise Unsupported('Unknown bounded periodic numerator')
        constant,slope,period=phases[wave]
        def phase(j):
            z=m.num(m.simplify((wave[0],m.mul(q((constant+slope*j)%2),m.PI))))
            if z is None:raise Unsupported('No exact real values for the whole period')
            return z
    values=[phase(j) for j in range(period)]
    if receipt is None:
        partial=[F(0)]
        for a in values:partial.append(partial[-1]+a)
    else:
        partial=[m.num(freeze(a)) for a in receipt['discrete_primitive']]
    if (len(partial)!=period+1 or partial[0]!=0 or partial[-1]!=0 or
        any(b-a!=v for a,b,v in zip(partial,partial[1:],values))):
        raise Unsupported('The proposed discrete primitive does not close over its entire period')
    bound=q(max(partial)-min(partial))
    lower=m.add(polynomial,q(floor))
    divisor=lower if root==1 else ('sqrt' if root==2 else 'cbrt',lower)
    major=m.div(bound,divisor)
    plan=dict(theorem='method.uniform_periodic_summation_by_parts',period=period,phase_values=[q(s) for s in values],
              discrete_primitive=[q(p) for p in partial],index_polynomial=polynomial,offset=offset,
              offset_lower_bound=q(floor),first_denominator_base_lower=q(initial),
              domain=[lo,hi,lc,rc],initial_index=start,root_degree=root,uniform_tail_from_index=major)
    return plan,dict(uniform=True,criterion='uniform_summation_by_parts',any_finite_tail_from_index_bound=major)


def uniform_telescoping_series(task,library,request,receipt=None):
    """Use a proved rational prefix as the sequence whose uniform convergence is requested."""
    from graphs import interval_terms
    from integrals import learned_nodes
    fields={'id','kind','source','term','variable','index','interval','start_index','printed_conditions','requested_output'}
    start=task.get('start_index');index,var=task['index'],task['variable']
    if (not library.data.get('uniform_rational_prefixes') or set(task)-fields or
            task.get('requested_output')!=['convergence_character','proof'] or type(start)!=int or start<1 or index==var or
            not uniform_series_source(task,character=True) or
            task.get('printed_conditions',f'lower index {start}.')!=f'lower index {start}.'):
        raise Unsupported('Additional hypotheses or convergence obligations need another argument')
    ctx=m.context(dict(variable=index,parameters=[var]));interval=interval_terms(task['interval'],ctx)
    n,x=('s',index),('s',var);variables=(index,var)
    raw=m.parse(task['term'],None,variables)
    if raw[0]!='div' or any(a not in (n,x) for part in m.rational_form(raw) for mon in part for a,_ in mon):
        raise Unsupported('A rational summand with an index-dependent denominator is required')
    domain=guards_on(x,*interval)+[('nonnegative',m.add(n,q(-start)))]
    # Applying the domain test to sqrt(u) also proves u>=0, so convergence is absolute.
    source_checks=prove_original_domain(('sqrt',raw),variables,domain)
    if receipt is None:
        candidate=None
        for base in learned_nodes(raw[2]):
            if not isinstance(base,tuple) or not m.contains(base,n):continue
            kernel=m.div(ONE,base)
            delta=m.add(kernel,m.neg(m.substitute(kernel,{n:m.add(n,ONE)})))
            if not m.rational_form(delta)[0]:continue
            num,den=m.rational_form(('div',raw,delta));scale=m.div(m.poly_expr(num),m.poly_expr(den))
            if m.contains(scale,n):continue
            candidate=m.mul(scale,kernel);break
        if candidate is None:raise Unsupported('No shifted reciprocal produces the original summand')
    else:candidate=freeze(receipt['potential'])
    candidate_checks=prove_original_domain(candidate,variables,domain)
    after=m.substitute(candidate,{n:m.add(n,ONE)})
    if m.rational_form(m.add(raw,m.neg(m.add(candidate,m.neg(after)))))[0]:
        raise Unsupported('The proposed potential has the wrong first difference')
    initial=m.substitute(candidate,{n:q(start)})
    last=m.simplify(m.substitute(candidate,{n:m.add(n,q(start))}))
    prefix=m.add(initial,m.neg(last))
    child=dict(kind='uniform_sequence_convergence',variable=var,index=index,function=source(last),interval=task['interval'],
               requested_output=['pointwise_limit','uniform_convergence_classification','proof'])
    result=request('pointwise limit and uniform error of the uncancelled upper boundary',child)['value']
    g=result['pointwise_limit'];pointwise=dict(generic=m.add(initial,m.neg(freeze(g['generic']))),exceptional=[
            dict(x=v['x'],value=m.add(m.substitute(initial,{x:freeze(v['x'])}),m.neg(freeze(v['value'])))) for v in g['exceptional']])
    return dict(theorem='method.uniform_rational_prefixes',source_sign_and_domain=source_checks,potential=candidate,
                original_potential_domain=candidate_checks,first_index=start,finite_sum_of_k_terms=prefix),dict(
                    pointwise_sum=pointwise,absolute_at_every_point=True,uniform=result['uniform'],
                    limit_of_supremum_error=result['limit_of_supremum_error'],criterion='uniform_finite_prefix')


def interval_guard(predicate,term,var,interval,ctx):
    """Prove a raw guard everywhere on the source interval, respecting its open ends."""
    from quadrature import enclose,guard_bounds
    a,b,lc,rc=interval
    if not m.variable_in(term):
        if known_guard((predicate,term),ctx):return ('parameter',term)
    if term==('v',var):
        for bound,closed,orientation in ((a,lc,1),(b,rc,-1)):
            if isinstance(bound,str):continue
            sign=m.sign(bound,ctx)
            if ((orientation==1 or predicate=='nonzero') and
                    (sign==orientation or sign==0 and (not closed or predicate=='nonnegative'))):
                return ('endpoint',bound,closed,orientation)
    if not isinstance(a,str) and not isinstance(b,str):
        # A linear function attains its extreme values at the endpoints of the closure.
        # A zero there is admissible for a strict guard only when the endpoint is open.
        if not domain_conditions(term):
            try:num,den=poly.rf(term,var)
            except poly.NotRational:pass
            else:
                if len(num)==2 and len(den)==1:
                    ends=[m.sign(m.substitute(term,{('v',var):z}),ctx) for z in (a,b)]
                    for direction in ((1,-1) if predicate=='nonzero' else (1,)):
                        if all(s==direction or s==0 and (predicate=='nonnegative' or not closed)
                               for s,closed in zip(ends,(lc,rc))):
                            return ('affine_endpoint_signs',*ends,lc,rc)
        left=enclose(a,None)[0];right=enclose(b,None)[1]
        return ('enclosure',*[q(v) for v in guard_bounds(predicate,term,(left,right),[var])])
    raise Unsupported('An original pointwise domain condition remains on the interval')


def modulus_estimate(raw,var,interval,ctx):
    """A proof tree for |f(u)-f(v)| <= C |u-v|^alpha on the whole interval."""
    from quadrature import enclose,guard_bounds
    x=('v',var);a,b,_,_=interval
    def absolute(e):return m.simplify(('abs',e))
    def upper(e):
        if not m.variable_in(e) and m.constant_defined(e,ctx):return absolute(e)
        if e[0] in ('sin','cos'):return ONE
        if e==x and not isinstance(a,str) and not isinstance(b,str):return m.add(absolute(a),absolute(b))
        if e[0]=='add':return m.add(upper(e[1]),upper(e[2]))
        if e[0]=='mul':return m.mul(upper(e[1]),upper(e[2]))
        if not isinstance(a,str) and not isinstance(b,str):
            lo,hi=enclose(e,(enclose(a,None)[0],enclose(b,None)[1]));return q(max(abs(lo),abs(hi)))
        raise Unsupported('No uniform magnitude bound for a factor')
    def lower(e):
        if not m.variable_in(e) and m.constant_defined(e,ctx) and m.nonzero(e,ctx):return absolute(e)
        if e==x and not isinstance(a,str) and m.sign(a,ctx)==1:return a
        if e==x and not isinstance(b,str) and m.sign(b,ctx)==-1:return m.neg(b)
        if not isinstance(a,str) and not isinstance(b,str):
            lo,hi=guard_bounds('nonzero',e,(enclose(a,None)[0],enclose(b,None)[1]),[var])
            if lo>0 or hi<0:return q(min(abs(lo),abs(hi)))
        raise Unsupported('No positive lower bound for the absolute denominator')
    def estimate(e):
        op=e[0];children=[];extra={}
        def child(f):
            z=estimate(f);children.append(z);return z['constant'],z['exponent']
        if not m.variable_in(e):
            if not m.constant_defined(e,ctx):raise Unsupported('Undefined constant')
            rule='constant';c,alpha=ZERO,ONE
        elif e==x:rule='identity';c,alpha=ONE,ONE
        elif op in ('sin','cos','atan','abs','sqrt','cbrt'):
            c,alpha=child(e[1]);rule='unit_lipschitz_'+op
            if op=='sqrt':
                rule='square_root_difference';c=m.simplify(('sqrt',c));alpha=m.mul(q(1,2),alpha)
            elif op=='cbrt':
                # 4(u²+uv+v²)−(u−v)²=3(u+v)² for u,v the real cube roots.
                rule='real_cube_root_difference';c=m.simplify(('cbrt',m.mul(q(4),c)));alpha=m.mul(q(1,3),alpha)
        elif op=='ln':
            positive=interval_guard('positive',e[1],var,interval,ctx)
            floor=lower(e[1]);c,alpha=child(e[1]);c=m.div(c,floor)
            rule='log_difference'
            extra.update(minimum_argument=floor,positive_argument=positive)
        elif op in ('add','mul'):
            u,v=e[1:];p,j=child(u);r,k=child(v)
            alpha=k if p==ZERO else j
            if p!=ZERO and r!=ZERO and j!=k:
                if isinstance(a,str) or isinstance(b,str):raise Unsupported('A bounded diameter is needed to lower a modulus exponent')
                diameter=m.add(b,m.neg(a))
                if not m.known_nonnegative(m.add(ONE,m.neg(diameter)),ctx):
                    raise Unsupported('The unit-diameter estimate does not apply on this interval')
                alpha=q(min(m.num(j),m.num(k)));extra['diameter_at_most_one']=diameter
            if op=='add':rule='triangle';c=m.add(p,r)
            else:
                rule='product_difference'
                left=ZERO if r==ZERO else upper(u);right=ZERO if p==ZERO else upper(v)
                extra['factor_bounds']=[left,right];c=m.add(m.mul(left,r),m.mul(right,p))
        elif op=='pow' and e[2]>=1:
            p,alpha=child(e[1]);degree=e[2];radius=upper(e[1]) if degree>1 else ONE
            extra.update(degree=degree,radius=radius);rule='factor_power_difference';c=m.mul(q(degree),m.mul(p,m.power(radius,degree-1)))
        elif op=='div':
            u,v=e[1:];p,j=child(u);r,k=child(v);d=lower(v)
            if p!=ZERO and r!=ZERO and j!=k:raise Unsupported('Incompatible quotient moduli')
            alpha=k if p==ZERO else j
            c=m.add(m.div(p,d),ZERO if r==ZERO else m.div(m.mul(upper(u),r),m.power(d,2)));extra['minimum_absolute_denominator']=d;rule='quotient_difference'
        else:raise Unsupported('Missing modulus rule for '+op)
        return dict(rule=rule,expression=e,constant=m.simplify(c),exponent=alpha,children=children,**extra)
    return estimate(raw)


def continuity_goal(t,lib,request,chart,saved=None):
    from graphs import interval_terms
    fields={'kind','id','source','variable','function','given_domain','requested_output','parameters','stated_conditions','assignments'}
    wanted=t.get('requested_output',[]);v=t['variable'];params=t.get('parameters',[]);facts=t.get('stated_conditions',[])
    outputs={'uniform_continuity','continuity','boundedness','unboundedness','sufficient_delta_for_each_positive_epsilon','prove_power_bound_for_modulus'}
    provenance={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','page_png_sha256'}
    origin=t.get('source',{})
    if (set(t)-fields or not isinstance(origin,dict) or set(origin)-provenance
            or not wanted or set(wanted)-outputs):
        raise Unsupported('Additional domain or mathematical request remains')
    raw=m.parse(t['function'],v,params);x=('v',v);ctx=m.context(dict(variable=v,parameters=params,parameter_conditions=facts))
    from integrals import learned_nodes
    continuous={'v','s','q','pi','add','mul','div','pow','rpow','abs','sqrt','cbrt','exp','ln','sin','cos','tan','cot','atan','asin','acos','sinh','cosh','tanh'}
    if any(n[0] not in continuous for n in learned_nodes(raw) if isinstance(n,tuple)):
        raise Unsupported('Continuity of a source constructor requires a separate proof')
    domains=t['given_domain'];multiple=isinstance(domains,list);domains=domains if multiple else [domains]
    if not domains:raise Unsupported('No source interval')
    assigned=t.get('assignments',{})
    if assigned and (assigned!={'0':'0'} or chart!='damped_reciprocal'):
        raise Unsupported('A separately assigned point needs its own continuity certificate')
    plans=[];answers=[]
    for notation in domains:
        interval=interval_terms(notation,ctx);a,b,lc,rc=interval
        if a=='+inf' or b=='-inf' or (not isinstance(a,str) and not isinstance(b,str) and m.sign(m.add(b,m.neg(a)),ctx)!=1):
            raise Unsupported('A nonempty ordered interval is required')
        if assigned and (a!=ZERO or not lc):raise Unsupported('The assigned point must be the included left endpoint')
        regular=(a,b,False,rc) if assigned else interval
        plan=dict(domain=notation,guards=[(op,g,interval_guard(op,g,v,regular,ctx)) for op,g in domain_conditions(raw)])
        result={}
        def limit_at(role,e,point,side,variable=v):
            z=dict(kind='limit',variable=variable,expression=source(e),approach=dict(point=point if isinstance(point,str) else source(point),side=side),
                   parameters=params,parameter_conditions=facts)
            return freeze(request(role,z)['value'])
        if chart in ('quantitative_modulus','damped_reciprocal'):
            if chart=='quantitative_modulus':tree=modulus_estimate(raw,v,interval,ctx)
            else:
                from verify import same_value
                if (raw[0]!='mul' or x not in raw[1:] or isinstance(a,str) or isinstance(b,str)
                        or not m.known_nonnegative(a,ctx)):raise Unsupported('A finite nonnegative interval and a damped phase are required')
                wave=raw[2] if raw[1]==x else raw[1]
                if wave[0] not in ('sin','cos'):raise Unsupported('The oscillating factor needs a uniform bound and a Lipschitz modulus')
                c=m.simplify(m.substitute(wave[1],{x:ONE}))
                if not m.constant_defined(c,ctx) or not same_value(wave[1],m.div(c,x)):raise Unsupported('The reciprocal phase was not identified')
                C=m.add(m.simplify(('sqrt',m.add(b,m.neg(a)))),m.simplify(('sqrt',m.mul(q(2),m.simplify(('abs',c))))))
                tree=dict(rule='damped_reciprocal',expression=raw,frequency=c,constant=C,exponent=q(1,2),extension=assigned)
            plan['estimate']=tree
            C,alpha=tree['constant'],tree['exponent']
            # The auxiliary epsilon is positive and distinct from the original parameters.
            eps='epsilon'
            while eps in [v,*params]:eps+='_'
            bound={'constant':C,'exponent':alpha}
            if 'prove_power_bound_for_modulus' in wanted:result['prove_power_bound_for_modulus']=bound
            if 'sufficient_delta_for_each_positive_epsilon' in wanted:
                result['sufficient_delta_for_each_positive_epsilon']=dict(variable=eps,positive=True,
                    delta=m.power(m.div(('s',eps),m.add(ONE,C)),int(1/m.num(alpha))))
            uniform=True
        elif chart=='closed_interval_extension':
            if any(isinstance(z,str) for z in (a,b)) or set(wanted)&{'sufficient_delta_for_each_positive_epsilon','prove_power_bound_for_modulus'}:
                raise Unsupported('Compactification cannot give the requested explicit tolerance here')
            limits=[]
            for end,closed,side in [(a,lc,'right'),(b,rc,'left')]:
                if closed:continue
                value=limit_at('finite extension at '+source(end),raw,end,side)
                if isinstance(value,str) or not m.constant_defined(value,ctx):raise Unsupported('An endpoint value is not finite')
                limits.append([end,value])
            plan['finite_extensions']=limits;uniform=True
        elif chart in ('endpoint_obstruction','right_endpoint_obstruction'):
            if set(wanted)-{'uniform_continuity','continuity'}:raise Unsupported('The endpoint obstruction does not establish all requests')
            if isinstance(a,str) or isinstance(b,str):raise Unsupported('Bounded interval required for the endpoint test')
            # Check one saved side at a time, without leaving failed child proofs in the successful plan.
            endpoint=((b,'left') if not rc else None) if chart=='right_endpoint_obstruction' else (
                (a,'right') if not lc else (b,'left') if not rc else None)
            if endpoint is None:raise Unsupported('No missing endpoint')
            end,side=endpoint;value=limit_at('endpoint obstruction to Cauchy continuity',raw,end,side)
            if value not in ('+inf','-inf'):raise Unsupported('No divergent endpoint found')
            plan['divergent_limit']=[end,value];uniform=False
        elif chart=='separated_values':
            if set(wanted)&{'sufficient_delta_for_each_positive_epsilon','prove_power_bound_for_modulus'}:
                raise Unsupported('A counterexample cannot supply the requested quantitative modulus')
            plan['sequences']=separated_arguments(raw,v,interval,ctx,limit_at);uniform=False
        else:raise Unsupported('Unknown continuity transition')
        if 'continuity' in wanted:result['continuity']=True
        if 'uniform_continuity' in wanted:result['uniform_continuity']=uniform
        if 'boundedness' in wanted:
            if raw[0] in ('sin','cos'):plan['range_bound']=[q(-1),ONE]
            elif chart=='closed_interval_extension':plan['bounded_by_compact_extension']=True
            else:raise Unsupported('Boundedness requires a separate proof')
            result['boundedness']=True
        if 'unboundedness' in wanted:
            if b!='+inf':raise Unsupported('Unboundedness still needs a witness')
            leading=raw
            if raw[0]=='add':
                for i in (1,2):
                    if raw[i][0] in ('sin','cos'):
                        leading=raw[3-i];plan['bounded_remainder']=(raw[i],[q(-1),ONE]);break
            value=limit_at('unbounded values on the original interval',leading,'+inf','positive_infinity')
            if value not in ('+inf','-inf'):raise Unsupported('Infinite endpoint behavior not established')
            result['unboundedness']=True;plan['unbounded_limit']=value
        if set(result)!=set(wanted):raise Unsupported('A requested property remains open')
        plans.append(plan);answers.append(result)
    return dict(chart=chart,intervals=plans),answers if multiple else answers[0]


def jump_witness(*,tolerance_floor=None,inverse=False):
    """At zero test affine branches A*t and A*t+J. The jump must survive every input radius."""
    ctx=m.context(dict(variable='t',parameters=['L','r'],parameter_conditions=['L>0','r>0']))
    radius=('s','r')
    for slope in (ZERO,ONE):
        jump=m.div(tolerance_floor,q(2)) if tolerance_floor is not None else ONE
        if m.sign(jump,ctx)!=1 or tolerance_floor is not None and m.sign(m.add(tolerance_floor,m.neg(jump)),ctx)!=1:continue
        if inverse and m.sign(slope,ctx)!=1:continue
        return dict(base_point=ZERO,slope=slope,jump=jump,argument_sequence='1/n',
                    lower_absolute=m.mul(slope,radius),upper_absolute=m.add(m.mul(slope,radius),jump),
                    violated_tolerance=m.div(jump,q(2)))
    raise Unsupported('No discontinuous witness proved the required ball inclusion')


def neighborhood_goal(t,lib):
    """Read ball inclusions with both radii explicit. Provenance may not add a theorem to prove."""
    kind=t['kind'];meta=t.get('source',{});fields={'kind','id','source'}
    if not lib.data.get('quantified_neighborhoods'):raise Unsupported('Missing neighborhood rules')
    def check(keys,literal):
        provenance={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
        if set(t)-fields-keys or not isinstance(meta,dict) or set(meta)-provenance or meta.get('literal_requirement',literal)!=literal:
            raise Unsupported('An additional source obligation remains')
    if kind=='epsilon_delta_proof':
        check({'expression','base_point','method_requirement','variable','parameters'},'Посредством ε–δ доказать непрерывность функции на её области.')
        if t.get('base_point')!='arbitrary point in natural domain' or t.get('method_requirement')!='epsilon_delta':
            raise Unsupported('Expected pointwise continuity relative to the natural domain')
        var=t.get('variable','x');expr=t['expression']
        params=t.get('parameters',sorted(set(re.findall(r'\b[a-zA-Z]\b',expr))-{var,'e'}))
        raw=m.parse(expr,var,params);center='x0';eps='epsilon'
        while center in [var,*params]:center+='_'
        while eps in [var,*params,center]:eps+='_'
        a=('s',center);ctx=m.context(dict(variable=var,parameters=[*params,center]))
        segment=(m.add(a,q(-1)),m.add(a,ONE),True,True)
        estimate=modulus_estimate(raw,var,segment,ctx)
        C,alpha=estimate['constant'],estimate['exponent']
        radius=m.power(m.div(('s',eps),m.add(ONE,C)),int(1/m.num(alpha)))
        return (dict(center=center,epsilon=eps,local_interval=segment,source_domain=domain_conditions(raw),estimate=estimate),
                dict(continuous_at_every_domain_point=True,delta=('min',ONE,radius)))
    if 'epsilon_family' in t:
        check({'epsilon_family'},'Следует ли непрерывность, если определение ε–δ выполнено лишь для указанного множества ε?')
        family=t['epsilon_family']
        if isinstance(family,dict) and set(family)=={'finite_values'} and isinstance(family['finite_values'],list):
            if any(not re.fullmatch(r'\d+(?:/\d+|\.\d+)?',str(z)) for z in family['finite_values']):
                raise Unsupported('Positive rational tolerances required')
            vals=[F(str(z)) for z in family['finite_values']]
            if any(z<=0 for z in vals):raise Unsupported('Positive rational tolerances required')
            lower=q(min(vals,default=1))
        elif family=='finite set of positive epsilon':
            # Vacuous tests allow any jump when the family is empty.
            lower='min(E) if E is nonempty, otherwise 1'
        else:
            match=re.fullmatch(r'epsilon=(\d+)/(\d+)\^n for n=1,2,\.\.\.',str(family))
            if not match:raise Unsupported('Cofinality or a positive lower bound has not been established')
            c,b=map(int,match.groups())
            if min(c,b)<=0:raise Unsupported('Geometric tolerances must be positive and defined')
            if b>1:
                return (dict(transition='cofinal_tolerances',numerator=q(c),base=q(b),
                             lower_bound_for_denominator='1+n*(base-1)',index_requirement='n>numerator/(epsilon*(base-1))'),
                        dict(implies_continuity=True,reason='cofinal_at_zero'))
            lower=q(c)
        return (dict(transition='positive_tolerance_floor',lower=lower,radius=ONE,
                     witness=jump_witness(tolerance_floor=('s','L') if isinstance(lower,str) else lower)),
                dict(implies_continuity=False,reason='positive_lower_bound_allows_jump'))
    if 'quantification' in t:
        data=t['quantification']
        if isinstance(data,str):
            heading=re.fullmatch(r'for epsilon>(\d+(?:\.\d+)?) and each x there is local delta bounding all \|f\(x_prime\)-f\(x\)\|; for smaller epsilon cannot do this at every x',data)
            if not heading:raise Unsupported('The quantified threshold is unspecified')
            cut=F(heading[1]);printed=heading[1].replace('.',',')
            # The original heading explicitly includes equality in the second range.
            if not isinstance(meta,dict) or 'literal_requirement' not in meta:raise Unsupported('The boundary tolerance needs its source inclusion')
            check({'expression','quantification'},f'Доказать утверждения для ε>{printed} и 0<ε≤{printed}, определить все точки разрыва.')
        elif isinstance(data,dict) and set(data)=={'test_all_larger','disprove_all_at_most','classify_discontinuities'} and data['classify_discontinuities'] is True:
            check({'expression','quantification'},None)
            cut=F(str(data['test_all_larger']))
            if F(str(data['disprove_all_at_most']))!=cut:raise Unsupported('The two requested thresholds differ')
        else:raise Unsupported('The two quantified ranges and continuity request are required')
        raw=m.parse(t['expression'],'x',extra_functions=('floor',));ctx=m.context(dict(variable='x'))
        if any(not known_guard(g,ctx) for g in domain_conditions(raw)):raise Unsupported('The original expression must be defined on the entire line')
        numerator,denom=m.rational_form(raw);x=('v','x');linear=((x,1),);stair=((('floor',x),1),)
        if denom!={():F(1)} or set(numerator)-{(),linear,stair}:raise Unsupported('No affine law between consecutive jumps')
        slope=numerator.get(linear,0);jump=numerator.get(stair,0)
        if slope<=0 or jump<=0 or jump!=cut:raise Unsupported('The required positive jump threshold was not proved')
        return (dict(transition='affine_floor_jumps',slope=q(slope),jump=q(jump),constant=q(numerator.get((),0)),
                     local_radius='min(1,(epsilon-jump)/slope)',test_points='k and k-1/n for n>=2',
                     difference='jump+slope/n'),dict(discontinuities='all integers',valid_at_every_point_exactly_for_epsilon_above=q(jump)))
    if 'hypothesis' in t:
        example=t.get('example')
        check({'hypothesis','example'} if example is not None else {'hypothesis'},
              'Следует ли непрерывность, какое свойство характеризовано и как это видно на заданном примере?' if example is not None else
              'Следует ли непрерывность и какое свойство характеризует условие?')
        h=t['hypothesis']
        if isinstance(h,str):
            a='|x-x0|<delta';b='|f(x)-f(x0)|<epsilon'
            match=re.fullmatch(r'for all (sufficiently small )?(delta|epsilon)>0 exists (delta|epsilon)>0: (.+) implies (.+)',h)
            if not match or [match[4],match[5]] not in ([a,b],[b,a]):raise Unsupported('Unrecognized ball inclusion')
            side={'delta':'input','epsilon':'output'}
            h=dict(given_radius=side[match[2]],chosen_radius=side[match[3]],antecedent='input' if match[4]==a else 'output',
                   given_range='sufficiently_small' if match[1] else 'positive')
        if (not isinstance(h,dict) or set(h)!={'given_radius','chosen_radius','antecedent','given_range'} or
                {h['given_radius'],h['chosen_radius']}!={'input','output'} or h['antecedent'] not in ('input','output')
                or h['given_range'] not in ('positive','sufficiently_small')):
            raise Unsupported('Both distinct radius binders and their range are required')
        forward=h['antecedent']=='input';given_input=h['given_radius']=='input';small=h['given_range']=='sufficiently_small'
        plan=dict(transition='quantified_balls',inclusion=h)
        if forward and not given_input:prop='continuity'
        elif forward:prop='locally_bounded_image' if small else 'bounded_image_of_each_centered_ball'
        elif given_input:prop='positive_image_separation_outside_each_input_ball'
        else:prop='bounded_preimage_of_some_output_ball' if small else 'bounded_preimage_of_each_centered_output_ball'
        if prop!='continuity':
            witness=jump_witness(inverse=not forward);r=('s','r');A=witness['slope']
            chosen=(m.add(witness['upper_absolute'],ONE) if forward else
                    m.mul(A,r) if given_input else m.div(r,A))
            plan.update(witness=witness,chosen_radius=chosen)
        if example is not None:
            if prop!='positive_image_separation_outside_each_input_ball' or not isinstance(example,dict) or set(example)!={'rational','irrational'}:
                raise Unsupported('The additional example needs a separate proof')
            x=('v','x');atan=('atan',x);u=m.parse(example['rational'],'x');v=m.parse(example['irrational'],'x')
            C=m.simplify(m.add(v,atan));ctx=m.context(dict(variable='x'))
            if domain_conditions(u) or domain_conditions(v) or m.simplify(u)!=atan or m.variable_in(C) or not m.known_nonnegative(m.add(C,m.neg(m.PI)),ctx):
                raise Unsupported('The branch inverse or strict separation has not been proved')
            plan['example']=dict(separator=m.div(C,q(2)),lower_inverse='tan(y)',upper_inverse=('tan',m.add(C,m.neg(('s','y')))),
                                 containing_intervals=[(m.neg(m.div(m.PI,q(2))),m.div(m.PI,q(2))),
                                                       (m.add(C,m.neg(m.div(m.PI,q(2)))),m.add(C,m.div(m.PI,q(2))))],
                                 discontinuity='two dense branches with unequal limits')
        return plan,dict(implies_continuity=prop=='continuity',equivalent_property=prop)
    raise Unsupported('An explicit-function or quantified threshold proof is still required')


def separated_arguments(raw,v,interval,ctx,limit):
    """Construct and check two nearby points with separated images on a tail."""
    from integrals import learned_nodes
    from verify import same_value
    x=('v',v);n=('v','__index');a,b,_,_=interval
    if '__index' in ctx['parameters'] or v=='__index':raise Unsupported('The witness index is not fresh')
    def at_infinity(e):
        return limit('limit on the witness tail',e,'+inf','positive_infinity','__index')
    def positive_direction(degree):
        if degree>=1:return b=='+inf'
        return (a=='-inf' or not isinstance(a,str) and m.known_nonnegative(m.neg(a),ctx)) and (b=='+inf' or not isinstance(b,str) and m.sign(b,ctx)==1)
    def separated(delta):
        return delta in ('+inf','-inf') or isinstance(delta,tuple) and m.constant_defined(delta,ctx) and m.nonzero(delta,ctx)
    if b=='+inf' or a=='-inf':
        try:
            p,d=poly.rf(raw,v)
        except poly.NotRational:pass
        else:
            if len(p)>len(d)+1:
                direction=ONE if b=='+inf' else q(-1)
                bound=a if b=='+inf' else b
                if not isinstance(bound,str) and not m.constant_defined(bound,ctx):raise Unsupported('Undefined tail endpoint')
                # n > |bound| + 1 puts both points inside the indicated half-line.
                threshold=ONE if isinstance(bound,str) else m.add(ONE,m.simplify(('abs',bound)))
                h=m.power(n,-(len(p)-len(d)-1));left=m.mul(direction,n);right=m.mul(direction,m.add(n,h))
                delta=at_infinity(m.simplify(m.add(m.substitute(raw,{x:right}),m.neg(m.substitute(raw,{x:left})))))
                if separated(delta):
                    return dict(witness='rational_growth',points=[left,right],index_greater_than=threshold,
                                tail_direction=direction,distance=h,distance_limit=ZERO,value_difference_limit=delta)
    for wave in learned_nodes(raw):
        if not isinstance(wave,tuple) or wave[0] not in ('sin','cos'):continue
        phase=wave[1]
        for degree in (-1,2,1):
            if not positive_direction(degree):continue
            coeff=m.simplify(m.substitute(phase,{x:ONE}))
            if not m.constant_defined(coeff,ctx) or m.sign(coeff,ctx)!=1 or not same_value(phase,m.mul(coeff,m.power(x,degree))):continue
            cycle=m.mul(m.mul(q(2),m.PI),n)
            if degree==1:
                if wave[0]!='sin':continue
                # A small shift of phase then detects amplification by an increasing envelope.
                first=m.div(cycle,coeff);step=m.div(ONE,m.mul(coeff,n));second=m.add(first,step)
                phases=[ZERO,m.simplify(('sin',m.div(ONE,n)))];distance=step
            else:
                off=q(1,2) if wave[0]=='sin' else ZERO
                phases=[ONE,q(-1)]
                theta=[m.add(cycle,m.mul(m.add(off,q(k)),m.PI)) for k in (0,1)]
                if degree==-1:
                    first,second=[m.div(coeff,z) for z in theta];distance=m.div(m.mul(coeff,m.PI),m.mul(*theta))
                else:
                    first,second=[('sqrt',m.div(z,coeff)) for z in theta]
                    distance=m.div(m.PI,m.mul(coeff,m.add(first,second)))
            # Both indices range over positive integers. The chosen phases differ by pi,
            # or by 1/n in the amplification branch. These equalities fix the two images.
            values=[m.simplify(m.substitute(raw,{wave:w,x:z})) for w,z in zip(phases,(first,second))]
            if any(m.contains(e,x) for e in values):continue
            delta=at_infinity(m.simplify(m.add(values[1],m.neg(values[0]))))
            if separated(delta):
                return dict(witness='periodic_phase',wave=wave,positive_coefficient=coeff,phase_power=degree,
                            points=[first,second],distance=distance,distance_limit=ZERO,phase_values=phases,
                            pulled_back_values=values,value_difference_limit=delta)
    raise Unsupported('No two sequences with vanishing separation and separated images have been established')


# A concentration profile separates pointwise decay, peak height and integral mass.
_SEQUENCE_QUESTIONS = {'pointwise convergence', 'uniform convergence', 'interchange of limit and integral'}
_SEQUENCE_REQUESTS = {
    'Для каких alpha последовательность сходится поточечно на сегменте?': {'pointwise convergence'},
    'Для каких alpha последовательность сходится равномерно на сегменте?': {'uniform convergence'},
    'Для каких alpha возможен предельный переход под знаком интеграла от 0 до 1?': {'interchange of limit and integral'},
    'Показать поточечную сходимость и различие интеграла предела и предела интегралов.':
        {'pointwise convergence', 'interchange of limit and integral'},
    'Показать неравномерную сходимость и равенство интеграла предела и предела интегралов.':
        {'uniform convergence', 'interchange of limit and integral'},
    'Законен ли переход к пределу под знаком интеграла?': {'interchange of limit and integral'},
}


def concentration_source(task):
    src=task.get('functional_statement')
    metadata=task.get('source',{})
    if (not isinstance(src,dict) or set(task)-{'kind','id','source','functional_statement','statement','requested_output'}
            or not isinstance(metadata,dict) or set(metadata)-{
                'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}):
        raise Unsupported('A concentration proof must bind all of the stated source requirements')
    bind=lambda txt: re.sub(r'\s+', '', txt)
    parameter=src.get('parameter')
    if task['kind']=='parameter_sequence_classification' and set(src)=={'sequence','domain','parameter','question'}:
        if not isinstance(parameter,str) or parameter in ('n','x'):
            raise Unsupported('The power parameter must be independent of n and x')
        m.context(dict(variable='n',parameters=[parameter]))
        domain=re.fullmatch(r'\[([^,]+),([^,]+)\]',bind(src['domain']))
        if not domain:raise Unsupported('Need a closed finite interval starting at zero')
        ends=domain.groups();want={src['question']}
    elif task['kind']=='sequence_integral_interchange' and set(src)=={'sequence','interval','questions'}:
        ends=src['interval'];want=set(src['questions']);parameter=None
    else:raise Unsupported('Unknown concentration goal or extra hypotheses')
    if not (want and want<=_SEQUENCE_QUESTIONS and len(ends)==2):raise Unsupported('Unknown limit comparison')
    low,top=map(exact_rational,ends)
    if low!=0 or top is None or top<=0:raise Unsupported('Need a positive finite interval from zero')
    seq=src['sequence'];raw=task.get('statement');requested=task.get('requested_output',[])
    native=sorted(want)==sorted(requested)
    if raw is not None:
        suffix='x in ['+str(ends[0])+','+str(ends[1])+']'
        if bind(raw) not in {bind(seq+', '+tail) for tail in ('n>=1, '+suffix,suffix+', n>=1')}:
            raise Unsupported('The original expression or its index and interval were changed')
    elif metadata.get('literal_requirement') is not None:
        raise Unsupported('The printed statement must be bound')
    if not native:
        if not len(requested)==1 or _SEQUENCE_REQUESTS.get(requested[0])!=want:
            raise Unsupported('The requested statement is not the stated concentration goal')
        if (('неравномерную' in requested[0] or 'равенство' in requested[0] or 'различие' in requested[0])
                and parameter is not None):raise Unsupported('An asserted comparison requires a definite exponent')
        if requested[0].endswith('от 0 до 1?') and top!=1:
            raise Unsupported('The printed integration range differs')
    if metadata.get('literal_requirement') not in (None,*requested):
        raise Unsupported('The literal statement asks for an additional result')
    tree=m.parse(seq,None,('n','x',*([parameter] if parameter else [])))
    return tree,top,parameter,want,requested[0] if not native else None


def concentration_profile(raw,top,parameter):
    """Read C n^alpha x^j times a profile whose argument or endpoint scale can move."""
    n,x=('s','n'),('s','x');a=('s',parameter)
    def factors(e,sgn=1):
        tag=e[0]
        if tag in ('mul','div'):
            yield from factors(e[1],sgn)
            yield from factors(e[2],sgn if tag=='mul' else -sgn)
        else:yield e,sgn
    def monomial(e,params=()):
        c=F(1);degree={n: F(0),x: F(0)}
        for t,sgn in params or list(factors(e)):
            base=t[1] if t[0] in ('pow','rpow') else t
            exp=q(t[2]) if t[0]=='pow' else m.simplify(t[2]) if t[0]=='rpow' else ONE
            if base in degree:
                if base==x and (sgn<0 or t[0]=='rpow' or m.num(exp) is None or m.num(exp)<=0):
                    raise Unsupported('An original spatial factor has a pole at zero')
                if (power:=m.num(exp)) is not None:
                    prior=degree[base]
                    if not isinstance(prior,F):raise Unsupported('Combined symbolic power requires another parameter reduction')
                    degree[base]=prior+sgn*power
                elif base==n and exp==a and parameter and sgn==1 and degree[n]==0:degree[n]=a
                else:raise Unsupported('Unsupported real exponent in moving amplitude')
            elif (value:=m.num(t)) is not None and (sgn==1 or value):c*=value**sgn
            else:raise Unsupported('Need a checked scalar monomial')
        return c,degree[n],degree[x]
    all_factors=list(factors(raw));matches=[]
    for t,sgn in all_factors:
        if t[0]=='exp' and sgn==1:
            try:c,i,j=monomial(t[1])
            except Unsupported:continue
            if c<0 and i==1 and j>0 and j.denominator==1:matches.append((t,sgn,'exponential',-c,j,None))
        elif t[0]=='rpow' and t[2]==n and sgn==1:
            # The polynomial base has no original domain restrictions before simplification.
            expected=m.add(ONE,m.mul(q(-1/top),x));ctx=m.context(dict(variable='n',parameters=['x']))
            if (all(known_guard(g,ctx) for g in domain_conditions(t[1])) and
                    not m.rational_form(m.add(t[1],m.neg(expected)))[0]):
                matches.append((t,sgn,'beta',F(1,top),F(1),None))
        elif t[0]=='add' and sgn==-1:
            for u,v in (t[1:],tuple(reversed(t[1:]))):
                if m.num(u)!=1:continue
                try:c,i,j=monomial(v)
                except Unsupported:continue
                if c>0 and i>1 and j>0 and i.denominator==1 and j.denominator==1:
                    matches.append((t,sgn,'reciprocal',c,j/i,i))
    if len(matches)!=1:raise Unsupported('No unique rescaling with a decaying positive profile')
    node,sgn,kind,scale,dilation,tail=matches[0]
    all_factors.remove((node,sgn))
    C,alpha,degree=monomial(None,all_factors or [(ONE,1)])
    if (not (C>0 and degree>0 and degree.denominator==1) or (parameter is not None and alpha!=a)
            or (kind=='reciprocal' and (not isinstance(alpha,F) or alpha>=tail))):
        raise Unsupported('Need a positive profile of finite pointwise decay with its actual exponent')
    return kind,C,alpha,degree,scale,dilation,tail


def concentration_goal(task,library):
    from math import factorial
    if not library.data.get('rescaled_sequence_profiles'):
        raise Unsupported('Rescaled profile theorem is absent from the library')
    raw,L,parameter,want,assertion=concentration_source(task)
    kind,C,alpha,mdeg,c,r,p=concentration_profile(raw,L,parameter)
    peak,mass=mdeg/r,(mdeg+1)/r
    evidence=dict(theorem='method.separate_pointwise_peak_and_mass',source_domain=(q(0),q(L)),source_indices='n>=1',
                  family=kind,coefficient=q(C),index_exponent=q(alpha) if isinstance(alpha,F) else alpha,
                  space_power=q(mdeg),scale=q(c),dilation=q(r),
                  pointwise_reason='zero at x=0 and tail decay at each fixed positive x')
    answer={'pointwise_limit': ZERO}
    def criterion(exponent):
        return (parameter+'<'+source(q(exponent))) if parameter else alpha<exponent
    if 'pointwise convergence' in want:answer['pointwise_convergence']='all real '+parameter if parameter else True
    if 'uniform convergence' in want:
        evidence['peak_threshold']=q(peak)
        evidence['peak_certificate']={
            'exponential':'t=c*n*x^r; t^(m/r)*exp(-t) peaks at t=m/r, eventually inside the source interval',
            'beta':'x=m*L/(n+m); the normalized maximum tends to a finite strictly positive constant',
            'reciprocal':'t=n*x^r; t^(m/r)/(1+c*t^p) is bounded and positive at t=1'}[kind]
        answer['uniform_convergence']=criterion(peak)
    if 'interchange of limit and integral' in want:
        if kind=='reciprocal' and mass>=p:raise Unsupported('The normalized integral profile has no finite dominating tail')
        evidence['mass_threshold']=q(mass)
        evidence['mass_certificate']={
            'exponential':'t=c*n*x^r; the remaining positive integral tends to Gamma((m+1)/r)',
            'beta':'Euler integral m!/((n+1)...(n+m+1)) after x=L*t',
            'reciprocal':'t=n*x^r; profile t^((m+1)/r-1)/(1+c*t^p) is integrable at zero and infinity'}[kind]
        answer['integral_of_limit']=ZERO
        answer['interchange_valid']=criterion(mass)
        if parameter:
            answer['integral_limit_cases']={'negative_mass_exponent':'0','zero_mass_exponent':'positive finite','positive_mass_exponent':'+inf'}
        elif alpha<mass:answer['limit_of_integrals']=ZERO
        elif alpha>mass:answer['limit_of_integrals']='+inf'
        elif kind=='beta':answer['limit_of_integrals']=q(C*L**int(mdeg+1)*factorial(int(mdeg)))
        elif kind=='exponential' and mass.denominator==1:
            answer['limit_of_integrals']=q(C*factorial(int(mass)-1)/(r*c**int(mass)))
        elif kind=='reciprocal' and mass==1 and p==2:
            answer['limit_of_integrals']=m.div(m.mul(q(C/(2*r)),m.PI),m.simplify(('sqrt',q(c))))
        else:
            answer['limit_of_integrals']='positive finite integral of the rescaled profile'
    argument=['При x=0 каждый член равен нулю. При фиксированном положительном x проверяем затухание профиля.']
    if 'peak_threshold' in evidence:
        argument.append('Выделяем масштаб движущегося максимума. Сравниваем степень множителя с '+source(q(peak))+'.')
    if 'mass_threshold' in evidence:
        argument.append('Переносим масштаб в интеграл вместе с дифференциалом. Множитель меняет поведение при степени '+source(q(mass))+'.')
    evidence['argument']=argument
    if assertion and (('неравномерную' in assertion and answer.get('uniform_convergence') is not False)
                      or ('равенство' in assertion and answer.get('interchange_valid') is not True)
                      or ('различие' in assertion and answer.get('interchange_valid') is not False)):
        raise Unsupported('The claimed comparison is false for this source')
    return evidence,answer


def exact_rational(text):
    expr=m.parse(text,None)
    if not m.constant_defined(expr,m.context(dict(variable='x'))):raise Unsupported('Undefined scalar bound')
    value=m.num(m.simplify(expr))
    if value is None:raise Unsupported('A checked rational bound is required')
    return value


def absolute_numeric_tail(task):
    """Fit a uniform term bound C/[n(n+1)] and sum its exact positive tails."""
    from math import floor
    fields={'kind','id','source','term','index','variable','start_index','interval','tolerance'}
    metadata=task.get('source',{})
    if (set(task)-fields or not isinstance(metadata,dict) or set(metadata)-{
            'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}
            or metadata.get('literal_requirement') not in (None,
                'Найти достаточное число членов для строгой ошибки <epsilon равномерно по вещественным x, провести численный расчёт.')
            or task['interval'] not in ('real line','R','(-inf,+inf)')):
        raise Unsupported('A sufficient strictly bounded tail on the original real line is required')
    index,var,start=task['index'],task['variable'],task['start_index']
    if index==var or type(start) is not int or start<1:raise Unsupported('Positive integer indices are required')
    m.context(dict(variable=index,parameters=[var]));tol=exact_rational(task['tolerance'])
    raw=m.parse(task['term'],index,[var]);n=('v',index)
    if raw[0]!='div' or tol<=0:raise Unsupported('Need a quotient and a positive tolerance')
    wave,den=raw[1:];C=F(1)
    if wave[0]=='mul':
        a,b=wave[1:]
        if m.num(a) is None:a,b=b,a
        if m.num(a) is not None:C=abs(m.num(a));wave=b
    if wave[0] not in ('sin','cos') or not C or domain_conditions(wave[1]) or domain_conditions(den):
        raise Unsupported('No everywhere-defined bounded wave and polynomial denominator')
    p,d=m.rational_form(den)
    if any(atom!=n for part in (p,d) for mon in part for atom,_ in mon):
        raise Unsupported('The denominator depends on the spatial variable or is not polynomial')
    pc,dc=(coefficient_rows(z,n) for z in (p,d))
    if set(dc)!={0} or max(pc,default=-1)!=2:raise Unsupported('Need a quadratic denominator')
    high,mid,low=(m.num(m.div(pc.get(i,ZERO),dc[0])) for i in (2,1,0))
    if high<=0 or mid<high or low<0:raise Unsupported('The lower envelope An(n+1) is unproved')
    prefix=max(start,floor(C/(high*tol)));bound=C/(high*(prefix+1))
    if bound>=tol:raise Unsupported('The proposed cutoff lacks a strict error bound')
    return (dict(theorem='method.uniform_reciprocal_difference_tail',source_start=start,denominator=(q(low),q(mid),q(high)),
                 envelope_coefficient=q(C/high),cutoff=prefix,
                 argument='Ограничиваем модуль тригонометрической функции единицей. Знаменатель не меньше положительного A·n(n+1). Разлагаем 1/[n(n+1)] в разность последовательных обратных чисел и складываем хвост.'),
            dict(sufficient_terms=prefix-start+1,last_term_index=prefix,uniform_error_upper_bound=q(bound)))


def uniform_exp_taylor(task):
    """Locate the sharp cut between two strictly checked positive Taylor tails."""
    src=task.get('functional_statement');meta=task.get('source',{})
    if (not isinstance(src,dict) or set(src)!={'function','terms','domain','tolerance'} or src['function']!='exp(x)'
            or src['terms']!='sum_(i=0..n) x^i/i!' or set(task)-{'kind','source','id','statement','functional_statement'}
            or not isinstance(meta,dict) or set(meta)-{
                'exercise','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement','printed_subpart'}):
        raise Unsupported('The original exponential polynomial and full uniform error question are needed')
    interval=re.fullmatch(r'\[0,([^,\]]+)\]',src['domain']);lit=task.get('statement')
    if not interval or meta.get('literal_requirement') not in (None,lit):raise Unsupported('Unrecognized source error comparison')
    X=exact_rational(interval[1]);eps=exact_rational(src['tolerance'])
    if X<0 or eps<=0:raise Unsupported('Need a nonnegative interval and positive tolerance')
    if lit is not None:
        match=re.fullmatch(r'При каких n гарантируется abs\(exp\(x\)-sum\(x\^i/factorial\(i\),i=0\.\.n\)\)<([^ ]+) при всех 0<=x<=([^?]+)\?',lit)
        if not match or (exact_rational(match[1]),exact_rational(match[2]))!=(eps,X):
            raise Unsupported('The printed error inequality or interval differs from its typed form')
    if X==0:
        return dict(theorem='method.positive_taylor_tail',argument='На вырожденном промежутке x=0, и все частичные суммы равны единице.'),dict(minimal_degree=0)
    terms=[F(1)]
    def term(k):
        while len(terms)<=k:terms.append(terms[-1]*X/len(terms))
        return terms[k]
    failed=None
    for N in range(256):
        lower=F(0)
        for k in range(N+1,N+34):
            lower+=term(k)
            if lower>=eps:
                failed=dict(degree=N,last_index=k,lower=q(lower));break
            ratio=X/(k+2)
            if ratio>=1:continue
            upper=lower+term(k+1)/(1-ratio)
            if upper<eps:
                if N and (not failed or failed['degree']!=N-1):raise Unsupported('Sharpness remains open')
                return (dict(theorem='method.positive_taylor_tail',endpoint=q(X),tolerance=q(eps),passed_degree=N,
                             last_index=k,upper_ratio=q(ratio),upper=q(upper),previous_failure=failed,
                             argument='Остаток положительного ряда возрастает к правому концу. Складываем первые члены хвоста точно и оцениваем остальные геометрической прогрессией. Для предыдущей степени проверяем нижнюю границу ошибки.'),
                        dict(minimal_degree=N,all_degrees_from=N,uniform_error_strictly_below=q(eps)))
        else:break
    raise Unsupported('The adjacent rational enclosures do not yet decide the strict cutoff')

def series_interval_input(task):
    fields={'kind','id','source','term','index','variable','start_index','interval','printed_conditions','requested_output'}
    output=task.get('requested_output');start=task['start_index'];index,var=task['index'],task['variable']
    if (set(task)-fields or not uniform_series_source(task,character=output==['convergence_character','proof'])
            or output not in (['uniform_convergence','proof'],['uniform_convergence_classification','proof'],['convergence_character','proof'])
            or type(start) is not int or start<0 or index==var):
        raise Unsupported('Unrecognized original interval, initial index or convergence requirement')
    for name in (index,var):m.context(dict(variable=name))
    notes=task.get('printed_conditions',f'lower index {start}.').split('; ')
    if notes.pop()!=f'lower index {start}.' or len(notes)>1:
        raise Unsupported('Additional assumptions or a different start require proof')
    return index,var,start,task['interval'],notes[0] if notes else None


def indexed_power_series(task):
    """Find a geometric term, a summable amplitude, or an exact finite difference."""
    index,var,start,interval,condition=series_interval_input(task)
    n,x=('s',index),('s',var)
    raw=m.parse(task['term'],None,(index,var),extra_functions=('factorial',))
    if raw[0]=='add' and start>=1 and condition is None and interval in ('[-1,1]','[0,1]','(-1,1)'):
        first,minus=raw[1:]
        if (first==('div',('rpow',x,n),n) and minus[0]=='mul' and minus[1]==q(-1)):
            shift=m.add(n,ONE);next_value=('div',('rpow',x,shift),shift)
            other=minus[2]
            if (other[0]=='div' and other[1][:2]==('rpow',x) and
                    all(not domain_conditions(a) and m.simplify(a)==shift for a in (other[1][2],other[2]))):
                conditional=[q(-1)] if interval=='[-1,1]' else []
                return (dict(theorem='method.uniform_telescoping_power_tail',potential=first,shifted_potential=next_value,
                             argument='В соседних слагаемых сокращаются совпадающие граничные члены. Последний член по модулю не больше обратного индекса на всём промежутке. В точке −1, если она входит в промежуток, ряд сходится условно: модули сравнимы с 1/n.'),
                        dict(absolute_at_every_point=not conditional,conditional_points=conditional,uniform=True,pointwise_sum=m.div(('pow',x,start),q(start)),
                             uniform_error_after_index='1/(N+1)'))
    top,den=raw[1:] if raw[0]=='div' else (raw,ONE)
    if top==('rpow',x,n):prefactor=ONE
    elif top[0]=='mul' and ('rpow',x,n) in top[1:]:
        prefactor=top[2] if top[1]==('rpow',x,n) else top[1]
    else:raise Unsupported('No full geometric factor with the original index')
    if domain_conditions(prefactor) or m.contains(prefactor,n):raise Unsupported('The coefficient has additional source domain obligations')
    p,d=m.rational_form(prefactor);mon=p.keys();C=m.num(m.simplify(prefactor))
    if C==0 or d!={():F(1)} or any(a!=x for term in mon for a,_ in term):
        raise Unsupported('A nonzero polynomial spatial coefficient is required')
    def result(theorem,arg,value,**proof):return dict(theorem=theorem,argument=arg,initial_index=start,**proof),value
    if C is not None and den==ONE and (bound:=re.fullmatch(r'abs\('+re.escape(var)+r'\)<(.+)',interval)):
        limit=bound[1]
        if condition==limit+'<1' and limit.isascii() and limit.isidentifier() and limit not in (index,var):
            m.context(dict(variable=var,parameters=[limit]))
            return result('method.uniform_geometric_envelope','При положительном радиусе члены ограничены геометрическим рядом с основанием меньше единицы. При неположительном радиусе область пуста.',
                          dict(absolute_at_every_point=True,uniform=True,empty_region=limit+'<=0'),radius=limit)
        if condition is not None:raise Unsupported('The original bound is unrecognized')
        R=exact_rational(limit)
        if R<=0:return result('method.uniform_geometric_envelope','Область пуста.',dict(absolute_at_every_point=True,uniform=True,empty_region=True))
        if R<1:return result('method.uniform_geometric_envelope','Мажорируем каждый член числовой геометрической прогрессией.',
                             dict(absolute_at_every_point=True,uniform=True),radius=q(R))
        if R==1:return result('method.uniform_geometric_envelope','В каждой точке сходится геометрический ряд. На всём открытом промежутке верхняя грань модуля каждого члена остаётся постоянной.',
                              dict(absolute_at_every_point=True,uniform=False),term_supremum=q(abs(C)))
    if condition is not None:raise Unsupported('The stated parameter conditions need another tail proof')
    if C is not None and den[0]=='pow' and den[1]==n and den[2]>1 and start>=1 and interval in ('[-1,1]','[0,1]','(-1,1)'):
        return result('method.uniform_geometric_envelope','Модуль степени точки не превосходит единицы. Числовой степенной ряд показателя больше единицы даёт мажоранту.',
                      dict(absolute_at_every_point=True,uniform=True),majorant_coefficient=q(abs(C)),majorant_power=den[2])
    if C is not None and den==('factorial',n) and interval in ('(0,+infinity)','[0,+infinity)','real line','R'):
        return result('method.uniform_geometric_envelope','На каждой фиксированной точке отношение модулей последовательных членов стремится к нулю. На неограниченном промежутке отдельные степени неограниченны.',
                      dict(absolute_at_every_point=True,uniform=False),term_supremum='+inf')
    if den==ONE and interval in ('[0,1]','[0,1)'):
        coeff=poly.univariate_coefficients(p,x)
        if not coeff or sum(coeff):raise Unsupported('The source coefficient has no cancelling factor at the transition')
        # Divide exactly by 1-x in ascending coefficient order.
        cumulative=F(0);qcoeff=[]
        for a in coeff[:-1]:cumulative+=a;qcoeff.append(cumulative)
        Q=ZERO
        for a in reversed(qcoeff):Q=m.add(q(a),m.mul(x,Q))
        endpoint=sum(qcoeff)
        value=dict(absolute_at_every_point=True,uniform=endpoint==0,
                   pointwise_sum=dict(interior=m.mul(Q,('pow',x,start)) if start else Q))
        if interval=='[0,1]':value['pointwise_sum']['at_1']=ZERO
        return result('method.uniform_geometric_envelope','Формула конечной суммы сокращает множитель 1−x. Ошибка на остальных точках равна |Q(x)x^(N+1)|. Вдали от 1 она убывает геометрически, а на подходе к 1 её верхняя грань стремится к |Q(1)|.',
                      value,quotient=Q,limiting_error_supremum=q(abs(endpoint)))
    raise Unsupported('No complete geometric tail on the original interval')


def telescoping_product_series(task):
    index,var,start,interval,condition=series_interval_input(task)
    if start<1:raise Unsupported('The product prefix starts at a positive index')
    hit=re.fullmatch(r'(.+?)/product\(([^,]+),([A-Za-z_]\w*),(\d+),([A-Za-z_]\w*)\)',task['term'])
    if not hit or hit[3] in (index,var) or (int(hit[4]),hit[5])!=(start,index):
        raise Unsupported('No product with the original lower index and upper boundary')
    n,k,x=(('s',z) for z in (index,hit[3],var));names=(index,hit[3],var)
    numerator=m.parse(hit[1],None,names);factor=m.parse(hit[2],None,names)
    if domain_conditions(factor) or domain_conditions(numerator):raise Unsupported('Original product factors need a global domain proof')
    body=m.simplify(m.add(factor,q(-1)))
    C=m.num(m.div(body,m.mul(k,x)))
    delta=m.mul(q(C),m.mul(n,x)) if C is not None else None
    if C is None or C<=0:raise Unsupported('Each new product factor must have the form 1+C*k*x with C>0')
    A=m.num(m.div(numerator,delta))
    if A is None or A==0:raise Unsupported('The numerator is not a scalar multiple of the factor increment')
    match=re.fullmatch(r'\[([^,]+),([^,]+)(\]|\))',interval)
    if not match:raise Unsupported('Need the original nonnegative interval')
    low,high,end=match.groups();lower=None
    if high in ('+inf','+infinity') and end!=')':raise Unsupported('The infinite endpoint must be open')
    if condition:
        symbol=condition.removesuffix('>0')
        if condition!=symbol+'>0' or not symbol.isascii() or not symbol.isidentifier() or symbol in names:
            raise Unsupported('Unknown product parameter condition')
        m.context(dict(variable=var,parameters=[symbol]))
        if (low,high)==(symbol,'+infinity'):lower=symbol
        elif (low,high)!=('0',symbol):raise Unsupported('The positive parameter must be an interval endpoint')
    else:
        lo=exact_rational(low);hi=exact_rational(high) if high not in ('+inf','+infinity') else None
        if lo<0 or hi is not None and hi<=lo:raise Unsupported('A nondegenerate nonnegative interval is required')
        if lo>0:lower=q(lo)
    arg='Новый множитель Pₙ/Pₙ₋₁ отличается от единицы ровно на член числителя с постоянным множителем. Члены ряда превращаются в разность соседних обратных произведений.'
    if lower is not None:reason='При положительной нижней границе обратное произведение убывает не медленнее геометрической прогрессии.'
    else:reason='При x=0 все слагаемые нулевые. При каждом x>0 предел суммы равен постоянной. Этот скачок исключает равномерность на исходном промежутке.'
    return (dict(theorem='method.uniform_product_reciprocal_tail',factor=factor,increment=delta,series_coefficient=q(A),
                 positive_spatial_lower_bound=lower,initial_index=start,argument=[arg,reason]),
            dict(absolute_at_every_point=True,uniform=lower is not None,
                 pointwise_sum=dict(positive=q(A),at_0=ZERO) if lower is None else q(A)))


def trigonometric_uniform_tail(task):
    """Choose a uniform discrete primitive or show a resonant Cauchy block."""
    index,var,start,interval,condition=series_interval_input(task)
    if start<1 or task.get('requested_output')==['convergence_character','proof']:
        raise Unsupported('Need a positive-index uniform series goal')
    n,x=('s',index),('s',var);raw=m.parse(task['term'],None,(index,var),extra_functions=('floor',))
    wave,den=raw[1:] if raw[0]=='div' else (None,None);phase=('sin',('mul',n,x));sx=('sin',x)
    block_sign=('rpow',q(-1),('floor',('sqrt',n)))
    if wave and wave!=block_sign and domain_conditions(wave):raise Unsupported('An original phase has an unproved domain')
    wave=m.simplify(wave) if wave else None;phase=m.simplify(phase)
    if wave==phase and den is not None and (den==n or den[0]=='pow' and den[1]==n and den[2]>0):
        p=1 if den==n else den[2]
        if p>1:
            return (dict(theorem='method.uniform_phase_primitive',decay=p,argument='Мажорируем синусы единицей и сравниваем со сходящимся числовым рядом.'),dict(uniform=True))
        match=re.fullmatch(r'\[([A-Za-z_]\w*),2\*pi-\1\]',interval)
        if match and condition==match[1]+'>0' and match[1] not in (index,var):
            m.context(dict(variable=var,parameters=[match[1]]))
            return (dict(theorem='method.uniform_phase_primitive',decay=p,distance=match[1],
                         argument='В непустом промежутке геометрическая сумма экспонент ограничена через sin(ε/2). Суммирование по частям с убывающим 1/n даёт общий убывающий остаток. Если ε>π, промежуток пуст.'),dict(uniform=True))
        if condition is None and interval in ('[0,2*pi]','[0,+infinity)','(0,+infinity)','[0,1]','(0,1)'):
            return (dict(theorem='method.uniform_phase_primitive',moving_point=f'1/(2*{index})',block='N..2N',
                         argument='В точке x=1/(2N) фазы членов N…2N лежат между 1/2 и 1. Каждый синус имеет общий положительный нижний предел, и сумма этих членов отдалена от нуля. Поэтому равномерный критерий Коши не выполняется.'),dict(uniform=False))
    if condition is not None or interval not in ('[0,+infinity)','(0,+infinity)'):
        raise Unsupported('The argument must be supported on the whole stated interval')
    if wave==m.mul(phase,sx) and den==('sqrt',('add',n,x)):
        return (dict(theorem='method.uniform_phase_primitive',primitive_bound=q(2),tail_weight='1/sqrt(N)',
                     argument='При нерезонансном x частичные суммы синусов ограничены через 1/|sin(x/2)|. Множитель sin(x) убирает этот знаменатель, а в резонансе члены равны нулю. Суммирование по частям даёт остаток порядка 1/√N.'),dict(uniform=True))
    if wave==m.simplify(block_sign) and den==('sqrt',('mul',n,('add',n,x))):
        return (dict(theorem='method.uniform_phase_primitive',prefix_bound_order='sqrt(N)',weight_upper='1/N',adjacent_weight_difference='<=1/N^2',
                     argument='На каждом блоке между соседними квадратами знак постоянен. Знаки полных блоков чередуются, их длины линейны, а незаконченный блок имеет длину O(√N). С весом не больше 1/n и разностью весов не больше 1/n² суммирование по частям даёт равномерно малый хвост.'),dict(uniform=True))
    raise Unsupported('Neither a bounded trigonometric primitive nor a resonant tail witness was found')


UNIFORM_TAIL_THEOREMS={'method.uniform_geometric_envelope','method.uniform_telescoping_power_tail',
                       'method.uniform_product_reciprocal_tail','method.uniform_phase_primitive','method.weierstrass_tail_envelopes'}


def general_uniform_series(task,library,saved=None):
    if not library.data.get('general_uniform_series_tails'):
        raise Unsupported('Uniform tail alternatives are absent from the library')
    routes=[indexed_power_series,telescoping_product_series,trigonometric_uniform_tail,reciprocal_phase_series]
    errors=[]
    for route in routes:
        try:
            result=route(task)
            if saved is None or saved['theorem']==result[0]['theorem']:return result
        except (Unsupported,poly.ResourceBound,poly.Undefined,ValueError,ZeroDivisionError) as exc:errors.append(str(exc))
    raise Unsupported('; '.join(errors) or 'No matching recorded tail alternative')

def elementary_uniform_error(task,library):
    """Derive a numerical uniform modulus or a moving witness on the stated interval."""
    from graphs import interval_terms
    allowed={'id','kind','source','function','index','variable','interval','requested_output','parameters','conditions','pieces'}
    meta=task.get('source',{})
    if (not library.data.get('elementary_uniform_errors') or set(task)-allowed or
            set(task.get('requested_output',()))!={'pointwise_limit','uniform_convergence_classification','proof'} or
            not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','pdf_sha256','page_png_sha256','printed_subpart','heading_page'}):
        raise Unsupported('The uniform error needs a bound source function, domain and pointwise goal')
    index,var,domain=task['index'],task.get('variable','x'),task['interval'];params=task.get('parameters',[]);cond=task.get('conditions',[])
    if index==var or index in params or var in params:raise Unsupported('The source index and spatial coordinate must be independent')
    n,x=('s',index),('s',var);names=(index,var,*params)
    m.context(dict(variable=var,parameters=[index,*params]))
    parse=lambda text:m.parse(text,None,names)
    ctx=m.context(dict(variable=var,parameters=[index,*params],parameter_conditions=[index+'>0']))
    def equivalent(a,b):return not m.rational_form(m.add(a,m.neg(b)))[0]
    def guards(e):return all(known_guard(g,ctx) for g in domain_conditions(e))
    def out(value,modulus,uniform,arg,**data):
        return dict(method='elementary_uniform_error',theorem='method.uniform_error_and_moving_witness',
                    argument=arg,domain=domain,**data),dict(pointwise_limit=value,uniform=uniform,uniform_error_bound=modulus)
    notation=re.sub(r'\s+','',domain) if domain!='real line' else domain
    pure=not params and not cond
    if 'pieces' in task:
        if not pure or task.get('function') is not None or len(task['pieces'])!=3:
            raise Unsupported('Only a single checked triangular support is handled here')
        (a,left),(b,right),(c,zero)=task['pieces'];raw=parse(left);mirror=parse(right)
        pattern=rf'0<={re.escape(var)}<=([^/]+)/{re.escape(index)}'
        hit=re.fullmatch(pattern,re.sub(r'\s+','',a))
        if not hit or not notation.startswith('[0,') or not notation.endswith(']'):
            raise Unsupported('Need the source support near zero')
        half,L=exact_rational(hit[1]),exact_rational(notation[3:-1]);edge=2*half
        if min(half,L)<=0 or zero!='0' or not guards(raw) or not guards(mirror):raise Unsupported('Unproved support or raw branch domain')
        boundaries=[re.sub(r'\s+','',t) for t in (b,c)]
        if boundaries!=[f'{half}/{index}<{var}<{edge}/{index}',f'{var}>={edge}/{index}']:
            raise Unsupported('The pieces must partition the domain without introducing a gap')
        monom=m.div(raw,x);p,d=m.rational_form(monom);c_n=poly.univariate_coefficients(p,n)
        if (not c_n or d!={():F(1)} or sum(bool(a) for a in c_n)!=1 or c_n[-1]<=0 or
                not equivalent(mirror,m.mul(monom,m.add(m.div(q(edge),n),m.neg(x))))):
            raise Unsupported('The moving tent is not symmetric with verified slopes')
        degree=len(c_n)-1;height=c_n[-1]*half
        return out(ZERO,source(q(height))+f'*{index}^{degree-1}',degree<1,
                   'Опора сжимается к нулю, где функция равна нулю. На её середине получаем точную высоту, по которой проверяем равномерность.',peak=m.div(q(half),n))
    raw=parse(task['function']);power=('rpow',x,n)
    if (raw[0]=='div' and raw[1]==power and raw[2][0]=='add' and set(raw[2][1:])=={ONE,power} and len(params)==1
            and cond==[params[0]+'>0']):
        e=params[0]
        if notation==f'[0,1-{e}]':
            return out(ZERO,f'(1-{e})^{index} when 0<{e}<1',True,
                       'Ни одна точка непустого интервала не достигает 1. Модуль отношения не больше степени верхнего конца. При параметре, равном единице, остаётся только нуль, при большем параметре область пуста.',
                       parameter_cases=(f'0<{e}<1',f'{e}=1',f'{e}>1'))
        if notation==f'[1+{e},+infinity)':
            return out(ONE,f'(1+{e})^(-{index})',True,'Вычитаем отношение из единицы и мажорируем обратной степенью положительной нижней границы.')
        if notation==f'[1-{e},1+{e}]':
            value=dict(below_1=ZERO,at_1=q(1,2),above_1=ONE,only_if=f'0<{e}<2')
            return out(value,None,False,
                       'При параметре меньше двух поточечный предел имеет скачок в 1, тогда как все члены непрерывны. При параметре от двух в промежуток входит −1, где каждый нечётный член не определён.',
                       original_domain_failure=dict(condition=e+'>=2',point=q(-1),indices='odd'))
    if raw[0]=='rpow' and raw[2]==n and guards(raw[1]):
        field=m.mul(n,m.add(raw[1],q(-1)));p,d=m.rational_form(field)
        if d=={():F(1)} and m.contains(field,x) and all(a==x for mon in p for a,_ in mon):
            field=m.poly_expr(p);norm=m.simplify(('exp',field))
            named=(len(params)==2 and notation=='('+','.join(params)+')' and cond==['finite interval '+params[0]+'<'+params[1]])
            if pure or named:
                if named:finite=True
                else:
                    a,b,_,_=interval_terms(domain,ctx);finite=all(not isinstance(z,str) and m.num(z) is not None for z in (a,b))
                if finite:return out(norm,'C/n on the given finite interval',True,
                    'На ограниченном промежутке поле P(x) ограничено. При достаточно больших целых n основание положительно. Равномерная оценка логарифмического остатка даёт n ln(1+P(x)/n)=P(x)+O(1/n), после чего экспонента сохраняет равномерное приближение.',field=field)
                coeff=poly.univariate_coefficients(p,x)
                if domain in ('R','real line') and len(coeff)==2 and coeff[1]:
                    point=m.div(m.add(n,q(-coeff[0])),q(coeff[1]))
                    return out(norm,None,False,'Выбираем движущуюся точку, где P(x)=n. Разность eⁿ−2ⁿ не стремится к нулю.',moving_point=point)
    if len(params)==1 and not cond and notation==f'[1,{params[0]}]' and raw[0]=='mul':
        transform=raw[2] if raw[1]==n else raw[1] if raw[2]==n else ZERO
        if transform==('add',('rpow',x,('div',ONE,n)),q(-1)) or transform==('add',('rpow',x,('div',ONE,n)),('mul',q(-1),ONE)):
            return out(('ln',x),'C(a)/n',True,'На непустом промежутке логарифм ограничен сверху ln(a). Разлагаем exp(ln(x)/n) равномерно и умножаем остаток на n. При верхнем конце меньше единицы область пуста.')
    if not pure:raise Unsupported('The fixed parameter hypotheses are not bound to a uniform estimate')
    a,b,_,_=interval_terms(domain,ctx);lo=m.num(a) if not isinstance(a,str) else None;hi=m.num(b) if not isinstance(b,str) else None
    if raw[0]=='sqrt' and raw[1][0]=='add':
        for part,small in (raw[1][1:],tuple(reversed(raw[1][1:]))):
            if part[0]=='pow' and part[2]==2 and not m.contains(part,n) and guards(part) and small[0]=='div':
                c=m.num(small[1]);den=small[2];p=1 if den==n else den[2] if den[:2]==('pow',n) else 0
                if c is not None and c>0 and p>0:return out(('abs',part[1]),f'sqrt({c})/{index}^({p}/2)',True,
                    'По неравенству треугольника разность между √(u²+s²) и |u| лежит от нуля до |s|. Оценка годится также в нулях u.',decay_power=q(F(p,2)))
    if raw[0]=='mul' and lo is not None and lo>0:
        # Direct multiplication exposes the main factor and an increment of the square root or atan profile.
        scale,diff=raw[1:]
        if scale==n and diff[0]=='add' and diff[1][0]=='sqrt' and diff[2]==('mul',q(-1),('sqrt',x)) and guards(diff[1][1]):
            A=m.num(m.mul(n,m.add(diff[1][1],m.neg(x))))
            if A is not None and A>0:
                factor=m.div(q(A*A),m.mul(q(8*lo),('sqrt',q(lo))))
                return out(m.div(q(A),m.mul(q(2),('sqrt',x))),source(m.div(factor,n)),True,
                           'Рационализуем разность корней. После вычитания предельного выражения тот же приём даёт второй обратный множитель. Положительная нижняя граница x превращает оценку в C/n.')
    if raw[0]=='mul' and lo is not None and lo>=0:
        a0,phase=raw[1:] if raw[1]==x else tuple(reversed(raw[1:]))
        if a0==x and phase[0]=='atan' and guards(phase[1]):
            c=m.num(m.div(phase[1],m.mul(n,x)))
            if c is not None and c>0:return out(m.mul(m.div(m.PI,q(2)),x),source(m.div(q(1/c),n)),True,
                'Для положительного аргумента разность арктангенсов равна арктангенсу обратного аргумента. Его модуль не больше аргумента, и множитель x сокращает пространственный знаменатель. В нуле обе функции равны нулю.')
    if (lo is not None and lo>=0 and hi is not None and raw[0]=='rpow' and raw[2]==('div',ONE,n)
            and raw[1][0]=='add' and power in raw[1][1:]):
        const=next(a for a in raw[1][1:] if a!=power) if raw[1][1:]!=(power,power) else ZERO;c=m.num(const)
        if c is not None and c>0:
            return out(('max',ONE,x),'O(1/n) uniformly on the given bounded interval',True,
                       'Сумма двух неотрицательных степеней лежит между большей степенью и её удвоением. Берём корень порядка n и используем ограниченность точки и c^(1/n).',constant=q(c))
    raise Unsupported('No checked elementary uniform error on the given interval')


def uniform_sequence_abstract(task,library):
    if not library.data.get('elementary_uniform_errors'):
        raise Unsupported('The uniform error rules are not available')
    meta=task.get('source',{})
    if (set(task)-{'id','kind','source','interval','index','variable','printed_conditions','function','requested_output'} or
            not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','pdf_sha256','page_png_sha256','printed_subpart','literal_requirement'} or
            meta.get('literal_requirement') not in (None,'Доказать равномерную сходимость при данных условиях.') or
            task.get('requested_output')!=['proof_of_stated_uniform_convergence']):
        raise Unsupported('Unknown requirements in the uniform limit theorem')
    n,x=task['index'],task['variable'];interval=task['interval'];condition=task['printed_conditions'];formula=task['function']
    for name in (n,x):m.context(dict(variable=name))
    if n==x:raise Unsupported('Distinct spatial and index variables are required')
    if (match:=re.fullmatch(r'floor\('+n+r'\*([A-Za-z_]\w*)\('+x+r'\)\)/'+n,formula)):
        f=match[1]
        if condition!=f'{f} arbitrary on {interval}. Prove uniform convergence to {f}.' or not re.fullmatch(r'\[\w+,\w+\]',interval):
            raise Unsupported('The unrestricted function and its given domain must be bound')
        method='method.uniform_floor_quantization';value=f+'('+x+')';bound=f'1/{n}'
        arg='По определению целой части 0≤n f(x)−floor(n f(x))<1. Делим на положительное n и получаем одну оценку во всех точках.'
    elif (match:=re.fullmatch(n+r'\*\(([A-Za-z_]\w*)\('+x+r'\+1/'+n+r'\)-\1\('+x+r'\)\)',formula)):
        f=match[1];ends=re.fullmatch(r'\[([A-Za-z_]\w*),([A-Za-z_]\w*)\]',interval)
        hypothesis=re.fullmatch(rf'{f} has continuous derivative in \(([A-Za-z_]\w*),([A-Za-z_]\w*)\), \1<([A-Za-z_]\w*)<([A-Za-z_]\w*)<\2\. Prove uniform convergence to the derivative\.',condition)
        if not ends or not hypothesis or ends.groups()!=hypothesis.groups()[2:] or len(set(hypothesis.groups()))!=4:
            raise Unsupported('Need a compact interval strictly inward of the stated differentiability area')
        method='method.uniform_mean_value_difference';value=f+"'("+x+')';bound="modulus of continuity of f' at 1/"+n
        arg='Берём замкнутый промежуток чуть шире исходного, внутри области непрерывной производной. Для всех достаточно больших n точки x и x+1/n лежат в нём. Теорема о среднем и равномерная непрерывность производной дают общий остаток.'
    else:
        matched=re.fullmatch(r'sum\(([A-Za-z_]\w*)\('+x+r'\+([A-Za-z_]\w*)/'+n+r'\)/'+n+r',\2,0,'+n+r'-1\)',formula)
        if (not matched or len({n,x,*matched.groups()})!=4 or not re.fullmatch(r'\[\w+,\w+\]',interval) or
                condition!=matched[1]+' continuous on R. Prove uniform convergence on every finite segment.'):
            raise Unsupported('Need translated left Riemann sums of the given continuous function')
        method='method.uniform_translated_riemann_sums';value=f'∫_0^1 {matched[1]}({x}+t) dt';bound='common modulus of continuity at 1/'+n
        arg='Все отрезки x+[0,1] лежат в одном компакте. Сравниваем каждый прямоугольник с интегралом на его основании. Общий модуль непрерывности на масштабе 1/n ограничивает ошибку всей суммы.'
    return dict(theorem=method,argument=arg,source_condition=condition,error_bound=bound),dict(uniform=True,pointwise_limit=value)

def weierstrass_tail_envelopes(task,library):
    """Verify the original finite terms, then compare the tail with a summable numerical envelope."""
    from graphs import interval_terms
    from math import factorial
    fields={'kind','id','source','term','index','variable','start_index','interval','parameters','conditions','method_requirement','requested_output'}
    nname,xname,start=task['index'],task['variable'],task['start_index'];n,x=('s',nname),('s',xname)
    interval=task['interval'];pars=task.get('parameters',[]);cond=task.get('conditions',[])
    if (not library.data.get('general_uniform_series_tails') or set(task)-fields or type(start) is not int or not 1<=start<=512
            or nname==xname or {nname,xname}&set(pars) or not uniform_series_source(task,majorant=True)
            or task.get('method_requirement','weierstrass_majorant')!='weierstrass_majorant'
            or task.get('requested_output')!=['uniform_convergence','proof']):
        raise Unsupported('An original Weierstrass test with its complete initial domain is required')
    for name in (nname,xname):m.context(dict(variable=name))
    raw=m.parse(task['term'],None,(nname,xname,*pars),extra_functions=('factorial','floor'))
    def out(bound,argument,**plan):
        return dict(theorem='method.weierstrass_tail_envelopes',argument=argument,original_start=start,
                    majorant=bound,**plan),dict(uniform=True,absolute_at_every_point=True,criterion='weierstrass_majorant')
    def power_index(e):
        return 1 if e==n else e[2] if e[:2]==('pow',n) and e[2]>0 else 0 if e==ONE else None
    def compact_radius():
        if len(pars)==1 and interval==f'(-{pars[0]},{pars[0]})' and cond in ([pars[0]+'>0'],[]):
            m.context(dict(variable=xname,parameters=pars));return pars[0]
        if not pars and not cond:
            a,b,_,_=interval_terms(interval,dict(parameters=[]));values=[m.num(z) for z in (a,b) if not isinstance(z,str)]
            if len(values)==2 and all(z is not None for z in values):return q(max(map(abs,values)))
        raise Unsupported('The fixed spatial bound is not established')
    if not pars and not cond and raw[0]=='div' and raw[2][0]=='add' and x in raw[2][1:]:
        scale=raw[2][2] if raw[2][1]==x else raw[2][1];wave=raw[1]
        if scale[0]=='rpow' and scale[2]==n and (C:=m.num(scale[1])) is not None and C>1:
            if wave!=('rpow',q(-1),n) and (wave[0] not in ('sin','cos') or domain_conditions(wave[1])):
                raise Unsupported('Need a bounded everywhere-defined numerator')
            a,_,closed,_=interval_terms(interval,dict(parameters=[]));left=m.num(a) if not isinstance(a,str) else None
            if left is None or left<-C**start or left==-C**start and closed:
                raise Unsupported('The first original denominator can vanish')
            tail=start
            while C**tail<2*abs(left) and tail<start+256:tail+=1
            if C**tail<2*abs(left):raise Unsupported('A quantitative lower tail base could not be found')
            return out(f'2/{C}^{nname}',
                       'На всём промежутке проверяем знак знаменателя начиная с первого индекса. Отдельные начальные члены могут быть неограниченными, но определены. На хвосте знаменатель не меньше половины экспоненциального слагаемого, а числитель ограничен единицей.',
                       first_bounded_index=tail,spatial_lower_bound=q(left))
    if not pars and not cond and raw[0]=='div' and raw[1][0]=='mul' and raw[2]==('sqrt',('factorial',n)):
        scalar,plus=raw[1][1:];exponent=power_index(scalar)
        band=re.fullmatch(r'(.+)<=abs\('+re.escape(xname)+r'\)<=(.+)',interval)
        if (exponent is not None and band and plus[0]=='add' and set(plus[1:])=={
                ('rpow',x,n),('rpow',x,('mul',q(-1),n))}):
            a,b=map(exact_rational,band.groups())
            if not 0<a<=b:raise Unsupported('Both absolute-value interval bounds are required')
            R=max(b,1/a)
            return out(f'2*{nname}^{exponent}*({R})^{nname}/sqrt({nname}!)',
                       'Используем обе границы модуля точки для прямой и обратной степеней. Отношение соседних положительных мажорант стремится к нулю за счёт факториала.',
                       lowest_modulus=q(a),greatest_modulus=q(b))
    if raw[0]=='div' and raw[1]==('rpow',x,n) and raw[2][0]=='factorial' and raw[2][1][0]=='floor':
        phase=raw[2][1][1]
        if phase[0]=='div' and phase[1]==n and (d:=m.num(phase[2])) is not None and d>=1 and d.denominator==1:
            R=compact_radius();bound=source(R) if not isinstance(R,str) else R
            return out(f'{bound}^{nname}/floor({nname}/{d})!',
                       'Ограничиваем модуль точки фиксированным радиусом. На каждом классе вычетов индекс факториала растёт на единицу, поэтому каждый из конечного числа полученных рядов сходится по отношению членов.',
                       residue_classes=d.numerator,radius=R)
    if raw[0]=='ln' and raw[1][0]=='add' and raw[1][1]==ONE and raw[1][2][0]=='div' and start>=2:
        a,b=raw[1][2][1:];s=b[2] if b[0]=='mul' and b[1]==n else ZERO
        if (a[:2]==('pow',x) and a[2]>0 and not a[2]%2 and s[:2]==('pow',('ln',n)) and s[2]>1):
            R=compact_radius();bound=source(R) if not isinstance(R,str) else 'abs('+R+')'
            return out(f'{bound}^{a[2]}/({nname}*ln({nname})^{s[2]})',
                       'При n≥2 знаменатель положителен. Применяем ln(1+u)≤u при u≥0 и ограничиваем пространственную степень на всём промежутке. Интегральный признак после замены t=ln n даёт сходимость числовой мажоранты.',
                       radius=R,index_start_checked=start)
    if not pars and not cond and interval in ('[0,+infinity)','(0,+infinity)') and (nname,xname)==('n','x'):
        kind,C,alpha,degree,c,r,_=concentration_profile(raw,F(1),None);d=degree/r;t=ceil(d)
        if kind=='exponential' and d-alpha>1:
            coef=q(C*factorial(t)*max(F(1),c**(-t)))
            return out(source(coef)+f'/{nname}^({d-alpha})',
                       'Вводим t=c n x^r. Для t≤1 нормированная пространственная степень ограничена единицей. Для t≥1 используем член положительного ряда экспоненты с целой степенью не меньше показателя профиля. Остаётся сходящийся числовой степенной ряд.',
                       spatial_power=q(degree),decay=q(d-alpha),scale=q(c))
    raise Unsupported('No summable uniform majorant for the original analytic envelope')


def reciprocal_phase_series(task):
    """Use a small-phase majorant pointwise and a moving fixed-phase witness uniformly."""
    index,var,start,interval,condition=series_interval_input(task);n,x=('s',index),('s',var)
    raw=m.parse(task['term'],None,(index,var));kind='method.uniform_phase_primitive'
    if start<1 or condition or interval!='(0,+infinity)' or raw[0]!='mul' or raw[1][:1]!=('rpow',):
        raise Unsupported('Need the original positive moving-phase interval')
    height,wave=raw[1:];A=m.num(height[1]);phase=wave[1] if wave[0]=='sin' else ZERO
    if (height[2]!=n or A is None or A<1 or phase[0]!='div' or phase[2][0]!='mul' or phase[2][2]!=x
            or phase[2][1][:1]!=('rpow',) or phase[2][1][2]!=n):
        raise Unsupported('No verified exponential moving phase')
    C=m.num(phase[1]);B=m.num(phase[2][1][1])
    if C is None or C<=0 or B is None or B<=A:raise Unsupported('The pointwise geometric bound is not summable')
    return (dict(theorem=kind,moving_point=f'{C}/({B})^{index}',pointwise_rate=q(A/B),
                 argument='При каждом фиксированном x>0 используем |sin u|≤|u| и получаем сходящуюся геометрическую мажоранту. В движущейся точке аргумент синуса равен 1, а модуль члена не стремится к нулю. Поэтому равномерной сходимости нет.'),
            dict(uniform=False,absolute_at_every_point=True))

def functional_request(task,typed,raw_forms,printed,native):
    """Bind a typed functional statement to any retained source text and requested conclusion."""
    meta=task.get('source',{});raw=task.get('statement');want=task.get('requested_output')
    if (set(task)-{'kind','id','source','statement','functional_statement','requested_output'} or
            not isinstance(meta,dict) or set(meta)-{
                'exercise','pdf_page','printed_page','pdf_sha256','page_png_sha256','printed_subpart','literal_requirement'} or
            raw is not None and raw not in raw_forms or
            want not in (None,[native],[printed]) or
            meta.get('literal_requirement') not in (None,printed,*raw_forms)):
        raise Unsupported('The typed functional goal differs from a retained source obligation')
    if task['functional_statement']!=typed:raise Unsupported('The functional goal has extra or different hypotheses')


def regularity_of_series(task,library):
    if not library.data.get('uniform_series_calculus'):
        raise Unsupported('The local uniform derivative bounds are absent from the library')
    src=task['functional_statement'];term=src['term'];n,x=('s','n'),('s','x');raw=m.parse(term,None,('n','x'))
    dom=src.get('domain');ind=src.get('indices','n>=1');reg=src.get('required_regularity');lattice='n in Z'
    def bind(body,label,native,typed=None,require_domain=True):
        if require_domain:
            suffix='x in R' if dom=='R' else dom
            source_forms=(f'{fun}(x)=sum_{{{body}}} {term}, {suffix}' for fun in ('f','zeta','theta','g'))
        else:source_forms=(f'{fun}(x)=sum_{{{body}}} {term}' for fun in ('f','g'))
        functional_request(task,typed or dict(term=term,domain=dom,**({'indices':ind} if 'indices' in src else {}),
                                              required_regularity=reg),tuple(source_forms),label,native)
    def certificate(theorem,arg,**value):return dict(theorem=theorem,argument=arg,source_term=raw,source_indices=ind),value
    if task['kind']=='series_operation_justification' and src.get('question')=='termwise differentiation':
        print_text='Законно ли почленное дифференцирование ряда?';start=src['start']
        functional_request(task,dict(term=term,start=start,question='termwise differentiation'),
                           (f'sum_{{n>={start}}} {term}',),print_text,'termwise differentiation')
        if type(start) is not int or start<1 or raw[0]!='atan' or raw[1][0]!='div':
            raise Unsupported('Need a positive-index arctangent family')
        a,den=raw[1][1:];C=m.num(m.div(a,x)) if not domain_conditions(a) else None
        if C is None or not C or den[:2]!=('pow',n) or den[2]<=1:raise Unsupported('A summable derivative envelope has not been proved')
        slope=m.div(q(C),m.mul(den,m.add(ONE,m.power(raw[1],2))))
        return certificate('method.local_uniform_series_differentiation',
            'Члены обращаются в нуль в одной и той же точке. Их производные мажорируются сходящимся числовым степенным рядом на всей прямой. Это устанавливает законность почленного дифференцирования.',
            valid=True,domain='R',derivative_term=slope,majorant=q(abs(C)),decay_power=den[2])
    if task['kind']!='functional_series_regularity':raise Unsupported('Unknown series calculus claim')
    if reg=='C^infinity' and ind=='n>=1' and re.fullmatch(r'x>(.+)',dom or '') and raw[0]=='div' and raw[1]==ONE:
        power=raw[2];edge=exact_rational(dom[2:])
        if power[0]=='rpow' and power[1]==n and edge>=1 and not domain_conditions(power[2]):
            coeff=m.rational_form(power[2]);p,d=coeff;P=poly.univariate_coefficients(p,x)
            if d=={():F(1)} and P and len(P)==2 and P[1]>0 and P[0]+P[1]*edge>=1:
                bind('n>=1','Доказать непрерывность и существование непрерывных производных всех порядков.','all derivatives')
                return certificate('method.local_uniform_series_differentiation',
                    'На каждом компакте показатель n больше единицы с фиксированным запасом. При каждом дифференцировании появляется множитель, пропорциональный ln n. Любая его фиксированная степень поглощается половиной запаса степенного убывания.',
                    regularity=reg,domain=dom,derivative_multiplier=m.neg(m.mul(q(P[1]),('ln',n))))
    if reg=='C^infinity' and ind=='Z' and dom=='x>0' and raw[0]=='exp' and not domain_conditions(raw[1]):
        pn,pd=m.rational_form(raw[1])
        if pd=={():F(1)} and len(pn)==1:
            (mon,C),=pn.items();degrees=dict(mon)
            if C<0 and set(degrees) in ({x,n},{x,n,m.PI}) and degrees[x]==1 and degrees[n]>0 and degrees[n]%2==0 and degrees.get(m.PI,1)==1:
                bind(lattice,'Доказать определённость и бесконечную дифференцируемость.','all derivatives')
                return certificate('method.local_uniform_series_differentiation',
                    'На каждом компакте x≥δ>0 отрицательная экспонента мажорирует все степенные множители, возникающие при любом конечном числе производных. Нулевой индекс даёт постоянную, обе бесконечные стороны абсолютно сходятся вместе с производными.',
                    regularity=reg,domain=dom,derivative_multiplier=m.div(raw[1],x))
    if reg and (order:=re.fullmatch(r'C\^(\d+)',reg)) and dom=='R' and ind=='n>=1' and raw[0]=='div':
        wave,den=raw[1:];k=int(order[1]);label='Показать непрерывность суммы и существование непрерывной производной.'
        if (wave[0] in ('sin','cos') and den[:2]==('pow',n) and den[2]>k+1 and not domain_conditions(wave[1])):
            P,D=m.rational_form(wave[1]);cross=dict(((n,1),(x,1)))
            if D=={():F(1)} and P and all(dict(a) in ({},cross) for a in P) and (k==1 or not task.get('statement')):
                bind('n>=1',label if k==1 else None,'finite derivative order')
                return certificate('method.local_uniform_series_differentiation',
                    'Модуль тригонометрической функции ограничен единицей. Каждое дифференцирование по x добавляет не более одной степени n, поэтому для всех нужных порядков сохраняется сходящаяся числовая мажоранта.',
                    regularity=reg,domain=dom,highest_derivative_decay=den[2]-k)
    if ind=='Z' and raw[0]=='div' and raw[2][0]=='pow' and raw[2][2]>1 and not domain_conditions(raw[2][1]):
        c=m.num(raw[1]);u=raw[2][1];p,d=m.rational_form(u)
        if (c is not None and c!=0 and d=={():F(1)} and set(p)=={((n,1),),((x,1),)} and p[((x,1),)]==-1 and p[((n,1),)]>0):
            spacing=p[((n,1),)];period=src.get('claimed_period')
            if period is not None:
                label='Показать периодичность с периодом '+period+'.';shift=exact_rational(period)/spacing
                bind(lattice,label,'prove period',dict(term=term,indices=ind,claimed_period=period),False)
                if shift.denominator!=1 or shift==0:raise Unsupported('The proposed shift does not preserve the pole lattice')
                return certificate('method.lattice_series_reindexing',
                    'Вне исходных полюсов обе стороны двустороннего ряда абсолютно сходятся. Положительное расстояние от решётки сохраняется при заявленном сдвиге, который переиндексирует всю решётку.',
                    period=q(shift*spacing),excluded_lattice_spacing=q(spacing),index_shift=q(shift))
            bind(lattice,'Показать, что определена и непрерывна во всех точках, кроме целых.' if spacing==1 else None,
                 'definition domain and continuity',dict(term=term,indices=ind,question='definition domain and continuity'),False)
            return certificate('method.lattice_series_reindexing',
                'Вне точных полюсов все конечные члены непрерывны. На каждом компакте модуль знаменателя на обеих бесконечных сторонах растёт не медленнее фиксированной доли |n|, поэтому хвост равномерно суммируем.',
                continuous=True,excluded_lattice_spacing=q(spacing),majorant_power=raw[2][2])
    raise Unsupported('No checked derivative envelope or reindexing on the original parameter domain')


def uniform_source_witness(task,library,request):
    src=task['functional_statement'];term=src['term'];domain=src['domain'];start=src['start']
    n,x=('s','n'),('s','x');raw=m.parse(term,None,('n','x'))
    if not library.data.get('uniform_series_calculus') or type(start) is not int or start<0:
        raise Unsupported('No verified uniform series witness on the source indices')
    question=src.get('question')
    if question=='does absolute pointwise and uniform convergence imply uniform convergence of the absolute series':
        label='Следует ли из абсолютной и равномерной сходимости равномерная сходимость ряда модулей? Рассмотреть данный пример.'
        functional_request(task,dict(domain=domain,term=term,start=start,question=question),
                           (f'sum_{{n>={start}}} {term}, 0<=x<=1',),label,question)
        if domain!='[0,1]' or raw[0]!='mul' or raw[1][0]!='mul' or raw[1][1]!=('rpow',q(-1),n) or raw[2]!=('rpow',x,n):
            raise Unsupported('No separated alternating sign and geometric source term')
        pref=raw[1][2];core=('mul',pref,raw[2]);qtask=dict(kind='uniform_series_convergence',term=source(core),
              interval=domain,index='n',variable='x',start_index=start,requested_output=['convergence_character','proof'])
        child=request('pointwise and uniform convergence of the same magnitudes without alternating signs',qtask)
        value=child['value']
        if not value['absolute_at_every_point'] or value['uniform'] or child['compilation']['theorem']!='method.uniform_geometric_envelope':
            raise Unsupported('The transformed magnitudes do not give a nonuniform counterexample')
        # The verified quotient was obtained by exact polynomial division by 1-x.
        Q=freeze(child['compilation']['quotient']);p,d=m.rational_form(Q)
        coeff=poly.univariate_coefficients(p,x)
        if d!={():F(1)} or coeff is None:raise Unsupported('No bounded polynomial coefficient on the unit interval')
        C=sum(map(abs,coeff))
        return (dict(theorem='method.signed_geometric_tail_witness',majorant=q(C),
                     argument='На каждом x знак пространственного множителя одинаков для всех индексов, поэтому ряд модулей имеет тот же критерий равномерности, что и ряд без чередования знаков. Знакочередующийся хвост дополнительно ограничен C(1−x)x^(N+1), что равномерно стремится к нулю.'),
                dict(printed_implication=False,source_series_uniform=True,source_series_pointwise_absolute=True,
                     absolute_series_uniform=False))
    questions=['is convergence uniform','is the sum continuous']
    label='Доказать неравномерную сходимость к непрерывной на сегменте сумме.'
    functional_request(task,dict(term=term,domain=domain,start=start,questions=questions),
                       (f'sum_{{n>={start}}} ({term}), x in {domain}',),label,'nonuniform continuous sum')
    ends=re.fullmatch(r'\[0,([^,\]]+)\]',domain)
    if not ends or start!=1 or raw[0]!='add' or raw[2][0]!='mul' or raw[2][1]!=q(-1) or domain_conditions(raw):
        raise Unsupported('The full telescope including its initial term requires explicit domain checks')
    potential,shifted=raw[1],raw[2][2]
    if m.simplify(shifted)!=m.simplify(m.substitute(potential,{n:m.add(n,q(-1))})):
        raise Unsupported('The proposed consecutive difference is not the original term')
    lower=m.simplify(m.substitute(potential,{n:ZERO}));want=['pointwise convergence','uniform convergence']
    child=request('pointwise and uniform limits of the terminal potential',dict(kind='sequence_integral_interchange',
                  functional_statement=dict(sequence=source(potential),interval=['0',ends[1]],questions=want),requested_output=want))
    if lower!=ZERO or freeze(child['value']['pointwise_limit'])!=ZERO or child['value']['uniform_convergence']:
        raise Unsupported('The certified difference does not establish the stated continuous nonuniform limit')
    return dict(theorem='method.uniform_difference_of_rescaled_profiles',terminal_potential=potential,
                argument='Проверяем разность двух соседних значений потенциала. Начальное значение равно нулю, поэтому частичная сумма равна терминальному потенциалу. Отдельная цепочка находит его поточечный предел и проверяет движущийся максимум.'),dict(sum=ZERO,continuous=True,uniform=False)

def abstract_uniform_theorem(task,library):
    """Introduce quantifier, comparison and Abel obligations over general functions or coefficients."""
    if not library.data.get('abstract_uniform_theorems'):raise Unsupported('General uniform comparison is not admitted')
    src=task['functional_statement'];qst=src.get('question');dom=src.get('domain');term=src.get('term')
    def finish(theorem,typed,forms,printed,native,argument,**value):
        functional_request(task,typed,forms,printed,native)
        return dict(theorem=theorem,argument=argument,hypotheses=typed.get('hypotheses',[])),value
    def proof(theorem,typed,forms,printed,native,arg,**value):
        return finish(theorem,typed,forms,printed,native,arg,proved=True,**value)
    family='method.uniform_quantifier_equivalence'
    if criterion:=src.get('criterion'):
        seq=src.get('sequence','');match=re.fullmatch(r'([A-Za-z_]\w*)_n on ([A-Za-z_]\w*)',seq)
        if not match:raise Unsupported('The error supremum and its exact domain are required')
        f,A=match.groups()
        if src.get('limit')!=f or criterion!=f'lim_(n->infinity) sup_(x in {A}) abs({f}_n(x)-{f}(x))=0':
            raise Unsupported('The error supremum must compare the named sequence and limit')
        raw=f'Доказать критерий равномерной сходимости {f}_n к {f} на {A}: lim(n→inf) sup(x in {A}) abs({f}(x)-{f}_n(x))=0 тогда и только тогда, когда сходимость равномерная.'
        return proof(family,dict(sequence=seq,limit=f,criterion=criterion),(raw,),raw,'uniform error criterion',
            'Если все ошибки меньше ε/2, их верхняя грань не больше ε/2. Если верхняя грань меньше ε, она ограничивает каждую ошибку. На пустом множестве берём верхнюю грань неотрицательных ошибок равной нулю.',
            equivalence=True,cutoff_dependencies=['epsilon'])
    if isinstance(qst,str) and qst.startswith('definition of '):
        seq=src.get('sequence','');f=re.fullmatch(r'([A-Za-z_]\w*)_n',seq);left=re.fullmatch(r'\(([A-Za-z_]\w*),\+infinity\)',dom or '')
        if not f or not left:raise Unsupported('Need the declared sequence and whole right ray')
        on=f'({left[1]},+inf)';phrases={
            'definition of pointwise convergence':('поточечной сходимости на '+on,'∀x∈D ∀ε>0 ∃N(x,ε) ∀n≥N: |f_n(x)−f(x)|<ε',['point','epsilon']),
            'definition of uniform convergence on every finite subinterval':('равномерной сходимости на каждом конечном интервале (a,b) внутри '+on,
                '∀ bounded (a,b)⊂D ∀ε>0 ∃N(a,b,ε) ∀n≥N ∀x∈(a,b): |f_n(x)−f(x)|<ε',['finite_subinterval','epsilon']),
            'definition of uniform convergence on the whole interval':('равномерной сходимости на всём '+on,
                '∀ε>0 ∃N(ε) ∀n≥N ∀x∈D: |f_n(x)−f(x)|<ε',['epsilon'])}
        if qst not in phrases:raise Unsupported('Unknown order of the source quantifiers')
        wording,quant,depends=phrases[qst];raw='Что означает для последовательности '+seq+'(x) условие '+wording+'?'
        quant=quant.replace('f_n(',seq+'(').replace('f(',f[1]+'(')
        return finish(family,dict(sequence=seq,domain=dom,question=qst),(raw,),raw,qst,
                      'Выписываем условия на последовательность в порядке зависимостей числа N.',quantified_definition=quant,cutoff_dependencies=depends)
    if found:=re.fullmatch(r'sum_\(n in Z\) ([A-Za-z_]\w*)_n\*([A-Za-z_]\w*)\^n',src.get('series','')):
        a,x=found.groups();hypotheses=src.get('hypotheses',[])
        bound=re.fullmatch(r'converges at ([A-Za-z_]\w*) and ([A-Za-z_]\w*)',hypotheses[0]) if len(hypotheses)==2 else None
        if not bound or len({a,x,*bound.groups(),'n'})!=5:raise Unsupported('The two distinct convergent source radii are required')
        b,c=bound.groups();typed=dict(series=src['series'],hypotheses=[hypotheses[0],f'abs({b})<abs({c})'],
               goal=f'converges for abs({b})<abs({x})<abs({c})')
        raw=f'Доказать для двустороннего ряда Лорана sum({a}_n*{x}^n,n=-inf..inf), что сходимость при {b},{c}, |{b}|<|{c}|, влечёт сходимость всюду при |{b}|<|{x}|<|{c}|.'
        return proof('method.independent_laurent_tails',typed,(raw,),raw,'interior Laurent convergence',
            'Положительная и отрицательная части сходятся раздельно в исходном смысле. Их члены ограничены соответственно на внешнем и внутреннем радиусе. При промежуточном модуле каждая граница получает геометрический множитель с основанием меньше единицы.',
            absolute_on_open_annulus=True,inner_radius=b,outer_radius=c)
    if src.get('series')=='sum_(n>=1) a_n/n^x':
        typed=dict(series=src['series'],hypotheses=['converges at x=x0'],goal='convergence for x>x0')
        raw='Доказать, что сходимость ряда Дирихле sum(a_n/n^x,n=1..inf) при x=x0 влечёт сходимость при всех x>x0.'
        return proof('method.uniform_abel_multiplier',typed,(raw,),raw,'Dirichlet convergence halfline',
            'Берём исходные сходящиеся коэффициенты aₙ/n^x₀. Дополнительный вес n^(−(x−x₀)) положителен, не больше единицы и убывает. Суммирование по частям переносит оценку Коши на взвешенный хвост.',
            convergent_for='x>x0')
    if qst=='uniform convergence' and dom=='x>=0' and isinstance(term,str) and (
            term=='a_n/n^x' or (phase:=re.fullmatch(r'a_n\*exp\(-(?:(\d+(?:/\d+)?)\*)?n\*x\)',term)) and
            (phase[1] is None or exact_rational(phase[1])>=0)):
        raw='sum_{n>=1} a_n converges; sum_{n>=1} '+term;printed='Доказать равномерную сходимость при x>=0.'
        return proof('method.uniform_abel_multiplier',dict(term=term,domain=dom,hypotheses=['sum a_n converges'],question=qst),
            (raw,),printed,qst,
            'Для каждого параметра веса неотрицательны, убывают и не превосходят единицы. При суммировании по частям общий модуль конечного хвоста ограничен модулем Коши сходящегося числового ряда независимо от параметра.',
            uniform=True,domain=dom)
    if qst=='prove uniform convergence of sum f_n' and dom and re.fullmatch(r'\[\w+,\w+\]',dom):
        printed='Доказать равномерную сходимость sum f_n на '+dom+'.'
        return proof('method.uniform_cauchy_comparison',dict(domain=dom,hypotheses=['sum abs(f_n) converges uniformly'],question=qst),
            ('sum_{n>=1} abs(f_n) converges uniformly on '+dom,),printed,qst,
            'По неравенству треугольника модуль каждого конечного хвоста исходного ряда не больше хвоста ряда модулей. Его равномерная оценка Коши переносится на исходный ряд.',uniform=True)
    if qst=='absolute and uniform convergence on the whole interval' and dom and (
            ends:=re.fullmatch(r'\[([A-Za-z_]\w*),([A-Za-z_]\w*)\]',dom)):
        printed='Доказать абсолютную и равномерную сходимость на '+dom+'.'
        return proof('method.uniform_monotone_endpoint_majorant',dict(domain=dom,hypotheses=[
            'each phi_n is monotone',f'sum phi_n is absolutely convergent at {ends[1]} and at {ends[2]}'],question=qst),
            ('sum_{n>=1} phi_n(x), each phi_n monotone on '+dom+', absolutely convergent at both endpoints',),printed,qst,
            'Монотонность каждого члена ограничивает его модуль максимумом модулей на концах. Этот максимум не превышает суммы двух концевых модулей, которая суммируема по исходным условиям.',
            uniform=True,absolute_at_each_point=True)
    if qst=='absolute and uniform convergence' and dom=='each closed interval inside the convergence interval' and term=='a_n*x^n':
        printed='Доказать абсолютную и равномерную сходимость на каждом сегменте, целиком лежащем внутри интервала сходимости.'
        return proof('method.uniform_geometric_envelope',dict(term=term,domain=dom,question=qst),('sum_{n>=0} '+term,),printed,qst,
            'Между наибольшим модулем точки на заданном сегменте и радиусом выбираем больший промежуточный радиус. Члены ряда при этом радиусе ограничены. На сегменте к этой границе добавляется геометрический множитель с основанием меньше единицы.',
            absolute_at_each_point=True,uniform_on_each_inner_segment=True)
    if qst=='absolute and uniform convergence' and dom=='each bounded closed set avoiding all a_n' and isinstance(term,str) and (
            power:=re.fullmatch(r'1/\(x-a_n\)(?:\^([1-9]\d*))?',term)):
        degree=int(power[1] or 1)
        base='1/a_n' if degree==1 else '1/a_n^'+str(degree)
        printed='Доказать абсолютную и равномерную сходимость на каждом ограниченном замкнутом множестве K, не содержащем a_n.'
        return proof('method.uniform_receding_poles',dict(term=term,domain=dom,hypotheses=['a_n->+infinity','sum abs('+base+') converges'],question=qst),
            ('a_n->infinity; sum abs('+base+') convergent; sum_{n>=1} '+term,),printed,qst,
            'На замкнутом ограниченном множестве все начальные слагаемые определены. Для больших n расстояние |x−aₙ| не меньше |aₙ|/2 независимо от x. Возведение в степень даёт суммируемую мажоранту с постоянным множителем.',
            uniform=True,absolute_at_each_point=True,exponent=degree)
    if qst=='can discontinuous functions converge uniformly to a continuous function' and dom=='R':
        seq=src.get('sequence','');match=re.fullmatch(r'indicator_Q\(x\)/n(?:\^(\d+))?',seq)
        if not match or match[1]=='0':raise Unsupported('A vanishing multiple of a dense-set indicator is required')
        printed='Могут ли разрывные функции сходиться равномерно к непрерывной? Рассмотреть данный пример.'
        return finish('method.uniform_vanishing_indicator',dict(sequence=seq,domain=dom,question=qst),
            ('f_n='+seq+' on R, n>=1',),printed,qst,
            'В каждой окрестности есть рациональные и иррациональные точки. Поэтому каждый член разрывен всюду. Его модуль ограничен убывающим числовым множителем, так что предел нуль достигается равномерно.',
            example_works=True,uniform=True,continuous_limit=True,limit=ZERO)
    raise Unsupported('No applicable equivalence or comparison theorem for the stated quantified goal')


FUNCTIONAL_TRANSPORT_FIELDS={
    'functional_series_domain_regularity':{'term','start','questions'},
    'sequence_and_derivative_limit':{'sequence','domain','questions'},
    'limit_of_series':{'term','start','approach'},
    'uniform_sequence_rate':{'index','start','tolerance','sequence','domain','sampling'},
    'sequence_derivative_theorem':{'sequence','hypotheses','goal','printed_separate_example'},
    'uniform_sequence_extremum_theorem':{'sequence','hypotheses','question'},
}


def functional_transport_routing(task,kind):
    src=task.get('functional_statement')
    if not isinstance(src,dict):return False
    if kind in FUNCTIONAL_TRANSPORT_FIELDS:return FUNCTIONAL_TRANSPORT_FIELDS[kind]<=set(src)
    if kind=='functional_series_example':return 'support' in src
    if kind=='functional_series_regularity':return 'hypotheses' in src and str(src.get('term','')).startswith('abs(')
    return kind=='series_operation_justification' and src.get('question')=='termwise integration' and {'term','start','interval'}<=set(src)


def functional_transport_certificate(theorem,value,*arguments,**evidence):
    return dict(theorem='method.'+theorem,argument=list(arguments),**evidence),value


def read_series_regularity(task,lib,request):
    from operations import expression_positions
    from polynomial import rf
    from tasks import source
    from verify import same_value
    src=task['functional_statement'];term=src['term'];start=src['start'];questions=src['questions']
    if type(start) is not int or start<1 or questions not in (['convergence domain','continuity'],['convergence domain','differentiability']):
        raise Unsupported('Need the original series domain and its requested regularity')
    continuity=questions[1]=='continuity';label='непрерывность' if continuity else 'дифференцируемость'
    printed=f'Определить область существования и исследовать {label}.'
    functional_request(task,dict(term=term,start=start,questions=questions),
                       (f'sum_{{n>={start}}} {term}',f'sum_{{n>={start}}} ({term})'),printed,questions[1])
    n=('v','n');x=('s','x');raw=m.parse(term,'n',['x']);ctx=m.context(dict(variable='n',parameters=['x']))
    if raw[0]=='rpow' and raw[2]==n and continuity:
        child=dict(kind='functional_series_convergence_set',term=term,index='n',start_index=start,variables=['x'],
                   stated_conditions=[],requested_output=['absolute_convergence_set','conditional_convergence_set','proof'])
        certified=request('определить область сходимости исходного ряда перед проверкой непрерывности',child)
        plan=certified['compilation']
        if (plan.get('theorem')!='method.first_order_geometric_endpoint' or not plan.get('limiting_base')
                or any(e!=n for _,e in domain_conditions(raw[1]))):
            raise Unsupported('The child did not prove a compact-uniform geometric scale without hidden poles')
        return functional_transport_certificate('convergence_domain_before_local_uniformity',
                 dict(convergence_domain=certified['value']['absolute_convergence_set'],continuous_on_convergence_domain=True),
                 'Сначала поставить и проверить подцель об области сходимости. Она исключает границы, на которых корень приближается к единице и член не стремится к нулю.',
                 'На каждом компакте внутри найденной области предельное основание отделено от границы, а приращение обратно пропорционально индексу. Один геометрический ряд мажорирует весь хвост.',
                 'Каждый член непрерывен на исходном компакте. Равномерный предел даёт непрерывность суммы.',domain_goal=child)
    if raw[0]!='div':raise Unsupported('Need a normalized rational or geometric series on the given domain')
    top,den=raw[1:]
    if den[0]=='rpow' and den[2]==n and continuity and not domain_conditions(den[1]) and not domain_conditions(top):
        v=('v','regCoordinate');p,d=rf(m.substitute(top,{x:v}),v[1])
        A=m.add(den[1],q(-1));a,b=rf(m.substitute(A,{x:v}),v[1])
        if d==(1,) and b==(1,) and sum(z!=0 for z in p)==1 and sum(z!=0 for z in a)==1:
            k,j=len(a)-1,len(p)-1
            if k>0 and k%2==0 and a[-1]>0 and j>0:
                value=dict(sum_at_zero=ZERO,sum_off_zero=m.div(top,m.mul(A,m.power(den[1],start-1))),
                           convergence_domain='R',continuous_off_zero=True,continuous_at_zero=j>k)
                return functional_transport_certificate('geometric_sum_on_nonzero_and_zero_branches',value,
                         'Из исходного основания получить точную геометрическую сумму вне точки, где оно равно единице. В самой точке каждый исходный член равен нулю.',
                         'Сравнить степени числителя и знаменателя явной суммы. Это проверяет непрерывность в точке, где нельзя было делить на единицу минус основание.',
                         first_index=start,vanishing_order_of_numerator=j,vanishing_order_of_denominator=k)
    wave=('rpow',q(-1),n);polarity=[e for _,e in expression_positions(top) if e==wave]
    if len(polarity)==1 and not domain_conditions(top,positive_integer_exponents=(n,)) and not domain_conditions(den):
        with_sign=m.simplify(m.substitute(top,{wave:ONE}));without=m.simplify(m.substitute(top,{wave:ZERO}))
        coeff=m.add(with_sign,m.neg(without))
        if not same_value(top,m.add(without,m.mul(wave,coeff))):raise Unsupported('Only one independent alternating factor can be separated')
        from ordinary_series import polynomial_coefficients
        dc=polynomial_coefficients(den,n,ctx);cc=polynomial_coefficients(coeff,n,ctx)
        rate=max(dc,default=0);A=dc.get(0,ZERO)
        if (rate>0 and not set(dc)-{rate,0} and dc[rate]==ONE and set(cc)=={rate-1}
                and not m.variable_in(without) and (rate>=2 or without==ZERO)
                and (rate==1 or known_nonnegative_parameter(A,x))):
            g=cc[rate-1];removed=f'for every integer n>={start}, n+({source(A)})!=0' if rate==1 else 'R'
            # Check all coordinate coefficients are polynomial on the real line, so the
            # uniform remainders and their derivatives admit finite compact bounds.
            v=('v','regCoordinate')
            for e in (without,g,A):
                p,d=rf(m.substitute(e,{x:v}),v[1])
                if d!=(1,):raise Unsupported('A coordinate coefficient has its own pole')
            return functional_transport_certificate('subtract_uniform_reference_series',
                     dict(convergence_domain=removed,continuous_on_convergence_domain=True,
                          **({'differentiable_on_convergence_domain':True} if not continuity else {})),
                     'Отделить постоянный по индексу множитель при знакочередующемся гармоническом ряде. Разность записать с исходным знаменателем.',
                     'На каждом компакте остаточные члены имеют суммируемые оценки O(n⁻²). При запросе производной те же оценки получаются после дифференцирования коэффициентов и знаменателя.',
                     'Начальные знаменатели проверяются на исходной области. При линейном росте знаменателя любое напечатанное целое значение, где он равен нулю, исключено.',
                     reference_coefficient=g,denominator_index_degree=rate,source_offset=A)
    if top==('abs',x) and not continuity and not domain_conditions(den):
        from ordinary_series import polynomial_coefficients
        dc=polynomial_coefficients(den,n,ctx);rate=max(dc,default=0);A=dc.get(0,ZERO)
        if rate>=2 and not set(dc)-{rate,0} and dc[rate]==ONE and known_nonnegative_parameter(A,x):
            v=('v','regCoordinate');_,d=rf(m.substitute(A,{x:v}),v[1])
            if d!=(1,):raise Unsupported('The varying denominator does not have a bounded derivative on compacts')
            return functional_transport_certificate('absolute_factor_and_summable_smooth_envelopes',
                 dict(convergence_domain='R',differentiable_domain='R without 0',continuous_at_zero=True,
                      one_sided_slopes='±sum_{n≥start} 1/(n^d+A(0))'),
                 'Положительный знаменатель сравнивается с n^d. На каждом компакте ряд и его производные вне нуля имеют суммируемые мажоранты.',
                 'Разностное отношение в нуле равно знаку смещения, умноженному на ряд с тем же знаменателем. Равномерная мажоранта даёт одну положительную величину и противоположные знаки на двух сторонах.',
                 denominator_power=rate,first_index=start,source_offset=A)
    raise Unsupported('No certified regularity through a derived functional-series envelope')


def known_nonnegative_parameter(e,x):
    ctx=m.context(dict(variable='n',parameters=[x[1]]))
    if m.known_nonnegative(e,ctx):return True
    p,d=m.rational_form(e)
    return d=={():F(1)} and all(c>=0 and all(a==x and k%2==0 for a,k in j) for j,c in p.items())


def limit_from_series_transport(task):
    from integrals import affine
    from tasks import source
    from verify import same_value
    src=task['functional_statement'];term=src['term'];start=src['start'];approach=src['approach']
    if type(start) is not int or start<1 or approach not in (dict(point='1',side='left'),dict(point='0',side='right'),
                    dict(point='+inf',side='positive_infinity')):
        raise Unsupported('Need an original checked one-sided approach')
    point=approach['point'];suffix={'1':'1-','0':'0+','+inf':'infinity'}[point]
    n=('v','n');x=('s','x');raw=m.parse(term,'n',['x'])
    forms=[f'sum_{{n>={start}}} {term}, x->{suffix}',f'sum_{{n>={start}}} ({term}), x->{suffix}']
    if term=='(-1)^(n+1)*x^n/(n*(x^n+1))':forms.append(f'sum_{{n>={start}}} (-1)^(n+1)/n*x^n/(x^n+1), x->{suffix}')
    functional_request(task,dict(term=term,start=start,approach=approach),tuple(forms),'Найти предел.','limit')
    power=('rpow',x,n)
    if point=='1' and raw[0]=='add' and raw[1]==power and raw[2][0]=='mul' and raw[2][1]==q(-1):
        nxt=('rpow',x,m.add(n,ONE))
        if same_value(m.simplify(raw[2][2]),m.simplify(nxt)) and not domain_conditions(raw,positive_integer_exponents=(n,('add',n,ONE))):
            return functional_transport_certificate('sum_before_limit_of_unbounded_telescope',
                  dict(limit=ONE,termwise_boundary_limit=ZERO),
                  'Поставить промежуточную цель вычислить точную конечную сумму. Разность степеней телескопируется на исходных целых индексах.',
                  'В левой окрестности единицы последний член стремится к нулю при N→∞. После суммирования остаётся x^s с пределом единица.',
                  'Предел отдельного слагаемого равен нулю, поэтому менять порядок пределов без новой оценки нельзя.',
                  terminal_potential=nxt,first_index=start)
    if point=='1' and raw[0]=='div' and raw[1][0]=='mul' and raw[2][0]=='mul':
        phase,z=raw[1][1:];weight,D=raw[2][1:]
        if (z==power and phase[0]=='rpow' and phase[1]==q(-1) and weight==n and
                D[0]=='add' and power in D[1:] and not domain_conditions(phase[2])):
            c=m.num(D[2] if D[1]==power else D[1]);a,b=map(m.num,affine(phase[2],'n'))
            if c is not None and c>0 and a is not None and a.denominator==1 and a%2 and b is not None and b.denominator==1:
                sign=(-1)**(int(b)%2);prefix=sum(F((-1)**j,j) for j in range(1,start))
                value=m.mul(q(F(sign,1)/(1+c)),m.add(m.neg(('ln',q(2))),q(-prefix)))
                return functional_transport_certificate('endpoint_limit_under_uniform_alternating_tail',dict(limit=value),
                     'В исходной левой окрестности x^n убывает по n. Положительное отношение x^n/(c+x^n) также убывает, а его произведение с 1/n ограничено 1/n.',
                     'Равномерная оценка остатка Лейбница допускает почленный переход к единице. После подстановки остаётся знакочередующийся гармонический ряд с точно учтённым началом.',
                     first_index=start,uniform_tail_bound='1/(N+1)')
    if point=='0' and raw[0]=='div' and raw[1]==ONE and raw[2][0]=='mul':
        B,N=raw[2][1:]
        if B[0]=='rpow' and B[2]==n and (b:=m.num(B[1])) is not None and b>1 and N==('rpow',n,x):
            lim=F(1)/(b**start*(1-F(1)/b))
            return functional_transport_certificate('endpoint_limit_under_positive_summable_envelope',dict(limit=q(lim)),
                   'При x≥0 множитель n^x не меньше единицы. Обратный геометрический фактор мажорирует все исходные члены.',
                   'Почленные пределы равны геометрическим мажорантам. Их суммирование с исходного индекса даёт ответ.',
                   first_index=start,majorant=('rpow',q(F(1)/b),n))
    if point=='+inf' and raw[0]=='div' and raw[1]==('pow',x,2):
        den=raw[2];wanted=m.add(ONE,m.mul(m.power(n,2),m.power(x,2)))
        if not domain_conditions(den) and same_value(wanted,den):
            initial=sum(F(1,j*j) for j in range(1,start))
            zeta=m.div(m.power(m.PI,2),q(6));value=m.add(zeta,q(-initial))
            return functional_transport_certificate('endpoint_limit_under_positive_summable_envelope',dict(limit=value),
                   'На всей вещественной области член неотрицателен и не превосходит 1/n². Для каждого индекса предел при x→+∞ равен 1/n².',
                   'Суммируемая мажоранта разрешает переход к пределу под знаком ряда. Для вычисления суммы 1/n² используем равенство Парсеваля для функции x, синусные коэффициенты 2(−1)^(n+1)/n и квадратная норма 2π²/3.',
                   first_index=start,majorant=m.div(ONE,m.power(n,2)))
    raise Unsupported('The source approach still needs a summable or telescoping bound')


def integrated_telescoping_powers(task):
    from integrals import affine
    from verify import same_value
    src=task['functional_statement'];term=src['term'];start=src['start'];n=('v','n');x=('s','x')
    if type(start) is not int or start<1 or src.get('interval')!=['0','1']:raise Unsupported('Need the original positive unit interval')
    functional_request(task,dict(term=term,start=start,interval=['0','1'],question='termwise integration'),
        (f'sum_{{n>={start}}} ({term}), 0<=x<=1',),'Законно ли почленное интегрирование ряда на сегменте?','termwise integration')
    raw=m.parse(term,'n',['x'])
    if raw[0]!='add' or raw[1][0]!='rpow' or raw[1][1]!=x or raw[2][0]!='mul' or raw[2][1]!=q(-1) or raw[2][2][0]!='rpow' or raw[2][2][1]!=x:
        raise Unsupported('Need an exact difference of two original powers')
    p,q0=raw[1][2],raw[2][2][2]
    if p[:2]!=('div',ONE) or q0[:2]!=('div',ONE) or domain_conditions(p[2]) or domain_conditions(q0[2]):
        raise Unsupported('Both reciprocal exponents must be defined on the whole lattice')
    a,b=map(m.num,affine(p[2],'n'))
    if a is None or a<=0 or b is None or a*(start-1)+b<=0 or not same_value(q0[2],m.substitute(p[2],{n:m.add(n,q(-1))})):
        raise Unsupported('The previous exponent and its strictly positive initial denominator do not follow from the source')
    p0=q(F(1)/(a*(start-1)+b));value=q(F(1)/(1+a*(start-1)+b))
    return functional_transport_certificate('integral_limit_of_telescoping_powers',
          dict(termwise_integration_valid=True,integral=value,sum_for_x_positive=('add',ONE,('mul',q(-1),('rpow',x,p0))),sum_at_zero=ZERO),
          'Проверить точный сдвиг исходных показателей. Частичная сумма равна терминальной степени минус исходная начальная степень.',
          'При x>0 терминальная степень стремится к единице, а в x=0 все исходные члены равны нулю. Полученная сумма интегрируема.',
          'Интегрирование конечных сумм даёт точный предел, равный интегралу предельной суммы. Поэтому запрошенная перестановка верна даже без равномерной сходимости на замкнутом сегменте.',
          first_index=start,initial_exponent=p0)


def sequence_derivative_transport(task):
    from integrals import affine
    from tasks import known_guard
    src=task['functional_statement'];term=src['sequence'];point=src.get('derivative_point')
    n=('v','n');x=('s','x');raw=m.parse(term,'n',['x'])
    if src.get('domain')!='R' or src.get('questions')!=['uniform convergence','interchange of derivative and limit']:
        raise Unsupported('Need both comparisons on the original whole line')
    if point is not None:
        printed='Доказать равномерную сходимость и неравенство производной предела в 1 и предела производных в 1.'
        functional_request(task,dict(sequence=term,domain='R',derivative_point=point,questions=src['questions']),
            (f'f_n(x)={term}, x in R, n>=1',),printed,'uniform convergence and derivative discrepancy')
        if point!='1' or raw[0]!='div' or raw[2]!=n or raw[1][0]!='atan' or raw[1][1]!=('rpow',x,n):
            raise Unsupported('The uniform arctangent bound and the fixed derivative witness do not bind the original source')
        return functional_transport_certificate('bounded_error_vs_uncontrolled_derivative',
                dict(uniform_limit=ZERO,uniform=True,derivative_of_limit_at_point=ZERO,limit_of_derivatives_at_point=q(1,2)),
                'Глобальный модуль арктангенса не превосходит π/2. После деления на индекс получается равномерная нулевая граница.',
                'При дифференцировании множитель n из целой степени сокращает знаменатель. В исходной точке x=1 производная равна 1/2 при каждом индексе.',
                'Производная нулевого предела равна нулю. Это устанавливает несовпадение отдельно от равномерности исходных функций.',
                uniform_error_bound='pi/(2*n)',point=ONE)
    printed='Доказать равномерную сходимость и отсутствие общего тождества между производной предела и пределом производных.'
    functional_request(task,dict(sequence=term,domain='R',questions=src['questions']),
        (f'f_n(x)={term}, x in R, n>=1',),printed,'uniform convergence and derivative discrepancy')
    if raw[0]!='add' or raw[2][0]!='div' or raw[2][2]!=n or raw[2][1][0]!='sin' or domain_conditions(raw[1]):
        raise Unsupported('Need a checked fixed profile plus oscillatory error')
    phase=raw[2][1][1]
    if phase[0]!='mul' or phase[1]!=n or any(
            not known_guard(g,m.context(dict(variable='n',parameters=['x']))) for g in domain_conditions(phase[2])):
        raise Unsupported('The phase must have an independently bound affine coordinate')
    v=('v','x');s,t=affine(m.substitute(phase[2],{x:v}),'x')
    if m.num(s) is None or not m.num(s) or not m.constant_defined(t,m.context(dict(variable='x'))) or m.variable_in(raw[1]):
        raise Unsupported('The derivative witness needs a nonzero affine slope and fixed main profile')
    point=m.div(m.neg(t),s)
    if any(not known_guard((g,m.substitute(e,{x:point})),m.context(dict(variable='x')))
           for g,e in domain_conditions(raw[1],True)):
        raise Unsupported('The fixed limiting profile lacks a derivative at the generated witness')
    return functional_transport_certificate('bounded_error_vs_uncontrolled_derivative',
              dict(uniform_limit=raw[1],uniform=True,derivative_difference_at_witness=s),
              'Синус делится на растущий индекс, поэтому ошибка ограничена 1/n на всей прямой.',
              'Поставить промежуточную цель о нуле аффинной части фазы. В найденной точке косинус равен единице при каждом индексе.',
              'При дифференцировании индекс сокращается и в этой точке остаётся ненулевая добавка, отсутствующая у производной предельного профиля.',
              uniform_error_bound='1/n',generated_witness=point)


def advanced_functional_transport(task):
    src=task['functional_statement'];k=task['kind']
    if k=='uniform_sequence_rate':
        sample=re.fullmatch(r'x=(\d+)\^\(-1/m\) for integers m>=1',src.get('sampling',''))
        start=src['start'];tol=exact_rational(src['tolerance'])
        if (not sample or int(sample[1])<=1 or type(start) is not int or start<1 or not 0<tol<1 or
                src.get('domain')!='0<x<1' or src.get('sequence')!='x^n' or src.get('index')!='n'):
            raise Unsupported('Need a positive geometric sampling and pointwise strict decay')
        b=int(sample[1]);raw=task.get('statement','')
        printed=re.fullmatch(r'Для x\^n, 0<x<1, найти наименьший номер N\(epsilon,x\), с которого ошибка в точке не превосходит ([\d.]+), при (x=\d+\^\(-1/m\)), m=1,2,… \. Выяснить равномерность на \(0,1\)\.',raw)
        if raw and (not printed or exact_rational(printed[1])!=tol or printed[2]!=sample[0].split()[0]):
            raise Unsupported('The printed numerical threshold or set of sample points differs')
        functional_request(task,dict(sequence='x^n',index='n',start=start,domain='0<x<1',sampling=sample[0],tolerance=src['tolerance']),
                           (raw,), 'Найти точный порог и выяснить равномерность.', 'geometric sequence threshold')
        exponent=next((a for a in range(1,65) if F(1,b**a)==tol),None)
        val=f'max({start},{exponent}*m)' if exponent is not None else f'max({start},ceil(m*ln(1/({tol}))/ln({b})))'
        return functional_transport_certificate('exact_geometric_threshold_and_moving_endpoint',
                 dict(least_index_at_sample=val,uniform=False,global_error_supremum=ONE),
                 'Знак ln x отрицательный. При применении логарифма к требованию погрешности направление сравнения для индекса меняется.',
                 'Округление вверх даёт первый допустимый индекс. Монотонное уменьшение гарантирует тот же порог для всего последующего хвоста.',
                 'На открытом промежутке верхняя грань x^n равна единице при каждом n. Поэтому найденные пороги не заменяются одним равномерным порогом.',
                 tolerance=q(tol),sampling_base=q(b))
    if k=='functional_series_example':
        h=re.fullmatch(r'(\d+)\^\(-n-1\)<x<\1\^\(-n\)',src.get('support',''))
        start=src.get('start')
        if not h or int(h[1])<2 or type(start) is not int or start<1 or src.get('outside_value')!='0' or src.get('domain')!='[0,1]':
            raise Unsupported('The original support intervals and zero region are not bound')
        b=h[1];term=f'sin({b}^(n+1)*pi*x)^2/n'
        text=f'sum_{{n>={start}}} f_n on [0,1]: f_n={term} for {h[0]}, 0 on 0<=x<={b}^(-n-1) and {b}^(-n)<=x<=1'
        goal='Доказать абсолютную и равномерную сходимость и невозможность мажорирования сходящимся числовым рядом с неотрицательными членами.'
        functional_request(task,dict(domain='[0,1]',term=term,support=h[0],outside_value='0',start=start,
            question='prove absolute and uniform convergence and rule out a summable positive termwise bound'),
            (text,),goal,'disjoint supports and impossibility of summable separate bounds')
        return functional_transport_certificate('disjoint_support_tail_and_separate_maxima',
                    dict(pointwise_absolute=True,uniform=True,uniform_tail='1/(N+1)',summable_separate_majorants=False),
                    'Поддержки попарно не пересекаются. В любой точке хвост состоит не более чем из одного ненулевого слагаемого, модуль которого не больше обратного индекса.',
                    'Для каждого индекса отдельно решить фазовое уравнение с sin²=1 внутри его поддержки. Этот максимум равен 1/n, поэтому любой набор отдельных мажорант не суммируем.',
                    support_base=q(int(b)),maximizer=f'3/(2*{b}^(n+1))')
    if k=='functional_series_regularity':
        h=re.fullmatch(r'abs\(x-r_k\)/(\d+)\^k',src.get('term',''))
        question=src.get('question')
        if not h or int(h[1])<2 or question not in ('continuity','differentiability at rational and irrational points'):
            raise Unsupported('Need an original summable family of translated absolute values')
        b=h[1];text=f'f=sum_{{k>=1}} {h[0]} on [0,1], r_k enumerate rationals of [0,1]'
        printed='Доказать непрерывность.' if question=='continuity' else 'Доказать дифференцируемость в иррациональных и недифференцируемость в рациональных точках.'
        functional_request(task,dict(term=h[0],domain='[0,1]',hypotheses=['r_k enumerate the rational numbers in [0,1]'],question=question),
                           (text,),printed,question)
        val=dict(continuous=True,lipschitz_constant=q(1,int(b)-1))
        if question!='continuity':
            val.update(differentiable_at_irrational_interior=True,rational_interior_jump=f'2*sum({b}^(-k) for r_k=x)>0',
                       endpoints='finite relative one-sided derivatives')
        return functional_transport_certificate('summable_envelopes_for_absolute_value_kinks',val,
                    'Разностные отношения каждого модуля ограничены его геометрическим весом независимо от центра. Сумма весов даёт липшицеву непрерывность.',
                    'Для производной переносим односторонние пределы через суммируемую мажоранту. Все слагаемые с совпадающим центром дают положительный скачок, остальные производные имеют одинаковые пределы.',
                    weight_base=q(int(b)),source_interval='[0,1]')
    gaussian='exp(-(x-n)^2)'
    if k=='sequence_derivative_theorem':
        typed=dict(sequence='f^(n)(x)',hypotheses=['f is smooth on R','f^(n) converges locally uniformly to phi'],
                   goal='phi(x)=C*exp(x)',printed_separate_example='f_n(x)='+gaussian)
        printed='Доказать, что phi(x)=C*exp(x). Рассмотреть напечатанный рядом пример.'
        functional_request(task,typed,(f'f smooth on R; f^(n) converges uniformly to phi on each finite open interval; example f_n={gaussian}',),
                           printed,'eigenfunction of derivative limit')
        return functional_transport_certificate('derivative_iteration_limit_is_eigenfunction',
                  dict(all_limits='C*exp(x)',example_local_uniform_limit=ZERO,example_global_uniform=False),
                  'Сдвинутая последовательность производных имеет тот же локально равномерный предел. На каждом компакте интегрирование равенства приращений и переход к пределу дают φ(x)−φ(a)=∫φ.',
                  'Непрерывность φ позволяет дифференцировать это равенство. Из φ′=φ следует постоянство e⁻ˣφ.',
                  'У напечатанного сдвига гауссиана на |x|≤M модуль не превосходит exp(−(n−M)²) при n>M. Максимум на всей прямой равен единице в движущейся точке n.',
                  verified_example=gaussian)
    if k=='uniform_sequence_extremum_theorem':
        base={'kind','id','source','statement','requested_output','functional_statement','printed_claim','printed_index_omission'}
        typed=dict(sequence='f_n',hypotheses=['each f_n is bounded on R','f_n converges uniformly to phi on each compact interval'],
                   question='does lim_n sup_x f_n(x)=sup_x phi(x) follow')
        print_statement='each f_n defined and bounded on R and converges uniformly to phi on every compact interval'
        printed='Следует ли равенство lim sup_x f(x)=sup_x phi(x)? В напечатанной левой части отсутствует индекс n.'
        if (set(task)-base or task.get('printed_claim')!='lim_(n->infinity) sup_x f(x)=sup_x phi(x)' or
                task.get('printed_index_omission') is not True or task.get('statement') not in (None,print_statement) or
                task.get('requested_output') not in (None,[printed]) or src!=typed):
            raise Unsupported('The literal omission and intended supremum question must be retained together')
        return functional_transport_certificate('compact_limits_do_not_control_global_maxima',
                  dict(literal_left_side_missing_index=True,intended_implication=False,example_each_supremum=ONE,limit_supremum=ZERO),
                  'В буквальной левой части отсутствует индекс, по которому берётся предел, поэтому она не сравнивает максимумы последовательности.',
                  'Для естественной формулировки с f_n взять сдвигающийся гауссиан. На каждом компакте он стремится к нулю равномерно, хотя его максимум на всей прямой сохраняется и достигается в n.',
                  verified_counterexample=gaussian)
    raise Unsupported('This quantified series or sequence goal needs another transport theorem')


def functional_transport_goal(task,lib,request):
    if not lib.data.get('coefficient_and_limit_transport'):raise Unsupported('The coefficient-and-limit transitions are absent')
    k=task['kind']
    try:
        if k=='functional_series_domain_regularity':return read_series_regularity(task,lib,request)
        if k=='limit_of_series':return limit_from_series_transport(task)
        if k=='series_operation_justification':return integrated_telescoping_powers(task)
        if k=='sequence_and_derivative_limit':return sequence_derivative_transport(task)
        return advanced_functional_transport(task)
    except (poly.NotRational,poly.Undefined) as exc:
        raise Unsupported('The source series falls outside the proved transport chart') from exc


def fourier_transport_certificate(theorem,value,*arguments,**evidence):
    return functional_transport_certificate(theorem,value,*arguments,
        certificate=dict(coefficient_construction=theorem),**evidence)


def fourier_transport_goal(task,lib):
    """Use the period, source coverage and coefficient recurrences as separate obligations."""
    from verify import same_value
    if not lib.data.get('coefficient_and_limit_transport'):raise Unsupported('Fourier transport absent')
    base={'kind','id','source','function_or_given','interval','requested_output'}
    meta=task.get('source',{});f=task.get('function_or_given');wanted=task.get('requested_output')
    interval=task.get('interval');method=task.get('method_requirement')
    if not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_pages','pdf_sha256',
                                               'page_png_sha256','literal_requirement'}:
        raise Unsupported('An additional source Fourier obligation remains')
    label=meta.get('literal_requirement')
    if wanted==['fourier_series_or_explain_underdetermination'] and not set(task)-base-{'printed_branches'}:
        branches=task['printed_branches'];ctx=m.context(dict(variable='x'))
        if not isinstance(branches,list) or len(branches)!=2 or any(set(b)!={'condition','expression'} for b in branches):
            raise Unsupported('Need the exact printed branches')
        expressions=', '.join(f'{b["expression"]} for {b["condition"]}' for b in branches)
        if f!=expressions or interval!=['-pi','pi'] or label not in (
                None,'Разложить в ряд Фурье. (-pi,pi), a,b constants, first subinterval printed pi<x<0'):
            raise Unsupported('The printed period or branch text differs')
        cells=[]
        for b in branches:
            r=re.fullmatch(r'(.+)<x<([^<>]+)',b['condition'])
            if not r:raise Unsupported('Branch interval unreadable')
            left,right=(m.parse(r[i],None) for i in (1,2))
            cells.append((left,right,m.sign(m.add(right,m.neg(left)),ctx)))
        if sorted(c[2] for c in cells if c[2] is not None)!=[-1,1]:raise Unsupported('Need one certified empty branch')
        left,right,_=next(c for c in cells if c[2]==1)
        if left!=ZERO or right!=m.PI:raise Unsupported('The uncovered part of the original period is not bound')
        return fourier_transport_certificate('verify_interval_coverage_before_fourier_coefficients',
                    dict(fourier_series_uniquely_determined=False,uncovered_interval=['-pi','0'],possible_difference_of_a0=ONE),
                    'Проверить каждую печатную ветвь как множество точек. Ветвь с левым пределом больше правого пуста, а правая половина задана.',
                    'На незаданной половине выбрать два интегрируемых продолжения, различающихся на единицу. Их постоянные коэффициенты различны. Следовательно, исходное условие не определяет единственный ряд.')
    if (wanted==['all_real_fourier_coefficients','coefficient_recurrence_a_n_a_n_minus_2'] and f=='sec(x)'
            and not set(task)-base and isinstance(interval,list) and len(interval)==2):
        A=m.parse(interval[0],None);B=m.parse(interval[1],None);phase=m.pi_multiple(B)
        if phase is None or phase<=0 or 1/phase not in range(4,65,2) or not same_value(A,m.neg(B)):
            raise Unsupported('The symmetric period must have a verified even frequency stride and no pole')
        if label not in (None,f'Разложить в ряд Фурье. ({interval[0]},{interval[1]}). Указание: вывести соотношение между a_n и a_(n-2)',
                         f'Разложить в ряд Фурье. ({interval[0]},{interval[1]}).',f'Разложить в ряд Фурье. ({interval[0]},{interval[1]})'):
            raise Unsupported('The printed secant recurrence differs')
        stride=int(1/phase)
        z=m.div(m.add(ONE,('sin',B)),('cos',B));a0=m.div(m.mul(q(2),('ln',z)),B)
        a1=m.mul(q((-1)**(stride//2)),a0)
        for j in range(stride//2):
            r=stride-2*j-1
            a1=m.add(a1,m.div(m.mul(q(4*(-1)**j),('sin',m.mul(q(r),B))),m.mul(q(r),B)))
        return fourier_transport_certificate('fourier_stride_from_nearby_harmonics',
                   dict(a0=a0,a1=a1,b_n=ZERO,frequency_stride=stride,
                        recurrence=f'a_n=a_(n-2)+sum(j=0..{stride-1},(-1)^j*J({stride}*n-2*j))/L, n>=2',
                        kernel='J(m)=4*sin((m-1)*L)/(m-1)'),
                   'Проверить отсутствие полюсов секанса и чётность на исходном полупериоде. Синусные коэффициенты равны нулю.',
                   'Для вспомогательного интеграла I_m сложить гармоники cos(mx) и cos((m−2)x). Их сумма содержит cos x, который точно сокращается со знаменателем.',
                   'Полученную рекурсию для I_m пройти до индекса на два периода гармоник ниже. Начальный интеграл вычисляется через ln(sec L+tan L), что даёт оба начальных коэффициента.',
                   half_interval=B,auxiliary_relation='I_m+I_(m-2)=J(m)')
    if wanted in (['all_three_fourier_series'],['all_fourier_series']) and method=='termwise_integration':
        forms=task.get('functions');first='x=2*sum(n>=1,(-1)^(n+1)*sin(n*x)/n)'
        if (set(task)-base-{'functions','method_requirement'} or f!=first or interval!=['-pi','pi'] or
                not isinstance(forms,list) or not 1<=len(forms)<=6 or forms!=[f'x^{j}' for j in range(2,len(forms)+2)] or
                len(forms)!=3 and wanted==['all_three_fourier_series'] or label not in (
                None,'Получить ряды для x²,x³,x⁴ в (-π,π) почленным интегрированием')):
            raise Unsupported('The original odd base series and the requested consecutive powers differ')
        n=('s','n');last=m.div(q(2),n);rows=[]
        for d in range(2,len(forms)+2):
            # Coefficients below multiply the common phase (-1)^(n+1).
            last=m.mul(q(-d),m.div(last,n)) if d%2==0 else m.add(m.div(m.mul(q(2),m.power(m.PI,d-1)),n),m.mul(q(d),m.div(last,n)))
            rows.append(dict(power=d,constant=m.div(m.power(m.PI,d),q(d+1)) if d%2==0 else ZERO,
                             wave='cos' if d%2==0 else 'sin',coefficient_without_common_phase=last))
        return fourier_transport_certificate('integral_recurrence_of_fourier_powers',
                    dict(common_phase='(-1)^(n+1)',rows=rows,valid_on='(-pi,pi)'),
                    'На каждом внутреннем компакте исходный синусный ряд сходится равномерно по Дирихле. Интегрировать его от нуля почленно.',
                    'Интегрирование меняет синус на косинус со знаком минус и делителем n. Среднее новой чётной степени берётся прямым интегралом.',
                    'При интегрировании чётного ряда постоянный член даёт линейный профиль. Подставить в него уже заданный исходный ряд и повторить операцию. Все требуемые степени строятся одним переходом.',
                    source_method='termwise_integration')
    if wanted==['parseval_identity','sine_squared_series_sum','cosine_squared_series_sum'] and method=='parseval_identity':
        branches=task.get('printed_branches');p=task.get('parameters')
        if (set(task)-base-{'parameters','printed_branches','method_requirement'} or interval!=['-pi','pi'] or
                not isinstance(p,list) or len(p)!=1 or not isinstance(p[0],str) or not p[0].isidentifier() or
                label not in (None,'Написать равенство Ляпунова и вывести суммы sin²(nα)/n² и cos²(nα)/n², n≥1')):
            raise Unsupported('Need the printed even interval-pulse and its Parseval requests')
        a=p[0]
        if branches!=[dict(condition=f'abs(x)<{a}',expression='1'),dict(condition=f'{a}<abs(x)<pi',expression='0')] or f!=f'f=1 for abs(x)<{a}, 0 for {a}<abs(x)<pi':
            raise Unsupported('The active pulse and the printed branches differ')
        return fourier_transport_certificate('parseval_of_even_pulse_gives_squared_wave_sum',
                    dict(pulse_width=f'b=min(pi,max(0,{a}))',a0='2*b/pi',a_n='2*sin(n*b)/(pi*n)',b_n=ZERO,
                         parseval='2*b/pi=2*b^2/pi^2+4/pi^2*sum(sin(n*b)^2/n^2)',
                         sine_sum=f'(pi*r-r^2)/2, r={a} modulo pi in [0,pi)',
                         cosine_sum='pi^2/6-(pi*r-r^2)/2'),
                    'Ограничить активную часть исходным периодом. Чётность даёт нулевые синусные коэффициенты, прямой интеграл индикатора даёт косинусные.',
                    'Подставить коэффициенты и интеграл квадрата импульса в равенство Парсеваля. Для аргумента в [0,π] это прямо даёт сумму квадратов синусов.',
                    'Квадраты синуса периодичны по исходному аргументу с периодом π. Сумму квадратов косинуса получаем из тождества sin²+cos²=1 и суммы обратных квадратов.',
                    endpoint_values_irrelevant_for_integrals=True)
    if wanted==['fourier_of_x','fourier_of_y'] and not set(task)-base-{'parameter'}:
        r=re.fullmatch(r'square 0<x<(\w+),0<y<\1, arc length (\w+) from O=\(0,0\), counterclockwise',f or '')
        if not r or r[2]!=task.get('parameter') or interval!=['0','4*'+r[1]] or label not in (
                None,f'Найти оба ряда Фурье координат x({r[2]}),y({r[2]}), 0<={r[2]}<=4{r[1]}'):
            raise Unsupported('The closed orientation and arclength source must be preserved')
        a,s=r.groups()
        return fourier_transport_certificate('periodic_piecewise_affine_derivative_transfer',
                   dict(mean_x=f'{a}/2',mean_y=f'{a}/2',domain=f'0<={s}<=4*{a}',
                        coordinates=[s,a,f'3*{a}-{s}','0'],carrier=f'w_n=pi*n/(2*{a}), r_n=exp(-i*pi*n/2)',
                        complex_x_coefficient=f'-(1-r_n)*(1-r_n^2)/(4*{a}*w_n^2)',complex_y_coefficient='r_n*c_n(x)',
                        real_conversion='a_n=2*Re(c_n), b_n=-2*Im(c_n)',absolute_convergence=True),
                   'По длине дуги построить четыре аффинных участка. Ордината получается сдвигом абсциссы на длину одной стороны.',
                   'Граничный член интегрирования по частям исчезает по периодичности. Производная абсциссы постоянна на каждом исходном участке, поэтому её коэффициенты вычисляются конечной суммой экспонент.',
                   'Сдвиг умножает коэффициенты ординаты на фазу. Убывание 1/n² даёт абсолютную сходимость обоих рядов, включая стыки.',
                   side_condition=a+'>0',orientation='counterclockwise')
    raise Unsupported('No verified Fourier transport for this source condition')
