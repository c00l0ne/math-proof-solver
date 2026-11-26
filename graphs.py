"""Exact branches of rational graphs and their deterministic visible drawing."""
from fractions import Fraction as F
from functools import cmp_to_key
from hashlib import sha256
import re
from time import perf_counter
from xml.etree import ElementTree as ET

import intervals as line
import expressions as m
import polynomial as poly
from model import ONE,ZERO,Unsupported,canonical,freeze,q
from operations import version
from tasks import domain_conditions,source


Z=(F(0),);O=(F(1),)
SET_TASK_FIELDS={'kind','task_type','id','schema','source','source_number','source_exercise_number','source_subpart',
                 'source_edition','source_pdf_pages','source_statement','assumptions','transcription_notes','program_status','goal'}


def order_source_method(task,statement,methods):
    provenance=task.get('source',{})
    fields={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','printed_hint',
            'literal_requirement','explicit_required_method'}
    if (not isinstance(provenance,dict) or set(provenance)-fields or ('kind' in task and 'task_type' in task and task['kind']!=task['task_type'])
            or task.get('source_statement',statement)!=statement
            or provenance.get('literal_requirement',statement)!=statement):
        raise Unsupported('Extra or conflicting conditions in the source ordering problem')
    required=provenance.get('explicit_required_method')
    supplied=task.get('method_requirement')
    if any(m is not None and m not in methods for m in (supplied,required)) or (
            supplied is not None and required is not None and supplied!=required):
        raise Unsupported('The requested ordering method has no matching proof plan')
    return required if required is not None else supplied


def ordered_cuts(values):
    finite=sorted((x for x in values if not isinstance(x,str)),key=cmp_to_key(line.compare))
    return [x for i,x in enumerate(finite) if not i or line.compare(finite[i-1],x)]


def step_level_continuity(text,var):
    """Pull isolated jumps back through monotone charts and compute the two traces of the outer function."""
    from tasks import known_guard
    from verify import same_value
    X=('s',var);zero=m.ZERO;one=m.ONE
    e=m.parse(text,None,[var],extra_functions={'floor','sign'})
    def nodes(z):
        yield z
        for a in z[1:]:
            if isinstance(a,tuple):yield from nodes(a)
    steps=set(z for z in nodes(e) if z[0] in ('floor','sign'))
    if len(steps)!=1:raise Unsupported('One isolated step operation and its original phase are required')
    step,=steps;op,phase=step;i=('s','j' if var=='k' else 'k');dummy=('s','__step' if var!='__step' else '__step1')
    outer=m.substitute(e,{step:dummy});p=m.simplify(m.substitute(outer,{dummy:zero}))
    a=m.simplify(m.add(m.substitute(outer,{dummy:one}),m.neg(p)))
    if not same_value(outer,m.add(p,m.mul(a,dummy))):raise Unsupported('The dependence on the step value must be affine')
    trig=phase[0] if op=='sign' and phase[0] in ('sin','cos') else None
    t=phase[1] if trig else phase
    root=t==('sqrt',X);square=t==('pow',X,2)
    reciprocal=t[0]=='div' and t[2]==X and m.num(t[1]) not in (None,0)
    b=m.simplify(m.substitute(t,{X:zero})) if not reciprocal else zero
    slope=m.simplify(m.add(m.substitute(t,{X:one}),m.neg(b)))
    affine=not domain_conditions(t) and m.num(slope) not in (None,0) and m.num(b) is not None and same_value(t,m.add(m.mul(slope,X),b))
    if not (root or square or reciprocal or affine) or op=='sign' and not trig and not affine or trig and not (affine or reciprocal):
        raise Unsupported('A complete monotone inverse for the level sets of the original phase is required')
    ctx=dict(parameters=[var],assumptions=[])
    if any(g not in domain_conditions(t) and not known_guard(g,ctx) for g in domain_conditions(e)):
        raise Unsupported('An extra source hole remains outside the monotone phase partition')
    def at(z,pos):
        out=m.simplify(m.substitute(z,{X:pos}))
        for v in list(nodes(out)):
            if v[0]=='sin':
                coefficient=m.polynomial_quotient(m.div(v[1],m.PI));c=m.simplify(m.substitute(coefficient,{i:zero}))
                d=m.simplify(m.add(m.substitute(coefficient,{i:one}),m.neg(c)))
                if all(m.num(x) is not None and m.num(x).denominator==1 for x in (c,d)) and same_value(coefficient,m.add(c,m.mul(d,i))):
                    out=m.substitute(out,{v:zero})
        return m.simplify(out)
    families=[];special=[]
    def traces(pos,left,right,actual,index):
        v,w=(at(z,pos) for z in (p,a))
        combine=lambda value:m.simplify(m.add(v,m.mul(w,value)))
        families.append(dict(location=pos,index=index,left=combine(left),right=combine(right),value=combine(actual),
                             jump_if_nonzero=w,classification='continuous' if w==zero else 'jump_where_coefficient_nonzero'))
    if trig:
        levels=[(m.mul(m.PI,m.add(m.mul(m.q(2),i),m.q(j) if trig=='sin' else m.q(2*j+1,2))),
                 (1 if j==0 else -1)*(1 if trig=='sin' else -1)) for j in range(2)]
    else:levels=[(i,1)] if op=='floor' else [(zero,1)]
    for v,direction in levels:
        index='all integers '+i[1] if op=='floor' or trig else 'one point'
        if affine:cells=[(m.div(m.add(v,m.neg(b)),slope),1 if m.num(slope)>0 else -1)]
        elif root:cells=[(m.power(v,2),1)];index=i[1]+' positive integer'
        elif square:cells=[(('sqrt',v),1),(m.neg(('sqrt',v)),-1)];index=i[1]+' positive integer'
        else:
            cells=[(m.div(t[1],v),-1 if m.num(t[1])>0 else 1)]
            if op=='floor' or trig=='sin' and direction==1:index=i[1]+' nonzero integer'
        for pos,sense in cells:
            left,right=(m.add(v,m.q(-1)),v) if op=='floor' else (m.q(-1),one)
            if sense*direction<0:left,right=right,left
            traces(pos,left,right,v if op=='floor' else zero,index)
    if root or square:
        special.append(dict(point=zero,classification='continuous',value=at(p,zero),relative_sides='right' if root else 'both'))
    if reciprocal:
        v,w=(at(z,zero) for z in (p,a))
        if not all(m.constant_defined(z,ctx) for z in (v,w)):raise Unsupported('Outer coefficients lack finite limits at the omitted origin')
        if op=='floor':
            scale=m.simplify(m.mul(w,t[1]));sgn=m.sign(scale,ctx)
            if sgn in (1,-1):left,right=('-inf','+inf') if sgn==1 else ('+inf','-inf')
            elif w==zero:
                trend=m.polynomial_quotient(m.add(p,m.mul(a,t)));left=right=at(trend,zero)
                if not m.constant_defined(left,ctx):raise Unsupported('The trend at the accumulation point needs a separate limit')
            else:raise Unsupported('The coefficient at the reciprocal pole has unresolved sign')
            special.append(dict(point=zero,value=None,left=left,right=right,classification='removable' if left==right else 'infinite_discontinuity',
                                argument='floor(t)-t is bounded between -1 and 0'))
        elif known_guard(('nonzero',w),ctx):
            special.append(dict(point=zero,value=None,classification='oscillatory_discontinuity',left='does_not_exist',right='does_not_exist',
                                argument='positive and negative half periods occur arbitrarily close on either side'))
        elif same_value(w,zero):special.append(dict(point=zero,value=None,classification='removable',left=v,right=v))
        else:raise Unsupported('The oscillatory coefficient at the removed point remains unresolved')
    return dict(theorem='method.step_level_continuity',phase=phase,original_guards=domain_conditions(e),step=op,
                outer_constant=p,outer_coefficient=a,chart='affine' if affine else 'square_root' if root else 'square' if square else 'reciprocal',
                trig=trig),dict(domain=dict(variable=var,support='nonnegative' if root else 'nonzero' if reciprocal else 'all real'),
                                jump_families=families,other_points=special,elsewhere='continuous')


def pointwise_phase_limit(task,lib):
    """Compare an exponential rate with zero, then evaluate one rational family at 0, 1 and infinity."""
    from verify import same_value
    keys={'kind','id','source','variable','limit_variable','limit_domain','approach','expression','domain','requested_output'}
    src=task.get('source',{});var=task['variable'];idx=task['limit_variable'];domain=task.get('domain')
    if (not lib.data.get('pointwise_phase_limit') or set(task)-keys or not isinstance(src,dict)
            or set(src)-{'exercise','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or src.get('literal_requirement') not in (None,'Исследовать на непрерывность и построить график функции, заданной пределом.')
            or task['requested_output']!=['pointwise limit','continuity on original domain and exceptional points']
            or task['approach']!='+infinity' or task['limit_domain'] not in ('positive real','positive integers')
            or domain not in ('R',var+'>=0') or var==idx):
        raise Unsupported('The original pointwise limit, domain and all continuity obligations must be retained')
    m.context(dict(variable=idx,parameters=[var]));X,N=('s',var),('s',idx);T=('s','__weight')
    if T in (X,N):raise Unsupported('The weight symbol must be fresh')
    text=task['expression']
    root=re.fullmatch(r'nth_root\((.+),'+re.escape(idx)+r'\)',text)
    original=m.parse(root[1] if root else text,None,[var,idx])
    if root or original[0]=='div' and original[1][0]==original[2][0]=='ln':
        # A sum lies between its largest term and the number of terms times that largest term.
        def summands(e):return summands(e[1])+summands(e[2]) if e[0]=='add' else [e]
        def levels(e,logarithmic):
            values=[]
            for term in summands(e):
                if term==m.ONE:z=m.ZERO if logarithmic else m.ONE
                elif logarithmic and term[0]=='exp':
                    z=m.polynomial_quotient(m.div(term[1],N))
                    if domain_conditions(term[1]) or not same_value(term[1],m.mul(N,z)):
                        raise Unsupported('Exponential term has an unverified growth rate')
                elif not logarithmic and term[0]=='rpow':
                    degree=m.num(m.polynomial_quotient(m.div(term[2],N)))
                    if (degree is None or degree.denominator!=1 or degree<=0 or degree%2
                            or domain_conditions(term[1]) or domain_conditions(term[2]) or not same_value(term[2],m.mul(N,m.q(degree)))):
                        raise Unsupported('A nonnegative base to a natural power is required')
                    z=m.power(term[1],int(degree))
                else:raise Unsupported('A term is not a positive exponential or an even-power base')
                if m.contains(z,N) or domain_conditions(z):raise Unsupported('The envelope coefficient has extra coordinate restrictions')
                values.append(z)
            return values
        if root:
            if task['limit_domain']!='positive integers':raise Unsupported('The root indices must be positive integers')
            choices=levels(original,False);scale=m.ONE;bound='root_of_term_count'
        else:
            choices=levels(original[1][1],True);bottom=levels(original[2][1],True)
            nums=[m.num(z) for z in bottom]
            if None in nums or max(nums)<=0:raise Unsupported('The limiting denominator must be a positive constant')
            scale=m.q(max(nums));bound='log_term_count_over_index'
        return dict(theorem='method.finite_maximum_envelope',error_bound=bound,number_of_terms=len(choices),
                    denominator_rates=None if root else bottom),dict(domain=domain,variable=var,maximum_of=choices,
                    divisor=scale,classification='continuous',exceptional_points=[])
    def walk(e):
        yield e
        for a in e[1:]:
            if isinstance(a,tuple):yield from walk(a)
    mode=None;phase=None;replace={}
    for e in walk(original):
        if e[0] in ('exp','tanh') and m.contains(e[1],N):
            f=m.polynomial_quotient(m.div(e[1],N));typ='exponential'
            if not same_value(e[1],m.mul(N,f)) or domain_conditions(e[1]):raise Unsupported('Unverified linear growth of the exponent')
        elif e[0]=='rpow' and e[1]==N:f=e[2];typ='index_power'
        elif e[0]=='rpow' and e[2]==N and task['limit_domain']=='positive integers' and e[1]==X and domain==var+'>=0':
            f=m.add(X,m.q(-1));typ='positive_geometric_base'
        else:continue
        if domain_conditions(f) or m.contains(f,N):raise Unsupported('Non-affine or partially defined growth rate')
        if phase is None:phase,mode=f,typ
        if mode!=typ:raise Unsupported('More than one independent asymptotic scale is needed')
        ratio=m.num(m.polynomial_quotient(m.div(f,phase)))
        if ratio is None or ratio.denominator!=1 or not same_value(f,m.mul(m.q(ratio),phase)):
            raise Unsupported('The growth rates do not have a common integral scale')
        w=m.power(T,int(ratio)*(2 if e[0]=='tanh' else 1))
        replace[e]=('div',m.add(w,m.q(-1)),m.add(w,m.ONE)) if e[0]=='tanh' else w
    if phase is None:raise Unsupported('The source has no supported positive-weight phase')
    b=m.simplify(m.substitute(phase,{X:m.ZERO}));s=m.simplify(m.add(m.substitute(phase,{X:m.ONE}),m.neg(b)))
    if m.num(s) in (None,0) or m.num(b) is None or not same_value(phase,m.add(b,m.mul(s,X))):
        raise Unsupported('The level zero does not yet have a complete partition')
    cut=m.div(m.neg(b),s)
    if domain!='R' and m.num(cut)<=0:raise Unsupported('The threshold is outside or on the domain boundary')
    reduced=m.substitute(original,replace)
    if m.contains(reduced,N) or any(e[0] not in ('s','q','add','mul','div','pow') for e in walk(reduced)):
        raise Unsupported('Additional independent phases or nonrational coefficients remain')
    def by_degree(poly):
        coeff={}
        for mon,c in poly.items():
            k=dict(mon).get(T,0);sub=tuple((a,d) for a,d in mon if a!=T)
            coeff.setdefault(k,{})[sub]=c
        return {k:m.poly_expr(p) for k,p in coeff.items()}
    def definite(poly):
        vals=[m.num(c) for c in by_degree(poly).values()]
        return bool(vals) and all(z is not None and z>0 for z in vals) or bool(vals) and all(z is not None and z<0 for z in vals)
    for relation,g in domain_conditions(reduced):
        num,den=m.rational_form(g)
        if relation!='nonzero' or not definite(num) or not definite(den):
            raise Unsupported('A source divisor may vanish for positive weight')
        if mode=='positive_geometric_base' and not m.nonzero(m.substitute(g,{T:m.ZERO,X:m.ZERO}),dict(parameters=[],assumptions=[])):
            raise Unsupported('The geometric weight can vanish at the included endpoint')
    num,den=map(by_degree,m.rational_form(reduced));num=num or {0:m.ZERO}
    if min(num)<min(den) or max(num)>max(den):raise Unsupported('A separate infinite or rate-dependent branch remains')
    small=m.div(num.get(min(den),m.ZERO),den[min(den)]);large=m.div(num.get(max(den),m.ZERO),den[max(den)])
    left,right=(small,large) if m.num(s)>0 else (large,small)
    level=m.simplify(m.substitute(reduced,{T:m.ONE,X:cut}))
    traces=[m.simplify(m.substitute(z,{X:cut})) for z in (left,right)]
    if not all(m.constant_defined(z,dict(parameters=[],assumptions=[])) for z in [level,*traces]):raise Unsupported('Undefined joining value')
    classification='continuous' if all(same_value(z,level) for z in traces) else 'removable' if same_value(*traces) else 'jump'
    return dict(theorem='method.pointwise_phase_limit',rate=phase,rate_type=mode,scale_replacements=list(replace.items()),rational_in_weight=reduced,
                weight_numerator=sorted(num.items()),weight_denominator=sorted(den.items()),one_sided_at_cut=traces),dict(
                variable=var,domain=domain,cut=cut,left_formula=left,right_formula=right,at_cut=level,classification=classification,
                elsewhere='continuous_on_each_relative_open_piece')


def rational_roots(p):
    """Return every real root or decline when no complete factor certificate exists."""
    if len(p)<=3:return line.roots(p)
    if p[-1]<0:p=tuple(-c for c in p)
    if p[0]>0 and all(not c or i%2==0 and c>0 for i,c in enumerate(p)):return []
    monic=tuple(c/p[-1] for c in p);factor=poly.proper_factor(monic)
    if not factor:
        if poly.no_real_roots(p):return []
        raise Unsupported('A real-root isolation for the remaining factor is required')
    quotient,remainder=poly.pdiv(monic,factor)
    if remainder!=Z or not 1<len(factor)<len(p):raise Unsupported('Incomplete exact factorization')
    return rational_roots(factor)+rational_roots(quotient)


def peval(p,x):
    a=F(0)
    for c in reversed(p):a=a*x+c
    return a


def isolate_equation(t,lib):
    """Isolate all distinct real zeros of a guarded, parameter-free polynomial equation."""
    printed=t.get('source',{})
    if (not lib.data.get('isolate_polynomial_equations') or set(t)-{'id','kind','source','given','variable'}
            or set(printed)-{'exercise','pdf_page','printed_page','pdf_sha256','literal_requirement','printed_subpart'}
            or printed.get('literal_requirement','Определить число вещественных корней и отделить эти корни.')!='Определить число вещественных корней и отделить эти корни.'):
        raise Unsupported('Unbound equation requirement or parameter domain')
    raw=t['given'];var=t.get('variable','x')
    if raw.count('=')!=1:raise Unsupported('A scalar equation is required')
    left,right=(m.parse(re.sub(r'[⁰¹²³⁴⁵⁶⁷⁸⁹]+',lambda s:'^'+s[0].translate(str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')),s),var) for s in raw.split('='))
    expr=('add',left,('mul',q(-1),right))
    try:
        p,_=poly.rf(expr,var)
        p,excluded=admissible_polynomial_roots(p,domain_conditions(expr),var)
    except (poly.NotRational,poly.Undefined) as exc:
        raise Unsupported('A defined rational equation with polynomial guards is required') from exc
    bound,intervals,counts=sturm_intervals(p)
    return (dict(polynomial=list(map(q,p)),cauchy_bound=q(bound),original_nonzero_polynomials=excluded,
                 sturm_counts=[s for _,s in sorted(zip(intervals,counts))]),
            dict(distinct_real_roots=len(intervals),isolating_intervals=[(q(a),q(b)) for a,b in sorted(intervals)]))


def sturm_intervals(p):
    intervals=[];bound=F(1);counts=[]
    if len(p)>1:
        v=poly.distinct_root_counter(p)
        while bound<=1+max(abs(c/p[-1]) for c in p[:-1]):bound*=2
        todo=[(-bound,bound,v(-bound),v(bound))]
        while todo:
            a,b,va,vb=todo.pop();count=va-vb-int(not peval(p,b))
            if not count:continue
            if count==1 and b-a<=1:intervals.append((a,b));counts.append((va,vb,not peval(p,b)));continue
            mid=(a+b)/2;vm=v(mid)
            if not peval(p,mid):intervals.append((mid,mid));counts.append((vm,vm,True))
            todo.extend(((mid,b,vm,vb),(a,mid,va,vm)))
    return bound,intervals,counts


def admissible_polynomial_roots(p,guards,var):
    """Remove every root forbidden by an uncancelled source denominator."""
    if p==Z:raise Unsupported('An identically zero equation needs an infinite solution set')
    excluded=[]
    for predicate,guard in guards:
        if predicate!='nonzero':raise Unsupported('An original nonrational domain guard remains')
        g,_=poly.rf(guard,var)
        if g==Z:raise Unsupported('An original denominator vanishes identically')
        excluded.append(list(map(q,g)))
        while len(common:=poly.pgcd(p,g))>1:p=poly.pdiv(p,common)[0]
    return p,excluded


def approximate_equation_roots(task,library,request):
    """Combine exhaustive root isolation with a prescribed, checked numerical iteration."""
    from quadrature import enclose
    from tasks import source
    fields={'id','kind','source','equation','variable','requested_roots','absolute_error','method','section_context'}
    src=task.get('source',{});method=task.get('method','unspecified')
    headings={'newton':'Пользуясь методом Ньютона, определить корни с указанной точностью.',
              'false_position':'Методом пропорциональных частей определить корни уравнения с указанной точностью.'}
    provenance={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
    context='Previous group explicitly specifies Newton; this separately phrased exercise gives no mandatory method.'
    if (not library.data.get('certified_root_iterations') or set(task)-fields or set(src)-provenance or
            'section_context' in task and task['section_context']!=context or method not in (*headings,'unspecified') or
            'literal_requirement' in src and src['literal_requirement']!=headings.get(method) or
            task.get('requested_roots')!='all real' or task['equation'].count('=')!=1):
        raise Unsupported('The original count of roots or mandatory method needs a separate proof')
    var=task.get('variable','x');x=('v',var)
    tol=F(str(task['absolute_error']))
    if not F(1,10**18)<=tol:raise Unsupported('The requested precision is outside the numerical method range')
    a,b=(m.parse(s,var) for s in task['equation'].split('='))
    raw=('add',a,('mul',q(-1),b))
    try:
        p,_=poly.rf(raw,var)
    except poly.NotRational:
        p=None
    except poly.Undefined as exc:
        raise Unsupported('An original denominator vanishes identically') from exc
    guards=domain_conditions(raw)
    if p is not None:
        p,excluded=admissible_polynomial_roots(p,guards,var)
        if len(p)>1:
            p=poly.pdiv(p,poly.pgcd(p,tuple(i*c for i,c in enumerate(p) if i)))[0]
        slope=tuple(i*c for i,c in enumerate(p) if i)
        ev=lambda t:(peval(p,t),)*2
        der=lambda t:(peval(slope,t),)*2
        radius,seeds,counts=sturm_intervals(p)
        completeness=dict(proof='sturm',polynomial=list(map(q,p)),excluded_polynomial_factors=excluded,
                          cauchy_bound=q(radius),variations=counts)
        if seeds:
            v=poly.distinct_root_counter(p)
            seeds.sort()
            def around_zero(x):
                width=F(1,2)
                while v(x+width)!=v(x-width)-1 or not peval(p,x-width)*peval(p,x+width):
                    width/=2
                return x-width,x+width
            for i,(left,right) in enumerate(seeds):
                if left==right:
                    seeds[i]=around_zero(left)
                    continue
                while not peval(p,left)*peval(p,right):
                    mid=(left+right)/2
                    if not peval(p,mid):
                        left,right=around_zero(mid)
                        break
                    if v(left)-v(mid)>0:right=mid
                    else:left=mid
                seeds[i]=(left,right)
    else:
        if guards:raise Unsupported('An original guard needs a nonpolynomial domain proof')
        dt=dict(kind='differentiate',function=source(raw),variable=var,method_requirement='table_and_rules')
        derivative=freeze(request('derivative of the source residual',dt)['value'])
        ev=lambda t:enclose(raw,(t,t))
        der=lambda t:enclose(derivative,(t,t))
        ctx=m.context({'variable':'__root_probe' if var!='__root_probe' else '__root_probe_','parameters':[var]})
        fixed=m.substitute(derivative,{x:('s',var)})
        direction=m.sign(fixed,ctx) if m.constant_defined(fixed,ctx) else None
        if direction in (1,-1):
            radius=F(1)
            while radius<=128 and not (strict_sign(ev(-radius))*strict_sign(ev(radius))==-1):
                radius*=2
            if radius>128:raise Unsupported('No certified opposite signs found')
            seeds=[(-radius,radius)];completeness=dict(proof='global_monotonicity',direction=direction,derivative=derivative)
        else:
            # Every trig monomial in the bounded remainder has absolute value at most one.
            numerator,denominator=m.rational_form(raw);poly_terms={};bounded=F(0)
            if denominator!={():F(1)}:raise Unsupported('No polynomial plus bounded remainder was found')
            for mon,c in numerator.items():
                if not mon or all(atom==x for atom,_ in mon):poly_terms[mon]=c
                elif all(atom[0] in ('sin','cos') for atom,_ in mon):bounded+=abs(c)
                else:raise Unsupported('No global bound for the nonpolynomial remainder')
            powers=poly.univariate_coefficients(poly_terms,x)
            if powers is None or len(powers)<2:raise Unsupported('No increasing polynomial magnitude at infinity')
            radius=F(2)+sum(map(abs,powers[:-1]))/abs(powers[-1])+bounded/abs(powers[-1])
            cells=[];seeds=[];todo=[(-radius,radius)]
            while todo:
                left,right=todo.pop()
                box=enclose(raw,(left,right))
                ds=enclose(derivative,(left,right))
                sl,sr=strict_sign(ev(left)),strict_sign(ev(right))
                if strict_sign(box) or strict_sign(ds) and sl*sr:
                    live=not strict_sign(box) and sl*sr<0
                    cells.append(dict(interval=[q(left),q(right)],value_bounds=list(map(q,box)),
                                      derivative_bounds=list(map(q,ds)),endpoint_signs=[sl,sr],contains_root=live))
                    if live:seeds.append((left,right))
                else:
                    if len(cells)+len(todo)>192 or right-left<tol/8:
                        raise Unsupported('The remaining interval has an unresolved zero or stationary point')
                    mid=(left+right)/2
                    todo.extend(((mid,right),(left,mid)))
            completeness=dict(proof='polynomial_dominates_bounded_remainder',polynomial=list(map(q,powers)),
                              remainder_bound=q(bounded),symmetric_radius=q(radius),cells=cells,derivative=derivative)

    transcripts=[];answer=[]
    for left,right in sorted(seeds):
        root,proof=refine_root_bracket(ev,der,left,right,tol,method)
        transcripts.append(proof);answer.append(root)
    return dict(theorem='method.certified_root_iterations',source_residual=raw,source_guards=guards,
                global_root_coverage=completeness,brackets=transcripts,method=method,absolute_tolerance=q(tol)),dict(roots=answer)



def graphical_goal_kind(task):
    return task.get('task_type',task.get('kind')) in ('graphical_equation','graphical_system')


def graph_crossing_bracket(residual,left,right,tol):
    from quadrature import enclose
    def sign(x):return strict_sign(enclose(residual,(x,x)))
    sl,sr=sign(left),sign(right)
    if sl*sr!=-1:raise Unsupported('No two opposite graph ordinates were verified')
    seed=[q(left),q(right)]
    while right-left>2*tol:
        width=right-left
        for portion in (F(1,2),F(1,4),F(3,4)):
            t=left+portion*width
            v=sign(t)
            if not v:continue
            if v==sl:left=t
            else:right=t
            break
        else:raise Unsupported('The crossing could not be isolated with outward enclosures')
    return dict(x=q((left+right)/2),interval=[q(left),q(right)],initial_interval=seed,
                crossing_signs=[sl,sr],absolute_error=q((right-left)/2))


def nonpolynomial_graph_arcs(left,right,var,assumptions):
    from integrals import affine
    from quadrature import enclose
    x=('v',var)
    lhs,rhs=left.split('=',1) if right is None else (left,right)
    def sides(e):
        transform=re.fullmatch(r'(lg|ln|log[1-9]\d*)\('+re.escape(var)+r'\)',e)
        if transform:
            op=transform[1]
            logarithm=ONE if op=='ln' else ('ln',q(10 if op=='lg' else int(op[3:])))
            return m.div(('ln',x),logarithm)
        return m.parse(e,var)
    U,V=sides(lhs),sides(rhs)
    pairs=[(lhs,rhs,U,V),(rhs,lhs,V,U)]
    for text,_,first,second in pairs:
        if first==('tan',x) and second==x:
            limit=next((z for z in assumptions if z.startswith('0<='+var+'<=')),None)
            if limit is None:raise Unsupported('All branches and endpoints of the printed tangent range are needed')
            end=m.num(m.div(m.parse(limit.split('<=')[-1],None),m.PI))
            if end is None or end.denominator!=1 or end<=0:raise Unsupported('The tangent range needs a whole number of half-turns')
            count=int(end);p0,p1=enclose(m.PI,None)
            holes={F(2*j+1,2) for j in range(count)}
            seen={m.num(m.div(m.parse(z.split('!=',1)[1],None),m.PI)) for z in assumptions if z.startswith(var+'!=')}
            if seen!=holes or len(assumptions)!=1+len(seen):raise Unsupported('Every printed tangent pole must be preserved')
            seeds=[]
            for j in range(1,count):
                t=m.add(x,m.neg(m.mul(q(j),m.PI)))
                residual=m.add(m.div(('sin',t),('cos',t)),m.neg(x))
                seeds.append((residual,j*p1+F(1,10**6),F(2*j+1,2)*p0-F(1,10**6)))
            return seeds,[ZERO],[
                'Сравниваем графики тангенса и прямой на каждой исходной ветви. Разность строго возрастает, её производная равна tan²(x).',
                'На первой ветви имеется только пересечение в нуле. На последней до правого конца тангенс неположителен.',
                'Каждая полная внутренняя ветвь пересекает прямую один раз после целой кратности π. Проверяем два знака в её пределах.']
        log=re.fullmatch(r'(lg|ln|log[1-9]\d*)\('+re.escape(var)+r'\)',text)
        if log:
            if assumptions not in ([],[var+'>0']):raise Unsupported('The logarithmic graph uses its full positive domain')
            slope,shift=affine(second,var)
            if m.num(slope) is None or m.num(slope)<=0 or shift!=ZERO:
                raise Unsupported('A positive straight line through the origin is required')
            op=log[1];sc=ONE if op=='ln' else ('ln',q(10 if op=='lg' else int(op[3:])))
            coefficient=m.mul(slope,sc);peak=m.div(ONE,coefficient)
            dg=strict_sign(enclose(m.add(('ln',peak),q(-1)),None))
            residual=m.add(('ln',x),m.neg(m.mul(coefficient,x)))
            reason=['Разность ординат после положительного масштабирования равна ln(x)−c x. Она строго вогнута, а её единственный максимум расположен при x=1/c.']
            if dg==-1:return [],[],[*reason,'Даже в максимуме логарифмический граф ниже прямой.']
            if dg!=1:raise Unsupported('Possible tangent contact needs an exact comparison at the maximum')
            lo,hi=enclose(peak,None);middle=(lo+hi)/2
            c,_=enclose(coefficient,None)
            if c<=0:raise Unsupported('A positive lower estimate of the slope is required')
            far=max(F(2),2*middle,(2/c)**2)
            return [(residual,F(1),middle),(residual,middle,far)],[],[*reason,'Фиксируем две смены порядка графиков по обе стороны от максимума.']
        if first[0]!='rpow' or (base:=m.num(first[1])) is None or base<=1 or assumptions:
            continue
        slope,offset=affine(first[2],var);k=m.num(slope);b=m.num(offset)
        if k is None or b is None:continue
        exponential=('exp',m.mul(('ln',q(base)),first[2]))
        residual=m.add(exponential,m.neg(second))
        if second==x and k<0:
            right_end=2+max(F(0),b/(-k))
            return [(residual,F(0),right_end)],[],[
                'На отрицательной полуоси положительная экспонента выше прямой. На положительной полуоси экспонента строго убывает, а прямая возрастает.',
                'Проверяем единственную смену порядка двух графиков.']
        if second[0]=='pow' and second[1]==x and second[2]>0 and second[2]%2==0 and k>0 and not b:
            power=second[2];frequency=m.mul(slope,('ln',q(base)))
            cut=m.div(q(power),frequency);val=m.mul(q(power),m.add(ONE,m.neg(('ln',cut))))
            peak=strict_sign(enclose(val,None))
            if not peak:raise Unsupported('Possible tangency needs an exact comparison of the positive minimum')
            seeds=[(residual,F(-1),F(0))]
            if peak==-1:
                u,v=enclose(cut,None);middle=(u+v)/2
                ln_residual=m.add(m.mul(frequency,x),m.neg(m.mul(q(power),('ln',x))))
                c,_=enclose(frequency,None)
                if c<=0:raise Unsupported('A positive lower estimate of the frequency is required')
                end=max(F(2),2*middle,(2*power/c)**2)
                seeds.extend(((ln_residual,F(1),middle),(ln_residual,middle,end)))
            return seeds,[],[
                'На отрицательной полуоси экспонента возрастает, а чётная степень убывает. Между −1 и 0 их порядок меняется.',
                'На положительной полуоси сравниваем логарифмы ординат. Их разность строго выпукла, её минимум определяет число пересечений.']
    raise Unsupported('No checked whole-domain comparison for the original graphs')


def graph_intersection_certificate(task,library,request):
    from integrals import affine
    from quadrature import enclose
    from tasks import source
    if not library.data.get('graph_intersection_certificates'):
        raise Unsupported('Mathematical graph intersections are unavailable')
    kind=task.get('task_type',task.get('kind'));goal=task.get('goal',{});hypotheses=task.get('assumptions',[])
    provenance={'source_number','source_exercise_number','source_subpart','source_edition','source_pdf_pages'}
    pending='Required graph/construction and any graphical root or symmetry obligations are pending.'
    if (set(task)-{'id','kind','task_type','source','source_statement','goal','assumptions',
                   'transcription_notes','program_status','pending_obligations',*provenance}
            or not isinstance(hypotheses,list) or task.get('transcription_notes',[])
            or task.get('program_status') not in (None,'not_attempted')
            or task.get('pending_obligations',[]) not in ([],[pending])):
        raise Unsupported('The original graph questions and restrictions must all be represented')
    statement=task.get('source_statement')
    if statement:
        read=re.fullmatch(r'(?:Графически решить(?: систему)?|Приближённо решить) (.+)\.',statement)
        forms=[goal.get('equation')] if kind=='graphical_equation' else goal.get('equations',[])
        if not read or not all(isinstance(e,str) for e in forms):
            raise Unsupported('The mathematical graph method is not bound')
        literal=read[1].split(', построив график ',1)
        actual=[v.replace(' ','') for v in literal[0].split(',')]
        if actual!=[e.replace(' ','') for e in forms]:
            raise Unsupported('The displayed graph equations differ from the original source')
        if len(literal)==2:
            plot=literal[1].replace(' ','')
            x,=re.findall(r'[A-Za-z][A-Za-z0-9_]*',actual[0])[:1]
            if (len(forms)!=1 or not plot.startswith('y=') or not actual[0].endswith('=0') or
                    poly.rf(m.parse(plot[2:],x),x)!=poly.rf(m.parse(actual[0].split('=')[0],x),x)):
                raise Unsupported('The requested cubic graph must represent the original zero locus')
    chart_label='Графически найти решения уравнения или системы на исходной области. Требование к способу сохраняется.'
    tol=F(1,10**4)
    def polynomial_roots(residual,variable):
        p,d=poly.rf(residual,variable)
        if len(d)!=1:raise Unsupported('A nonpolynomial graph cut remains')
        child=dict(kind='approximate_equation_roots',equation=source(residual)+'=0',variable=variable,
                   requested_roots='all real',absolute_error='0.0001',method='unspecified')
        trace=request('all intersections of the residual graph with the axis',child)
        if trace.get('status')!='SOLVED':raise Unsupported('The polynomial graph crossings were not exhausted')
        return trace['value']['roots'],trace['compilation']['brackets']
    def variables(equations):
        return sorted(set(re.findall(r'[A-Za-z][A-Za-z0-9_]*',' '.join(equations)))-
                      m.FUNCTIONS-set(m.ALIASES)-{'lg','e','pi'}-
                      {z for z in re.findall(r'\blog[1-9]\d*\b',' '.join(equations))})
    if kind=='graphical_equation':
        equation=goal.get('equation','');vs=variables([equation])
        method=goal.get('method_requirement')
        if (len(vs)!=1 or equation.count('=')!=1 or set(goal)-{'equation','method_requirement','goals','goal'}
                or method not in ('graphical','graphical approximation using the requested cubic graph')
                or goal.get('goals',[]) not in ([],['approximate every real root'])
                or goal.get('goal') not in (None,'find all admissible real roots graphically')):
            raise Unsupported('All roots and the graphical method must be requested')
        x,=vs;left,right=equation.split('=')
        try:
            raw=('add',m.parse(left,x),('mul',q(-1),m.parse(right,x)))
            if hypotheses or any(m.num(e) in (0,None) for r,e in domain_conditions(raw)):
                raise poly.NotRational
            if method=='graphical approximation using the requested cubic graph' and len(poly.rf(raw,x)[0])!=4:
                raise Unsupported('The explicitly requested cubic graph must be kept')
            roots,brackets=polynomial_roots(raw,x)
        except (poly.NotRational,poly.Undefined,Unsupported):
            if method!='graphical':raise Unsupported('No verified crossings of the requested cubic graph')
            seeds,exact,steps=nonpolynomial_graph_arcs(left,right,x,hypotheses)
            roots=[dict(x=e,absolute_error=ZERO) for e in exact]
            roots.extend(graph_crossing_bracket(e,a,b,tol) for e,a,b in seeds)
            brackets=[row.get('interval',[row['x'],row['x']]) for row in roots]
        else:
            steps=['Сравниваем ординаты исходных графиков по разности. Нули разности — ровно точки пересечения.',
                   'Точные знаки на концах уточнённых интервалов подтверждают пересечения. Полиномиальный подсчёт проверяет, что других точек нет.']
        return dict(theorem='method.certified_graph_intersections',argument=steps,coordinate=x,brackets=brackets,
                    verified_method=chart_label),dict(roots=roots,method='comparison of graph ordinates with certified brackets')
    forms=goal.get('equations',[])
    axes=variables(forms)
    if (kind!='graphical_system' or len(axes)!=2 or hypotheses or
            any(e.count('=')!=1 for e in forms) or len(forms)!=2 or set(goal)!={'equations','method_requirement','goals'}
            or goal['method_requirement']!='graphical' or goal['goals']!=['find every real intersection']):
        raise Unsupported('Both curves and their full real graph domain must be bound')
    for v in axes:
        x=next(h for h in axes if h!=v)
        equations=[]
        for expr in forms:
            a,b=expr.split('=')
            raw=('add',m.parse(a,v,[x]),('mul',q(-1),m.parse(b,v,[x])))
            _,den=m.rational_form(raw)
            if den!={():F(1)} or any(m.num(e) in (None,0) for r,e in domain_conditions(raw)):
                raise Unsupported('A graph-domain divisor needs its own proof')
            equations.append(raw)
        for i,expr in enumerate(equations):
            try:slope,shift=affine(expr,v)
            except Unsupported:continue
            k=m.num(slope)
            if not k:continue
            ordinate=m.div(m.neg(shift),q(k));v_ast=('v',v);x_ast=('s',x);t=('v',x)
            residual=m.substitute(m.substitute(equations[1-i],{v_ast:ordinate}),{x_ast:t})
            ordinate=m.substitute(ordinate,{x_ast:t})
            roots,brackets=polynomial_roots(residual,x)
            points=[]
            for row,span in zip(roots,brackets):
                a,b=map(lambda e:m.num(freeze(e)),span['final_bracket'])
                values=enclose(ordinate,(a,b))
                points.append(dict(coordinate_intervals={x:[q(a),q(b)],v:list(map(q,values))}))
            return dict(theorem='method.certified_graph_intersections',argument=[
                'Одно уравнение задаёт единственную ординату при каждой абсциссе. Сравниваем этот граф со второй исходной кривой.',
                'Подстановка ординаты даёт нулевую линию разности. Проверяем все её действительные пересечения и переносим интервалы на обе координаты.'
            ],ordinate=ordinate,residual=residual,brackets=brackets,verified_method=chart_label),dict(intersections=points)
    raise Unsupported('Neither curve is an explicit polynomial graph in one original coordinate')


def strict_sign(bounds):
    return 1 if bounds[0]>0 else -1 if bounds[1]<0 else 0


def refine_root_bracket(ev,der,left,right,tolerance,method):
    """Numerical steps may be rounded; opposite signs certify the rounded result."""
    seed=(q(left),q(right));moves=[]
    grid=F(1)
    while grid*tolerance<64:grid*=10
    last=right
    for _ in range(64):
        yl,yr=ev(left),ev(right);sl,sr=strict_sign(yl),strict_sign(yr)
        if sl*sr!=-1:raise Unsupported('The isolated zero has no certified sign-changing bracket')
        if method=='newton':
            x=last;fx,dx=ev(x),der(x)
            if strict_sign(dx):
                ratios=[u/v for u in fx for v in dx]
                candidate=(x-max(ratios),x-min(ratios))
            else:candidate=None
            inputs=[q(x),list(map(q,fx)),list(map(q,dx))]
        else:
            estimates=[left-u*(right-left)/(v-u) for u in yl for v in yr]
            candidate=(min(estimates),max(estimates));inputs=[list(map(q,yl)),list(map(q,yr))]
        if candidate is not None:
            x=F(round(grid*sum(candidate)/2),grid)
            room=min(x-left,right-x)
            if left<=x<=right and (room>0 or right-left<=tolerance):
                # Checking a tighter bracket around the actual iterate also handles
                # regula falsi when one of the original endpoints stays fixed.
                lo,hi=max(left,x-tolerance),min(right,x+tolerance)
                moves.append(dict(method='newton' if method=='newton' else 'false_position',
                                  previous_bracket=[q(left),q(right)],inputs=inputs,iterate_interval=list(map(q,candidate)),iterate=q(x)))
                if strict_sign(ev(lo))*strict_sign(ev(hi))==-1:
                    err=max(x-lo,hi-x)
                    return dict(approximation=q(x),absolute_error=q(err)),dict(seed=seed,iterations=moves,final_bracket=[q(lo),q(hi)])
                sign=strict_sign(ev(x))
                if sign:
                    if sign==sl:left=x
                    else:right=x
                    last=x
                    continue
        x=(left+right)/2;sign=strict_sign(ev(x))
        if not sign:
            raise Unsupported('No strict sign for the middle point of the bracket')
        if sign==sl:left=x
        else:right=x
        last=x
        moves.append(dict(method='bracket_refinement',split=q(x),sign=sign))
    raise Unsupported('The numerical method did not reach the requested accuracy')


def nonzero_on_integer_tail(poly,start):
    if not any(poly) or any(not z.b and z.a.denominator==1 and z.a>=start for z in rational_roots(poly)):
        raise Unsupported('A denominator vanishes at an original integer index')


def ordinate(p,d,x):
    a,b=line.peval(p,x),line.peval(d,x)
    conjugate=line.Quadratic(b.a,-b.b,b.d)
    return a.mul(conjugate).scale(1/(b.a*b.a-b.b*b.b*b.d))


def graph_curve(raw,var,extra_guards=()):
    p,d=poly.rf(raw,var);common=poly.pgcd(p,d)
    p=poly.pdiv(p,common)[0];d=poly.pdiv(d,common)[0]
    p,d=tuple(c/d[-1] for c in p),tuple(c/d[-1] for c in d)
    h=poly.quotient_derivative_numerator(p,d)
    holes=[]
    for relation,expr in (*domain_conditions(raw),*extra_guards):
        if relation!='nonzero':raise Unsupported('A nonrational original guard needs a different domain proof')
        guard,_=poly.rf(expr,var)
        if guard==Z:raise Unsupported('The original divisor vanishes identically')
        holes+=rational_roots(guard)
    roots=ordered_cuts(holes+rational_roots(p)+rational_roots(h))
    cut=[dict(x=line.quadratic_term(x),type='pole' if not line.peval(d,x).sign() else
              'hole' if any(line.compare(x,t)==0 for t in holes) else 'point',
              y=line.quadratic_term(ordinate(p,d,x)) if line.peval(d,x).sign() else None) for x in roots]
    endpoints=['-inf',*roots,'+inf'];branches=[]
    for a,b in zip(endpoints,endpoints[1:]):
        s=line.between(a,b);v=peval(p,s)/peval(d,s)
        branches.append({'left':line.endpoint_term(a),'right':line.endpoint_term(b),'sample':q(s),
                         'sign':line.sign(v),'derivative_sign':line.sign(peval(h,s))})
    def tail(left):
        diff=len(p)-len(d)
        if p==Z or diff<0:return q(0)
        if not diff:return q(p[-1]/d[-1])
        return '+inf' if p[-1]*d[-1]*((-1)**diff if left else 1)>0 else '-inf'
    return {'numerator':tuple(map(q,p)),'denominator':tuple(map(q,d)),'derivative_numerator':tuple(map(q,h)),
            'cuts':cut,'branches':branches,'tail_limits':(tail(True),tail(False)),
            'vertical_intercept':None if any(x.sign()==0 for x in holes) else line.quadratic_term(ordinate(p,d,line.Quadratic(0))),
            'polynomial_part':tuple(map(q,poly.pdiv(p,d)[0]))}


def split_common_factors(expanded,eligible):
    factors={a:k for a,k in m.common_mon(expanded).items() if eligible(a)}
    rest={tuple((a,k-factors.get(a,0)) for a,k in mon if k!=factors.get(a,0)):c for mon,c in expanded.items()}
    return factors,m.poly_expr(rest)


SHAPE_OUTPUTS={
    'strict_monotonicity_intervals':['all_strict_increasing_and_decreasing_intervals'],
    'concavity_and_inflection':['all_concavity_intervals','all_inflection_points'],
    'classify_extrema':['all_strict_local_extrema','justification_on_original_domain'],
}


def shape_task(task):
    meta=task.get('source',{});kind=task['kind']
    fields={'id','kind','source','function','variable','parameters','stated_conditions','requested_output','method_requirement'}
    provenance={'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','printed_instruction',
                'definition','definition_page','page_png_sha256'}
    if (kind not in SHAPE_OUTPUTS or set(task)-fields or set(meta)-provenance
            or task.get('requested_output')!=SHAPE_OUTPUTS[kind]
            or task.get('method_requirement','any')!='any'
            or meta.get('printed_instruction') not in (None,'Определить промежутки монотонности в строгом смысле.')
            or kind!='strict_monotonicity_intervals' and 'printed_instruction' in meta
            or meta.get('definition') not in (None,'Strict maximum/minimum in a two-sided open neighborhood contained in the domain.')):
        raise Unsupported('Original shape question, method or scope is not admitted')
    x=task['variable']
    return kind,x,('v',x)


def positive_parameter_reduction(task,lib,request):
    """Construct a dimensionless rational child while retaining the whole original domain."""
    from derivative_proofs import everywhere_guard, quadratic_point
    kind,name,x=shape_task(task)
    pars=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if (not lib.data.get('positive_axis_normalization') or kind=='classify_extrema'
            or len(pars)!=1 or conditions!=[pars[0]+'>0']):
        raise Unsupported('A single independent positive scale is required')
    scale=('s',pars[0]);raw=m.parse(task['function'],name,pars)
    u='phaseCoordinate'
    while u in (name,*pars):u+='_'
    local=('v',u);ctx=m.context(dict(variable=u))
    def strip(polynomial):
        if not polynomial:return ZERO,0
        parts={};degree=None
        for mon,c in polynomial.items():
            powers=dict(mon);a=powers.pop(scale,0)
            if (degree is not None and a!=degree) or set(powers)-{local}:
                raise Unsupported('An independent parameter remains after positive scaling')
            degree=a;parts[tuple(powers.items())]=c
        return m.poly_expr(parts),degree
    def reduce(e):
        ne=m.substitute(e,{x:m.mul(scale,local)})
        p,d=m.rational_form(ne);P,i=strip(p);D,j=strip(d)
        ratio=m.div(P,D)
        return ratio,i-j
    for guard,g in domain_conditions(raw,True):
        e,_=reduce(g)
        if not everywhere_guard((guard,e),u,ctx):
            raise Unsupported('An original guard was not established before homogeneous normalization')
    transformed,weight=reduce(raw)
    child=dict(kind=kind,function=source(transformed),variable=u,parameters=[],stated_conditions=[],
               requested_output=SHAPE_OUTPUTS[kind])
    evidence=request('complete derivative sign cells in an equivalent positive coordinate',child)
    answer=evidence['value']
    def position(point):
        if point in ('-inf','+inf'):return point
        return m.mul(scale,quadratic_point(line.read_quadratic_term(freeze(point))))
    def region(region):
        tag,parts=freeze(region)
        if tag!='real_set':raise Unsupported('A dimensionless interval certificate is required')
        return ('real_set',tuple((position(a),position(b),ca,cb) for a,b,ca,cb in parts))
    val={k:region(v) for k,v in answer.items() if k!='inflections'}
    if kind=='concavity_and_inflection':
        factor=m.power(scale,weight)
        val['inflections']=[(m.mul(scale,freeze(a)),m.mul(factor,freeze(b))) for a,b in answer['inflections']]
    plan=dict(theorem='method.positive_axis_normalization',scale=scale,weight=weight,original=raw,
              transformed=transformed,coordinate=u,child=child,cells=[],
              argument='Заменяем x положительной кратной новой координаты. Выделяем общий положительный масштаб из исходных ограничений и функции. Производные первого и второго порядка получают положительные множители. Переносим все интервалы и координаты перегибов обратно.')
    return plan,val


def indexed_phase_shape(task,lib):
    """Generate every interval of a constant-plus-one-harmonic derivative as a phase pullback."""
    from derivative_proofs import everywhere_guard,table
    from integrals import affine
    kind,name,x=shape_task(task)
    if not lib.data.get('indexed_derivative_phase') or task.get('parameters'):
        raise Unsupported('Unknown phase domain or original parameter restriction')
    conditions=task.get('stated_conditions',[]);text=task['function'];extension=False
    if kind=='strict_monotonicity_intervals' and conditions==[name+'>=0']:
        pattern=fr'piecewise\((.+) if {re.escape(name)}>0, 0 if {re.escape(name)}=0\)'
        branch=re.fullmatch(pattern,text)
        if not branch:raise Unsupported('The assigned endpoint and positive branch are not explicit')
        text=branch[1];extension=True
    elif conditions not in ([],[name+'>0']):raise Unsupported('The specified source domain needs a separate proof')
    raw=m.parse(text,name);ctx=m.context(dict(variable=name))
    if extension:
        if raw[0]!='mul' or x not in raw[1:]:raise Unsupported('The positive branch does not have a vanishing linear factor')
        amp=raw[1] if raw[2]==x else raw[2]
        def bounded(e):
            return (m.constant_defined(e,ctx) or e in (('sin',('ln',x)),('cos',('ln',x)))
                    or e[0] in ('add','mul') and all(bounded(z) for z in e[1:]))
        if not bounded(amp):raise Unsupported('No proved bounded amplitude at the original assigned zero')
    order=2 if kind=='concavity_and_inflection' else 1
    positive=bool(conditions);nonzero=False
    for k,g in domain_conditions(raw,True):
        if g==x and k in ('positive','nonzero'):
            positive|=k=='positive';nonzero|=k=='nonzero'
        elif not everywhere_guard((k,g),name,ctx):
            raise Unsupported('An original expression has other excluded or singular points')
    D=raw;steps=[]
    for _ in range(order):
        D,t=table(D,name,lib);steps.extend(t)
    top,bottom=m.rational_form(D);factors=[]
    def pull(p):
        def candidate(a):
            return (a==m.PI or a[0]=='exp' and not domain_conditions(a) or a==x and (positive or nonzero))
        common,rest=split_common_factors(p,candidate)
        for factor,power in common.items():
            if factor==x and not positive and power%2:
                raise Unsupported('An odd power would change sign between the two original components')
            factors.append((factor,power))
        return rest
    top,den=map(pull,(top,bottom))
    if den!=ONE and m.num(den) not in (1,) and not everywhere_guard(('positive',den),name,ctx):
        raise Unsupported('The remaining denominator has no sign certificate')
    rows,den2=m.rational_form(top)
    if den2!={():F(1)}:raise Unsupported('The reduced derivative is not a finite linear combination of harmonics')
    A=B=F(0);phase=None;fixed={}
    for mon,c in rows.items():
        if all(m.constant_defined(a,ctx) for a,_ in mon):fixed[mon]=c;continue

        if len(mon)!=1 or mon[0][1]!=1 or mon[0][0][0] not in ('sin','cos'):
            raise Unsupported('Multiple harmonic degrees need a polynomial phase reduction')
        tag,arg=mon[0][0]
        if phase is not None and arg!=phase:raise Unsupported('The harmonics do not share the same phase')
        phase=arg
        if tag=='sin':A+=c
        else:B+=c
    if phase is None or not (A or B):raise Unsupported('No nonconstant trigonometric phase')
    if phase==('ln',x):
        if not positive:raise Unsupported('The logarithmic coordinate requires the positive domain')
        inverse='exp(t)';orientation=1;domain=name+'>0'
    elif phase[0]=='div' and phase[2]==x and m.constant_defined(phase[1],ctx) and m.sign(phase[1],ctx) in (-1,1):
        if not (positive or nonzero):raise Unsupported('The inverse coordinate loses the original pole')
        c=source(phase[1]);inverse=f'({c})/t';orientation=-m.sign(phase[1],ctx)
        domain=name+('>0' if positive else '!=0, intersect each phase interval with each of t>0 and t<0')
    else:
        a,b=affine(phase,name);s=m.sign(a,ctx)
        if s not in (-1,1) or not all(m.constant_defined(v,ctx) for v in (a,b)) or positive or nonzero:
            raise Unsupported('The linear phase needs a total real affine bijection')
        inverse=f'(t-({source(b)}))/({source(a)})';orientation=s;domain='all real'
    radius2=A*A+B*B;C=m.poly_expr(fixed)
    comparison=m.sign(m.add(m.power(C,2),q(-radius2)),ctx)
    if comparison not in (-1,0,1):raise Unsupported('The constant must be compared exactly with the harmonic amplitude')
    delta=(m.mul(q(1 if B>0 else -1,2),m.PI) if A==0 else
           m.add(('atan',q(B/A)),m.PI if A<0 else ZERO))
    delta=source(m.simplify(delta));cases=[];roots=[]
    if comparison>=0 and not extension:
        raise Unsupported('The established global weak-sign route should handle this nonchanging phase')
    if comparison>=0:
        sign=m.sign(C,ctx)
        if sign not in (1,-1):raise Unsupported('The remaining weak sign could not be certified')
        cases=[dict(phase='all admitted t',sign=sign,isolated_zeros=comparison==0)]
    else:
        fresh=next(z for z in ('k','j','r','ell') if z!=name)
        alpha=source(('asin',m.div(m.neg(C),('sqrt',q(radius2)))))
        a=f'({alpha})-({delta})+2*pi*{fresh}';b=f'pi-({alpha})-({delta})+2*pi*{fresh}'
        end=f'({alpha})-({delta})+2*pi*({fresh}+1)'
        roots=[a,b];cases=[dict(phase=f'{a} < t < {b}',sign=1),dict(phase=f'{b} < t < {end}',sign=-1)]
    pullback={'t':source(phase),'x_from_t':inverse,'source_domain':domain,'integer_parameter':None if not roots else fresh,
              'inverse_orientation':orientation,'phase_cells':cases,'include_finite_in_domain_ends':True}
    if extension:
        pullback['value_at_zero']=ZERO
        pullback['continuous_extension_at_zero']=True
        pullback['zero_in_maximal_monotone_interval']=not bool(roots)
    if kind=='concavity_and_inflection':
        val=dict(convex=dict(pullback,select_sign=1),concave=dict(pullback,select_sign=-1),flat=[],
                 inflections=[dict(phase=z,inverse=inverse,ordinate='evaluate original function at inverse(z)',scope=domain) for z in roots])
    elif kind=='strict_monotonicity_intervals':
        val=dict(strictly_increasing=dict(pullback,select_sign=1),strictly_decreasing=dict(pullback,select_sign=-1),flat=[])
    else:
        val=dict(extrema=[dict(phase=z,inverse=inverse,scope=domain,type='strict_maximum' if orientation*(1 if j==0 else -1)<0 else 'strict_minimum',
                              ordinate='evaluate original function at inverse(z)') for j,z in enumerate(roots)],no_other_extrema=True)
    coverage={'chart':{'branches':cases}} if kind=='classify_extrema' else {'cells':cases}
    return dict(theorem='method.indexed_derivative_phase',function=raw,derivative=D,table_steps=steps,
                amplitude=[C,q(A),q(B)],phase=phase,positive_factors=factors,**coverage,
                argument='Табличное дифференцирование оставляет один общий угол. Снимаем доказанно положительные множители, сводим линейную комбинацию синуса и косинуса к одному синусу со сдвигом. Все фазы знака выходят из точных нулей, возвращаем их на каждой ветви координаты. Изолированный нуль без смены знака не разрывает строгую монотонность.'),val


def monomial_exponential_sign(task,lib):
    """Find all critical cuts from the sign of the linear derivative factor."""
    from integrals import affine
    kind,name,x=shape_task(task)
    if not lib.data.get('monomial_exponential_shape') or kind!='strict_monotonicity_intervals':
        raise Unsupported('Only the exact monotonicity contract is handled')
    pars=task.get('parameters',[]);guards=task.get('stated_conditions',[])
    if len(pars)>2 or not all(z in [p+'>0' for p in pars]+[name+'>=0',name+'>0'] for z in guards):
        raise Unsupported('Unbound source restrictions in the source exponential')
    ctx=m.context(dict(variable=name,parameters=pars,parameter_conditions=[z for z in guards if z not in (name+'>=0',name+'>0')]))
    raw=m.parse(task['function'],name,pars)
    if raw[0] not in ('mul','div'):raise Unsupported('Need a product or quotient of a monomial and exponential')
    lhs,rhs=raw[1:];divisor=raw[0]=='div'
    if not divisor and rhs[:2] in (('pow',x),('rpow',x)):lhs,rhs=rhs,lhs
    if lhs[:2] not in (('pow',x),('rpow',x)):
        raise Unsupported('The original monomial power does not use the source coordinate')
    power=q(lhs[2]) if lhs[0]=='pow' else lhs[2]
    if rhs[0]=='exp':
        if not pars:raise Unsupported('The established finite rational-sign route already handles an unscaled exponential')
        exponent=rhs[1]
    elif rhs[0]=='rpow' and not domain_conditions(rhs[2]) and m.constant_defined(rhs[1],ctx) and m.sign(rhs[1],ctx)==1:
        exponent=m.mul(('ln',rhs[1]),rhs[2])
    else:raise Unsupported('The original exponential needs a positive base')
    if domain_conditions(exponent) and rhs[0]=='exp':raise Unsupported('An original exponent guard must be proved')
    slope,offset=affine(exponent,name)
    if not all(m.constant_defined(v,ctx) for v in (power,slope,offset)) or m.sign(power,ctx)!=1:
        raise Unsupported('Power, slope and offset must be fixed and defined, with positive monomial order')
    if divisor:slope=m.neg(slope)
    s=m.sign(slope,ctx)
    if s not in (1,-1):raise Unsupported('The slope of the normalized exponential is not strictly signed')
    incidence=name+'>0' in guards or name+'>=0' in guards
    n=m.num(power)
    if not incidence and (n is None or n.denominator!=1):raise Unsupported('A real power needs its original positive domain')
    root=m.div(m.neg(power),slope);zero_in=name+'>0' not in guards
    if incidence:
        rows=[(ZERO,root,1),(root,'+inf',-1)] if s<0 else [(ZERO,'+inf',1)]
    elif n%2:
        # The factor x^(n-1) is positive away from zero and has even order there.
        rows=[('-inf',root,-s),(root,'+inf',s)]
    elif s<0:
        rows=[('-inf',ZERO,-1),(ZERO,root,1),(root,'+inf',-1)]
    else:
        rows=[('-inf',root,1),(root,ZERO,-1),(ZERO,'+inf',1)]
    cert=dict(cells=[dict(left=a,right=b,direction=d) for a,b,d in rows],source_zero_included=zero_in,
              source_guard=guards,positive_exponential=True,include_each_finite_admitted_endpoint=True)
    return (dict(theorem='method.monomial_exponential_sign',function=raw,source_order=power,exponential_slope=slope,
                 linear_factor=m.add(power,m.mul(slope,x)),argument='Производная равна положительному экспоненциальному множителю, степени x и линейному множителю p+kx. Для целой степени проверяем чётность по обе стороны нуля. Для положительной полуоси продолжаем к нулю только когда он входит в исходную область.',**cert),
            dict(strictly_increasing=dict(cert,select_sign=1),strictly_decreasing=dict(cert,select_sign=-1),flat=[]))


def absolute_harmonic_shape(task,lib):
    from integrals import affine
    kind,name,x=shape_task(task)
    if (not lib.data.get('indexed_derivative_phase') or kind!='strict_monotonicity_intervals' or task.get('parameters') or
            task.get('stated_conditions')):
        raise Unsupported('The global absolute-harmonic question is not bound')
    ctx=m.context(dict(variable=name));raw=m.parse(task['function'],name)
    if raw[0]!='add':raise Unsupported('Need a linear term and one absolute harmonic')
    line,h=raw[1:]
    if line[0]=='abs':line,h=h,line
    weight=ONE
    if h[0]=='mul' and m.constant_defined(h[1],ctx):weight,h=h[1:]
    if h[0]!='abs' or h[1][0]!='sin' or domain_conditions(line) or domain_conditions(h):
        raise Unsupported('The original amplitude or phase contains an extra domain restriction')
    a,_=affine(line,name);phase=h[1][1];b,shift=affine(phase,name)
    vals=list(map(m.num,(a,weight,b,shift)))
    if any(z is None for z in vals) or vals[1]<=0 or vals[2]<=0:
        raise Unsupported('Need a strictly positive amplitude and phase slope')
    a,c,b,shift=vals;strength=c*b
    if abs(a)>=strength:
        cases=[dict(phase='R',sign=1 if a>0 else -1)]
    else:
        k=next(z for z in ('k','j','r') if z!=name)
        cut=source(('acos',q(-a/strength)))
        cases=[dict(phase=f'{k}*pi<t<{k}*pi+{cut}',sign=1),
               dict(phase=f'{k}*pi+{cut}<t<({k}+1)*pi',sign=-1)]
    payload=dict(phase=source(phase),inverse=f'(t-({shift}))/{b}',phase_cells=cases,finite_boundaries_included=True)
    return (dict(theorem='method.absolute_harmonic_cells',function=raw,cells=cases,amplitude=q(strength),slope=q(a),
                 argument='Разбиваем в нулях исходного синуса. После сдвига угла на kπ производная на каждой открытой ячейке равна a+c b cos(t−kπ), строго убывает по фазе. Границы присоединяются по непрерывности; при одном знаке строгая монотонность продолжается через углы.'),
            dict(strictly_increasing=dict(payload,select_sign=1),strictly_decreasing=dict(payload,select_sign=-1),flat=[]))


def positive_logarithmic_curvature(task,lib):
    """Prove a positive polynomial in the log as a weighted sum of quadratics on x>0."""
    from collections import defaultdict
    from derivative_proofs import table
    kind,name,x=shape_task(task)
    if (not lib.data.get('positive_logarithmic_curvature') or kind!='concavity_and_inflection'
            or task.get('parameters') or task.get('stated_conditions')!=[name+'>0']):
        raise Unsupported('A complete curvature question on the positive half-line is required')
    raw=m.parse(task['function'],name);ctx=m.context(dict(variable=name));t=('ln',x)
    def valid(g):
        k,e=g
        return e==x or m.constant_defined(e,ctx) and (m.sign(e,ctx)==1 or k=='nonnegative' and m.known_nonnegative(e,ctx))
    if not all(map(valid,domain_conditions(raw,True))):
        raise Unsupported('The original positive interval has an unproved guard')
    D,s1=table(raw,name,lib);DD,s2=table(D,name,lib)
    if not m.contains(DD,t):raise Unsupported('The ordinary rational sign route remains available')
    cert=[]
    for expr in m.rational_form(DD):
        def factor(e):
            if e==x:return True
            return ((e[0]=='exp' or e[:2]==('rpow',x)) and all(map(valid,domain_conditions(e))))
        pulled,rem=split_common_factors(expr,factor)
        p,d=m.rational_form(rem)
        if d!={():F(1)}:raise Unsupported('One expanded factor is not a polynomial')
        groups=defaultdict(lambda:[F(0)]*3)
        for mon,c in p.items():
            powers=dict(mon)
            if set(powers)-{t,x} or powers.get(t,0)>2:raise Unsupported('Need a quadratic coefficient in the log')
            groups[powers.get(x,0)][powers.get(t,0)]+=c
        strict=False
        for a,b,c in groups.values():
            if c<0 or c==0 and (b or a<0) or c>0 and b*b>4*a*c:
                raise Unsupported('A coefficient can be negative for some logarithmic coordinate')
            strict|=bool(c>0 and b*b<4*a*c or c==0 and a>0)
        if not strict:raise Unsupported('No strict positive coefficient of the positive weights')
        cert.append(dict(positive_factors=list(pulled.items()),quadratic_coefficients=[(k,list(map(q,v))) for k,v in sorted(groups.items())]))
    return (dict(theorem='method.positive_logarithmic_curvature',function=raw,derivative=DD,cells=[dict(domain=name+'>0',direction=1)],
                 table_steps=s1+s2,certificates=cert,argument='На положительном луче отбрасываем только положительные множители. Группируем знаковые многочлены по степеням x. При каждой степени остаётся неотрицательный квадратный многочлен от ln x, и хотя бы один строго положителен. Поэтому вторая производная нигде не меняет знак.'),
            dict(convex=('real_set',((ZERO,'+inf',False,False),)),concave=('real_set',()),flat=('real_set',()),inflections=[]))


def cosine_coordinate_extrema(task,lib):
    """Reduce rational trigonometric expressions to one compact Chebyshev interval."""
    from derivative_proofs import quadratic_point, table
    from integrals import affine
    from polynomial import rf
    kind,name,x=shape_task(task)
    if (not lib.data.get('cosine_coordinate_extrema') or kind!='classify_extrema'
            or task.get('parameters') or task.get('stated_conditions')):
        raise Unsupported('This cosine coordinate requires an entire real source')
    raw=m.parse(task['function'],name);ctx=m.context(dict(variable=name));u='cosineCoordinate'
    if u==name:u+='_'
    z=('v',u);chebyshev=[ONE,z]
    def harmonic(angle):
        slope,offset=affine(angle,name);n=m.num(slope)
        if offset!=ZERO or n is None or n.denominator!=1 or not 1<=abs(n)<=8:
            raise Unsupported('A nonzero integral multiple of the common angle is required')
        k=abs(int(n))
        while len(chebyshev)<=k:
            chebyshev.append(m.add(m.mul(m.mul(q(2),z),chebyshev[-1]),m.neg(chebyshev[-2])))
        return chebyshev[k]
    def lower(e):
        if e[0]=='q':return e
        if e[0] in ('add','mul','div'):
            return (e[0],lower(e[1]),lower(e[2]))
        if e[0]=='cos':return harmonic(e[1])
        if e[0]=='pow':
            a,k=e[1:]
            if a[0]=='sin' and k%2==0:
                return m.power(m.add(ONE,m.neg(m.power(harmonic(a[1]),2))),k//2)
            return ('pow',lower(a),k)
        raise Unsupported('An additional source function cannot be expressed rationally through the cosine')
    lower_bound=line.Quadratic(F(-1));upper=line.Quadratic(F(1))
    def inside(a):return line.compare(a,lower_bound)>=0 and line.compare(a,upper)<=0
    guards=[]
    for rel,g in domain_conditions(raw,True):
        p,d=rf(lower(g),u)
        if not any(p) or any(inside(a) for a in [*rational_roots(p),*rational_roots(d)]):
            raise Unsupported('An original rational factor has unproved sign or a hole on the compact image')
        if rel!='nonzero' and p[0]*d[0]<=0:raise Unsupported('An original positive guard fails on the compact image')
        guards.append((rel,g))
    F0=lower(raw);D,steps=table(F0,u,lib);p,d=rf(D,u)
    if not any(p) or any(inside(a) for a in rational_roots(d)):
        raise Unsupported('The transformed function has a pole or is identically flat')
    cuts=ordered_cuts([lower_bound,upper,*[a for a in rational_roots(p) if inside(a)]])
    signs=[]
    for a,b in zip(cuts,cuts[1:]):
        sample=line.between(a,b)
        signs.append(1 if peval(p,sample)*peval(d,sample)>0 else -1)
    def value(at):return m.simplify(m.substitute(F0,{z:quadratic_point(at)}))
    def point(a,s,ph):
        return dict(type='strict_maximum' if s>0 else 'strict_minimum',phase_family=ph,value=value(a))
    k=next(i for i in ('k','j','r') if i!=name)
    extrema=[point(cuts[0],-signs[0],f'(2*{k}+1)*pi'),point(cuts[-1],signs[-1],f'2*pi*{k}')]
    for j,c in enumerate(cuts[1:-1]):
        a,b=signs[j:j+2]
        if a!=b:extrema.append(point(c,a,f'+/-acos({source(quadratic_point(c))})+2*pi*{k}'))
    branches=[dict(left=quadratic_point(a),right=quadratic_point(b),sign=s) for a,b,s in zip(cuts,cuts[1:],signs)]
    return (dict(theorem='method.cosine_coordinate_extrema',function=raw,chebyshev_coordinate=u,
                 rational_composition=F0,source_guards=guards,chart={'branches':branches},table_steps=steps,
                 argument='Раскрываем косинусы целых кратностей по рекурсии Чебышёва. Исходная область не теряется: все делители проверены на [-1,1]. На внутренности отрезка сравниваем знаки производной, а на концах отдельно рассматриваем односторонние знаки. Обращаем косинус по каждому периоду.'),
            dict(extrema=extrema,no_other_extrema=True,integer_parameter=k))


def extrema_plan(t,lib,request):
    for method in (indexed_phase_shape,cosine_coordinate_extrema):
        try:return method(t,lib)
        except (Unsupported,poly.NotRational,poly.Undefined):pass
    fields={'id','kind','schema','source','function','variable','parameters','stated_conditions','method_requirement','requested_output'}
    if not lib.data.get('strict_local_extrema') or set(t)-fields or t.get('kind')!='classify_extrema' or t.get('parameters',[]) or t.get('stated_conditions',[]):
        raise Unsupported('Unimplemented constraints or parameter classification for extrema')
    if t.get('method_requirement','any') not in ('any','first_derivative_test') or set(t.get('requested_output',()))!={'all_strict_local_extrema','justification_on_original_domain'}:
        raise Unsupported('Different extremum criterion, endpoint convention or additional source output')
    var=t['variable'];ctx=m.context({'variable':var});raw=m.parse(t['function'],var);e=raw
    def cubed(node):
        if node[0]=='cbrt':return node[1]
        if node[0] in ('mul','div'):return node[0],cubed(node[1]),cubed(node[2])
        if node[0]=='pow':return 'pow',cubed(node[1]),node[2]
        poly.rf(node,var);return 'pow',node,3
    mode='rational';positive=[];sign_key='derivative_sign'
    try:
        if raw[0]=='abs':mode='square_of_absolute_value';e=('pow',raw[1],2)
        elif raw[0]=='sqrt':mode='increasing_square_root';e=raw[1]
        else:
            try:poly.rf(raw,var)
            except poly.NotRational:e=cubed(raw);mode='increasing_cube'
        chart=graph_curve(e,var)
    except poly.NotRational:
        child=request('derivative on the original domain',{'kind':'partial_derivatives','function':t['function'],'variables':[var],'requested_partials':[[var]],
                       'method_requirement':'table_and_rules','requested_output':['specified_partial_derivatives']})
        formula=m.substitute(freeze(child['value'][0]),{('s',var):('v',var)})
        def strip(expanded):
            exps,rest=split_common_factors(expanded,lambda a:a[0]=='exp')
            positive.extend(exps.items())
            return rest
        p,d=map(strip,m.rational_form(formula))
        if not positive:raise Unsupported('No rational derivative-sign certificate')
        e=('div',p,d);mode='derivative_with_positive_factors';sign_key='sign'
        chart=graph_curve(e,var,domain_conditions(raw))
    if t.get('method_requirement')=='first_derivative_test' and mode in ('square_of_absolute_value','increasing_cube','increasing_square_root'):
        raise Unsupported('The requested derivative of the original function has not been established')
    result=[]
    if mode=='increasing_square_root':
        for b in chart['branches']:b['in_domain']=b['sign']>=0
    for i,point in enumerate(chart['cuts']):
        if not all(b.get('in_domain',True) for b in chart['branches'][i:i+2]):continue
        before=chart['branches'][i][sign_key];after=chart['branches'][i+1][sign_key]
        if point['type']!='point' or (before,after) not in ((1,-1),(-1,1)):continue
        x=line.read_quadratic_term(point['x']);at=q(x.a) if not x.b else m.add(q(x.a),m.mul(q(x.b),('sqrt',q(x.d))))
        value=m.substitute(raw,{('v',var):at})
        if not m.constant_defined(value,ctx):raise Unsupported('Original extremum value has an unresolved raw domain')
        result.append({'type':'strict_maximum' if before==1 else 'strict_minimum','point':at,'value':m.simplify(value)})
    return {'method':mode,'rational_expression':e,'positive_factors':tuple(positive),'sign_key':sign_key,'chart':chart},{'extrema':tuple(result)}


def optimize_geometric_profile(profile, variable, scalar):
    """Global derivative comparisons in normalized coordinates, including open ends."""
    from tasks import source
    x=variable
    one=q(1)
    kind,*items=profile
    def power(base,exponent):
        p=F(exponent)
        if p.denominator==1:return m.power(base,p.numerator)
        if p.denominator in (2,3):return m.power(('sqrt' if p.denominator==2 else 'cbrt',base),p.numerator)
        return ('rpow',base,q(p))
    def outcome(point,condition=None,attained=True):
        return dict(point=point,condition=condition,attained=attained)
    if kind=='unit_product':
        p,r=map(F,items)
        if min(p,r)<=0:raise Unsupported('Positive powers on both factors are required')
        fn=m.mul(power(x,p),power(m.add(one,m.neg(x)),r))
        sign=m.add(q(p),m.mul(q(-p-r),x))
        proof='Оба множителя положительны на (0,1). Логарифмическая производная после умножения на t(1−t) имеет знак линейного выражения. Оно меняет знак с плюса на минус.'
        return fn,sign,proof,[outcome(q(p/(p+r)))]
    if kind=='opposite_powers':
        a,p,b,r,unit=items
        a,p,b,r=map(F,(a,p,b,r))
        if min(a,p,b,r)<=0:raise Unsupported('Positive coefficients and opposite nonzero powers required')
        threshold=b*r/(a*p)
        if unit and threshold>=1:raise Unsupported('The stationary point must be inside the physical upper bound')
        fn=m.add(m.mul(q(a),power(x,p)),m.mul(q(b),power(x,-r)))
        sign=m.add(m.mul(q(a*p),power(x,p+r)),q(-b*r))
        proof='После умножения производной на положительную степень t её знак задаёт строго возрастающая степень. Ниже точки равенства производная отрицательна, выше положительна.'
        return fn,sign,proof,[outcome(power(q(threshold),1/(p+r)))]
    if kind=='reciprocal_pair':
        a,b,p=items
        p=F(p);a,b=map(scalar,(a,b))
        if p<=0:raise Unsupported('A positive reciprocal exponent is required')
        complement=m.add(one,m.neg(x))
        ratio=m.div(x,complement)
        balance=power(m.div(a,b),1/(p+1))
        sign=m.add(m.mul(b,power(ratio,p+1)),m.neg(a))
        fn=m.add(m.mul(a,power(x,-p)),m.mul(b,power(complement,-p)))
        proof='Коэффициенты положительны. Производная имеет знак разности между степенью отношения t/(1−t), умноженной на второй коэффициент, и первым коэффициентом. Отношение строго возрастает от нуля до бесконечности.'
        return fn,sign,proof,[outcome(m.div(balance,m.add(one,balance)))]
    if kind=='even_power_and_linear':
        n,a,b,c=items
        if n<2 or n%2 or a<=0:raise Unsupported('A positive even leading term is required')
        fn=m.add(m.add(m.mul(q(a),m.power(x,n)),m.mul(q(b),x)),q(c))
        sign=m.add(m.mul(q(n*a),m.power(x,n-1)),q(b))
        base=F(-b,n*a)
        point=q(0) if not base else m.mul(q(1 if base>0 else -1),power(q(abs(base)),F(1,n-1)))
        return fn,sign,'Производная строго возрастает на всей прямой и меняет знак при единственном действительном корне.',[outcome(point)]
    if kind=='quadratic_to_cap':
        a,b,c,include=items
        a,b,c=map(scalar,(a,b,c))
        fn=m.add(m.add(m.mul(a,m.power(x,2)),m.mul(b,x)),c)
        sign=m.add(m.mul(m.mul(q(2),a),x),b)
        upper=m.add(m.mul(q(2),a),b)
        point=m.div(m.neg(b),m.mul(q(2),a))
        proof='Производная при t=0 положительна. Если её значение при t=1 отрицательно, вершина лежит строго внутри интервала. Иначе функция возрастает во всём интервале, и верхняя грань достигается только при допустимой границе t=1.'
        return fn,sign,proof,[outcome(point,source(upper)+'<0'),outcome(one,source(upper)+'>=0',include)]
    if kind=='positive_quadratic_sign':
        fn,a,b,c=map(scalar,items)
        sign=m.add(m.add(m.mul(a,m.power(x,2)),m.mul(b,x)),c)
        disc=m.add(m.power(b,2),m.neg(m.mul(q(4),m.mul(a,c))))
        point=m.div(m.add(m.neg(b),m.neg(('sqrt',disc))),m.mul(q(2),a))
        proof='Производная имеет знак квадратного трёхчлена с отрицательным старшим и положительным свободным коэффициентами. У него ровно один положительный корень. Разные знаки на границах помещают корень в открытый интервал.'
        return fn,sign,proof,[outcome(point)]
    if kind=='projection_ends':
        return x,one,'Скалярное произведение с единичным направлением принимает все значения между −1 и 1. Обе границы достигаются при противоположных направлениях.',[outcome(q(-1)),outcome(one)]
    if kind=='square_root_sum':
        a,b=map(scalar,items)
        fn=m.add(m.mul(a,('sqrt',x)),m.mul(b,('sqrt',m.add(one,m.neg(x)))))
        total=m.add(m.power(a,2),m.power(b,2))
        sign=m.add(m.power(a,2),m.neg(m.mul(total,x)))
        proof='После умножения на положительный знаменатель и сравнения квадратов положительных слагаемых знак производной сводится к линейному. На отрезке он меняется с плюса на минус ровно один раз.'
        return fn,sign,proof,[outcome(m.div(m.power(a,2),total))]
    if kind=='linear_plus_hypotenuse':
        include=items[-1]
        a,b,upper=map(scalar,items[:-1])
        fn=m.add(m.mul(a,('sqrt',m.add(one,m.power(x,2)))),m.neg(m.mul(b,x)))
        sign=m.add(m.mul(m.add(m.power(a,2),m.neg(m.power(b,2))),m.power(x,2)),m.neg(m.power(b,2)))
        mid=m.div(b,('sqrt',m.add(m.power(a,2),m.neg(m.power(b,2)))))
        difference=m.add(upper,m.neg(mid))
        proof='На неотрицательной полуоси сравнение положительных сторон после возведения в квадрат даёт строго возрастающий знаковый трёхчлен. Его положительный корень даёт минимум, если лежит до верхнего конца. Иначе минимум достигается на верхнем конце.'
        inside,at_bound=('>=','<') if include else ('>','<=')
        return fn,sign,proof,[outcome(mid,source(difference)+inside+'0'),outcome(upper,source(difference)+at_bound+'0',include)]
    if kind=='affine_squared_over_product':
        a,b,c=map(scalar,items)
        factor=m.add(a,m.mul(b,x))
        fn=m.div(m.power(factor,2),m.mul(x,m.add(c,m.neg(x))))
        coefficient=m.add(m.mul(b,c),m.mul(q(2),a));product=m.mul(a,c)
        sign=m.add(m.mul(coefficient,x),m.neg(product))
        proof='Знак производной совпадает со знаком линейного выражения после сокращения положительных множителей. Его единственный корень лежит в интервале, и знак меняется с минуса на плюс.'
        return fn,sign,proof,[outcome(m.div(product,coefficient))]
    if kind=='rational':
        expression,interval,sense=items
        fn=scalar(expression);chart=graph_curve(fn,x[1])
        lo,hi=interval
        cut=lambda endpoint,line_point: endpoint is None or line.compare(line.Quadratic(endpoint),line_point)
        interior=[]
        for i,item in enumerate(chart['cuts']):
            at=line.read_quadratic_term(item['x'])
            if (lo is not None and cut(lo,at)>=0) or (hi is not None and cut(hi,at)<=0):continue
            if item['type']!='point':raise Unsupported('A pole or a hole meets the geometric interval')
            if chart['branches'][i]['derivative_sign']!=chart['branches'][i+1]['derivative_sign']:
                interior.append((i,at))
        if len(interior)!=1:raise Unsupported('The profile needs a single interior change of derivative sign')
        i,at=interior[0];start=1 if sense=='maximum' else -1;turn=chart['cuts'][i]['x']
        for branch in chart['branches']:
            a,b=branch['left'],branch['right']
            if b!='+inf' and lo is not None and cut(lo,line.read_quadratic_term(b))>=0:continue
            if a!='-inf' and hi is not None and cut(hi,line.read_quadratic_term(a))<=0:continue
            before=b!='+inf' and line.compare(line.read_quadratic_term(b),at)<=0
            if branch['derivative_sign']!=(start if before else -start):
                raise Unsupported('A whole-interval derivative sign has not been checked')
        point=q(at.a) if not at.b else m.add(q(at.a),m.mul(q(at.b),('sqrt',q(at.d))))
        return fn,dict(turn=turn,chart=chart),'Точная таблица знаков подтверждает рост и убывание на всех соответствующих ветвях исходного профиля.' if sense=='maximum' else 'Точная таблица знаков подтверждает убывание и рост на всех соответствующих ветвях исходного профиля.',[outcome(point)]
    raise Unsupported('No whole-interval extremum argument for this profile')



def physical_axis_extremum(task):
    provenance=task.get('source',{})
    if (not isinstance(provenance,dict) or set(provenance)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or set(task)-{'id','kind','schema','source','given','requested_output'}):
        raise Unsupported('The applied problem must bind the original geometry and outputs')
    given=task.get('given','');out=task.get('requested_output');title=provenance.get('literal_requirement')
    name=r'([A-Za-z][A-Za-z0-9_]*)'
    sphere=re.fullmatch(fr'point light on line of centers outside two disjoint spheres of radii {name}>{name}(?:, center distance {name})?',given)
    rod=re.fullmatch(fr'rod of length {name}>2{name} lowered into hemispherical bowl of radius {name}',given)
    if sphere and out==['maximize_total_illuminated_surface','location_of_source'] and title in (
            None,'Найти положение, максимизирующее сумму освещенных частей поверхностей.'):
        R,r,D=sphere.groups()
        if R==r or D in (R,r):raise Unsupported('The radii and separation name have distinct roles')
        if D is None:
            D='D'
            while D in (R,r):D+='_'
        R,r,D=(('s',n) for n in (R,r,D))
        root=lambda e:m.simplify(('sqrt',e))
        gap=m.add(m.power(R,2),m.neg(m.power(r,2)))
        r3=m.mul(R,root(R));s3=m.mul(r,root(r))
        weights=m.add(r3,s3)
        lost_at_infinity=m.add(m.power(R,2),m.neg(m.mul(R,root(gap))))
        threshold=m.div(m.power(weights,2),lost_at_infinity)
        between=m.div(m.mul(D,r3),weights)
        area_constant=m.add(m.power(R,2),m.power(r,2))
        scale=m.mul(q(2),m.PI)
        inside=m.mul(scale,m.add(area_constant,m.neg(m.div(m.power(weights,2),D))))
        outside=m.mul(scale,m.add(m.power(r,2),m.mul(R,root(gap))))
        return dict(theorem='method.coaxial_opaque_sphere_caps',argument=[
            'Между шарами лучи к их видимым шапкам расходятся в разные полупространства. При расстояниях d и D−d освещённая площадь, делённая на 2π, равна R²+r²−R³/d−r³/(D−d).',
            'По Коши минимально возможная потеря равна (R^(3/2)+r^(3/2))²/D и достигается при отношении расстояний R^(3/2):r^(3/2). Сохраняем открытый интервал между поверхностями.',
            'На внешнем луче ближний шар отбрасывает конус тени. Если его угловой радиус не меньше дальнего, дальняя освещённая площадь нулевая. Иначе из равенства касательного угла следует θ₀=asin(a(L+D)/(bL))−asin(a/L), где a,b — ближний и дальний радиусы и L — расстояние до ближнего центра.',
            'Часть дальнего шара вне тени имеет площадь 2πb²(cos θ₀−b/(L+D)). Здесь θ₀ строго убывает: производная первой арксинусной части имеет больший модуль, поскольку D>b и её аргумент больше a/L. Поэтому обе внешние площади растут к своим недостижимым пределам.',
            'Когда ближе большой шар, внешняя грань равна 2πR². Когда ближе малый, она равна 2π(r²+R√(R²−r²)) и строго больше первой, так как √(1−t²)>1−t² при 0<t<1.',
            'Сравнение внутренней оценки с большей внешней гранью даёт порог D*. При D≥D* стационарная точка лежит строго вне шаров: D*>Σ/√r≥Σ/√R, поскольку 1−√(1−t²)<t≤√t. При D<D* вся внутренняя ветвь ниже внешней грани.'
        ],separation=D,conditions=[R[1]+'>'+r[1]+'>0',D[1]+'>'+R[1]+'+'+r[1]],
                    model='opaque disjoint spheres and point source with direct rays'),dict(branches=[
            dict(condition={'relation':'at_least','lhs':D,'rhs':threshold},attained=True,
                 maximum=inside,location=dict(between_centres=True,distance_from_large_centre=between)),
            dict(condition={'relation':'less','lhs':D,'rhs':threshold},attained=False,supremum=outside,
                 approaching='outer ray past the smaller sphere')])
    if rod and out==['equilibrium_configuration'] and title in (None,'Найти положение равновесия стержня.'):
        length,radius,other=rod.groups()
        if radius!=other or length==radius:raise Unsupported('The bowl radius must match the hypothesis')
        L,a=('s',length),('s',radius)
        Q=m.add(m.power(L,2),m.mul(q(128),m.power(a,2)))
        c=m.div(m.add(L,('sqrt',Q)),m.mul(q(16),a))
        top=m.mul(q(4),a)
        return dict(theorem='method.hemispherical_rod_energy',argument=[
            'В модели однородного тонкого стержня и гладкой чаши устойчивое равновесие минимизирует высоту центра масс.',
            'Зафиксируем наклон θ над горизонтом. Заглублённый конец опирается на сферу, выход из чаши приходится на кромку. Длина хорды от кромки до заглублённого конца не превосходит 2a cos θ. Равенство получается в вертикальной диаметральной плоскости.',
            'Поэтому наименьшая возможная высота имеет вид (L/2−2a cos θ)sin θ. Производная равна (L/2)cos θ−2a cos 2θ.',
            'По c=cos θ знак производной задаёт вогнутый трёхчлен −4ac²+Lc/2+2a. На [0,1] он имеет единственный положительный корень в точности при L<4a. При L≥4a высота минимальна в горизонтальном положении.'
        ],conditions=[a[1]+'>0',L[1]+'>2*'+a[1]],model='homogeneous thin rod, symmetric frictionless support, stable equilibrium under gravity'),dict(other_stationary_example='A vertical rod with its lower tip at the bottom is also a force balance, unstable to tilt.',branches=[
            dict(condition={'relation':'less','lhs':L,'rhs':top},stable=True,angle_to_horizontal=('acos',c),
                 direction='vertical diametral plane',inserted_length=m.mul(m.mul(q(2),a),c)),
            dict(condition={'relation':'at_least','lhs':L,'rhs':top},stable=True,angle_to_horizontal=m.ZERO,
                 placement='horizontal, with rim supports bracketing the centre of mass')])
    raise Unsupported('There is no matching complete physical equilibrium or visibility goal')


def applied_extremum(task,library):
    """Compile original geometric data into a global one-variable proof."""
    if library.data.get('physical_axis_extrema') and 'requested_output' in task:
        return physical_axis_extremum(task)
    if not library.data.get('normalized_applied_extrema') or set(task)-{'id','kind','schema','source','given'}:
        raise Unsupported('Unsupported mathematical output or applied-extremum input')
    provenance=task.get('source',{})
    if (not isinstance(provenance,dict) or set(provenance)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or not isinstance(task.get('given'),str)):
        raise Unsupported('The original applied-extremum condition is not identified')
    from tasks import source
    given=task['given'];request=provenance.get('literal_requirement');v='t'
    def matches(pattern):return re.fullmatch(pattern,given)
    name=r'([A-Za-z][A-Za-z0-9_]*)'
    def model(expected,params,conditions,interval,profile,scale,dimensions,reason,sense,offset='0',readout='identity'):
        if request!=expected or len(set(params))!=len(params):
            raise Unsupported('The geometric model does not bind the complete requested extremum')
        variable=v
        while variable in params:variable+='_'
        # All formulas refer to the same fresh scalar coordinate.
        def scalar(text):
            text=re.sub(r'\bt\b',variable,text) if 't' not in params else text.replace('@',variable)
            return m.parse(text.replace('@',variable),variable,params)
        x=('v',variable)
        objective,sign,calculus,branches=optimize_geometric_profile(profile,x,scalar)
        scale_term=scalar(scale);offset_term=scalar(offset)
        if m.variable_in(scale_term,variable) or m.variable_in(offset_term,variable):
            raise Unsupported('The physical normalization must be independent of the scalar coordinate')
        formulas={key:scalar(formula) for key,formula in dimensions.items()}
        def at(expr,p):return m.simplify(m.substitute(expr,{x:p}))
        results=[]
        for row in branches:
            p=row['point']
            val=at(objective,p)
            if readout=='reciprocal':val=m.div(q(1),val)
            bound=m.add(offset_term,m.mul(scale_term,val))
            if readout=='sqrt':bound=m.simplify(('sqrt',bound))
            results.append(dict(condition=row['condition'],attained=row['attained'],coordinate=p,
                                bound=bound,configuration={key:at(expr,p) for key,expr in formulas.items()} if row['attained'] else {}))
        premises=dict(condition_binding=conditions,parameter_names=params,scalar=variable,domain=interval,
                      quantities=formulas,scale=scale_term,offset=offset_term,model_argument=reason,readout=readout)
        return dict(theorem='method.normalized_applied_extrema',model=premises,profile=objective,
                    derivative_sign=sign,calculus_argument=calculus),dict(extremum=sense,branches=results)
    if found:=matches('rectangle of fixed area '+name):
        S=found[1]
        return model('Найти прямоугольник с наименьшим периметром.',[S],[S+'>0'],'(0,+inf)',
            ('opposite_powers',1,1,1,1,False),f'2*sqrt({S})',{'sides_1':f'sqrt({S})*@','sides_2':f'sqrt({S})/@'},
            'Произведение двух положительных сторон равно площади. Положительная первая сторона однозначно определяет вторую. Деление первой стороны на корень из площади даёт параметр t.', 'minimum')
    if found:=matches('right triangle, a leg plus hypotenuse equal constant '+name):
        L=found[1]
        return model('Найти треугольник наибольшей площади.',[L],[L+'>0'],'(0,1)',
            ('unit_product',F(1,2),1),f'{L}^2/4',{'leg_1':f'{L}*(1-@)/2','leg_2':f'{L}*sqrt(@)','hypotenuse':f'{L}*(1+@)/2'},
            'Квадрат второго катета равен разности квадратов гипотенузы и первого катета. После деления на квадрат фиксированной суммы получается t. Все t между нулём и единицей дают невырожденный прямоугольный треугольник.', 'maximum')
    if found:=matches(r'((?:closed|open) circular cylindrical tin of fixed capacity|right circular cylinder topped by hemisphere, total volume) '+name):
        V=found[2];cap=found[1].startswith('right')
        open_top=found[1].startswith('open')
        R=f'cbrt({"3*" if cap else ""}{V}/({"2*" if cap else ""}pi))'
        a,b=(F(5,3),F(4,3)) if cap else (F(1 if open_top else 2),F(2))
        h=f'{V}/(pi*({R}*@)^2)'+(f'-2*{R}*@/3' if cap else '')
        geometry='Объём добавленного полушара равен 2πr³/3, площадь полусферы равна 2πr². Дно и бок цилиндра входят в полную поверхность, круг сопряжения внутри тела.' if cap else (
            f'Объём равен πr²h. Бок имеет площадь 2πrh, число внешних круговых оснований равно {1 if open_top else 2}. '
            'Для каждого положительного радиуса объём определяет положительную высоту.')
        title='Найти размеры минимальной полной поверхности.' if cap else 'Найти размеры с минимальной полной поверхностью.'
        return model(title,[V],[V+'>0'],'(0,1)' if cap else '(0,+inf)',('opposite_powers',a,2,b,1,cap),
                     f'pi*{R}^2',{'radius':R+'*@','cylinder_height':h},geometry,'minimum')
    if matches(r'rectangle inscribed in given circular segment no larger than a semicircle'):
        return model('Найти максимальную площадь прямоугольника.',['R','d'],['R>0','0<=d<R'],'(d/R,1)',
            ('positive_quadratic_sign','(@-d/R)*sqrt(1-@^2)','-2','d/R','1'),'2*R^2',
            {'width':'2*R*sqrt(1-@^2)','height':'R*@-d','distance_of_arc_side_from_center':'R*@'},
            'Три вершины прямоугольника на окружности влекут четвёртую на той же окружности. Поэтому у невырожденного вписанного прямоугольника хотя бы две вершины лежат на хорде. Они соседние, так как при диагонали на хорде другая диагональ выходит за пределы сегмента. При ординате верхней стороны Rt высота равна Rt−d и ширина равна 2R√(1−t²). После удаления положительного знаменателя производная имеет значения знакового трёхчлена 1−(d/R)²>0 у нижнего края и d/R−1<0 у верхнего.', 'maximum')
    ellipse=r'x²/'+name+r'²\+y²/'+name+r'²=1'
    if found:=matches('rectangle with sides parallel to axes inscribed in '+ellipse):
        a,b=found.groups()
        return model('Найти прямоугольник наибольшей площади.',[a,b],[a+'>0',b+'>0'],'(0,1)',
            ('unit_product',F(1,2),F(1,2)),f'4*{a}*{b}',{'width':f'2*{a}*sqrt(@)','height':f'2*{b}*sqrt(1-@)'},
            'Пара точек эллипса на одной горизонтали имеет абсциссы противоположных знаков, а пара на одной вертикали имеет противоположные ординаты. Параметр t есть квадрат отношения положительной абсциссы вершины к соответствующей полуоси.', 'maximum')
    exponent=r'(?:\^([1-9][0-9]?)|(²))?'
    if found:=matches(r'diameter '+name+r' of circular log; rectangular beam breadth b,height h; strength proportional to b'+exponent+r'\*h'+exponent):
        D=found[1]
        b_power=2 if found[3] else int(found[2] or 1)
        h_power=2 if found[5] else int(found[4] or 1)
        return model('Найти размеры с наибольшей прочностью.',[D],[D+'>0'],'(0,1)',
            ('unit_product',F(h_power,2),F(b_power,2)),f'{D}^{b_power+h_power}',{'breadth':D+'*sqrt(1-@)','height':D+'*sqrt(@)'},
            f'Диагональ вписанного прямоугольника равна диаметру. Если сечение меньше, его подобное увеличение повышает прочность. Квадрат относительной высоты равен t, прочность сравнивается по b^{b_power}h^{h_power}.',
            'maximum')
    if found:=matches('hemisphere radius '+name+', inscribed rectangular box with square base'):
        R=found[1]
        return model('Найти параллелепипед наибольшего объема.',[R],[R+'>0'],'(0,1)',
            ('unit_product',F(1,2),1),f'2*{R}^3',{'height':R+'*sqrt(@)','base_side':f'{R}*sqrt(2*(1-@))'},
            'У параллелепипеда все вершины одинаково удалены от его центра. Поэтому вершины на сферической границе максимизируют линейную функцию на его вершинах. Не все восемь могут быть на сфере, иначе центр совпадёт с центром полушара, и часть вершин окажется ниже его плоскости. На плоскости и на сфере лежит не более чем по четыре вершины, следовательно, это две противоположные грани. На высоте h горизонтальное сечение есть диск радиуса √(R²−h²). Из прямоугольников с ограниченной диагональю наибольшую площадь имеет квадрат. Он достижим над центром полушара.',
            'maximum')
    if found:=matches('circular cylinder inscribed in sphere of radius '+name):
        R=found[1];volume=request=='Найти наибольший объём.'
        title='Найти наибольший объём.' if volume else 'Найти цилиндр с максимальной полной поверхностью.'
        profile=('unit_product',F(1,2),1) if volume else ('rational','(1+2*@)/(1+@^2)',(F(0),None),'maximum')
        dims={'radius':R+'*sqrt(1-@)','height':f'2*{R}*sqrt(@)'} if volume else {
            'radius':R+'/sqrt(1+@^2)','height':f'2*{R}*@/sqrt(1+@^2)'}
        return model(title,[R],[R+'>0'],'(0,1)' if volume else '(0,+inf)',profile,
                     f'2*pi*{R}^{3 if volume else 2}',dims,
                     'Осевая плоскость даёт вписанный в большой круг прямоугольник, поэтому r²+(h/2)²=R². Решение этого соотношения по квадрату относительной высоты или по отношению h/(2r) охватывает все положительные размеры.',
                     'maximum')
    if given=='circular cone circumscribed about fixed sphere':
        return model('Найти конус наименьшего объема.',['R'],['R>0'],'(0,1)',
            ('rational','(1+@)^2/(@*(1-@))',(F(0),F(1)),'minimum'),'pi*R^3/3',
            {'height':'R*(1+1/@)','radius':'R*(1+@)/sqrt(1-@^2)'},
            'В осевом сечении окружность радиуса R вписана в равнобедренный треугольник. При синусе полуугла t расстояние от вершины до центра равняется R/t, полная высота R+R/t. Радиус основания равен высоте, умноженной на t/√(1−t²). Все t между нулём и единицей реализуются.', 'minimum')
    if found:=matches('cone with fixed slant height '+name+'|sector cut from a disk of radius '+name+', roll remainder into a conical funnel'):
        length=found[1] or found[2];sector=found[1] is None
        dims={'height':length+'*sqrt(@)','radius':length+'*sqrt(1-@)'}
        if sector:dims['removed_sector_angle']='2*pi*(1-sqrt(1-@))'
        return model('Какой сектор вырезать для наибольшей вместимости?' if sector else 'Найти наибольший объем.',
            [length],[length+'>0'],'(0,1)',('unit_product',F(1,2),1),f'pi*{length}^3/3',dims,
            'Образующая, радиус основания и высота образуют прямоугольный треугольник. При сворачивании длина оставшейся дуги становится длиной окружности основания, а радиус исходного диска становится образующей. Значение t равно квадрату относительной высоты.' if sector else 'Образующая, радиус и высота образуют прямоугольный треугольник. Параметр t равен квадрату высоты, делённому на квадрат образующей.', 'maximum')
    if found:=matches('right circular cone with axial aperture 2'+name+' and base radius '+name+', inscribed cylinder'):
        angle,R=found.groups();c=f'cot({angle})'
        return model('Найти цилиндр наибольшей полной поверхности.',[angle,R],[R+'>0',f'0<{angle}<pi/2'],'(0,1)',
            ('quadratic_to_cap',f'1-{c}',c,'0',False),f'2*pi*{R}^2',
            {'radius':R+'*@','height':f'{R}*{c}*(1-@)'},
            'Круговое сечение боковой поверхности прямого конуса горизонтально: ограничение её квадратичной формы на наклонную плоскость имеет неодинаковые коэффициенты в горизонтальном направлении и перпендикулярном ему. Два равных обода на боковой поверхности имели бы одинаковую высоту, поэтому нижний обод вписанного цилиндра лежит в основании. Подобие даёт высоту R cot(α)(1−t) при радиусе Rt. Предельный радиус R соответствует нулевой высоте. Производная при t=0 положительна, поскольку 0<α<π/2.', 'maximum')
    if found:=matches(r'point M\('+name+r',\1\), parabola y²=2\1\*x'):
        P=found[1]
        return model('Найти кратчайшее расстояние.',[P],[P+'!=0'],'(-inf,+inf)',
            ('even_power_and_linear',4,F(1,4),-2,2),P+'^2',{'x':P+'*@^2/2','y':P+'*@'},
            'Вся парабола параметризуется y=pt, x=pt²/2. Сравниваем квадраты расстояний, поскольку расстояния неотрицательны.', 'minimum',readout='sqrt')
    point=r'(-?\d+(?:\.\d+)?)'
    if found:=matches(r'point A=\('+point+','+point+r'\), (?:unit circle x²\+y²=1|circle centered at origin of radius '+name+')'):
        a,b,R=found.groups();r=R or '1'
        norm=f'sqrt(({a})^2+({b})^2)'
        if F(a)==F(b)==0:raise Unsupported('A central point gives a separate constant-distance case')
        return model('Найти кратчайшее и наибольшее расстояния.',[R] if R else [],[R+'>0'] if R else [],'[-1,1]',
            ('projection_ends',),f'2*{r}*{norm}',{'x':f'-{r}*({a})*@/{norm}','y':f'-{r}*({b})*@/{norm}'},
            'Квадрат расстояния от A до точки окружности равен сумме квадратов расстояния A от центра и радиуса минус удвоенное скалярное произведение. Выбираем t как косинус угла с направлением, противоположным OA. На крайних значениях точки лежат на прямой OA.',
            'minimum_and_maximum',offset=f'{norm}^2+{r}^2',readout='sqrt')
    if found:=matches(r'ellipse '+ellipse+r',0<\2<\1; chord through vertex B\(0,-\2\)'):
        a,b=found.groups()
        return model('Найти наибольшую хорду.',[a,b],[f'0<{b}<{a}'],'[0,1]',
            ('quadratic_to_cap',f'{b}^2-{a}^2',f'2*{b}^2',f'{a}^2+{b}^2',True),'1',
            {'x_absolute':a+'*sqrt(1-@^2)','y':b+'*@'},
            'Сравниваем квадраты длин хорд. Второй конец имеет координаты (±a√(1−t²),bt). При t<0 отражение во вторую полуэллиптическую дугу увеличивает длину, поскольку меняет знак положительного линейного коэффициента 2b²t. При t=1 диаметр достижим.', 'maximum',readout='sqrt')
    if found:=matches('tangent to ellipse '+ellipse+r' at M\(x,y\), triangle formed with coordinate axes'):
        a,b=found.groups()
        return model('Провести касательную так, чтобы площадь треугольника наименьшая.',[a,b],[a+'>0',b+'>0'],'(0,1)',
            ('unit_product',F(1,2),F(1,2)),f'{a}*{b}/2',{'x_absolute':a+'*sqrt(@)','y_absolute':b+'*sqrt(1-@)'},
            'Касательная xX/a²+yY/b²=1 отсекает отрезки длины a²/|x| и b²/|y|. Площадь равна ab/(2√(t(1−t))). Поиск минимума равносилен максимуму положительного знаменателя. Оба знака каждой координаты независимы, точки на осях исключены.',
            'minimum',readout='reciprocal')
    if found:=matches('open isosceles trapezoidal water channel, water depth '+name+', wet cross-section '+name+', bank inclination '+name):
        h,S,phi=found.groups()
        cap=f'{S}/{h}^2'
        return model('Минимизировать смоченный периметр и найти наклон боков.',[h,S],[h+'>0',S+'>0'],f'[0,{cap})',
            ('linear_plus_hypotenuse','2','1',cap,False),h,{'bottom_width':f'{S}/{h}-{h}*@','cotangent_of_bank_angle':'@'},
            'Если t есть горизонтальный откос на единицу глубины, боковые стороны имеют длину h√(1+t²), а основание при заданной площади равно S/h−ht. Оно должно быть положительным. При t<0 обе боковые стороны длиннее вертикальных, а основание шире, чем при t=0. Положительные достаточно малые t уменьшают периметр относительно t=0.', 'minimum',
            offset=f'{S}/{h}')
    if found:=matches('isosceles trapezoid ABCD, AD parallel BC, AD=2'+name+', acute angle BAD='+name+r'; sinuosity = perimeter/circumference of circle of same area'):
        a,angle=found.groups()
        cs=f'cos({angle})';tg=f'tan({angle})'
        return model('Найти форму с наименьшей извилистостью.',[a,angle],[a+'>0','0<'+angle+'<pi/2'],'(0,1)',
            ('affine_squared_over_product','2',f'1/{cs}-1','2'),f'1/(pi*{tg})',
            {'shorter_base':f'2*{a}*(1-@)','height':f'{a}*@*{tg}','leg':f'{a}*@/{cs}'},
            'При горизонтальной проекции боковой стороны at высота равна at tan α, верхнее основание равно 2a(1−t), площадь равна a² tan α·t(2−t). Квадрат отношения периметра к длине окружности той же площади имеет профиль (2+(sec α−1)t)²/[t(2−t)]. Острый угол даёт sec α−1>0, поэтому критическая доля 2/(1+sec α) строго между 0 и 1.',
            'minimum',readout='sqrt')
    if found:=matches('plant A at perpendicular distance '+name+' from N-S rail, city B on rail '+name+r' north of plant\. Cost per ton-km '+name+r' on branch, '+name+r' on main rail \(\3>\4\)'):
        a,b,p,qc=found.groups()
        return model('Определить угол phi подъездного пути A к железной дороге для минимальной стоимости перевозки A→B.',
            [a,b,p,qc],[f'{a}>0',f'{b}>0',f'0<{qc}<{p}'],f'[0,{b}/{a}]',
            ('linear_plus_hypotenuse',p,qc,f'{b}/{a}',True),a,{'cosine_of_angle':f'@/sqrt(1+@^2)','rail_offset':a+'*@'},
            'Конец ветки на железной дороге можно выбирать между основанием перпендикуляра и городом. За этим отрезком проекция на ближайший конец не увеличивает ни одно из двух расстояний и уменьшает одно из них. Если отступ от перпендикуляра равен at, стоимость равна ap√(1+t²)+q(b−at). Угол острый или прямой, его однозначно задаёт приведённый косинус.',
            'minimum',offset=f'{qc}*{b}')
    if found:=matches('sources at A,B with strengths '+name+','+name+' candela; AB='+name):
        A,B,L=found.groups()
        return model('Найти наименее освещенную точку отрезка.',[A,B,L],[z+'>0' for z in (A,B,L)],'(0,1)',
            ('reciprocal_pair',A,B,2),f'1/{L}^2',{'distance_from_A':L+'*@','distance_from_B':L+'*(1-@)'},
            'Освещённости складываются и пропорциональны силе источника, делённой на квадрат расстояния. На открытом отрезке t=AM/AB. Сингулярные положения в источниках не могут давать меньшую конечную освещённость.', 'minimum')
    if found:=matches(r'round table of radius '+name+r', lamp vertically above center\. I=I0\*sin\(phi\)/r², phi ray elevation above table'):
        a=found[1]
        return model('Найти высоту наибольшей освещенности края.',[a,'I0'],[a+'>0','I0>0'],'(0,1)',
            ('unit_product',F(1,2),1),f'I0/{a}^2',{'lamp_height':a+'*sqrt(@/(1-@))'},
            'Расстояние от лампы до края равно √(a²+h²), синус наклона луча равен h/√(a²+h²). Квадрат синуса t лежит в (0,1) и взаимно однозначно связан с положительной высотой.', 'maximum')
    if found:=matches('river width '+name+', channel of width '+name+' perpendicular to river'):
        a,b=found.groups()
        return model('Какой максимальной длины суда могут пройти поворот?',[a,b],[a+'>0',b+'>0'],'(0,1)',
            ('reciprocal_pair',a,b,F(1,2)),'1',{'sine_of_turn_angle':'sqrt(@)'},
            'Для каждого острого угла поворота максимально разрешённая длина тонкого продольного отрезка равна сумме частей между внутренним углом и внешними берегами, a/sin θ и b/cos θ. Такой отрезок помещается при каждом угле тогда и только тогда, когда его длина не превышает минимума этой суммы. Положительная ширина корпуса вводит дополнительное ограничение, для которого исходных данных нет. Параметр t=sin² θ.', 'maximum_transit_length')
    if found:=matches('daily ship costs '+name+' fixed plus a component proportional to the cube of speed'):
        a=found[1];b='c' if a!='c' else 'k'
        root=f'cbrt({a}/{b})'
        return model('Найти наиболее экономичную скорость v.',[a,b],[a+'>0',b+'>0'],'(0,+inf)',
            ('opposite_powers',1,2,1,1,False),f'{b}*{root}^2',{'speed':root+'*@'},
            'Для фиксированного пути суточные затраты делятся на суточный пробег v. Стоимость на единицу пути равна a/v+cv² при положительном коэффициенте c. Нормируем скорость на кубический корень из a/c.', 'minimum')
    if found:=matches('weight on horizontal rough plane, coefficient of friction '+name):
        k=found[1];W='W' if k!='W' else 'G'
        return model('Под каким углом к горизонту приложить минимальную силу, достаточную, чтобы сдвинуть груз?',
            [k,W],[k+'>0',W+'>0'],'[0,1]',('square_root_sum',k,'1'),f'{k}*{W}',
            {'tangent_of_angle':'sqrt(@/(1-@))'},
            'При весе W и угле φ к горизонтали нормальная реакция равна W−F sin φ. Порог равенства горизонтальной составляющей и предельной силы трения даёт F=kW/(cos φ+k sin φ). Наклон вниз или против направления движения не улучшает порог. При найденном остром угле реакция положительна. Чистый подъём требует силы W, между тем максимум знаменателя равен √(1+k²)>k.',
            'minimum',readout='reciprocal')
    raise Unsupported('No justified geometric reduction for this complete condition')


def natural_domain(t,lib,request):
    """Intersect all raw definedness constraints on a complete partition of the real line."""
    spec=t['goal']
    kind=t.get('kind',t.get('task_type'));restricted=kind=='restricted_real_function_domain'
    if (not lib.data.get('finite_real_domains') or set(t)-SET_TASK_FIELDS or t.get('assumptions') or
        kind not in ('real_function_domain','restricted_real_function_domain') or
        set(spec)-{'variable','variable_space','expression','goal'}-({'ambient_domain'} if restricted else set()) or
        spec.get('variable_space','real_numbers')!='real_numbers' or
        spec.get('goal') not in (('maximal real domain within the printed restriction',) if restricted else ('maximal real domain','natural real domain'))):
        raise Unsupported('A different source domain or additional requested outputs remain')
    var=spec['variable'];ctx=m.context({'variable':var});text=spec['expression']
    names={'log','lg',*re.findall(r'\b(log_[1-9][0-9]*)\s*\(',text)}
    extended=lib.data.get('elementary_domain_preimages')
    raw=m.parse(text,var,extra_functions=names|({'factorial','root4'} if extended else set()));guards=domain_conditions(raw)
    def visit(e):
        tag=e[0]
        if tag=='factorial':guards.append(('nonnegative_integer',e[1]))
        if tag=='root4':guards.append(('nonnegative',e[1]))
        if tag in names:
            if tag.startswith('log_') and int(tag[4:])<=1:raise Unsupported('A logarithm needs a valid fixed base')
            guards.append(('positive',e[1]))
        if tag=='rpow':
            base=m.substitute(e[1],{('v',var):('s',var)})
            fixed={**ctx,'parameters':[var]}
            if not m.constant_defined(base,fixed) or m.sign(base,fixed)!=1:
                raise Unsupported('A real power needs a full classification of its base and exponent')
        for c in e[1:]:
            if isinstance(c,tuple):visit(c)
    visit(raw)
    if not restricted and all(r!='nonnegative_integer' for r,_ in guards):
        try:return domain_partition(var,guards,names,lib.data.get('endpoint_change_of_variable'))
        except (poly.NotRational,Unsupported,line.Unsupported):
            if not extended:raise
    if not extended:raise Unsupported('A periodic or discrete domain requires a set-preimage argument')
    from plane_domains import domain_preimages
    def standard(e):
        tag=e[0]
        if tag=='lg' or tag.startswith('log_'):
            base=10 if tag=='lg' else int(tag[4:])
            return ('div',('ln',standard(e[1])),('ln',q(base)))
        if tag=='v':return ('s',var)
        return (tag,*(standard(a) if isinstance(a,tuple) else a for a in e[1:]))
    value=domain_preimages([(r,standard(e)) for r,e in guards],[var],elementary=True)
    if restricted:
        a,b,lc,rc=interval_terms(spec.get('ambient_domain',''),ctx)
        value['ambient_interval']=(a,b,lc,rc)
        intervals=clipped_periods(value)
        if intervals is not None:value['intervals_pi']=intervals
    return {'method':'sign_preimages','raw_conditions':guards},value


def clipped_periods(region):
    """Intersect affine periodic bands on a bounded interval, in exact units of pi."""
    from math import ceil,floor
    a,b,lc,rc=region['ambient_interval'];var=('s',region['variables'][0])
    if isinstance(a,str) or isinstance(b,str):return None
    a,b=m.pi_multiple(a),m.pi_multiple(b)
    if a is None or b is None:return None
    cuts={a,b};bands=[]
    for cell in region['intersection']:
        if cell.get('shape')!='intervals':return None
        phase=cell['phase'];offset=m.substitute(phase,{var:q(0)})
        p,d=m.rational_form(m.add(phase,m.neg(offset)));slope=p.get(((var,1),))
        shift=m.pi_multiple(offset)
        if d!={():F(1)} or len(p)!=1 or not slope or shift is None:return None
        origin=m.num(cell['origin_pi'])-shift;period=cell['period_pi'];width=cell['width_pi']
        bands.append((slope,origin,period,width,cell['closed']))
        for end in (origin,origin+width):
            lo,hi=sorted(((slope*a-end)/period,(slope*b-end)/period))
            if floor(hi)-ceil(lo)>line.MAX_POLYNOMIALS:return None
            cuts.update((end+k*period)/slope for k in range(ceil(lo),floor(hi)+1))
    def includes(x):
        return ((x!=a or lc) and (x!=b or rc) and
                all((0<z<width or closed and z in (0,width)) for s,o,p,width,closed in bands for z in [(s*x-o)%p]))
    points=sorted(cuts)
    atoms=line.make_union([line.Quadratic(x) for x in points],
                          [False,*[includes((u+v)/2) for u,v in zip(points,points[1:])],False],
                          [includes(x) for x in points])[1]
    return [(q(line.read_endpoint(u).a),q(line.read_endpoint(v).a),left,right) for u,v,left,right in atoms]


def domain_partition(var,guards,names=(),simplify_guards=False):
    """Keep all raw definedness predicates before reducing any individual sign test."""
    guards=tuple(dict.fromkeys(guards));ctx=m.context({'variable':var})
    def polynomials(relation,e,threshold=0):
        tag=e[0]
        if tag in names or tag=='ln':
            if tag=='ln' and not threshold or tag=='log' and relation=='nonzero' and not threshold:return polynomials(relation,e[1],1)
            if tag=='lg' or tag.startswith('log_'):
                base=10 if tag=='lg' else int(tag[4:])
                if threshold*base.bit_length()<=line.MAX_BITS:
                    return polynomials(relation,e[1],base**threshold)
        if tag=='exp' and not threshold:return O,O
        if not threshold and tag in ('abs','sqrt','cbrt'):
            if tag in ('abs','sqrt') and relation=='nonnegative':return O,O
            if tag=='abs' and relation=='positive':return poly.rf(('pow',e[1],2),var)
            return polynomials(relation,e[1])
        shifted=('add',e,q(-threshold))
        if m.constant_defined(shifted,ctx):
            sign=m.sign(shifted,ctx)
            if sign in (-1,0,1):return (F(sign),),O
        try:return poly.rf(shifted,var)
        except poly.NotRational:
            if not simplify_guards:raise
            return poly.rf(m.simplify(shifted),var)
    def factors(relation,e):
        if relation=='nonzero' and e[0] in ('mul','div'):
            yield from factors(relation,e[1]);yield from factors(relation,e[2])
        elif relation=='nonzero' and e[0] in ('sqrt','cbrt','abs','pow'):
            yield from factors(relation,e[1])
        elif relation=='nonzero' and e[0]=='rpow':
            yield 'positive',e[1]
        else:yield relation,e
    constraints=[(r,*polynomials(r,part)) for relation,e in guards for r,part in factors(relation,e)]
    cuts=ordered_cuts(x for _,p,d in constraints for part in (p,d) for x in rational_roots(part))
    def contains(x):
        for relation,p,d in constraints:
            denominator=line.peval(d,x).sign()
            if not denominator:return False
            s=line.peval(p,x).sign()*denominator
            if not {'positive':s>0,'nonnegative':s>=0,'nonzero':s!=0}[relation]:return False
        return True
    edges=['-inf',*cuts,'+inf'];samples=[line.between(a,b) for a,b in zip(edges,edges[1:])]
    cells=[contains(line.Quadratic(s)) for s in samples];points=[contains(x) for x in cuts]
    value=line.make_union(cuts,cells,points);line.validate_real_set(value)
    return {'raw_conditions':guards,'cuts':tuple(map(line.quadratic_term,cuts)),'samples':tuple(map(q,samples)),
            'open_cells':tuple(cells),'point_membership':tuple(points)},value


def endpoint_change_of_variable(v,a,b,f,request):
    """Integrate c*u^n/d on a component where the continuous product u' d is constant."""
    from integrals import inner_derivative_task
    from tasks import source
    A,B=m.num(m.simplify(a)),m.num(m.simplify(b))
    if A is None or B is None or A==B or f[0]!='div':return None
    x=('v',v);raw=m.substitute(f,{('s',v):x});numerator=m.simplify(raw[1]);d=raw[2]
    c=q(1)
    if numerator[0]=='mul' and numerator[1][0]=='q':c,numerator=numerator[1:]
    u,n=numerator[1:] if numerator[0]=='pow' else (numerator,1)
    if n<1 or not m.variable_in(u,v):return None
    child=request('derivative of the inner variable',inner_derivative_task({'variable':v},source(u)),
                  ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'))
    du=freeze(child['value'])
    # The ordinary derivative table is valid under the displayed smoothness guards.
    if child['child_result']['schema']!='original-table-derivative/v1':
        raise Unsupported('Derivative scope requires a checked pointwise table')
    guards=domain_conditions(raw)+list(freeze(child['compilation']['sufficient_formula_domain']))+domain_conditions(du)
    try:partition,domain=domain_partition(v,guards,simplify_guards=True)
    except (poly.NotRational,poly.Undefined) as exc:raise Unsupported('Open-interval guard partition is unproved') from exc
    low,high=sorted((A,B));lo,hi=line.Quadratic(low),line.Quadratic(high)
    if not any(line.compare(line.read_endpoint(left),lo)<=0 and line.compare(hi,line.read_endpoint(right))<=0
               for left,right,_,_ in domain[1]):
        raise Unsupported('One component must contain the entire open integration interval')
    product=m.mul(du,d);square=m.num(m.power(product,2))
    if square is None or square<=0:raise Unsupported('Squared change-of-variable factor is not a positive constant')
    # A nonvanishing continuous real function on an interval keeps its sign.
    sample=q((A+B)/2);at=m.substitute(product,{x:sample});ctx=m.context({'variable':v})
    sign=m.sign(at,ctx) if m.constant_defined(at,ctx) else None
    if sign not in (-1,1):raise Unsupported('Sign of the Jacobian factor is unproved')
    scale=m.mul(q(sign),('sqrt',q(square)))
    primitive=m.div(m.mul(c,m.power(u,n+1)),m.mul(scale,q(n+1)))
    limits=[];sides=('right','left') if A<B else ('left','right')
    for point,side in zip((a,b),sides):
        task={'kind':'limit','expression':source(primitive),'variable':v,'approach':{'point':source(point),'side':side}}
        value=freeze(request('primitive limit from the '+side,task)['value'])
        if not isinstance(value,tuple) or not m.constant_defined(value,ctx):
            raise Unsupported('An endpoint primitive limit is not finite')
        limits.append(value)
    total=m.add(limits[1],m.neg(limits[0]))
    return dict(method='endpoint_change_of_variable',variable=v,bounds=(a,b),difference=total,integrand=f,
                u=u,du=du,power=n,primitive=primitive,endpoint_values=limits,one_sided_limits=sides,
                scale_on_interval=scale,scale_squared=q(square),sign_witness=(sample,at),
                source_domain=domain,guard_partition=partition),total


def proposed_substitution_branches(v,t,a,b,lhs,rhs,request):
    """Prove inverse charts on oriented open cells of a supplied substitution."""
    from integrals import affine,inner_derivative_task
    from quadrature import enclose,pi_range,product
    from tasks import known_guard,source
    from verify import same_value
    x,y=('v',v),('v',t);ctx=m.context({'variable':v})
    def minus(p,r):return m.add(p,m.neg(r))
    def scalar_sign(z):
        z=m.simplify(z);sign=m.sign(z,ctx)
        if sign is not None:return sign
        lo,hi=enclose(z,None)
        if lo>0:return 1
        if hi<0:return -1
        raise Unsupported('Cannot certify the sign of a branch boundary')
    def band(angle):
        # atan(t)+k*pi has range ((k-1/2)*pi,(k+1/2)*pi).
        multiple=m.pi_multiple(m.simplify(angle));half=F(1,2)
        if multiple is not None:return (multiple+half).__floor__()
        lo,hi=pi_range()
        lo,hi=product(enclose(angle,None),(1/hi,1/lo))
        k=(lo+half).__floor__()
        if k!=(hi+half).__floor__():raise Unsupported('Unresolved tangent phase interval')
        return k
    if lhs in (x,y):left,raw=lhs,rhs
    elif rhs in (x,y):left,raw=rhs,lhs
    else:raise Unsupported('The substitution must specify a variable as a function')
    direct=left==y
    supplied=v if direct else t
    if not m.variable_in(raw,supplied) or m.variable_in(raw,t if direct else v):
        raise Unsupported('The two substitution variables must be independent coordinates')
    orientation=scalar_sign(minus(b,a))
    if not orientation:raise Unsupported('A nondegenerate source interval is required')
    possible=[];details={}
    forward=raw
    fold=raw[0]=='abs' or raw[0]=='pow' and raw[2]==2
    cube_fold=raw[0]=='cbrt' and raw[1][0]=='pow' and raw[1][2]==2
    if raw[0]=='tan' or fold or cube_fold:
        if not direct:raise Unsupported('An inverse selection is required for this supplied relation')
        inner=raw[1][1] if cube_fold or fold and raw[1][0]=='cbrt' and raw[0]=='pow' else raw[1]
        if any(not known_guard(g,ctx) for g in domain_conditions(inner)):raise Unsupported('Unproved domain of the affine coordinate')
        slope,shift=affine(inner,v)
        slope_sign=scalar_sign(slope)
        if not slope_sign:raise Unsupported('The affine coordinate is constant')
        def linear_inverse(z):return m.div(minus(z,shift),slope)
        def phase(z):return m.substitute(inner,{x:z})
        if raw[0]=='tan':
            method='periodic_tangent';details['phase']=inner
            first,last=sorted((band(phase(a)),band(phase(b))))
            if last-first>line.MAX_BRANCHES:raise Unsupported('Tangent partition exceeds supported branch count')
            possible=[(linear_inverse(m.mul(q(F(2*k+1,2)),m.PI)),'pole') for k in range(first-1,last+1)]
            def inverse_at(sample):
                k=band(phase(sample))
                return (linear_inverse(m.add(('atan',y),m.mul(q(k),m.PI))),
                        m.div(q(1),m.mul(slope,m.add(q(1),m.power(y,2)))),slope_sign,{'phase_index':k})
        else:
            method='folded_power';possible=[(linear_inverse(q(0)),'turning_point')]
            cube_fold=cube_fold or raw[0]=='pow' and raw[1][0]=='cbrt'
            if raw[0]=='abs':base,base_jac=y,q(1)
            elif cube_fold:base,base_jac=m.mul(y,('sqrt',y)),m.mul(q(F(3,2)),('sqrt',y))
            else:base,base_jac=('sqrt',y),m.div(q(F(1,2)),('sqrt',y))
            def inverse_at(sample):
                side=scalar_sign(phase(sample))
                return linear_inverse(m.mul(q(side),base)),m.div(m.mul(q(side),base_jac),slope),side*slope_sign,{'affine_sign':side}
    else:
        try:p,d=poly.rf(raw,supplied)
        except (poly.NotRational,poly.Undefined) as exc:raise Unsupported('No justified inverse family for the proposed map') from exc
        if max(len(p),len(d))>2:raise Unsupported('A different inverse of the rational map is required')
        def coefficients(p):return (p[1] if len(p)>1 else F(0)),p[0]
        A,B=coefficients(p);C,D=coefficients(d);det=A*D-B*C
        if not det:raise Unsupported('A constant fractional linear map has no inverse')
        if any(c['type']=='hole' for c in graph_curve(raw,supplied)['cuts']):
            raise Unsupported('The supplied fractional map contains an additional original hole')
        if not direct:A,B,C,D=D,-B,-C,A
        def linear(p,z,r):return m.add(m.mul(q(p),z),q(r))
        forward=raw if direct else m.div(linear(A,x,B),linear(C,x,D))
        denom=linear(-C,y,A)
        inverse=raw if not direct else m.div(linear(D,y,-B),denom)
        jac=m.div(q(det),m.power(denom,2));method='fractional_linear'
        if C:possible=[(q(-D/C),'pole')]
        def inverse_at(sample):return inverse,jac,line.sign(det),{}
    cuts=[];endpoint_poles=[]
    for point,kind in possible:
        d1=orientation*scalar_sign(minus(point,a));d2=orientation*scalar_sign(minus(b,point))
        if d1>0 and d2>0:cuts.append((point,kind))
        elif kind=='pole' and (d1==0 or d2==0):endpoint_poles.append(point)
    cuts.sort(key=cmp_to_key(lambda l,r:orientation*scalar_sign(minus(l[0],r[0]))))
    edges=[a,*(p for p,_ in cuts),b];branches=[]
    sides=('right','left') if orientation>0 else ('left','right')
    for i,(l,r) in enumerate(zip(edges,edges[1:]),1):
        inverse,jac,sign,witness=inverse_at(m.mul(q(F(1,2)),m.add(l,r)))
        derivative=request(f'inverse derivative on branch {i}',inner_derivative_task({'variable':t},source(inverse)),
                           ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'))
        if not same_value(freeze(derivative['value']),jac):raise Unsupported('The inverse Jacobian identity failed')
        images=[]
        for point,side in zip((l,r),sides):
            limit={'kind':'limit','variable':v,'expression':source(forward),'approach':{'point':source(point),'side':side}}
            images.append(freeze(request(f'branch {i} image from the {side}',limit)['value']))
        branches.append(dict(source_bounds=(l,r),source_sides=sides,image_bounds=tuple(images),monotonicity=sign,
                             inverse=inverse,inverse_jacobian=jac,**witness))
    return dict(method=method,forward=forward,cuts=cuts,endpoint_singularities=endpoint_poles,branches=branches,**details)


def interval_terms(notation,ctx):
    if notation in ('R','real line'):return '-inf','+inf',False,False
    match=re.fullmatch(r'(\[|\()\s*([^,]+),\s*([^,]+)\s*(\]|\))',notation)
    if not match:raise Unsupported('An interval or the entire real line is required')
    def endpoint(s):
        s=s.strip().replace('infinity','inf')
        if s=='inf':return '+inf'
        if s in ('-inf','+inf'):return s
        e=m.parse(s,None,ctx.get('parameters',()))
        if not m.constant_defined(e,ctx):raise Unsupported('Unproved interval endpoint')
        return m.simplify(e)
    a,b=map(endpoint,(match[2],match[3]));lc,rc=match[1]=='[',match[4]==']'
    if a=='+inf' or b=='-inf' or a=='-inf' and lc or b=='+inf' and rc:raise Unsupported('Invalid interval')
    if not isinstance(a,str) and not isinstance(b,str) and m.sign(m.add(b,m.neg(a)),ctx) not in (0,1):
        raise Unsupported('The order of the interval endpoints is unproved')
    return a,b,lc,rc


def rational_interval(notation):
    a,b,lc,rc=interval_terms(notation,{'parameters':[],'assumptions':[]})
    def endpoint(e):
        if isinstance(e,str):return e
        v=m.num(e)
        if v is None:raise Unsupported('Unproved rational interval endpoint')
        return line.Quadratic(v)
    return endpoint(a),endpoint(b),lc,rc


def function_image(t,lib,request):
    """Map each source-domain monotone cell and each included point; union the image atoms."""
    spec=t['goal'];var=spec['variable'];expr=spec['expression'];kind=t.get('kind',t.get('task_type'))
    combined=kind=='real_function_domain_and_range'
    keys={'variable','variable_space','expression','goals'} if combined else {'variable','expression','given_domain','domain_condition','goal'}
    if (not lib.data.get('monotone_cell_image') or set(t)-SET_TASK_FIELDS or t.get('assumptions') or set(spec)-keys or
        kind not in ('real_function_domain_and_range','restricted_function_image') or
        (combined and (spec.get('variable_space','real_numbers')!='real_numbers' or set(spec['goals'])!={'maximal real domain','exact image of that domain'})) or
        (not combined and spec.get('goal')!='exact image')):
        raise Unsupported('A different source or image is requested')
    sub={'kind':'real_function_domain','goal':{'variable':var,'expression':expr,'goal':'maximal real domain'}}
    domain=freeze(request('maximal domain of the original function',sub)['value'])
    if isinstance(domain,dict):raise Unsupported('The image of a periodic or discrete source set requires its monotone branches')
    def unpack_set(value):return [(line.read_endpoint(a),line.read_endpoint(b),lc,rc) for a,b,lc,rc in value[1]]
    def belongs(x,atoms):
        return any((line.compare(a,x)<0 or lc and not line.compare(a,x)) and
                   (line.compare(x,b)<0 or rc and not line.compare(x,b)) for a,b,lc,rc in atoms)
    def samples(cuts):
        ends=['-inf',*cuts,'+inf']
        return [line.Quadratic(line.between(a,b)) for a,b in zip(ends,ends[1:])]
    def make(cuts,test):
        return line.make_union(cuts,[test(x) for x in samples(cuts)],[test(x) for x in cuts])
    restrictions=[];notation=spec.get('given_domain','R')
    def restrict(left,relation,right):
        query={'kind':'real_inequality','variable':var,'left':left.strip(),'relation':relation,'right':right.strip()}
        restrictions.append(unpack_set(freeze(request('stated input-set inequality',query)['value'])))
    if 'domain_condition' in spec and spec['domain_condition'] not in ('R','real line'):
        guard=re.fullmatch(r'([^<>=!]+)(!=|<=|>=|<|>|=)([^<>=!]+)',spec['domain_condition'])
        if not guard:raise Unsupported('An explicit real domain comparison is required')
        restrict(*guard.groups())
    condition=re.fullmatch(r'\{\s*'+re.escape(var)+r'\s*:\s*([^<>=]+)\s*(<=|<)\s*([^<>=]+)\s*(<=|<)\s*([^<>=]+)\s*\}',notation)
    if condition:
        a,op,u,op2,b=condition.groups()
        restrict(a,op,u);restrict(u,op2,b)
    elif notation!='R':
        restrictions.append([rational_interval(notation)])
    inner=m.parse(expr,var,extra_functions={'lg'});maps=[];ctx=m.context({'variable':var})
    while True:
        try:poly.rf(inner,var);break
        except poly.NotRational:pass
        tag=inner[0]
        if tag=='rpow' and not m.variable_in(inner[1]) and m.constant_defined(inner[1],ctx):
            base=m.num(m.simplify(inner[1]))
            if base is None or base<=0:raise Unsupported('A fixed positive exponential base is required')
            if base==1:inner=q(1);continue
            maps.append(('fixed_exponential',q(base)));inner=inner[2];continue
        if tag in ('abs','sqrt','cbrt','lg','ln','exp','asin','acos','atan','acot'):
            maps.append((tag,None));inner=inner[1];continue
        if tag not in ('add','mul','div'):raise Unsupported('No supported monotone transformation of rational cells')
        left,right=inner[1:];child,c=(right,left) if tag!='div' and not m.variable_in(left) else (left,right)
        if m.variable_in(c) or not m.constant_defined(c,ctx):raise Unsupported('Unproved constant map on image intervals')
        if tag=='div':
            if not m.nonzero(c,ctx):raise Unsupported('Unproved nonzero scale')
            c=m.div(q(1),c)
        if tag=='mul' and m.simplify(c)==m.ZERO:
            # The domain of the unsimplified expression was proved before reducing the map.
            maps.append(('scale',m.ZERO));inner=m.ZERO;break
        if tag!='add' and m.sign(c,ctx) not in (-1,1):raise Unsupported('Unproved orientation of scale')
        maps.append(('translate' if tag=='add' else 'scale',c));inner=child
    maps.reverse()
    curve=graph_curve(inner,var);p,d=[tuple(m.num(freeze(q)) for q in curve[k]) for k in ('numerator','denominator')]
    restrictions.append(unpack_set(domain))
    cuts=ordered_cuts([line.read_quadratic_term(k['x']) for k in curve['cuts']]+[y for group in restrictions for a,b,_,_ in group for y in (a,b)])
    contains=lambda x:all(belongs(x,group) for group in restrictions)
    edges=['-inf',*cuts,'+inf'];atoms=[]
    for i,s in enumerate(samples(cuts)):
        if not contains(s):continue
        f=ordinate(p,d,s)
        def limit_at(x):
            if isinstance(x,str):
                tail=curve['tail_limits'][int(x=='+inf')]
                return tail if isinstance(tail,str) else line.Quadratic(m.num(tail))
            if not line.peval(d,x).sign():return '+inf' if f.sign()>0 else '-inf'
            return ordinate(p,d,x)
        a,b=map(limit_at,edges[i:i+2]);order=line.compare(a,b)
        atoms.append((a,b,True,True) if not order else (a,b,False,False) if order<0 else (b,a,False,False))
    for x in cuts:
        if contains(x):
            y=ordinate(p,d,x);atoms.append((y,y,True,True))
    def union(pieces):return make(ordered_cuts(y for a,b,_,_ in pieces for y in (a,b)),lambda x:belongs(x,pieces))
    rational_image=union(atoms);ranges=unpack_set(rational_image)
    if maps and maps[0][0]=='abs':
        def neg(y):return ('+inf' if y=='-inf' else '-inf') if isinstance(y,str) else y.neg()
        folded=[];zero=line.Quadratic(0)
        for a,b,lc,rc in ranges:
            if line.compare(b,zero)<=0:folded.append((neg(b),neg(a),rc,lc))
            elif line.compare(a,zero)>=0:folded.append((a,b,lc,rc))
            else:
                k=line.compare(neg(a),b)
                folded.append((zero,neg(a) if k>0 else b,True,lc and k>=0 or rc and k<=0))
        ranges=unpack_set(union(folded))
    def term(y):
        if isinstance(y,str):return y
        return q(y.a) if not y.b else m.add(q(y.a),m.mul(q(y.b),('sqrt',q(y.d))))
    mapped=[(term(a),term(b),lc,rc) for a,b,lc,rc in ranges]
    for index,(tag,c) in enumerate(maps):
        if tag=='abs':
            if index and not all(not isinstance(a,str) and m.sign(a,ctx) in (0,1) for a,_,_,_ in mapped):
                raise Unsupported('An interior absolute-value fold needs its own sign partition')
            continue
        decreasing=tag in ('acos','acot') or tag=='scale' and m.sign(c,ctx)==-1 or tag=='fixed_exponential' and m.num(c)<1
        def mapping(x):
            if isinstance(x,str):
                if tag=='fixed_exponential':return q(0) if (x=='+inf')==decreasing else '+inf'
                if tag=='atan':return m.mul(q(F(-1 if x=='-inf' else 1,2)),m.PI)
                if tag=='acot':return m.PI if x=='-inf' else q(0)
                if tag=='exp' and x=='-inf':return q(0)
                if tag in ('acos','asin') or tag in ('sqrt','ln','lg') and x=='-inf':raise Unsupported('Image escapes the real domain')
                return ('+inf' if x=='-inf' else '-inf') if decreasing else x
            if tag=='translate':return m.add(x,c)
            if tag=='fixed_exponential':return m.simplify(('rpow',c,x))
            if tag=='scale':return m.mul(x,c)
            if tag in ('lg','ln') and m.simplify(x)==q(0):return '-inf'
            if tag=='lg':
                n=m.num(x)
                if n is not None and n>0:
                    num,den=n.numerator,n.denominator;power=0
                    while num%10==0:num//=10;power+=1
                    while den%10==0:den//=10;power-=1
                    if num==den==1:return q(power)
                return m.simplify(m.div(('ln',x),('ln',q(10))))
            return m.simplify((tag,x))
        mapped=[(mapping(a),mapping(b),lc,rc) for a,b,lc,rc in mapped]
        if decreasing:mapped=[(b,a,rc,lc) for a,b,lc,rc in reversed(mapped)]
    input_domain=make(cuts,contains)
    return {'maps':maps,'rational_chart':curve,'input_domain':input_domain,'inner_image':rational_image}, {
            'domain':input_domain,'image_intervals':tuple(mapped)}


def function_bounds(task,lib,request):
    fields={'kind','id','source','function','variable','given_domain','domain_condition','requested_output','parameters','stated_conditions'}
    if 'goal' in task:
        spec=task['goal'];kind=task.get('kind',task.get('task_type'))
        if (set(task)-SET_TASK_FIELDS-{'pending_obligations'} or task.get('assumptions') or
                ('domain' in spec)==('ambient_interval' in spec)):
            raise Unsupported('Additional source conditions or an ambiguous interval')
        if kind=='function_infimum_supremum' and set(spec.get('goals',()))=={'infimum','supremum'}:
            requested=spec['goals'];label='goals'
        elif kind=='function_oscillation' and spec.get('goal') in ('supremum minus infimum','supremum minus infimum on the original domain within this interval'):
            requested=['oscillation'];label='goal'
        else:raise Unsupported('Unrecognized original request for bounds')
        if set(spec)-{label,'expression','variable','domain','ambient_interval','original_domain'}:raise Unsupported('Extra source objective')
        task={'kind':'function_bounds','function':spec['expression'],'variable':spec.get('variable','x'),
              'given_domain':spec.get('domain',spec.get('ambient_interval')),'requested_output':requested}
        if 'original_domain' in spec:task['domain_condition']=spec['original_domain']
    wanted=task.get('requested_output')
    if (lib.data.get('task_compilers',{}).get('function_bounds')!='attained_image_endpoints' or
        set(task)-fields or task.get('parameters') or task.get('stated_conditions') or
        not isinstance(wanted,(tuple,list)) or not wanted or len(set(wanted))!=len(wanted) or
        set(wanted)-{'infimum','supremum','minimum','maximum','oscillation'}):
        raise Unsupported('Additional bound, parameter or attainment obligations remain')
    goal={'expression':task['function'],'variable':task['variable'],'given_domain':task['given_domain'],'goal':'exact image'}
    if 'domain_condition' in task:goal['domain_condition']=task['domain_condition']
    image=request('full image on the original restricted domain',{'kind':'restricted_function_image','goal':goal})['value']
    intervals=image['image_intervals']
    if not intervals:raise Unsupported('Bounds on an empty source set require a specified convention')
    values={}
    for key in wanted:
        if key=='oscillation':
            low,high=intervals[0][0],intervals[-1][1]
            width='+inf' if isinstance(low,str) or isinstance(high,str) else m.simplify(m.add(freeze(high),m.neg(freeze(low))))
            values[key]={'value':width,'exists':True,'attained':intervals[0][2] and intervals[-1][3]}
            continue
        if key in ('infimum','minimum'):endpoint,attained=intervals[0][0],intervals[0][2]
        else:endpoint,attained=intervals[-1][1],intervals[-1][3]
        exists=key in ('infimum','supremum') or attained
        values[key]={'value':endpoint if exists else None,'exists':exists,'attained':attained}
    return {'image_intervals':intervals},values


def graph_analysis(t,library):
    metadata={'id','source_number','source_exercise_number','source_subpart','source_edition','source_pdf_pages','schema','source',
              'task_type','kind','source_statement','goal','assumptions','transcription_notes','program_status','pending_obligations'}
    if not library.data.get('rational_graphs') or set(t)-metadata or t.get('kind',t.get('task_type'))!='construct_graph' or t.get('assumptions',[]):
        raise Unsupported('Unknown graph source, constraints or method')
    spec=t['goal'];v=spec['variable'];m.context({'variable':v})
    if set(spec)-{'variable','expression','parameter','parameter_values','goal'}:raise Unsupported('Extra graph obligation')
    family='parameter' in spec
    description=spec.get('goal')
    form=(r'(?:construct|draw|plot) (?:every|all) (?:listed|requested|specified) graphs?' if family else
          r'(?:construct|draw|plot) (?:a|the) (?:(?:full|complete|requested|rational|function) )*graph(?: (?:on|over) (?:its|the) (?:(?:original|real|natural|full) )*domain)?')
    if family!=('parameter_values' in spec) or description is not None and (not isinstance(description,str) or not re.fullmatch(form,' '.join(description.lower().split()).rstrip('.'))):
        raise Unsupported('Specific graph construction or parameters not represented')
    params=[spec['parameter']] if family else [];m.context({'variable':v,'parameters':params})
    values=spec['parameter_values'] if family else [None]
    if not isinstance(values,(tuple,list)) or not values:raise Unsupported('Finite explicit parameter list required')
    expr=m.parse(spec['expression'],v,params);curves=[]
    for value in values:
        raw=expr
        if family:
            original=m.parse(value,None)
            if not m.constant_defined(original,m.context({'variable':v})):raise Unsupported('Undefined parameter value')
            if m.num(m.simplify(original)) is None:raise Unsupported('Rational parameter values required')
            raw=m.substitute(raw,{('s',params[0]):original})
        curves.append(dict(parameter_value=value,**graph_curve(raw,v)))
    return curves


def svg_canvas(width,height):
    return ET.Element('svg',{'xmlns':'http://www.w3.org/2000/svg','width':str(width),'height':str(height),'viewBox':f'0 0 {width} {height}'})


def svg_element(parent,tag,**kw):
    return ET.SubElement(parent,tag,{k.replace('_','-'):str(v) for k,v in kw.items()})


def svg_label(parent,x,y,s,**options):
    e=svg_element(parent,'text',x=f'{x:.2f}',y=f'{y:.2f}',font_family='sans-serif',font_size=12,fill='#273344',**options);e.text=s


def svg_text(root):
    return ET.tostring(root,encoding='unicode',short_empty_elements=True)+'\n'


def svg_payload(svg):
    return {'drawing_svg':svg,'drawing_sha256':sha256(svg.encode()).hexdigest()}


def drawing(t,curves):
    """One polyline per proved monotone cell, sampled at every visible pixel column."""
    def middle(a):
        lo,hi=line.read_quadratic_term(freeze(a)).bounds(80)
        return (lo+hi)/2
    def poly_values(values):return tuple(m.num(freeze(z)) for z in values)
    cuts=[c for curve in curves for c in curve['cuts']]
    xs=[F(-2),F(2)]+[middle(c['x']) for c in cuts]
    xmin=min(xs);xmax=max(xs);span=xmax-xmin;xmin-=span/5;xmax+=span/5
    W,H,L=696,362,57
    grid=[xmin+(xmax-xmin)*i/W for i in range(W+1)]
    coefficients=[(poly_values(c['numerator']),poly_values(c['denominator'])) for c in curves]
    def value(p,d,x):return peval(p,x)/peval(d,x)
    ys=[value(p,d,x) for p,d in coefficients for x in grid if peval(d,x)]
    ys.sort();skip=len(ys)//25 if any(c['type']=='pole' for c in cuts) else 0
    anchors=[F(-1),F(1),ys[skip],ys[-1-skip]]+[middle(c['y']) for c in cuts if c['y']]
    ymin=min(anchors);ymax=max(anchors);span=ymax-ymin;ymin-=span/8;ymax+=span/8
    top=48+(16*((len(curves)+3)//4) if len(curves)>1 else 0)
    sx=lambda x:float(L+W*(x-xmin)/(xmax-xmin))
    sy=lambda y:float(top+H*(ymax-max(ymin-span,min(ymax+span,y)))/(ymax-ymin))
    root=svg_canvas(780,top+H+49);elem=svg_element;label=svg_label
    elem(root,'rect',width='100%',height='100%',fill='white')
    spec=t['goal'];label(root,L,23,'y = '+spec['expression'])
    clip=elem(elem(root,'defs'),'clipPath',id='plot');elem(clip,'rect',x=L,y=top,width=W,height=H)
    plot=elem(root,'g',clip_path='url(#plot)')
    def visible(x,y,z,w):
        if y==w:return (x,y,z,w) if top<=y<=top+H else None
        a,b=sorted(((top-y)/(w-y),(top+H-y)/(w-y)));a=max(0,a);b=min(1,b)
        if a<=b:return x+(z-x)*a,y+(w-y)*a,x+(z-x)*b,y+(w-y)*b
    def stroke(parent,x1,y1,x2,y2,color,**options):
        if parent is not root:
            clipped=visible(x1,y1,x2,y2)
            if clipped is None:return
            x1,y1,x2,y2=clipped
        elem(parent,'line',x1=f'{x1:.2f}',x2=f'{x2:.2f}',y1=f'{y1:.2f}',y2=f'{y2:.2f}',stroke=color,**options)
    def ticks(lo,hi):
        raw=(hi-lo)/7;scale=F(10)**(len(str(raw.numerator))-len(str(raw.denominator)))
        if scale>raw:scale/=10
        step=next(k*scale for k in (1,2,5,10) if k*scale>=raw)
        return (i*step for i in range((lo/step).__ceil__(),(hi/step).__floor__()+1))
    for x in ticks(xmin,xmax):
        stroke(plot,sx(x),top,sx(x),top+H,'#e1e6ed');label(root,sx(x),top+H+21,format(float(x),'.3g'),text_anchor='middle')
    for y in ticks(ymin,ymax):
        stroke(plot,L,sy(y),L+W,sy(y),'#e1e6ed')
        label(root,L-6,sy(y)+4,format(float(y),'.3g'),text_anchor='end')
    stroke(plot,L,sy(F(0)),L+W,sy(F(0)),'#506076');stroke(plot,sx(F(0)),top,sx(F(0)),top+H,'#506076')
    label(root,L+W,top+H+39,spec['variable'],text_anchor='end')
    colors=('#066eae','#b84a27','#21815b','#8b4e99','#8c6920','#c93d68')
    for ix,(curve,(p,d)) in enumerate(zip(curves,coefficients)):
        color=colors[ix%len(colors)];layer=elem(plot,'g',data_curve=ix)
        if len(curves)>1:
            xx=L+174*(ix%4);yy=42+16*(ix//4)
            stroke(root,xx,yy-4,xx+17,yy-4,color,stroke_width=2)
            label(root,xx+21,yy,spec['parameter']+' = '+str(curve['parameter_value']))
        if len(d)>1:
            trend=poly_values(curve['polynomial_part'])
            if len(trend)<=2:stroke(layer,L,sy(peval(trend,xmin)),L+W,sy(peval(trend,xmax)),'#8494a8',stroke_dasharray='5 5')
        cuts=curve['cuts'];locations=[xmin,*[middle(c['x']) for c in cuts],xmax]
        if any(sx(b)-sx(a)<1 for a,b in zip(locations,locations[1:])):raise Unsupported('Distinct landmarks cannot be resolved in this drawing')
        for j,branch in enumerate(curve['branches']):
            left,right=locations[j:j+2]
            lcut=line.read_endpoint(freeze(branch['left']));rcut=line.read_endpoint(freeze(branch['right']))
            def boundary(k,x):
                if k<0 or k>=len(cuts):return value(p,d,x)
                if cuts[k]['y'] is not None:return middle(cuts[k]['y'])
                return ymax+span if branch['sign']>0 else ymin-span
            points=[(left,boundary(j-1,left))]
            points.extend((x,value(p,d,x)) for x in grid if left<x<right
                          and line.compare(lcut,line.Quadratic(x))<0 and line.compare(line.Quadratic(x),rcut)<0)
            points.append((right,boundary(j,right)))
            screen=[(sx(x),sy(y)) for x,y in points];path=[]
            for a,b in zip(screen,screen[1:]):
                clip=visible(*a,*b)
                if clip:
                    start,end=clip[:2],clip[2:]
                    if not path or start!=path[-1]:path.append(start)
                    path.append(end)
            elem(layer,'polyline',data_branch=j,points=' '.join(f'{x:.2f},{y:.2f}' for x,y in path),
                 fill='none',stroke=color,stroke_width='1.7',stroke_linejoin='round')
        for c in cuts:
            x=sx(middle(c['x']))
            if c['type']=='pole':stroke(layer,x,top,x,top+H,'#af5250',stroke_dasharray='4 4',data_kind='pole')
            if c['type']=='hole':
                elem(layer,'circle',cx=f'{x:.2f}',cy=f'{sy(middle(c["y"])):.2f}',r=4,fill='white',stroke=color,stroke_width=2,data_kind='hole')
    return svg_text(root)


def graph_solution(t,library):
    curves=graph_analysis(t,library);svg=drawing(t,curves)
    return {'curves':curves,**svg_payload(svg)}


def solve_graph(t,library):
    start=perf_counter();r={'schema':'rational-graph-run/v1','task':t,'library_hash':library.hash,'operation_hash':version(),
        'status':'GRAPH_PENDING','value':None,'verification':{'status':'incomplete'}}
    try:
        r['value']=graph_solution(t,library);r['status']='SOLVED';r['verification']=verify_graph(r,library,t)
    except (Unsupported,line.Unsupported,poly.NotRational,poly.Undefined,poly.ResourceBound,ArithmeticError,TypeError,KeyError,ValueError) as exc:
        r.update(status='GRAPH_PENDING',value=None,reason=str(exc) or 'Nonrational graph or unresolved original domain')
    r['elapsed_seconds']=round(perf_counter()-start,6);return r


def verify_graph(r,library,expected_task):
    from verify import require,VerificationError
    require(set(r)<={'schema','task','library_hash','operation_hash','status','value','verification','elapsed_seconds'},'Unexpected graph claim')
    require(r['library_hash']==library.hash and r['operation_hash']==version() and r['status']=='SOLVED','Incomplete or changed graph basis')
    require(expected_task is None or canonical(r['task'])==canonical(expected_task),'Graph source changed')
    try:value=graph_solution(r['task'],library)
    except (Unsupported,line.Unsupported,poly.NotRational,poly.Undefined,poly.ResourceBound,ArithmeticError,TypeError,KeyError,ValueError) as exc:raise VerificationError(str(exc)) from exc
    require(canonical(r['value'])==canonical(value),'Graph domain, monotonicity, parameter family or figure changed')
    return {'status':'passed','checked_nodes':0,'checked_branches':sum(len(c['branches']) for c in value['curves']),
            'checked_drawings':1,'complete':True,'scope':'all real branches and a finite viewing window'}


def graph_report(result):
    def show(z):
        if isinstance(z,str):return z.replace('inf','∞')
        z=freeze(z)
        if z[0]=='q':return str(m.num(z))
        r=line.read_quadratic_term(z)
        return str(r.a) if not r.b else f'{r.a}+({r.b})√{r.d}'
    if result['schema']=='strict-extrema-run/v1':
        lines=['Строгие локальные экстремумы',str(result['task'].get('function','')),result['status']]
        if result.get('value'):
            cert=result['compilation']
            for b in cert['chart']['branches']:
                if not b.get('in_domain',True):continue
                motion={1:'возрастает',-1:'убывает',0:'постоянна'}[b[cert['sign_key']]]
                lines.append(f'На ({show(b["left"])}, {show(b["right"])}) функция {motion}.')
            for p in result['value']['extrema']:
                name='Максимум' if p['type']=='strict_maximum' else 'Минимум'
                lines.append(f"{name} ({m.render(freeze(p['point']))}, {m.render(freeze(p['value']))})")
            if not result['value']['extrema']:lines.append('Строгих локальных экстремумов нет.')
        else:lines.append(result.get('reason',''))
        return '\n'.join(lines)+'\n'
    goal=result['task'].get('goal');goal=goal if isinstance(goal,dict) else {}
    lines=['ГРАФИК ФУНКЦИИ']
    if isinstance(goal.get('expression'),str):lines.append('y = '+goal['expression'])
    lines.append(result['status'])
    if not result.get('value'):return '\n'.join(lines+[result.get('reason','')])+'\n'
    for curve in result['value']['curves']:
        if curve['parameter_value'] is not None:lines.append(goal['parameter']+' = '+str(curve['parameter_value']))
        excluded=[show(c['x']) for c in curve['cuts'] if c['type']!='point']
        lines.append('Область определения ℝ'+(' \\ {'+', '.join(excluded)+'}' if excluded else ''))
        for c in curve['cuts']:
            if c['type']=='pole':lines.append('Вертикальная асимптота x = '+show(c['x']))
            elif c['type']=='hole':lines.append('Выколотая точка ('+show(c['x'])+', '+show(c['y'])+')')
        for b in curve['branches']:
            motion={1:'возрастает',-1:'убывает',0:'постоянна'}[b['derivative_sign']]
            sign={1:'f(x)>0',-1:'f(x)<0',0:'f(x)=0'}[b['sign']]
            lines.append(f'На ({show(b["left"])}, {show(b["right"])}) функция {motion}, {sign}.')
        lines.append('Пределы на левом и правом концах '+', '.join(map(show,curve['tail_limits'])))
    return '\n'.join(lines)+'\n'


def derivative_signs(task,lib,request):
    """Determine strict shape from an exhaustive sign partition of the original derivative."""
    try:return positive_parameter_reduction(task,lib,request)
    except (Unsupported,poly.NotRational,poly.Undefined):pass
    for method in (indexed_phase_shape,monomial_exponential_sign,absolute_harmonic_shape,positive_logarithmic_curvature):
        try:return method(task,lib)
        except (Unsupported,poly.NotRational,poly.Undefined):pass
    from tasks import guard_source,entailed_domain_guards,source
    from operations import expression_positions
    from verify import same_value
    kind=task['kind'];second=kind=='concavity_and_inflection';x=task['variable'];ctx=m.context(dict(variable=x))
    headings={'strict_monotonicity_intervals':['all_strict_increasing_and_decreasing_intervals'],
              'concavity_and_inflection':['all_concavity_intervals','all_inflection_points']}
    origin=task.get('source',{})
    if (not lib.data.get('derivative_sign_certificates') or set(task)-{'id','kind','source','function','variable','parameters','stated_conditions','requested_output'}
            or task.get('parameters') or task.get('requested_output')!=headings.get(kind)
            or set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','printed_instruction'}
            or origin.get('printed_instruction') not in (None,'Определить промежутки монотонности в строгом смысле.')
            or second and 'printed_instruction' in origin):raise Unsupported('Unbound shape, parameter or source method')
    f=m.parse(task['function'],x);v=('v',x)
    conditions=task.get('stated_conditions',[]);restrictions=[]
    if not isinstance(conditions,list):raise Unsupported('A list of source restrictions is required')
    for s in conditions:
        a=re.fullmatch(r'(.+?)(<=|>=|<|>)(.+)',s)
        if not a:raise Unsupported('Unparsed source inequality')
        left,right=(m.parse(a[j],x) for j in (1,3))
        restrictions.extend(domain_conditions(left)+domain_conditions(right))
        e=m.add(left,m.neg(right))
        if a[2].startswith('<'):e=m.neg(e)
        restrictions.append(('nonnegative' if '=' in a[2] else 'positive',e))
    for _,z in expression_positions(f):
        if z[0]=='rpow' and not (m.sign(z[1],ctx)==1 or ('positive',z[1]) in restrictions):
            raise Unsupported('The natural domain of the real power including its boundary is unclassified')
    original=domain_conditions(f)+restrictions
    smooth=domain_conditions(f,True)+restrictions
    base,_=domain_partition(x,original,simplify_guards=True);regular,_=domain_partition(x,smooth,simplify_guards=True)
    def member(part,y):
        cuts=list(map(line.read_quadratic_term,part['cuts']))
        for i,z in enumerate(cuts):
            d=line.compare(y,z)
            if d==0:return part['point_membership'][i]
            if d<0:return part['open_cells'][i]
        return part['open_cells'][-1]
    guards=[guard_source(g) for g in entailed_domain_guards(smooth)]
    derivative=f
    for order in range(1,(2 if second else 1)+1):
        t=dict(kind='differentiate',function=source(derivative),variable=x,stated_conditions=guards,method_requirement='table_and_rules')
        derivative=m.simplify(freeze(request(f'derivative of order {order} on the open regular cells',t)['value']))
    factors=[]
    def sign_representative(expanded):
        selected,rest=split_common_factors(expanded,lambda a:a[0] in ('sqrt','abs','cbrt','exp','rpow','cosh'))
        for atom,k in selected.items():
            tag=atom[0];part=atom[1]
            replacement=part if tag=='cbrt' else m.power(part,2) if tag in ('sqrt','abs') else m.ONE
            rest=m.mul(rest,m.power(replacement,k));factors.append((atom,k,replacement))
        return rest
    num,den=map(sign_representative,m.rational_form(derivative))
    trig=None
    try:
        p,d=poly.rf(m.div(num,den),x)
    except poly.NotRational:
        # 1 ± sin(g) and 1 ± cos(g) vanish only at isolated points for a nonconstant polynomial g.
        if den!=m.ONE:raise Unsupported('Remaining denominator is not rational')
        terms=m.rational_form(num)[0];constant=terms.get((),F(0));parts=[(z,c) for z,c in terms.items() if z]
        if len(parts)!=1:raise Unsupported('The derivative sign still has multiple independent elementary factors')
        mon,c=parts[0]
        if len(mon)!=1 or mon[0][1]!=1 or mon[0][0][0] not in ('sin','cos') or not c:
            raise Unsupported('An elementary derivative factor still requires a sign partition')
        atom=mon[0][0];angle=atom[1];ap,ad=poly.rf(angle,x)
        if len(ad)!=1 or len(ap)<2:raise Unsupported('A nonconstant polynomial phase is required')
        if abs(constant)>=abs(c):
            trig=dict(bounded_atom=atom,constant=str(constant),factor=str(c),nonzero_on_each_interval=True)
            p,d=(F(line.sign(constant)),),O
        else:raise Unsupported('Infinitely many phase intervals require an indexed real partition')
    cuts=ordered_cuts([*map(line.read_quadratic_term,base['cuts']),*map(line.read_quadratic_term,regular['cuts']),
                       *rational_roots(p),*rational_roots(d)])
    edges=['-inf',*cuts,'+inf'];cells=[];signs=[];present=[]
    for a,b in zip(edges,edges[1:]):
        sample=line.between(a,b);y=line.Quadratic(sample);exists=member(base,y)
        if exists and not member(regular,y):raise Unsupported('A source interval still lacks differentiability')
        s=None
        if exists:
            denominator=peval(d,sample)
            if not denominator:raise Unsupported('A sign representative is singular on a full interval')
            s=line.sign(peval(p,sample)*denominator)
        cells.append(dict(left=line.endpoint_term(a),right=line.endpoint_term(b),sample=q(sample),direction=s));signs.append(s)
    present=[bool(member(base,z)) for z in cuts]
    joins=[]
    for i,z in enumerate(cuts):
        if present[i] and signs[i] is None and signs[i+1] is None:
            raise Unsupported('An isolated source point requires a convention for shape intervals')
        if second and present[i] and signs[i] is not None and signs[i]==signs[i+1] and not member(regular,z):
            loc=q(z.a) if not z.b else m.add(q(z.a),m.mul(q(z.b),('sqrt',q(z.d))))
            at=m.substitute(f,{v:loc})
            if not m.constant_defined(at,ctx):raise Unsupported('Undefined curvature join')
            slopes=[]
            quotient=('div',('add',f,('mul',q(-1),at)),('add',v,('mul',q(-1),loc)))
            for side in ('left','right'):
                limit=dict(kind='limit',variable=x,approach=dict(point=source(loc),side=side))
                value=request('continuity from '+side,{**limit,'expression':source(f)})['value']
                if isinstance(value,str) or not same_value(freeze(value),at):raise Unsupported('The function is discontinuous at a curvature join')
                slope=freeze(request('first difference quotient from '+side,{**limit,'expression':source(quotient)})['value'])
                if isinstance(slope,str):raise Unsupported('The slope at a curvature join must be finite')
                slopes.append(slope)
            direction=signs[i]
            change=m.sign(m.add(slopes[1],m.neg(slopes[0])),ctx)
            if change is None or change not in (0,direction):
                raise Unsupported('The one-sided slopes cannot be glued with the same curvature')
            joins.append(dict(point=loc,value=at,left_slope=slopes[0],right_slope=slopes[1],direction=direction))
    def ranges(sign):
        selected=[s==sign for s in signs]
        return line.make_union(cuts,selected,[ok and (selected[i] or selected[i+1]) for i,ok in enumerate(present)])
    plan=dict(variable=x,function=f,derivative=derivative,domain=base,smooth_domain=regular,factors=factors,
              sign_ratio=(tuple(map(q,p)),tuple(map(q,d))),trigonometric_bound=trig,cells=cells)
    if joins:plan['curvature_joins']=joins
    if not second:return plan,dict(strictly_increasing=ranges(1),strictly_decreasing=ranges(-1),flat=ranges(0))
    inflections=[]
    for i,z in enumerate(cuts):
        if not present[i] or (signs[i],signs[i+1]) not in ((1,-1),(-1,1)):continue
        loc=q(z.a) if not z.b else m.add(q(z.a),m.mul(q(z.b),('sqrt',q(z.d))))
        val=m.substitute(f,{v:loc})
        if not m.constant_defined(val,ctx):raise Unsupported('The ordinate of a candidate inflection is not proved defined')
        if not member(regular,z):
            request('derivative exists at the exceptional inflection',dict(kind='derivative_at',function=source(f),variable=x,point=source(loc)))
        inflections.append((loc,m.simplify(val)))
    return plan,dict(convex=ranges(1),concave=ranges(-1),flat=ranges(0),inflections=inflections)

def comparison_inputs(task):
    origin=task.get('source',{});out=task.get('requested_output',['proof'])
    if (set(origin)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or origin.get('literal_requirement') not in (None,'Доказать неравенство.','Доказать обе оценки.')
            or out not in (['proof'],['proof','geometric_interpretation'])
            or set(task)-{'kind','id','source','given','statement','requested_output'}):raise Unsupported('An additional source requirement remains unbound')
    if task['kind']=='prove_inequality' and 'statement' not in task:
        given=task['given'].removesuffix(' for all real x');comparison,_,conditions=given.partition(',')
    elif task['kind']=='proof_about_real_functions' and 'given' not in task:
        text=task['statement'];geometry=' Дать геометрическую интерпретацию.'
        if text.endswith(geometry)!=('geometric_interpretation' in out):raise Unsupported('The geometric part is unbound')
        match=re.fullmatch(r'Доказать (.+?) (?:при|для) (.+?)\.',text.removesuffix(geometry))
        if not match:raise Unsupported('The source statement is outside the inequality grammar')
        comparison,conditions=match.groups()
    else:raise Unsupported('Ambiguous inequality source')
    x='x'
    def normalize(s):
        for a,b in [('≤','<='),('≥','>='),('−','-'),('²','^2'),('³','^3'),('π','pi')]:s=s.replace(a,b)
        s=re.sub(r'(?<=[\d)])(?=[a-z(])','*',s)
        s=re.sub(r'\b(sin|cos|tan|ln)\s+x\b',r'\1(x)',s);s=re.sub(r'\be\^x\b','exp(x)',s)
        return s.strip()
    def triples(s):
        chunks=re.split(r'(<=|>=|<|>)',normalize(s))
        if len(chunks)<3 or any(not t.strip() for t in chunks):raise Unsupported('Unknown comparison or restriction')
        for i in range(0,len(chunks)-2,2):
            a,b=m.parse(chunks[i],x),m.parse(chunks[i+2],x);op=chunks[i+1]
            from operations import expression_positions
            if any(n[0]=='s' for e in (a,b) for _,n in expression_positions(e)):raise Unsupported('Parameter families require a uniform sign proof')
            yield (a,b,'=' not in op) if op.startswith('<') else (b,a,'=' not in op)
    return list(triples(comparison)),[triple for c in conditions.split(',') if c.strip() for triple in triples(c)],out


def printed_inequality(task,lib,request):
    """Certify every source comparison by bounding differences on their monotonicity cells."""
    from tasks import source
    if not lib.data.get('derivative_sign_certificates'):raise Unsupported('The derivative sign method is unavailable')
    comparisons,constraints,out=comparison_inputs(task);x='x';v=('v',x);ctx=m.context(dict(variable=x))
    def expand(a,b):
        return [(a[1],b),(m.neg(a[1]),b)] if a[0]=='abs' else [(a,b)]
    restrictions=[];guards=[]
    for a,b,strict in constraints:
        for l,h in expand(a,b):
            guards.extend(domain_conditions(l)+domain_conditions(h))
            guards.append(('positive' if strict else 'nonnegative',m.add(h,m.neg(l))))
            restrictions.append(source(l)+('<' if strict else '<=')+source(h))
    _,scope=domain_partition(x,guards,simplify_guards=True)
    if not scope[1]:raise Unsupported('Empty or unresolved source region')
    def coordinate(endpoint):
        z=line.read_quadratic_term(freeze(endpoint))
        return q(z.a) if not z.b else m.add(q(z.a),m.mul(q(z.b),('sqrt',q(z.d))))
    def sign_at(e):return 1 if e=='+inf' else -1 if e=='-inf' else m.sign(e,ctx)
    claims=[];pictures=[]
    for a,b,strict in comparisons:
        _,defined=domain_partition(x,guards+domain_conditions(a)+domain_conditions(b),simplify_guards=True)
        if scope!=defined:raise Unsupported('An original operand is undefined on the claimed region')
        for l,h in expand(a,b):
            gap=m.add(h,m.neg(l))
            t=dict(kind='strict_monotonicity_intervals',function=source(gap),variable=x,stated_conditions=restrictions,
                   requested_output=['all_strict_increasing_and_decreasing_intervals'])
            chart=request('monotonicity regions of the comparison difference',t)['compilation']
            edges={};bounds=[]
            for cell in chart['cells']:
                direction=cell['direction']
                if direction is None:continue
                endpoint=cell['left' if direction>=0 else 'right']
                if direction==0:point=freeze(cell['sample']);value=m.simplify(m.substitute(gap,{v:point}))
                elif isinstance(endpoint,str):
                    child=dict(kind='limit',variable=x,expression=source(gap),approach=dict(point=endpoint,side='positive_infinity' if endpoint=='+inf' else 'negative_infinity'))
                    value=freeze(request('lower endpoint limit of a comparison difference',child)['value'])
                else:
                    point=coordinate(endpoint);raw=m.substitute(gap,{v:point})
                    if m.constant_defined(raw,ctx):value=m.simplify(raw)
                    else:
                        child=dict(kind='limit',variable=x,expression=source(gap),approach=dict(point=source(point),side='right' if direction>0 else 'left'))
                        value=freeze(request('one-sided boundary of a comparison difference',child)['value'])
                if sign_at(value) not in ((1,) if strict and direction==0 else (0,1)):raise Unsupported('The lower value does not prove the printed inequality')
                bounds.append((cell,direction,value))
                for end in (cell['left'],cell['right']):
                    if not isinstance(end,str):edges[canonical(end)]=freeze(end)
            for point in chart['domain']['cuts']:edges[canonical(point)]=freeze(point)
            checked=[]
            for end in edges.values():
                point=coordinate(end)
                z=line.read_quadratic_term(end)
                if not any((line.compare(z,line.read_endpoint(u))>0 or lc and line.compare(z,line.read_endpoint(u))==0)
                           and (line.compare(z,line.read_endpoint(w))<0 or rc and line.compare(z,line.read_endpoint(w))==0) for u,w,lc,rc in scope[1]):continue
                raw=m.substitute(gap,{v:point});value=m.simplify(raw)
                if not m.constant_defined(raw,ctx) or sign_at(value) not in ((1,) if strict else (0,1)):raise Unsupported('A source point violates the bound or its sign is open')
                checked.append((point,value))
            relation=source(l)+(' < ' if strict else ' ≤ ')+source(h)
            claims.append(dict(relation=relation,difference=gap,bounds=bounds,source_points=checked,
                               explanation='На каждой ветви сравниваем нижнее значение разности с нулём и учитываем включённые концы.'))
        if 'geometric_interpretation' in out:pictures.append('На заданной области график y = '+source(a)+(' строго ниже' if strict else ' лежит не выше')+' графика y = '+source(b)+'.')
    return dict(source_region=scope,restrictions=guards),dict(claims=claims,geometric_interpretation=pictures)

def image_by_branches(t,lib,request):
    """Exact images of monotone branches, their excluded limits and their included endpoints."""
    from math import gcd,floor,ceil
    from functools import reduce
    from tasks import source
    from verify import same_value
    from quadrature import enclose
    if (not lib.data.get('images_of_monotonicity_cells') or set(t)-SET_TASK_FIELDS or t.get('assumptions')
            or set(t['goal'])!={'variable','expression','given_domain','goal'} or t['goal']['goal']!='exact image'):
        raise Unsupported('The branch image needs an explicit source function and a single stated interval')
    g=t['goal'];x=g['variable'];ctx=m.context(dict(variable=x));v=('v',x);e=m.parse(g['expression'],x,extra_functions={'floor','max','min'})
    notation=g['given_domain'];trig=lib.data.get('trig_branch_intervals') and e[0] in ('cot','tan')
    abs_region=(re.fullmatch(r'\{\s*'+re.escape(x)+r'\s*:\s*([^<=>]+)\s*(<|<=)\s*abs\('+re.escape(x)+r'\)\s*(<|<=)\s*([^<=>]+)\s*\}',notation) if trig else None)
    if abs_region:
        lower,rel1,rel2,upper=abs_region.groups()
        bounds=[m.parse(s,None) for s in (lower,upper)]
        if not all(m.constant_defined(z,ctx) for z in bounds):raise Unsupported('An original bound on the absolute value is not real')
        lo,hi=map(m.simplify,bounds)
        if m.num(lo) is None or m.num(hi) is None or not 0<=m.num(lo)<m.num(hi):raise Unsupported('Unproved bounds on an absolute value')
        if lo==m.ZERO and rel1=='<=':regions=[(m.neg(hi),hi,rel2=='<=',rel2=='<=')]
        else:regions=[(m.neg(hi),m.neg(lo),rel2=='<=',rel1=='<='),(lo,hi,rel1=='<=',rel2=='<=')]
    else:regions=[interval_terms(notation,ctx)]
    raw_interval=regions[0];a,b,lc,rc=raw_interval
    def cmp(u,w):
        if u==w:return 0
        if isinstance(u,str) or isinstance(w,str):
            if u=='-inf' or w=='+inf':return -1
            if u=='+inf' or w=='-inf':return 1
        if same_value(u,w):return 0
        diff=m.add(u,m.neg(w));s=m.sign(diff,ctx)
        if s in (-1,1):return s
        l,r=enclose(diff,None)
        if l>0 or r<0:return 1 if l>0 else -1
        raise Unsupported('Cannot strictly order two image endpoints')
    if cmp(a,b)>=0:raise Unsupported('A nondegenerate source interval is required')
    def at(form,point):return m.simplify(m.substitute(form,{v:point}))
    def subimage(form,interval,var=x):
        return request('exact image of a component of the composition',dict(kind='restricted_function_image',
              goal=dict(variable=var,expression=source(form),given_domain=interval,goal='exact image')))['value']
    def as_domain(z):
        if isinstance(z,str):return z
        p=m.num(z)
        return line.quadratic_term(line.Quadratic(p)) if p is not None else z
    finite_algebraic=all(isinstance(z,str) or m.num(z) is not None for z in (a,b))
    domain=('real_set' if finite_algebraic else 'real_expression_intervals',((as_domain(a),as_domain(b),lc,rc),))
    if set(t.get('source',{}))-{'exercise','printed_subpart','pdf_page','printed_page','pdf_pages','pdf_sha256'}:
        raise Unsupported('An additional printed image requirement remains unbound')
    plan=dict(chart='images_of_monotonicity_cells',source=e,interval=raw_interval)
    def finish(pieces):
        ordered=sorted(pieces,key=cmp_to_key(lambda r,s:cmp(r[0],s[0]) or int(s[2])-int(r[2])))
        merged=[]
        for l,h,cl,ch in ordered:
            order=cmp(l,h)
            if order>0 or not order and not (cl and ch):raise Unsupported('Invalid interval image')
            if merged and (cmp(l,merged[-1][1])<0 or cmp(l,merged[-1][1])==0 and (cl or merged[-1][3])):
                u,w,cu,cw=merged.pop();sg=cmp(w,h)
                merged.append((u,w if sg>=0 else h,cu,cw if sg>0 else ch if sg<0 else cw or ch))
            else:merged.append((l,h,cl,ch))
        return plan,dict(domain=domain,image_intervals=merged)
    if trig:
        from ray_proofs import phase_interval,phase_zeros
        kind=e[0];divisor='cos' if kind=='tan' else 'sin';shift=F(1,2) if kind=='tan' else F(0)
        pieces=[];domains=[];branches=[]
        for a,b,lc,rc in regions:
            start,stop=phase_interval(e[1],x,a,b);first,last=phase_zeros(divisor,(start,stop),True,True)
            if last-first>line.MAX_BRANCHES:raise Unsupported('The source contains too many individual pole intervals')
            poles=[F(j)+shift for j in range(first,last+1)]
            turns=[start,*sorted((v for v in poles if v not in (start,stop)),reverse=start>stop),stop]
            coordinates=[m.add(a,m.mul(q((v-start)/(stop-start)),m.add(b,m.neg(a)))) for v in turns]
            increasing=(kind=='tan')==(start<stop)
            for l,h,u,w in zip(coordinates,coordinates[1:],turns,turns[1:]):
                cl=u==start and lc and u not in poles;ch=w==stop and rc and w not in poles
                domains.append((as_domain(l),as_domain(h),cl,ch))
                vals=[]
                for point,turn,side,expected in ((l,u,'right','-inf' if increasing else '+inf'),(h,w,'left','+inf' if increasing else '-inf')):
                    if turn not in poles:vals.append(at(e,point));continue
                    child=dict(kind='limit',variable=x,expression=g['expression'],approach=dict(point=source(point),side=side))
                    value=request('one-sided limit at an original trigonometric pole',child)['value']
                    if value!=expected:raise Unsupported('The one-sided limit disagrees with the orientation of the branch')
                    vals.append(value)
                pieces.append((vals[0],vals[1],cl,ch) if increasing else (vals[1],vals[0],ch,cl))
                branches.append(dict(phase=(q(u),q(w)),included=(cl,ch),pole_ends=(u in poles,w in poles),increasing=increasing))
        symbolic=any(not isinstance(z,str) and z[0]!='quadratic_real' for l,h,_,_ in domains for z in (l,h))
        domain=('real_expression_intervals' if symbolic else 'real_set',tuple(domains))
        plan.update(source_intervals=regions,periodic_branches=branches)
        return finish(pieces)
    original_guards=domain_conditions(e)
    def require_unbroken_domain():
        if not original_guards:return
        guards=[]
        if not isinstance(a,str):guards.append(('nonnegative' if lc else 'positive',m.add(v,m.neg(a))))
        if not isinstance(b,str):guards.append(('nonnegative' if rc else 'positive',m.add(b,m.neg(v))))
        if domain_partition(x,guards+original_guards,simplify_guards=True)[1]!=domain_partition(x,guards,simplify_guards=True)[1]:
            raise Unsupported('This real-interval argument would lose an original-domain restriction')
    def walk(z):
        yield z
        for child in z[1:]:
            if isinstance(child,tuple):yield from walk(child)
    def affine_coeff(z):
        p,d=poly.rf(z,x)
        if len(d)!=1 or len(p)>2:raise Unsupported('A rational affine branch is required')
        return p[0]/d[0],(p[1] if len(p)>1 else F(0))/d[0]
    # A union of the exact branch images also handles jumps in floor and changes of the active affine form.
    if any(z[0] in ('max','min','floor') for z in walk(e)):
        require_unbroken_domain();L,H,_,_=rational_interval(g['given_domain']);cuts=set()
        def branches(z,sample=None):
            try:return {affine_coeff(z)}
            except (poly.NotRational,Unsupported):pass
            tag=z[0];left=branches(z[1],sample)
            if tag=='floor':
                if len(left)!=1 or isinstance(L,str) or isinstance(H,str):raise Unsupported('A bounded affine floor phase is required')
                c,k=next(iter(left))
                if sample is not None:return {(F(floor(c+k*sample)),F(0))}
                if not k:return {(F(floor(c)),F(0))}
                lo,hi=sorted((c+k*L.a,c+k*H.a));j0,j1=floor(lo),floor(hi)
                if j1-j0>line.MAX_BRANCHES:raise Unsupported('Too many integer crossings in the requested interval')
                cuts.update((j-c)/k for j in range(ceil(lo),j1+1));return {(F(j),F(0)) for j in range(j0,j1+1)}
            if tag=='abs':right={(-c,-k) for c,k in left};tag='max'
            elif tag in ('min','max','add','mul','div'):right=branches(z[2],sample)
            else:raise Unsupported('Unknown operation on affine branches')
            if len(left)*len(right)>line.MAX_BRANCHES:raise Unsupported('An affine branch partition exceeds the available representation')
            result=set()
            for c,k in left:
                for d,j in right:
                    if tag in ('min','max'):
                        if sample is None:
                            if j!=k:cuts.add((d-c)/(k-j))
                            result.update(((c,k),(d,j)))
                        else:result.add(((c,k) if (c+k*sample>=d+j*sample)==(tag=='max') else (d,j)))
                    elif tag=='add':result.add((c+d,k+j))
                    elif tag=='mul' and not k*j:result.add((c*d,k*d+j*c))
                    elif tag=='div' and not j and d:result.add((c/d,k/d))
                    else:raise Unsupported('Non-affine product or variable divisor')
            return result
        branches(e);points=[line.Quadratic(c) for c in sorted(cuts) if line.compare(L,line.Quadratic(c))<0 and line.compare(line.Quadratic(c),H)<0]
        edges=[L,*points,H];pieces=[];forms=[]
        def evaluate(form,z):
            c,k=form
            if not isinstance(z,str):return q(c+k*z.a)
            if not k:return q(c)
            return z if k>0 else ('+inf' if z=='-inf' else '-inf')
        for l,h in zip(edges,edges[1:]):
            sample=line.between(l,h);form,=branches(e,sample);u,w=evaluate(form,l),evaluate(form,h)
            pieces.append((w,u,False,False) if form[1]<0 else (u,w,not form[1],not form[1]))
            forms.append((q(sample),tuple(map(q,form))))
        for z in [*points,*([L] if lc else []),*([H] if rc else [])]:
            form,=branches(e,z.a);w=evaluate(form,z);pieces.append((w,w,True,True))
        plan.update(affine_forms=forms,breakpoints=list(map(line.quadratic_term,points)));return finish(pieces)
    # All harmonics of one affine phase have the same amplitude on a full cycle.
    trig=[z for z in walk(e) if z[0] in ('sin','cos')]
    if trig and all(z[1]==trig[0][1] for z in trig):
        phase=trig[0][1];p,d=m.rational_form(e)
        if d=={():F(1)} and all(not mon or len(mon)==1 and mon[0][1]==1 and mon[0][0] in trig for mon in p):
            require_unbroken_domain()
            C=p.get((),F(0));S=p.get(((('sin',phase),1),),F(0));T=p.get(((('cos',phase),1),),F(0))
            if not S and not T:return finish([(q(C),q(C),True,True)])
            if (not S or not T) and not isinstance(a,str) and not isinstance(b,str):
                from ray_proofs import phase_interval,phase_zeros
                try:turns=phase_interval(phase,x,a,b)
                except Unsupported:turns=None
                if turns and abs(turns[1]-turns[0])<=2:
                    first,last=phase_zeros('cos' if S else 'sin',turns,False,False)
                    candidates=[(at(e,a),lc),(at(e,b),rc)]
                    candidates.extend((q(C+(S or T)*(-1 if j%2 else 1)),True) for j in range(first,last+1))
                    vals=sorted((v for v,_ in candidates),key=cmp_to_key(cmp))
                    attained=lambda end:any(included and cmp(value,end)==0 for value,included in candidates)
                    plan.update(phase=phase,phase_turns=list(map(q,turns)),interior_critical_labels=list(range(first,last+1)),extreme_candidates=candidates)
                    return finish([(vals[0],vals[-1],attained(vals[0]),attained(vals[-1]))])
            _,k=affine_coeff(phase)
            if not k:raise Unsupported('A nonconstant affine harmonic phase is required')
            length=None if isinstance(a,str) or isinstance(b,str) else m.pi_multiple(m.simplify(m.mul(q(abs(k)),m.add(b,m.neg(a)))))
            if length is not None and length<2:raise Unsupported('An interval shorter than one full cycle needs its individual turning points')
            if length is None and not (isinstance(a,str) or isinstance(b,str)):raise Unsupported('The phase coverage is not proved')
            radius=m.simplify(('sqrt',q(S*S+T*T)));lo=m.add(q(C),m.neg(radius));hi=m.add(q(C),radius)
            cl=ch=True
            if length==2 and not lc and not rc:
                initial=at(e,a);cl=cmp(initial,lo)!=0;ch=cmp(initial,hi)!=0
            plan.update(phase=phase,frequency=q(k),amplitude=radius,full_period=True);return finish([(lo,hi,cl,ch)])
    # Factor through a common power. Preserve raw definedness of the original expression on this interval.
    notation=g['given_domain'];restr=[]
    if not isinstance(a,str):restr.append(x+('>=' if lc else '>')+source(a))
    if not isinstance(b,str):restr.append(x+('<=' if rc else '<')+source(b))
    def power_degrees(z):
        if z==v:return [1]
        if z[0]=='pow' and z[1]==v and z[2]>0:return [z[2]]
        return [n for child in z[1:] if isinstance(child,tuple) for n in power_degrees(child)]
    deg=reduce(gcd,power_degrees(e),0)
    if deg>=2 and e!=('pow',v,deg):
        require_unbroken_domain()
        def lower(z):
            if z[0]=='pow' and z[1]==v:return m.power(v,z[2]//deg)
            return (z[0],*(lower(c) if isinstance(c,tuple) else c for c in z[1:]))
        inner=subimage(('pow',v,deg),notation);pieces=[];outer=lower(e)
        for u,w,cu,cw in inner['image_intervals']:
            label=('[' if cu else '(')+(u if isinstance(u,str) else source(u))+','+(w if isinstance(w,str) else source(w))+(']' if cw else ')')
            pieces.extend(subimage(outer,label)['image_intervals'])
        plan.update(common_power=deg,outer=outer);return finish(pieces)
    chart=request('all monotonicity cells of the original function',dict(kind='strict_monotonicity_intervals',function=g['expression'],variable=x,
                  stated_conditions=restr,requested_output=['all_strict_increasing_and_decreasing_intervals']))['compilation']
    part=chart['domain'];domain=line.make_union([line.read_quadratic_term(freeze(z)) for z in part['cuts']],part['open_cells'],part['point_membership'])
    def coordinate(z):
        u=line.read_quadratic_term(freeze(z));return q(u.a) if not u.b else m.add(q(u.a),m.mul(q(u.b),('sqrt',q(u.d))))
    def endpoint(z,side):
        p=z if isinstance(z,str) else coordinate(z)
        if not isinstance(z,str):
            value=m.substitute(e,{v:p})
            if m.constant_defined(value,ctx):return m.simplify(value)
        direction=('positive_infinity' if z=='+inf' else 'negative_infinity') if isinstance(z,str) else side
        return freeze(request('one-sided boundary of a monotone branch',dict(kind='limit',expression=g['expression'],variable=x,
               approach=dict(point=p if isinstance(p,str) else source(p),side=direction)))['value'])
    pieces=[];included=[]
    for cell in chart['cells']:
        sign=cell['direction']
        if sign is None:continue
        if sign==0:
            w=at(e,freeze(cell['sample']));pieces.append((w,w,True,True));continue
        u=endpoint(cell['left'],'right');w=endpoint(cell['right'],'left')
        pieces.append((u,w,False,False) if sign>0 else (w,u,False,False))
        for z in (cell['left'],cell['right']):
            if isinstance(z,str) or freeze(z) in included:continue
            z=freeze(z);u0=line.read_endpoint(z)
            if any((line.compare(u0,line.read_endpoint(l))>0 or cl and line.compare(u0,line.read_endpoint(l))==0) and
                   (line.compare(u0,line.read_endpoint(h))<0 or ch and line.compare(u0,line.read_endpoint(h))==0) for l,h,cl,ch in domain[1]):
                w=at(e,coordinate(z));pieces.append((w,w,True,True));included.append(z)
    plan.update(included_points=included,cell_images=pieces);return finish(pieces)
