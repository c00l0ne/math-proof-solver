"""Checked attainable level sets, analytic geometry, and source-domain reductions."""
from fractions import Fraction as F
from functools import reduce
import re

import expressions as m
from cartesian_fields import vector_source
from graphs import refine_root_bracket, strict_sign
from model import ONE, ZERO, Unsupported, freeze, q
from planar_integrals import root_power_primitive
from quadrature import enclose
from tasks import domain_conditions
from verify import same_value


P=m.PI
PLOT_CONTINUITY='Исследовать на непрерывность и нарисовать эскиз графика.'
FLOOR_LIMIT='Исследовать на непрерывность и построить график функции, заданной пределом.'
NUMBER=r'(-?[0-9]+(?:[./][0-9]+)?)'
TRANSLATE=str.maketrans({'²':'^2','³':'^3','⁴':'^4','−':'-'})


def plus(*a):return reduce(m.add,a,ZERO)
def times(*a):return reduce(m.mul,a,ONE)
def diff(a,b):return m.add(a,m.neg(b))
def squared(a):return m.power(a,2)
def root(a):return m.simplify(('sqrt',a))
def absolute(a):return m.simplify(('abs',a))
def s(n):return ('s',n)


def proof(method,argument,value,**checks):
    return dict(theorem='method.'+method,argument=list(argument),**checks),value


def source_fields(task,fields,headings=(),extras=()):
    vector_source(task,fields,headings,extras)


def power_phase(expr,var):
    """Read a fixed nonzero monomial phase in the original coordinate."""
    x=('s',var);a,b=m.rational_form(expr)
    if not a or len(a)!=1 or not b or len(b)!=1:
        raise Unsupported('No monotonically invertible monomial phase')
    (ma,u),=a.items();(mb,v),=b.items()
    powers={x:0};coef=q(u/v)
    for sign,term in ((1,ma),(-1,mb)):
        for sym,p in term:
            if sym==P:coef=m.mul(coef,m.power(P,sign*p))
            elif sym!=x:raise Unsupported('An additional phase factor was not bound')
            else:powers[x]+=sign*p
    if powers[x] not in (-2,-1,1,2) or m.sign(coef,m.context({}))!=1:
        raise Unsupported('An admitted real phase needs a positive fixed scale and power ±1 or ±2')
    for relation,term in domain_conditions(expr,True):
        n,d=m.rational_form(term)
        if (relation!='nonzero' or powers[x]>0 or len(n)!=1 or len(d)!=1
                or any(v!=x for a in (*n,*d) for v,_ in a)):
            raise Unsupported('An uncancelled original phase restriction is not the coordinate zero')
    return coef,powers[x]


def invert_positive_power(A,p,h):
    if p in (1,-1):
        return [m.div(h,A) if p==1 else m.div(A,h)]
    z=root(m.div(h,A) if p==2 else m.div(A,h))
    return [m.neg(z),z]


def phase_lattice(A,p,levels,*,cut_zero=False):
    bounds='nonzero phase' if p<0 else 'every phase'
    if p%2==0:bounds='strictly positive phase' if p<0 or cut_zero else 'nonnegative phase'
    return dict(preimages=invert_positive_power(A,p,levels),phase=levels,
                attainment=bounds,reversed_on='x>0' if p==-2 else 'both half-lines' if p==-1
                         else 'x<0' if p==2 else None)


def read_axis_function(text,var,more=()):
    return m.parse(text.translate(TRANSLATE),None,[var],extra_functions=set(more))


def continuity_from_phase(task):
    source_fields(task,{'goal','function','variable','requested_output'},(PLOT_CONTINUITY,),('notation_review',))
    if 'goal' in task:
        item=task['goal']
        if (not isinstance(item,dict) or set(item)!={'variable','expression','goal'}
                or item['goal']!='construct the complete graph' or {'function','variable','requested_output'}&task.keys()
                or task.get('source',{}).get('literal_requirement')!=PLOT_CONTINUITY):
            raise Unsupported('The source drawing does not include a separate continuity question')
        f,x=item['expression'],item['variable']
    else:
        if task['requested_output']!=['continuity_on_original_domain','exceptional_points']:
            raise Unsupported('The original mathematics of continuity and exceptional points is required')
        f,x=task['function'],task['variable']
    X=s(x)
    k=s('k' if x!='k' else 'j')
    target=m.mul(P,k)
    pows=re.fullmatch(r'\(-1\)\^\[(.*)\]',f)
    if pows:
        phase=read_axis_function(pows[1],x);A,p=power_phase(phase,x)
        if p not in (1,2):raise Unsupported('The floor image and its zero-side traces are not established')
        lattice=phase_lattice(A,p,k,cut_zero=p==2)
        value=dict(original_domain='all real under the integer-part notation',jumps=lattice,continuous_elsewhere=True)
        steps=[
            'Read the brackets in the integer-part notation. At each attainable integer crossing the exponent changes by one.',
            'The two one-sided values differ by sign. The exact value uses the floor at the original integer.',
            'On the open cells the parity is constant. A square phase at its zero minimum stays on the same floor branch.']
        steps.append('If the delimiters group a rational exponent instead, approximate each phase value by reduced rationals with odd denominators and numerators of either parity. Both signs occur arbitrarily near every source point, including the nonnegative boundary for a square phase.')
        value['grouping_interpretation']=dict(domain='phase has rational value with odd reduced denominator',
                                                continuous_nowhere_relative_to_that_domain=True)
        return proof('attainable_phase_events',steps,value,original_phase=phase)
    raw=read_axis_function(f,x,('floor','sign'))
    if raw[0]=='mul':
        a,b=raw[1:]
        if a[0]=='sign':a,b=b,a
        if a[0]=='floor' and b[0]=='sign' and b[1][0]=='sin':
            A,p=power_phase(a[1],x);B,h=power_phase(b[1][1],x)
            coefficient=m.num(m.simplify(m.div(B,P)))
            sA=m.num(A);ratio=sA/(coefficient*coefficient) if sA is not None and coefficient else None
            if p!=-2 or h!=-1 or ratio is None or ratio.denominator!=1 or ratio<=0:
                raise Unsupported('The two original event lattices have not been reconciled')
            at_cross=phase_lattice(A,p,k,cut_zero=True)
            phase_zeros=phase_lattice(B,h,target)
            return proof('attainable_phase_events',[
                'The floor changes at positive attained integers. Each zero of the sine has phase an integer multiple of π.',
                'The ratio of squared phase scales gives an integer, so every sign event also lies on the floor-event lattice.',
                'At pure floor events the nonzero sign multiplies a change of one. At coincident events the two signs are opposite and the larger-side floor is positive. Both kinds are jumps.',
                'Near zero positive and negative sine half periods occur arbitrarily close, while the floor tends to infinity.'],
                dict(original_domain=f'{x}!=0',jumps=at_cross,zero_sine_events=phase_zeros,at_zero='unbounded oscillation'),
                original_expression=raw,integer_scale_ratio=q(ratio))
    if raw[0] in ('cot','tan'):
        phase=raw[1];op=raw[0];order=1;shape='linear_tangent_pole'
    elif raw[0]=='pow' and raw[1][0] in ('sec','csc') and raw[2]==2:
        phase=raw[1][1];op=raw[1][0];order=2;shape='positive_inverse_square'
    elif raw[0]=='div' and raw[1]==ONE:
        den=raw[2];op='sin';order=1;shape='reciprocal_sine';phase=None
        for z in (den,*(den[1:] if den[0]=='mul' else ())):
            e,n=(z[1],z[2]) if z[0]=='pow' else (z,1)
            if e[0]!=op:continue
            phase=e[1];order=n
            if z!=den:
                other=den[1] if den[2]==z else den[2]
                if other!=squared(X):raise Unsupported('A remaining original denominator is not a square of the coordinate')
                shape='coordinate_square_and_sine'
        if phase is None:raise Unsupported('The reciprocal denominator has no checked single sine')
    else:raise Unsupported('No complete source phase partition has been found')
    A,p=power_phase(phase,x)
    if op in ('tan','sec'):target=m.mul(P,m.add(k,q(1,2)))
    nonzero=shape=='coordinate_square_and_sine' or p<0
    lattice=phase_lattice(A,p,target,cut_zero=p==2)
    leading='nondegenerate simple sine or cosine zero transported by the phase derivative'
    if op=='cot':direction='(+infinity,-infinity) if the phase decreases, reverse if it increases'
    elif op=='tan':direction='(+infinity,-infinity) if the phase increases, reverse if it decreases'
    elif order%2==0:direction='both +infinity'
    else:direction='opposite infinities, sign on the right determined by (-1)^k times the phase derivative'
    zero_case=('oscillatory omitted accumulation point' if p<0 else
               'both +infinity; leading power is x^(-4)' if shape=='coordinate_square_and_sine' and phase==X and order==2
               else 'both +infinity; leading power is x^(-2)' if p==2 and order==1 and op=='sin'
               else 'include the zero phase among the simple poles' if op in ('cot','sin','csc') and p==1
               else 'continuous if present in original domain')
    return proof('attainable_phase_events',[
        'Find every attainable zero of the original sine or cosine before cancellation.',
        'Transport the local signed zero through each strictly monotone phase chart. Even inverse powers give the same positive infinity on both sides.',
        'Treat a critical point or a deleted origin separately. For reciprocal phases compare fixed-phase sequences near zero.'],
        dict(original_domain='exclude the displayed poles and separately excluded coordinate values',
             poles=dict(lattice,side_behavior=direction,local_order=order),at_zero=zero_case,
             coordinate_zero_excluded=nonzero,continuous_elsewhere=True),
        original_expression=raw,phase=phase,local_rule=leading,raw_guards=domain_conditions(raw,True))


def geometric_power_limits(task):
    source_fields(task,{'variable','limit_variable','limit_domain','approach','expression','domain','requested_output'},
                  (FLOOR_LIMIT,),('notation_review',))
    x=task['variable'];n=task['limit_variable'];X=s(x);text=task['expression']
    if (task['limit_domain']!='positive integers' or task['approach']!='+infinity'
            or task['requested_output'] not in (['pointwise limit','continuity on original domain and exceptional points'],
                ['pointwise limit','continuity on original domain and exceptional points','graph'])):
        raise Unsupported('The pointwise limit, integer index and original continuity question must be bound')
    arctan=re.fullmatch(r'\['+re.escape(x)+r'\*atan\('+re.escape(n)+r'\*cot\('+re.escape(x)+r'\)\)\]',text)
    if arctan:
        if task['domain']!='x outside pi*Z':raise Unsupported('The original cotangent poles must be omitted')
        return proof('attainable_phase_events',[
            'At a fixed nonzero cotangent, arctan(n cot x) tends to the signed π/2. Near the limit the magnitude increases monotonically.',
            'If the original brackets denote a floor, a positive integral limit is approached from below and lowers the limiting integer by one.',
            'Partition at cotangent zeroes and poles, and for the floor reading also at the attained integral levels of the limiting branch. At zero both adjacent limits are zero.'],
            dict(original_domain=task['domain'],inner_limit=f'(pi/2)*{x}*sign(cot({x}))',
                 grouping_reading='inner_limit',
                 floor_reading='floor(inner_limit) except positive integer inner_limit, where subtract one',
                 jumps_on_original_domain='cotangent zeros in both readings; also interior nonzero integer levels in the floor reading',
                 removed_nonzero_poles='different finite traces',zero_extension=ZERO))
    e=m.parse(text,None,[x,n]);powers=[]
    def visit(t):
        if t[0]=='rpow' and not domain_conditions(t[2]) and same_value(t[2],m.mul(q(2),s(n))):powers.append(t)
        for v in t[1:]:
            if isinstance(v,tuple):visit(v)
    visit(e)
    if len(powers)!=1 or task['domain']!='R':raise Unsupported('The requested function does not have one even geometric sequence on the stated real domain')
    a=powers[0];osc=a[1]
    if osc[0] in ('sin','cos') and osc[1]==X:coef=ONE;family=osc[0]
    elif osc[0]=='mul':
        u,v=osc[1:]
        if m.num(v) is not None:u,v=v,u
        if m.num(u) is None or m.num(u)<=0 or v!=('sin',X):raise Unsupported('No fixed sine threshold')
        coef=u;family='sin'
    else:raise Unsupported('No checked geometric amplitude')
    if e==a and coef==ONE:
        base='x=k*pi' if family=='cos' else 'x=pi/2+k*pi'
        return proof('attainable_phase_events',[
            'The even-power base is nonnegative. At an attained magnitude-one endpoint it remains one, and elsewhere its powers tend to zero.',
            'At each isolated magnitude-one point the function has a removable discontinuity, since all nearby values off that set are zero.'],
            dict(pointwise_limit=dict(one=base,zero='elsewhere'),removable_discontinuities=base),source_oscillation=osc)
    if (e[0]!='div' or e[1]!=X or e[2][0]!='add'
            or (e[2][1],e[2][2]) not in ((ONE,a),(a,ONE)) or family!='sin' or m.num(coef)<=1):
        raise Unsupported('A crossed magnitude-one threshold with the original numerator is required')
    theta=('asin',m.div(ONE,coef))
    return proof('attainable_phase_events',[
        'Compare the attainable absolute sine amplitude with one. The respective denominator limit is one, two, or positive infinity.',
        'At a threshold the magnitude-one condition is a simple crossing. The two limiting branch values differ by x at the crossing, and x there is nonzero.'],
        dict(pointwise_limit=[dict(condition='abs(amplitude)<1',value=X),dict(condition='abs(amplitude)=1',value=m.div(X,q(2))),
                              dict(condition='abs(amplitude)>1',value=ZERO)],
             jump_families=[m.add(target:=m.mul(P,s('k')),theta),diff(target,theta)]),source_oscillation=osc)


PIECEWISE_HEADING='Исследовать непрерывность и выяснить характер точек разрыва.'
DENSE_HEADINGS=(
    'Исследовать на непрерывность функцию xχ(x) и построить эскиз графика.',
    'Доказать разрывность в каждой рациональной точке и непрерывность в каждой иррациональной точке, построить эскиз графика.',
    'Исследовать непрерывность заданной функции и построить эскиз графика.',
    PIECEWISE_HEADING,
)


def dense_source_continuity(task):
    source_fields(task,{'branches','function','chi','requested_output'},DENSE_HEADINGS)
    target=task.get('requested_output')
    x=s('x');branches=task.get('branches')
    def finish(steps,**values):return proof('dense_domain_continuity',steps,values)
    if task.get('chi')=='Dirichlet function: 1 on rationals, 0 on irrationals; preceding task':
        if target not in (None,['continuity']) or 'branches' in task:raise Unsupported('A single Dirichlet-weighted field is required')
        match=re.fullmatch(r'([a-zA-Z][a-zA-Z_0-9]*|[0-9]+)\*chi\(x\)',task.get('function',''))
        if not match or match[1]!='x':raise Unsupported('An unbound factor in the Dirichlet product')
        return finish(['Along rational points the values converge to the point; along irrational points they are zero.',
                       'Density of both sets leaves exactly the origin, where the product is squeezed in absolute value by |x|.'],
                      continuous_at=[ZERO],discontinuous_elsewhere='no two-sided limit')
    if not isinstance(branches,list) or len(branches)!=2 or 'function' in task or 'chi' in task:
        raise Unsupported('The original two dense branches were not identified')
    (d,a),(e,b)=branches
    if (d,e)==('x rational','x irrational') and b=='0' and not target:
        phase=read_axis_function(a,'x')
        if phase[0]!='sin':raise Unsupported('No checked equality of the two dense branch limits')
        h,p=power_phase(phase[1],'x')
        if p!=1:raise Unsupported('The complete common zero profile was not deduced')
        return finish(['The rational branch has limiting value sin(phase) and the irrational branch has limiting value zero.',
                       'Both sets are dense. Equality holds exactly at the attained sine zeros, at which the actual value is also zero.'],
                      continuous_on=phase_lattice(h,p,m.mul(P,s('k'))),elsewhere='no limit')
    if d not in ('x=m/n rational in lowest terms, n>0','x=m/n reduced rational, n>=1') or e!='x irrational':
        raise Unsupported('Reduced positive denominators and the complementary irrational branch are required')
    reasoning=['A bounded interval contains only finitely many reduced fractions with denominator below any fixed bound.',
               'Along distinct rational inputs tending to the point, their reduced denominators therefore tend to infinity.']
    if b=='0' and a=='1/n' and target in (None,['prove_rational_discontinuity_and_irrational_continuity']):
        return finish(reasoning+['The punctured limit is zero at every point. Compare with the positive assigned value of each rational input.'],
                     continuous_on='irrational inputs',removable_discontinuities='all rational inputs',punctured_limit=ZERO)
    hit=re.fullmatch(r'n\*x/\(n\+([1-9]\d*)\)',a)
    if b=='abs(x)' and hit and target in (None,['continuity']):
        return finish(reasoning+['The rational limiting branch is x and the irrational limiting branch is |x|.',
                    'On the positive side those limits agree, but a positive rational point has a smaller specified value. At zero the specified value agrees as well.'],
                    continuous_on='zero and positive irrational inputs',removable_discontinuities='positive rational inputs',
                    other_discontinuities='all negative inputs have distinct dense-branch limits')
    raise Unsupported('No checked limiting branch identity for the original rational/irrational branches')


def branch_interval(condition):
    if clauses:=re.fullmatch(NUMBER+r'(<=|<)x(<=|<)'+NUMBER,condition):
        a,lo,hi,b=clauses.groups()
        return [(F(a),F(b),lo=='<=',hi=='<=')]
    if upper:=re.fullmatch('x(<=|<)'+NUMBER,condition):
        return [(None,F(upper[2]),False,upper[1]=='<=')]
    if lower:=re.fullmatch('x(>=|>)'+NUMBER,condition):
        return [(F(lower[2]),None,lower[1]=='>=',False)]
    if lower:=re.fullmatch(NUMBER+r'(<=|<)x',condition):
        return [(F(lower[1]),None,lower[2]=='<=',False)]
    if ab:=re.fullmatch(r'abs\(x\)(<=|>)'+NUMBER,condition):
        b=F(ab[2])
        if b<=0:raise Unsupported('A positive original symmetric threshold is needed')
        return [(-b,b,True,True)] if ab[1]=='<=' else [(None,-b,False,False),(b,None,False,False)]
    raise Unsupported('A complete one-dimensional branch interval was not bound')


def elementary_piecewise(task):
    kind=task['kind']
    headings=(PIECEWISE_HEADING,'Определить, является ли указанная функция непрерывной.',
              'Определить, является ли непрерывной функция.','Найти все a, при которых функция непрерывна.',
              'При каком выборе числа a функция f(x) будет непрерывной?')
    source_fields(task,{'branches'},headings)
    branches=task['branches'];X=s('x')
    if len(branches)==2 and {c for c,_ in branches}=={'x rational','x irrational'}:
        return dense_source_continuity(task)
    if (len(branches)==2 and branches[0][0]=='x noninteger' and branches[1]==['x integer','0']):
        ph=read_axis_function(branches[0][1],'x')
        if ph!=('pow',('cot',m.mul(P,X)),2):raise Unsupported('No verified pole and assignment pattern')
        return proof('piecewise_boundary_matching',[
            'The cotangent is continuous between its original integer poles.',
            'The inverse square of the local phase difference is positive and unbounded from both sides. The assigned value stays zero.'],
            dict(jumps=[],infinite_discontinuities='every integer',continuous_elsewhere=True))
    fixed=set()
    for _,formula in branches:
        fixed|=set(re.findall(r'[a-zA-Z][a-zA-Z_0-9]*',formula))-({'x','pi','e'}|m.FUNCTIONS|set(m.ALIASES))
    params=sorted(fixed)
    if len(params)!=(1 if kind=='continuous_parameter_fit' else 0):raise Unsupported('The original free parameter and output disagree')
    ctx=m.context(dict(variable='__piece',parameters=params))
    charts=[]
    for c,f in branches:
        expr=m.parse(f,None,['x',*params])
        if any(not m.constant_defined(t,ctx) or m.sign(t,ctx) not in (
                (1,-1) if rel=='nonzero' else (1,0) if rel=='nonnegative' else (1,))
                for rel,t in domain_conditions(expr)):
            raise Unsupported('An original branch has an unresolved interior domain restriction')
        for lo,hi,lclose,hclose in branch_interval(c):
            if lo is not None and hi is not None and lo>=hi:raise Unsupported('The original interval has no interior')
            charts.append((lo,hi,lclose,hclose,expr))
    def at(expr,t):
        e=m.substitute(expr,{X:q(t)})
        if not m.constant_defined(e,ctx):raise Unsupported('A branch has an undefined endpoint value')
        return m.simplify(e)
    edges=sorted({t for l,h,_,_,_ in charts for t in (l,h) if t is not None})
    if not edges:raise Unsupported('No original finite boundary data')
    cuts=[];conditions=[]
    for u in edges:
        left=[f for l,h,lc,hc,f in charts if (l is None or l<u) and (h is None or u<=h)]
        right=[f for l,h,lc,hc,f in charts if (l is None or l<=u) and (h is None or u<h)]
        point=[f for l,h,lc,hc,f in charts if (l is None or l<u or l==u and lc) and (h is None or u<h or h==u and hc)]
        if max(map(len,(left,right,point)))>1:raise Unsupported('Two original branch pieces overlap')
        L=at(left[0],u) if left else None;R=at(right[0],u) if right else None
        val=at(point[0],u) if point else None
        compared=[v for v in (L,R,val) if v is not None]
        conditions.extend(diff(v,compared[0]) for v in compared[1:] if not same_value(v,compared[0]))
        label=('jump' if L is not None and R is not None and not same_value(L,R)
               else 'different assigned value' if point and any(not same_value(v,val) for v in compared)
               else 'continuous relative to original domain' if point else 'omitted point')
        cuts.append(dict(point=q(u),left=L,right=R,value=val,classification=label))
    if params:
        nonzero=[z for z in conditions if not same_value(z,ZERO)]
        v=s(params[0]);sol=None
        if not nonzero:out=dict(continuous_for='all real values of the original parameter')
        else:
            for term in nonzero:
                a=m.simplify(m.substitute(term,{v:ZERO}));b=diff(m.simplify(m.substitute(term,{v:ONE})),a)
                if m.num(b) in (None,0) or not same_value(term,m.add(a,m.mul(b,v))):
                    raise Unsupported('No exact affine parameter solving the original endpoint equalities')
                t=m.div(m.neg(a),b)
                if sol is not None and not same_value(t,sol):return proof('piecewise_boundary_matching',
                    ['The linear endpoint equations have different roots.'],dict(continuous_for='empty'))
                sol=t
            out=dict(parameter=params[0],continuous_for=sol)
    else:out=dict(boundaries=cuts,continuous_on_open_cells=True)
    return proof('piecewise_boundary_matching',[
        'On each source branch the admitted elementary formula is continuous.',
        'Collect all finite interval endpoints without choosing a different assigned value. Substitute to evaluate each relative side and compare at every cut.'],
        out,original_boundary_checks=cuts)


def dirichlet_continuity(task):
    kind=task['kind']
    if kind=='nested_limit_dirichlet_proof':
        source_fields(task,{'expression','domain','indices'},
                      ('Доказать разрывность во всякой точке функции Дирихле, заданной повторным пределом.',))
        if (task['expression']!='lim_{m->infty}(lim_{n->infty} cos(pi*m!*x)^n)' or task['domain']!='real x'
                or task['indices']!='positive integers m,n'):
            raise Unsupported('The original factorial phase and both ordered indices are required')
        return proof('dense_domain_continuity',[
            'For each irrational x the factorial phase is never integral, so the inner cosine has modulus below one.',
            'For a reduced rational x with denominator q, eventually 2q divides m!. The cosine becomes one on this outer tail.',
            'Earlier rational indices can have an undefined odd-parity inner limit. The outer limit depends on the complete tail.',
            'The resulting function has value one on rationals and zero on irrationals. Density proves discontinuity at every point.'],
            dict(continuous_on='empty',function='indicator of the rationals',index_scope='inner limits on an eventual outer tail'))
    source_fields(task,{'statement','requested_output'})
    if (task['statement']!='Для ограниченной f на [a,b] доказать непрерывность слева m(x)=inf_{a≤ξ<x}f(ξ), M(x)=sup_{a≤ξ<x}f(ξ) на [a,b].'
            or task['requested_output']!=['proof']):
        raise Unsupported('The exact strict-prefix theorem must be bound')
    return proof('piecewise_boundary_matching',[
        'For x>a the strict prefix is the increasing union of all strict prefixes at t<x.',
        'Every point in the prefix enters one of the earlier prefixes. Approximants to its infimum and supremum prove convergence of the corresponding monotone extrema from the left.',
        'The strict prefix at a is empty, so the printed formula defines a real function on (a,b].'],
        dict(left_continuity_domain='(a,b]',at_a='undefined by the strict-prefix formula',literal_closed_domain_needs_value=True))


def distance_union(task):
    source_fields(task,{'set','distance','requested_output'},
                  ('Найти аналитическое выражение расстояния до заданного множества, построить график и исследовать непрерывность.',))
    if (task.get('requested_output') not in (None,['analytic_distance','continuity'])
            or task['distance']!='shortest distance of x on the number line to the set'):
        raise Unsupported('The real distance and its original continuity question are required')
    intervals=[]
    for piece in task['set'].split(' union '):
        m0=re.fullmatch(r'\['+NUMBER+','+NUMBER+r'\]',piece)
        if not m0:raise Unsupported('Expected a finite union of nonempty closed intervals')
        a,b=(F(t) for t in m0.groups())
        if a>b:raise Unsupported('The original interval endpoints are reversed')
        intervals.append((a,b))
    union=[]
    for a,b in sorted(intervals):
        if union and a<=union[-1][1]:
            A,B=union.pop()
            union.append((A,max(b,B)))
        else:union.append((a,b))
    gaps=[dict(between=(q(b),q(c)),midpoint=q((b+c)/2),expression=f'min(x-({b}),({c})-x)')
          for (_,b),(c,_) in zip(union,union[1:])]
    return proof('piecewise_geometric_measure',[
        'Outside a finite union of closed intervals the nearest point is an adjacent endpoint.',
        'Inside the original set the distance is zero. In a gap its formula is the lesser of the two adjacent distances.',
        'Applying the triangle inequality to every nearest point yields the global Lipschitz constant one.'],
        dict(zero_regions=[(q(a),q(b)) for a,b in union],
             left_tail=f'{union[0][0]}-x',right_tail=f'x-({union[-1][1]})',gaps=gaps,continuous='all real'))


def horizontal_section(vertices,height):
    intersections=[]
    for (x,y),(u,v) in zip(vertices,vertices[1:]+vertices[:1]):
        if height==y==v:intersections.extend((x,u))
        elif y!=v and min(y,v)<=height<=max(y,v):intersections.append(x+(u-x)*(height-y)/(v-y))
    return max(intersections)-min(intersections) if intersections else F(0)


def swept_area(task):
    source_fields(task,{'figure','closed_triangle_vertices','rectangles','area','width','domain','requested_output'},
                  ('Найти аналитические выражения обеих функций, построить их графики и исследовать непрерывность.',))
    if (task.get('requested_output') not in (None,['analytic_area','analytic_cross_section_length','continuity_of_both'])
            or task['domain']!='0<=y<+infinity' or task['area']!='S(y) is the area of the figure between Y=0 and Y=y'
            or task['width']!='b(y) is the length of the horizontal cross-section at Y=y'):
        raise Unsupported('Bind both requested cross-section measures on the original height domain')
    def point(p):
        if not isinstance(p,list) or len(p)!=2:raise Unsupported('Each source vertex must have two real coordinates')
        return tuple(F(str(x)) for x in p)
    tri=list(map(point,task['closed_triangle_vertices']))
    if len(tri)!=3:raise Unsupported('The known triangular support needs three vertices')
    (a,b),(c,d),(e,f)=tri
    if (c-a)*(f-b)==(d-b)*(e-a):raise Unsupported('The original triangle is degenerate')
    polygons=[tri]
    for rr in task['rectangles']:
        (x,y),(u,v)=map(point,rr)
        if x>=u or y>=v:raise Unsupported('A named rectangle has reversed or equal corners')
        polygons.append([(x,y),(u,y),(u,v),(x,v)])
    projected=sorted((min(x for x,_ in p),max(x for x,_ in p)) for p in polygons)
    if any(b>c for (_,b),(c,_) in zip(projected,projected[1:])):
        raise Unsupported('Horizontal sections of the original pieces may overlap on positive length')
    H=sorted({F(0)}|{y for p in polygons for _,y in p if y>=0})
    if any(y<0 for p in polygons for _,y in p):raise Unsupported('The source figure extends below its original baseline')
    cells=[];area=F(0);Y=s('y')
    def W(y):return sum(horizontal_section(p,y) for p in polygons)
    for a,b in zip(H,H[1:]):
        L=(2*a+b)/3;R=(a+2*b)/3
        slope=(W(R)-W(L))/(R-L);w=W(L)-slope*(L-a)
        z=diff(Y,q(a))
        width=m.add(q(w),m.mul(q(slope),z))
        integral=plus(q(area),times(q(w),z),times(q(slope/2),squared(z)))
        cells.append(dict(open_interval=[q(a),q(b)],width=width,area=integral))
        area+=w*(b-a)+slope*(b-a)**2/2
    endpoints=[]
    for i,y in enumerate(H):
        left=m.substitute(cells[i-1]['width'],{Y:q(y)}) if i else None
        right=m.substitute(cells[i]['width'],{Y:q(y)}) if i<len(cells) else ZERO
        w=q(W(y))
        endpoints.append(dict(height=q(y),width=w,left=left,right=right,
                             continuous=all(same_value(t,w) for t in (left,right) if t is not None)))
    return proof('piecewise_geometric_measure',[
        'Sort the actual vertex heights. Between consecutive heights a convex polygon has a section whose endpoints move linearly.',
        'The horizontal projections of the named pieces have disjoint interiors, so their widths add. At an endpoint use the closed polygon sides themselves.',
        'Integrating each affine width gives the accumulated area. Adjacent primitive pieces join continuously at their shared area values.'],
        dict(cells=cells,endpoint_widths=endpoints,tail=dict(width=ZERO,area=q(area)),area_continuous=True))


def text_key(value):
    if not isinstance(value,str):raise Unsupported('A mathematical formula must be text')
    return re.sub(r'\s+','',value.translate(TRANSLATE))


def requested(task,*output):
    if task.get('requested_output') not in (None,list(output)):
        raise Unsupported('A different output changes the original source proof')


def curvature(task):
    kind=task['kind'];x,y,r,r1,r2=map(s,('x','y','r','r_prime','r_second'))
    if kind=='polar_curvature_formula':
        source_fields(task,{'coordinate','radius_function','requested_output'},
            ('Написать формулу радиуса кривизны линии, заданной в полярных координатах.',))
        requested(task,'polar_curvature_radius_formula')
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',task['coordinate']) or not re.fullmatch(
                r'arbitrary twice differentiable r\('+re.escape(task['coordinate'])+r'\)',task['radius_function']):
            raise Unsupported('Need a twice differentiable radius in the stated angular coordinate')
        speed=plus(squared(r),squared(r1));det=plus(squared(r),times(q(2),squared(r1)),m.neg(times(r,r2)))
        return proof('regular_curve_curvature',[
            'The derivative in the rotating orthonormal polar frame has coordinates (r′,r).',
            'Differentiating the frame gives second derivative (r″−r,2r′). The speed squared and determinant give the unsigned curvature.'],
            dict(radius=m.div(times(speed,root(speed)),absolute(det)),
                 conditions=['r^2+r_prime^2>0','nonzero velocity-acceleration determinant'],
                 zero_determinant='zero curvature at regular points',stationary='a regular chart is required'),
            speed_squared=speed,determinant=det)
    raw=text_key(task['curve'])
    if kind=='curvature_identity':
        source_fields(task,{'curve','normal_segment','requested_output'},
            ('Доказать пропорциональность радиуса кривизны кубу отрезка нормали.',))
        requested(task,'prove_curvature_radius_proportional_to_cube_of_normal_segment')
        match=re.fullmatch(r'y\^2=2\*([A-Za-z]\w*)\*x-([A-Za-z]\w*)\*x\^2',raw)
        if not match or len(set(match.groups())|{'x','y'})!=4 or task['normal_segment']!='distance along normal from point to x-axis':
            raise Unsupported('Need an implicit quadratic graph and its normal intercept')
        p0,h=map(s,match.groups());slope=m.div(diff(p0,times(h,x)),y)
        ell=times(absolute(y),root(plus(ONE,squared(slope))))
        return proof('regular_curve_curvature',[
            'On a branch with y≠0, differentiate the conic equation twice. Substituting the conic equality makes the second derivative −p²/y³.',
            'The normal vector (−y′,1) reaches the x-axis at parameter −y, so its segment length is |y|√(1+y′²).',
            'Substitution into the graph formula gives the cube law. At the axis the normal lies along it, so the literal segment has no unique endpoint.',
            'If p=0 the quadratic level degenerates into lines, an axis, or an isolated point. A finite proportionality coefficient is not defined for that case.'],
            dict(radius=m.div(times(squared(ell),ell),squared(p0)),normal_length=ell,
                 factor=m.div(ONE,squared(p0)),conditions=[('nonzero',p0),('nonzero',y)]),
            slope=slope,second=m.neg(m.div(squared(p0),m.power(y,3))))
    if kind=='curve_curvature_radius':
        source_fields(task,{'curve','representation','positive_parameters','requested_output'},
            ('Определить радиус кривизны кривой в полярных координатах. Параметры положительны.',))
        requested(task,'curvature_radius')
        match=re.fullmatch(r'r\^2=([A-Za-z]\w*)\^2\*cos\(([1-9]\d*)\*phi\)',raw)
        if not match or task['representation']!='polar' or task['positive_parameters']!=[match[1]]:
            raise Unsupported('Need a positive radial scale and a nonzero integer angular frequency')
        a,k=s(match[1]),int(match[2]);A=squared(a);R=squared(r)
        speed1=times(q(F(k*k,4)),m.div(diff(squared(A),squared(R)),R))
        speed=plus(R,speed1);det=plus(times(q(1+F(k*k,2)),R),times(q(3),speed1))
        radius=m.div(times(speed,root(speed)),det) if k!=2 else m.div(A,times(q(3),absolute(r)))
        return proof('regular_curve_curvature',[
            'A real nonzero branch has r²=a² cos(kφ)>0. Differentiate this original relation twice.',
            'Eliminate sin²(kφ) by 1−cos²(kφ). The polar determinant is (1+k²/2)r²+3(r′)², strictly positive on the nonzero branch.',
            'At the origin r cannot be used in this chart. Each incident regular branch has limiting curvature zero.'],
            dict(radius=radius,conditions=[('positive',a),('nonzero',r)],origin='branch limit of curvature is zero'),
            prime_squared=speed1,speed_squared=speed,determinant=det)
    if kind!='curvature_extremum':raise Unsupported('Unknown source curvature question')
    source_fields(task,{'curve','domain','positive_parameters','maximum_curvature','requested','source_domain_note','requested_output'},
        ('Найти точку кривой с наибольшей кривизной.',
         'По максимальной кривизне найти абсциссу, в которой она достигается.'))
    match=re.fullmatch(r'y=(?:('+NUMBER[1:-1]+r')\*)?ln\(x\)',raw)
    if match and not set(task)-{'id','kind','source','curve','domain','requested_output'} and task['domain']=='x>0':
        requested(task,'point_of_greatest_curvature')
        a=F(match[1]) if match[1] else F(1)
        if not a:raise Unsupported('The logarithmic graph is a horizontal line')
        x0=m.div(q(abs(a)),root(q(2)));y0=times(q(a),('ln',x0))
        return proof('curvature_sign_decomposition',[
            'Graph curvature is |a|x/(a²+x²)^(3/2) on its original positive domain.',
            'Its derivative has the sign of a²−2x². The unique sign change from positive to negative gives the global maximizer.'],
            dict(point=[x0,y0]),derivative_sign_factor=diff(q(a*a),times(q(2),squared(x))))
    match=re.fullmatch(r'y=([A-Za-z]\w*)\*x\^([3-9]\d*|[12]\d+)/([1-9]\d*)',raw)
    if (not match or task['domain']!='0<=x<+inf' or task.get('positive_parameters')!=[match[1]]
            or task.get('requested')!='x' or 'maximum_curvature' not in task or 'requested_output' in task):
        raise Unsupported('Need a positive monomial graph on the specified ray and a prescribed maximum')
    k=s(match[1]);p,d=map(int,match.groups()[1:]);K=F(str(task['maximum_curvature']))
    if p>40 or K<=0 or k==x:raise Unsupported('Source scale or exponent is outside the proven setting')
    slope=times(q(F(p,d)),k,m.power(x,p-1));s2=F(p-2,2*p-1);t=plus(ONE,q(s2))
    x0=m.div(times(q(F(p-1,K)),root(q(s2))),times(t,root(t)))
    return proof('curvature_sign_decomposition',[
        'With s=y′>0, curvature is (p−1)s/[x(1+s²)^(3/2)] on x>0.',
        'The sign of the derivative is the sign of (p−2)−(2p−1)s². The slope grows strictly from zero to infinity.',
        'The endpoint curvature is zero. At the unique positive maximizer insert the critical slope and divide by the given positive maximum.'],
        dict(x=x0),slope=slope,critical_slope_squared=q(s2),maximum=q(K))


def flat_contact(task):
    source_fields(task,{'variable','function','other_curve'},
        ('Доказать бесконечный порядок касания с осью Ox в x=0.',))
    f=task['function'];x=task['variable']
    if not isinstance(f,dict) or set(f)!={'off_zero','at_zero'} or f['at_zero']!='0' or task['other_curve']!='0':
        raise Unsupported('Match both plateau values and the horizontal comparison curve')
    match=re.fullmatch(r'exp\(-'+NUMBER+r'/'+re.escape(x)+r'\^([1-9]\d*)\)',text_key(f['off_zero']))
    if not match:raise Unsupported('Need an exponential with an inverse even-power negative phase')
    c,p=F(match[1]),int(match[2])
    if c<=0 or p%2:raise Unsupported('The phase must tend to minus infinity from both directions')
    return proof('exponential_flat_extension',[
        'Put t=1/x on the punctured line. Each derivative is a polynomial in t times exp(−c t^p): differentiate using d/dx=−t² d/dt.',
        'For positive c and even p the exponential dominates every polynomial at both infinities. This holds as well after multiplying by t.',
        'Induction using the difference quotient at zero proves that every derivative exists and vanishes there.'],
        dict(point=ZERO,all_derivatives=ZERO,contact_order='infinite'),phase_coefficient=q(c),even_power=p)


def phase_endpoint(multiplier,inward):
    """A rational point certified to lie just within the stated phase cell."""
    p0,p1=enclose(P,None)
    b=sorted((multiplier*p0,multiplier*p1))
    return b[1]+F(1,10**8) if inward>0 else b[0]-F(1,10**8)


def numerical_roots(task):
    source_fields(task,{'equation','variable','requested_roots','absolute_error','method','section_context'},
        ('Пользуясь методом Ньютона, определить корни с указанной точностью.',
         'С указанной точностью найти три первых положительных корня.',
         'С указанной точностью найти два положительных корня.'))
    variable=task['variable'];eq=text_key(task['equation']);mode=task['method'];asked=task['requested_roots']
    if not re.fullmatch(r'[A-Za-z]\w*',variable):raise Unsupported('Invalid root variable')
    eq=re.sub(r'\b'+re.escape(variable)+r'\b','x',eq)
    tol=F(str(task['absolute_error']))
    if not F(1,10**10)<=tol<=F(1,4) or mode not in ('newton','unspecified'):
        raise Unsupported('Need a supported certified absolute accuracy and method')
    literal=task.get('source',{}).get('literal_requirement','')
    if ('Ньютон' in literal)!=(mode=='newton') and literal:
        raise Unsupported('The numerical method conflicts with the original instruction')
    if 'три первых' in literal and asked!='first three positive' or 'два положительных' in literal and asked!='two positive':
        raise Unsupported('The requested root counts disagree with the source')
    reflect=False
    log_equation=re.fullmatch(r'x\*log([1-9]\d*)\(x\)='+NUMBER,eq)
    if log_equation and asked=='all real':
        base=int(log_equation[1]);target=F(log_equation[2])
        if base<=1 or target<=0:raise Unsupported('The base and target do not give the required positive logarithmic branch')
        f=f'x*ln(x)-({target})*ln({base})';dd='ln(x)+1'
        formula=m.parse(f,'x');bound=F(2)
        while bound<=128 and strict_sign(enclose(formula,(bound,bound)))!=1:bound*=2
        if bound>128:raise Unsupported('Unable to certify a finite positive logarithmic root bracket')
        regions=[(F(1),bound,f,dd)]
        why='For 0<x<1 the original logarithm is negative. Beyond 1 the product grows strictly and crosses the given positive target.'
    elif eq=='x*tanh(x)=1' and asked=='all real':
        regions=[(F(0),F(2),'x*(exp(2*x)-1)/(exp(2*x)+1)-1',
                    '(exp(2*x)-1)/(exp(2*x)+1)+4*x*exp(2*x)/(exp(2*x)+1)^2')]
        reflect=True
        why='The original expression is even and is strictly increasing on the positive axis, as x and tanh(x) are increasing and positive there.'
    elif eq=='cos(x)*cosh(x)=1' and asked=='two positive':
        f='cos(x)*(exp(x)+exp(-x))/2-1'
        d='(cos(x)*(exp(x)-exp(-x))-sin(x)*(exp(x)+exp(-x)))/2'
        regions=[(phase_endpoint(F(3,2),1),phase_endpoint(2,-1),f,d),
                 (phase_endpoint(2,1),phase_endpoint(F(5,2),-1),f,d)]
        why=('Near zero cos(x)cosh(x) decreases since tan(x)>tanh(x). In the first subsequent positive cosine lobe '
             'the product first increases; on the right half, tan(x)−tanh(x) increases through zero exactly once. '
             'The product exceeds one at the midpoint, so there is one crossing on either side.')
    elif eq=='tan(x)=x' and asked=='first three positive' and mode=='unspecified':
        regions=[(phase_endpoint(j,1),phase_endpoint(F(2*j+1,2),-1),
                  f'sin(x-{j}*pi)-x*cos(x-{j}*pi)',f'x*sin(x-{j}*pi)') for j in range(1,4)]
        why=('The original tangent is negative on the intervening positive half-cells. In the initial positive half-cell '
             'tan(x)>x. In each subsequent positive half-cell tan(x)−x increases from a negative number to infinity.')
    elif eq=='cot(x)=1/x-x/2' and asked=='two positive' and mode=='unspecified':
        f='x*cos(x)-(1-x^2/2)*sin(x)';d='x^2*cos(x)/2'
        regions=[(phase_endpoint(a,1),phase_endpoint(b,-1),f,d)
                 for a,b in ((F(1,2),1),(F(3,2),2))]
        why=('Multiplication by x sin(x) preserves roots within the open cells. The derivative of the transformed expression '
             'has the sign of cos(x). The values at the bounding integer and half-integer multiples of pi isolate two admissible positive roots.')
    else:raise Unsupported('The original equation does not fit the supported sign cells and root count')
    answers=[];steps=[]
    for a,b,f,d in regions:
        ff,dd=m.parse(f,'x'),m.parse(d,'x')
        ev=lambda t:enclose(ff,(t,t))
        der=lambda t:enclose(dd,(t,t))
        ans,trace=refine_root_bracket(ev,der,a,b,tol,mode)
        if mode=='newton' and not any(z.get('method')=='newton' for z in trace['iterations']):
            raise Unsupported('The certified bracket must contain an actual Newton step')
        answers.append(ans);steps.append(dict(trace,residual=ff,derivative=dd))
    if reflect:
        a=answers[0]
        answers.insert(0,dict(a,approximation=m.neg(a['approximation'])))
    return proof('root_sign_cells_and_iterations',[
        why,'Evaluate the original or equivalent residual on certified rational interior points, preserving all initial poles.',
        'Refine a sign-changing bracket by the required method and check the absolute error against its endpoints.'],
        dict(roots=answers,absolute_tolerance=q(tol)),brackets=steps,reflection=reflect)


def radical_moments(ratio,scale,accuracy):
    """Enclose the normalized integral of sqrt(1-ratio*sin(t)^2) on a quadrant."""
    if not 0<=ratio<1:raise Unsupported('The original ellipse must be nondegenerate')
    A,B=enclose(scale,None)
    if A<=0:raise Unsupported('A positive metric scale is required')
    term=ratio/4;total=F(0)
    for j in range(1,129):
        total+=term
        term*=ratio*F((2*j-1)*(2*j+1),4*(j+1)**2)
        lo=A*(1-total-term/(1-ratio));hi=B*(1-total)
        if lo>0 and hi-lo<=accuracy/4:return lo,hi,j
    raise Unsupported('The certified radical moment tail exhausts the available order')


def numeric_length(task):
    source_fields(task,{'accuracy','function','interval','curve','semiaxes','span','sag','model'},(
        'Найти с точностью до 0,01 длину дуги одной полуволны синусоиды.',
        'Найти с точностью до 0,01 длину дуги эллипса с данными полуосями.',
        'Найти длину параболического провода с точностью до 1 см.'))
    fields=set(task)-{'id','kind','source','accuracy'};units=None;count=None
    accuracy=str(task['accuracy'])
    if fields=={'function','interval'}:
        tol=F(accuracy);f=text_key(task['function'])
        match=re.fullmatch(r'(?:'+NUMBER+r'\*)?sin\(x\)',f)
        if not match or task['interval']!=['0','pi']:
            raise Unsupported('Need a sine graph on its original whole half-wave')
        a=F(match[1]) if match[1] else F(1)
        major=1+a*a;ratio=a*a/major;scale=times(P,root(q(major)))
        lo,hi,count=radical_moments(ratio,scale,tol)
        metric='Factor sqrt(1+a²) from the positive speed sqrt(1+a² cos²(x)) over [0,pi].'
        exact=None
    elif fields=={'curve','semiaxes'} and task['curve']=='ellipse':
        tol=F(accuracy);a,b=sorted((F(str(u)) for u in task['semiaxes']),reverse=True)
        if b<=0:raise Unsupported('Both ellipse semiaxes must be positive')
        ratio=1-b*b/(a*a);scale=times(q(2*a),P)
        lo,hi,count=radical_moments(ratio,scale,tol)
        metric='Use the regular elliptical parametrization and four identical quadrant arcs for the whole perimeter.'
        exact=None
    elif fields=={'span','sag','model'} and task['model']=='parabolic wire between equal-height supports':
        span=re.fullmatch(r'2\*l='+NUMBER+r' m',task['span'])
        sag=re.fullmatch(r'h='+NUMBER+r' cm',task['sag'])
        ac=re.fullmatch(NUMBER+r' m',accuracy)
        if not span or not sag or not ac:raise Unsupported('Match length, sag, and tolerance with their original units')
        l=F(span[1])/2;h=F(sag[1])/100;tol=F(ac[1]);units='m'
        if l<=0 or h<=0:raise Unsupported('Nonpositive span or sag needs a different geometry')
        u=2*h/l
        exact=times(q(2*l/u),root_power_primitive(q(u),0))
        lo,hi=enclose(exact,None)
        metric='Put the vertex at the origin. By symmetry use twice the metric integral on [0,l]. The slope is 2hx/l².'
    else:raise Unsupported('The source does not name the full regular arc with all required lengths')
    if tol<=0:raise Unsupported('The reported accuracy must be positive')
    grid=1
    while F(1,grid)>tol:grid*=10
    result=F(round(grid*(lo+hi)/2),grid);err=max(abs(result-lo),abs(result-hi))
    if err>tol:raise Unsupported('The requested rounding is wider than the proven interval')
    steps=[metric,
           'Integrate the binomial sine-power moments using a geometric bound on the tail.' if count is not None else
           'Substitute the graph slope and use the checked primitive of the positive radical metric.',
           'Enclose the resulting length independently and include the rounding error.']
    return proof('regular_curve_length_error',steps,dict(length=q(result),absolute_error=q(err),unit=units),
        certified_interval=[q(lo),q(hi)],terms=count,exact=exact)


def surface_invariance(task):
    source_fields(task,{'given','requested_output'},('Исследовать характер поверхности.',))
    requested(task,'surface_classification')
    raw=text_key(task['given'])
    if raw=='z=f(sqrt(x^2+y^2))':
        return proof('geometric_invariant_fibers',[
            'The argument of f is the Euclidean radius in the horizontal plane, unchanged by every rotation about the vertical axis.',
            'At every admissible nonnegative radius the entire original circle is present. The surface is generated by rotating the meridian.'],
            dict(type='surface of revolution',axis='Oz',domain='rho>=0 and f(rho) is defined'))
    match=re.fullmatch(r'z=f\(y-([A-Za-z]\w*)\*x\)',raw)
    if match and match[1] not in ('x','y','z'):
        a=match[1]
        return proof('geometric_invariant_fibers',[
            'Holding the argument y−ax fixed leaves the graph height fixed.',
            'Each admissible level admits all translations along the same nonzero direction (1,a,0).'],
            dict(type='cylindrical surface',direction=[ONE,s(a),ZERO],domain=f'f(y-{a}*x) defined'))
    if raw not in ('z=f(y/x)','z=x*f(y/x)'):raise Unsupported('No complete line or rotation family was found')
    cone=raw.startswith('z=x*')
    return proof('geometric_invariant_fibers',[
        'The original source requires x≠0. On every fiber of y/x=t, substitute y=tx.',
        'The branch is parametrized by x(1,t,f(t)) for x≠0 and any admissible t.' if cone
        else 'The branch is parametrized by (x,tx,f(t)) for x≠0 and any admissible t.',
        'The generators meet at the origin after closure; the source quotient gives no value there.' if cone else
        'The nonvertical generators lie in horizontal planes. The excluded line x=0 is retained.'],
        dict(type='cone' if cone else 'ruled surface',generator='x*(1,t,f(t))' if cone else '(x,t*x,f(t))',
             domain='x != 0 and f(y/x) defined'))


def functional_fibers(task):
    source_fields(task,{'given','arguments','requested_output'},
                  ('Найти f(1,y/x).','Найти f(x).','Определить f и z.','Найти f и z.','Найти f(x,y).'))
    raw=text_key(task['given'])
    head=task.get('source',{}).get('literal_requirement')
    outputs={}
    if raw=='f(x,y)=2*x*y/(x^2+y^2)':
        if task.get('arguments') not in (None,['1','y/x']):raise Unsupported('The given function needs the actual requested arguments')
        requested(task,'value_at_arguments')
        expected='Найти f(1,y/x).';expr='2*x*y/(x^2+y^2)';domain='x != 0, y real'
        step='Substitute (1,y/x) into the original function and clear the nonzero x². Its original slope entry requires x≠0.'
    elif raw=='f(y/x)=sqrt(x^2+y^2)/x,x>0':
        expected='Найти f(x).';expr='sqrt(1+t^2)';domain='all real t'
        step='Because x>0, the original square root is x sqrt(1+(y/x)²). Every slope is attained by x=1.'
    elif raw=='z=sqrt(y)+f(sqrt(x)-1);z=xaty=1':
        expected='Определить f и z.';expr='(t+1)^2-1';domain='t >= -1'
        outputs.update(z='x+sqrt(y)-1',z_domain='x>=0,y>=0')
        step='On the named slice y=1 the argument t=sqrt(x)−1 has exact image [−1,+∞); its inverse is x=(t+1)².'
    elif raw=='z=x+y+f(x-y);z=x^2aty=0':
        expected='Найти f и z.';expr='t^2-t';domain='all real t'
        outputs.update(z='(x-y)^2+2*y',z_domain='all real x,y')
        step='On y=0 the argument is x itself. Every real t is attained and subtraction of the known term isolates f.'
    elif raw=='f(x+y,y/x)=x^2-y^2':
        expected='Найти f(x,y).';expr='u^2*(1-v)/(1+v)';domain='u != 0,v != -1, or (u,v)=(0,-1) with value 0'
        step='For v≠−1 invert u=x(1+v), with x≠0, then substitute. For v=−1 the image consists only of u=0, and x²−y² is identically zero on that fiber.'
    else:raise Unsupported('The given relation does not match a proven fiber identity')
    if expected!='Найти f(1,y/x).':
        if 'arguments' in task:raise Unsupported('The original unknown function is not a value at new supplied arguments')
        requested(task,'unknown_function',*(['surface_function'] if outputs else []))
    if head not in (None,expected):raise Unsupported('The same input cannot replace the requested original function value')
    return proof('invert_variable_on_its_image',[
        step,'Check the derived expression against the original function relation on every attained input and keep unattained inputs free.'],
        dict(function=expr,determined_domain=domain,**outputs))


def level_lattice(task):
    kind=task['kind']
    if kind=='discontinuity_set':
        source_fields(task,{'given','requested_output'},('Найти точки разрыва.',))
        requested(task,'natural_domain','discontinuity_set')
        if text_key(task['given'])!='1/(sin(x)*sin(y))':raise Unsupported('Need the original product of sine denominators')
        return proof('attainable_phase_lattice',[
            'The reciprocal is continuous on every connected cell in which both sine factors are nonzero.',
            'Each excluded line is approached by points of the natural domain with denominator tending to zero; the reciprocal has no finite continuous extension there.'],
            dict(domain='x not in pi*Z and y not in pi*Z',singular_set=['x in pi*Z','y in pi*Z']))
    source_fields(task,{'function','variables','parameters','stated_conditions','level_parameter','requested_output'},(),('printed_instruction',))
    if task.get('source',{}).get('printed_instruction') not in (None,'Найти поверхности уровня следующих функций'):
        raise Unsupported('Bind the complete printed radial level request')
    axes=task['variables'];c=task['level_parameter']
    if (not isinstance(axes,list) or len(axes)<2 or len(set(axes))!=len(axes)
            or c in axes or any(not re.fullmatch(r'[A-Za-z]\w*',v) for v in axes+[c])
            or task['parameters'] or task['stated_conditions'] or task['requested_output']!=['all_level_sets']):
        raise Unsupported('Need all levels of the original unrestricted radial phase')
    if text_key(task['function'])!='sign(sin('+'+'.join(v+'^2' for v in axes)+'))':
        raise Unsupported('The attainable phase must be a sum of the original unrestricted coordinate squares')
    return proof('attainable_phase_lattice',[
        'The radial phase r² attains precisely the nonnegative reals. For each integer k≥0 its phase intervals alternate sign.',
        'Intersect every sine phase cell with [0,+∞) before taking its radial preimage; keep the origin in the zero fiber.'],
        dict(level=c,positive='2*k*pi<r^2<(2*k+1)*pi',negative='(2*k+1)*pi<r^2<(2*k+2)*pi',
             zero='r^2=k*pi',index='k=0,1,2,...',all_other_levels='empty'),coordinates=axes)


ITERATED='Найти оба повторных предела в указанном порядке.'
ITERATED_EXPLICIT='Найти оба повторных предела: сначала y→b, затем x→a; затем в обратном порядке.'
FINITE_DIRECTIONS='Для каких направлений φ существует конечный предел?'


def xy_limits(task):
    source_fields(task,{'given','requested_output','printed_assertion','approach'},(ITERATED,ITERATED_EXPLICIT,FINITE_DIRECTIONS,
        'Доказать, что оба повторных предела в начале не существуют, но общий предел 0.',
        'Существует ли совместный предел при x,y→0?',
        'Найти предел на каждом луче t→+∞. Является ли f бесконечно малой при x,y→+∞?'))
    raw=text_key(task['given']);head=task.get('source',{}).get('literal_requirement')
    if raw in ('f=(x+y)*sin(1/x)*sin(1/y)','(x+y)*sin(1/x)*sin(1/y)'):
        expected='Доказать, что оба повторных предела в начале не существуют, но общий предел 0.'
        requested(task,'prove_claim_about_joint_and_two_iterated_limits')
        if task.get('printed_assertion') not in (None,'both iterated limits do not exist while the joint limit as x,y→0 equals 0'):
            raise Unsupported('The printed assertion does not agree with the proof goal')
        steps=['The original coordinate domain omits x=0 and y=0. Its absolute value is bounded by |x+y|.',
            'Fix a small y with y sin(1/y)≠0. Paths of positive x resolving the reciprocal phase to pi/2 and 3pi/2 yield opposite nonzero inner limits.',
            'Such fixed y occur in every punctured neighborhood; symmetry gives the missing inner limit in the other order.']
        value=dict(joint_limit=ZERO,inner_y='not defined on a punctured neighborhood',inner_x='same by symmetry')
    elif raw=='2*x*y/(x^2+y^2)':
        expected='Существует ли совместный предел при x,y→0?'
        requested(task,'joint_limit_existence_and_value')
        if task.get('approach') not in (None,'x→0,y→0 jointly'):raise Unsupported('Both approaches must be to the original origin')
        steps=['Both y=x and y=0 with x≠0 satisfy the original nonzero denominator.',
               'The restrictions equal one and zero respectively, so a joint limit is impossible.']
        value=dict(joint_limit='does not exist',path_values=[ONE,ZERO])
    elif raw=='f=x^2*exp(-(x^2-y));rayx=t*cos(alpha),y=t*sin(alpha),0<=t<infinity':
        expected='Найти предел на каждом луче t→+∞. Является ли f бесконечно малой при x,y→+∞?'
        requested(task,'limit_along_every_ray','joint_infinitesimality_at_positive_infinity')
        steps=['On each ray with nonzero cos(alpha), the negative quadratic exponential term dominates the linear term and the polynomial prefactor.',
               'When cos(alpha)=0 the prefactor is zero. Yet the admissible parabola y=x² with x→+∞ gives x², disproving a joint limit of zero.']
        value=dict(all_ray_limits=ZERO,joint_infinitesimal=False,counterpath='y=x^2')
    elif raw=='exp(x/(x^2+y^2));x=rho*cos(phi),y=rho*sin(phi),rho→+0':
        expected=FINITE_DIRECTIONS
        requested(task,'directions_with_finite_limit','finite_limit_value')
        steps=['For rho>0 the source denominator is rho² and the exact exponent is cos(phi)/rho.',
               'Split the constant coefficient by its sign and apply the ordinary exponential limits.']
        value=dict(finite_directions='cos(phi)<=0',limits={'cos(phi)<0':ZERO,'cos(phi)=0':ONE},
                   infinite='cos(phi)>0')
    elif raw=='exp(x^2-y^2)*sin(2*x*y);samepolarsubstitution,rho→+infty':
        expected=FINITE_DIRECTIONS
        requested(task,'directions_with_finite_limit','finite_limit_value')
        steps=['The specified polar phase and exponent reduce to rho² sin(2phi) and rho² cos(2phi).',
               'A zero phase gives the identically zero function; a negative exponential coefficient gives a squeezed limit of zero.',
               'For nonzero phase choose sequences attaining opposite extrema. At exponent coefficient zero or positive the limit is not finite.']
        value=dict(finite_directions='sin(2*phi)=0 or cos(2*phi)<0',limit=ZERO)
    else:
        raw,delimiter,centers=raw.partition(';')
        if not delimiter:raise Unsupported('Two original iteration targets were not specified')
        expected=(ITERATED,ITERATED_EXPLICIT)
        requested(task,'both_ordered_iterated_limits')
        if raw=='(x^2+y^2)/(x^2+y^4)' and centers=='a=infty,b=infty':
            first,second=ZERO,ONE
            steps=['Fix x and divide numerator and denominator by y⁴ on the inner positive tail.',
                   'In reverse fix y and divide by x². All tails avoid the joint zero of the sum-of-squares denominator.']
        elif raw=='x^y/(1+x^y)' and centers=='a=infty,b=+0':
            first,second=q(F(1,2)),ONE
            steps=['Fix x>0 first: x^y=exp(y ln x) tends to one from the positive y branch.',
                   'In reverse fixed y>0 makes x^y grow without bound on the positive x tail; divide by x^y.']
        elif raw=='sin(pi*x/(2*x+y))' and centers=='a=infty,b=infty':
            first,second=ZERO,ONE
            steps=['The affine denominator is nonzero eventually on each of the fixed-variable slices.',
                   'In one order the argument tends to zero by dividing by y; in the other it tends to pi/2 by dividing by x. Use continuity of sine.']
        elif raw=='tan(x*y/(1+x*y))/(x*y)' and centers=='a=0,b=infty':
            first,second=ZERO,ONE
            steps=['Set u=xy with the original guards u≠0, u≠−1 and cos(u/(1+u))≠0; each relevant tail or punctured interval satisfies them.',
                   'With fixed nonzero x as y grows, |u| grows and tan(u/(1+u)) stays finite near tan(1). In the reverse order u tends to zero and tan(v)/v tends to one for v=u/(1+u).']
        elif raw=='log_base(x,x+y)' and centers=='a=1,b=0':
            first,second=ONE,'does not exist'
            steps=['The base-change quotient is ln(x+y)/ln(x), with x>0, x≠1, and x+y>0.',
                   'For fixed x≠1, y→0 gives one. In reverse, for each sufficiently small fixed y≠0 the numerator approaches a nonzero value while ln(x) has opposite signs on the two sides.']
        else:raise Unsupported('The original two limits do not match supported fixed-variable reductions')
        steps.append('The outer operation preserves each proved constant inner limit.')
        value=dict(y_then_x=first,x_then_y=second)
    if head not in (None,*(expected if isinstance(expected,tuple) else (expected,))):
        raise Unsupported('A different arrangement of the source limits changes the requested proof')
    if 'printed_assertion' in task and expected!='Доказать, что оба повторных предела в начале не существуют, но общий предел 0.':
        raise Unsupported('The given joint and repeated limits do not assert an extra condition')
    if 'approach' in task and expected!='Существует ли совместный предел при x,y→0?':
        raise Unsupported('The asserted approach must match the request')
    return proof('axis_limits_and_attainable_paths',steps,value,source_formula=task['given'])


def envelope(task):
    source_fields(task,{'source_formula','stated_conditions','requested_output'},('find_envelope',))
    match=re.fullmatch(r'spheresofradius([A-Za-z]\w*)centeredonconex\^2\+y\^2=z\^2',text_key(task['source_formula']))
    if not match or match[1] in ('x','y','z') or task['stated_conditions'] or task['requested_output']!=['find_envelope']:
        raise Unsupported('Need a positive-radius sphere with centers on the specified double cone')
    rho=s(match[1]);d=m.div(rho,root(q(2)))
    return proof('offset_normal_geometry',[
        'For a smooth point Q on either nappe, differentiate |P−Q|²=rho² with respect to both center coordinates.',
        'The difference P−Q is orthogonal to both tangent directions, so it equals rho times one of the two unit normals.',
        'Retain the signed planar radius when the offset crosses the axis. The vertex has no unique normal; include the limits from smooth center points.',
        'If the geometric exterior is required, minimize the distance to centers over the horizontal angle and then over the nonnegative generator coordinate. The latter is (r+|z|)/2.'],
        dict(center='(s*cos(phi),s*sin(phi),epsilon*s), s>0,epsilon=+-1',
             regular_envelope='((s+delta)*cos(phi),(s+delta)*sin(phi),epsilon*(s-delta))',
             offset_parameter=[d,m.neg(d)],conditions=[('positive',rho)],vertex_center='smooth-center limits',
             distance_to_center_set='abs(sqrt(x^2+y^2)-abs(z))/sqrt(2)',
             exterior_boundary='abs(sqrt(x^2+y^2)-abs(z))=sqrt(2)*rho'))


def triangle_section_width(base,altitude,height):
    return times(base,diff(ONE,m.div(height,altitude)))


def applied_metric(task):
    source_fields(task,{'given','requested_output'},(
        'Найти прямоугольник наибольшего периметра и исследовать возможность решения.',
        'Найти минимальное расстояние между кораблями.'))
    raw=text_key(task['given']);head=task.get('source',{}).get('literal_requirement')
    if raw=='rectangleinscribedintriangleofbasebandaltitudeh':
        requested(task,'maximal_perimeter_rectangle','attainment_and_possibility')
        if head not in (None,'Найти прямоугольник наибольшего периметра и исследовать возможность решения.'):
            raise Unsupported('Need the original perimeter and its attainment')
        b,h,y=map(s,('b','h','height'));width=triangle_section_width(b,h,y)
        return proof('metric_extremum_with_attainment',[
            'On a fixed side of length b the opposite line cuts a section of width b(1−y/h) by similarity.',
            'A one-sided inscribed rectangle exists throughout 0<y<h precisely when the altitude foot lies in this side. If it does not, a section endpoint projects outside the side for every positive height.',
            'Twice width plus height is affine. If b=h it is constant; otherwise its supremum occurs at a degenerate endpoint.',
            'If all three sides are allowed as bases, apply the result to the two further sides with the same altitude test. Their lengths and altitudes need the third vertex position, which is not fixed by b,h.'],
            dict(width=width,perimeter=times(q(2),plus(width,y)),perimeter_supremum='2*max(b,h) on the admissible fixed base',
                 attained='all heights 0<height<h when b=h and the altitude foot belongs to the base',
                 additional_bases='test the corresponding third vertex projection'))
    if raw!='twoshipswithconstantsspeedsu,vonintersectingstraightlinesatangletheta;currentdistancesfromcrossinga,b':
        raise Unsupported('The source does not give supported trajectory geometry')
    requested(task,'minimum_distance')
    if head not in (None,'Найти минимальное расстояние между кораблями.'):
        raise Unsupported('A different relative-motion question was requested')
    A,B,U,V=map(s,('signed_a','signed_b','signed_u','signed_v'));c=('cos',s('theta'))
    position=plus(squared(A),squared(B),times(q(-2),c,A,B))
    velocity=plus(squared(U),squared(V),times(q(-2),c,U,V))
    mixed=plus(times(A,U),times(B,V),m.neg(times(c,plus(times(A,V),times(B,U)))))
    t0=m.neg(m.div(mixed,velocity));t=('max',ZERO,t0)
    return proof('metric_extremum_with_attainment',[
        'Take signed coordinates on the two directed lines. The relative displacement is linear in time.',
        'Minimize its squared norm P+2Bt+Dt². When D>0 it is strictly convex and has stationary time −B/D; constrain it to the future half-line.',
        'If D=0 the relative velocity vanishes and the distance is constant. The unsigned distances and speeds alone do not specify the signs of the actual positions and velocities.'],
        dict(distance=root(plus(position,times(q(2),mixed,t),times(velocity,squared(t)))),
             future_time=t,unrestricted_time=t0,zero_relative_velocity=root(position),
             necessary_data='signed initial distances and signed velocities'),quadratic=[position,mixed,velocity])


SOURCE_ROUTES={
    'construct_graph':continuity_from_phase,
    'continuity_original_expression':continuity_from_phase,
    'pointwise_limit_continuity_graph':geometric_power_limits,
    'dense_piecewise_continuity_graph':dense_source_continuity,
    'piecewise_continuity':elementary_piecewise,
    'continuous_parameter_fit':elementary_piecewise,
    'piecewise_continuity_classification':elementary_piecewise,
    'nested_limit_dirichlet_proof':dirichlet_continuity,
    'proof_about_real_functions':dirichlet_continuity,
    'distance_function_continuity_graph':distance_union,
    'cross_section_area_width_graph':swept_area,
    'polar_curvature_formula':curvature,
    'curvature_identity':curvature,
    'curve_curvature_radius':curvature,
    'curvature_extremum':curvature,
    'infinite_contact_proof':flat_contact,
    'approximate_equation_roots':numerical_roots,
    'numeric_arc_length':numeric_length,
    'surface_classification':surface_invariance,
    'functional_equation':functional_fibers,
    'level_sets':level_lattice,
    'discontinuity_set':level_lattice,
    'multivariable_limit':xy_limits,
    'applied_extremum':applied_metric,
    'surface_envelope':envelope,
}


def contact_conditions(task):
    kind=task['kind'];raw=text_key(task['curve']);x=s('x')
    if kind=='intersection_angle_proof':
        source_fields(task,{'curve','hypotheses'},('Доказать, что острые углы пересечения параболы с Ox равны.',))
        if raw!='y=a*(x-x1)*(x-x2)' or task['hypotheses']!=['a!=0','x1<x2','0<alpha,beta<pi/2']:
            raise Unsupported('The two simple roots and the acute angle convention must be bound')
        d=times(s('a'),diff(s('x2'),s('x1')))
        return proof('contacts_by_matching_jets',[
            'At each simple root differentiate the factored parabola. The two slopes are opposite and nonzero.',
            'The acute unsigned angle with the axis has tangent equal to the absolute slope.'],
            dict(equal=True,angle=('atan',absolute(d))),slopes=[m.neg(d),d])
    source_fields(task,{'curve','hypotheses'},(
        'При каком соотношении парабола касается Ox?','При каком условии кривая касается Ox?',
        'При каком a есть касание?','Доказать касание в общих точках.',
        'Доказать ортогональность сети гипербол.','Доказать ортогональность сети парабол.'))
    heading=task.get('source',{}).get('literal_requirement');extra=task.get('hypotheses')
    if raw=='y=a*x^2+b*x+c':
        need='При каком соотношении парабола касается Ox?'
        steps=['The root and zero-slope equations must hold at the same point.',
               'Since the leading coefficient of a parabola is nonzero, solve the slope equation and substitute in the curve.']
        A,B,C=map(s,'abc')
        val=dict(condition=('zero',diff(squared(B),times(q(4),A,C))),point=[m.div(m.neg(B),times(q(2),A)),ZERO],
                 leading_coefficient=('nonzero',A))
    elif raw=='y=x^3+p*x+q':
        need='При каком условии кривая касается Ox?'
        steps=['At a contact root t the two equations give p=−3t² and q=2t³.',
               'Eliminate t; conversely the discriminant relation either gives the triple zero or recovers the real repeated root.']
        p,h=map(s,'pq')
        val=dict(condition=('zero',plus(times(q(4),m.power(p,3)),times(q(27),squared(h)))),
                 root_in_nonzero_case=m.div(times(q(-3,2),h),p),triple_root=ZERO)
    elif raw=='y=a*x^2andy=ln(x)':
        need='При каком a есть касание?'
        steps=['The common point must satisfy x>0. Equating slopes gives a x²=1/2.',
               'Match the actual ordinates, solve ln(x)=1/2 and substitute back into both symbolic equations.']
        x0=('exp',q(1,2));A0=m.div(ONE,times(q(2),('exp',ONE)))
        val=dict(parameter=A0,contact=[x0,q(1,2)])
    elif raw=='y=f(x)>0andy=f(x)*sin(a*x)' and extra==['f differentiable','f(x)>0']:
        need='Доказать касание в общих точках.'
        steps=['Since the first graph is positive, identical ordinates require sin(ax)=1.',
               'Consequently cos(ax)=0. The product derivative at every common point equals f′ on its original differentiability domain.']
        val=dict(tangent_at_every_intersection=True,common_argument='sin(a*x)=1')
    elif raw=='x^2-y^2=aandxy=b':
        need='Доказать ортогональность сети гипербол.'
        y=s('y');normals=([times(q(2),x),times(q(-2),y)],[y,x])
        steps=['Use the gradient of each original level as a normal. Their exact scalar product is zero.',
               'Both normals are nonzero away from the origin, which is not a regular hyperbola intersection.']
        val=dict(normals=normals,angle=m.div(P,q(2)),regular_condition='x^2+y^2>0')
    elif raw=='y^2=4a(a-x),a>0;y^2=4b(b+x),b>0':
        need='Доказать ортогональность сети парабол.'
        a,b,y=map(s,'aby')
        steps=['Subtract the two original equations and divide by a+b>0. The common coordinate is x=a−b, with y²=4ab.',
               'Both normals are nonzero. Their scalar product is −16ab+4y², which vanishes at either original intersection.']
        val=dict(intersections=[[diff(a,b),times(q(e),root(times(q(4),a,b)))] for e in (-1,1)],angle=m.div(P,q(2)),
                 normals=[[times(q(4),a),times(q(2),y)],[times(q(-4),b),times(q(2),y)]])
    else:raise Unsupported('The original contact or intersection has no admitted jet matching')
    if heading not in (None,need) or extra is not None and need!='Доказать касание в общих точках.':
        raise Unsupported('The output and all regularity conditions must match the source')
    return proof('contacts_by_matching_jets',steps,val)


def secant_directions(task):
    kind=task['kind'];x=s('x')
    if kind=='tangent_angle_parameter':
        source_fields(task,{'curve','hypotheses','threshold_degrees'},('Найти n>0, чтобы угол с осью Ox был больше 89°.',))
        angle=F(str(task['threshold_degrees']));head=task.get('source',{}).get('literal_requirement')
        if text_key(task['curve'])!='atan(n*x)' or task['hypotheses']!=['n>0'] or not 0<angle<90 or head and angle!=89:
            raise Unsupported('Bind the original parameter, angle units and strict threshold')
        limit=('tan',times(q(angle/180),P))
        return proof('secant_tangent_directions',[
            'The arctangent graph with positive parameter crosses only the origin and has positive slope n there.',
            'The acute angle is atan(n), strictly increasing; convert the given degree measurement before inverting.'],
            dict(parameter='n',strict_lower_bound=limit,point=[ZERO,ZERO]))
    if kind=='tangent_limit_proof':
        source_fields(task,{'function','condition','axis','off_zero','at_zero'},(
            'Показать касание графика указанной оси.',
            'Доказать, что предельное положение секущих через A(0,1) — ось Oy.'))
        head=task.get('source',{}).get('literal_requirement')
        if set(task)-{'kind','id','source'}=={'off_zero','at_zero'} and text_key(task['off_zero'])=='abs(x)^alpha,alpha!=0' and task['at_zero']=='1':
            if head not in (None,'Доказать, что предельное положение секущих через A(0,1) — ось Oy.'):
                raise Unsupported('The original secants must use the assigned point')
            return proof('secant_tangent_directions',[
                'Use the assigned height 1 in the original secant quotient.',
                'For positive alpha its numerator tends to −1; for negative alpha it tends to positive infinity.',
                'In either case the magnitude of the slope diverges, so the unoriented line tends to the vertical axis.'],
                dict(line='Oy',secant_point=[ZERO,ONE],continuous=False))
        if (head not in (None,'Показать касание графика указанной оси.') or
                set(task)-{'kind','id','source'}!={'function','condition','axis'} or task['function']!='abs(x)^alpha'):
            raise Unsupported('The power trace with its exponent interval was not supplied')
        branch={'0<alpha<1':'Oy','1<alpha<+infinity':'Ox'}
        axis=branch.get(task['condition'])
        if axis is None or task['axis']!=axis:raise Unsupported('The requested axis does not follow from the exponent interval')
        return proof('secant_tangent_directions',[
            'The slope of the secant at the origin is sign(x)|x|^(alpha−1).',
            'The sign of alpha−1 determines whether the direction tends to vertical or horizontal.'],
            dict(line=axis,point=[ZERO,ZERO],exponent_condition=task['condition']))
    source_fields(task,{'curve','at'},('Найти угол между левой и правой касательными в точке.',))
    f=text_key(task['curve']);at=F(str(task['at']))
    if at==0 and (hit:=re.fullmatch(r'sqrt\(1-exp\(-([A-Za-z]\w*)\^2\*x\^2\)\)',f)) and hit[1]!='x':
        h=s(hit[1]);A=absolute(h);point=[ZERO,ZERO]
        steps=['Use 1−exp(−u)~u from the positive side with u=a²x².',
               'The positive square root has leading coefficient |a||x|. Keep a=0 as the constant special case.']
    elif at==1 and f=='asin(2*x/(1+x^2))':
        A=ONE;point=[ONE,m.div(P,q(2))]
        steps=['The original denominator is positive. Its distance from the upper inverse-sine endpoint is (x−1)²/(1+x²).',
               'The inverse angle difference is asymptotic to the square root of twice this distance; the height has a downward cusp.']
    else:raise Unsupported('The source point is not a checked fold of its original real branch')
    angle=times(q(2),('atan',A));ray=diff(P,angle)
    orientation=q(-1 if at==1 else 1)
    return proof('secant_tangent_directions',steps+[
        'Read each one-sided slope from the signed secant. Distinguish the outgoing rays from the unoriented tangent lines.'],
        dict(point=point,slopes=[times(m.neg(orientation),A),times(orientation,A)],
             angle_between_rays=ray,angle_between_lines=('min',angle,ray)))


def tangent_segments(task):
    kind=task['kind']
    headings=('Доказать постоянство угла между касательной и радиус-вектором.',
        'Найти длину подкасательной и дать способ построения касательной.',
        'Доказать указанное свойство параболы и дать способ построения касательной.',
        'Доказать постоянство подкасательной и дать способ построения касательной.',
        'Определить длину нормали от точки цепной линии до оси Ox.',
        'Доказать постоянство расстояния между пересечениями касательной с осями.',
        'Доказать постоянство длины отрезка касательной к трактрисе.')
    if kind=='polar_tangent_angle':
        source_fields(task,{'curve','parameters'},headings[:1])
        if text_key(task['curve'])!='r=a*exp(m*phi)' or task['parameters']!='a,m constants':
            raise Unsupported('The angular growth rate and the fixed scales must be bound')
        return proof('tangent_metric_sections',[
            'In the rotating orthonormal frame the tangent vector is (r′,r). For the original logarithmic spiral r′=m r.',
            'The ratio of components is independent of the parameter. At m=0 the tangent is perpendicular to the radius.'],
            dict(cotangent=s('m'),unoriented_cosine=m.div(absolute(s('m')),root(plus(ONE,squared(s('m'))))),
                 zero_scale='curve degenerates when a=0'))
    if kind=='tangent_segment_length':
        source_fields(task,{'curve','hypotheses'},headings[-1:])
        if list(map(text_key,task['curve']))!=['a*(ln(tan(t/2))+cos(t))','a*sin(t)'] or task['hypotheses']!=['a>0','0<t<pi']:
            raise Unsupported('The original tractrix, positivity and half-turn range are required')
        return proof('tangent_metric_sections',[
            'Along the given branch the coordinate velocities satisfy x′/y′=cot(t) away from cos(t)=0.',
            'The tangent segment reaches the axis after vertical displacement of magnitude a sin(t). Its length is a sin(t)√(1+cot²(t))=a.',
            'At t=pi/2 the first nonzero displacements give a vertical secant limit, with the same length a.'],
            dict(length=s('a'),stationary_chart_tangent='vertical at t=pi/2'))
    source_fields(task,{'curve','property','requested_output','point','condition'},headings)
    raw=text_key(task['curve']);head=task.get('source',{}).get('literal_requirement')
    x,y,a=map(s,'xya')
    if kind=='subtangent_construction' and raw=='y=a*x^n':
        need=headings[1];n=s('n');signed=m.div(x,n)
        steps=['Differentiate on a real smooth nonzero power branch. Then y/y′=x/n.',
               'The axis intersection of the tangent is x−y/y′; join it to the original point.']
        val=dict(length=absolute(signed),axis_hit=[diff(x,signed),ZERO],conditions=['a*n*x != 0','real differentiable branch'],
                 degenerate='verify zero or undefined slope separately')
    elif kind=='subtangent_construction' and raw=='y=a^x,a>0':
        need=headings[3];signed=m.div(ONE,('ln',a))
        steps=['For a>0 and a≠1, the slope is y ln(a), so division by the nonzero slope removes y.',
               'At a=1 the source curve is horizontal and has no finite intersection with the x-axis.']
        val=dict(length=absolute(signed),axis_hit=[diff(x,signed),ZERO],conditions=['a>0','a!=1'],
                 degenerate='no finite subtangent at a=1')
    elif kind=='tangent_segment_construction' and raw=='y^2=2px':
        need=headings[2];requested(task,'printed_segment_property','tangent_construction')
        prop=task['property'];p=s('p')
        if prop=='subtangent equals twice the abscissa':
            val=dict(signed_subtangent=times(q(2),x),length=times(q(2),absolute(x)))
        elif prop=='subnormal is constant':
            val=dict(signed_subnormal=p,length=absolute(p))
        else:raise Unsupported('The original geometric segment is not specified')
        val.update(axis_hit=[m.neg(x),ZERO],conditions=['p!=0','y!=0'],vertex='vertical tangent; coincident normal axis')
        steps=['On the regular branch implicit differentiation gives y′=p/y.',
               'Use y/y′ or yy′ for the directed projection and the original parabola equality. The tangent passes through (−x,0).']
    elif kind=='normal_segment_length' and raw=='y=a*cosh(x/a)' and task['point']==['x0','y0']:
        need=headings[4];y0=s('y0')
        steps=['The normal vector has direction (−y′,1). Its axis intercept uses parameter −y0.',
               'The positive hyperbolic identity gives √(1+sinh²(x0/a))=cosh(x0/a); substitute the original height.']
        val=dict(length=m.div(squared(y0),absolute(a)),conditions=['a!=0','y0=a*cosh(x0/a)'])
    elif kind=='tangent_intercept_length' and raw=='cbrt(x)^2+cbrt(y)^2=cbrt(a)^2' and task['condition']=='a>0':
        need=headings[5]
        steps=['Use the real odd-cube parameterization (a cos³(t),a sin³(t)). At nonaxial points the tangent cuts the axes at a cos(t) and a sin(t).',
               'The distance between axis intercepts is a. At an original cusp one needs the limiting intercept convention.']
        val=dict(length=a,conditions=['a>0','x*y!=0'],axis_cusps='length by branch limit')
    else:raise Unsupported('The original tangent metric construction is not supported')
    if head not in (None,need):raise Unsupported('The printed geometric requirement changed')
    allowed={'curve'}|({'property','requested_output'} if kind=='tangent_segment_construction' else
                       {'point'} if kind=='normal_segment_length' else {'condition'} if kind=='tangent_intercept_length' else set())
    if set(task)-{'id','kind','source'}-allowed:raise Unsupported('An additional geometric requirement was not checked')
    return proof('tangent_metric_sections',steps,val)


def one_coordinate_curve(task):
    printed=('Найти y′_x для заданной полярной кривой.',
             'Найти указанное отношение дифференциалов (производную одной функции по другой).')
    source_fields(task,{'coordinates','parameter','parameters','stated_conditions','orders','requested_output','polar_chart'},
                  printed,('printed_instruction','polar_data','parameter_rename'))
    var=task['parameter'];T=s(var);params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    requested(task,'derivatives_as_functions_of_parameter')
    if (task['orders']!=[1] or not isinstance(params,list) or len({var,*params})!=len(params)+1 or
            any(not re.fullmatch(r'[A-Za-z]\w*',x) for x in (var,*params))):
        raise Unsupported('Need the first original ordinate derivative, with fixed scales')
    pair=list(map(text_key,task['coordinates']))
    if len(pair)!=2:raise Unsupported('Read both original coordinates')
    origin=task.get('source',{});head=origin.get('literal_requirement')
    if origin.get('printed_instruction') not in (None,'Найти производные y′ₓ (параметры положительны), если'):
        raise Unsupported('A different source derivative instruction was supplied')
    if origin.get('parameter_rename') not in (None,'The printed variable x is renamed t; the horizontal coordinate is the original denominator function.'):
        raise Unsupported('The derivative orientation changed')
    if 'polar_chart' in task:
        chart=task['polar_chart']
        if (set(chart)!={'radius','radial_coordinate','angular_coordinate','parameter'} or
                chart['radial_coordinate']!='sqrt(x^2+y^2)' or chart['angular_coordinate']!='atan(y/x)' or
                chart['parameter']!=var or head not in (None,printed[0]) or conditions):
            raise Unsupported('Do not replace the prescribed principal arctangent chart by a global angle')
        if origin.get('polar_data') not in (None,dict(r=chart['radius'],phi=var,
                printed_definition='r=sqrt(x^2+y^2), phi=atan(y/x)')):
            raise Unsupported('The duplicate source angle and radius do not agree')
        r=m.parse(chart['radius'],None,[var,*params]);C=('cos',T);S=('sin',T)
        xy=[m.parse(f,None,[var,*params]) for f in pair]
        if any(domain_conditions(a) for a in [r,*xy]) or not all(same_value(a,b) for a,b in zip(xy,(times(r,C),times(r,S)))):
            raise Unsupported('The included Cartesian parametrization does not agree with the raw radius')
        if len(params)==1:
            a=s(params[0])
            if same_value(r,times(a,T)):prime=a
            elif same_value(r,times(a,plus(ONE,C))):prime=times(m.neg(a),S)
            else:raise Unsupported('Unknown elementary radial derivative')
        elif len(params)==2:
            a,b=map(s,params)
            if same_value(r,times(a,('exp',times(b,T)))):prime=times(b,r)
            elif same_value(r,times(a,plus(b,C))):prime=times(m.neg(a),S)
            else:raise Unsupported('Unknown elementary radial derivative')
        else:raise Unsupported('Unknown elementary radial derivative')
        dx=diff(times(prime,C),times(r,S));dy=plus(times(prime,S),times(r,C))
        return proof('regular_coordinate_and_branch',[
            'Use the original principal arctangent range and nonzero x, which also give r>0.',
            'The signed horizontal half-plane chooses ±(r cos(t),r sin(t)). The common sign cancels in the slope.',
            'The polar velocity has norm squared r²+r′²>0. Divide by its horizontal component when nonzero; otherwise the tangent is vertical.'],
            dict(regular_domain=[f'-pi/2<{var}<pi/2',('positive',r),('nonzero',dx)],
                 ordered_values=[('div',dy,dx)],zero_horizontal_velocity='vertical tangent'),
            horizontal_velocity=dx,vertical_velocity=dy)
    V=re.escape(var)
    left=re.fullmatch(r'([A-Za-z]\w*)\*cos\('+V+r'\)\^([1-9]\d*)',pair[0])
    right=re.fullmatch(r'([A-Za-z]\w*)\*sin\('+V+r'\)\^([1-9]\d*)',pair[1])
    if left and right:
        p=int(left[2]);names=list(dict.fromkeys([left[1],right[1]]))
        if (p!=int(right[2]) or p%2==0 or not 3<=p<=31 or params!=names or
                conditions!=[a+'>0' for a in names] or head is not None):
            raise Unsupported('Odd powered coordinates require both original positive scales')
        ratio=m.div(s(right[1]),s(left[1]))
        D=m.neg(times(ratio,m.power(('tan',T),p-2)))
        return proof('regular_coordinate_and_branch',[
            'Differentiate both original odd powered coordinates on the nonaxial parts.',
            'At a horizontal extremity compare the leading ordinate order p with horizontal order two; its one-sided branch slopes are zero.',
            'At a vertical extremity the horizontal order is p and the vertical order is two, so no finite graph slope exists.'],
            dict(regular_domain='nonaxial parameters',ordered_values=[D],
                 stationary={'sin(t)=0':'horizontal tangent, one-sided branch slopes zero','cos(t)=0':'vertical tangent'}),
            odd_power=p,scales=[s(a) for a in names])
    if params or conditions or head==printed[0] or 'polar_data' in origin:
        raise Unsupported('No admitted source branch for additional fixed parameters')
    # A variable may share a letter with a function. Replace its lexical token.
    x,y=[re.sub(r'\b'+V+r'\b','_',p0) for p0 in pair]
    if [x,y]==['asin(_/sqrt(1+_^2))','acos(1/sqrt(1+_^2))']:
        if head is not None:raise Unsupported('The original source wants graph derivatives on this principal branch')
        val=dict(regular_domain=f'{var}!=0',ordered_values=[('sign',T)],zero_horizontal_velocity='graph cusp at ordinate derivative jump')
        steps=['In the principal inverse-trig ranges the coordinates equal atan(t) and |atan(t)|.',
               'Inverting the first coordinate gives the exact graph Y=|X|. At t=0 its side derivatives are −1 and 1.']
    elif [x,y]==['cbrt(1-sqrt(_))','sqrt(1-cbrt(_))'] and head is None:
        D=m.div(m.power(('cbrt',diff(ONE,root(T))),2),
                times(('rpow',T,q(1,6)),root(diff(ONE,('cbrt',T)))))
        val=dict(regular_domain=f'0<{var}<1',ordered_values=[D],
                 endpoint_slopes={'0':'positive infinite','1':ZERO})
        steps=['The original square roots and cube roots give exactly 0≤t≤1. Differentiate each on its open interval.',
               'At t→0 take u=√t: 1−X~u/3 and 1−Y~u^(2/3)/2, so the common slope diverges.',
               'At t→1 invert u=1−X³. Then Y~√(2/3)X^(3/2), yielding one-sided derivative zero.']
    elif [x,y]==['_^2','sin(_)/_'] and head==printed[1]:
        D=m.div(diff(times(T,('cos',T)),('sin',T)),times(q(2),m.power(T,3)))
        val=dict(regular_domain=f'{var}!=0',ordered_values=[D],omitted_parameter='t=0 excluded from original sine quotient')
        steps=['The same positive horizontal value has the two parameters ±t. The original sine quotient is even, so the ordinate agrees.',
               'Divide the velocities for t≠0. The missing center is not assigned a value by the source.']
    elif [x,y]==['cos(_)','sin(_)'] and head==printed[1]:
        val=dict(regular_domain=f'sin({var})!=0',ordered_values=[m.neg(('cot',T))],zero_horizontal_velocity='vertical tangent')
        steps=['Differentiate sine and cosine. At sin(t)=0 the horizontal velocity vanishes but the vertical velocity is nonzero.',
               'Each local semicircle has a vertical tangent at that turning point, with no finite derivative there.']
    elif [x,y]==['cot(_)','tan(_)'] and head==printed[1]:
        val=dict(regular_domain=f'sin({var})*cos({var})!=0',ordered_values=[m.neg(squared(('tan',T)))])
        steps=['On the intersection of both original tangent domains, Y=1/X and X≠0.',
               'The reciprocal graph derivative gives the required coefficient without crossing a pole.']
    elif [x,y]==['acos(_)','asin(_)'] and head==printed[1]:
        val=dict(regular_domain=f'-1<={var}<=1',ordered_values=[q(-1)],endpoint_slopes={'-1':q(-1),'1':q(-1)})
        steps=['The two principal inverse-trig values add to pi/2 on the whole real source interval.',
               'Thus the graph is a line segment with relative derivative −1 even at its two ends.']
    else:raise Unsupported('The original coordinate pair needs a different regularity or stationary argument')
    return proof('regular_coordinate_and_branch',steps,val)


def rate_from_measure(task):
    heads=('Найти скорость роста площади круга, когда радиус 10 см и равномерно растёт со скоростью 2 см/с.',
           'Найти скорости изменения площади и диагонали прямоугольника в указанный момент.',
           'Найти скорость роста расстояния между одновременно вышедшими из одного порта пароходами, идущими на север и восток.')
    source_fields(task,{'shape','radius_cm','radius_rate_cm_per_s','requested','side_values_m','given_rates_m_per_s',
                        'initial_position','motions'},heads,('geometry','model'))
    fields=set(task)-{'id','kind','source'};head=task.get('source',{}).get('literal_requirement')
    if fields=={'shape','radius_cm','radius_rate_cm_per_s','requested'} and task['shape']=='circle':
        R=F(str(task['radius_cm']));d=F(str(task['radius_rate_cm_per_s']))
        if (R<=0 or task['requested']!=['area_rate_cm2_per_s'] or head not in (None,heads[0])
                or head==heads[0] and (R,d)!=(10,2)):
            raise Unsupported('The radius, its units and signed rate must come from the original source')
        val=dict(area_rate=times(q(2*R*d),P),unit='cm^2/s')
        steps=['The circle has area πR² for positive radius. Differentiate this metric with respect to time.',
               'Insert the original signed radius rate and keep the squared-length units.']
    elif fields=={'side_values_m','given_rates_m_per_s','requested'}:
        a,b=(F(str(z)) for z in task['side_values_m'])
        rates=task['given_rates_m_per_s'];out=task['requested']
        if min(a,b)<=0 or head not in (None,heads[1]) or out!=['area rate','diagonal rate'] or len(rates)!=2:
            raise Unsupported('Need two positive sides and both requested rates')
        limits=[re.fullmatch(r'(one|the other)(?: side)? (decreases|increases) by ([0-9]+(?:[./][0-9]+)?) m/s',r) for r in rates]
        if not all(limits) or [f[1] for f in limits]!=['one','the other']:raise Unsupported('The two signed side rates are missing')
        p,r=(F(f[3])*(-1 if f[2]=='decreases' else 1) for f in limits)
        if head==heads[1] and (a,b,p,r)!=(20,15,-1,2):raise Unsupported('A source measurement changed')
        radius=root(q(a*a+b*b))
        def effects(u,v):return dict(area_rate=q(u*b+a*v),diagonal_rate=m.div(q(a*u+b*v),radius))
        val=dict(listed_order=effects(p,r),reversed_if_unassigned=effects(r,p),area_unit='m^2/s',diagonal_unit='m/s')
        steps=['Apply product differentiation to the rectangle area, and differentiate the positive diagonal norm.',
               'When the wording leaves the side labels implicit, give the result for the listed order and keep the other assignment separate.']
    elif fields=={'initial_position','motions','requested'} and task['initial_position']=='same port and time':
        data=task['motions']
        if not isinstance(data,list) or len(data)!=2 or any(set(v)!={'direction','speed_km_per_hour'} for v in data):
            raise Unsupported('Need both original trajectories in consistent units')
        axes={'north':0,'south':0,'east':1,'west':1}
        directions=[v['direction'] for v in data]
        if any(v not in axes for v in directions) or axes[directions[0]]==axes[directions[1]]:
            raise Unsupported('The route requires genuinely orthogonal directions')
        a,b=[F(str(v['speed_km_per_hour'])) for v in data]
        geometry=task.get('source',{}).get('geometry')
        if (min(a,b)<=0 or task['requested']!=['distance_rate'] or head not in (None,heads[2])
                or (head==heads[2] or geometry is not None) and (directions,[a,b])!=(['north','east'],[30,40])
                or geometry not in (None,'Measured t hours after departure: northward ship 30 km/h and eastward ship 40 km/h, perpendicular displacement components.')):
            raise Unsupported('The given positive speed units or separation question changed')
        v=root(q(a*a+b*b));val=dict(distance_rate=v,initial_right_rate=v,unit='km/h')
        steps=['From the common initial point, orthogonal constant motions have relative squared distance (a²+b²)t².',
               'On the actual future half-line its positive root grows linearly. Differentiate there and check the initial right quotient.']
    else:raise Unsupported('No supported metric motion with the requested quantities')
    return proof('rates_from_original_measure',steps,val)


def curve_measure(task):
    kind=task['kind'];a,c,z,t=map(s,('a','c','z0','t0'))
    if kind=='space_curve_length':
        head='Найти длину дуги; параметры положительны.'
        source_fields(task,{'curve','endpoints','stated_conditions','requested_output'},(head,))
        requested(task,'arc_length')
        if task['stated_conditions']!=['parameters positive']:raise Unsupported('Need the original positive geometric scale')
        form=tuple(map(text_key,task['curve']))
        start=task['endpoints']
        if start=='A(a,0,0) to B(x,y,z)' and form==(
                'x^2+y^2+z^2=a^2','sqrt(x^2+y^2)*cosh(atan(y/x))=a'):
            h=('atan',m.div(s('y'),s('x')))
            val=dict(length=times(a,root(q(2)),absolute(('atan',('sinh',h)))),
                     original_component='x>0 and both source equations',initial='A(a,0,0)')
            steps=['On the component through A the original quotient needs x>0. Use its principal angle and put r=a sech(t), z=±a tanh(t).',
                   'The spherical relation gives exactly these two branches. In the polar speed the identity sech²(t)+tanh²(t)=1 gives 2a² sech²(t).',
                   'Use the positive speed and the primitive atan(sinh(t)); the actual endpoint picks the sign and angle.']
        elif start!='O to A(x0,y0,z0)':
            raise Unsupported('The complete actual initial and final positions must be specified')
        elif form==('y=a*asin(x/a)','z=(a/4)*ln((a-x)/(a+x))'):
            x=s('x0');L=plus(x,times(m.div(a,q(4)),('ln',m.div(plus(a,x),diff(a,x)))))
            val=dict(length=absolute(L),conditions=['a>0','abs(x0)<a','the endpoint satisfies both original equations'])
            steps=['The logarithm and inverse sine give |x|<a on the branch. Put U=a²/(a²−x²)>0.',
                   'The square of the metric speed is 1+U+U²/4=(1+U/2)². Integrate the positive square root and take absolute orientation.']
        elif len(form)==2 and form[0]=='(x-y)^2=a*(x+y)' and form[1].startswith('x^2-y^2='):
            right=m.parse(form[1].split('=',1)[1],None,['x'])
            n,d=m.rational_form(right)
            coefficient=n.get(((s('x'),2),),F(0))
            if (any(rel!='nonzero' or m.num(t) in (None,0) for rel,t in domain_conditions(right))
                    or len(n)!=1 or d!={():F(1)} or coefficient<=1):
                raise Unsupported('The original real equality does not force collapse to the axis')
            val=dict(length=absolute(z),conditions=['x0=y0=0'],trace='Oz',other_endpoints='not on the original trace')
            steps=['The second original equation forces y² to be a strictly negative multiple of x².',
                   'Realness forces both x and y to vanish. The first equation is then satisfied for any z. The entire trace is the z-axis.']
        elif form==('x^2+y^2=c*z','y/x=tan(z/c)'):
            t=m.div(z,c);L=times(c,root(t),plus(ONE,times(q(2,3),t)))
            val=dict(length=L,parameter=t,conditions=['c>0','0<z0/c<pi/2','endpoint satisfies both original equations'],
                     origin='limit endpoint of either eligible branch',other_components='cannot reach by crossing an original excluded pole')
            steps=['For t=z/c>0 the original tangent and nonzero quotient require cos(t)≠0. The continuous branch from the origin stays in the first positive chart.',
                   'Its coordinates are (±c√t cos(t),±c√t sin(t),ct) with common horizontal sign. The metric speed is c(2t+1)/(2√t).',
                   'Integrate the positive speed from the limiting initial endpoint; the integrable 1/√t singularity introduces no extra interval.']
        else:raise Unsupported('The original space-curve branch needs another metric chart')
        return proof('curve_metric_branch_integration',steps,val)
    if kind=='line_integral':
        source_fields(task,{'parameter','variables','parameters','stated_conditions','path','scalar','requested_output'},
                      ('Вычислить интеграл первого рода по напечатанной параметризации и промежутку.',))
        var=task['parameter'];p=task['parameters'];pieces=task['path']
        if (not isinstance(p,list) or len(p)!=1 or var in p or task['variables']!=list('xyz') or task['scalar']!='z'
                or len(pieces)!=1 or task['requested_output']!=['line_integral']
                or task['stated_conditions'] not in ([p[0]+'>0'],[p[0]+'>=0'])):
            raise Unsupported('Need the explicit single source arc and positive end')
        piece=pieces[0]
        chart=list(map(text_key,piece['map']))
        if (set(piece)!={'map','lower','upper'} or piece['lower']!='0' or piece['upper']!=p[0]
                or len(chart)!=3 or chart[:2]!=[f'{var}*cos({var})',f'{var}*sin({var})']):
            raise Unsupported('No supported complete spiral chart for this scalar weight')
        scale=re.fullmatch(r'(?:'+NUMBER+r'\*)?'+re.escape(var),chart[2])
        if not scale:raise Unsupported('The axial metric component is not a fixed linear coordinate')
        c=F(scale[1]) if scale[1] else F(1)
        if task.get('source',{}).get('literal_requirement') is not None and c!=1:
            raise Unsupported('The axial scale differs from the cited source')
        t=s(p[0]);offset=q(1+c*c);b=plus(offset,squared(t))
        return proof('curve_metric_branch_integration',[
            'The horizontal rotating frame contributes t²+1 to the squared speed; the fixed vertical velocity contributes its own square.',
            'The original weight is the signed vertical coordinate. Integrate the metric by the quadratic substitution from the source t=0 to its actual upper end.'],
            dict(line_integral=times(q(c/3),diff(times(b,root(b)),times(offset,root(offset))))))
    if kind=='line_integral_from_geometric_locus':
        source_fields(task,{'scalar','curve','requested_output'},('Вычислить интеграл первого рода по указанной дуге.',))
        if (task['requested_output']!=['line_integral'] or task['scalar']!='z' or text_key(task['curve'])!=
                'x^2+y^2=z^2,y^2=a*x;O(0,0,0)toA(a,a,sqrt(2))'):
            raise Unsupported('The named source endpoints, scalar and curve do not agree')
        radius=root(q(38))
        integral=times(m.div(root(q(2)),q(2)),diff(
            m.div(diff(times(q(25),radius),q(18)),q(64)),
            times(q(17,256),('ln',m.div(plus(q(25),times(q(4),radius)),q(17))))))
        return proof('curve_metric_branch_integration',[
            'Substitute the printed endpoint in both original equations. On the cone it requires a²=1, so other a give no such arc.',
            'On either admissible sign branch use x=sign(a)t², y=sign(a)t, z=t√(1+t²), 0≤t≤1.',
            'The weighted positive speed is t√(8t⁴+9t²+2). Substituting u=t² and completing the square yields a real elementary primitive.'],
            dict(line_integral=integral,condition='a^2=1',other_parameters='original endpoint outside the source curve'))
    source_fields(task,{'curve','density','requested_output'},('Найти указанные массовые характеристики дуги.',))
    requested(task,'mass')
    f=text_key(task['curve']);w=text_key(task['density'])
    if f=='ellipsex=a*cos(t),y=b*sin(t);a>=b>0;0<=t<=2*pi' and w=='abs(y)':
        b=s('b');S=root(diff(squared(a),squared(b)))
        value=times(q(2),b,plus(b,m.div(times(squared(a),('asin',m.div(S,a))),S)))
        steps=['The full ellipse has four equal mass quadrants since the given density is |y|.',
               'On one quadrant use u=cos(t) and the source metric √(a²sin²(t)+b²cos²(t)); the sine density cancels the substitution factor.',
               'The radial minorant stays positive. Evaluate the circular case separately before dividing by eccentricity.']
        val=dict(mass=value,conditions=['a>b>0'],circular_mass=times(q(4),squared(a)),circular_condition='a=b>0')
    elif f=='y^2=2*p*x;0<=x<=p/2' and w=='abs(y)':
        p=s('p');value=times(q(2,3),squared(p),diff(times(q(2),root(q(2))),ONE))
        val=dict(mass=value,conditions=['p>0'],one_branch_mass=m.div(value,q(2)),zero_scale='point with zero mass at p=0',
                 negative_scale='the stated x interval is empty')
        steps=['Use ordinate t as parameter on the full source arc, with x=t²/(2p) and −p≤t≤p for p>0.',
               'The density |t| is even and the metric speed is √(1+t²/p²). Substitute its quadratic argument on the positive half.']
    elif f=='x=a*t,y=a*t^2/2,z=a*t^3/3;0<=t<=1' and w=='sqrt(2*y/a)':
        C=plus(times(q(1,8),diff(times(q(3),root(q(3))),ONE)),
               times(q(3,16),('ln',m.div(plus(q(3),times(q(2),root(q(3)))),q(3)))))
        val=dict(mass=times(absolute(a),C),conditions=['a!=0'])
        steps=['The original density is t on [0,1] because 2y/a=t². The Euclidean speed is |a|√(1+t²+t⁴).',
               'Use u=t² and complete the square in u²+u+1. The positive radical primitive gives the stated value.']
    else:raise Unsupported('The requested mass needs a different source density or chart')
    return proof('curve_metric_branch_integration',steps,val)


def accumulated_axis_area(task):
    headings=('Составить выражение площади S, найти производную и построить её график.',
              'Найти площадь S(x), её производную и построить график производной.')
    source_fields(task,{'function','S','area','domain','requested_output'},headings)
    requested(task,'area_as_function','derivative')
    X=s('x');a=s('a');f=task['function'];head=task.get('source',{}).get('literal_requirement')
    if isinstance(f,dict):
        if (task.get('S')!='area between f, x-axis and perpendicular at x>=0' or head not in (None,headings[0])
                or set(task)-{'id','kind','source','function','S','requested_output'}):
            raise Unsupported('Bind the baseline, initial end and actual independent area request')
        pieces=[]
        for restriction,expr in f.items():
            raw=read_axis_function(expr,'x');numerator,denominator=m.rational_form(raw)
            if (domain_conditions(raw) or denominator!={():F(1)}
                    or set(numerator)-{(),((X,1),)}):
                raise Unsupported('On each printed slice use a verified affine height')
            (lo,hi,lc,hc),=branch_interval(restriction)
            if lo is None or hi is not None and hi<=lo:raise Unsupported('The original area height interval is invalid')
            a0,b0=numerator.get((),F(0)),numerator.get(((X,1),),F(0))
            if min(a0+b0*lo, a0+b0*hi if hi is not None else b0)<0:
                raise Unsupported('A sign-changing piece needs its own geometric area decomposition')
            pieces.append((lo,hi,lc,hc,a0,b0,raw))
        if not pieces:raise Unsupported('No original height is supplied')
        pieces.sort(key=lambda p:p[0]);previous=(F(0),False);area=F(0);values=[];joins=[]
        for lo,hi,lc,hc,a0,b0,raw in pieces:
            if (lo!=previous[0] or lc==previous[1] or hi is None and (lo,hi,lc,hc,a0,b0,raw)!=pieces[-1]):
                raise Unsupported('The source height does not cover its half-line by distinct adjacent intervals')
            h0=a0+b0*lo;shift=diff(X,q(lo));S=plus(q(area),times(q(h0),shift),times(q(b0/2),squared(shift)))
            if values and not same_value(m.substitute(values[-1]['height'],{X:q(lo)}),q(h0)):
                joins.append(q(lo))
            values.append(dict(interval=[q(lo),q(hi) if hi is not None else '+inf'],closed=[lc,hc],area=S,height=raw))
            if hi is not None:area+=h0*(hi-lo)+b0*(hi-lo)**2/2
            previous=(hi,hc)
        if previous[0] is not None:raise Unsupported('The full requested half-line is not covered')
        return proof('accumulate_area_from_signed_height',[
            'On each interval the named affine height is nonnegative, so its integral equals geometric area.',
            'Compute its primitive anchored at the actual cumulative area at the preceding boundary.',
            'The derivative equals the height inside each interval. At a boundary compare the two finite height traces.'],
            dict(pieces=values,nondifferentiable_joins=joins,relative_derivative_at_zero=q(pieces[0][4])))
    if (head not in (None,headings[1]) or text_key(f)!='sqrt(a^2-x^2)' or task['domain']!='abs(x)<=a'
            or task['area']!='geometric area bounded by arc, x-axis and perpendiculars at 0 and x'
            or set(task)-{'id','kind','source','function','area','domain','requested_output'}):
        raise Unsupported('Need the full semicircle and its original unoriented area')
    u=absolute(X);r=root(diff(squared(a),squared(X)))
    S=times(q(1,2),plus(times(u,r),times(squared(a),('asin',m.div(u,a)))))
    return proof('accumulate_area_from_signed_height',[
        'On a nondegenerate semicircle geometric area is the integral from 0 to |x| because its height is even and nonnegative.',
        'Use the positive radius primitive on 0≤|x|≤a. Differentiate the signed upper end on each branch.',
        'At zero the area is asymptotic to a|x|; at each external endpoint the finite relative derivative is zero.'],
        dict(area=S,derivative=times(('sign',X),r),domain='a>0, |x|<=a',derivative_excludes='x=0',
             zero_radius='only one source point; no ordinary derivative',endpoint_derivative=ZERO))


def derivative_difference_extremum(task):
    heading='Найти максимальное расхождение производных и построить соответствующие графики.'
    source_fields(task,{'functions','given','requested_output'},(heading,))
    requested(task,'maximum_of_derivative_difference','attainment')
    X=s('x');a,b=map(lambda f:read_axis_function(f,'x'),task['functions'])

    def affine(phase):
        top,bottom=m.rational_form(phase)
        if bottom!={():F(1)} or any(atom not in (X,P) for mon in top for atom,_ in mon):
            raise Unsupported('Expected a globally affine phase')
        slope={};offset={}
        for mon,coefficient in top.items():
            degrees=dict(mon);degree=degrees.pop(X,0)
            if degree>1:raise Unsupported('The source phase is not affine')
            (slope if degree else offset)[tuple(degrees.items())]=coefficient
        return m.poly_expr(slope),m.poly_expr(offset)

    def polynomial(expr):
        top,bottom=m.rational_form(expr)
        if bottom!={():F(1)} or domain_conditions(expr):
            raise Unsupported('The original signals need a globally differentiable chart')
        for atom in {v for mon in top for v,_ in mon}-{X,P}:
            if atom[0] not in ('sin','cos'):raise Unsupported('Unsupported original signal atom')
            affine(atom[1])
        return top

    original=list(map(polynomial,(a,b)))
    delta=m.addp(original[1],{mon:-c for mon,c in original[0].items()})
    deltas=[(mon,c) for mon,c in delta.items() if mon]
    if len(deltas)!=1 or len(deltas[0][0])!=1:
        raise Unsupported('The signal difference is not one sinusoid and a constant')
    (((osc,k),),c),=deltas
    if k!=1 or osc[0] not in ('sin','cos'):
        raise Unsupported('The remaining mode is not a single sine or cosine')
    bound=task.get('given')
    if bound is not None:
        hit=re.fullmatch(r'function difference at most '+NUMBER,bound)
        if not hit or abs(c)+abs(delta.get((),0))>F(hit[1]):
            raise Unsupported('The source bound on the original difference failed')
    scale,offset=affine(osc[1]);ctx=m.context({})
    if m.sign(scale,ctx)==0:
        return proof('single_frequency_derivative_extremum',['A constant difference has zero derivative.'],
                     dict(maximum=ZERO,attainment='all real x'))
    if m.sign(scale,ctx) not in (-1,1):raise Unsupported('Need an invertible signed phase')
    levels=m.mul(P,s('k'))
    if osc[0]=='cos':levels=m.add(levels,m.mul(q(1,2),P))
    return proof('single_frequency_derivative_extremum',[
        'Subtract the two globally differentiable signals and collect terms. Only the single displayed frequency remains, up to a constant.',
        'The derivative of the constant vanishes. The derivative of the oscillation has magnitude at most the absolute amplitude times the absolute phase slope.',
        'The affine phase ranges over the real line, so each extremizing phase has the indicated real preimage.'],
        dict(maximum=absolute(m.mul(q(c),scale)),attainment=m.div(diff(levels,offset),scale),index='k is any integer'),
        original_difference=m.poly_expr(delta),phase=osc[1])


CURVE_ROUTES={
    'plane_curve_contact_angle':contact_conditions,
    'intersection_angle_proof':contact_conditions,
    'tangent_angle_parameter':secant_directions,
    'tangent_limit_proof':secant_directions,
    'one_sided_tangent_angle':secant_directions,
    'polar_tangent_angle':tangent_segments,
    'subtangent_construction':tangent_segments,
    'tangent_segment_construction':tangent_segments,
    'normal_segment_length':tangent_segments,
    'tangent_intercept_length':tangent_segments,
    'tangent_segment_length':tangent_segments,
    'parametric_curve_derivatives':one_coordinate_curve,
    'related_rates':rate_from_measure,
    'space_curve_length':curve_measure,
    'line_integral':curve_measure,
    'line_integral_from_geometric_locus':curve_measure,
    'wire_mass_properties':curve_measure,
    'area_primitive_and_graph':accumulated_axis_area,
    'area_primitive':accumulated_axis_area,
    'derivative_difference_extremum':derivative_difference_extremum,
}


def geometric_domain_goal(task):
    if selected_source_measure_branch(task) is not None:return True
    rule=SOURCE_ROUTES.get(task.get('kind')) or CURVE_ROUTES.get(task.get('kind')) or GRAPH_CHART_ROUTES.get(task.get('kind')) or FEASIBLE_EXTREMA_ROUTES.get(task.get('kind'))
    if rule is None:return False
    try:
        rule(task)
    except (Unsupported,KeyError,TypeError,ValueError,ZeroDivisionError,IndexError,AttributeError):
        return False
    return True



def lyapunov_normal_statement(task):
    claim='prove Lyapunov inequality phi(P1,P)<C*rho(P1,P)'
    source_fields(task,{'source_formula','stated_conditions','requested_output'},(claim,))
    fields=task.get('source_formula','');facts=task.get('stated_conditions',[])
    if (fields!='z=f(x,y); phi(P1,P)=angle between normals; rho(P1,P)=Euclidean distance'
            or task.get('requested_output')!=[claim] or facts not in (
                ['D bounded and closed','f has bounded second derivatives on D'],
                ['D bounded and closed','f has bounded second derivatives on D','D convex'],
                ['D bounded and closed','f has bounded second derivatives on D','D piecewise smooth paths of length <=K times endpoint distance'])):
        raise Unsupported('Bind the graph and the ambient distance, with only the stated Hessian and path conditions')
    argument=[
        'Записываем единичную нормаль как (−∇f,1)/√(1+|∇f|²). Норма производной этой нормировки по градиенту не больше 1.',
        'Угол по длине хорды двух единичных нормалей не превосходит π/2, умноженного на длину хорды.',
        'Если точки соединены кусочно гладким путём в D длины не более K плоских расстояний, интегрируем ограниченный гессиан вдоль пути. Получаем оценку угла через πMK/2 и пространственное расстояние.',
    ]
    value=dict(scope='distinct graph points and the upward normals',bound_coefficient='pi*M*K/2',
               conditions='Hessian operator norm bounded by M and short connecting paths inside D')
    if len(facts)==2:
        argument.extend([
            'Берём две полосы x⁴≤|y|≤2x⁴, 0≤x≤1, соединённые прямоугольником 1/2≤x≤1, |y|≤2. Это ограниченное замыкание связной области.',
            'Пусть η — гладкая нечётная функция, равная знаку вне (−1,1). При x>0 задаём f=x³ y η(y/x⁴), при x≤0 задаём f=0. На полосах f=±x³y, в соединяющем прямоугольнике x отделено от нуля. Гессиан ограничен на D. В начале градиент равен o расстояния, поэтому вторые производные существуют и там.',
            'При y=±x⁴ высоты равны x⁷, f_x одинаково равно 3x⁶, а f_y равно ±x³. Хорда нормалей имеет порядок x³, расстояние графических точек равно 2x⁴. Ни одна общая константа не покрывает такие пары.'
        ])
        value.update(printed_claim_holds=False,counterexample=dict(
            domain='0<=x<=1 and x^4<=abs(y)<=2*x^4, joined by 1/2<=x<=1 and abs(y)<=2',
            function='x^3*y*eta(y/x^4) for x>0, zero otherwise',points=['(x,x^4,x^7)','(x,-x^4,x^7)'],
            angle_to_distance='unbounded as x tends to zero'))
    else:value['proved']=True
    return proof('short_paths_and_normal_metric',argument,value)



def coordinate_image_composition(task):
    given=task['given'];name=r'([A-Za-z]\w*)'
    grammar=fr'{name} continuous on R=\(a,A\)x\(b,B\), {name},{name} continuous on R\'=\(a\',A\'\)x\(b\',B\'\) and valued in \(a,A\),\(b,B\)'
    hit=re.fullmatch(grammar,given)
    if not hit or len(set(hit.groups()))!=3:
        raise Unsupported('The outer rectangle and both distinct image coordinates must be bound')
    f,p,q0=hit.groups()
    literal=task.get('source',{}).get('literal_requirement','')
    k=re.fullmatch(fr"Доказать непрерывность(?: напечатанной)? F\(u,v\)={f}\({p}\(u,v\),({p}|{q0})\(u,v\)\) на R'\.",literal)
    if not k:raise Unsupported('The declared outer function and its two coordinate arguments differ')
    source_fields(task,{'given'},(literal,))
    repeated=k[1]==p
    value=dict(continuous_on_domain_of_composition=True,second_component=k[1],
               sufficient_condition='the map into the outer domain is continuous')
    if repeated:
        value.update(printed_claim_holds=False,counterexample=dict(first_interval=[0,1],second_interval=[2,3],
                    images={p:[1,2],q0:[5,2]},result='the repeated first coordinate is outside the second interval'))
    return proof('typed_composition_image_inclusion',[
        'Непрерывность композиции требует, чтобы обе координаты вместе попадали в область внешней функции.',
        'Гипотезы гарантируют это для пары из первой и второй функций. При повторе первой координаты нужна ещё принадлежность её значения второму интервалу.',
        'В непересекающихся интервалах постоянные координатные функции удовлетворяют своим условиям. Повтор первой координаты выводит аргумент за пределы внешней области.'
    ],value)


def homogeneous_radial_claim(task):
    title='Доказать непрерывность вдоль каждого луча x=t cos α,y=t sin α при t→0 и нарушение совместной непрерывности.'
    source_fields(task,{'given'},(title,))
    data=re.fullmatch(r'f=(.+) off origin, f\(0,0\)=([^ ]+)',task.get('given',''))
    if not data:raise Unsupported('Both the homogeneous formula and its assigned origin value are required')
    x,y=s('x'),s('y')
    raw=m.parse(data[1].replace('²','^2').replace('⁴','^4'),None,['x','y'])
    if raw[0]!='div' or domain_conditions(raw[1]) or domain_conditions(raw[2]):
        raise Unsupported('The two homogeneous polynomials must be defined everywhere')
    def pol(e):
        p,d=m.rational_form(e)
        deg={sum(k for a,k in mon) for mon in p}
        if d!={():F(1)} or len(deg)!=1 or any(a not in (x,y) for mon in p for a,k in mon):
            raise Unsupported('A nonzero polynomial of a single degree is required')
        return p,deg.pop()
    numerator,n=pol(raw[1]);denominator,d=pol(raw[2])
    powers={mon[0][0] for mon,c in denominator.items() if len(mon)==1 and c>0}
    if (powers!={x,y} or any(c<=0 or any(k%2 for v,k in mon) for mon,c in denominator.items())
            or m.simplify(m.parse(data[2],None))!=ZERO or n>=d):
        raise Unsupported('The denominator must be positive away from the origin and its degree strictly larger')
    # A nonzero homogeneous polynomial of degree n cannot vanish at n+1 distinct slopes.
    for k in range(n+1):
        val=m.num(m.simplify(m.substitute(raw,{x:ONE,y:q(k)})))
        if val:break
    else:raise Unsupported('No certified nonzero ray coefficient')
    difference=n-d
    return proof('homogeneous_ray_degree_obstruction',[
        'Положительные чётные степени в знаменателе дают строгую положительность вдали от начала.',
        'Подстановка (x,y)=t(1,k) выносит степень t, равную разности однородных степеней. Выбираем наклон с ненулевой полученной константой.',
        'Разность степеней отрицательна, поэтому на этом луче предел бесконечен. Нулевая присвоенная величина не согласуется уже с лучевым пределом.'
    ],dict(printed_claim_holds=False,counterexample=dict(ray=[ONE,q(k)],coefficient=q(val),degree=difference,
           limit='+inf' if val>0 else '-inf'),joint_continuity=False),homogeneity_degrees=[n,d])


def source_geometric_domains(task,library,request):
    from graphs import graphical_goal_kind,graph_intersection_certificate
    if graphical_goal_kind(task):return graph_intersection_certificate(task,library,request)
    if library.data.get('domain_source_resolutions') and task.get('kind')=='multivariate_continuity':
        literal=task.get('source',{}).get('literal_requirement','')
        if 'и нарушение совместной непрерывности' in literal:return homogeneous_radial_claim(task)
        if literal.startswith('Доказать непрерывность') and 'F(u,v)' in literal:return coordinate_image_composition(task)
    if library.data.get('typed_source_reductions') and task.get('kind')=='surface_geometry' and 'angle between normals' in str(task.get('source_formula','')):
        return lyapunov_normal_statement(task)
    residual_flag=('residual_local_derivatives' if task.get('kind') in
                   ('partial_derivatives','first_and_second_total_differentials') else 'residual_projected_sections')
    if library.data.get(residual_flag):
        candidate=selected_residual_geometry(task)
        if candidate is not None:return candidate
    if library.data.get('checked_source_integral_branches'):
        piece=selected_source_measure_branch(task)
        if piece is not None:return piece
    rule=SOURCE_ROUTES.get(task.get('kind')) or CURVE_ROUTES.get(task.get('kind')) or GRAPH_CHART_ROUTES.get(task.get('kind')) or FEASIBLE_EXTREMA_ROUTES.get(task.get('kind'))
    if rule is None:raise Unsupported('Unsupported source geometry goal')
    if task.get('kind') in CURVE_ROUTES and not library.data.get('source_curve_contacts'):
        raise Unsupported('The source curve transition is unavailable in this library')
    if rule is derivative_difference_extremum and not library.data.get('single_frequency_derivative_extrema'):
        raise Unsupported('The single-frequency derivative bound is unavailable in this library')
    if task.get('kind') in GRAPH_CHART_ROUTES and not library.data.get('source_multivariate_graph_charts'):
        raise Unsupported('The local multivariable graph transition is unavailable in this library')
    if task.get('kind') in FEASIBLE_EXTREMA_ROUTES and not library.data.get('source_feasible_extrema'):
        raise Unsupported('Verified signs and feasible-coordinate reductions are unavailable in this library')
    try:
        return rule(task)
    except Unsupported:
        raise
    except (KeyError,TypeError,ValueError,ZeroDivisionError,IndexError,AttributeError) as exc:
        raise Unsupported('The original geometric or continuity question is incomplete') from exc


def polynomial_level(form,parameters):
    x,y=map(s,'xy')
    a,b=form.split('=')
    raw=('add',m.parse(a,None,['x','y',*parameters]),('mul',q(-1),m.parse(b,None,['x','y',*parameters])))
    if any(r!='nonzero' or m.num(t) in (None,0) for r,t in domain_conditions(raw)):
        raise Unsupported('An original level divisor needs an independent domain proof')
    p,d=m.rational_form(raw)
    if not p or d!={():F(1)}:raise Unsupported('The original relation is not a nonzero polynomial level')
    return p


def graph_chart_source(task,fields,heading):
    source_fields(task,fields,(heading,),('section_convention',))
    note=task.get('source',{}).get('section_convention')
    if note not in (None,'p310 footnote: existence of the implicit functions and needed derivatives is assumed in most exercises unless otherwise stated'):
        raise Unsupported('An extra source regularity convention must be preserved')


def quartic_ordinate_branches(task):
    from intervals import Quadratic,between,compare,peval,padd,pmul,pscale,roots,trim
    from graphs import ordered_cuts
    output=task['requested_output'];head='implicit branch decomposition; '+', '.join(output)
    graph_chart_source(task,{'source_formula','stated_conditions','requested_output'},head)
    if output not in (['regions_with_one_two_three_four_values','branch_points','continuous_single_valued_branches'],
                      ['branch_points','continuous_single_valued_branches']):
        raise Unsupported('Need all original values or branches under their original projection')
    domain=task['stated_conditions'];upper=None
    if domain:
        if len(domain)!=1 or len(ends:=branch_interval(domain[0]))!=1:raise Unsupported('Need one original symmetric interval')
        lo,hi,lc,hc=ends[0]
        if hi is None or hi<=0 or lo!=-hi or not lc or not hc:raise Unsupported('The source interval is not symmetric and closed')
        upper=Quadratic(hi*hi)
    X,Y=map(s,'xy');P0=polynomial_level(text_key(task['source_formula']),[])
    pol={}
    for mon,c in P0.items():
        if set(dict(mon))-{X,Y}:raise Unsupported('Cannot classify a level with a free polynomial coefficient')
        i,j=(dict(mon).get(k,0) for k in (X,Y))
        if i%2 or j%2 or i+j>4:raise Unsupported('Need a quadratic equation in the two coordinate squares')
        pol[i//2,j//2]=c
    a=pol.get((0,2),F(0))
    if not a:raise Unsupported('No quadratic dependence on the ordinate square')
    B=trim([pol.get((i,1),F(0))/a for i in range(2)])
    C=trim([pol.get((i,0),F(0))/a for i in range(3)])
    D=padd(pmul(B,B),pscale(C,F(-4)))
    if not any(D):raise Unsupported('An identically repeated ordinate root needs a different branch classification')
    z=Quadratic(F(0))
    cuts=ordered_cuts([z,*([upper] if upper is not None else []),
        *(x for p in (B,C,D) if any(p) for x in roots(p)
          if compare(x,z)>0 and (upper is None or compare(x,upper)<0))])
    def term(u):return plus(q(u.a),times(q(u.b),root(q(u.d)))) if u.b else q(u.a)
    def counts(u):
        b,c,d=(peval(f,u).sign() for f in (B,C,D))
        if d<0:return dict(ordinates=0,real_square_roots=0)
        if d==0:return dict(ordinates=2 if b<0 else 1 if not b else 0,real_square_roots=1,
                           repeated_ordinate_square=True)
        positive=1 if c<0 else int(b<0) if c==0 else 2*int(b<0)
        return dict(ordinates=2*positive+int(c==0),real_square_roots=2,zero_ordinate=(c==0))
    points=[dict(square_abscissa=term(x),**counts(x)) for x in cuts]
    bins=[dict(square_interval=(term(a),term(b) if b!='+inf' else b),
               **counts(Quadratic(between(a,b)))) for a,b in zip(cuts,cuts[1:]+(['+inf'] if upper is None else []))]
    def polynomial(coef,argument):
        return plus(*(times(q(v),m.power(argument,j)) for j,v in enumerate(coef) if v))
    x2=squared(X);bf,df=(polynomial(p,x2) for p in (B,D))
    branch=[m.div(plus(m.neg(bf),times(q(k),root(df))),q(2)) for k in (-1,1)]
    return proof('real_quartic_projection',[
        'Set t=y² and solve the actual quadratic in t. Each positive root gives two real ordinates; zero gives one.',
        'In s=x² split at all roots of the discriminant, product and sum. Exact signs on each component and at its ends determine every multiplicity.',
        'Take ±sqrt(t) only on the displayed nonnegative branch domains. Equal radicals can join at discriminant zero or t=0; isolated zero fibers do not extend.'],
        dict(square_ordinate_roots=branch,branch_domain='on the original x interval, discriminant >=0 and chosen root >=0',
             square_cut_points=points,square_open_cells=bins,
             ordinate_selection='sign choices are constant on each strictly positive branch interval; glue only at equal endpoint values'))


def singular_graph_directions(task):
    from graphs import ordered_cuts,rational_roots
    from intervals import peval
    output=task['requested_output']
    if output not in (['prove two local differentiable branches','both slopes at origin'],["y' at (0,0)"]):
        raise Unsupported('Need the original local graph and its directions at the origin')
    graph_chart_source(task,{'source_formula','stated_conditions','requested_output'},'singular curve derivatives; '+', '.join(output))
    conditions=task['stated_conditions'];pars=[]
    for item in conditions:
        p=re.fullmatch(r'([A-Za-z]\w*)!=0',item)
        if not p or p[1] in 'xy' or p[1] in pars:raise Unsupported('A fixed nonzero parameter must be declared')
        pars.append(p[1])
    x,y,t=map(s,('x','y','direction'))
    poly=polynomial_level(text_key(task['source_formula']),pars)
    if any(a not in {x,y,*map(s,pars)} for mon in poly for a,_ in mon):
        raise Unsupported('The level has a nonalgebraic initial part')
    rank=lambda mon:dict(mon).get(x,0)+dict(mon).get(y,0)
    degree=min(map(rank,poly))
    if not 2<=degree<=4:raise Unsupported('Need a genuinely singular polynomial level at the origin')
    lead={mon:c for mon,c in poly.items() if rank(mon)==degree}
    factor={a:n for a,n in m.common_mon(lead).items() if a in set(map(s,pars))}
    if any(a not in factor or factor[a]!=n for mon in lead for a,n in mon if a not in (x,y)):
        raise Unsupported('The initial directions depend on an unclassified parameter polynomial')
    initial=[F(0)]*(degree+1)
    for mon,c in lead.items():initial[dict(mon).get(y,0)]+=c
    if not initial[-1]:raise Unsupported('The vertical direction may be part of the source tangent cone')
    roots=ordered_cuts(rational_roots(tuple(initial)))
    slope=[(r,peval(tuple(j*c for j,c in enumerate(initial) if j),r)) for r in roots]
    if not slope or any(not d.sign() for r,d in slope) or len(output)==2 and len(slope)!=2:
        raise Unsupported('Each requested direction must be a simple attained real root')
    def term(u):return plus(q(u.a),times(q(u.b),root(q(u.d)))) if u.b else q(u.a)
    lift={}
    for mon,c in poly.items():
        powers=dict(mon);j=powers.pop(y,0);i=powers.pop(x,0)+j-degree
        if i:powers[x]=i
        if j:powers[t]=j
        lift[tuple(sorted(powers.items()))]=c
    return proof('simple_directions_at_singular_level',[
        'The lowest nonzero homogeneous part contains every limiting direction. Its vertical value is nonzero.',
        'In the punctured chart y=x*t factor the exact power of x. The continued equation at x=0 is the initial polynomial in t.',
        'All real direction roots are simple. The implicit function theorem gives the full local branches and their slopes at the source point.'],
        dict(branch_count=len(slope),slopes=[term(r) for r,d in slope],point=[ZERO,ZERO],
             graph_form='y=x*t(x) in each neighborhood of a simple root'),
        initial_direction_polynomial=list(map(q,initial)),initial_nonzero_parameter_factor=list(factor.items()),
        derivatives_at_directions=[term(d) for r,d in slope],blown_up_relation=m.poly_expr(lift))


def explicit_level_differentials(task):
    want=task['requested_output'];kind=task['kind'];raw=text_key(task['source_formula'])
    prefix='implicit differentials' if kind=='implicit_differentials' else 'implicit differential identity'
    graph_chart_source(task,{'source_formula','stated_conditions','requested_output','point','dependent','suggested_method'},prefix+'; '+', '.join(want))
    if task.get('suggested_method') is not None:raise Unsupported('The actual suggested derivation must be preserved')
    cond=task['stated_conditions'];x,y=map(s,'xy')
    ordinary=kind=='implicit_differential_identity' and 'point' not in task and 'dependent' not in task
    if (ordinary and raw=='1+x*y=k*(x-y)' and cond==['k constant'] and want==['prove dx/(1+x²)=dy/(1+y²)']):
        k=s('k');v=plus(x,k);Y=m.div(diff(times(k,x),ONE),v)
        steps=['The source excludes x=−k because 1+k²>0. Solve for y on the full original real level.',
               'Differentiate the fractional-linear expression. The same scale (1+k²)/(x+k)² appears in 1+y², so it cancels.']
        val=dict(identity='dx/(1+x^2)=dy/(1+y^2)',graph=Y,domain=('nonzero',v))
    elif (ordinary and raw=='x^2*y^2+x^2+y^2-1=0' and cond==['x*y>0'] and
          want==['prove dx/sqrt(1-x^4)+dy/sqrt(1-y^4)=0']):
        steps=['The source with xy>0 implies both squared coordinates lie strictly between zero and one.',
               'The original level gives 1−x⁴=y²(1+x²)² and its symmetric identity. Take their positive roots, retaining |x| and |y|.',
               'Use the common sign of x and y to compare the requested differential with the derivative of the original level.']
        val=dict(identity=want[0][6:],positive_radicals=[times(absolute(y),plus(ONE,squared(x))),
                 times(absolute(x),plus(ONE,squared(y)))],domain=['original level','x*y>0'])
    elif (ordinary and raw=='a*x^2+2*b*x*y+c*y^2+2*d*x+2*e*y+f=0' and not cond and
          want==['prove d^3/dx^3[(y_pp)^(-2/3)]=0 where defined']):
        a,b,c,d,e,f=map(s,'abcdef')
        L=plus(times(b,x),times(c,y),e)
        scale=plus(times(a,squared(e)),times(q(-2),b,d,e),times(c,squared(d)),
                   m.neg(times(diff(times(a,c),squared(b)),f)))
        polynomial=diff(squared(plus(times(b,x),e)),times(c,plus(times(a,squared(x)),times(q(2),d,x),f)))
        steps=['Implicit differentiation gives y″=−C/L³ with L=bx+cy+e.',
               'The original equation makes the numerator C constant and reduces L² to a quadratic in x by completing the square.',
               'Where L,C are nonzero the power (y″)^(-2/3) is constant times L². Its third derivative vanishes.']
        val=dict(third_derivative=ZERO,second_derivative=m.neg(m.div(scale,m.power(L,3))),
                 squared_linear_term=polynomial,conditions=[('nonzero',L),('nonzero',scale)])
    elif (ordinary and raw=='F(x,y,z)=0determinesx(y,z),y(x,z),z(x,y)' and not cond and
          want==['prove x_y*y_z*z_x=-1']):
        steps=['The three prescribed local graph functions describe the same points. Differentiate z(x(y,z),y)=z at fixed z.',
               'Differentiating y(x,z(x,y))=y at fixed x proves y_z*z_y=1; multiply the first identity by y_z.']
        val=dict(cyclic_product=q(-1),domain='all three compatible differentiable local graph inverses')
    elif (kind=='implicit_differentials' and raw=='z-x-atan(y/(z-x))=0' and not cond and want==['dz','d²z']
          and task['dependent']=='z' and task.get('point') is None):
        z=s('z');w=diff(z,x);T=('tan',w);U=squared(('sec',w));H1=plus(T,times(w,U));H2=times(q(2),U,plus(ONE,times(w,T)))
        dx,dy=map(s,('dx','dy'))
        steps=['The original principal arctangent gives w=z−x in (−pi/2,pi/2) with w≠0. Its inverse relation is y=w tan(w).',
               'On each admissible branch this right-hand side has nonzero derivative with the sign of w.',
               'Differentiate the actual inverse relation twice before returning to z=x+w.']
        val=dict(dz=plus(dx,m.div(dy,H1)),second_differential=m.neg(m.div(times(H2,squared(dy)),m.power(H1,3))),
                 conditions=['-pi/2<z-x<pi/2','z!=x','y>0'])
    elif (ordinary and raw=='[z-f(alpha)]^2=x^2*(y^2-alpha^2);[z-f(alpha)]*f_prime(alpha)=alpha*x^2'
          and not cond and want==['prove z_x*z_y=x*y']):
        steps=[
            'Put W=z−f(alpha). Differentiate the first equality. The second cancels both alpha-derivative coefficients, yielding W*z_x=x*(y²−alpha²) and W*z_y=x²*y.',
            'For W≠0 multiply and use the original square equality. On y=0 the real equality forces z=f(0) along that line, so z_x=0.',
            'At x=0 and y≠0 the first equality gives W=0. If f′(alpha)=0 there, z_y=0 by differentiating the exact trace z(0,y)=f(alpha(0,y)).',
            'Otherwise fix y and let x approach zero. For x≠0 the two original equations force W≠0 and give z_x=W/x. If y²−alpha(0,y)²>0, then |W/x| tends to a positive number and f′(alpha(x,y)) tends to zero by the second equation.',
            'The last limit would force f′(alpha(0,y))=0: either alpha equals its central value arbitrarily close, or the continuous alpha path reaches a whole one-sided interval and the mean value theorem for f gives that derivative. Thus |W/x| tends to zero and the mean value theorem gives z_x(0,y)=0.']
        val=dict(identity='z_x*z_y=x*y',zero_factor_branches=['y=0','x=0 and f_prime(alpha)=0',
                   'x=0 and f_prime(alpha)!=0'],regular_branch='W!=0')
    else:raise Unsupported('The original implicit identities need a different explicit level reduction')
    return proof('explicit_level_differential_intermediates',steps,val)


def homogeneous_two_coordinate_jet(task):
    output=['z_x','z_y','z_xx','z_xy','z_yy']
    graph_chart_source(task,{'source_formula','residual','stated_conditions','requested_output','point','dependent','independent'},
        'implicit derivative; '+', '.join(output))
    raw=text_key(task['source_formula']);encoded=text_key(task['residual'])
    if (task['requested_output']!=output or task['point'] is not None or task['dependent']!='z'
            or task['independent']!=['x','y'] or task['stated_conditions'] or raw!=encoded+'=0'):
        raise Unsupported('The five first and second partials must bind the same original relation')
    hit=re.fullmatch(r'z-sqrt\(x\^2-(?:'+NUMBER+r'\*)?y\^2\)\*(tan|sin|cos|exp)\(x/sqrt\(x\^2-(?:'+NUMBER+r'\*)?y\^2\)\)',encoded)
    if not hit or hit[1]!=hit[3]:raise Unsupported('Need the same positive radical scale in both slots')
    c=F(hit[1]) if hit[1] else F(1);kind=hit[2]
    if c<=0:raise Unsupported('The original indefinite quadratic scale needs a strictly positive coefficient')
    x,y=map(s,'xy');radicand=diff(squared(x),times(q(c),squared(y)));R=root(radicand);phase=m.div(x,R)
    H=(kind,phase)
    if kind=='tan':
        H1=squared(('sec',phase));H2=times(q(2),H1,H)
    elif kind=='sin':H1=('cos',phase);H2=m.neg(H)
    elif kind=='cos':H1=m.neg(('sin',phase));H2=m.neg(H)
    else:H1=H2=H
    D=[m.div(x,R),m.div(times(q(-c),y),R)]
    S=[diff(m.div(q(int(i==0)),R),m.div(times(phase,z),R)) for i,z in enumerate(D)]
    normal=diff(H,times(phase,H1))
    first=[plus(times(z,normal),times(q(int(i==0)),H1)) for i,z in enumerate(D)]
    second=[]
    for i,j in ((0,0),(0,1),(1,1)):
        rij=m.div(diff(q(([F(1),-c][i]) if i==j else F(0)),times(D[i],D[j])),R)
        second.append(plus(times(rij,normal),times(R,H2,S[i],S[j])))
    conditions=[('positive',radicand)]
    if kind=='tan':conditions.append(('nonzero',('cos',phase)))
    return proof('homogeneous_scale_jet',[
        'Use the original positive scale r and phase s=x/r. The source keeps r nonzero and retains every outer pole.',
        'The product and chain rules give z_i=r_i(h−s h′)+delta_i h′.',
        'Differentiate this once more and collect the terms into r_ij(h−s h′)+r h″ s_i s_j. Substitute the exact derivatives of the original quadratic scale.'],
        dict(derivatives=dict(zip(output,[*first,*second])),source_domain=conditions),
        radial_scale=R,phase=phase,outer_jet=[H,H1,H2])


def parametric_tangent_image(task):
    line='Уравнения касательной прямой и нормальной плоскости в указанной точке.'
    plane='Уравнения касательной плоскости и нормали при указанных параметрах.'
    source_fields(task,{'parametrization','parameters','coordinates','requested_output'},(line,plane))
    if task['coordinates']!=list('xyz'):raise Unsupported('The full Cartesian source coordinates are required')
    chart=task['parametrization'];params=task['parameters'];output=task['requested_output']
    if set(chart)!={'variables','map','at'}:raise Unsupported('The source needs the original point and full parameter chart')
    h=task.get('source',{}).get('literal_requirement')
    def geometry(P,N):
        xx=list(map(s,('X','Y','Z')));displacement=[diff(a,b) for a,b in zip(xx,P)]
        return dict(point=P,direction=N,plane_residual=m.dot(displacement,N),
                    line_coordinates=[plus(a,times(s('lambda'),b)) for a,b in zip(P,N)])
    a,b,c=map(s,'abc')
    if output==['tangent_line_and_normal_plane'] and h in (None,line) and params==list('abc') and chart==dict(
            variables=['t'],map=['a*sin(t)^2','b*sin(t)*cos(t)','c*cos(t)^2'],at=['pi/4']):
        point=[times(q(1,2),t) for t in (a,b,c)]
        branches=[dict(condition='a^2+c^2>0',**geometry(point,[a,ZERO,m.neg(c)])),
                  dict(condition='a=c=0, b!=0',**geometry(point,[ZERO,ONE,ZERO])),
                  dict(condition='a=b=c=0',degenerate='point with no tangent line or normal plane')]
        return proof('intrinsic_tangent_at_chart_rank_loss',[
            'At the original parameter pi/4, the velocity is (a,0,−c). It gives the tangent and normal plane if nonzero.',
            'If the velocity vanishes and b≠0, the actual image is a segment of Oy, so a one-sided tangent uses Oy.',
            'If all three scales vanish the image is just one point.'],
            dict(branches=branches))
    if output!=['tangent_plane_and_normal_line'] or h not in (None,plane):
        raise Unsupported('Need the printed tangent plane and normal line')
    if params==['a','b','c','phi0','psi0'] and chart==dict(variables=['phi','psi'],
            map=['a*cos(psi)*cos(phi)','b*cos(psi)*sin(phi)','c*sin(psi)'],at=['phi0','psi0']):
        phi,psi=map(s,('phi0','psi0'))
        d=[times(('cos',psi),('cos',phi)),times(('cos',psi),('sin',phi)),('sin',psi)]
        axes=[a,b,c];P0=[times(u,v) for u,v in zip(axes,d)]
        normal=[m.div(u,v) for u,v in zip(d,axes)]
        branches=[dict(condition='a*b*c!=0',**geometry(P0,normal))]
        for i,t in enumerate('abc'):
            branches.append(dict(condition=t+'=0; other two axes nonzero',
                **geometry(P0,[q(int(i==j)) for j in range(3)])))
        branches.append(dict(condition='at least two axes zero',degenerate='segment or point, no intrinsic surface plane'))
        steps=['With three nonzero scales, use the regular implicit ellipsoid rather than the angular coordinate rank.',
               'The implicit gradient is nonzero even at a pole of the supplied parameterization.',
               'If precisely one scale is zero the image is a filled planar ellipse, with its intrinsic coordinate plane.']
    elif params==['phi0','r0','alpha'] and chart==dict(variables=['phi','r'],
            map=['r*cos(phi)','r*sin(phi)','r*cot(alpha)'],at=['phi0','r0']):
        phi,r,alpha=map(s,params);g=('cot',alpha);C=('cos',phi);S=('sin',phi);P0=[times(r,z) for z in (C,S,g)]
        branches=[dict(condition='sin(alpha)!=0, r0!=0',**geometry(P0,[times(g,C),times(g,S),q(-1)])),
                  dict(condition='sin(alpha)!=0, r0=0, cot(alpha)=0',**geometry([ZERO]*3,[ZERO,ZERO,ONE])),
                  dict(condition='sin(alpha)!=0, r0=0, cot(alpha)!=0',degenerate='no single plane at the conical vertex'),
                  dict(condition='sin(alpha)=0',degenerate='the original coordinates containing cot(alpha) are undefined')]
        steps=['On a nonzero generator, the two parameter directions give a nonzero normal proportional to (cot(alpha)cos(phi),cot(alpha)sin(phi),−1).',
               'At the origin the nonplanar cone has several limiting surface normals. If cot(alpha)=0 the trace itself is the horizontal plane.']
    elif params==['u0','v0','a'] and chart==dict(variables=['u','v'],
            map=['u*cos(v)','u*sin(v)','a*v'],at=['u0','v0']):
        u,v=map(s,('u0','v0'));C=('cos',v);S=('sin',v);P0=[times(u,C),times(u,S),times(a,v)]
        branches=[dict(condition='a^2+u0^2>0',**geometry(P0,[times(a,S),times(m.neg(a),C),u])),
                  dict(condition='a=u0=0',**geometry(P0,[ZERO,ZERO,ONE]))]
        steps=['The two tangent vectors have cross product (a sin(v),−a cos(v),u). The norm squared is a²+u².',
               'At a=u=0 that parameterization loses rank, but the whole image for a=0 lies in and fills the horizontal plane.']
    else:raise Unsupported('The original parametric trace requires a different classification near rank loss')
    return proof('intrinsic_tangent_at_chart_rank_loss',steps,dict(branches=branches))


GRAPH_CHART_ROUTES={
    'implicit_branch_decomposition':quartic_ordinate_branches,
    'singular_curve_derivatives':singular_graph_directions,
    'implicit_differential_identity':explicit_level_differentials,
    'implicit_differentials':explicit_level_differentials,
    'implicit_derivative':homogeneous_two_coordinate_jet,
    'tangent_geometry':parametric_tangent_image,
}


def signed_source_extremum(task):
    """Certify local signs, cut points and excluded limiting values in one real variable."""
    K=task['kind'];W=task.get('requested_output');M=task.get('source',{});raw=task.get('function')
    var=task.get('variable','x');V=re.escape(var) if isinstance(var,str) and re.fullmatch(r'[a-z]',var) else None
    def result(tag,value,*steps,**witness):
        return proof(tag,steps,dict(formula=value),**witness)
    if K=='mathematical_question':
        source_fields(task,{'functions','assigned_values','requested_output'},
                      ('Prove the classifications at 0 despite both functions having all derivatives zero there.',),('page_png_sha256',))
        fs=task.get('functions');vals=task.get('assigned_values')
        if not isinstance(fs,list) or len(fs)!=2 or vals!={'f(0)':0,'g(0)':0} or W!=['prove extrema classification and flatness']:
            raise Unsupported('Both germs, their assigned values and their whole derivative assertions are required')
        F0,G0=(text_key(a) for a in fs)
        hit=re.fullmatch(r'f\(x\)=exp\(-(?:(\d+)/|1/)x\^([1-9]\d*)\)',F0)
        if not hit or int(hit[2])%2 or G0!='g(x)=x*'+F0.split('=',1)[1]:
            raise Unsupported('Need an even inverse power and the exact odd multiplier')
        p=int(hit[2]);a=int(hit[1] or 1)
        if a<=0:raise Unsupported('The exponential coefficient must produce decay')
        return result('sign_with_excluded_endpoints','f has a strict minimum at 0; g has no extremum at 0; all derivatives there vanish',
            'На проколотой области производная конечного многочлена по x,x⁻¹, умноженного на исходную экспоненту, имеет тот же вид.',
            'Подстановка u=1/|x|^p и неравенство e^(A u)≥(A u)^N/N! для любого N доказывают подавление любой фиксированной степени.',
            'Индукция по разностному отношению даёт производные ноль в назначенной точке. Знак f положителен, знак g меняется.',
            inverse_power=p,decay_scale=q(a),differentiation_invariant='Laurent polynomial times original exp')
    if K=='extremum_envelope':
        source_fields(task,{'given','requested_output'},('Определить M(x)=sup f и m(x)=inf f.','Найти M0,M1,M2.'))
        condition=text_key(task['given'])
        rational0=re.fullmatch(r'f\(xi\)=\(([1-9]\d*)\+xi\)/\(([1-9]\d*)\+xi\^2\),x<xi<\+infty',condition)
        if rational0 and W==['lower_and_upper_envelopes'] and M.get('literal_requirement') in (None,'Определить M(x)=sup f и m(x)=inf f.'):
            A,B=map(int,rational0.groups());scale=f'sqrt({A*A+B})';lo=f'(-{A}-{scale})';hi=f'(-{A}+{scale})'
            desc=f'M(x)=f({hi}) when x<={hi} and f(x) otherwise; m(x)=f({lo}) when x<={lo}, f(x) for {lo}<x<-{A}, and 0 for x>=-{A}'
            return result('sign_with_excluded_endpoints',desc,
                'Знаменатель положителен на всей оси. Знак производной задаёт A²+B−(ξ+A)², с отрицательными внешними ветвями.',
                'Верхняя кандидатная точка даёт максимум только до удаления из открытого интервала. После неё верхняя грань равна пределу у x.',
                'Для нижней грани сравниваем значение в нижней стационарной точке, левый след и нулевой предел на бесконечности.',
                stationary=[lo,hi],boundary_attainment='max attained iff x<high root; min attained iff x<low root',
                forbidden_lower_boundary=True,limit_at_infinity=ZERO,original_zero=-A)
        gaussian=re.fullmatch(r'M_k=sup\(allrealx,abs\(f\^\(k\)\(x\)\)\),f\(x\)=exp\(-(?:(\d+)\*)?x\^2\)',condition)
        if gaussian and not W and M.get('literal_requirement')=='Найти M0,M1,M2.':
            c=int(gaussian[1] or 1)
            if c<=0:raise Unsupported('A decaying Gaussian is required')
            return result('sign_with_excluded_endpoints',f'M0=1, M1=sqrt({2*c}/e), M2={2*c}',
                'Полагаем t=C x². Три веса равны e^(-t), 2√(C t)e^(-t), C|4t−2|e^(-t).',
                'Стационарный кандидат второго веса t=1/2. Для третьего веса отдельно рассматриваем t≤1/2 и t≥1/2.',
                'На второй ветви третьего веса кандидат t=3/2 даёт 4C e^(-3/2)<2C, поэтому общий максимум в t=0.',
                gaussian_scale=q(c),derivative_orders=[0,1,2],attaining_squared_scaled_coordinates=[ZERO,q(1,2),ZERO])
        raise Unsupported('An actual open interval or fixed family of derivative orders is required')
    if not V:raise Unsupported('A single original real coordinate is required')
    if 'branches' in task:
        source_fields(task,{'variable','branches','point','requested_output'},
            ('Investigate all extrema of the printed piecewise function.','Investigate the extremum at zero.'),('page_png_sha256',))
        b=task['branches']
        if not isinstance(b,list) or len(b)!=2 or b[1]!=[var+'=0','0'] or b[0][0]!=var+'!=0':
            raise Unsupported('The missing limit point must have its assigned original value')
        F0=text_key(b[0][1]);head=M.get('literal_requirement')
        bounded=re.fullmatch(r'abs\('+V+r'\)(?:\^([1-9]\d*))?\*\(([1-9]\d*)\+(sin|cos)\(1/'+V+r'\)\)',F0)
        if bounded and int(bounded[2])>1 and task.get('point')=='0' and W==['classify extremum at 0'] and head in (None,'Investigate the extremum at zero.'):
            return result('sign_with_excluded_endpoints','strict minimum at 0',
                'Осциллирующий множитель больше нуля по равномерной амплитудной оценке. Степенной множитель положителен во всех соседних ненулевых точках.',
                'Сравниваем с назначенным значением в начале. Существование там производной не требуется.',
                amplitude_lower=q(int(bounded[2])-1),checked_point=ZERO,assigned_value=ZERO)
        wave=re.fullmatch(r'exp\(-1/abs\('+V+r'\)\)\*\((sqrt\([1-9]\d*\)|[1-9]\d*)\+(sin|cos)\(1/'+V+r'\)\)',F0)
        if wave and 'point' not in task and W==['classify extrema'] and head in (None,'Investigate all extrema of the printed piecewise function.'):
            A=wave[1];S=int(A[5:-1]) if A.startswith('sqrt(') else int(A)**2
            if S<2:raise Unsupported('A trigonometric derivative can change sign below its amplitude')
            name=wave[2]
            d=('cos(t)-sin(t)','cos(t)+sin(t)') if name=='sin' else ('-sin(t)-cos(t)','-sin(t)+cos(t)')
            return result('sign_with_excluded_endpoints','strict minimum at 0; no other extrema',
                'Выбираем поперечную координату t=1/x отдельно на каждой полуоси. Она обратима, а экспонента равна e^(-|t|).',
                'После выделения положительной экспоненты амплитуда производной осциллирующего члена не превосходит √2.',
                'Знак на t>0 отрицателен вне изолированных нулей, на t<0 положителен. В назначенной точке значение ноль, а всюду рядом положительно.',
                transformed_derivative_signs=[f'{d[0]}-{A}<=0 on t>0',f'{d[1]}+{A}>=0 on t<0'],
                real_nulls_isolated=True,assigned_value=ZERO)
        raise Unsupported('The whole original punctured interval is not covered by a fixed sign bound')
    source_fields(task,{'function','variable','parameters','stated_conditions','method_requirement','requested_output'},
                  (),('definition_page','definition'))
    head=M.get('definition')
    if (head not in (None,'Strict maximum/minimum in a two-sided open neighborhood contained in the domain.')
            or task.get('parameters',[]) or task.get('stated_conditions',[]) or task.get('method_requirement') not in (None,'any')
            or W!=['all_strict_local_extrema','justification_on_original_domain'] or not isinstance(raw,str)):
        raise Unsupported('The original strict-extremum question must remain unchanged')
    pair=re.fullmatch(r'cos\(((?:[1-9]\d*\*)?'+V+r')\)\+cosh\(\1\)',raw)
    if pair:
        return result('sign_with_excluded_endpoints',f'strict global minimum: {var}=0, f=2; no local maximum',
            'На положительной полуоси после положительного масштаба sinh(t)>t≥sin(t), на отрицательной знак обратный.',
            'Критическая точка имеет строгую смену знака. Доказанные знаки охватывают всю вещественную ось.',
            derivative_signs=['negative','zero','positive'],candidate=ZERO)
    cut=re.fullmatch(r'abs\('+V+r'\)\*exp\(-abs\('+V+r'([-+])([1-9]\d*(?:/[1-9]\d*)?)\)\)',raw)
    if cut:
        a=F(cut[2]);sgn=1 if cut[1]=='-' else -1;r0=max(a,F(1));p0=sgn*r0;p1=-sgn
        return result('sign_with_excluded_endpoints',f'strict maxima at {var}={p1} and {var}={p0}; strict minimum {var}=0',
            'Разбиваем область в нулях модулей. Каждая экспонента положительна, и знак производной определяется линейным множителем.',
            'Со стороны сдвига функция сначала увеличивается и достигает максимума при |x|=max(1,|A|). На противоположной стороне |x|=1.',
            'Начало имеет значение 0 и положительные значения по обе стороны. Других смен знаков нет.',
            absolute_cuts=[ZERO,q(sgn*a)],maxima=[q(p1),q(p0)],minima=[ZERO],
            maximum_values=[('exp',q(-1-a)),m.mul(q(r0),('exp',q(a-r0)))])
    raise Unsupported('No complete one-dimensional sign split is available')


def source_curve_direction_cases(task):
    """Distinguish actual nodes, cusps and excluded endpoint tangents."""
    source_fields(task,{'source_formula','stated_conditions','requested_output'},
                  ('classify_singular_points_and_sketch_the_curve','classify_singular_points','study_curve_shape_for_all_parameters'))
    W=task['requested_output'];cond=task['stated_conditions'];f=text_key(task['source_formula'])
    def done(value,*steps,**guard):
        return proof('source_tangent_branch_cases',steps,dict(formula=value),**guard)
    if W==['study_curve_shape_for_all_parameters'] and cond==['a<=b<=c'] and f=='y^2=(x-a)*(x-b)*(x-c)':
        return done('a<b<c: oval over [a,b] and branches over [c,infinity); a=b<c: isolated a and regular c; a<b=c: node at b, regular a; a=b=c: right cusp',
            'Отмечаем все разные корни и их кратности. Знак куба на промежутках определяется чётностью кратности.',
            'Простой корень даёт одну регулярную вертикальную касательную. При двойном корне делим на квадрат смещения и проверяем знак оставшегося множителя.',
            'Положительный остаток даёт узел с двумя различными направлениями, отрицательный — изолированную точку. Тройной корень даёт односторонний касп.',
            ordered_roots=['a','b','c'],processed_multiplicities=[1,2,3],both_ordinate_signs=True,node_slopes=['-sqrt(b-a)','sqrt(b-a)'])
    if W!=['classify_singular_points'] or cond:
        raise Unsupported('A complete original singularity classification is required')
    n=r'([A-Za-z_]\w*)'
    parabola=re.fullmatch(r'y\^2='+n+r'\*x\^2\+x\^3',f)
    lemniscate=re.fullmatch(r'\(x\^2\+y\^2\)\^2='+n+r'\^2\*\(x\^2-y\^2\)',f)
    pole=re.fullmatch(r'\('+n+r'\+x\)\*y\^2=\(\1-x\)\*x\^2',f)
    if any((parabola,lemniscate,pole)):
        A=(parabola or lemniscate or pole)[1]
        if A in ('x','y','z','pi','e'):raise Unsupported('A genuine real parameter is required')
        if parabola:
            return done(f'{A}>0: node at (0,0), slopes ±sqrt({A}); {A}=0: right cusp; {A}<0: isolated origin',
                'Область задаётся знаком x²(A+x). Ноль x=−A прост для A≠0, поэтому геометрически регулярный.',
                'В проколотой окрестности начала y=x t даёт t²=A+x. При A>0 оба корня при x=0 простые.',
                'Нулевой масштаб меняет кратность на три, отрицательный оставляет только точку.',
                parameter=A,direction_equation=f't^2={A}',origin_cases=['positive','zero','negative'])
        if lemniscate:
            return done(f'{A}!=0: origin is a node, slopes ±1; {A}=0: origin isolated',
                'При ненулевом масштабе из второй компоненты градиента следует y=0, а ненулевые корни первой не лежат на уровне.',
                'Ведущая часть пропорциональна y²−x². После y=x t простые корни t=±1 продолжаются в две настоящие ветви.',
                'При нулевом масштабе исходная сумма двух квадратов в квадрате обращается в ноль только в начале.',
                parameter=A,origin_cases=['nonzero','zero'],direction_equation='t^2=1')
        return done(f'{A}!=0: origin is a node, slopes ±1; {A}=0: real line x=0, whose only nonregular point for the unreduced polynomial is the origin',
            'При ненулевом масштабе x=−A исключается из исходного равенства. Корень x=A прост; вне начала нет особых точек.',
            'Начальный остаток y²/x²=(A−x)/(A+x) стремится к 1. Получаем две простые непересекающиеся ветви на каждой стороне.',
            'При A=0 разделяем алгебраический градиент исходного произведения и реальное множество x=0, которое геометрически регулярно.',
            parameter=A,pole_checked='x=-A is not on the nonzero-scale original level',direction_equation='t^2=1')
    log=re.fullmatch(r'y=(?:(-?[1-9]\d*)\*)?x\*ln\(x\)',f)
    if log:
        A=int(log[1] or 1)
        u='downward' if A>0 else 'upward'
        return done(f'smooth for x>0; excluded closure point (0,0), vertical tangent {u}',
            'Логарифм требует x>0, там график гладок. Произведение x ln x стремится к нулю у исключённого конца.',
            'Для касательной сравниваем секущий наклон A ln x с бесконечностью. Сам конец не становится точкой исходного графика.',
            natural_domain='x>0',endpoint_in_domain=False,secant_scale=q(A))
    logistic=re.fullmatch(r'y=x/\(1\+exp\((?:([-]?[1-9]\d*)|1)/x\)\)',f)
    if logistic:
        A=int(logistic[1] or 1);slopes=[ONE,ZERO] if A>0 else [ZERO,ONE]
        return done(f'smooth for x!=0; closure corner (0,0), slopes left={int(A>0)}, right={int(A<0)}',
            'Модуль исходной функции не больше |x|, поэтому обе ветви имеют один предельный пункт.',
            'Секущий наклон 1/(1+exp(A/x)) берём отдельно слева и справа. Они дают разные касательные.',
            natural_domain='x!=0',endpoint_in_domain=False,one_sided_slopes=slopes)
    cotangent=re.fullmatch(r'y=atan\(1/sin\((?:([1-9]\d*)\*)?x\)\)',f)
    if cotangent:
        A=int(cotangent[1] or 1)
        return done(f'all x=k*pi/{A} are excluded. Closure endpoints ±pi/2 have common one-sided slope (-1)^(k+1)*{A}',
            'Нули синуса исключены из исходной области. По разным сторонам знаки синуса противоположны, а арктангенс стремится к разным концам диапазона.',
            'На каждой компоненте исходная производная равна −A cos(Ax)/(1+sin²(Ax)). У двух предельных пунктов на одной вертикали наклоны равны.',
            jump_points=f'k*pi/{A}',endpoint_in_domain=False,coincident_limits=False)
    raise Unsupported('No verified actual or limiting tangent branch is available')


def source_extrema_on_reduced_coordinates(task):
    """Reduce constrained signs without losing stationary points, boundary values or strictness."""
    K=task['kind'];goal=('classify_all_extrema_on_original_domain' if K=='multivariate_extrema'
                         else 'all_constrained_extremum_points')
    source_fields(task,{'source_formula','stated_conditions','requested_output'},(goal,),('section_convention',))
    if task.get('source',{}).get('section_convention') not in (None,
            'The strict inequalities on p340 define strict local extrema; flat attained global bounds and non-strict extrema must be identified separately.'):
        raise Unsupported('The original strict-extremum convention is required')
    C=[text_key(t) for t in task['stated_conditions']];F0=text_key(task['source_formula'])
    if task['requested_output']!=[goal]:raise Unsupported('The original questions about all extrema are required')
    def out(value,*steps,**evidence):
        return proof('extremum_via_feasible_reduction',steps,dict(formula=value),**evidence)
    N=r'([A-Za-z_]\w*)';L=r'([1-9]\d*)'
    box=lambda b:[f'0<={v}<=pi{b}' for v in 'xy']
    if K=='constrained_extrema':
        t=re.fullmatch(r'x-y=pi/'+L,C[0]) if len(C)==1 else None
        if F0=='cos(x)^2+cos(y)^2' and t and int(t[1])>=2:
            d=int(t[1])
            result=('constant 1; no strict extrema' if d==2 else
                    f'maximum y=-pi/{2*d}+k*pi; minimum y=pi/2-pi/{2*d}+k*pi; x=y+pi/{d}')
            return out(result,
                'Линейная связь даёт обратимую координату y на всей прямой. Подставляем x=y+π/d.',
                'Сумма квадратов косинусов равна 1+cos(2y+π/d)cos(π/d). Если множитель нулевой, функция постоянна.',
                'Иначе максимумы и минимумы периодического косинуса переносятся в исходные точки.',
                inverse=f'x=y+pi/{d}',complete_parameter_line=True,constant_case=d==2)
        if F0=='x*y*z' and C==['x^2+y^2+z^2=1','x+y+z=0']:
            return out('permutations of (t,t,-2*t), t=±1/sqrt(6); values -2*t^3',
                'Сфера и плоскость имеют независимые нормали на общей окружности. Значит, все экстремумы удовлетворяют стационарности Лагранжа.',
                'Попарное вычитание уравнений градиента показывает, что если все координаты различны, третьи координаты должны совпасть.',
                'При двух равных t ограничения дают третью −2t и 6t²=1. Компактность гарантирует максимум и минимум среди всех полученных точек.',
                regular_intersection=True,equality_patterns=['x=y','x=z','y=z'],t_squared=q(1,6))
        if F0=='x*y+y*z' and C==['x^2+y^2=2','y+z=2','x,y,z>0']:
            return out('unique strict maximum at (1,1,1) with value 2; infimum 0 not attained',
                'Положительные корни дают x=√(2−y²), z=2−y, значит 0<y<√2. Оба ограничения и вся открытая область восстановлены.',
                'Производная сводится к 2(1−y)[1+(1+y)/√(2−y²)]. Скобка строго положительна.',
                'Перемена знака при y=1 даёт максимум. Функция положительна и стремится к нулю на исключённом конце.',
                inverse=['x=sqrt(2-y^2)','z=2-y'],open_interval=['0','sqrt(2)'],stationary_parameter=ONE)
        if (F0=='(x-xi)^2+(y-eta)^2+(z-zeta)^2' and
                C==['A*x+B*y+C*z=0','x^2+y^2+z^2=R^2','xi/cos(alpha)=eta/cos(beta)=zeta/cos(gamma)',
                    'cos(alpha)^2+cos(beta)^2+cos(gamma)^2=1']):
            return out('q=P-n*(P.n)/|n|^2; nearest=abs(R)*q/|q|, farthest=-abs(R)*q/|q| for q!=0; constant distance if q=0',
                'Фиксированный допустимый P переносим на плоскость ортогональной проекцией q. Нормаль плоскости ненулевая.',
                'На исходной сфере квадрат расстояния равен R²+|P|²−2q·X. Остальные данные P сохраняются.',
                'При q≠0 точные концы скалярного произведения следуют из Коши и достигаются на двух концах диаметра. При q=0 все расстояния равны.',
                plane_normal=['A','B','C'],original_direction_conditions=C[2:],degenerate_radius='one point if R=0',zero_projection='entire circle')
        raise Unsupported('No signed reversible reduction for the complete constraint is available')
    ellipse=re.fullmatch(r'x\*y\*sqrt\('+L+r'-x\^2/'+N+r'\^2-y\^2/'+N+r'\^2\)',F0)
    if ellipse and C==[ellipse[2]+'>0',ellipse[3]+'>0'] and ellipse[2]!=ellipse[3] and not ({ellipse[2],ellipse[3]}&{'x','y','z'}):
        d,a,b=ellipse.groups()
        return out(f'absolute extrema at x=±{a}*sqrt({d}/3), y=±{b}*sqrt({d}/3), value sign(x*y)*{a}*{b}*({d}/3)^(3/2); boundary arcs same sign are nonstrict opposite local extrema',
            'Переходим к нормированному диску. Квадраты двух координат и оставшийся радиальный квадрат неотрицательны и в сумме дают постоянную.',
            'Квадрат модуля цели пропорционален произведению трёх долей. AM–GM даёт наибольший модуль при равных долях, строго в каждом квадранте.',
            'На границе значение ноль. По знаку xy это только нестрогий локальный минимум или максимум относительно диска. Точки осей допускают оба знака.',
            normalized_constraints=['u^2+v^2<=1','u^2','v^2','1-u^2-v^2'],equality_fractions=[q(1,3)]*3)
    projection=re.fullmatch(r'\('+N+r'\*x\+'+N+r'\*y\+'+N+r'\)/sqrt\(x\^2\+y\^2\+'+L+r'\)',F0)
    if projection:
        a,b,c,d=projection.groups()
        if (C==[f'{a}^2+{b}^2+{c}^2!=0'] and len({a,b,c})==3 and not ({a,b,c}&{'x','y','z'})):
            K=f'sqrt({a}^2+{b}^2+{c}^2/{d})';S=f'sqrt({a}^2+{b}^2)'
            return out(f'{c}!=0: sole attained extremum at ({d}*{a}/{c},{d}*{b}/{c}), value sign({c})*{K}, opposite bound -sign({c})*{S} not attained; {c}=0: both bounds ±{S} not attained',
                'Делим (x,y,√d) на его положительную норму. Получаем взаимно однозначную координату на открытой верхней полусфере.',
                'Цель становится линейным функционалом. Внутренний критический вектор параллелен его фиксированному вектору.',
                'По знаку третьего коэффициента одна из полярных точек достигается. Противоположный предел вычисляем на экваторе, который не включает инверсия.',
                excluded_equator=True,stationarity='parallel to fixed normal',hemisphere_height=d)
    if F0=='sin(x)+cos(y)+cos(x-y)' and C==box('/2'):
        return out('global maximum (pi/3,pi/6): 3*sqrt(3)/2; minima relative to the square (0,pi/2): 0 and (pi/2,0): 2',
            'Для фиксированного x сумма двух косинусов равна 2cos(x/2)cos(y−x/2). Профиль имеет максимум при y=x/2.',
            'Знак производной оставшегося максимального профиля задаёт (1+s)(1−2s), s=sin(x/2). Получаем единственную внутреннюю точку максимума.',
            'На y=π/2 нижний профиль 2sin x. В углу (π/2,0) обе входящие производные положительны; остальные границы имеют направление убывания или возрастания к другому допустимому значению.',
            maximum_fiber='y=x/2',closed_source_square=True,strict_boundary_cases=['(0,pi/2)','(pi/2,0)'])
    if F0=='sin(x)*sin(y)*sin(x+y)' and C==box(''):
        return out('strict global max x=y=pi/3; strict global min x=y=2*pi/3, values ±3*sqrt(3)/8; lower two edges nonstrict minima, upper two edges nonstrict maxima, excluding opposite corners',
            'Фиксируем s=x+y в нижнем треугольнике. Произведение синусов максимально при x=y, а профиль равен 2sin³(s/2)cos(s/2).',
            'После квадратов синуса и косинуса степенной момент достигает максимума при sin²(s/2)=3/4. Отражение обеих координат меняет знак.',
            'На краях, обращённых к треугольнику одного знака, нуль только нестрогий экстремум. У смешанных углов и на внутренней диагонали встречаются оба знака.',
            phase='s=x+y',sign_cells=['s<pi','s=pi','s>pi'],profile_equality=q(3,4))
    polar=re.fullmatch(r'x-'+L+r'\*y\+ln\(sqrt\(x\^2\+y\^2\)\)\+'+L+r'\*atan\(y/x\)',F0)
    if polar and not C:
        b,c=map(int,polar.groups())
        return out('no extrema; '+('no stationary point' if b*c==1 else f'saddle at ({F(b*c-1,b*b+1)},{F(b+c,b*b+1)})'),
            'Арктангенс y/x требует x≠0. Выбираем две полярные ветви с одним и тем же интервалом θ и независимым знаком x.',
            'Стационарность выражается A′=c A для A=cosθ−b sinθ, с противоположным знаком A и выбранной полуоси.',
            'При существовании точки радиальная вторая производная отрицательна, угловая положительна. Поэтому никакой кандидат экстремумом не является.',
            original_domain='x!=0',both_halfplanes=True,branch_equation=f'({b*c-1})*sin(theta)=({b+c})*cos(theta)')
    ring=re.fullmatch(r'x\*y\*ln\((?:\(x\^2\+y\^2\)/'+L+r'|x\^2\+y\^2)\)',F0)
    if ring and not C:
        d=int(ring[1] or 1)
        return out(f'strict local extrema at x^2+y^2={d}/e, |x|=|y|; values -{d}/(2e) for xy>0, +{d}/(2e) for xy<0; axis saddles at r^2={d}; no global extrema',
            'Проколотая область обязательна из-за логарифма. В полярных координатах цель — произведение (s ln(s/d))/2 и sin(2θ).',
            'Нули производных дают либо радиальный минимум s=d/e и край углового множителя, либо одновременные нули множителей.',
            'В первом случае совпадают требуемые знаки приращений, во втором произведение меняет знак вдоль двух независимых параметров.',
            original_domain='r>0',radial_critical=f'{d}/e',crossing_zero=d)
    separable=re.fullmatch(r'x\+y\+'+L+r'\*sin\(x\)\*sin\(y\)',F0)
    if separable and not C:
        j=int(separable[1])
        value=('no local extrema' if j<=2 else f'u=x+y, v=x-y, phi=asin(2/{j}); minima u=-phi+2k*pi and v odd multiple of pi; maxima u=pi+phi+2k*pi and v even multiple of pi; mixed cases saddles')
        return out(value,
            'Поворот u=x+y,v=x−y обратим на всей плоскости. Произведение синусов даёт сумму −(j/2)cos(u)+(j/2)cos(v).',
            'Первый профиль имеет производную 1+(j/2)sin u. При j≤2 он строго возрастает, иначе два простых ряда критических фаз.',
            'У сепарабельной суммы локальные типы совпадают только при одинаковых локальных типах обеих координат.',
            scaled_wave=j,inverse=['(u+v)/2','(u-v)/2'],global_range='unbounded both ways')
    perspective=re.fullmatch(r'x\+y\^2/\('+L+r'\*x\)\+x\^2/y\+'+L+r'/x',F0)
    if perspective and C==['x>0','y>0','z>0']:
        b,c=map(int,perspective.groups())
        return out(f't=cbrt({b}/2), A=1+3*t^2/{b}, x=sqrt({c}/A), y=t*x, every z>0: global minimum 2*sqrt({c}*A); no strict local extrema',
            'Положительное отношение t=y/x отделяет масштаб x. Цель равна xA(t)+C/x, A=1+t²/B+1/t.',
            'Знак производной A меняется единственный раз при t³=B/2. AM–GM даёт единственный масштаб x=√(C/A) для этого отношения.',
            'Исходное ограничение z>0 сохраняется. Цель от z не зависит, поэтому минимумы по всем трём координатам нестрогие.',
            ratio='t=y/x',positive_scale=True,missing_coordinate='z',strictness='flat direction')
    chain=re.fullmatch(N+r'\^2/x\+x\^'+L+r'/y\+y\^'+L+r'/z\+z\^'+L+r'/'+N,F0)
    if chain and C==[f'x,y,z,{chain[1]},{chain[5]}positive'] and chain[1]!=chain[5] and not ({chain[1],chain[5]}&{'x','y','z'}):
        a,p0,q0,r0,b=chain.groups();p0,q0,r0=map(int,(p0,q0,r0))
        weights=[p0*q0*r0,q0*r0,r0,1];J=sum(weights)
        return out(f'lambda=( {a}^{2*weights[0]}/({b}*'+ '*'.join(f'{i}^{i}' for i in weights)+f') )^(1/{J}); min={J}*lambda at x={a}^2/({weights[0]}*lambda), y=x^{p0}/({weights[1]}*lambda), z=y^{q0}/({weights[2]}*lambda)',
            'Записываем векторы показателей положительных мономов в логарифмах x,y,z. Равенство взвешенной суммы показателей нулю даёт последовательные веса.',
            'Применяем взвешенное AM–GM к каждому слагаемому, делённому на его вес. Равенство восстанавливает x,y,z по очереди.',
            'В логарифмах сумма экспонент строго выпукла, поскольку векторы показателей имеют полный ранг. Других локальных экстремумов нет.',
            weights=weights,canceled_exponents=[0,0,0],logarithmic_convexity='strict')
    if F0=='sin(x)+sin(y)+sin(z)-sin(x+y+z)' and C==['0<=x,y,z<=pi']:
        return out('strict global maximum 4 at x=y=z=pi/2; nonstrict global minima 0 on edges where two coordinates are both 0 or both pi',
            'Переносим сумму в произведение 4sin((x+y)/2)sin((y+z)/2)sin((z+x)/2). Каждый аргумент находится в [0,π].',
            'Три множителя одновременно единичны только в центре, нули дают точно перечисленные рёбра. В положительной области логарифм произведения строго вогнут.',
            'В положительной нецентральной точке есть допустимое направление к большему значению. Все вершины куба имеют значение ноль, поэтому в каждой положительной точке доступна двусторонняя координата; дополнительных минимумов нет.',
            transformed_factors=['sin((x+y)/2)','sin((y+z)/2)','sin((z+x)/2)'],strictly_concave_log=True)
    raise Unsupported('The feasible face or every stationary locus in the original domain remains to be checked')


FEASIBLE_EXTREMA_ROUTES={
    'classify_extrema':signed_source_extremum,
    'mathematical_question':signed_source_extremum,
    'extremum_envelope':signed_source_extremum,
    'plane_curve_singularity':source_curve_direction_cases,
    'multivariate_extrema':source_extrema_on_reduced_coordinates,
    'constrained_extrema':source_extrema_on_reduced_coordinates,
}


def branch_integral_proof(task,rule,value,*steps,**facts):
    data=dict(value=m.simplify(value)) if isinstance(value,tuple) else dict(formula=value) if isinstance(value,str) else value
    return proof(rule,steps,data,required_method=task.get('method_requirement'),**facts)


def checked_transport_identity(left,right,variables,scope):
    """Recompute the algebraic equality after its original denominators were guarded."""
    a,b=(m.parse(x,None,variables) for x in (left,right))
    if not same_value(a,b):raise Unsupported('Algebraic transport left an unexplained residual')
    return dict(left=a,right=b,scope=scope)


def finite_branch_source_goal(task):
    """Evaluate branch-sensitive finite integral data without deleting prescribed substitutions."""
    source_fields(task,{'integrand','integration_order','parameters','stated_conditions','requested_output',
                       'endpoint_limit','method_requirement','substitution'},
                  ('Вычислить интегралы.',),('printed_integrand',))
    order=task['integration_order'];goal=task['requested_output'];method=task.get('method_requirement')
    parameters=task.get('parameters',[]);conds=task.get('stated_conditions',[]);sub=task.get('substitution')
    if (goal!=['exact_integral'] or len(order)!=1 or not isinstance(order[0],dict) or
            set(order[0])!={'variable','lower','upper'} or order[0]['variable']!='x'):
        raise Unsupported('One original oriented interval with all conditions is required')
    lo,hi=(order[0][n] for n in ('lower','upper'));raw=text_key(task['integrand'])
    meta=task.get('source',{});literal=meta.get('printed_integrand');end=task.get('endpoint_limit')
    def answer(rule,value,*steps,**data):return branch_integral_proof(task,rule,value,*steps,original_bounds=[lo,hi],**data)
    def oriented(value,*steps,**data):return answer('source_oriented_substitution_branches',value,*steps,**data)
    def plain(meth=None):
        return method==meth and not (parameters or conds or sub or literal or end)
    posint=r'([1-9]\d*)'
    tri=re.fullmatch(r'piecewise\(xif0<=x<=([a-z]),\1\*\(1-x\)/\(1-\1\)if\1<=x<=1\)',raw)
    if (tri and lo=='0' and hi=='1' and parameters==[tri[1]] and
            not (conds or method or sub or literal or end) and tri[1]!='x'):
        T=tri[1]
        return oriented(f'{T}/(2*(1-{T})) for {T}<0; {T}/2 for 0<={T}<1; 1/2 for {T}>1; at {T}=1 the second formula is undefined at x=1 and the left trace (or first-branch endpoint) gives 1/2',
            'При параметре ниже нуля первый кусок пуст, выше единицы пуст второй. Интегрируем единственную оставшуюся линейную ветвь.',
            'Внутренний параметр даёт два треугольника. В общем стыке их ординаты совпадают.',
            'При параметре 1 у второй записи ровно в конце делитель нуль. Отдельно сохраняем левый след и значение первой ветви.',
            parameter_cells=[f'{T}<0',f'0<={T}<1',f'{T}=1',f'{T}>1'],undefined_formula_at_endpoint=True)
    if plain('integration_by_parts') and raw=='abs(ln(x))' and (lo,hi)==('1/exp(1)','exp(1)'):
        E=('exp',ONE)
        return oriented(diff(q(2),m.div(q(2),E)),
            'Делим исходный модуль в точке x=1. На обоих положительных промежутках выполняем указанное интегрирование по частям.',
            'Берём u=ln x и dv=dx. Получаем x ln x−x; левый вклад берём с минусом, правый с плюсом.',
            branches=[['1/e','1'],['1','e']],ibp_factors=['ln(x)','1'],primitive='x*ln(x)-x')
    reciprocal=re.fullmatch(r't=x-1/x',sub or '')
    if (reciprocal and method=='stated_substitution' and not (parameters or conds or literal or end)
            and raw=='(1+x^2)/(1+x^4)' and re.fullmatch(r'-[1-9]\d*(?:/[1-9]\d*)?',lo or '')
            and hi==lo[1:]):
        a=F(hi);K=a-1/a;rad=root(q(2));phi=('atan',m.div(q(K),rad)) if K else ZERO
        val=m.div(plus(P,times(q(2),phi)),rad)
        identity=checked_transport_identity('(1+1/x^2)/((x-1/x)^2+2)',raw,['x'],'x!=0')
        return oriented(val,
            'Указанное t=x−1/x разрывно в нуле. Исходное ядро там непрерывно, одиночная точка вклада не даёт. На обоих кусках производная карты строго положительна.',
            'Умножаем исходный знаменатель на 1/x². После переноса дифференциала ядро равно 1/(t²+2).',
            'Оба образа имеют по одному бесконечному концу. Арктангенсовые следы конечны, и складываем обе ориентации.',
            proposed_map='t=x-1/x',source_split=ZERO,image_branches=[[q(-K),'+infinity'],['-infinity',q(K)]],
            transformed_integrand='1/(t^2+2)',strict_jacobian='1+1/x^2',
            source_join_continuous=True,algebraic_transport=identity)
    if (sub=='t=x+1/x' and method=='stated_substitution' and not (parameters or conds or literal or end)
            and raw=='(1+x-1/x)*exp(x+1/x)' and re.fullmatch(r'[1-9]\d*',hi or '') and lo=='1/'+hi and int(hi)>1):
        B=F(hi);limit=B+1/B;val=times(q(B-1/B),('exp',q(limit)))
        identity=checked_transport_identity('1+x*(1-1/x^2)','1+x-1/x',['x'],'x>0')
        return oriented(val,
            'Указанная сумма x+1/x убывает до x=1 и возрастает после. Переносим каждую сторону к своим ориентированным концам.',
            'На ветвях x=(t±√(t²−4))/2 исходный множитель становится x′+x. Подынтегральное выражение — производная x(t)e^t.',
            'При t=2 обе обратные дают x=1 и одинаковый конечный след. Вклады в стыке сокращаются.',
            proposed_map=sub,source_split=ONE,image_branches=[[q(limit),q(2)],[q(2),q(limit)]],
            primitive='x(t)*exp(t)',inverse_branches=['(t-sqrt(t^2-4))/2','(t+sqrt(t^2-4))/2'],algebraic_transport=identity)
    if (raw=='abs(cos(x)*ln(1/x))' and parameters==['n'] and conds==['n is a natural number']
            and method is None and not sub and not end and (lo,hi)==('exp(-2*pi*n)','1')
            and literal in (None,'|cos x (ln (1/x))|')):
        return oriented('Si(1)-Si(exp(-2*pi*n))-2*pi*n*sin(exp(-2*pi*n))',
            'Именно напечатанное произведение: при 0<x≤1 оба множителя cos x и ln(1/x) неотрицательны.',
            'После интегрирования по частям остаётся sin x/x. Его первообразная Si(x)=∫₀ˣ sin(t)/t dt, в нижнем нуле вес непрерывно продолжается.',
            'Оба исходных предела остаются положительными при любом фиксированном натуральном n. Подставляем конечные следы.',
            sign_scope='0<x<=1',named_primitive={'name':'Si','continuous_derivative':'sin(x)/x','value_at_zero':ZERO},
            printed_product_preserved=True)
    mirror=re.fullmatch(r'x\*sin\(x\)/\('+posint+r'\+(?:'+posint+r'\*)?cos\(x\)\^2\)',raw)
    if plain() and (lo,hi)==('0','pi') and mirror:
        a,b=int(mirror[1]),int(mirror[2] or 1);val=m.div(times(P,('atan',root(q(b,a)))),root(q(a*b)))
        return oriented(val,
            'Отражение x↦π−x оставляет вес синуса и квадрата косинуса неизменным.',
            'Сумма двух линейных множителей равна π. После деления пополам подстановка u=cos x оставляет симметричный рациональный вес.',
            'Знаменатель A+B u² положителен на [−1,1]. Арктангенс даёт оба конечных следа.',
            reflection='pi-x',symmetric_weight=True,substitution='u=cos(x)',phase_bounds=[ONE,q(-1)])
    radicand=raw=='1/(x*sqrt(x^2-1))'
    hit=re.fullmatch(r'-([2-9]\d*|1[0-9]+)',lo or '')
    if (radicand and hit and hi=='-1' and end=={'at':'upper','side':'left'} and
            not (parameters or conds or method or sub or literal)):
        A=int(hit[1]);val=m.neg(('acos',q(1,A)))
        return oriented(val,
            'На отрицательной ветви замена u=−x переводит интервал в обратный порядок. Множитель 1/x остаётся отрицательным.',
            'У положительного края 1 исходная особенность имеет порядок (u−1)^(-1/2), поэтому односторонний интеграл существует.',
            'Производная arccos(1/u) равна 1/(u√(u²−1)) для u>1. Возвращаем отрицательный знак.',
            inverse_chart='x=-u',endpoint_exponent=q(-1,2),proper_side='u>1')
    if plain() and lo=='0' and raw=='asin(sqrt(x/(1+x)))' and re.fullmatch(posint,hi or ''):
        A=int(hi);val=diff(times(q(A+1),('atan',root(q(A)))),root(q(A)))
        return oriented(val,
            'Угол исходной обратной функции находится в первом квадранте. Его тангенс √x, поэтому получаем arctan(√x).',
            'После t=√x вес 2t arctan t. Интегрирование по частям даёт (t²+1)arctan t−t.',
            'Положительная ветвь t покрывает весь исходный отрезок, включая непрерывный нижний след.',
            inverse_chart='x=t^2, t>=0',rewritten_integrand='atan(sqrt(x))',primitive='(1+t^2)*atan(t)-t')
    period=re.fullmatch(r'([1-9]\d*)\*pi',hi or '')
    if plain() and lo=='0' and period and int(period[1])%2==0:
        periods=int(period[1])//2
        def kernel(a):return m.div(times(q(2),P),root(q(a*a-1)))
        partial=re.fullmatch(r'1/\(\('+posint+r'\+cos\(x\)\)\*\('+posint+r'\+cos\(x\)\)\)',raw)
        if partial:
            A,B=map(int,partial.groups())
            if min(A,B)>1 and A!=B:
                identity=checked_transport_identity(f'1/(({A}+u)*({B}+u))',f'(1/({A}+u)-1/({B}+u))/{B-A}',
                                                   ['u'],'abs(u)<=1')
                return oriented(times(q(periods,B-A),diff(kernel(A),kernel(B))),
                    'Оба исходных знаменателя положительны. Разложение даёт разность двух обратных линейных выражений косинуса.',
                    'В каждом полном периоде t=tan(x/2) имеет две монотонные ветви. После смены переменной получается 2dt/[(A+1)+(A−1)t²].',
                    'Объединённые вещественные лучи дают 2π/√(A²−1). Возвращаем коэффициент разложения и число периодов.',
                    complete_periods=periods,offsets=[A,B],tangent_half_angle=True,partial_fractions=identity)
        if raw=='1/(sin(x)^4+cos(x)^4)':
            return oriented(times(q(4*periods),kernel(3)),
                'Знаменатель равен (3+cos4x)/4 и строго положителен. Предлагаем фазу 4x.',
                'При подстановке нужно сохранить четыре одинаковых полных периода на каждом исходном обороте.',
                'Для одного периода применяем две полуугловые ветви и арктангенсовые следы обратного линейного косинуса.',
                original_full_periods=periods,transformed_full_periods=4*periods,phase='4*x',offset=3)
    if (raw=='x^(m-1)*(1-x)^(n-1)' and (lo,hi)==('0','1') and parameters==['m','n']
            and conds==['m is a positive integer','n is a positive integer'] and method=='repeated_integration_by_parts'
            and not (sub or literal or end)):
        return answer('finite_endpoint_index_reduction','(m-1)!*(n-1)!/(m+n-1)!',
            'Для n>1 переносим производную с (1−x)^(n−1), взяв x^m/m за первообразную другого множителя.',
            'Граничный член нулевой: m>0 убирает левый конец, n>1 правый. Получаем B(m,n)=(n−1)B(m+1,n−1)/m.',
            'При n=1 используем B(m,1)=1/m. Последовательная подстановка конечного числа понижений даёт факториалы.',
            recurrence='B(m,n)=(n-1)*B(m+1,n-1)/m for n>1',base='B(m,1)=1/m',original_index_domain='m,n positive integers')
    raise Unsupported('No certificate covers the specified finite integral and its original methods')


def explicit_substitution_source(task):
    """Validate the proposed real map by inverse images and signed bounds."""
    source_fields(task,{'statement','requested_output'},())
    t=task['statement'];W=task['requested_output']
    def emit(value,*steps,**details):
        return branch_integral_proof(task,'source_oriented_substitution_branches',value,*steps,**details)
    refusal=re.fullmatch(r'∫₀([²³⁴⁵⁶⁷⁸⁹]) x ∛\(1−x²\) dx; можно ли положить x=sin t и если нет, почему\?',t)
    if W==['decision','explanation'] and refusal:
        b=int(refusal[1].translate(str.maketrans('²³⁴⁵⁶⁷⁸⁹','23456789')))
        return emit('the proposed real substitution is invalid',
            'Вещественный кубический корень определён при всех исходных x, в том числе при x>1.',
            'Образ синуса содержится в [−1,1]. Хвост от 1 до исходного верхнего предела не имеет действительного прообраза.',
            source_interval=[ZERO,q(b)],map_range=[q(-1),ONE],missing_source_interval=['1',str(b)])
    if W==['decision','explanation'] and t=='∫₀¹ √(1−x²) dx; при подстановке x=sin t можно ли взять пределы π и π/2?':
        return emit('the bounds pi to pi/2 are valid, and the integral equals pi/4',
            'На [π/2,π] синус строго убывает с 1 до 0, поэтому в указанном ориентированном порядке он покрывает x от 0 до 1.',
            'На этой ветви cos t≤0, значит корень равен −cos t. Вместе с dx получаем −cos²t.',
            'Интеграл от π к π/2 сохраняет знак и равен π/4.',
            covering=True,orientation='decreasing map, descending parameter bounds',parameter_bounds=['pi','pi/2'],
            pulled_back_integrand='-cos(t)^2')
    m0=re.fullmatch(r'В ∫₀\^\{2π\} ([A-Za-z])\(x\)cos\(x\)dx выполнить замену sin\(x\)=t\.',t)
    if W==['transformed_integral'] and m0:
        f=m0[1];terms=[f'{f}(asin(t))',f'{f}(pi-asin(t))',f'{f}(2*pi+asin(t))']
        V=f'integral(0,1,{terms[0]}) + integral(1,-1,{terms[1]}) + integral(-1,0,{terms[2]})'
        return emit(V,
            'На полном периоде делим в максимуме и минимуме синуса. На каждом участке выбираем свою действительную обратную ветвь.',
            'Ориентации t равны 0→1, 1→−1, −1→0. Множитель cos x dx превращается в dt с исходным знаком.',
            'Функция произвольна, поэтому её значения на разных обратных ветвях не отождествляем.',
            branch_bounds=[[0,1],[1,-1],[-1,0]],inverse_branches=['asin(t)','pi-asin(t)','2*pi+asin(t)'],
            carried_integrands=terms)
    raise Unsupported('The original map or its entire signed interval could not be bound')


def endpoint_and_weight_sources(task):
    """Bind improper traces, reductions, comparisons and mean-point branches."""
    K=task['kind'];W=task.get('requested_output');meta=task.get('source',{});x=task.get('variable')
    def measure(value,*step,**evidence):
        return branch_integral_proof(task,'exact_weighted_interval_transfer',value,*step,**evidence)
    def reduction(value,*step,**evidence):
        return branch_integral_proof(task,'finite_endpoint_index_reduction',value,*step,**evidence)
    if K=='integral_reduction_family':
        source_fields(task,{'integrand','variable','lower','upper','index','parameters','index_domain','method_requirement','requested_output'},
                      (),('printed_instruction',))
        if (meta.get('printed_instruction') not in (None,'С помощью формул понижения вычислить интегралы, зависящие от параметра n, принимающего целые положительные значения.')
                or x!='x' or task['index']!='n' or task['index_domain']!='positive_integers' or task['integrand']!='x^m*ln(x)^n'
                or (task['lower'],task['upper'])!=('0','1') or task['parameters']!=['m']
                or task.get('method_requirement')!='reduction_formula' or W!=['exact_indexed_integral']):
            raise Unsupported('The printed recurrence and its whole parameter space are required')
        return reduction('(-1)^n*n!/(m+1)^(n+1) if m>-1; divergent with sign (-1)^n if m<=-1',
            'При m>−1 степенная первообразная x^(m+1)/(m+1) существует. На нижнем конце она подавляет любую фиксированную степень логарифма.',
            'По частям получаем I_n=−n I_(n−1)/(m+1) и I_0=1/(m+1), что даёт указанную формулу.',
            'При m≤−1 замена t=−ln x оставляет несобственный хвост e^(−(m+1)t)t^n с постоянным знаком. Он расходится.',
            recurrence='I_n=-n*I_(n-1)/(m+1)',initial_value='1/(m+1)',convergence_condition='m>-1')
    if K=='indexed_integral_identity':
        source_fields(task,{'indices','stated_conditions','definition','claim','requested_output'},())
        if (W!=['proof'] or task['indices']!=['m','n'] or task['stated_conditions']!=['m,n nonnegative integers']
                or task['definition']!='P_n(x)=d^n/dx^n((x^2-1)^n)/(2^n*n!)'
                or task['claim']!='integral(-1,1,P_m(x)*P_n(x),x) = (0 if m!=n else 2/(2*n+1))'):
            raise Unsupported('The original Rodrigues scaling and both index cases are required')
        return reduction('integral P_m*P_n = 0 if m!=n, 2/(2*n+1) if m=n',
            'При разных индексах переносим производную большего порядка. У (x²−1)^n на обоих концах кратность n, поэтому все граничные члены нулевые.',
            'На меньшем многочлене производная большего порядка тождественно нулевая. При равных индексах остаётся ведущий коэффициент (2n)!/(2^n(n!)²).',
            'Момент (1−x²)^n переводим u=(x+1)/2 в бета-интеграл B(n+1,n+1). По конечной рекурсии он равен (n!)²/(2n+1)!.',
            original_method='repeated integration by parts from Rodrigues',scaling='2*4^n',zero_boundary_orders='0,...,n-1')
    if K=='prove_integral_identity':
        source_fields(task,{'integrand','variable','lower','upper','parameters','parameter_domains','conclusion',
                           'left','right','stated_conditions','method_requirement','requested_output'},
                      (['proof'],),('printed_instruction',))
        if (x=='x' and W is None and task.get('method_requirement')=='euler_formula'
                and set(task)-{'kind','source','id','integrand','variable','lower','upper','parameters','parameter_domains',
                              'conclusion','method_requirement'}==set()
                and task['parameter_domains']=={'m':'integer','n':'integer'} and task['parameters']==['m','n']
                and (task['lower'],task['upper'])==('0','2*pi')
                and task['integrand']=='exp(i*n*x)*exp(-i*m*x)' and task['conclusion']=={'m!=n':'0','m=n':'2*pi'}
                and meta.get('printed_instruction') in (None,'Пользуясь формулой Эйлера, показать, что')):
            return reduction('0 if m!=n; 2*pi if m=n',
                'Выписываем действительную и мнимую компоненты по напечатанной формуле Эйлера. Произведение соответствует частоте k=n−m.',
                'Для k≠0 первообразные синуса и косинуса имеют одинаковые следы на концах целого числа оборотов. При k=0 вес равен 1.',
                integer_frequency='n-m',used_euler_formula=True,phase_span='2*pi*(n-m)')
        if (x=='x' and W==['proof'] and task.get('parameters')==['a','b']
                and set(task)-{'kind','source','id','variable','parameters','left','right','stated_conditions','requested_output'}==set()
                and task['stated_conditions']==['a>0','b>0','The integral on the left exists.']
                and task['left']=='integral(f(a*x+b/x), x, 0, +inf)'
                and task['right']=='integral(f(sqrt(x^2+4*a*b)),x,0,+inf)/a'
                and meta.get('printed_instruction') is None):
            identity=checked_transport_identity('(a*x+b/x)^2-4*a*b','(a*x-b/x)^2',['x','a','b'],'x,a,b>0')
            return branch_integral_proof(task,'source_oriented_substitution_branches','the printed two integrals are equal',
                'На x>0 имеем (ax+b/x)²−4ab=(ax−b/x)². Предлагаем t=|ax−b/x|, делим при x=√(b/a).',
                'Обратные x_±=(±t+√(t²+4ab))/(2a). На первой ветви t убывает, на второй возрастает.',
                'Разность производных x_+′−x_-′=1/a. Пределы переносятся из существующих исходных несобственных частей.',
                proposed_map='abs(a*x-b/x)',source_split='sqrt(b/a)',pulled_argument='sqrt(t^2+4*a*b)',
                reduced_jacobian='1/a',orientation=['infinity to 0','0 to infinity'],algebraic_transport=identity)
        raise Unsupported('The exact printed identity, including the zero-frequency or reciprocal branch, must be retained')
    if K=='integral_mean_point_parameter':
        heading='Пусть ∫_0^x f(t)dt=x f(θx). Найти θ, а также lim_{x→+0}θ и lim_{x→+∞}θ для данной функции.'
        source_fields(task,{'function','variable','endpoint','parameters','stated_conditions','requested_output'},(heading,))
        if (x!='t' or task['endpoint']!='x' or
                W!=['mean_point_parameter','limit_at_zero_from_right','limit_at_positive_infinity']):
            raise Unsupported('The original mean point and both limits must be requested')
        raw=task['function'];C=task['stated_conditions'];params=task['parameters']
        if raw=='t^n' and C==['n>-1'] and params==['n']:
            return measure('n!=0: theta=(n+1)^(-1/n), both limits equal theta; n=0: theta arbitrary, limits not determined',
                'Условие n>−1 гарантирует сходимость у нуля. Среднее на [0,x] равно x^n/(n+1).',
                'При n≠0 положительная степенная функция взаимно однозначна и даёт θ∈(0,1). Значение не зависит от x.',
                'При n=0 функция постоянна. Из равенства нельзя вывести уникальную функцию θ(x) или её пределы.',
                parameter_domain='n>-1',zero_index_is_degenerate=True,original_point='theta*x')
        if raw=='ln(t)' and not (C or params):
            return measure('theta=exp(-1); both limits exp(-1)',
                'Несобственный левый след t ln t равен нулю. Среднее значение ln x−1.',
                'Равенство ln(θx)=ln x−1 имеет единственное 0<θ<1. Возвращаем этот постоянный результат для обоих пределов.',
                endpoint_trace=ZERO,unique_point=True)
        scale=re.fullmatch(r'exp\((?:([1-9]\d*)\*)?t\)',raw)
        if scale and not (C or params):
            A=int(scale[1] or 1)
            return measure(f'theta=ln((exp({A}*x)-1)/({A}*x))/({A}*x); limits 1/2 and 1',
                'Среднее строго между исходными конечными значениями. Обратная экспонента даёт единственную θ в (0,1).',
                'При u=A x→0⁺ имеем (e^u−1)/u=1+u/2+O(u²). Логарифмический предел равен половине.',
                'При u→∞ выделяем e^u. Деление ln u и ограниченного остатка на u оставляет единицу.',
                exponential_rate=q(A),limits=[q(1,2),ONE],normalized_scale='u=A*x')
        raise Unsupported('Mean point and endpoint behavior not established')
    if K=='improper_integral':
        source_fields(task,{'integrand','variable','lower','upper','requested_output'},(['exact_integral'],))
        raw=task['integrand'];g=re.fullmatch(r'ln\((sin|cos)\((?:([1-9]\d*)\*)?x\)\)',raw)
        if x=='x' and W==['exact_integral'] and g and task['lower']=='0':
            n=int(g[2] or 1)
            if task['upper']!=('pi/2' if n==1 else f'pi/{2*n}'):
                raise Unsupported('The logarithmic singularity must be on the exact quarter period')
            return measure(times(q(-1,2*n),P,('ln',q(2))),
                'Около нуля sin t∼t. Логарифмическая особенность интегрируема, а косинусный случай переносится отражением.',
                'Складываем два равных интеграла. ln(sin t cos t)=ln(sin(2t))−ln 2.',
                'Двойная фаза и отражение второй половины дают 2I=I−π ln 2/2. Возвращаем исходный масштаб.',
                original_singular_endpoint='left' if g[1]=='sin' else 'right',phase_scale=q(n),endpoint_kind='integrable logarithm')
    raise Unsupported('The complete weighted interval, tail, or original claim remains open')

def integral_on_real_components(task):
    """Sum all positive periodic components with their actual endpoint limits."""
    K=task['kind'];raw=task['integrand']
    if K=='integral_over_natural_domain':
        source_fields(task,{'variable','integrand','ambient_interval','domain','requested_output'},())
        span=task['ambient_interval']
        if (task['variable']!='x' or task['requested_output']!=['exact_integral'] or
                task['domain']!='all points where the integrand is defined' or len(span)!=2 or span[0]!='0'):
            raise Unsupported('The complete source interval and natural-domain measure are required')
        n=re.fullmatch(r'([1-9]\d*)\*pi',span[1])
        if not n or int(n[1])%2 or raw!='abs(cos(x))*sqrt(sin(x))':
            raise Unsupported('The real-domain lobes and exact endpoint integral must be associated')
        J=int(n[1])//2;val=q(4*J,3)
        return branch_integral_proof(task,'exact_weighted_interval_transfer',val,
            'Исходный квадратный корень требует sin x≥0. На указанном числе оборотов остаются все положительные полуволны и одиночный правый край.',
            'Делим каждую полуволну в максимуме синуса. Подстановка t=sin x с модулем косинуса даёт одинаковую меру на обеих монотонных ветвях.',
            'Один вклад равен ∫₀¹√t dt=2/3. Одиночная точка площади не добавляет.',
            positive_lobes=J,component='[2*k*pi,(2*k+1)*pi]',isolated_endpoint=span[1],monotone_branches=2*J)
    source_fields(task,{'variable','integrand','original_set','requested_output'},(['exact_integral'],))
    if (task['variable']!='x' or task['requested_output']!=['exact_integral'] or
            task['original_set']!='All x in (0,+infinity) at which the original integrand is real and defined.'):
        raise Unsupported('The natural domain and all positive periods are necessary')
    hit=re.fullmatch(r'exp\(-(?:(\d+)\*)?x/2\)\*abs\((?:(\d+)\*)?sin\(x\)-cos\(x\)\)/sqrt\(sin\(x\)\)',raw)
    if not hit or hit[1]!=hit[2] or int(hit[1] or 1)<=0:
        raise Unsupported('The full signed weight must differentiate the proposed positive profile')
    a=int(hit[1] or 1);phi=('atan',q(1,a))
    fac=m.div(q(4),root(root(q(1+a*a))))
    shift=('exp',m.neg(times(q(a,2),phi)));ratio=('exp',m.neg(times(q(a),P)))
    val=m.div(times(fac,shift),diff(ONE,ratio))
    return branch_integral_proof(task,'exact_weighted_interval_transfer',val,
        'Первоначальный знаменатель требует sin x>0, поэтому оставляем только открытые положительные полуволны.',
        'На каждой компоненте вес равен 2|F′| для F=e^(-a x/2)√(sin x). У обоих исключённых концов F стремится к нулю.',
        'Знак меняется в единственной вершине atan(1/a) внутри положительной полуволны. Полная вариация даёт четыре высоты F.',
        'При сдвиге на 2π вклад умножается на e^(-aπ)<1. Суммируем абсолютно сходящийся геометрический ряд.',
        original_components='(2*k*pi,(2*k+1)*pi)',endpoint_traces=[ZERO,ZERO],
        stationary_phase=phi,scale=a,geometric_ratio=ratio,finite_variation=True)


def source_projected_curve_measure(task):
    """Prove the projected strip or metric weight from the original geometric data."""
    K=task['kind'];W=task.get('requested_output')
    def out(value,*steps,**details):
        return branch_integral_proof(task,'curve_measure_from_complete_components',value,*steps,**details)
    if K=='prove_or_decide_integral_statement':
        source_fields(task,{'statement','requested_output'},())
        stated='Доказать, что прямой параболический сегмент с основанием b и высотой h (рис. 13) имеет площадь (2/3)bh.'
        if W!=['proof_or_counterexample'] or task['statement']!=stated:
            raise Unsupported('The original segment must be a direct parabolic cap')
        return out('2*b*h/3',
            'Направляем ось x вдоль хорды основания, её середина в начале. У прямого сегмента вершина на оси на высоте h.',
            'Парабола и условие x=±b/2 на основании дают верхнюю границу h(1−4x²/b²). Толщина положительна внутри хорды.',
            'Подстановка u=2x/b переводит полную область в −1≤u≤1. Интеграл (bh/2)∫(1−u²)du равен 2bh/3.',
            normalized_projection=['-1','1'],width_scale='b/2',height_fraction='1-u^2',direct_cap=True)
    if K=='bounded_solid_volume':
        source_fields(task,{'surfaces','requested_output'},('Вычислить объём тела по напечатанным поверхности и плоскостям.',))
        raw=text_key(task['surfaces']);label='x'
        if ';y=' in raw:
            raw=raw.translate(str.maketrans('xy','yx'))
            label='y'
        name=r'([A-Za-z_]\w*)'
        match=re.fullmatch(r'z=\+'+name+r',-\1;x='+name+r'\*cos\(u\)\*cos\(v\)\+'+name+
            r'\*sin\(u\)\*sin\(v\),y=\2\*cos\(u\)\*cos\(v\)-\3\*sin\(u\)\*cos\(v\),z=\1\*sin\(u\)',raw)
        if not match or W!=['exact_volume']:
            raise Unsupported('The paired elliptic fibers must follow from the complete original parametrization')
        c,a,b=match.groups()
        if len({a,b,c})!=3 or {a,b,c}&({'x','y','z','u','v','pi','e'}|m.FUNCTIONS):
            raise Unsupported('Three independent geometric scales are necessary')
        identity=checked_transport_identity('(1-r^2)/(B^2+(A^2-B^2)*r^2)',
            '(A^2/(B^2+(A^2-B^2)*r^2)-1)/(A^2-B^2)',['A','B','r'],'A,B>0; A!=B; 0<=r<=1')
        formula=(f'A=abs({a}), B=abs({b}), C=abs({c}); V=0 if B*C=0; V=2*pi*B^2*C/3 if A=0; '
            'otherwise d=sqrt(A^2+B^2), s0=A/d, u0=B/d, D=A^2-B^2, '
            'V=pi*A*B*C*(3-2*u0^3)/3 + 2*pi*B^2*C*(1-s0^3)/3 + 4*A*B^3*C*(2*H(u0)-H(1))/3, '
            'H(p)=(A^2*J(p)-p)/D for D!=0, H(p)=(p-p^3/3)/B^2 for D=0, '
            'J(p)=atan(p*sqrt(D)/B)/(B*sqrt(D)) for D>0 and '
            'atanh(p*sqrt(-D)/B)/(B*sqrt(-D)) for D<0')
        return out(formula,
            'При s=z/c обе допустимые косинусные ветви дают сечения x=p cos v+q sin v, y=(p±q) cos v после перепараметризации.',
            'Здесь p=A√(1−s²), q=B|s|. Вне обеих эллиптических областей можно уйти вдоль горизонтального луча. Внутри хотя бы одной нельзя выйти из неё без пересечения стенки. Поэтому берём объединение всех ограниченных компонент.',
            'При x положительном и t=x/√(p²+q²) допустимый косинус v лежит между (p t±q√(1−t²))/√(p²+q²). Два интервальных сечения умножают его на p+q и p−q с сохранением знака.',
            'Порядок концов меняется при t=q/√(p²+q²) и t=1/√2. Интегрируем объединение интервалов с однократным учётом перекрытия.',
            'Для p≥q площадь равна (3π/2)pq+2q²atan(q/p). Для q>p получаем (π/2)pq+2q²[π−atan(q/p)]. Обе формулы сходятся при p=q.',
            'Высотные ветви разделены в s0=A/√(A²+B²). Для арктангенсового интеграла по частям, затем r=√(1−s²) дают H′(r)=(1−r²)/(B²+(A²−B²)r²).',
            'При A=0 эллипсы совпадают, при B*C=0 пространственного объёма нет. Для одной выбранной широтной ветви объём отдельно равен 2πBC(A+B−AB/d)/3.',
            projection_axis=label,includes_both_cosine_branches=True,height_range=f'[-abs({c}),abs({c})]',
            union_section_switches=['q/sqrt(p^2+q^2)','1/sqrt(2)'],positive_slice_cases=['p>=q','p<q'],
            auxiliary_primitive_identity=identity,single_elliptic_sheet_volume='2*pi*B*C*(A+B-A*B/d)/3',
            boundary_coverage='union of all bounded components separated by original sheets and caps')
    if K=='area_bounded_by_curves':
        source_fields(task,{'equations','coordinate_system','parameters','stated_conditions','requested_output'},())
        if task['coordinate_system']!='rectangular' or W!=['bounded_area'] or task['parameters']:
            raise Unsupported('The complete original rectangular area is required')
        S=task['equations'];C=task['stated_conditions']
        if len(S)==4 and not C and S[1]=='y=0':
            log=re.fullmatch(r'y=abs\(log([1-9]\d*)\(x\)\)',S[0])
            if log and int(log[1])>1 and S[2:]==['x=1/'+log[1],'x='+log[1]]:
                B=int(log[1]);primitive='(x*ln(x)-x)/ln(B)'
                value=plus(q(B-F(1,B)),m.div(q(2-B-F(1,B)),('ln',q(B))))
                return out(value,
                    'Вертикальные границы положительны. Внутри них слой между 0 и модулем логарифма однозначен.',
                    'В точке x=1 логарифм меняет знак. Применяем первообразную (x ln x−x)/ln B отдельно с обоими знаками.',
                    projection_variable='x',branches=[[q(1,B),ONE],[ONE,q(B)]],primitive=primitive)
        if len(S)==3 and not C and S[2]=='x=0':
            base=re.fullmatch(r'y=([1-9]\d*)\^x',S[0]);top=re.fullmatch(r'y=([1-9]\d*)',S[1])
            if base and top and min(int(base[1]),int(top[1]))>1:
                B,H=int(base[1]),int(top[1]);L=('ln',q(B));z=ONE if B==H else m.div(('ln',q(H)),L)
                return out(diff(times(q(H),z),m.div(q(H-1),L)),
                    'Решаем пересечение верхней горизонтали и строго возрастающей экспоненты. Правый конец ln(H)/ln(B)>0.',
                    'На исходной полосе толщина H−B^x неотрицательна. Вычитаем два интеграла между 0 и точкой пересечения.',
                    projection_variable='x',right_endpoint=z,vertical_thickness=f'{H}-{B}^x')
        sine=re.fullmatch(r'x=(?:([1-9]\d*)\*)?sin\(pi\*y\)',S[1]) if len(S)==3 else None
        if (sine and S[0]=='y=(x+1)^2' and S[2]=='y=0' and C==['0<=y<=1']):
            B=int(sine[1] or 1)
            return out(plus(q(1,3),m.div(q(2*B),P)),
                'По горизонтальной координате y обе параболические ветви равны −1±√y. Синус неотрицателен на исходном интервале.',
                'Правая параболическая ветвь встретит синус при y=1. Левая на всём исходном промежутке не встречается с синусом и не замыкает эту область.',
                'Толщина B sin(πy)+1−√y неотрицательна. Интегрируем её по 0≤y≤1.',
                projection_variable='y',source_intersections=[['y=0','lower end'],['y=1','right branch meets sine']],
                horizontal_bounds=['-1+sqrt(y)',f'{B}*sin(pi*y)'])
        raise Unsupported('One bounded component and exact projected thickness are required')
    if K=='polar_curve_length':
        source_fields(task,{'curve','stated_conditions','requested_output'},('Найти длину дуги кривой.',))
        hit=re.fullmatch(r'r\^n=([a-z])\^n\*cos\(n\*phi\)',task['curve'])
        if (W!=['arc_length'] or not hit or hit[1] in ('n','r') or
                task['stated_conditions']!=[hit[1]+'>0','n positive integer']):
            raise Unsupported('The positive scale and all polar lobe indices are required')
        A=hit[1]
        return out(f'full curve length {A}*Beta(1/2,1/(2*n)); each of n lobes has 1/n of this length',
            'В положительном радиусе область cos(nφ)≥0 разбивается на n одинаковых лепестков. Отрицательные радиусы после (r,φ)↦(−r,φ+π) не дают новой точки.',
            'На внутренности r′=−r tan(nφ); скорость по полярному углу равна A cos(nφ)^(1/n−1).',
            'Показатель больше −1, поэтому край интегрируем. Подстановка u=nφ, затем s=sin²u даёт бета-интеграл и множитель 1/n на лепесток.',
            angular_coverage='n distinct nonnegative-radius lobes',endpoint_integrability='1/n-1>-1',
            phase_metric='A*cos(u)^(1/n-1)',beta_arguments=['1/2','1/(2*n)'])
    raise Unsupported('The complete geometrical profile is not available')


SOURCE_MEASURE_BRANCHES={
    'iterated_integral':finite_branch_source_goal,
    'integral_substitution_validity':explicit_substitution_source,
    'transform_definite_integral':explicit_substitution_source,
    'integral_reduction_family':endpoint_and_weight_sources,
    'indexed_integral_identity':endpoint_and_weight_sources,
    'prove_integral_identity':endpoint_and_weight_sources,
    'integral_mean_point_parameter':endpoint_and_weight_sources,
    'improper_integral':endpoint_and_weight_sources,
    'integral_over_natural_domain':integral_on_real_components,
    'improper_integral_on_set':integral_on_real_components,
    'area_bounded_by_curves':source_projected_curve_measure,
    'polar_curve_length':source_projected_curve_measure,
    'prove_or_decide_integral_statement':source_projected_curve_measure,
    'bounded_solid_volume':source_projected_curve_measure,
}


def selected_source_measure_branch(task):
    build=SOURCE_MEASURE_BRANCHES.get(task.get('kind'))
    if build is None:return None
    try:return build(task)
    except (Unsupported,KeyError,TypeError,ValueError,ZeroDivisionError,IndexError,AttributeError):
        return None


def projection_orders_source(task):
    """Project a common three-dimensional body in each of the six coordinate orders."""
    source_fields(task,{'integrand','source_order','requested_output'},
                  ('Расставить пределы тройного интеграла различными способами.',))
    kind=task['kind'];raw=text_key(task['source_order']);f=task['integrand']
    if kind!='triple_integration_orders' or task['requested_output']!=['alternative_orders_with_bounds'] or not re.fullmatch(r'[A-Za-z]\w*\(x,y,z\)',f):
        raise Unsupported('All original coordinate orders and the unchanged kernel are required')
    integer=r'([1-9]\d*)'
    triangle=re.fullmatch(r'0<=x<='+integer+r',0<=y<=\1-x,0<=z<=x\+y',raw)
    cone=re.fullmatch(r'-'+integer+r'<=x<=\1,-sqrt\((\d+(?:\^2)?)-x\^2\)<=y<=sqrt\(\2-x\^2\),sqrt\(x\^2\+y\^2\)<=z<=\1',raw)
    powers=re.fullmatch(r'0<=x<='+integer+r',0<=y<=\1,0<=z<=x\^'+integer+r'\+y\^\2',raw)
    if not (triangle or cone or powers):
        raise Unsupported('The exact projected fibers are not proved')
    if cone:
        L,base=cone.groups()
        if (int(base[:-2])**2 if base.endswith('^2') else int(base))!=int(L)**2:
            raise Unsupported('The source disk radius must agree with the cone cap')
    def fiber(v,lo,hi):
        return dict(variable=v,lower=str(lo),upper=str(hi))
    def emit(a,b):
        if triangle:
            L=triangle[1];q=f'{a}+{b}';inner=(f'max(0,z-{a})',f'{L}-{a}')
            explanation=[
                'Исходно x≥0,y≥0,x+y≤L и 0≤z≤x+y. При фиксированном z нижняя граница второго поперечного координатного сечения max(0,z−x).',
                'Максимум суммы x+y равен L независимо от фиксированного x, поэтому 0≤z≤L. Нижняя граница не превосходит верхней именно на этой проекции.',
                'Перестановка x,y оставляет ограничивающие выражения симметричными. Ядро интеграла сохраняется в исходном порядке аргументов.']
            return ([fiber(a,0,L),fiber(b,0,f'{L}-{a}'),fiber('z',0,q)],
                    [fiber(a,0,L),fiber('z',0,L),fiber(b,*inner)],
                    [fiber('z',0,L),fiber(a,0,L),fiber(b,*inner)]),explanation
        if cone:
            L=cone[1]
            zroot=f'sqrt(z^2-{a}^2)';cap=f'sqrt({base}-{a}^2)'
            explanation=[
                'Диск исходной проекции следует из x²+y²≤z² и z≤L. В обратную сторону это неравенство равносильно исходной нижней границе z≥√(x²+y²).',
                'При фиксированном z сечение — полный диск радиуса z, поэтому поперечные пределы включают оба знака корня.',
                'При фиксированной первой координате минимальная высота |x|. Якобиан перестановки равен единице по модулю.']
            return ([fiber(a,'-'+L,L),fiber(b,'-'+cap,cap),fiber('z',f'sqrt({a}^2+{b}^2)',L)],
                    [fiber(a,'-'+L,L),fiber('z',f'abs({a})',L),fiber(b,'-'+zroot,zroot)],
                    [fiber('z',0,L),fiber(a,'-z','z'),fiber(b,'-'+zroot,zroot)]),explanation
        L,p=map(int,powers.groups()); cap=L**p;upper=2*cap
        qa,qb=f'{a}^{p}',f'{b}^{p}'
        def threshold(rhs):
            term=f'max(0,{rhs})'
            return term if p==1 else f'sqrt({term})' if p==2 else f'({term})^(1/{p})'
        inner=threshold(f'z-{qa}')
        explanation=[
            'На неотрицательном квадрате обе степени монотонны. При фиксированных x,z из y^p≥z−x^p получаем y≥(max(0,z−x^p))^(1/p).',
            'Чтобы такая y была не выше L, необходимо и достаточно z≤x^p+L^p. Для проекции на z,x это даёт x≥(max(0,z−L^p))^(1/p).',
            'Полный диапазон z идёт от 0 до 2L^p. Переходы внутри max сохраняют области с отрицательным правым выражением и обе части высот.']
        return ([fiber(a,0,L),fiber(b,0,L),fiber('z',0,f'{qa}+{qb}')],
                [fiber(a,0,L),fiber('z',0,f'{qa}+{cap}'),fiber(b,inner,L)],
                [fiber('z',0,upper),fiber(a,threshold(f'z-{cap}'),L),fiber(b,inner,L)]),explanation
    left,explain=emit('x','y');right,_=emit('y','x');rows=[*left,*right]
    assert len({tuple(x['variable'] for x in d) for d in rows})==6
    show=[' '.join(f"{t['lower']}<={t['variable']}<={t['upper']}" for t in d) for d in rows]
    return proof('complete_projected_fibers',explain,
                 dict(formula=' | '.join(show),integration_orders=rows,unchanged_integrand=f),
                 original_bounds=raw,nonempty_projection_checked=True,equivalence='monotone scalar elimination on both coordinate signs')


def spherical_projection_source(task):
    source_fields(task,{'integrand','region','requested_output'},
                  ('Перейти к сферическим координатам в интеграле от радиальной f.',))
    raw=text_key(task['region']);shape=re.fullmatch(r'boundedbyz=x\^2\+y\^2,x=y,x=([1-9]\d*),y=0,z=0',raw)
    f=re.fullmatch(r'([A-Za-z]\w*)\(sqrt\(x\^2\+y\^2\+z\^2\)\)',task['integrand'])
    if not (shape and f) or task['requested_output']!=['transformed_integrand_with_jacobian','bounds']:
        raise Unsupported('The complete original spherical chart must be bound')
    cap,fn=shape[1],f[1]
    bounds=[['phi','0','pi/4'],['psi','0',f'atan({cap}/cos(phi))'],
            ['r','sin(psi)/cos(psi)^2',f'{cap}/(cos(phi)*cos(psi))']]
    return proof('complete_projected_fibers',[
        'Используем исходную сферическую широту ψ от горизонтальной плоскости. Из 0≤y≤x следует 0≤φ≤π/4, а z≥0 даёт ψ≥0.',
        'При r>0 неравенство z≤x²+y² равносильно r≥sinψ/cos²ψ. Условие x≤L даёт r≤L/(cosφ cosψ). Вертикальная ось вне внутренности области.',
        'Совместимость двух радиальных пределов равносильна tanψ≤L/cosφ. У единичной сферы координатная плотность r²cosψ.',
        'Начало и границы с неполным углом имеют нулевую объёмную меру. Ядро f зависит от r, дополнительных ограничений для него не вводим.'],
        dict(formula=f'{fn}(r)*r^2*cos(psi); phi: 0..pi/4; psi: 0..atan({cap}/cos(phi)); r: sin(psi)/cos(psi)^2..{cap}/(cos(phi)*cos(psi))',
             integration_order=bounds,jacobian='r^2*cos(psi)'),
        original_coordinates=['r cos(phi) cos(psi)','r sin(phi) cos(psi)','r sin(psi)'],azimuth_projection=True,source_bounds=raw)


def solid_angle_source(task):
    source_fields(task,{'observer','rectangle','requested_output'},
                  ('Найти телесный угол прямоугольника и приближённую формулу при большом a.',))
    N=r'([A-Za-z_]\w*)'
    hit=re.fullmatch(r'x='+N+r'>0,0<=y<='+N+r',0<=z<='+N,task['rectangle'])
    if not hit or task['observer']!=[0,0,0] or task['requested_output']!=['exact_solid_angle','large_distance_approximation']:
        raise Unsupported('The full rectangular viewing domain and both measures are required')
    a,b,c=hit.groups()
    if len(set((a,b,c)))!=3 or {a,b,c}&({'x','y','z','pi','e'}|m.FUNCTIONS):
        raise Unsupported('The three original geometric parameters must be independent')
    a0,b0,c0=map(s,(a,b,c));p=squared(a0);q0=squared(b0);r0=squared(c0)
    norm2=plus(p,q0,r0);den=times(p,norm2);numer=times(q0,r0)
    if not same_value(plus(den,numer),times(plus(p,q0),plus(p,r0))):
        raise Unsupported('Failed to verify the mixed corner primitive factorization')
    angle=('atan',m.div(times(b0,c0),times(a0,root(norm2))))
    leading=m.div(times(b0,c0),p)
    return proof('normal_projection_measure',[
        'В плоскости x=a>0 каждый луч из начала встречает прямоугольник не более одного раза. На единичной сфере мера радиальной проекции равна a/(a²+y²+z²)^(3/2) dy dz.',
        'Для углового потенциала arctan(yz/(a√(a²+y²+z²))) производная по z равна ay/[(a²+z²)√(a²+y²+z²)].',
        'Его смешанная производная по y даёт исходную проективную плотность. На осях потенциал нуль, поэтому остаётся дальний угол (b,c).',
        'При фиксированных положительных b,c и a→∞ аргумент арктангенса эквивалентен bc/a². Нулевая или пустая сторона имеет нулевую меру.'],
        dict(formula=f'atan({b}*{c}/({a}*sqrt({a}^2+{b}^2+{c}^2))) for positive sides, otherwise 0; leading equivalent {b}*{c}/{a}^2 for fixed positive sides',
             nondegenerate_angle=angle,large_distance_leading=leading),
        corner_factorization=[plus(den,numer),times(plus(p,q0),plus(p,r0))],projection_is_injective=True)


def self_potential_source(task):
    from plane_domains import source_spatial_force
    source_fields(task,{'integrand','region','requested_output'},
                  ('Вычислить потенциал на себя однородного шара по напечатанной нормировке.',))
    if task['integrand']!='rho0^2/(2*norm(x1-x2))' or task['requested_output']!=['exact_self_potential']:
        raise Unsupported('The printed pairing factor and homogeneous density must be retained')
    R=re.fullmatch(r'x1,x2 each in 3-ball radius ([A-Za-z_]\w*)',task['region'])
    if not R or R[1] in {'x','y','z','rho0','pi','e'}|m.FUNCTIONS:
        raise Unsupported('Both actual regions must be the same ball')
    A=R[1]
    child={'kind':'newton_potential_or_force','region':f'xi^2+eta^2+zeta^2<={A}^2',
           'density':'rho0','point':'P(x,y,z)','requested_output':['potential']}
    inner,result=source_spatial_force(child,lambda rule,st,val,**d:(dict(theorem='method.'+rule,argument=st,**d),val))
    val=times(q(16,15),squared(P),squared(s('rho0')),m.power(absolute(s(A)),5))
    return proof('composed_radial_shell_moments',[
        'Ядро 1/|P−Q| локально интегрируемо в трёх измерениях: интеграл по шару радиуса ε равен 2πε². Этот предел равномерен по точке P.',
        'Предлагаем сначала вычислить внутренний слой Q. Угловой метод даёт потенциал шара внутри: 2πρ₀(R²−r²/3).',
        'Внешний интеграл по P использует полную меру 4πr²dr и множитель ρ₀/2 из исходной симметричной пары.',
        'Точные степенные моменты от 0 до радиуса дают 16π²ρ₀²R⁵/15. Совпадающие точки не добавляют отдельного слагаемого.'],
        dict(formula=f'16*pi^2*rho0^2*abs({A})^5/15',value=m.simplify(val)),
        inner_reduction=inner,inner_value=result,full_positive_radial_measure=True,coincidence_tail_bound='2*pi*eps^2')


def real_power_spatial_cases(task):
    """Keep every real sign branch before integrating radial or simplex powers."""
    kind=task['kind'];goal=task.get('requested_output')
    def power_cases():
        return dict(positive_base='any real exponent',negative_base=[
            ['integer or reduced rational p/q with q odd and p even','positive result'],
            ['integer or reduced rational p/q with q odd and p odd','negative result'],
            ['other real exponents','no real value']])
    N=r'([A-Za-z_]\w*)'
    if kind=='solid_centroid':
        source_fields(task,{'region','density','stated_conditions','requested_output'},
                      ('Найти координаты центра масс заданного тела.',))
        raw=task['region']
        hit=re.fullmatch(r'\(x/'+N+r'\)\^n\+\(y/'+N+r'\)\^n\+\(z/'+N+
             r'\)\^n=1,x=0,y=0,z=0;n>0,x>=0,y>=0,z>=0',raw)
        if not hit or goal!=['centroid_coordinates'] or task['density']!='constant' or task['stated_conditions']:
            raise Unsupported('The centroid must refer to the whole displayed orthant and its density')
        a,b,c=hit.groups()
        if len({a,b,c})!=3 or {a,b,c}&({'x','y','z','n','pi','e'}|m.FUNCTIONS):raise Unsupported('Independent scale parameters are required')
        factor='Gamma(2*alpha)*Gamma(1+3*alpha)/(Gamma(alpha)*Gamma(1+4*alpha))'
        return proof('verified_real_power_coordinate_cases',[
            'Каждый исходный знаменатель ненулевой. На внутренности первого октанта знак основания x/a есть знак a. При отрицательных основаниях проверяем действительность показателя до замены.',
            'При положительных значениях всех трёх степеней замена u_i=(x_i/|a_i|)^n переводит область в положительный симплекс. Якобиан содержит произведение u_i^(α−1), где α=1/n>0.',
            'Первый момент по выбранной координате прибавляет α к её показателю Дирихле. Деление на положительную массу даёт общий гамма-множитель.',
            'Если одна из действительных степеней имеет отрицательный знак, после той же замены ограничение становится знаковой полуплоскостью в октанте. При наличии плюсов обе стороны неограничены и имеют бесконечный объём, при всех минусах исходный уровень пуст.',
            'Недействительная степень в одном из внутренних направлений не даёт тела положительной трёхмерной меры.'],
            dict(formula=f'alpha=1/n. If all original powers have positive sign on the interior, centroid={factor}*(abs({a}),abs({b}),abs({c})); otherwise no finite positive-mass body'),
            source_sign_cases=power_cases(),simplex_density='u^(alpha-1)*v^(alpha-1)*w^(alpha-1)',
            positive_mass_division=True,nonzero_scales=[a,b,c],correct_orthant='x,y,z>=0')
    source_fields(task,{'surfaces','stated_conditions','requested_output'},('Найти объём ограниченного тела.',))
    raw=task['surfaces'];hit=re.fullmatch(r'\(x\^2/'+N+r'\^2\+y\^2/'+N+
         r'\^2\)\^n\+z\^\(2\*n\)/'+N+r'\^\(2\*n\)=\(z/'+N+
         r'\)\*\(x\^2/\1\^2\+y\^2/\2\^2\)\^\(n-2\)',raw)
    if not hit or task['stated_conditions']!=['n>1'] or goal!=['exact_volume']:
        raise Unsupported('The full radial power equation and source exponent condition are required')
    a,b,c,h=hit.groups()
    if len({a,b,c,h})!=4 or {a,b,c,h}&({'x','y','z','n','pi','e'}|m.FUNCTIONS):raise Unsupported('Independent scale parameters are required')
    finite=f'pi^2*abs({a}*{b}*{c})*abs({c}/{h})/(3*n*sin(pi/n))'
    return proof('verified_real_power_coordinate_cases',[
        'Фиксируем знак z и отдельно проверяем действительность z^(2n) и c^(2n). Нулевые знаменатели исключены до преобразования.',
        'Нормируем x=|a|r cosφ,y=|b|r sinφ, |z|=|c|r s с s>0. Обратный якобиан по модулю равен |abc|r². Исключённая ось r=0 объёма не добавляет.',
        'Пусть σ — знак отношения двух степеней, ε — знак z/h. Тогда уровень даёт r³(1+σ s^(2n))=ε|c/h|s.',
        'При σ=+1 радиальные лучи заполняются, только если ε=+1. После интеграла по r остаётся ∫₀∞s/(1+s^(2n))ds; оба конца сходятся из n>1. Бета-интеграл равен π/[2n sin(π/n)].',
        'При σ=−1 допустимая сторона абсциссы s=1 определяется ε. На соответствующей стороне радиальный объём имеет полюс первого порядка и бесконечную меру.',
        'Выводим отдельно конечную долю и полный объём, если противоположная знаковая компонента допускает бесконечную меру.'],
        dict(formula=f'For each real sign of z: sigma=sign(z^(2n)/{c}^(2n)), epsilon=sign(z/{h}). If sigma=+1 and epsilon=+1, its finite volume is {finite}. If sigma=-1, an admissible side of s=1 has infinite volume. If sigma=+1 and epsilon=-1, no positive-volume branch. The total is the sum over both real signs.',
             finite_branch_volume=finite),
        source_sign_cases=power_cases(),nonzero_scales=[a,b,c,h],zero_measure_axis='r=0',
        separate_power_denominators=True,infinite_pole='s=1 for sigma negative',radial_beta=['1/n','1-1/n'])

def polynomial_coordinate_derivative(expression,coordinate):
    from cartesian_fields import exact_polynomial_partial
    p,d=m.rational_form(expression)
    if d!={():F(1)} or any(v[0]!='s' for mon in p for v,_ in mon):
        raise Unsupported('A polynomial over the original real coordinates is required')
    return m.poly_expr(exact_polynomial_partial(p,coordinate))


def residual_partial_chart(task):
    """Differentiate a local radial or angular chart on its proven natural domain."""
    from tasks import compile_partial_bundle,source as show
    plan=compile_partial_bundle(task,{'selected_path_limits':{'count':12,'length':4}})
    meta=task.get('source',{})
    if (plan['stated_conditions'] or plan['parameters'] or plan['method_requirement']!='table_and_rules'
            or set(meta)-{'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256',
                          'printed_group_heading','source_partial_order_scope','derivative_sequence_convention',
                          'requested_derivative_sequences','required_equality'}):
        raise Unsupported('The original coordinate chart and its derivative method must be retained')
    V=plan['variables'];X=list(map(s,V));f=m.parse(plan['function'],None,V)
    paths=plan.get('selected_paths',plan['indices'])
    if tuple(map(tuple,meta.get('requested_derivative_sequences',paths)))!=tuple(paths):
        raise Unsupported('Printed derivative orders were changed')
    A=plus(*(squared(x) for x in X))
    table={};argument=[];domain=None;edge=[]
    eq=meta.get('required_equality')
    if eq is not None and (len(V)!=2 or tuple(map(tuple,eq))!=((V[0],V[1]),(V[1],V[0]))
                           or not all(tuple(k) in paths for k in eq)):
        raise Unsupported('Both printed mixed orders are required on the common domain')

    if f[0]=='atan' and f[1][0]=='div':
        numerator,denominator=f[1][1:];a,b=ONE,ZERO
        for x in X:a,b=diff(a,m.mul(b,x)),plus(b,m.mul(a,x))
        if (domain_conditions(numerator) or domain_conditions(denominator) or
                not same_value(numerator,b) or not same_value(denominator,a)):
            raise Unsupported('The angular chart is not the tangent of a sum')
        factors=[plus(ONE,squared(x)) for x in X]
        if not same_value(plus(squared(a),squared(b)),times(*factors)):
            raise Unsupported('The squared norm identity did not verify')
        for i,x in enumerate(X):
            num=diff(m.mul(a,polynomial_coordinate_derivative(b,x)),m.mul(b,polynomial_coordinate_derivative(a,x)))
            if not same_value(num,times(*(d for j,d in enumerate(factors) if i!=j))):
                raise Unsupported('The derivative numerator identity did not verify')
        for path in plan['indices']:
            i=V.index(path[0]); x=X[i];d=factors[i]
            if len(set(path))>1:
                table[path]=ZERO
            else:
                num=ONE
                for k in range(1,len(path)):
                    num=diff(m.mul(d,polynomial_coordinate_derivative(num,x)),times(q(2*k),x,num))
                table[path]=('div',num,('pow',d,len(path))) if len(path)>1 else ('div',num,d)
        domain=show(denominator)+'!=0'
        argument=['Распознаём действительную и мнимую части произведения ∏(1+i x_j).',
                  'Проверяем полиномиально тождество P²+Q²=∏(1+x_j²) и числитель PQ_j−QP_j. Отсюда первая производная равна 1/(1+x_j²).',
                  'Любой дальнейший шаг по другой координате даёт нуль. Повторные шаги по той же координате берём по правилу дроби.',
                  'Исключённые точки исходного знаменателя остаются исключёнными. Складывать главные ветви арктангенса не требуется.']
        family='verified_angular_product_chart'
    elif f[0]=='div' and f[1]==ONE and f[2][0]=='sqrt' and not domain_conditions(f[2][1]) and same_value(f[2][1],A) and max(plan['orders'])<=2:
        table,domain=radial_first_second(V,X,A,-1)
        argument=['Полагаем S=∑x_j². Исходный знаменатель отличен от нуля именно при S>0.',
                  'Применяем цепное правило к S^(-1/2), а затем правило произведения к каждому первому результату.',
                  'Слагаемое с δ_ij получается дифференцированием координаты x_i и равно нулю при разных индексах.']
        family='ordered_radial_derivatives'
    elif f[0]=='ln' and f[1][0]=='div' and f[1][1]==ONE and f[1][2][0]=='sqrt':
        A=f[1][2][1]
        if domain_conditions(A):raise Unsupported('An unrelated domain restriction was found')
        p,d=m.rational_form(A)
        if d!={():F(1)} or not p or any(v[0]!='s' for mon in p for v,_ in mon):
            raise Unsupported('A real polynomial squared radius is required')
        for path in plan['indices']:
            x=s(path[-1]);k=len(path)-1
            dA=polynomial_coordinate_derivative(A,x)
            old=table[path[:-1]][0] if k else ONE
            num=diff(m.mul(A,polynomial_coordinate_derivative(old,x)),times(q(k),old,dA)) if k else times(q(-1,2),dA)
            table[path]=(num,('div',num,('pow',A,k+1) if k else A))
        table={path:result for path,(_,result) in table.items()}
        domain=show(A)+'>0'
        argument=['На полной исходной области S>0 имеем ln(1/√S)=−ln(S)/2.',
                  'Первая производная −S_i/(2S). Каждый следующий шаг заменяет P/S^k на (SP_j−kPS_j)/S^(k+1).',
                  'Числители и производные полинома вычисляются точными таблицами коэффициентов в напечатанном порядке.']
        family='ordered_radial_derivatives'
    elif len(V)==2 and max(plan['orders'])<=2 and f[0]=='asin' and f[1][0]=='div' and f[1][2][0]=='sqrt' and f[1][1] in X and same_value(f[1][2][1],A) and not domain_conditions(f[1][2][1]):
        x=f[1][1];y=X[1-X.index(x)];u=x[1];v=y[1];sgn=m.div(y,absolute(y));a=absolute(y)
        table={(u,):('div',a,A),(v,):('div',m.neg(m.mul(x,sgn)),A),
               (u,u):('div',times(q(-2),x,a),('pow',A,2)),
               (v,v):('div',times(q(2),x,a),('pow',A,2))}
        table[u,v]=table[v,u]=('div',('mul',sgn,diff(squared(x),squared(y))),('pow',A,2))
        domain=v+'!=0'
        edge=[dict(condition=f'{v}=0 and {u}!=0',partials=[
            dict(path=list(path),value=ZERO) if all(i==u for i in path) else dict(path=list(path),existence=False)
            for path in paths])]
        argument=['На двух открытых полуплоскостях угол по главной ветви равен atan(x/|y|). Это следует из прямоугольного треугольника и диапазона арксинуса.',
                  'Дифференцируем на каждой полуплоскости. Производная |y| на ней равна y/|y|.',
                  'На оси y=0 исходная функция равна ±π/2 при x≠0. Сечения по x постоянны; по y односторонние наклоны исходной функции и её производной по x противоположны. Любая производная, начинающаяся с y, уже не существует на этой оси.',
                  'Исходный ноль знаменателя в начале координат исключён.']
        family='verified_principal_inverse_chart'
    elif len(V)==2 and max(plan['orders'])<=2 and f[0]=='acos' and f[1][0]=='sqrt' and f[1][1][0]=='div' and set(f[1][1][1:])==set(X):
        t=f[1][1];x,y=t[1:];u,v=x[1],y[1];B=m.mul(t,diff(ONE,t))
        first=m.div(q(-1),times(q(2),root(B)))
        second=m.div(diff(ONE,times(q(2),t)),times(q(4),m.power(root(B),3)))
        grad={u:m.div(ONE,y),v:m.div(m.neg(t),y)}
        hess={(u,u):ZERO,(u,v):m.div(q(-1),squared(y)),(v,u):m.div(q(-1),squared(y)),
              (v,v):m.div(times(q(2),t),squared(y))}
        for path in plan['indices']:
            a=path[0]
            if len(path)==1:table[path]=m.mul(first,grad[a]);continue
            b=path[1];table[path]=plus(times(second,grad[a],grad[b]),m.mul(first,hess[path]))
        domain=f'{v}!=0 and 0<{u}/{v}<1'
        edge=[dict(condition=f'{v}!=0 and {u}/{v}=0',partials=[
            dict(path=list(path),value=ZERO) if all(i==v for i in path) else dict(path=list(path),existence=False)
            for path in paths]),
              dict(condition=f'{v}!=0 and {u}/{v}=1',partials=[dict(path=list(path),existence=False) for path in paths])]
        argument=['Записываем t=x/y. Исходная область y≠0, 0≤t≤1. Внутри F(t)=arccos√t, F\'=−1/(2√(t(1−t))) и F\'\'=(1−2t)/(4(t(1−t))^(3/2)).',
                  'Для каждого порядка отдельно применяем цепное правило к F\'t_i. Смешанные производные совпадают при упрощении двух формул.',
                  'На концах 0 и 1 наклон переменного отношения имеет корневую особенность. При t=0 сечения по знаменателю постоянны; ни одна смешанная производная не существует на краю.']
        family='verified_principal_inverse_chart'
    else:
        raise Unsupported('No recognized local derivative chart')
    if eq and not same_value(*(table[tuple(k)] for k in eq)):
        raise Unsupported('The two ordered mixed derivatives do not coincide')
    items=[dict(path=list(path),value=table[path]) for path in paths]
    return proof(family,argument,dict(formula='; '.join('D['+','.join(row['path'])+']='+show(row['value']) for row in items),
        partial_derivatives=items,derivative_domain=domain,boundary_derivatives=edge,
        **({'ordered_equality':eq,'equal_on_common_domain':True} if eq else {})),
        natural_domain=plan['natural_domain'],original_method='table_and_rules',coordinate_sequence_verified=True)


def radial_first_second(variables,coordinates,A,exponent_twice):
    from tasks import source as show
    coefficient=q(exponent_twice)
    radius=('sqrt',A)
    grad={(v,):('div',times(coefficient,x),('pow',radius,2-exponent_twice)) for v,x in zip(variables,coordinates)}
    hess={(v,w):('div',plus(times(coefficient,q(exponent_twice-2),x,y),times(coefficient,A) if v==w else ZERO),
                     ('pow',radius,4-exponent_twice))
          for v,x in zip(variables,coordinates) for w,y in zip(variables,coordinates)}
    return {**grad,**hess},show(A)+'>0'


def radial_total_differential(task):
    from tasks import source as show
    source_fields(task,{'schema','function','variables','requested_output'},(),
                  ('printed_heading',))
    V=task['variables']
    if (not 2<=len(V)<=4 or len(set(V))!=len(V) or
            task['requested_output']!=['first_total_differential','second_total_differential']):
        raise Unsupported('Both total differentials and independent coordinates are required')
    if any(not isinstance(v,str) or ('d'+v) in V for v in V):
        raise Unsupported('Differential and coordinate symbols must be distinct')
    f=m.parse(task['function'],None,V)
    if f[0]!='sqrt' or domain_conditions(f[1]):raise Unsupported('No pure Euclidean radius')
    A=f[1];X=[s(v) for v in V if same_value(m.substitute(A,{s(w):ZERO for w in V if w!=v}),squared(s(v)))]
    if not X or not same_value(A,plus(*(squared(x) for x in X))):
        raise Unsupported('The complete axis set of the Euclidean radius is required')
    radius=('sqrt',A)
    increments=[s('d'+x[1]) for x in X]
    first=('div',plus(*(m.mul(x,dx) for x,dx in zip(X,increments))),radius)
    minors=[('pow',diff(m.mul(x,dy),m.mul(y,dx)),2) for i,(x,dx) in enumerate(zip(X,increments))
            for y,dy in zip(X[i+1:],increments[i+1:])]
    numerator=reduce(lambda a,b:('add',a,b),minors) if minors else ZERO
    second=('div',numerator,('pow',radius,3))
    domain=show(A)+'>0'
    return proof('ordered_radial_derivatives',[
        'На S>0 цепное правило даёт градиент S^(−1/2)(x_j) и матрицу вторых частных производных.',
        'Умножаем коэффициенты на дифференциалы независимых координат. Тождество Лагранжа записывает числитель второго дифференциала как сумму (x_i dx_j−x_j dx_i)² по i<j.',
        'В каждой точке S=0 сечение по активной координате равно |t|. Значит, уже первого полного дифференциала там нет.'],
        dict(formula='df='+show(first)+'; d2f='+show(second),first_differential=first,second_differential=second,
             derivative_domain=domain,no_differentials_at_squared_radius_zero=True))


RESIDUAL_GEOMETRY = {
    'partial_derivatives': residual_partial_chart,
    'first_and_second_total_differentials': radial_total_differential,
    'triple_integration_orders': projection_orders_source,
    'spherical_change_bounds': spherical_projection_source,
    'rectangle_solid_angle': solid_angle_source,
    'gravitational_self_potential': self_potential_source,
    'bounded_solid_volume': real_power_spatial_cases,
    'solid_centroid': real_power_spatial_cases,
}


def selected_residual_geometry(task):
    project=RESIDUAL_GEOMETRY.get(task.get('kind'))
    if project is not None:
        try:
            return project(task)
        except (Unsupported,KeyError,TypeError,ValueError,ZeroDivisionError,IndexError,AttributeError):
            pass
    return None
