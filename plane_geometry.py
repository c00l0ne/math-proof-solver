"""Planar tangent angles and curvature centers from verified coordinate jets."""
import re

import expressions as m
import intervals as line
import polynomial as poly
from cartesian_fields import vector_source
from model import ZERO, Unsupported, freeze, q
from tasks import domain_conditions, entailed_domain_guards, guard_source, known_guard, source
from verify import same_value

KINDS = {
    'angle_between_plane_tangents', 'curve_intersection_angle',
    'parametric_center_of_curvature', 'plane_curve_evolute', 'evolute_congruence',
    'rectilinear_motion_from_position', 'uniform_circular_motion_projection',
    'motion_under_constant_gravity', 'parametric_motion_kinematics',
}
EVOLUTE = 'Составить уравнение эволюты заданной кривой.'
CONGRUENCE = 'Доказать, что эволюта циклоиды есть циклоида, отличающаяся только положением.'
ANGLE_HEADINGS = (
    'Под каким углом кривая y=ln x пересекает Ox?',
    'Найти углы пересечения двух кривых.',
    'Найти углы пересечения синусоиды и косинусоиды.',
)


def names(text, *excluded):
    return sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi',*excluded})


def read_text(text):
    return text.replace('²','^2').replace('³','^3').replace('⁴','^4')


def reduce(e):
    numerator, denominator = m.rational_form(e)
    n = m.poly_expr(m.trig_reduce(numerator,complete=True))
    d = m.poly_expr(m.trig_reduce(denominator,complete=True))
    return m.div(n,d)


def determinant(a,b):
    return reduce(m.add(m.mul(a[0],b[1]),m.neg(m.mul(a[1],b[0]))))


def change(e,variable,value):
    return m.substitute(e,{('v',variable): value})


def compact_radical_ratio(value,variable,parameters,conditions):
    """Propose shorter quotients of terms and keep only an exact, domain-safe identity."""
    from operations import expression_positions
    numerator,denominator=m.rational_form(value)
    if min(len(numerator),len(denominator))<2 or not any(
            a[0]=='sqrt' for polynomial in (numerator,denominator) for term in polynomial for a,_ in term):
        return value
    var=('s',variable)
    ctx=m.context(dict(variable='__curve_scope',parameters=[variable,*parameters],parameter_conditions=conditions))
    candidates={m.div(m.poly_expr({n:nc}),m.poly_expr({d:dc}))
                for n,nc in numerator.items() for d,dc in denominator.items()}
    for e in sorted(candidates,key=lambda t:(sum(1 for _ in expression_positions(t)),t)):
        if (all(known_guard((rel,change(raw,variable,var)),ctx) for rel,raw in domain_conditions(e))
                and same_value(e,value)):
            return e
    return value


def checked_jet(expressions, variable, parameters, conditions, request, order):
    """Build first and second derivatives from the same original smooth chart."""
    raw_guards = tuple(dict.fromkeys(g for e in expressions for g in domain_conditions(e)))
    smooth_guards = tuple(dict.fromkeys(g for e in expressions for g in domain_conditions(e,True)))
    scope = list(dict.fromkeys([*conditions,*(guard_source(g) for g in entailed_domain_guards(smooth_guards))]))
    rows = [tuple(expressions)]
    seen = {}
    for j in range(1,order+1):
        values = []
        for i,e in enumerate(rows[-1]):
            if e not in seen:
                child = request(f'derivative {j} of coordinate {i+1}',dict(
                    kind='differentiate',function=source(e),variable=variable,parameters=list(parameters),
                    stated_conditions=scope,method_requirement='table_and_rules'))
                actual = child['compilation']
                retained = actual['display_sufficient_domain']
                if j>1 and retained:
                    raise Unsupported('A differentiated coordinate introduced an unproved chart restriction')
                value = freeze(child['value'])
                seen[e] = compact_radical_ratio(value,variable,parameters,scope) if j<order else value
            values.append(seen[e])
        rows.append(tuple(values))
    return rows,dict(natural_guards=raw_guards,smooth_guards=smooth_guards,derivative_conditions=scope)


def curvature(jet,guards,variable,parameters,conditions,at=None):
    p,v,a = jet
    if at is not None:
        ctx = m.context(dict(parameters=list(parameters),parameter_conditions=conditions))
        actual = [change(e,variable,at) for e in p]
        if not all(m.constant_defined(t,ctx) for t in (at,*actual)):
            raise Unsupported('The specified parameter does not give a verified source curve point')
        if not all(known_guard((rel,change(g,variable,at)),ctx) for rel,g in guards['smooth_guards']):
            raise Unsupported('The chart is not certified twice differentiable at the specified point')
        p,v,a = [tuple(reduce(change(e,variable,at)) for e in values) for values in jet]
    v2 = reduce(m.dot(v,v))
    cross = determinant(v,a)
    calculation = dict(point=p,velocity=v,acceleration=a,speed_squared=v2,determinant=cross)
    result = dict(parameter=variable,source_conditions=conditions,original_guards=guards['natural_guards'],
        smooth_guards=guards['smooth_guards'],regularity=(('positive',v2),('nonzero',cross)),
        excluded_cases=dict(zero_speed='the chart formula does not decide the geometric curvature',
                            nonzero_speed_and_zero_determinant='curvature is zero and has no finite center'))
    if at is not None and v2==ZERO:
        raise Unsupported('A stationary chart requires a separate geometric limit or reparametrization')
    if v2==ZERO or cross==ZERO:
        if at is None or all(m.constant_defined(t,ctx) for t in v):
            classification='stationary' if v2==ZERO else ('zero_curvature' if at is not None else 'zero_curvature_at_nonstationary_points')
            return calculation,dict(result,center=None,classification=classification)
        raise Unsupported('The regularity of the specified point was not decided')
    if at is not None and not (known_guard(('positive',v2),ctx) and known_guard(('nonzero',cross),ctx)):
        raise Unsupported('Speed or curvature at the specified point may vanish')
    signed_scale = reduce(m.div(v2,cross))
    offset = (m.mul(signed_scale,m.neg(v[1])),m.mul(signed_scale,v[0]))
    if not same_value(reduce(m.dot(offset,a)),v2) or not same_value(reduce(m.dot(offset,v)),ZERO):
        raise Unsupported('The proposed center failed the two second-order contact equations')
    center = tuple(reduce(m.add(x,y)) for x,y in zip(p,offset))
    return dict(calculation,normal_offset=offset),dict(result,center=center)


def equation_chart(curve):
    """Build parametrizations with reversible coverage of their complete real loci."""
    curve = read_text(curve)
    x,y = ('v','x'),('v','y')
    t = ('v','t')
    if curve.startswith('r='):
        parameters = names(curve[2:],'phi')
        r = m.parse(curve[2:],'phi',parameters)
        t = ('v','phi')
        return (m.mul(r,('cos',t)),m.mul(r,('sin',t))), 'phi',parameters,[],dict(
            original_radius=r,coverage='the Cartesian components implement the original polar equations')
    explicit = re.fullmatch(r'([xy])=(.*)',curve)
    if explicit and not re.search(r'\b'+explicit[1]+r'\b',explicit[2]):
        var = 'y' if explicit[1]=='x' else 'x'
        if re.search(r'\b'+var+r'\b',explicit[2]):
            parameters = names(explicit[2],var)
            p = m.parse(explicit[2],var,parameters)
            chart = (p,y) if var=='y' else (x,p)
            return chart,var,parameters,[],dict(coverage='direct graph coordinate with its exact natural domain')
    token = r'([A-Za-z_]\w*|\d+)'
    parabola = re.fullmatch(r'([xy])\^2=(.+)\*([xy])',curve)
    if parabola and parabola[1]!=parabola[3] and not (set(names(parabola[2]))&{'x','y','t'}):
        params = names(parabola[2])
        coef = m.parse(parabola[2],None,params)
        coord = ('div',m.power(t,2),coef)
        chart = (coord,t) if parabola[1]=='y' else (t,coord)
        return chart,'t',params,[source(coef)+'!=0'],dict(
            coverage='the squared coordinate serves as the parameter and the other coordinate is uniquely determined',
            degenerate='a zero coefficient gives a straight line with zero curvature wherever it is a regular curve')
    ellipse = re.fullmatch(r'x\^2/'+token+r'\^2\+y\^2/'+token+r'\^2=1',curve)
    if ellipse and not set(ellipse.groups())&{'x','y','t'}:
        params = names(ellipse[1]+' '+ellipse[2])
        a,b = (m.parse(e,None,params) for e in ellipse.groups())
        return (m.mul(a,('cos',t)),m.mul(b,('sin',t))),'t',params,[source(z)+'!=0' for z in (a,b)],dict(
            coverage='division by the two nonzero axis scales gives every point of the unit circle',
            degenerate='a zero axis scale makes the source equation undefined')
    asteroid = re.fullmatch(r'cbrt\(x\)\^2\+cbrt\(y\)\^2=cbrt\('+token+r'\)\^2',curve)
    if asteroid and asteroid[1] not in {'x','y','t'}:
        params = names(asteroid[1])
        a = m.parse(asteroid[1],None,params)
        return (m.mul(a,m.power(('cos',t),3)),m.mul(a,m.power(('sin',t),3))),'t',params,[source(a)+'!=0'],dict(
            coverage='take the real cube root of both coordinates divided by the nonzero scale to get the unit circle',
            degenerate='a zero scale collapses the locus to one point')
    raise Unsupported('No chart with complete real coverage has been established')


def graph_equation(text):
    """Read y=f(x) or x=g(y) without identifying the two local directions."""
    z = read_text(text)
    if '=' not in z:
        z = 'y='+z
    v,f = z.split('=',1)
    if v not in 'xy' or len(v)!=1:
        raise Unsupported('Expected an explicit plane graph or its reversed-coordinate representation')
    var = 'x' if v=='y' else 'y'
    return var,m.parse(f,var)


def angle(a,b):
    cross = determinant(a,b)
    cosine_numerator = reduce(m.dot(a,b))
    ctx = m.context({})
    if not all(m.nonzero(reduce(m.dot(v,v)),ctx) for v in (a,b)):
        raise Unsupported('The angle needs two nonzero tangent directions')
    if same_value(cosine_numerator,ZERO):
        return dict(angle=m.div(m.PI,q(2)),determinant=cross,dot=cosine_numerator)
    if same_value(cross,ZERO):
        return dict(angle=ZERO,determinant=cross,dot=cosine_numerator)
    if not m.nonzero(cosine_numerator,ctx):
        raise Unsupported('The tangent denominator is not known to be nonzero')
    ratio = reduce(('abs',m.div(cross,cosine_numerator)))
    return dict(angle=('atan',ratio),tangent_of_acute_angle=ratio,determinant=cross,dot=cosine_numerator)


def local_angle(curves,point,request):
    if len(curves)!=2:
        raise Unsupported('The angle requires exactly two original curves')
    directions = []
    for i,text in enumerate(curves):
        lhs,rhs = read_text(text).split('=')
        field = ('add',m.parse(lhs,None,['x','y']),('mul',q(-1),m.parse(rhs,None,['x','y'])))
        child = request(f'normal of level {i+1} at the common point',dict(kind='scalar_field_geometry',
            function=source(field),variables=['x','y'],points={'P':list(map(source,point))},
            requests=[dict(op='gradient',at='P')],level='0'))
        row = child['compilation']['points']['P']
        if not same_value(freeze(row['field_value']),ZERO):
            raise Unsupported('The specified point is not on both original levels')
        dx,dy = freeze(row['gradient'])
        directions.append((dy,m.neg(dx)))
    return dict(point=point,directions=directions,**angle(*directions))


def discover_intersections(curves):
    """Eliminate a coordinate and isolate every real common point."""
    (u,f),(v,g) = [graph_equation(s) for s in curves]
    identity = ('v',u)
    if u==v:
        diff = ('add',f,('mul',q(-1),g))
    else:
        diff = ('add',change(g,v,f),('mul',q(-1),identity))
    ctx = m.context({})
    if u==v and f[0]=='ln' and f[1]==identity and not m.variable_in(g) and m.constant_defined(g,ctx):
        roots = [m.simplify(('exp',g))]
        witness = dict(monotone_inverse='ln and exp are inverse on x>0')
    else:
        from graphs import rational_roots
        try:
            p,_ = poly.rf(diff,u)
        except (poly.NotRational,poly.Undefined,line.Unsupported) as exc:
            raise Unsupported('The complete set of real intersections has not been isolated') from exc
        if not any(p):
            raise Unsupported('Coincident loci need a separate description')
        try:
            roots = [m.add(q(r.a),m.mul(q(r.b),('sqrt',q(r.d)))) if r.b else q(r.a)
                     for r in rational_roots(p)]
        except (poly.NotRational,poly.Undefined,line.Unsupported) as exc:
            raise Unsupported('The real root isolation is incomplete') from exc
        witness = dict(elimination_equation=diff)
    points = []
    for coord in dict.fromkeys(roots):
        image = change(f,u,coord)
        other = change(g,v,coord if u==v else image)
        if not all(m.constant_defined(t,ctx) for t in (image,other)):
            raise Unsupported('A candidate lies outside or at an undecided original domain point')
        if not same_value(image if u==v else coord,other):
            raise Unsupported('An isolated root misses an original equation')
        point = (coord,reduce(image)) if u=='x' else (reduce(image),coord)
        points.append(point)
    return points,witness


def angle_goal(task,request):
    kind = task['kind']
    if kind=='angle_between_plane_tangents':
        vector_source(task,{'curves','point','requested_output'},())
        if task['requested_output']!=['smaller_angle'] or len(task['point'])!=2:
            raise Unsupported('Two original coordinates and the smaller angle of the tangent lines are required')
        curves=task['curves'];point=tuple(m.parse(z,None) for z in task['point'])
        answer = [local_angle(curves,point,request)]
        witness = {}
    else:
        vector_source(task,{'curves','line','curve'},ANGLE_HEADINGS)
        if set(task)&{'curves','line','curve'}=={'curves'}:
            curves=task['curves']
        elif set(task)&{'curves','line','curve'}=={'line','curve'}:
            curves=[task['curve'],task['line']]
        else:
            raise Unsupported('The two competing curve descriptions do not agree')
        if len(curves)!=2:
            raise Unsupported('The goal requires exactly two curves')
        curves = [s if '=' in s else 'y='+s for s in curves]
        (u,f),(v,g) = [graph_equation(s) for s in curves]
        heading=task.get('source',{}).get('literal_requirement')
        sine_cosine=(u==v=='x' and {f[0],g[0]}=={'sin','cos'} and f[1]==g[1]==('v','x'))
        if (heading==ANGLE_HEADINGS[0] and (u!=v or u!='x' or {f,g}!={('ln',('v','x')),ZERO})
                or heading==ANGLE_HEADINGS[2] and not sine_cosine):
            raise Unsupported('The typed curves disagree with the literal statement')
        if sine_cosine:
            representative=local_angle(curves,(m.div(m.PI,q(4)),m.div(('sqrt',q(2)),q(2))),request)
            answer=[dict(representative,point_family=('pi/4+pi*k','(-1)^k*sqrt(2)/2'),index='k any integer')]
            witness=dict(phase='sin x−cos x=sqrt(2)sin(x−pi/4)',
                         invariance='the two tangent slopes change signs together under x→x+pi')
        else:
            points,witness = discover_intersections(curves)
            answer = [local_angle(curves,point,request) for point in points]
    return (dict(theorem='method.plane_tangent_directions',source_curves=curves,**witness,
        argument='В каждой общей точке градиент исходного неявного уровня задаёт нормаль. Ненулевые касательные сравниваем по их определителю и скалярному произведению.'),
        dict(intersections=answer))


def shifted_modes(e,variable,amount):
    from integrals import affine
    x=('v',variable)
    def recurse(t):
        if t==x:
            return m.add(x,amount)
        if t[0] in ('sin','cos'):
            frequency,_ = affine(t[1],variable)
            turns=m.pi_multiple(m.mul(frequency,amount))
            if turns is None or (2*turns).denominator!=1:
                raise Unsupported('The candidate phase does not give an exact quarter-turn')
            choices = (('sin',1),('cos',1),('sin',-1),('cos',-1)) if t[0]=='sin' else (
                ('cos',1),('sin',-1),('cos',-1),('sin',1))
            function,sign=choices[int(2*turns)%4]
            return m.mul(q(sign),(function,t[1]))
        return (t[0],*(recurse(z) if isinstance(z,tuple) else z for z in t[1:]))
    return recurse(e)


def nonzero_drift(e,variable,ctx):
    """An affine drift plus bounded real trigonometric terms has a proper trace."""
    x = ('v',variable)
    numerator,denominator = m.rational_form(e)
    coeff = {}
    if any(m.variable_in(a,variable) for mon in denominator for a,_ in mon):
        return False
    for mon,value in numerator.items():
        if (x,1) in mon:
            rest=tuple((a,k) for a,k in mon if a!=x)
            if any(m.variable_in(a,variable) for a,_ in rest):
                return False
            coeff[rest]=value
        elif any(m.variable_in(a,variable) and a[0] not in ('sin','cos') for a,_ in mon):
            return False
    return m.nonzero(m.div(m.poly_expr(coeff),m.poly_expr(denominator)),ctx)


def discover_phase_translation(coordinates,result,variable,params):
    from operations import expression_positions
    center=result['center']
    analytic={'q','v','s','pi','add','mul','sin','cos','exp','sinh','cosh','pow'}
    if (center is None or result['smooth_guards'] or result['source_conditions'] or any(
            e[0] not in analytic for u in coordinates for _,e in expression_positions(u))):
        raise Unsupported('A phase congruence requires a real-analytic chart on the full parameter line')
    # A collapsed coordinate scale is an explicit degeneracy of this chart, never a curvature center.
    v2,det=(e for _,e in result['regularity'])
    for scale in [None,*params]:
        conditions=[] if scale is None else [scale+'!=0']
        ctx=m.context(dict(parameters=params,parameter_conditions=conditions))
        if scale is not None:
            replacement={('s',scale):ZERO}
            if any(m.variable_in(reduce(m.substitute(z,replacement)),variable) for z in coordinates):
                continue
        regular_witness=next((s for s in (ZERO,m.div(m.PI,q(2)),m.PI)
            if known_guard(('positive',reduce(change(v2,variable,s))),ctx)
            and known_guard(('nonzero',reduce(change(det,variable,s))),ctx)),None)
        if regular_witness is None or not any(nonzero_drift(e,variable,ctx) for e in coordinates):
            continue
        for phase in (ZERO,m.PI,m.neg(m.PI)):
            try:
                translation=tuple(reduce(m.add(p,m.neg(shifted_modes(r,variable,phase)))) for p,r in zip(center,coordinates))
            except Unsupported:
                continue
            if all(m.constant_defined(z,ctx) for z in translation):
                return dict(parameter_shift=phase,translation=translation,proved_on_regular_chart=True,
                    closure_equals_translated_full_trace=True,regularity_witness=regular_witness,
                    conditions=conditions,collapsed_parameter=scale,
                    argument='Ненулевые аналитические функции скорости и определителя имеют изолированные нули. Регулярные параметры плотны, а ненулевой дрейф координаты делает полный образ замкнутым. Перенос даёт равенство замыкания эволюты со всей кривой.')
    raise Unsupported('No exact phase translation preserving the complete image has been proved')


def evolute_goal(task,request):
    kind = task['kind']
    if kind=='parametric_center_of_curvature':
        vector_source(task,{'coordinates','parameter','parameters','stated_conditions','at','requested_output'},())
        if task['requested_output']!=['center_of_curvature']:
            raise Unsupported('Unknown curvature result requested')
        var,params = task['parameter'],task.get('parameters',[])
        conditions = task.get('stated_conditions',[])
        coordinates = tuple(m.parse(z,var,params) for z in task['coordinates'])
        at = m.parse(task['at'],None,params) if 'at' in task else None
        binding = dict(coverage='original parameterized chart')
    elif kind=='plane_curve_evolute':
        vector_source(task,{'curve'},[EVOLUTE])
        coordinates,var,params,conditions,binding = equation_chart(task['curve'])
        at = None
    elif kind=='evolute_congruence':
        vector_source(task,{'curve'},[CONGRUENCE])
        var='t'
        params=names(' '.join(task['curve']),var)
        coordinates=tuple(m.parse(z,var,params) for z in task['curve'])
        conditions = []
        at = None
        binding = dict(coverage='original parameterized curve')
    else:
        raise Unsupported('Unknown planar curvature conclusion')
    if len(coordinates)!=2:
        raise Unsupported('Exactly two coordinate functions are required')
    jet,guards = checked_jet(coordinates,var,params,conditions,request,2)
    work,result = curvature(jet,guards,var,params,conditions,at)
    if kind=='evolute_congruence':
        result['congruence'] = discover_phase_translation(coordinates,result,var,params)
    return dict(theorem='method.planar_curvature_center',coordinate_jet=work,chart=binding,derivative_scope=guards,
        argument='Радиус-вектор от точки до центра ортогонален скорости. Скалярное произведение того же вектора на ускорение равно квадрату скорости по условию касания второго порядка. Ненулевой определитель даёт единственный центр.'),dict(result,chart=binding)


def plane_geometry(task,library,request):
    if not library.data.get('plane_tangent_and_curvature'):
        raise Unsupported('The planar tangent and curvature rules are not enabled')
    if task['kind'] in ('angle_between_plane_tangents','curve_intersection_angle'):
        return angle_goal(task,request)
    if task['kind'] in ('rectilinear_motion_from_position','uniform_circular_motion_projection',
                        'motion_under_constant_gravity','parametric_motion_kinematics'):
        return motion_goal(task,request)
    return evolute_goal(task,request)


def harmonic_trace(coordinates,var,parameters):
    """Invert the linear map of one sine/cosine phase to its full planar trace."""
    from integrals import affine
    data=[m.rational_form(z) for z in coordinates]
    phases = {a[1] for n,d in data for mon in n for a,k in mon if a[0] in ('sin','cos') and m.variable_in(a,var)}
    if len(phases)!=1:
        raise Unsupported('A single common affine phase has not been identified')
    phase,=phases
    speed,initial=affine(phase,var)
    if m.variable_in(speed) or m.variable_in(initial):
        raise Unsupported('The phase has no constant rate and offset')
    sin,cos=('sin',phase),('cos',phase)
    origin=[];columns=[[],[]]
    for numerator,denominator in data:
        if (set(denominator)!={()} or any(len(mon)>1 or mon and mon[0] not in ((sin,1),(cos,1)) for mon in numerator)):
            raise Unsupported('The chart is not an affine image of a harmonic unit circle')
        for z,row in zip(((),((sin,1),),((cos,1),)),(origin,*columns)):
            row.append(q(numerator.get(z,0)/denominator[()]))
    S,C=map(tuple,columns);det=determinant(S,C)
    if not m.nonzero(det,m.context({})):
        raise Unsupported('The harmonic motion has a singular linear map')
    xx,yy=(('s','X'),('s','Y'))
    displacement=tuple(m.add(z,m.neg(a)) for z,a in zip((xx,yy),origin))
    u=m.div(determinant(displacement,C),det)
    v=m.div(determinant(S,displacement),det)
    norm=reduce(m.add(m.power(u,2),m.power(v,2)))
    if not same_value(reduce(m.substitute(norm,{xx:coordinates[0],yy:coordinates[1]})),m.ONE):
        raise Unsupported('The normalized harmonic trace failed the unit-circle equation')
    zero_rate=tuple(reduce(change(e,var,ZERO)) for e in coordinates)
    return dict(equation=(norm,m.ONE),phase=phase,phase_rate=speed,
                coefficient_matrix=(S,C),center=origin,nonzero_rate_covers_entire_trace=True,
                zero_rate_trace=zero_rate)


def motion_goal(task,request):
    kind=task['kind']
    result={};scope=[];argument='Скорость и ускорение получаем последовательным дифференцированием координат по времени.'
    if kind=='rectilinear_motion_from_position':
        vector_source(task,{'position','time','evaluate_at','requested_output'},(),('printed_goal','requested_operator'))
        var=task['time'];params=names(task['position'],var)
        t=m.parse(task['evaluate_at'],None,params)
        origin=task.get('source',{})
        if (task['requested_output']!=['velocity','acceleration','both_at_specified_time']
                or origin.get('printed_goal') not in (None,'Find velocity, acceleration and both at t=2.')
                or origin.get('printed_goal') and (origin.get('requested_operator')!='kinematics' or t!=q(2))):
            raise Unsupported('The printed motion outputs or specified time differ')
        coords=(m.parse(task['position'],var,params),)
    elif kind=='uniform_circular_motion_projection':
        vector_source(task,{'curve','initial_point','uniform_motion','period','projection','requested_output'},(
            'Determine velocity and acceleration of the projection on Ox.',))
        circle=re.fullmatch(r'x\^2\+y\^2=(\w+)\^2',task['curve'])
        if (not circle or task['initial_point']!=[circle[1],'0'] or task['uniform_motion'] is not True
                or task['projection'] not in ('x','y') or task['requested_output']!=['velocity','acceleration']
                or task.get('source',{}).get('literal_requirement') and task['projection']!='x'):
            raise Unsupported('A full turn, its source initial point and requested projection must be known')
        var='t';t=None;params=names(circle[1]+' '+task['period'],var)
        radius,period=(m.parse(e,None,params) for e in (circle[1],task['period']))
        omega=m.div(m.mul(q(2),m.PI),period)
        scope=[source(radius)+'>0',source(period)+'>0']
        if task['projection']=='y':
            raise Unsupported('The rotation sense is needed for the vertical projection')
        coords=(m.mul(radius,('cos',m.mul(omega,('v',var)))),)
        result.update(angular_speed=omega,projection=task['projection'])
        argument='За период фаза меняется на полный оборот. При начальной точке на горизонтальной оси проекция задаётся косинусом для обоих направлений вращения. '+argument
    elif kind=='parametric_motion_kinematics':
        vector_source(task,{'coordinates','variable','parameters','requested_output'},(
            'Determine trajectory, velocity and acceleration when omega is constant.',))
        var=task['variable'];t=None;params=task['parameters']
        if task['requested_output']!=['trajectory','velocity','acceleration'] or len(task['coordinates'])!=2:
            raise Unsupported('A complete planar trajectory and its velocity and acceleration are required')
        coords=tuple(m.parse(z,var,params) for z in task['coordinates'])
        result['trajectory']=harmonic_trace(coords,var,params)
        argument='Планарные координаты выражаются линейно через синус и косинус одной фазы. Обратная матрица переносит уравнение единичной окружности на всю траекторию. При нулевой частоте остаётся исходная точка. '+argument
    else:
        vector_source(task,{'initial_speed','launch_angle','plane','gravity','no_drag','requested_output'},(
            'For a point thrown with speed v0 at angle alpha, neglect drag. Find motion, velocity, acceleration, trajectory, maximum rise and range.',))
        if (task['plane']!='vertical Oxy' or task['gravity'] is not True or task['no_drag'] is not True
                or task['requested_output']!=['motion','velocity','acceleration','trajectory','maximum rise','range']):
            raise Unsupported('The constant-gravity model or the complete source requests differ')
        var='t';t=None;params=names(task['initial_speed']+' '+task['launch_angle']+' g',var)
        speed,alpha=(m.parse(task[k],None,params) for k in ('initial_speed','launch_angle'))
        g=('s','g');time=('v',var);u,w=(m.mul(speed,(z,alpha)) for z in ('cos','sin'))
        scope=[source(speed)+'>0','g>0']
        coords=(m.mul(u,time),m.add(m.mul(w,time),m.neg(m.mul(m.div(g,q(2)),m.power(time,2)))))
        h=m.div(m.power(w,2),m.mul(q(2),g));flight=m.div(m.mul(q(2),w),g)
        X=('s','X')
        result.update(motion=coords,trajectory=dict(
            horizontal_velocity_nonzero=m.add(m.mul(w,m.div(X,u)),m.neg(m.mul(m.div(g,q(2)),m.power(m.div(X,u),2)))),
            horizontal_velocity_zero='X=0',time_range='from release until return to launch level'),
            upward_launch=dict(when=('positive',w),time_of_apex=m.div(w,g),maximum_rise=h,flight_time=flight,
                range=m.mul(('abs',u),flight)),nonupward_launch=dict(when=('nonpositive',w),maximum_rise=ZERO,range=ZERO))
        argument='Закон движения следует из постоянного вертикального ускорения и начальной скорости при отсутствии сопротивления. Вершина определяется нулём вертикальной скорости, момент возврата — вторым нулём вертикальной координаты. '+argument
    jet,guards=checked_jet(coords,var,params,scope,request,2)
    _,v,a=jet
    result.update(velocity=v[0] if len(v)==1 else v,acceleration=a[0] if len(a)==1 else a,
        source_domain=guards['natural_guards'],smooth_domain=guards['smooth_guards'],conditions=scope)
    if len(v)==2:
        result.update(speed=('sqrt',reduce(m.dot(v,v))),acceleration_magnitude=('sqrt',reduce(m.dot(a,a))))
    if t is not None:
        ctx=m.context(dict(parameters=params))
        source_at=[change(e,var,t) for e in coords]
        if not all(m.constant_defined(e,ctx) for e in (t,*source_at)) or not all(
                known_guard((r,change(e,var,t)),ctx) for r,e in guards['smooth_guards']):
            raise Unsupported('The specified time is outside the smooth source chart')
        result['at_specified_time']=dict(time=t,velocity=reduce(change(v[0],var,t)),acceleration=reduce(change(a[0],var,t)))
    return dict(theorem='method.kinematic_coordinate_jet',coordinates=coords,velocity=v,acceleration=a,
        derivative_scope=guards,argument=argument),result

def geometric_profile(theorem,argument,**conclusion):
    return dict(method='geometric_profile_proof',theorem=theorem,argument=argument),conclusion


def level_profile_geometry(text,conditions,output):
    """Use normals of homogeneous or radial levels and compare them on a checked source domain."""
    if conditions:raise Unsupported('The geometry rule needs the actual stated domain')
    s=lambda k:('s',k);x,y,z=map(s,('x','y','z'));xyz=(x,y,z);coords=('x','y','z')
    ident=r'[A-Za-z_]\w*'
    if output=='prove constant tetrahedron volume with coordinate planes':
        match=re.fullmatch(r'x\*y\*z=('+ident+r')\^(\d+),\1>0',text)
        if not match or match[1] in coords or int(match[2])<1:raise Unsupported('Need a fixed positive coordinate product')
        level=m.power(s(match[1]),int(match[2]))
        return geometric_profile('method.axis_intercepts_of_product_level',
             'Дифференцируем произведение трёх координат. Так как оно положительно, все координаты ненулевые. Деление уравнения касательной плоскости на исходное произведение даёт перехваты 3x, 3y и 3z. Объём равен модулю их произведения, делённому на 6.',
             tangent_intercepts=[m.mul(q(3),a) for a in xyz],constant_volume=m.mul(q(9,2),level))
    if output=='prove sum of tangent plane axis intercepts constant':
        match=re.fullmatch(r'sqrt\(x\)\+sqrt\(y\)\+sqrt\(z\)=sqrt\(('+ident+r')\),\1>0',text)
        if not match or match[1] in coords:raise Unsupported('Need the actual nonnegative root sum and positive level')
        a=s(match[1]);scale=('sqrt',a)
        return geometric_profile('method.axis_intercepts_of_root_sum',
              'В положительной части поверхности градиент пропорционален обратным корням координат. Касательная плоскость отсекает отрезки √a·√x, √a·√y и √a·√z. Их сумма равна a. Когда координата обращается в нуль, предельная плоскость может содержать целую ось, поэтому конечные перехваты как отдельные точки определены в положительной части.',
              tangent_intercepts=[m.mul(scale,('sqrt',v)) for v in xyz],constant_sum=a,regular_intercept_domain='x,y,z>0',
              boundary_intercepts='finite limiting lengths; boundary planes can contain a coordinate axis')
    if output=='prove all tangent planes pass through cone vertex' and re.fullmatch(r'z=x\*'+ident+r'\(y/x\)',text):
        return geometric_profile('method.tangent_plane_of_homogeneous_graph',
             'При положительном масштабировании обеих исходных координат значение графика умножается на тот же множитель. Дифференцируем это равенство в масштабе 1, получаем x z_x+y z_y=z. Поэтому начало координат удовлетворяет уравнению касательной плоскости в каждой её регулярной точке.',
             proves_vertex_incidence=True,vertex=[ZERO,ZERO,ZERO],source_domain='x!=0 where the arbitrary profile is differentiable')
    if output=='prove every normal meets axis of rotation' and re.fullmatch(r'z='+ident+r'\(sqrt\(x\^2\+y\^2\)\), f_prime!=0',text):
        return geometric_profile('method.radial_normal_intersection',
             'Горизонтальная часть нормали направлена по радиусу и имеет длину |f′(r)|. Продолжаем нормаль на параметр r/f′(r), после чего обе горизонтальные координаты равны нулю. В гладкой точке на оси сама нормаль вертикальна.',
             regular_axis_intersection='(0,0,f(r)+r/f_prime(r)) for r>0',axis='Oz')
    match=re.fullmatch(r'z=(.+) on unit square; partition into finitely many pieces of diameter<=delta',text)
    req=re.fullmatch(r'bound delta so normals within a piece differ by less than (\d+) degree',output)
    if match and req:
        from fractions import Fraction
        e=m.parse(match[1],None,coords[:2]);p,d=m.rational_form(e)
        if domain_conditions(e) or d!={():Fraction(1)} or any(k not in ((),((x,2),),((y,2),)) for k in p):
            raise Unsupported('The upper normal variation needs a controlled Hessian over the entire convex square')
        L=2*max(abs(p.get(((a,2),),0)) for a in (x,y));angle=q(Fraction(int(req[1]),180))
        if not L or int(req[1])<=0:raise Unsupported('Nonconstant normal map and positive tolerance required')
        bound=m.div(m.mul(m.PI,angle),q(L))
        return geometric_profile('method.unit_normal_variation_bound',
            'Берём единичную нормаль как нормировку (−z_x,−z_y,1). Нормировка не увеличивает производную здесь, поскольку длина исходного вектора не меньше единицы. На отрезке внутри выпуклого квадрата угол не превосходит длины пути нормали. Получаем достаточную границу диаметра делением угла в радианах на норму гессиана.',
            sufficient_diameter_rule=[s('delta'),'<',bound],Hessian_norm=q(L))
    if output=='prove three confocal surfaces through M are orthogonal' and text==(
            'x^2/(a^2-lambda^2)+y^2/(b^2-lambda^2)+z^2/(c^2-lambda^2)=-1; a>b>c>0'):
        return geometric_profile('method.orthogonality_from_confocal_level_difference',
            'Вычитаем уравнения пары конфокальных уровней в их общей точке. Разность каждого обратного знаменателя содержит общий множитель λ_i²−λ_j². После сокращения остаётся скалярное произведение нормалей с постоянным множителем. Оно равно нулю для всех разных регулярных уровней.',
            pairwise_orthogonal=True,conditions=['distinct squared parameters','all source denominators nonzero','both level normals nonzero'])
    raise Unsupported('No certified normal or intercept construction on the stated surface')


def constrained_envelope_profile(text,conditions,output,space):
    """Eliminate stationary coordinates under the source parameter constraint and recover the contact locus."""
    if conditions or output not in ('find_envelope','prove normals envelope is evolute','shadow_cone'):
        raise Unsupported('Need a completely bound envelope or tangent-cone request')
    s=lambda k:('s',k);x,y,z=map(s,('x','y','z'));coords=(x,y,z);ident=r'[A-Za-z_]\w*'
    match=re.fullmatch(r'y=('+ident+r')\*x\+('+ident+r')/\1(?:\^(\d+))?, \2 constant',text)
    if not space and match:
        t,C,multiplicity=match.groups();order=int(multiplicity or 1)
        if len({t,C,'x','y'})!=4 or not 1<=order<=20:raise Unsupported('The fixed parameter and moving slope must be distinct')
        a,k=map(s,(C,t));px=m.div(m.mul(q(order),a),m.power(k,order+1));py=m.div(m.mul(q(order+1),a),m.power(k,order))
        value=dict(contact_parametrization=[px,py],parameter_condition=t+'!=0',degenerate_parameter=C+'=0 gives concurrent lines')
        if order==1:value['equation']=[m.power(y,2),'=',m.mul(q(4),m.mul(a,x))];value['regular_locus']='a!=0 and x!=0; vertex is only a closure point'
        return geometric_profile('method.stationary_slope_reciprocal_balance',
             'Дифференцируем исходную прямую по движущемуся наклону. Условие стационарности выражает точку касания как две обратные степени параметра. Подстановка проверяет и исходное уравнение и касание. Нулевой наклон остаётся исключённым.',**value)
    if not space and (span:=re.fullmatch(r'segment of length ('+ident+r') whose endpoints slide on the coordinate axes',text)):
        L=s(span[1]);t=s('t');cs,sn=('cos',t),('sin',t)
        return geometric_profile('method.envelope_of_fixed_length_intercept_segments',
             'Пара осевых отрезков длины l задаёт параметризацию (l cos t,l sin t). Стационарность линии отрезка даёт две линейные связи, из которых получаем координаты касания с кубами косинуса и синуса. Точка лежит на отрезке, а осевые вершины появляются как пределы.',
             contact_parametrization=[m.mul(L,m.power(cs,3)),m.mul(L,m.power(sn,3))],condition=span[1]+'>0',closed_envelope='astroid and all permitted axial reflections')
    measure= re.fullmatch(r'x\^2/a\^2\+y\^2/b\^2=1, enclosed area ('+ident+r') constant',text) if not space else \
             re.fullmatch(r'x\^2/a\^2\+y\^2/b\^2\+z\^2/c\^2=1; volume ('+ident+r') fixed',text)
    if measure:
        d=3 if space else 2;area=s(measure[1]);sphere_measure=m.mul(q(4,3),m.PI) if space else m.PI
        fixed=m.div(area,sphere_measure);scale=('sqrt',q(d));prod=m.ONE
        for a in coords[:d]:prod=m.mul(prod,a)
        return geometric_profile('method.fixed_measure_ellipsoid_envelope',
             'Сумма логарифмов полуосей постоянна. Вариации двух полуосей с противоположными логарифмическими приращениями уравнивают вклады координат в единицу. Каждый вклад равен 1/d. Обратная подстановка положительных полуосей √d·|x_i| проверяет все действительные ветви.',
             envelope=[('abs',prod),'=',m.div(fixed,m.power(scale,d))],semiaxis_witness=[m.mul(scale,('abs',v)) for v in coords[:d]],
             positive_measure=measure[1]+'>0')
    if not space and (hit:=re.fullmatch(r'ideal planar family of trajectories in vacuum, fixed initial speed ('+ident+r') and varying angle ('+ident+r')',text)):
        v,g=s(hit[1]),s('g');v2=m.power(v,2)
        envelope=m.add(m.div(v2,m.mul(q(2),g)),m.neg(m.div(m.mul(g,m.power(x,2)),m.mul(q(2),v2))))
        return geometric_profile('method.projectile_safety_parabola',
             'При x>0 исключаем время и записываем высоту как квадратный трёхчлен от тангенса угла. Его коэффициент при квадрате отрицателен. Стационарная высота даёт верхнюю огибающую. При x=0 вертикальная траектория имеет ту же предельную вершину.',
             envelope=[y,'=',envelope],stationary_slope=m.div(v2,m.mul(g,x)),domain='forward x>=0, initial speed and gravity positive')
    if not space and text=='normals to a planar curve' and output=='prove normals envelope is evolute':
        return geometric_profile('method.envelope_of_normal_lines',
             'Параметризуем регулярную кривую длиной дуги. Нормальная прямая записывается r(s)+h n(s). Её производная по s при фиксированном h равна (1−hκ)t. Стационарность требует h=1/κ, поэтому огибающая составляется из центров кривизны.',
             family_envelope='r(s)+n(s)/kappa(s)',regular_conditions=['regular C2 curve','nonzero curvature'],zero_curvature='no finite regular stationary contact at that parameter')
    if space and (hit:=re.fullmatch(r'spheres of radius ('+ident+r') centered on \(('+ident+r')\*cos\(('+ident+r')\),\2\*sin\(\3\),0\), \2>\1',text)):
        r,R,t=map(s,hit.groups());radius=('sqrt',m.add(m.power(x,2),m.power(y,2)))
        if len({r,R,t})!=3:raise Unsupported('The moving center and two fixed radii must be independent')
        return geometric_profile('method.stationary_distance_to_circular_centers',
             'В точке касания вектор от центра сферы перпендикулярен касательной к окружности центров. Планарные радиусы поэтому коллинеарны. Ветвь с расстоянием ρ+R невозможна при R>r, остаётся (ρ−R)²+z²=r². Обратный выбор полярного угла даёт контакт в каждой точке.',
             envelope=[m.add(m.power(m.add(radius,m.neg(R)),2),m.power(z,2)),'=',m.power(r,2)],conditions=['R>r>0','rho>0 on the torus'])
    if space and output=='shadow_cone' and text=='light source O; ball centered at C=(x0,y0,z0), radius R, ||C||^2>R^2':
        C=[s(k) for k in ('x0','y0','z0')];R=s('R');dot=m.dot(C,coords);norm=m.dot(C,C)
        return geometric_profile('method.tangent_cone_from_ray_discriminant',
             'Подставляем луч λ(x,y,z) в уравнение граничной сферы. Касание означает нулевой дискриминант квадратного уравнения. Скалярное произведение с направлением к центру должно быть положительным, чтобы точка касания лежала на прямом луче.',
             cone_equation=[m.power(dot,2),'=',m.mul(m.add(norm,m.neg(m.power(R,2))),m.dot(coords,coords))],
             forward_condition=[dot,'>',ZERO],contact_parameter=m.div(dot,m.dot(coords,coords)))
    raise Unsupported('No complete stationary parameter and geometric contact witness in this family')


def translate_discriminant(text,conditions,output):
    from math import gcd
    if output!='classify_discriminant_curves' or len(conditions)!=1:
        raise Unsupported('The moving family coordinate and classification must be explicit')
    if match:=re.fullmatch(r'y(?:\^(\d+))?=\(x-([A-Za-z_]\w*)\)\^(\d+)',text):
        mdeg,t,ndeg=match.groups();a,b=int(mdeg or 1),int(ndeg)
        if conditions!=[t+' variable'] or a<1 or b<2 or gcd(a,b)!=1 or a>1 and (a%2==b%2):
            raise Unsupported('The singular contact type needs another branch analysis')
        if a==1:
            return geometric_profile('method.discriminant_of_monomial_translates',
                 'Производная по параметру обнуляется только в переменной точке (c,0). В этой точке исходная кривая гладка и касательна к оси. Для чётной степени соседние сдвиги пересекаются с пределом на оси. При нечётной степени они не пересекаются, хотя общая касательная трасса та же.',
                 discriminant='y=0',type='regular horizontal contact',adjacent_intersections=b%2==0,contact_order=b)
        return geometric_profile('method.discriminant_of_monomial_translates',
             'Условие стационарности даёт линию положения особых точек. Оба градиента координатного уравнения там исчезают. Параметризация x−c=t^m, y=t^n выявляет касательную точки возврата по меньшей степени.',
             discriminant='y=0',type='locus of cusps',cusp_tangent='horizontal' if a<b else 'vertical',orders=[a,b])
    if (match:=re.fullmatch(r'\(y-([A-Za-z_]\w*)\)\^2=x\^2\*\(([A-Za-z_]\w*)-x\)/\(\2\+x\)',text)) and conditions==[match[1]+' variable']:
        return geometric_profile('method.discriminant_of_rational_square_translates',
             'Стационарность требует y=c. После её подстановки получаем x=0 или x=a и сохраняем исключение x=−a. В x=0 ведущие члены дают две косые касательные узла. В x=a корень простой и касательная вертикальна, совпадая с огибающей.',
             regular_envelope='x='+match[2],singular_discriminant='node locus x=0 when a!=0',source_exclusion='x=-'+match[2],
             degenerate_case='a=0 gives no real member outside its pole')
    raise Unsupported('No verified real classification of the stationary level')


def intrinsic_section_angle(task):
    kind=task['kind'];meta=task.get('source',{});base={'id','kind','source'};s=lambda k:('s',k)
    if not isinstance(meta,dict) or set(meta)-{'exercise','pdf_page','printed_page','pdf_sha256','printed_subpart','literal_requirement'}:
        raise Unsupported('The angle request has additional source conditions')
    if kind=='loxodrome_constant_angle':
        heading='Доказать, что напечатанная локсодрома пересекает все меридианы сферы под одинаковым углом.'
        match=re.fullmatch(r'tan\(pi/4\+psi/2\)=exp\(([A-Za-z_]\w*)\*phi\)',task.get('curve',''))
        if (set(task)-base-{'curve','coordinates',match[1] if match else ''} or not match or
                task.get(match[1])!='constant' or task.get('coordinates')!='phi longitude, psi latitude' or
                meta.get('literal_requirement') not in (None,heading)):
            raise Unsupported('Need the exact latitude law and fixed slope in ordinary spherical coordinates')
        k=s(match[1]);cosine=m.div(('abs',k),('sqrt',m.add(m.ONE,m.power(k,2))))
        return geometric_profile('method.latitude_and_meridian_angle',
             'Дифференцируем логарифм тангенса половинного угла. Получаем ψ_φ=k cosψ. В сферической метрике меридиональная скорость пропорциональна ψ_φ, а поперечная cosψ. Их отношение постоянно. При k=0 пересечение прямоугольное.',
             acute_angle_cosine=cosine,latitude_chart='-pi/2<psi<pi/2')
    heading='Найти тангенс угла касательной к кривой с плоскостью Oxy в данной точке.'
    point=task.get('point_projection',[]);curve=task.get('curve',[])
    if (set(task)-base-{'point_projection','curve','hypothesis'} or len(point)!=2 or len(curve)!=2
            or not (match:=re.fullmatch(r'z=([A-Za-z_]\w*)\(x,y\)',curve[0]))
            or not (direction:=re.fullmatch(r'\(x-([A-Za-z_]\w*)\)/cos\(([A-Za-z_]\w*)\)=\(y-([A-Za-z_]\w*)\)/sin\(\2\)',curve[1]))
            or (direction[1],direction[3])!=tuple(point) or task['hypothesis']!=match[1]+' differentiable'
            or meta.get('literal_requirement') not in (None,heading)):
        raise Unsupported('Need the exact horizontal projection and differentiable source graph')
    angle=s(direction[2]);tangent=m.add(m.mul(s(match[1]+'_x'),('cos',angle)),m.mul(s(match[1]+'_y'),('sin',angle)))
    return geometric_profile('method.projected_tangent_angle',
         'Параметризуем горизонтальную проекцию единичным вектором направления. Вертикальная компонента касательной получается по правилу цепочки для графика. Делим её модуль на горизонтальную длину, равную единице.',
         tangent_of_angle=('abs',tangent),oriented_tangent=tangent,point=point,
         literal_domain='cos(alpha) and sin(alpha) are nonzero in the quotient notation')
