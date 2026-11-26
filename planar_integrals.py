"""Lower original plane domains to checked moment and radial integration goals."""
import re
from fractions import Fraction

import expressions as m
from model import ONE, ZERO, Unsupported, freeze, q
from tasks import domain_conditions, guard_source, known_guard, source
from verify import same_value

KINDS={'planar_exact_integral':['exact_integral'],'planar_integral_mean':['area_mean'],
       'planar_area':['exact_area'],'polar_change_bounds':['polar_integrand_with_jacobian','bounds'],
       'polar_integral_reduction':['one_dimensional_integral'],'planar_integral_reduction':['one_dimensional_integral']}
X,Y=('s','x'),('s','y')


def fresh_coordinate(name,occupied):
    while name in occupied:name+='_'
    return name


POSITIVE_SECTION = (
    'Все параметры в этом и следующих параграфах раздела IV считать положительными, с. 208.',
    'Параметры положительны по общему соглашению раздела IV на с.208.',
)


def curve_chart_goal(task):
    kind=task.get('kind')
    curve=task.get('curve','')
    return (kind=='wire_mass_properties'
            or kind=='line_integral_from_geometric_locus' and 'scalar' in task
            or kind=='space_curve_length' and task.get('endpoints')=='0<t<infinity'
            or kind=='line_integral' and 'scalar' in task and len(task.get('variables',[]))==2 and task.get('source',{}).get('literal_requirement')==
                    'Вычислить интеграл первого рода по напечатанной параметризации и промежутку.'
            or kind in ('curve_chart_integral','difference_of_path_integrals','path_integral_given_area','rolling_circle_area')
            or kind=='greens_boundary_integral' and (isinstance(curve,str) and
                (curve.startswith('positively oriented boundary 0<x<') or task.get('requested_output')==['double_integral_expression']))
            or kind=='line_integral_from_geometric_locus' and 'coefficients' in task and isinstance(curve,str) and
                ('orientation' in task and ('and y=' in curve or re.fullmatch(r'x\^2\+y\^2=\w+\*x,y>=0',curve)) or
                 curve.startswith(('Viviani ','boundary of unit sphere patch ')) or ',y=x*tan(' in curve)
            or kind=='surface_area' and isinstance(task.get('surface'),str) and ' inside ' in task['surface']
            or kind=='area_from_line_integral' and isinstance(curve,str) and
                (curve.startswith('lemniscate ') or ' and coordinate axes' in curve or curve.startswith('(x+y)^(')))


def curve_harmonic_integral(expr,var,params,conditions,a,b):
    """Integrate a finite polynomial/exponential/Fourier density, including a decaying tail."""
    from integrals import harmonic_proposal,verify_harmonic_family
    task=dict(kind='integrate',integrand=source(expr),variable=var,parameters=params,
              requested_output=['primitive_family'])
    witness=harmonic_proposal(task,conditions)
    value,_=verify_harmonic_family(task,witness,conditions)
    primitive=value['representative']
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conditions))
    def endpoint(point):
        if point in ('-inf','+inf'):
            sign=1 if point=='-inf' else -1
            if any(m.sign(row['rate'],ctx)!=sign for row in witness['modes']):
                raise Unsupported('A harmonic mode has no decaying tail on the specified endpoint')
            return ZERO
        p=m.substitute(primitive,{('v',var):point})
        if not m.constant_defined(p,ctx):raise Unsupported('The curve primitive has an undefined endpoint')
        return m.simplify(p)
    return m.simplify(m.add(endpoint(b),m.neg(endpoint(a)))),witness


def curve_chart_moment(expr,var,params,conds,a,b,request,role):
    expr=m.simplify(expr);coordinate=('v',var)
    try:
        value,proof=curve_harmonic_integral(expr,var,params,conds,a,b)
        return dict(density=expr,bounds=(a,b),value=value,harmonic_coefficients=proof),value
    except (Unsupported,ArithmeticError):pass
    if isinstance(a,str) or isinstance(b,str):
        raise Unsupported('Need a checked convergent moment at the infinite endpoint')
    if change:=positive_radical_moment(expr,var,params,conds,a,b):
        return change,change['value']
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conds))
    from quadrature import enclose,guard_bounds
    from plane_domains import metric_sign
    for guard,e in domain_conditions(expr):
        if known_guard((guard,e),ctx):continue
        if guard=='nonnegative' and metric_sign(e,var,a,b,ctx) in (0,1):continue
        aa,bb=enclose(a,None),enclose(b,None)
        guard_bounds(guard,e,(aa[0],bb[1]),[var])
    # Remove a globally defined constant factor before asking for a scalar primitive.
    num,den=m.rational_form(expr)
    def constant_part(poly):
        common=m.common_mon(poly) if poly else {}
        return m.poly_expr({tuple((atom,degree) for atom,degree in sorted(common.items(),key=lambda p:str(p[0]))
                                  if not m.contains(atom,coordinate)):1})
    factor=m.div(constant_part(num),constant_part(den))
    residual=m.simplify(m.div(expr,factor))
    if not m.constant_defined(factor,ctx) or not same_value(expr,m.mul(factor,residual)):
        raise Unsupported('The scalar density cannot be separated on the full parameter domain')
    child=dict(kind='iterated_integral',integrand=source(residual),parameters=params,
               stated_conditions=conds,integration_order=[dict(variable=var,lower=source(a),upper=source(b))],
               requested_output=['exact_integral'])
    value=m.simplify(m.mul(factor,freeze(request(role,child)['value'])))
    return dict(density=expr,integrated_density=residual,constant_factor=factor,bounds=(a,b),value=value),value


def positive_radical_moment(expr,var,params,conditions,a,b):
    """Recognize u' sqrt(u) by exact comparison of the finite modes in the residual."""
    from integrals import affine,harmonic_modes,harmonic_equal,harmonic_scale,learned_nodes,HARMONIC_ZERO
    ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conditions))
    def modes(f):
        return harmonic_modes(dict(kind='integrate',integrand=source(f),variable=var,parameters=params),conditions)[0]
    for node in dict.fromkeys(z for z in learned_nodes(expr) if isinstance(z,tuple) and z[0]=='sqrt' and z[1][0]=='cosh'):
        u=node[1]
        try:
            slope,_=affine(u[1],var)
            if not m.nonzero(slope,ctx):continue
            remaining=m.simplify(m.div(expr,node))
            transformed=m.mul(slope,('sinh',u[1]))
            left,right=modes(remaining),modes(transformed)
        except Unsupported:continue
        pair=next(((key,i,j) for key,row in right.items() for i,coeff in enumerate(row)
                   for j,v in enumerate(coeff) if m.nonzero(v,ctx)),None)
        if pair is None:continue
        key,i,j=pair
        l=left.get(key,[])
        coefficient=m.simplify(m.div(l[i][j],right[key][i][j])) if i<len(l) else ZERO
        if not m.constant_defined(coefficient,ctx) or not same_value(expr,m.mul(node,remaining)):continue
        def at(table,key,i):
            modes=table.get(key,[])
            return modes[i] if i<len(modes) else HARMONIC_ZERO
        if any(not harmonic_equal(at(left,k,i),harmonic_scale(at(right,k,i),coefficient))
               for k in set(left)|set(right) for i in range(max(len(left.get(k,[])),len(right.get(k,[]))))):
            continue
        primitive=m.mul(m.mul(q(2,3),coefficient),m.mul(u,node))
        A,B=[m.substitute(primitive,{('v',var):v}) for v in (a,b)]
        if not all(m.constant_defined(v,ctx) for v in (A,B)):continue
        return dict(density=expr,bounds=(a,b),change=u,chain_coefficient=coefficient,
                    domain='cosh is strictly positive on the real line',checked_primitive=primitive,
                    value=m.simplify(m.add(B,m.neg(A))))
    return None


def known_curve_speed(curve,var,params,conds,a,b,request):
    """Find a square root of the squared speed without losing a fixed amplitude's sign."""
    from plane_domains import metric_sign,metric_square_root
    v=('v',var);ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conds))
    amplitude=ONE;unit=curve
    for name in params:
        z=('s',name);possible=[m.simplify(m.div(c,z)) for c in curve]
        if any(m.contains(c,z) for c in possible) or not all(same_value(c,m.mul(p,z)) for c,p in zip(curve,possible)):
            continue
        unit=possible
        amplitude=m.simplify(z if m.sign(z,ctx)==1 else ('abs',z))
        break
    velocity=[freeze(request('differentiate curve coordinate '+str(i),dict(
        kind='differentiate',function=source(x),variable=var,parameters=params,stated_conditions=conds,
        method_requirement='table_and_rules'))['value']) for i,x in enumerate(unit)]
    square=m.simplify(m.dot(velocity,velocity))
    speed,proof=metric_square_root(square,var,a,b,ctx)
    if proof is None and square[0]!='q':
        from integrals import harmonic_modes,harmonic_equal,HARMONIC_ZERO
        for candidate in (('cosh',m.mul(q(2),v)),):
            difference=m.add(square,m.neg(candidate))
            try:
                modes,_,_=harmonic_modes(dict(kind='integrate',integrand=source(difference),variable=var,parameters=params),conds)
            except Unsupported:continue
            if all(harmonic_equal(pair,HARMONIC_ZERO) for coeffs in modes.values() for pair in coeffs):
                speed=('sqrt',candidate);proof=dict(method='harmonic_square_norm',radicand=candidate)
                break
    if proof is None and metric_sign(speed,var,a,b,ctx) not in (0,1):
        raise Unsupported('The proposed speed sign is not confirmed on the whole arc')
    return m.simplify(m.mul(amplitude,speed)),dict(amplitude=amplitude,normalized_velocity=velocity,
                original_speed_square=square,root_proof=proof)


def source_curve_integrals(task,library,request):
    """Compile arc length, scalar density and moments into one-dimensional obligations."""
    from cartesian_fields import vector_source
    if not library.data.get('source_curve_chart_integrals'):raise Unsupported('No curve chart method is available')
    kind=task['kind'];wanted=task['requested_output']
    if kind in ('greens_boundary_integral','difference_of_path_integrals','path_integral_given_area') or (
            kind=='line_integral_from_geometric_locus' and 'coefficients' in task):
        return curve_circulation(task,request)
    if kind in ('area_from_line_integral','rolling_circle_area','surface_area'):
        return boundary_measure_chart(task,request)
    base=dict(theorem='method.curve_chart_moments')
    if kind in ('line_integral','curve_chart_integral'):
        vector_source(task,{'variables','parameter','parameters','stated_conditions','path','scalar','requested_output'},(
            'Вычислить интеграл первого рода по напечатанной параметризации и промежутку.',))
        params=task.get('parameters',[]);conds=task.get('stated_conditions',[]);names=task['variables'];var=task['parameter']
        if (wanted!=['line_integral'] or len(names) not in (2,3) or len(names)!=len(set(names)) or
                set(names)&set(params) or len(task['path'])!=1):
            raise Unsupported('A single complete scalar arc and all its coordinate names are required')
        ctx=m.context(dict(variable=var,parameters=params,parameter_conditions=conds))
        segment=task['path'][0]
        if set(segment)!={'map','lower','upper'} or len(segment['map'])!=len(names):
            raise Unsupported('The original parametrization or its bounds are incomplete')
        a,b=[m.parse(str(segment[k]),None,params) for k in ('lower','upper')]
        if not all(m.constant_defined(x,ctx) for x in (a,b)):
            raise Unsupported('The endpoints must initially be defined')
        if m.sign(m.add(b,m.neg(a)),ctx)==-1:a,b=b,a
        if not m.known_nonnegative(m.add(b,m.neg(a)),ctx):
            raise Unsupported('The parameter limits are not ordered on the whole stated component')
        curve=[m.parse(c,var,params) for c in segment['map']]
        from quadrature import enclose,guard_bounds
        def guarded(expressions,smooth):
            for key,e in (g for x in expressions for g in domain_conditions(x,smooth)):
                if known_guard((key,e),ctx):continue
                lo,hi=enclose(a,None),enclose(b,None)
                guard_bounds(key,e,(lo[0],hi[1]),[var])
        guarded(curve,True)
        speed,speed_proof=known_curve_speed(curve,var,params,conds,a,b,request)
        weight=m.parse(task['scalar'],None,[*names,*params])
        restricted=m.substitute(weight,dict(zip([('s',n) for n in names],curve)))
        guarded([restricted],False)
        plan,value=curve_chart_moment(m.mul(restricted,speed),var,params,conds,a,b,request,'weighted scalar arc moment')
        return dict(base,argument=['Differentiate every coordinate and check the nonnegative square root of the full speed squared.',
                                   'Restrict the original scalar field to the complete parameter interval and integrate against the speed.'],
                    path=curve,speed=speed,speed_proof=speed_proof,integral=plan),dict(line_integral=value)
    return implicit_curve_chart(task,base,request)


def implicit_curve_chart(task,base,request):
    from cartesian_fields import same_form_coefficient,vector_source
    kind=task['kind'];want=task['requested_output']
    T=('v','t');pi=m.PI;half_pi=m.div(pi,q(2));two_pi=m.mul(q(2),pi)
    sine,cosine=('sin',T),('cos',T)
    symbol=lambda s:('s',s)
    def scaled(A,*forms):return [m.mul(A,x) for x in forms]
    def chart(names,a,b,x,speed,argument,repeat=1,conds=None):
        return dict(parameters=list(names),conditions=[n+'>0' for n in names] if conds is None else conds,
                    interval=(a,b),path=x,speed=speed,copies=repeat,coverage=argument)
    def arc(form,label,C,weight=ONE):
        a,b=C['interval']
        detail,val=curve_chart_moment(m.mul(weight,m.mul(form,C['speed'])),'t',C['parameters'],C['conditions'],a,b,request,label)
        return detail,m.simplify(m.mul(q(C['copies']),val))
    name=r'([A-Za-z_]\w*)'
    curve=task['curve']
    if kind=='space_curve_length':
        vector_source(task,{'curve','endpoints','stated_conditions','requested_output'},
                      ('Найти длину дуги; параметры положительны.',))
        if (want!=['arc_length'] or task['endpoints']!='0<t<infinity'
                or task['stated_conditions'] not in ([],['parameters positive']) or len(curve) not in (2,3)):
            raise Unsupported('A complete parametrization on the positive unbounded ray is required')
        paths=[m.parse(c,'t') for c in curve]
        ctx=m.context(dict(variable='t'))
        if any(not known_guard(g,ctx) for x in paths for g in domain_conditions(x,True)):
            raise Unsupported('Smoothness on the entire parameter ray is unproved')
        speed,sp=known_curve_speed(paths,'t',[],[],ZERO,ONE,request)
        if speed[0] not in ('mul','exp') or m.constant_defined(speed,m.context({})):
            raise Unsupported('A globally proved decaying speed is required on the positive ray')
        # The square-root reduction is positive on the whole real ray if this speed is a positive constant times a real exponential.
        div=[node for node in (speed,*speed[1:]) if isinstance(node,tuple) and node[0]=='exp']
        if len(div)!=1 or m.sign(m.simplify(m.div(speed,div[0])),ctx)!=1:
            raise Unsupported('The normalized speed on the infinite ray has an unproved sign')
        plan,value=arc(ONE,'arc length on the convergent ray',
                       chart((),ZERO,'+inf',paths,speed,'The original entire parameter ray is traversed.'))
        return dict(base,speed_proof=sp,integral=plan,argument=['Differentiate the original map and extract a positive exponential speed.',
            'The primitive has a vanishing endpoint contribution at positive infinity.']),dict(arc_length=value)
    if kind=='line_integral_from_geometric_locus':
        vector_source(task,{'curve','scalar','requested_output'},
                      ('Вычислить интеграл первого рода по указанной дуге.',))
        if want!=['line_integral']:raise Unsupported('The requested scalar line integral changed')
        cells=[];manual=None
        if shape:=re.fullmatch(fr'circle x\^2\+y\^2={name}\*x',curve):
            A=symbol(shape[1]);radius=m.simplify(m.div(('abs',A),q(2)))
            cells=[chart(shape.groups(),ZERO,two_pi,[m.add(m.div(A,q(2)),m.mul(radius,cosine)),m.mul(radius,sine)],radius,
                         'Circle center is (a/2,0), radius |a|/2, and one full turn covers it once.',conds=[])]
            if task['scalar']=='sqrt(x^2+y^2)':
                cells=[chart(shape.groups(),m.neg(half_pi),half_pi,scaled(A,m.power(cosine,2),m.mul(cosine,sine)),('abs',A),
                             'The signed polar radius a*cos(t) parametrizes one full circle on this half-turn.',conds=[])]
                manual=lambda c:m.mul(('abs',A),cosine)
        elif shape:=re.fullmatch(fr'catenary y={name}\*cosh\(x/\1\)',curve):
            A=symbol(shape[1]);params=list(shape.groups())
            if not same_form_coefficient(m.parse(task['scalar'],None,['x','y',*params]),
                                         m.div(ONE,m.power(('s','y'),2)),['x','y',*params]):
                raise Unsupported('The positive exponential substitution requires the inverse-square height weight')
            plan=dict(base,argument=[
                'Put t=x/a for the whole catenary at a≠0. The arc speed after this change is |a| cosh(t).',
                'The restricted density is sech(t)/|a|. With u=e^t it becomes 2 du/(|a|(1+u²)) on (0,+∞).',
                'The primitive uses atan(u), with limiting values 0 and π/2.'])
            return plan,dict(line_integral=m.div(pi,('abs',A)),parameter_domain=shape[1]+'!=0')
        elif shape:=re.fullmatch(fr'arc of x\^\(2/3\)\+y\^\(2/3\)={name}\^\(2/3\)',curve):
            A=symbol(shape[1]);radius=('abs',A);params=list(shape.groups())
            if task['scalar']!='x^(4/3)+y^(4/3)':raise Unsupported('Retain the real rational powers in the original density')
            cells=[chart(params,ZERO,half_pi,scaled(radius,m.power(cosine,3),m.power(sine,3)),
                         m.mul(q(3),m.mul(radius,m.mul(sine,cosine))),
                         'Together the four reflected sign branches of the cubed sine and cosine cover the implicit astroid exactly once.',4,[])]
            manual=lambda c:m.mul(m.power(('cbrt',A),4),m.add(m.power(sine,4),m.power(cosine,4)))
        elif shape:=re.fullmatch(fr'convex boundary r={name},phi=0,phi=pi/4',curve):
            A=symbol(shape[1]);params=list(shape.groups());angle=m.div(pi,q(4))
            if task['scalar']!='exp(sqrt(x^2+y^2))':raise Unsupported('The stated radial density must be identified')
            cells=[chart(params,ZERO,A,[T,ZERO],ONE,'Two radial edges at fixed angles have unit speed and identical radial weights.',2),
                   chart(params,ZERO,angle,scaled(A,cosine,sine),A,'The third edge is the circle of radius a on the stated sector.')]
            manual=lambda c:('exp',T if c['copies']==2 else A)
        elif shape:=re.fullmatch(fr'logarithmic spiral r={name}\*exp\({name}\*phi\) inside r<=\1,\2>0',curve):
            A,K=map(symbol,shape.groups());radius=m.mul(A,('exp',m.mul(K,T)))
            cells=[chart(shape.groups(),'-inf',ZERO,[m.mul(radius,cosine),m.mul(radius,sine)],
                         m.mul(radius,('sqrt',m.add(ONE,m.power(K,2)))),
                         'The positive radius is strictly increasing for k>0 and r≤a exactly on t≤0.')]
        elif shape:=re.fullmatch(fr'arc of \(x\^2\+y\^2\)\^2={name}\^2\*\(x\^2-y\^2\)',curve):
            A=symbol(shape[1]);R=('abs',A);params=list(shape.groups());angle=m.div(pi,q(4))
            if task['scalar']!='abs(y)':raise Unsupported('The norm at the tip requires cancellation against the original weight')
            cells=[chart(params,ZERO,angle,[],('abs',A),
                         'On a half lobe, r=|a| sqrt(cos(2t)) and ds=|a| dt/sqrt(cos(2t)). The weight |y| cancels the root. Four reflected halves cover both lobes.',4,[])]
            manual=lambda c:m.mul(R,sine)
        elif shape:=re.fullmatch(fr'circle x\^2\+y\^2\+z\^2={name}\^2,x\+y\+z=0',curve):
            A=symbol(shape[1]);R=('abs',A);params=list(shape.groups())
            basis=(([2,-1,-1],q(6)),([0,1,-1],q(2)))
            cells=[chart(params,ZERO,two_pi,[
                m.mul(R,m.add(m.mul(m.div(q(i),('sqrt',basis[0][1])),cosine),m.mul(m.div(q(j),('sqrt',basis[1][1])),sine)))
                for i,j in zip(basis[0][0],basis[1][0])],R,
                'Two orthogonal unit vectors in the stated plane yield one circuit of its intersection with the sphere.',conds=[])]
        else:raise Unsupported('No checked chart covers the original locus and arc')
        parts=[];value=ZERO
        for i,C in enumerate(cells):
            names='xyz'[:len(C['path'])]
            f=manual(C) if manual else m.substitute(m.parse(task['scalar'],None,[*names,*C['parameters']]),
                                                    dict(zip(map(symbol,names),C['path'])))
            ctx=m.context(dict(variable='t',parameters=C['parameters'],parameter_conditions=C['conditions']))
            if any(not known_guard(g,ctx) for g in domain_conditions(f)):
                raise Unsupported('A condition of the original scalar density has not been established by the chart')
            detail,v=arc(f,'integrate weighted curve piece '+str(i),C);parts.append(dict(chart=C,integral=detail));value=m.add(value,v)
        result=dict(line_integral=m.simplify(value))
        if curve.startswith('arc of'):
            result['whole_locus_convention']='The given source has no endpoints. For an individual arc integrate the same density on its component interval(s) only.'
        return dict(base,argument=[C['coverage'] for C in cells]+['Integrate the original scalar weight against the certified speed.'],
                    pieces=parts),result
    if kind!='wire_mass_properties':raise Unsupported('No compatible scalar curve geometry')
    vector_source(task,{'curve','density','requested_output'},('Найти указанные массовые характеристики дуги.',))
    if specialized:=conic_wire_moment(curve,task['density'],want,base):
        return specialized
    C,labels,result_type,weight=wire_chart(curve,task['density'],want,chart)
    values={};parts=[]
    for label,form in labels.items():
        receipt,val=arc(form,'wire moment '+label,C,weight)
        values[label]=val;parts.append(dict(quantity=label,**receipt))
    if result_type=='centroid':
        ctx=m.context(dict(variable='t',parameters=C['parameters'],parameter_conditions=C['conditions']))
        if m.sign(values['mass'],ctx)!=1:raise Unsupported('The normalizing mass has not been proved positive')
        result=dict(centroid=[m.simplify(m.div(values[coord],values['mass'])) for coord in 'xyz'[:len(C['path'])]])
    elif result_type=='mean_polar_radius_via_I0=s*r0^2':
        result=dict(radius=m.simplify(('sqrt',m.div(values['polar_inertia'],values['length']))))
    else:result=values
    return dict(base,argument=[C['coverage'],'Integrate the weight times speed and the appropriate coordinate moments.'],
                chart=C,moments=parts),result


def wire_chart(curve,raw_weight,want,chart):
    """Choose a chart for a specified rod and form the requested distance moments."""
    name=r'([A-Za-z_]\w*)';t=('v','t');pi=m.PI;half=m.div(pi,q(2));two=m.mul(q(2),pi)
    sn,cs=('sin',t),('cos',t);square=lambda a:m.power(a,2);sym=lambda s:('s',s)
    weight=ONE;curve=re.sub(r'^(?:square |astroid )','',curve)
    def scaled(p,*xs):return [m.mul(p,x) for x in xs]
    if (shape:=re.fullmatch(fr'x={name}\*\(t-sin\(t\)\),y=\1\*\(1-cos\(t\)\);0<=t<=pi',curve)) and raw_weight=='unit':
        A=sym(shape[1]);c=chart(shape.groups(),ZERO,pi,scaled(A,m.add(t,m.neg(sn)),m.add(ONE,m.neg(cs))),
            m.mul(m.mul(q(2),A),('sin',m.div(t,q(2)))),'The half cycloid is monotone in x and has speed 2a sin(t/2).')
    elif curve=='x=exp(t)*cos(t),y=exp(t)*sin(t),z=exp(t);-infty<t<=0' and raw_weight=='unit':
        e=('exp',t);c=chart((),'-inf',ZERO,[m.mul(e,cs),m.mul(e,sn),e],m.mul(('sqrt',q(3)),e),
                           'The height exp(t) is strictly increasing, and the speed follows from sin²(t)+cos²(t)=1.')
    elif (shape:=re.fullmatch(fr'x={name}\*cos\(t\),y=\1\*sin\(t\),z={name}\*t/\(2\*pi\);0<=t<=2\*pi',curve)) and raw_weight=='unit':
        A,H=map(sym,shape.groups());rise=m.div(H,two)
        c=chart(shape.groups(),ZERO,two,[m.mul(A,cs),m.mul(A,sn),m.mul(rise,t)],
                ('sqrt',m.add(square(A),square(rise))),
                'The distance from the axis stays constant, and one turn and the increasing height describe the full helix.')
    elif (shape:=re.fullmatch(fr'x\^2\+y\^2={name}\^2',curve)) and raw_weight=='unit':
        A=sym(shape[1]);c=chart(shape.groups(),ZERO,two,scaled(A,cs,sn),A,
                           'The given circle has one full turn. Any diameter may serve as the moment axis by rotation.')
    elif (shape:=re.fullmatch(fr'boundary of spherical triangle x\^2\+y\^2\+z\^2={name}\^2,x>=0,y>=0,z>=0',curve)) and raw_weight=='unit' and want==['centroid']:
        A=sym(shape[1]);c=chart(shape.groups(),ZERO,half,scaled(A,cs,sn,ZERO),A,
                           'The boundary consists of three quarter great circles. Each coordinate receives two identical nonzero quarter-circle moments.',3)
        return c,{'mass':ONE,**{axis:m.mul(q(2,3),m.mul(A,cs)) for axis in 'xyz'}},'centroid',ONE
    elif (shape:=re.fullmatch(fr'x\^\(2/3\)\+y\^\(2/3\)={name}\^\(2/3\);(.+)',curve)) and raw_weight=='unit':
        A=sym(shape[1]);tail=shape[2]
        if (tail,want) not in (('x>=0,y>=0',['both_static_moments']),('r0>0',['mean_polar_radius_via_I0=s*r0^2'])):
            raise Unsupported('Bind the quadrant or the full astroid and the exact requested moment')
        c=chart((shape[1],),ZERO,half,scaled(A,m.power(cs,3),m.power(sn,3)),m.mul(q(3),m.mul(A,m.mul(sn,cs))),
                'Use the positive quadrant cubed sine and cosine, where both factors in the speed are nonnegative. Even squared weights permit full reflection.',4 if tail=='r0>0' else 1)
    elif (shape:=re.fullmatch(fr'y\^2=2\*{name}\*x;0<=x<=\1/2',curve)) and raw_weight=='abs(y)' and want==['mass']:
        P=sym(shape[1]);s=('sinh',t);h=('cosh',t)
        c=chart(shape.groups(),ZERO,('ln',m.add(ONE,('sqrt',q(2)))),scaled(P,m.div(square(s),q(2)),s),m.mul(P,square(h)),
                'On one branch put y=p sinh(t). The endpoint is sinh(t)=1 and the opposite branch has the same mass.',2)
        weight=m.mul(P,s)
    elif (shape:=re.fullmatch(fr'max\(abs\(x\),abs\(y\)\)={name}',curve)) and raw_weight=='unit' and want==['polar_inertia']:
        A=sym(shape[1]);c=chart(shape.groups(),m.neg(A),A,[A,t],ONE,
                           'The four equal sides are images by right-angle rotations, which preserve polar distance.',4)
    elif (shape:=re.fullmatch(fr'regular triangular boundary, polar vertices \({name},0\),\(\1,2\*pi/3\),\(\1,4\*pi/3\)',curve)) and raw_weight=='unit' and want==['polar_inertia']:
        A=sym(shape[1]);end=m.div(m.mul(A,('sqrt',q(3))),q(2))
        c=chart(shape.groups(),m.neg(end),end,[m.div(A,q(2)),t],ONE,
                'Each straight side is at distance a/2 from the center and has half-length a sqrt(3)/2. Rotations preserve all three polar moments.',3)
    else:raise Unsupported('No certified map and mass density for the original wire')
    x,y,*z=c['path'];z=z[0] if z else ZERO;dist=m.dot(c['path'],c['path'])
    choices={
        'mass':{'mass':ONE},
        'centroid':{'mass':ONE,**dict(zip('xyz',c['path']))},
        'both_static_moments':{'about_x':y,'about_y':x},
        'inertia_about_diameter':{'inertia':square(y)},
        'all_three_axial_inertias':dict(Ix=m.add(square(y),square(z)),Iy=m.add(square(x),square(z)),
                                        Iz=m.add(square(x),square(y))),
        'polar_inertia':{'polar_inertia':dist},
        'mean_polar_radius_via_I0=s*r0^2':{'length':ONE,'polar_inertia':dist},
    }
    expected=('centroid' if curve.startswith(('x=exp','x=')) and ';0<=t<=pi' in curve or curve.startswith('x=exp') else
              'all_three_axial_inertias' if curve.startswith('x=') else
              'inertia_about_diameter' if curve.startswith('x^2+y^2=') else
              'mass' if raw_weight=='abs(y)' else
              'both_static_moments' if ';x>=0,y>=0' in curve else
              'mean_polar_radius_via_I0=s*r0^2' if ';r0>0' in curve else 'polar_inertia')
    if want!=[expected]:raise Unsupported('The wire type does not entail the requested output')
    return c,choices[expected],expected,weight


def conic_wire_moment(curve,weight,want,base):
    """Keep the axis/sign cases of normalized conic arc moments."""
    name=r'([A-Za-z_]\w*)'
    if (want==['mass'] and weight=='abs(y)' and
            (ellipse:=re.fullmatch(fr'ellipse x={name}\*cos\(t\),y={name}\*sin\(t\);\1>=\2>0;0<=t<=2\*pi',curve))):
        a,b=ellipse.groups();A=('s',a);B=('s',b);S=('sqrt',m.add(m.power(A,2),m.neg(m.power(B,2))))
        result=m.mul(m.mul(q(2),B),m.add(B,m.mul(m.div(m.power(A,2),S),('asin',m.div(S,A)))))
        return (dict(base,argument=[
            'On the first quadrant set u=cos(t) in the moment with weight y=b sin(t). All four quadrants contribute equally.',
            'The reduced integral is 4b times the integral of sqrt(a²−(a²−b²)u²) on [0,1]. The argument is everywhere at least b²>0.',
            'If a>b use the sine substitution with arc-sine upper angle. If a=b the reduced integrand is constant.']),
            dict(cases=[{'condition':a+'>'+b,'mass':m.simplify(result)},
                        {'condition':a+'='+b,'mass':m.mul(q(4),m.power(A,2))}]))
    if (want==['centroid'] and weight=='unit' and
            (cat:=re.fullmatch(fr'y={name}\*cosh\(x/\1\);A\(0,\1\) to B\({name},{name}\)',curve))):
        a,b,h=cat.groups()
        A,B=('s',a),('s',b);u=m.div(B,A);s=('sinh',u);c=('cosh',u)
        x=m.add(B,m.neg(m.mul(A,m.div(m.add(c,q(-1)),s))))
        y=m.mul(A,m.div(m.add(m.div(u,q(2)),m.div(('sinh',m.mul(q(2),u)),q(4))),s))
        return (dict(base,argument=[
            'Check h=a cosh(b/a) and retain both possible signs of b. The measure is cosh(x/a)|dx|.',
            'The common orientation sign cancels in each centroid ratio. Put t=x/a.',
            'Use the endpoint integrals of cosh(t), t cosh(t), and cosh²(t). The mass is nonzero when b≠0.']),
            dict(centroid=[x,y],conditions=[a+'!=0',b+'!=0',h+'='+source(m.mul(A,c))]))
    return None


def curve_circulation(task,request):
    """Reduce a planar circulation or a complete oriented arc to its original region."""
    from cartesian_fields import same_form_coefficient,vector_source
    from integrals import propose
    kind=task['kind'];want=task['requested_output'];body=task.get('curve','')
    fields=task['coefficients'];xy=['x','y'];X,Y=(('s',s) for s in xy)
    pi=m.PI;half=m.div(pi,q(2));t=('v','t')
    standard={'coefficients','curve','requested_output'}
    def result(method,steps,**values):
        return dict(theorem='method.'+method,argument=steps),values
    def parsed(names,params=(),fun=()):
        if len(fields)!=len(names):raise Unsupported('Each coordinate requires an original field component')
        return [m.parse(f,None,[*names,*params],fun) for f in fields]
    def partial(expr,axis,names,params=(),conditions=()):
        proof=request('field derivative in '+axis,dict(kind='partial_derivatives',function=source(expr),variables=names,
            parameters=list(params),stated_conditions=list(conditions),requested_partials=[[axis]],
            requested_output=['specified_partial_derivatives']))
        return freeze(proof['partial_values'][0][1])
    def graph_strip(P,Q,a,b,lo,hi,orientation):
        if any(domain_conditions(f,True) for f in (P,Q)):
            raise Unsupported('Need a smooth one-form on the entire closed graph strip')
        curl=m.simplify(m.add(partial(Q,'x',xy),m.neg(partial(P,'y',xy))))
        vertical=m.substitute(curl,{Y:('v','y')})
        primitive,_=propose(vertical,'y')
        prim=m.substitute(primitive,{('v','y'):Y})
        if not same_value(partial(prim,'y',xy),curl):
            raise Unsupported('The vertical primitive must differentiate to the original curl')
        h=m.substitute(m.add(m.substitute(prim,{Y:hi}),m.neg(m.substitute(prim,{Y:lo}))),{X:t})
        plan,v=curve_chart_moment(h,'t',[],[],a,b,request,'one-dimensional integral of the planar curl')
        return dict(theorem='method.green_graph_strip',argument=[
            'For the certified graph strip use its boundary orientation and Green’s formula.',
            'Differentiate both original components, subtract in their oriented order, and check a vertical primitive.',
            'The remaining integral is the vertical endpoint difference integrated along the horizontal interval.'],
            bounds=dict(x=(a,b),y=(lo,hi)),orientation=orientation,curl=curl,vertical_primitive=prim,moment=plan),m.mul(q(orientation),v)
    if kind=='greens_boundary_integral':
        vector_source(task,standard|{'method_requirement'},('Применить формулу Грина.',))
        if task['method_requirement']!='green_theorem':raise Unsupported('The specified theorem is required')
        bound=re.fullmatch(r'positively oriented boundary 0<x<(pi|[1-9]\d*),0<y<sin\(x\)',body)
        if want==['line_integral'] and bound:
            b=m.parse(bound[1],None)
            if (m.sign(b,m.context({}))!=1 or m.sign(m.add(pi,m.neg(b)),m.context({})) not in (0,1)):
                raise Unsupported('Sine must be nonnegative on the whole graph strip')
            plan,v=graph_strip(*parsed(xy),ZERO,b,ZERO,('sin',X),1)
            return plan,dict(boundary_integral=v)
        if want==['double_integral_expression'] and body=='boundary of a bounded planar region S':
            P,Q=parsed(xy);r=('sqrt',m.dot((X,Y),(X,Y)));log=('ln',m.add(X,r))
            # Remove the explicit singular potential only after binding the original logarithm.
            coefficient=m.simplify(m.add(Q,m.neg(m.mul(Y,log))))
            if (not same_form_coefficient(P,r,xy)
                    or not same_form_coefficient(Q,m.add(coefficient,m.mul(Y,log)),xy)
                    or domain_conditions(coefficient,True) or m.contains(coefficient,log)):
                raise Unsupported('The original logarithmic boundary form has no certified regular remainder')
            remainder=m.add(coefficient,m.mul(q(-1,2),Y));value=partial(remainder,'x',xy)
            return result('green_graph_strip',[
                'On x+r>0 the exact potential H=(x*r+y² ln(x+r))/2 has derivatives r and y ln(x+r)+y/2.',
                'Subtract dH, which has zero circulation on the original defined closed curve. The remaining dy coefficient is smooth.',
                'Apply Green to the remainder. On x+r=0 the literal logarithm is undefined. A continuous extension, if used, is justified by the limits of y ln(x+r) and y² ln(x+r).'],
                double_integral=dict(region='S',integrand=value),orientation='positive',
                original_domain='x+sqrt(x²+y²)>0 along C',regularized_remainder=remainder)
        raise Unsupported('The original Green region and requested integral are not jointly covered')
    if kind=='difference_of_path_integrals':
        vector_source(task,{'coefficients','paths','requested_output'},('Найти разность двух указанных интегралов.',))
        if want!=['difference'] or len(task['paths'])!=2 or (
                task['paths'][1]!='vertical-axis parabola through A,B and origin, oriented A to B'):
            raise Unsupported('The two oriented graphs and all three points are required')
        numbers=re.fullmatch(r'line from A\((-?\d+),(-?\d+)\) to B\((-?\d+),(-?\d+)\)',task['paths'][0])
        if not numbers:raise Unsupported('The common endpoints must be identifiable')
        from fractions import Fraction as F
        a,u,b,v=map(F,numbers.groups())
        if not a or not b or a>=b:raise Unsupported('Three distinct horizontal coordinates are needed')
        k=(v/b-u/a)/(b-a);d=u/a-k*a
        if not k:raise Unsupported('No genuine parabolic region is bounded by the graphs')
        line=m.add(q(u),m.mul(q((v-u)/(b-a)),m.add(X,q(-a))))
        parabola=m.add(m.mul(q(k),m.power(X,2)),m.mul(q(d),X))
        # The graph difference is -k(x-a)(x-b), which has the sign of k inside.
        low,high,sign=(parabola,line,-1) if k>0 else (line,parabola,1)
        plan,val=graph_strip(*parsed(xy),q(a),q(b),low,high,sign)
        plan['graph_order_proof']=dict(line=line,parabola=parabola,interior_gap_factor=q(k))
        return plan,dict(difference=val)
    if kind=='path_integral_given_area':
        vector_source(task,standard|{'stated_conditions'},('Вычислить через указанные концы и площадь.',))
        if (want!=['formula_with_endpoints_and_area'] or body!='open path A(x1,y1) to B(x2,y2), encloses area S when closed by segment BA'
                or task['stated_conditions']!=['phi and phi_prime continuous']):
            raise Unsupported('The original area, endpoints and derivative linkage must all be known')
        P,Q=parsed(xy,['m'],['phi','phi_prime'])
        M=('s','m');E=('exp',X)
        if not all(same_form_coefficient(f,g,['x','y','m']) for f,g in (
                (P,m.add(m.mul(('phi',Y),E),m.neg(m.mul(M,Y)))),
                (Q,m.add(m.mul(('phi_prime',Y),E),m.neg(M))))):
            raise Unsupported('The proposed exact differential does not match both field components')
        return result('green_graph_strip',[
            'Subtract the differential of H=e^x phi(y)−my. The remainder is −my dx.',
            'Complete the contour by the stated segment BA. Green gives m times the signed enclosed area.',
            'On the straight segment y is affine in x. Its contribution is m(x2−x1)(y1+y2)/2, which must be subtracted.'],
            formula='H(B)-H(A)+m*(S_signed-(x2-x1)*(y1+y2)/2)',potential='H=e^x*phi(y)-m*y')

    vector_source(task,standard|{'orientation','suggested_method'},(
        'Замкнутый обход OmAnO: OmA по параболе, OnA по прямой.',
        'Вычислить по указанной пространственной кривой с заданным направлением.',
        'Вычислить интеграл по верхней полуокружности от A(a,0) к O(0,0).'))
    if want!=['line_integral']:raise Unsupported('The full oriented line integral was requested')
    orientation=task.get('orientation')
    circle=re.fullmatch(r'x\^2\+y\^2=([A-Za-z]\w*)\*x,y>=0',body)
    if circle and orientation==f'from A({circle[1]},0) to O(0,0)' and task.get('suggested_method') in (None,'close with OA'):
        P,Q=parsed(xy,['m']);M=('s','m')
        F=m.mul(('exp',X),('sin',Y))
        if not all(same_form_coefficient(f,g,['x','y','m']) for f,g in (
                (P,m.add(F,m.neg(m.mul(M,Y)))),
                (Q,m.add(m.mul(('exp',X),('cos',Y)),m.neg(M))))):
            raise Unsupported('The semicircular field needs the checked potential and constant curl')
        A=('s',circle[1]);val=m.mul(m.div(pi,q(8)),m.mul(M,m.power(A,2)))
        return result('green_graph_strip',[
            'The differential of e^x sin(y)−my accounts for both components except −my dx.',
            'It has equal endpoint values along the x-axis. The added straight segment also has zero remainder.',
            'Green integrates the constant curl m on the half disk. The traversal from A to 0 is positive when a>0 and negative when a<0.'],
            line_integral=m.mul(m.div(A,('abs',A)),val),domain=circle[1]+'!=0')
    if (body=='y=x^2 and y=x between intersections' and orientation==
            'O(0,0) to A(1,1) along y=x^2; A(1,1) to O(0,0) along y=x' and not task.get('suggested_method')):
        P,Q=parsed(xy)
        if not same_form_coefficient(P,q(-1),xy) or not same_form_coefficient(Q,('atan',m.div(Y,X)),xy):
            raise Unsupported('The original singular angle branch is unresolved')
        return result('green_graph_strip',[
            'The lower parabola is traversed O→A and the upper line A→O, giving positive orientation.',
            'Excise a small disk at O. The form is bounded and the curl −y/(x²+y²) is integrable there.',
            'Put y=xt. After the Jacobian, the double integral is −∫_0^1∫_x^1 t/(1+t²) dt dx.',
            'Reversing order gives −∫_0^1 t²/(1+t²)dt=π/4−1.'],
            line_integral=m.add(m.div(pi,q(4)),q(-1)),defined='improper value at the common singular endpoint')
    return spatial_circulation_chart(task,request,parsed,partial,result)


def spatial_circulation_chart(task,request,parsed,partial,result):
    from cartesian_fields import coordinate_curl
    body=task['curve'];orient=task.get('orientation');axes=list('xyz');t=('v','t');pi=m.PI
    if task.get('suggested_method') is not None:
        raise Unsupported('A spatial curve may have an additional printed method')
    circle=re.fullmatch(r'x\^2\+y\^2\+z\^2=([A-Za-z]\w*)\^2,y=x\*tan\(([A-Za-z]\w*)\);0<\2<pi',body)
    if circle and orient=='counterclockwise as seen from positive x':
        a,alpha=circle.groups();A,T=('s',a),('s',alpha)
        P=parsed(axes)
        if any(domain_conditions(f,True) for f in P):raise Unsupported('The field must be smooth on the full disk')
        curl=coordinate_curl(lambda f,x:partial(f,x,axes),P)
        if any(m.contains(c,('s',x)) for x in axes for c in curl):
            raise Unsupported('The planar disk route requires constant curl')
        normal=[('sin',T),m.neg(('cos',T)),ZERO]
        value=m.simplify(m.mul(m.mul(pi,m.power(A,2)),m.dot(curl,normal)))
        return result('oriented_field_pullback',[
            'The plane normal is (sin(alpha),−cos(alpha),0) with positive x component on the original angle interval.',
            'Stokes pairs the checked constant curl with this unit normal and the full disk area.',
            'The literal tangent requires alpha≠π/2. A continued plane at alpha=π/2 must be stated separately.'],
            line_integral=value,normal=normal,curl=curl,domain=f'0<{alpha}<pi, {alpha}!=pi/2')
    viviani=re.fullmatch(r'Viviani x\^2\+y\^2\+z\^2=([A-Za-z]\w*)\^2,x\^2\+y\^2=\1\*x,z>=0,\1>0',body)
    octant=body=='boundary of unit sphere patch x,y,z>=0'
    if viviani and orient=='counterclockwise as seen from x>a on Ox':
        a=viviani[1]
        if a not in ('a',):raise Unsupported('The viewing point was specified using a different radius')
        A=('s',a);half=m.div(A,q(2));sn,cs=('sin',t),('cos',t)
        paths=[([m.mul(half,m.add(ONE,cs)),m.mul(half,sn),m.mul(A,('sin',m.div(t,q(2))))],ZERO,m.mul(q(2),pi))]
        params=[a];coverage='The cylinder gives a single full circle in xy; the nonnegative square root on the sphere is a sin(t/2). In yz the loop is counterclockwise.'
    elif octant and orient=='outward side remains to the left':
        paths=[(p,ZERO,m.div(pi,q(2))) for p in [[('cos',t),('sin',t),ZERO],[ZERO,('cos',t),('sin',t)],[('sin',t),ZERO,('cos',t)]]]
        params=[];coverage='The positively oriented spherical octant boundary consists of the three cyclic quarter circles, each used once.'
    else:raise Unsupported('No complete spatial traversal matches the original curve and orientation')
    field=parsed(axes,params);pieces=[];total=ZERO
    for i,(path,a,b) in enumerate(paths):
        if any(domain_conditions(f,True) for f in field):raise Unsupported('The field is not globally smooth in this oriented chart')
        vel=[freeze(request('oriented velocity '+str((i,k)),dict(kind='differentiate',function=source(f),variable='t',
            parameters=params,stated_conditions=[p+'>0' for p in params],method_requirement='table_and_rules'))['value'])
             for k,f in enumerate(path)]
        replaced=[m.substitute(f,dict(zip([('s',s) for s in axes],path))) for f in field]
        witness,value=curve_chart_moment(m.dot(vel,replaced),'t',params,[p+'>0' for p in params],a,b,request,'oriented component sum')
        pieces.append(dict(path=path,velocity=vel,pullback=witness));total=m.add(total,value)
    return result('oriented_field_pullback',[coverage,'Restrict the field and integrate its product with the signed tangent on every arc.'],
                  line_integral=m.simplify(total),pieces=pieces)


def boundary_measure_chart(task,request):
    """Use the appropriate measure on an oriented ray, rolling locus or cylinder strip."""
    from cartesian_fields import vector_source
    kind=task['kind'];want=task['requested_output'];pi=m.PI
    def proved(name,argument,**values):
        return dict(theorem='method.'+name,argument=argument),values
    if kind=='rolling_circle_area':
        vector_source(task,{'geometry','special','requested_output'},('Найти охваченную площадь и разобрать указанный частный случай.',))
        choices={'externally rolling (epicycloid); R/r=n, integer n>=1':('r=R, cardioid',1),
                 'internally rolling (hypocycloid); R/r=n, integer n>=2':('r=R/4, astroid',-1)}
        if (goal:=choices.get(task['geometry'])) is None or want!=['area','special_case'] or task['special']!=goal[0]:
            raise Unsupported('The radius ratio and requested special rolling curve must match')
        special,sgn=goal;R,r=('s','R'),('s','r');A=m.add(R,m.mul(q(sgn),r))
        area=m.simplify(m.mul(pi,m.mul(A,m.add(R,m.mul(q(2*sgn),r)))))
        steps=['With n=R/r and uniform rolling, the complex position is '+(
            '(R+r)e^{it}−r e^{i(n+1)t}' if sgn==1 else '(R−r)e^{it}+r e^{−i(n−1)t}')+'.',
               'In a nondegenerate case, the numerator of the derivative of its polar angle is a positive constant times 1−cos(nt). The angle winds once since the circular factor after e^{it} avoids zero and winds zero times.',
               'In 1/2 Im integral of conjugate(z) z\' dt, the cross terms contain a full nonzero harmonic and integrate to zero. The constant modes give the area.']
        if sgn==-1:steps.append('At n=2 the path is a line segment and encloses zero area.')
        sub={'R':r} if sgn==1 else {'r':m.div(R,q(4))}
        return proved('boundary_radial_area',steps,area=area,
                      special_case=dict(source=special,area=m.simplify(m.substitute(area,{('s',s):a for s,a in sub.items()}))))
    if kind=='surface_area':
        vector_source(task,{'surface','requested_output'},('Вычислить площадь части цилиндрической поверхности.',))
        p=re.fullmatch(r'x\^2\+y\^2=([A-Za-z]\w*)\*x inside x\^2\+y\^2\+z\^2=\1\^2',task['surface'])
        if want!=['surface_area'] or not p:raise Unsupported('Bind both cylindrical and spherical boundaries')
        A=('s',p[1]);t=('v','t');g=m.mul(m.power(A,2),('sin',m.div(t,q(2))))
        # The angular metric is |a|/2, the vertical height is 2|a|sin(t/2).
        proof,value=curve_chart_moment(g,'t',[p[1]],[],ZERO,m.mul(q(2),pi),request,'one complete interval of cylindrical strips')
        return proved('curve_chart_moments',[
            'The base circle has center (a/2,0), radius |a|/2 and one complete angular turn.',
            'On its points x²+y²=a²(1+cos(t))/2, the vertical height allowed by the sphere is 2|a|sin(t/2).',
            'The angular arc speed times height gives the surface density |a|²sin(t/2).'],surface_area=value,moment=proof)
    vector_source(task,{'curve','suggested_substitution','method_requirement','requested_output'},
                  ('Вычислить площадь с помощью криволинейных интегралов.',))
    if want!=['area','boundary_evaluation'] or task['method_requirement']!='boundary_area_integral':
        raise Unsupported('The boundary integral must accompany the area')
    curve=task['curve'];hint=task.get('suggested_substitution');name=r'([A-Za-z_]\w*)'
    steps=['For positive traversal use the exact Green boundary density (x dy−y dx)/2.']
    def area(value,parameterization,integral,why):
        return proved('boundary_radial_area',[*steps,why],area=value,
                      boundary_evaluation=dict(chart=parameterization,integral=integral))
    if (match:=re.fullmatch(fr'lemniscate \(x\^2\+y\^2\)\^2={name}\^2\*\(x\^2-y\^2\)',curve)) and (
            hint in (None,'y=x*tan(phi)')):
        A=('s',match[1]);value=m.power(A,2)
        return area(value,'r²=a² cos(2 theta) on both admissible half-turn lobes','2 * 1/2 * integral[-pi/4,pi/4] a² cos(2 theta) d theta',
                    'The real positive radii occur when cos(2 theta)≥0. Integrate on the two disjoint lobes counted once each.')
    if hint not in (None,'x/a=cos(phi)^(2/n),y/b=sin(phi)^(2/n)'):
        raise Unsupported('The stated auxiliary transformation was not identified')
    if curve=='x^3+y^3=x^2+y^2 and coordinate axes':
        answer=m.add(q(1,3),m.div(m.mul(q(4),pi),m.mul(q(9),('sqrt',q(3)))))
        return area(answer,'polar ray r=1/(cos³(theta)+sin³(theta)), t=tan(theta)',
                    '1/2 * integral[0,inf] (1+t²)²/(1+t³)² dt',
                    'Only the first-quadrant segment joins the two nonzero axis intersections in a bounded region. Its axis segments contribute zero. Replace t by 1/t in the quartic term and use beta moments after t³.')
    if mshape:=re.fullmatch(fr'\(x\+y\)\^\({name}\+{name}\+1\)={name}\*x\^\1\*y\^\2;\3,\1,\2>0',curve):
        n,mname,a=mshape.groups()
        return area(f'{a}^2*Beta(2*{n}+1,2*{mname}+1)/2','s=x+y, t=x/(x+y), s=a*t^n*(1−t)^m',
                    f'{a}^2/2 * integral[0,1] t^(2*{n})*(1−t)^(2*{mname}) dt',
                    'The bounded positive loop has 0<t<1 and positive s with zero endpoints. In these coordinates x dy−y dx=−s² dt, so positive traversal reverses t.')
    normalized=fr'\(x/{name}\)\^{name}\+\(y/{name}\)\^\2='
    if mshape:=re.fullmatch(normalized+r'1 and coordinate axes;\1,\3,\2>0',curve):
        a,n,b=mshape.groups()
        return area(f'{a}*{b}*Gamma(1+1/{n})^2/Gamma(1+2/{n})','x=a cos(theta)^(2/n), y=b sin(theta)^(2/n)',
                    '1/2 * integral[0,pi/2] (x*y\'−y*x\') d theta',
                    'The two axes contribute zero. On the positive arc x decreases and y increases, so it is positively oriented. Substitute sin²(theta) in the two symmetric terms.')
    if mshape:=re.fullmatch(normalized+r'\(x/\1\)\^\(\2-1\)\+\(y/\3\)\^\(\2-1\) and coordinate axes;\1,\3>0,\2>1',curve):
        a,n,b=mshape.groups()
        return area(f'{a}*{b}/{n}*(Beta(1/{n},2-1/{n})+1)','normalized ray t=(y/b)/(x/a), U=x/a=(1+t^(n-1))/(1+t^n)',
                    'a*b/2 * integral[0,inf] ((1+t^(n-1))/(1+t^n))² dt',
                    'The positive radius is unique per ray. On this positively oriented graph the area form is a*b*U² dt/2. Inversion of t identifies the extreme terms, and t^n is the beta substitution.')
    raise Unsupported('No ordered radial boundary chart agrees with the original powered equation')


def section_parameters(task,texts,coordinates):
    """Read the printed positive-parameter convention carried by both input forms."""
    provenance=task.get('source',{})
    convention=provenance.get('section_convention')
    if (set(provenance)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','section_convention'} or
            convention not in (None,*POSITIVE_SECTION)):
        raise Unsupported('The printed geometric conditions have additional obligations')
    if 'parameters' in task:
        names=list(task['parameters'])
    elif convention:
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join(texts)))
                     -set(coordinates)-m.FUNCTIONS-set(m.ALIASES)-{'e','pi','inf','integral'})
    else:names=[]
    if len(names)!=len(set(names)) or set(names)&set(coordinates):
        raise Unsupported('A parameter collides with a coordinate')
    return names,[name+'>0' for name in names] if convention else []


def source_parametric_area(task,request):
    """Place a proved simple arc or closed parametrization in the oriented area theorem."""
    from integrals import harmonic_modes
    from plane_domains import metric_sign
    from polynomial import rf,NotRational,Undefined
    from graphs import rational_roots
    if (set(task)-{'id','kind','source','coordinate_system','equations','parameters','stated_conditions','requested_output'}
            or task.get('coordinate_system')!='parametric' or task.get('requested_output')!=['bounded_area']):
        raise Unsupported('The source has an additional parametric area requirement')
    equations=task['equations']
    if len(equations) not in (2,3) or not all(eq.startswith(c+'=') for eq,c in zip(equations,('x','y'))):
        raise Unsupported('Expected a planar parameter map')
    conditions=task.get('stated_conditions',[]);v='t';u=('v',v)
    spans=[s for s in conditions if re.fullmatch(r'([^<>=]+)<=t<=([^<>=]+)',s)]
    facts=[s for s in conditions if s not in spans]
    positive=re.compile(r'([A-Za-z_]\w*)>0')
    parameters,standard=section_parameters(task,[*equations,*conditions],('x','y',v))
    additional=[s for s in facts if (p:=positive.fullmatch(s)) and p[1] in parameters]
    assumptions=list(dict.fromkeys(standard+additional))
    ctx=m.context(dict(variable=v,parameters=parameters,parameter_conditions=assumptions))
    retained=[]
    for fact in facts:
        if fact in additional:continue
        tokens=fact.split('=')
        if len(tokens)!=2 or not all(m.constant_defined(m.parse(s,None,parameters),ctx) for s in tokens):
            raise Unsupported('The printed restriction is not recognized')
        retained.append(fact)  # The formula is derived on a superset of these fixed parameter values.
    X0,Y0=[m.parse(e[2:],v,parameters) for e in equations[:2]]
    # A sinusoidal graph can have two ordinates above a common x. The two
    # branches are related by t -> -t and can both be integrated in 0<t<pi.
    if not spans and len(equations)==2 and Y0[0]=='div' and not retained:
        cosine=('cos',u);sine=('sin',u)
        amplitude=m.simplify(m.substitute(X0,{cosine:ONE}))
        top,bottom=Y0[1:]
        coef=m.simplify(m.substitute(top,{sine:ONE}))
        shift=m.simplify(m.substitute(bottom,{sine:ZERO}))
        level=m.add(shift,q(-1))
        if (same_value(X0,m.mul(amplitude,cosine)) and same_value(top,m.mul(coef,m.power(sine,2)))
                and same_value(bottom,m.add(shift,sine))
                and not domain_conditions(X0) and len(domain_conditions(Y0))==1
                and all(m.constant_defined(z,ctx) and m.sign(z,ctx)==1 for z in (amplitude,coef,level))):
            square=m.power(shift,2);w=('v','w')
            rational=m.div(ONE,m.add(square,m.mul(m.add(square,q(-1)),m.power(w,2))))
            goal=dict(kind='improper_integral',variable='w',integrand=source(rational),parameters=parameters,
                      stated_conditions=assumptions,lower='0',upper='+inf',requested_output=['exact_integral'])
            val=request('integrate the half-angle reciprocal kernel on its regular positive ray',goal)['value']
            if val.get('convergence')!='convergent' or 'value' not in val:
                raise Unsupported('The reciprocal squared-sine kernel needs a finite integral')
            kernel=m.mul(q(2),freeze(val['value']))
            # (sin t)^4/(shift²-sin² t)=shift^4/(shift²-sin² t)-shift²-sin² t.
            value=m.mul(m.mul(q(2),m.mul(coef,amplitude)),
                        m.add(m.mul(m.power(square,2),kernel),m.neg(m.mul(m.PI,m.add(square,q(1,2))))))
            return dict(partition=dict(argument='two_sinusoidal_vertical_branches',positive_denominator_floor=level,
                                       branches='For 0<t<pi the reflected t has the same x and strictly greater y.',
                                       normalized_kernel=rational),sections=[dict(bounds=(ZERO,m.PI),density=Y0,integral=value)],
                        measure_scale=ONE),dict(area=value)
    if any(not known_guard(g,ctx) for term in (X0,Y0) for g in domain_conditions(term)):
        raise Unsupported('The original coordinate map is not defined on the whole arc')

    def on_interval(term,a,b):
        if any(not known_guard(g,ctx) for g in domain_conditions(term)):
            raise Unsupported('The arc has an unresolved domain')
        return freeze(request('differentiate a source parametrization coordinate',
            dict(kind='differentiate',variable=v,function=source(term),parameters=parameters,stated_conditions=assumptions,
                 method_requirement='table_and_rules'))['value'])

    def ordinate(term,point):return m.simplify(m.substitute(term,{u:point}))
    def integral(expr,a,b):
        goal=dict(kind='iterated_integral',integrand=source(expr),parameters=parameters,stated_conditions=assumptions,
                  integration_order=[dict(variable=v,lower=source(a),upper=source(b))],requested_output=['exact_integral'])
        return freeze(request('integrate the positively oriented area density',goal)['value'])

    if len(spans)==1 and len(equations)==3 and equations[2]=='y=0':
        a,b=[m.parse(s,None,parameters) for s in re.fullmatch(r'([^<>=]+)<=t<=([^<>=]+)',spans[0]).groups()]
        if not all(m.constant_defined(z,ctx) for z in (a,b)) or m.sign(m.add(b,m.neg(a)),ctx)!=1:
            raise Unsupported('The original parameter interval must have positive length')
        vx=on_interval(X0,a,b)
        sx=metric_sign(vx,v,a,b,ctx);sy=metric_sign(Y0,v,a,b,ctx)
        mid=m.div(m.add(a,b),q(2))
        if (sx not in (-1,1) or sy not in (-1,1) or m.sign(ordinate(vx,mid),ctx)!=sx or
                m.sign(ordinate(Y0,mid),ctx)!=sy or any(ordinate(Y0,p)!=ZERO for p in (a,b))):
            raise Unsupported('No single monotone graph above or below its closing axis was proved')
        density=m.mul(q(sx*sy),m.mul(Y0,vx))
        proof=dict(argument='monotone_graph_and_axis',coordinate_derivative=vx,monotone_sign=sx,height_sign=sy,
                   full_arc='The analytic derivative has a fixed weak sign and is nonzero at the midpoint. It cannot vanish on any open subinterval.')
    elif len(equations)==2 and not spans:
        a,b=ZERO,m.mul(q(2),m.PI)
        def monomial(term,wave):
            num,den=m.rational_form(term);atom=(wave,u)
            if len(num)!=1:return None
            mon,coef=next(iter(num.items()))
            order=dict(mon).get(atom,0)
            const={tuple(x for x in mon if x[0]!=atom):coef}
            factor=m.div(m.poly_expr(const),m.poly_expr(den))
            if order%2 and m.constant_defined(factor,ctx) and m.sign(factor,ctx)==1:return order,factor
        graph_powers=[monomial(z,w) for z,w in zip((X0,Y0),('cos','sin'))]
        contour_scale=ONE
        if all(graph_powers):
            proof=dict(argument='injective_odd_coordinate_powers',powers=graph_powers)
            contour_scale=m.mul(*(z[1] for z in graph_powers))
            X0,Y0=[m.power((wave,u),z[0]) for wave,z in zip(('cos','sin'),graph_powers)]
        else:
            try:
                p,d=rf(X0,v);rel,rel_d=rf(m.add(Y0,m.neg(m.mul(u,X0))),v)
            except (NotRational,Undefined):p=()
            if p and len(d)==1 and rel==(0,) and rel_d==(1,):
                roots=sorted({z.a for z in rational_roots(p) if not z.b})
                if len(roots)!=2 or any(z.b for z in rational_roots(p)):
                    raise Unsupported('Exactly two source zeroes with a simple slope arc are required')
                a,b=map(q,roots)
                proof=dict(argument='injective_slope_between_consecutive_axis_returns',endpoints=(a,b),
                           inverse='y/x equals t at each nonorigin point; the whole original trace has no other pair of equal parameters')
                density=m.div(m.power(X0,2),q(2));value=integral(density,a,b)
                return dict(partition=proof,sections=[dict(bounds=(a,b),density=density,integral=value)],
                            measure_scale=ONE,retained_conditions=facts),dict(area=value)
            # For z=c1*w+c2*w^2 on the unit circle, equal values at distinct w require
            # |c1|=|c2|*|w1+w2|<2|c2|. This also permits a single stationary cusp.
            spec=lambda e:dict(kind='integrate',variable=v,integrand=source(e),parameters=parameters)
            hx,_,_=harmonic_modes(spec(X0),assumptions);hy,_,_=harmonic_modes(spec(Y0),assumptions)
            modes={}
            for key in sorted(set(hx)|set(hy),key=repr):
                rowx=hx.get(key,[(ZERO,ZERO)]);rowy=hy.get(key,[(ZERO,ZERO)])
                if key[0]!=ZERO or len(rowx)!=1 or len(rowy)!=1:
                    raise Unsupported('A pure finite Fourier contour is required')
                x0,x1=rowx[0];y0,y1=rowy[0]
                z=(m.add(x0,m.neg(y1)),m.add(x1,y0))
                if z!=(ZERO,ZERO):modes[key[1]]=z
            if set(modes)-{ZERO,ONE,q(2)} or ONE not in modes:
                raise Unsupported('No injective closed contour chart is proved')
            norm=lambda k:m.add(*(m.power(z,2) for z in modes.get(k,(ZERO,ZERO))))
            margin=m.add(norm(ONE),m.neg(m.mul(q(4),norm(q(2)))))
            if not m.known_nonnegative(margin,ctx) or m.sign(norm(ONE),ctx)!=1:
                raise Unsupported('The first Fourier mode does not certify injectivity')
            proof=dict(argument='injective_quadratic_unit_circle_image',modes=list(modes.items()),squared_margin=margin)
        vx,vy=[on_interval(f,a,b) for f in (X0,Y0)]
        density=m.div(m.add(m.mul(X0,vy),m.neg(m.mul(Y0,vx))),q(2))
        proof['positive_diagonal_area_scale']=contour_scale
    else:raise Unsupported('No complete simple boundary and closing arc have been proved')
    value=integral(density,a,b)
    sign=m.sign(value,ctx)
    if sign not in (-1,1):raise Unsupported('The chosen boundary has no proved orientation and nonzero area')
    scale=m.mul(q(sign),proof.get('positive_diagonal_area_scale',ONE))
    plan=dict(partition={**proof,'orientation':sign},sections=[dict(bounds=(a,b),density=density,integral=value)],
              measure_scale=scale,retained_conditions=facts)
    return plan,dict(area=m.mul(scale,value))


def source_measure_moments(task,library,request):
    """Construct one-dimensional moment integrals from the source measure and its orientation."""
    if (not library.data.get('source_measure_moments') or
            set(task)-{'id','kind','source','statement','requested_output'}):
        raise Unsupported('The original moment request is not recognized')
    statement=task['statement'];wanted=task['requested_output']
    if task.get('kind')!='geometric_moments':
        raise Unsupported('Expected a geometric moment or centroid')
    section_parameters(task,[],())
    name=r'([A-Za-z_]\w*)'
    def match(pattern):
        return re.fullmatch(pattern,statement)
    theta,x,u=(('v',k) for k in ('phi','x','u'))
    shape=None;computations=[];constants={}
    def task_model(kind,measure,params,cases,known=None,post=None):
        nonlocal shape,computations,constants,finish,parameters
        shape=dict(kind=kind,measure=measure,proof_of_coverage=(
            'The stated geometry is parameterized or sliced once, with symmetric pieces counted explicitly.'))
        computations=cases;parameters=list(params)
        constants=known or {};finish=post
    def symbols(g):return [('s',s) for s in g]
    def norm(names):
        return lambda values,ctx:{'centroid_coordinates':tuple(m.div(values[k],values['mass']) for k in names)}
    def polynomial_column(width,xcoord,lo,hi):
        return [('mass','x',lo,hi,width),('x','x',lo,hi,m.mul(xcoord,width))]
    finish=None;parameters=[]

    if (g:=match(fr'Дуга полуокружности радиуса {name}, ось — диаметр через концы дуги\.')) and wanted==['static_moment','moment_of_inertia']:
        R,=symbols(g.groups());distance=m.mul(R,('sin',theta))
        tasks=[(key,'phi',ZERO,m.PI,m.mul(R,m.power(distance,d))) for key,d in (('static_moment',1),('moment_of_inertia',2))]
        task_model('semicircular_arc','R dφ with signed normal chosen toward the arc',g.groups(),tasks)
    elif (g:=match(fr'Дуга y²=2{name}x, 0≤x≤\1/2, относительно x=\1/2\.')) and wanted==['static_moment']:
        P,=symbols(g.groups());t=('v','u');s=('sinh',t);h=('cosh',t)
        # y=P sinh u is strictly increasing and x=P sinh²u/2.
        hi=('ln',m.add(ONE,('sqrt',q(2))));density=m.mul(m.power(P,2),m.mul(m.add(ONE,m.neg(m.power(s,2))),m.power(h,2)))
        task_model('parabolic_arc','2P cosh²(u) du for both halves',g.groups(),[('static_moment','u',ZERO,hi,density)])
    elif (g:=match(fr'Однородный треугольник с основанием {name} и высотой {name}, ρ=1; моменты относительно основания\.')) and wanted==['static_moment','moment_of_inertia']:
        B,H=symbols(g.groups());width=m.mul(m.mul(B,H),m.add(ONE,m.neg(x)))
        forms=[(key,'x',ZERO,ONE,m.mul(width,m.power(m.mul(x,H),d))) for key,d in (('static_moment',1),('moment_of_inertia',2))]
        task_model('triangle_plate','parallel section width b(1-x/h)',g.groups(),forms)
    elif (g:=match(fr'Параболический сегмент {name}y=(.+?), \1>0, y=0; моменты относительно Ox,Oy и радиусы r_x,r_y по I_x=S r_x²,I_y=S r_y²\.')) and wanted==['inertia_about_x','inertia_about_y','gyration_radii']:
        P=g[1];a,=symbols((P,))
        notation=g[2].replace('²','^2').replace('−','-')
        notation=re.sub(fr'(?<=\d)(?={re.escape(P)}|x)','*',notation)
        body=m.parse(re.sub(fr'(?<={re.escape(P)})x\b','*x',notation),'x',[P])
        ctx=m.context(dict(variable='x',parameters=[P],parameter_conditions=[P+'>0']))
        zero=m.simplify(m.substitute(body,{x:ZERO}));B=m.div(m.add(m.substitute(body,{x:ONE}),m.neg(m.substitute(body,{x:q(-1)}))),q(2))
        C=m.add(m.substitute(body,{x:ONE}),m.neg(B))
        if zero!=ZERO or m.sign(B,ctx)!=1 or m.sign(C,ctx)!=-1 or not same_value(body,m.mul(x,m.add(B,m.mul(C,x)))):
            raise Unsupported('The original closed positive parabolic section was not proved')
        hi=m.div(m.neg(B),C);coord=m.mul(x,hi);height=m.simplify(m.div(m.substitute(body,{x:coord}),a))
        forms=[('mass','x',ZERO,ONE,m.mul(hi,height)),('inertia_about_x','x',ZERO,ONE,m.mul(hi,m.div(m.power(height,3),q(3)))),
               ('inertia_about_y','x',ZERO,ONE,m.mul(hi,m.mul(m.power(coord,2),height)))]
        def radii(vals,ctx):
            return dict(inertia_about_x=vals['inertia_about_x'],inertia_about_y=vals['inertia_about_y'],
                        gyration_radii=[m.simplify(('sqrt',m.div(vals[k],vals['mass']))) for k in ('inertia_about_x','inertia_about_y')])
        task_model('parabolic_plate','vertical columns between y=0 and the positive quadratic graph',(P,),forms,post=radii)
    elif (g:=match(fr'Однородная эллиптическая пластинка с полуосями {name},{name}, ρ=1; моменты относительно главных осей\.')) and wanted==['principal_moments']:
        names=g.groups();axes=symbols(names);parts=[]
        for v in ('y','x'):
            qd=dict(left=source(m.add(*(m.power(m.div(('s',k),p),2) for k,p in zip(('x','y'),axes)))),right='1')
            child=dict(kind='ellipsoid_moment',integrand=v+'^2',variables=['x','y'],parameters=list(names),
                       stated_conditions=[s+'>0' for s in names],quadratic_region=qd,requested_output=['exact_integral'])
            val=request('quadratic moment on the stated elliptical disk',child)['value']
            if val.get('defined') is not True:raise Unsupported('The elliptical plate must have positive measure')
            parts.append(freeze(val['value']))
        return dict(theorem='method.source_measure_moments',measure='affine image of a disk with its full Jacobian',
                    coordinates=('x','y'),shapes=axes),dict(principal_moments=parts)
    elif (g:=match(fr'Однородный прямой круговой конус радиуса {name} и высоты {name}, ρ=1, относительно плоскости основания\.')) and wanted==['static_moment','moment_of_inertia']:
        R,H=symbols(g.groups());area=m.mul(m.mul(m.PI,H),m.power(m.mul(R,m.add(ONE,m.neg(x))),2))
        forms=[(key,'x',ZERO,ONE,m.mul(area,m.power(m.mul(x,H),d))) for key,d in (('static_moment',1),('moment_of_inertia',2))]
        task_model('cone','circular sections with linearly decreasing radius',g.groups(),forms)
    elif (g:=match(fr'Однородный шар радиуса {name}, массы {name}, относительно диаметра\.')) and wanted==['moment_of_inertia']:
        R,M=symbols(g.groups());square=m.add(m.power(R,2),m.neg(m.power(x,2)))
        # In a perpendicular disk of radius s, integrate r² (2πr dr), giving πs⁴/2.
        forms=[('mass','x',m.neg(R),R,m.mul(m.PI,square)),('unit_inertia','x',m.neg(R),R,m.mul(m.div(m.PI,q(2)),m.power(square,2)))]
        task_model('sphere_solid','perpendicular disks, uniform center density fixed by total mass',g.groups(),forms,
                   post=lambda v,ctx:dict(moment_of_inertia=m.mul(M,m.div(v['unit_inertia'],v['mass']))))
    elif (g:=match(fr'Круговая дуга x={name} cosφ,y=\1 sinφ, \|φ\|≤([A-Za-z_]\w*|α)≤π\.')) and wanted==['centroid_coordinates']:
        names=(g[1],'alpha' if g[2]=='α' else g[2]);R,A=symbols(names);forms=[('mass','phi',m.neg(A),A,R),
                ('x','phi',m.neg(A),A,m.mul(m.power(R,2),('cos',theta)))]
        task_model('symmetric_circular_arc','constant speed R, y-odd symmetry',names,forms,known={'y':ZERO},post=norm(('x','y')))
        shape['original_angle_constraint']=source(A)+'<=pi'
    elif (g:=match(fr'Область между {name}x=y², \1y=x², \1>0\.')) and wanted==['centroid_coordinates']:
        A,=symbols(g.groups());low=m.mul(A,m.power(u,4));high=m.mul(A,u);coord=m.mul(A,m.power(u,2));jac=m.mul(q(2),m.mul(A,u))
        span=m.add(high,m.neg(low))
        forms=[('mass','u',ZERO,ONE,m.mul(jac,span)),('x','u',ZERO,ONE,m.mul(jac,m.mul(coord,span))),
               ('y','u',ZERO,ONE,m.mul(jac,m.div(m.add(m.power(high,2),m.neg(m.power(low,2))),q(2))))]
        task_model('paired_parabolas','nonnegative intersection x=a,y=a. Both original equations force x,y≥0. '
                   'Use x=a*u² so the ordered vertical limits become a*u⁴ and a*u for 0≤u≤1.',g.groups(),forms,post=norm(('x','y')))
    elif (g:=match(fr'Область x²/{name}²\+y²/{name}²≤1, 0≤x≤\1, 0≤y≤\2\.')) and wanted==['centroid_coordinates']:
        A,B=symbols(g.groups());area=m.mul(m.mul(A,B),m.div(m.PI,q(4)))
        forms=[('x','phi',ZERO,m.div(m.PI,q(2)),m.mul(m.div(m.mul(m.power(A,2),B),q(3)),('cos',theta))),
               ('y','phi',ZERO,m.div(m.PI,q(2)),m.mul(m.div(m.mul(A,m.power(B,2)),q(3)),('sin',theta)))]
        task_model('quarter_ellipse','positive diagonal image of one disk quadrant, after radial r and r² moments',g.groups(),forms,
                   known={'mass':area},post=norm(('x','y')))
    elif (g:=match(fr'Однородный полушар радиуса {name}\.')) and wanted==['centroid']:
        R,=symbols(g.groups());area=m.mul(m.PI,m.add(m.power(R,2),m.neg(m.power(x,2))))
        forms=[('mass','x',ZERO,R,area),('z','x',ZERO,R,m.mul(x,area))]
        task_model('half_ball','circular cross section of area π(R²-z²) and two axial symmetries',g.groups(),forms,
                   known={'x':ZERO,'y':ZERO},post=lambda v,c:{'centroid':norm(('x','y','z'))(v,c)['centroid_coordinates']})
    elif (g:=match(fr'Область внутри r={name}\(1\+cosφ\)\.')) and wanted==['centroid_coordinates']:
        R,=symbols(g.groups());radius=m.mul(R,m.add(ONE,('cos',theta)));top=m.mul(q(2),m.PI)
        forms=[('mass','phi',ZERO,top,m.div(m.power(radius,2),q(2))),
               ('x','phi',ZERO,top,m.mul(('cos',theta),m.div(m.power(radius,3),q(3))))]
        task_model('nonnegative_radial_region','exact polar radial measure r dr dφ, unique full turn, reflection cancels y',g.groups(),forms,
                   known={'y':ZERO},post=norm(('x','y')))
    elif (g:=match(fr'Область под первой аркой циклоиды x={name}\(t−sin t\), y=\1\(1−cos t\), 0≤t≤2π, над Ox\.')) and wanted==['centroid_coordinates']:
        R,=symbols(g.groups());width=m.mul(R,m.add(ONE,m.neg(('cos',u))));upper=m.mul(q(2),m.PI)
        forms=[('mass','u',ZERO,upper,m.power(width,2)),('y','u',ZERO,upper,m.div(m.power(width,3),q(2)))]
        def center(v,ctx):return dict(centroid_coordinates=(m.mul(m.PI,R),m.div(v['y'],v['mass'])))
        task_model('cycloidal_strip','vertical height=a(1−cos t). The x Jacobian is the same, strictly positive inside. '
                    'Reflection t↦2π−t gives x(t)+x(2π−t)=2πa.',g.groups(),forms,post=center)
    elif (g:=match(fr'Тело вращения 0≤x≤{name}, y²≤2{name}x вокруг Ox\.')) and wanted==['centroid_coordinates']:
        A,P=symbols(g.groups());area=m.mul(m.mul(q(2),m.PI),m.mul(P,x))
        task_model('axial_parabolic_volume','circular sections of area 2πpx, counted once by their distinct axial positions',
                   g.groups(),polynomial_column(area,x,ZERO,A),known={'y':ZERO,'z':ZERO},post=norm(('x','y','z')))
    elif (g:=match(fr'Полусферическая поверхность x²\+y²\+z²={name}², z≥0\.')) and wanted==['centroid_coordinates']:
        R,=symbols(g.groups());density=m.mul(m.mul(q(2),m.PI),R)
        task_model('half_sphere_surface','spherical zones 2πR dz. Circumference 2πsqrt(R²-z²) is multiplied by meridian factor '
                   'R/sqrt(R²-z²) on each open latitude. The endpoint limit is finite.',g.groups(),
                   [('mass','x',ZERO,R,density),('z','x',ZERO,R,m.mul(x,density))],known={'x':ZERO,'y':ZERO},post=norm(('x','y','z')))
    else:raise Unsupported('The source measure, axis or branch geometry is not recognized')

    if len(set(parameters))!=len(parameters) or set(parameters)&{row[1] for row in computations}:
        raise Unsupported('Positive geometric dimensions must have distinct coordinate-free names')
    assumptions=[n+'>0' for n in parameters];values=constants.copy();proof=[]
    ctx=m.context(dict(variable='__moment',parameters=parameters,parameter_conditions=assumptions))
    for label,var,a,b,integrand in computations:
        child=dict(kind='iterated_integral',integrand=source(integrand),parameters=parameters,stated_conditions=assumptions,
                   integration_order=[dict(variable=var,lower=source(a),upper=source(b))],requested_output=['exact_integral'])
        values[label]=freeze(request('moment integral '+label,child)['value'])
        proof.append(dict(quantity=label,bounds=(a,b),density=integrand,value=values[label]))
    if finish and m.sign(values['mass'],ctx)!=1:
        raise Unsupported('A positive total measure is required before normalization')
    value=values if finish is None else finish(values,ctx)
    return dict(theorem='method.source_measure_moments',model=shape,computations=proof,parameter_domain=assumptions,
                symmetry_values=constants,normalizing_measure=values.get('mass')),value


def source_polar_metric(task,request):
    """Use the polar metric directly, including an angle defined by accumulation."""
    from plane_domains import metric_square_root
    if (task['kind']!='curve_arc_length' or task.get('coordinate_system')!='polar'
            or task.get('requested_output')!=['arc_length']
            or set(task)-{'id','kind','source','coordinate_system','equations','parameters','stated_conditions','requested_output'}):
        return None
    es=task['equations'];conditions=task.get('stated_conditions',[])
    pos=[c for c in conditions if re.fullmatch(r'[A-Za-z_]\w*>0',c) and c[:-2] in task.get('parameters',[])]
    conditions=[c for c in conditions if c not in pos]
    if len(conditions)!=1:return None
    angle=next((s[4:] for s in es if s.startswith('phi=')),None)
    if angle is None:return None
    accumulated=re.fullmatch(r'integral\((.*),([A-Za-z_]\w*),0,r\)',angle)
    terminal=re.fullmatch(r'0<=t<=([^<>=]+)<pi',conditions[0])
    radial=next((s[2:] for s in es if s.startswith('r=')),None)
    if accumulated and len(es)==1:
        upper=re.fullmatch(r'0<=r<=([^<>=]+)',conditions[0])
        if not upper:return None
        expression,dummy=accumulated.groups()
        p,assumptions=section_parameters(task,[*es,*conditions],('r','phi',dummy))
        assumptions=list(dict.fromkeys(assumptions+pos))
        if dummy in p or dummy=='r':raise Unsupported('The accumulated angle must bind an independent dummy variable')
        u=('v',dummy);r=('v','r');end=m.parse(upper[1],None,p)
        ctx=m.context(dict(variable='r',parameters=p,parameter_conditions=assumptions))
        if not m.constant_defined(end,ctx) or m.sign(end,ctx)!=1:
            raise Unsupported('The radius cap must be positive')
        raw=m.parse(expression,dummy,p)
        outer=m.context(dict(variable='__radial',parameters=[*p,dummy],parameter_conditions=[*assumptions,dummy+'>0']))
        if not m.constant_defined(m.substitute(raw,{u:('s',dummy)}),outer):
            raise Unsupported('The angle integrand must be continuous throughout the positive radial interval')
        limit=dict(kind='limit',expression=expression,variable=dummy,parameters=p,parameter_conditions=assumptions,
                   approach=dict(point='0',side='right'))
        at_zero=freeze(request('angular density continuous extension at radius zero',limit)['value'])
        if not isinstance(at_zero,tuple) or not m.constant_defined(at_zero,ctx):raise Unsupported('The radial angle needs a finite integrable lower extension')
        rate=m.substitute(raw,{u:r})
        speed_squared=m.add(ONE,m.power(m.mul(r,rate),2))
        form=dict(angle_integral=raw,angle_derivative=rate,endpoint_density=at_zero,
                  geometry='Each positive radius labels exactly one point. The polar metric is 1+r² φ′(r)².')
        variable='r'
    elif terminal and len(es)==2 and radial is not None:
        p,assumptions=section_parameters(task,[*es,*conditions],('t','r','phi'))
        assumptions=list(dict.fromkeys(assumptions+pos))
        end=m.parse(terminal[1],None,p);v='t';u=('v',v)
        ctx=m.context(dict(variable=v,parameters=p,parameter_conditions=assumptions))
        if not m.constant_defined(end,ctx) or m.sign(end,ctx)!=1:
            raise Unsupported('The printed upper parameter must be positive')
        radius=m.parse(radial,v,p);phase=m.parse(angle,v,p)
        if domain_conditions(radius) or not same_value(radius,m.add(ONE,('cos',u))):
            return None
        tg=('tan',m.div(u,q(2)))
        if not same_value(phase,m.add(u,m.neg(tg))) or any(
            not known_guard((rel,g),ctx) and
            (rel!='nonzero' or g[0]!='cos' or not same_value(g[1],m.div(u,q(2))))
            for rel,g in domain_conditions(phase)):
            return None
        dr=m.neg(('sin',u));dphi=m.div(('cos',u),radius)
        speed_squared=m.add(m.power(dr,2),m.power(m.mul(radius,dphi),2))
        form=dict(radius=radius,angle=phase,derivatives=[dr,dphi],parameter_upper=end,
                  original_bound=conditions[0],geometry='The radius is positive and strictly decreasing for 0<t<pi. '
                  'cos(t/2)>0 uses T<pi, so the original angle is defined. The half-angle identity gives the stated derivative.')
        variable=v
    else:return None
    density,metric=metric_square_root(speed_squared,variable,ZERO,end,ctx)
    child=dict(kind='iterated_integral',integrand=source(density),parameters=p,stated_conditions=assumptions,
               integration_order=[dict(variable=variable,lower='0',upper=source(end))],requested_output=['exact_integral'])
    value=freeze(request('integrate the directly verified polar speed',child)['value'])
    return dict(theorem='method.source_polar_metric',argument='direct_polar_metric',line_integral=[dict(pullback=density)],
                interval=(ZERO,end),original_chart=form,metric_identity=metric),dict(arc_length=value)


def source_homogeneous_area(task,request):
    """Reduce homogeneous plane equations by the prescribed polar or slope chart."""
    requirements=('polar_coordinates','derive_parametric_equations')
    method=task.get('method_requirement');eq=task.get('equations',[])
    fields={'id','kind','source','coordinate_system','equations','parameters','stated_conditions','requested_output','method_requirement'}
    if (set(task)-fields or method not in requirements or task.get('coordinate_system')!='rectangular'
            or task.get('requested_output')!=['bounded_area'] or len(eq)!=1 or eq[0].count('=')!=1):
        raise Unsupported('A compatible homogeneous area and its original chart method are required')
    params,assumptions=section_parameters(task,eq,('x','y'))
    stated=task.get('stated_conditions',[])
    if any(s not in [n+'>0' for n in params] for s in stated):
        raise Unsupported('An additional condition needs its own original-domain proof')
    assumptions=list(dict.fromkeys([*assumptions,*stated]))
    ctx=m.context(dict(variable='__plane',parameters=params,parameter_conditions=assumptions))
    L,R=(m.parse(s,None,['x','y',*params]) for s in eq[0].split('='))
    v=('v','u');φ=('v','phi');cos=('cos',φ);sin=('sin',φ)
    positive=lambda p:m.constant_defined(p,ctx) and m.sign(p,ctx)==1
    def pair(e,exponent):
        return e[0]=='rpow' and m.constant_defined(e[2],ctx) and same_value(e[2],exponent)
    if method==requirements[1] and L[0]=='add' and all(pair(e,q(2,3)) for e in (*L[1:],R)) and (
            set(e[1] for e in L[1:])=={X,Y} and positive(R[1])):
        chart=['x='+source(m.mul(R[1],m.power(('cos',('v','t')),3))),
               'y='+source(m.mul(R[1],m.power(('sin',('v','t')),3)))]
        goal=dict(kind='area_bounded_by_curves',coordinate_system='parametric',equations=chart,parameters=params,
                  stated_conditions=assumptions,requested_output=['bounded_area'])
        val=freeze(request('area of the derived real cube-root parametrization',goal)['value']['area'])
        return dict(partition=dict(argument='real_cube_root_circle_chart',source_equation=eq[0],coordinates=chart,
                                   proof='For real x and y the power 2/3 is the square of the real cube root. The inverse uses these two cube roots.'),
                    sections=[],measure_scale=ONE),dict(area=val)
    if domain_conditions(L) or domain_conditions(R):
        raise Unsupported('An original coordinate restriction may be erased by a homogeneous chart')
    left,right=map(coordinate_terms,(L,R))
    def coefficient(rows,state):return rows.get(state,ZERO)
    circle=m.add(m.power(X,2),m.power(Y,2))
    if method==requirements[0] and set(left)=={(4,0),(2,2),(0,4)} and set(right)=={(1,1)} and (
            same_value(L,m.power(circle,2)) and positive(B:=right[1,1])):
        A=m.div(B,q(2))
        goal=dict(kind='area_bounded_by_curves',coordinate_system='polar',equations=['r^2='+source(m.mul(A,('sin',m.mul(q(2),φ))))],
                  parameters=params,stated_conditions=assumptions,requested_output=['bounded_area'])
        val=freeze(request('positive radial sectors for the original polar rays',goal)['value']['area'])
        return dict(partition=dict(argument='homogeneous_positive_radial_sectors',radial_equation=goal['equations'][0]),
                    sections=[],measure_scale=ONE),dict(area=val)
    orientation=[];factor=None
    if method==requirements[0] and len(left)==2 and set(right)=={(1,1)} and all(c==ONE for c in left.values()):
        degree=max(i for i,j in left)
        if degree==3 and set(left)=={(3,0),(0,3)} and positive(A:=right[1,1]):
            factor=m.div(m.power(A,2),q(2));density=m.div(m.power(v,2),m.power(m.add(ONE,m.power(v,3)),2))
            lower,upper='0','+inf'
            orientation=['r=A*cos(phi)*sin(phi)/(cos(phi)^3+sin(phi)^3) for r>0',
                         'The first quadrant closes at the origin. Negative slopes are injective away from the origin and run to the pole at slope -1.',
                         'On 0<phi<pi/2 the positive tangent has differential dphi=du/(1+u^2).']
    if method==requirements[0] and set(left)<={(4,0),(2,2),(0,4)} and set(right)=={(2,0),(0,2)}:
        A=right[2,0];B=coefficient(left,(4,0));C=coefficient(left,(2,2));offset=m.add(C,m.mul(q(2),B))
        if same_value(A,right[0,2]) and same_value(B,coefficient(left,(0,4))) and all(map(positive,(A,B,offset))):
            factor=m.mul(q(2),A);density=m.div(ONE,m.add(m.mul(B,m.power(v,2)),offset))
            lower,upper='-inf','+inf'
            orientation=['The fourth-degree angular coefficient is strictly positive on the complete turn. r² equals A divided by that coefficient.',
                         'Four quadrants have the same measure. With t=tan(phi)>0 on the first, set u=t-1/t, a strictly increasing chart over the whole line.']
    if (method==requirements[1] and set(left)=={(4,0),(0,4)} and all(c==ONE for c in left.values())
            and set(right)=={(2,1)} and positive(A:=right[2,1])):
        factor=m.div(m.power(A,2),q(8));density=m.div(ONE,m.add(m.power(v,2),q(2)))
        lower,upper='-inf','+inf'
        orientation=['Set y=t*x where x is nonzero, giving x=A*t/(1+t^4) and y=A*t^2/(1+t^4).',
                     'Both tails and t=0 approach the origin; nonorigin points determine t uniquely. '
                     'The two loops are on opposite sides of x=0. Each has determinant x² with respect to t.',
                     'The primitive t³/(1+t⁴) vanishes at both ends of the positive half-line. '
                     'Its derivative is 4t²/(1+t⁴)² - t²/(1+t⁴). Both terms are integrable.',
                     'Inverting t interchanges t²/(1+t⁴) and 1/(1+t⁴). Adding them and setting u=t-1/t '
                     'gives du/(u²+2) on the full line.']
    if factor is None:raise Unsupported('The original homogeneous polynomial is outside the proved chart families')
    live_params=[n for n in params if m.contains(density,('s',n))]
    fact=[n+'>0' for n in live_params]
    goal=dict(kind='improper_integral',variable='u',integrand=source(density),parameters=live_params,stated_conditions=fact,
              lower=lower,upper=upper,requested_output=['exact_integral'])
    result=request('ordinary integral of the proved homogeneous area chart',goal)['value']
    if result.get('convergence')!='convergent' or 'value' not in result:
        raise Unsupported('The complete chart must have a finite area')
    value=freeze(result['value'])
    return dict(partition=dict(argument='verified_homogeneous_chart',original_equation=eq[0],method=method,orientation=orientation),
                sections=[dict(bounds=(lower,upper),density=density,integral=value)],measure_scale=factor),dict(area=m.mul(factor,value))


def revolution_patch(t,lib,request):
    """Recover the meridian and cover its geometric image once before integrating its metric."""
    fields={'kind','id','source','parametrization','region','surface_region','stated_conditions','requested_output'}
    src=t.get('source',{});output=t.get('requested_output');whole=output==['patch_area','whole_torus_area']
    allowed=('Найти площадь указанной части поверхности.','Найти площадь части тора между двумя параллелями, двумя меридианами и всей поверхности.')
    if (not lib.data.get('surface_revolution_patch') or set(t)-fields or not (whole or output==['surface_area'])
            or not isinstance(src,dict) or set(src)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}
            or src.get('literal_requirement') not in (None,*allowed)
            or src.get('literal_requirement')==allowed[1] and not whole):raise Unsupported('Unresolved surface map, method or additional output')
    named=t.get('surface_region');sphere=re.fullmatch(r'sphere of radius (\w+) between two given meridians and parallels',named) if isinstance(named,str) else None
    if sphere:
        if whole or set(t)&{'parametrization','region','stated_conditions'}:raise Unsupported('Conflicting original surface descriptions')
        rad=sphere[1];u=fresh_coordinate('latitude',{rad});v=fresh_coordinate('longitude',{rad,u})
        names=[rad];A=('s',rad);B=ZERO;C=A
        south,north,width=[('s',fresh_coordinate(k,{rad})) for k in ('lower_latitude','upper_latitude','longitude_width')]
        limits=[south,north];coverage=dict(kind='spherical_zone',latitude_interval=limits,longitude_width=width,
            definitions='lower and upper parallels have latitudes between -pi/2 and pi/2 in increasing order; width is the angle of the chosen meridian sector between 0 and 2*pi',
            inverse='height uniquely identifies latitude; longitude is unique modulo a turn away from the two poles')
        facts=[rad+'>0'];U=('s',u);rho=m.mul(A,('cos',U));height=m.mul(A,('sin',U))
    else:
        if named is not None:raise Unsupported('A one-to-one surface chart and its original boundaries remain to be constructed')
        chart=t.get('parametrization');region=t.get('region')
        if not isinstance(chart,list) or len(chart)!=3 or not isinstance(region,list) or len(region)!=2:raise Unsupported('Three coordinates and two source intervals required')
        intervals={}
        for s in region:
            b=re.fullmatch(r'([^<>=]+)(<=|<)([A-Za-z_]\w*)(<=|<)([^<>=]+)',s)
            if not b or b[3] in intervals:raise Unsupported('Malformed or repeated surface coordinate')
            intervals[b[3]]=(b[1],b[5])
        conditions=t.get('stated_conditions',[])
        if not isinstance(conditions,list) or not all(isinstance(q,str) for q in conditions):raise Unsupported('Explicit source conditions are required')
        names=sorted(set(re.findall(r'\b[A-Za-z_]\w*',' '.join(chart+region+conditions)))-set(intervals)-{'pi','e'}-m.FUNCTIONS-set(m.ALIASES))
        facts=[];orders=[]
        for cond in conditions:
            order=re.fullmatch(r'0<(\w+)<=(\w+)',cond)
            if order and set(order.groups())<=set(names):
                facts.extend([k+'>0' for k in order.groups()]);orders.append(tuple(('s',k) for k in order.groups()))
            else:facts.append(cond)
        ctx=m.context(dict(variable=fresh_coordinate('__surface',names),parameters=names,parameter_conditions=facts))
        xyz=[m.parse(z,None,[*intervals,*names]) for z in chart]
        if any(not known_guard(g,ctx) for z in xyz for g in domain_conditions(z,True)):raise Unsupported('An original surface chart restriction is unresolved')
        for u,v in (tuple(intervals),tuple(reversed(intervals))):
            U=('s',u);V=('s',v);cv=('cos',V);sv=('sin',V)
            rho=m.simplify(m.substitute(xyz[0],{cv:ONE}));height=xyz[2]
            if (not m.contains(rho,V) and not m.contains(height,V) and same_value(xyz[0],m.mul(rho,cv))
                    and same_value(xyz[1],m.mul(rho,sv))):break
        else:raise Unsupported('The source map is not a single meridian rotated through the given azimuth')
        cu=('cos',U);su=('sin',U);B=m.simplify(m.substitute(rho,{cu:ZERO}));z0=m.simplify(m.substitute(height,{su:ZERO}))
        A=m.add(m.substitute(rho,{cu:ONE}),m.neg(B));C=m.add(m.substitute(height,{su:ONE}),m.neg(z0))
        if (not all(m.constant_defined(k,ctx) for k in (A,B,C,z0)) or m.sign(A,ctx)!=1 or not same_value(m.power(A,2),m.power(C,2))
                or not same_value(rho,m.add(B,m.mul(A,cu))) or not same_value(height,m.add(z0,m.mul(C,su)))):
            raise Unsupported('A circular meridian with constant nonzero speed remains unproved')
        ang={axis:[m.parse(k,None,names) for k in ends] for axis,ends in intervals.items()}
        if not all(m.constant_defined(z,ctx) for ends in ang.values() for z in ends):raise Unsupported('A source angular endpoint is undefined')
        turn=m.mul(q(2),m.PI)
        def once(ends):
            delta=m.add(ends[1],m.neg(ends[0]));multiple=m.pi_multiple(delta)
            if multiple is not None:return m.mul(q(max(0,min(2,multiple))),m.PI)
            return ('max',ZERO,('min',turn,delta))
        width=once(ang[v]);start=ang[u][0]
        if (A,B) in orders or m.sign(m.add(B,m.neg(A)),ctx) in (0,1):
            limits=[start,m.add(start,once(ang[u]))]
            coverage=dict(kind='periodic_meridian',source_intervals=intervals,longitude_width=width,meridian_interval=limits,
                          inverse='angle about the axis and the angle on the profile circle are each unique modulo one turn; a parallel with zero orbit radius is a single point of zero surface area')
        elif B==ZERO and not whole:
            pts=[m.pi_multiple(z) for z in ang[u]]
            if None in pts or not -Fraction(1,2)<=pts[0]<=pts[1]<=Fraction(1,2):raise Unsupported('The entire source latitude interval must be on the nonnegative-radius branch')
            limits=ang[u];coverage=dict(kind='spherical_zone',source_intervals=intervals,longitude_width=width,latitude_interval=limits,
                                        inverse='height is strictly monotone between distinct parallels; poles have zero surface area')
        else:raise Unsupported('The radius changes sign or spindle overlap has not been excluded')
    def derivative(role,z):
        return freeze(request(role,dict(kind='partial_derivatives',function=source(z),variables=[u],parameters=names,
                                      stated_conditions=facts,requested_output=['first_partial_derivatives']))['value'][0])
    dr=derivative('radial derivative along the meridian',rho);dz=derivative('vertical derivative along the meridian',height)
    if not same_value(m.dot((dr,dz),(dr,dz)),m.power(A,2)):raise Unsupported('Meridian arclength identity failed')
    primitive=m.add(m.mul(B,U),m.mul(A,('sin',U)))
    if not same_value(derivative('primitive of nonnegative orbit radius',primitive),rho):raise Unsupported('Meridian integral did not verify')
    delta=m.add(m.substitute(primitive,{U:limits[1]}),m.neg(m.substitute(primitive,{U:limits[0]})))
    area=m.mul(width,m.mul(A,delta))
    values={'surface_area':area}
    if whole:
        turn=m.mul(q(2),m.PI);full=m.add(m.substitute(primitive,{U:turn}),m.neg(m.substitute(primitive,{U:ZERO})))
        values={'patch_area':area,'whole_torus_area':m.mul(turn,m.mul(A,full))}
    return dict(theorem='method.surface_revolution_patch',meridian=[rho,height],meridian_parameter=u,azimuth=v,metric_diagonal=[m.power(A,2),m.power(rho,2)],
                meridian_speed=A,orbit_radius=rho,primitive=primitive,coverage=coverage,computed_interval=limits,
                complete_turns=[m.mul(q(2),m.PI)]*2 if whole else []),values


def plane_curve_radius(task,lib,request):
    """Radius is speed cubed over absolute turning; use a tangent to a level or a given chart."""
    if not lib.data.get('plane_curve_turning'):raise Unsupported('The plane curvature theorem is unavailable')
    fields={'kind','id','source','curve','representation','parameter','positive_parameters','printed_conditions','requested_output','method_requirement'}
    src=task.get('source',{});mode=task['representation'];curve=task['curve']
    if (set(task)-fields or task.get('method_requirement') not in (None,'any') or task.get('requested_output',['curvature_radius'])!=['curvature_radius']
            or not isinstance(src,dict) or set(src)-{'exercise','printed_page','pdf_page','pdf_sha256','literal_requirement'}
            or src.get('literal_requirement') not in (None,'Определить радиус кривизны заданной кривой.',
                'Определить радиус кривизны кривой в полярных координатах. Параметры положительны.')):
        raise Unsupported('The original method or additional curvature obligation remains')
    polar=mode=='polar';implicit=mode=='implicit'
    if src.get('literal_requirement','').endswith('Параметры положительны.') and not polar:
        raise Unsupported('The printed polar representation was changed')
    t=task.get('parameter','phi' if polar else 't');v=('s',t)
    if implicit:
        if not isinstance(curve,str) or curve.count('=')!=1 or 'parameter' in task:raise Unsupported('One original level equation is required')
        strings=curve.split('=');coordinates=['x','y']
    elif polar:
        if not isinstance(curve,str) or not re.fullmatch(r'r\s*=\s*[^=]+',curve):raise Unsupported('The positive and negative polar branches and their endpoints must be proved')
        strings=[curve.split('=')[1]];coordinates=[t]
    elif mode=='parametric' and isinstance(curve,list) and len(curve)==2 and all(isinstance(z,str) for z in curve):
        strings=curve;coordinates=[t]
    else:raise Unsupported('A regular plane chart or level function is required')
    names=sorted(set(re.findall(r'\b[A-Za-z_]\w*',' '.join(strings)))-set(coordinates)-{'pi','e'}-m.FUNCTIONS-set(m.ALIASES))
    positives=task.get('positive_parameters',[]);printed=task.get('printed_conditions',[])
    if not all(isinstance(group,list) and all(isinstance(c,str) for c in group) for group in (positives,printed)) or set(positives)-set(names):
        raise Unsupported('Unbound parameter assumptions')
    if src.get('literal_requirement','').endswith('Параметры положительны.') and set(positives)!=set(names):raise Unsupported('A printed positive parameter is missing')
    coords=[m.parse(z,None,[*coordinates,*names]) for z in strings]
    facts=[p+'>0' for p in positives];ordered=[]
    for condition in printed:
        pair=re.fullmatch(r'(\w+)>=(\w+)',condition)
        if pair and set(pair.groups())<=set(names):ordered.append(pair.groups())
        else:facts.append(condition)
    for a,b in ordered:
        if b+'>0' in facts:facts.append(a+'>0')
    natural=list(dict.fromkeys(g for z in coords for g in domain_conditions(z,True)))
    fixed_guards=[g for g in natural if not any(m.contains(g[1],('s',p)) for p in coordinates)]
    facts.extend(guard_source(g) for g in fixed_guards)
    dummy=fresh_coordinate('__point',set(coordinates+names))
    ctx=m.context(dict(variable=dummy,parameters=[*coordinates,*names],parameter_conditions=facts))
    if any(g not in fixed_guards and not known_guard(g,ctx) for g in natural):
        raise Unsupported('Boundary points of this nonsmooth chart require a separate local analysis')
    def differential(role,z,variables):
        return list(map(freeze,request(role,dict(kind='partial_derivatives',function=source(z),variables=variables,
            parameters=names,stated_conditions=facts,requested_output=['first_partial_derivatives']))['value']))
    def tidy(z):
        p,d=m.rational_form(z)
        return m.div(m.poly_expr(m.trig_reduce(p,complete=True)),m.poly_expr(m.trig_reduce(d,complete=True)))
    def cross(a,b):return tidy(m.add(m.mul(a[0],b[1]),m.neg(m.mul(a[1],b[0]))))
    plan=dict(theorem='method.plane_curve_turning',representation=mode,source_formulas=coords,source_conditions=printed,
              positive_parameters=positives,original_domain=natural)
    if implicit:
        F=m.add(coords[0],m.neg(coords[1]));terms=coordinate_terms(F)
        if not terms or any(i+j>2 for i,j in terms):raise Unsupported('Singular points of a higher-degree level set need a separate chart')
        grad=differential('gradient of the original level',F,coordinates);gx,gy=grad
        xx,xy=differential('first row of its Hessian',gx,coordinates);yx,yy=differential('second row of its Hessian',gy,coordinates)
        if not same_value(xy,yx):raise Unsupported('Mixed derivatives do not agree')
        N=m.dot(grad,grad);detH=m.add(m.mul(xx,yy),m.neg(m.power(xy,2)))
        T=m.add(m.add(m.mul(xx,m.power(gy,2)),m.mul(yy,m.power(gx,2))),m.mul(q(-2),m.mul(xy,m.mul(gx,gy))))
        D=tidy(m.add(T,m.neg(m.mul(q(2),m.mul(detH,F)))))
        if any(m.contains(D,z) for z in (X,Y)):raise Unsupported('The turning determinant does not reduce on this level')
        if not any(i+j>0 for i,j in terms):raise Unsupported('A constant level equation does not specify a curve')
        plan.update(level=F,gradient=grad,hessian=[[xx,xy],[yx,yy]],tangent=[m.neg(gy),gx],level_multiple=m.mul(q(2),detH))
        singular=dict(type='degenerate_conic_if_turning_zero',condition=D,nonconstant_coefficients=[c for degree,c in sorted(terms.items()) if degree!=(0,0)],
                      constant_term=terms.get((0,0),ZERO),
                      detail='on F=0 nonzero turning forces nonzero gradient; a degenerate conic gives lines, a point or no points; if every nonconstant coefficient vanishes the level is empty or the entire plane, with no distinguished curve')
    else:
        if polar:
            rad=coords[0];rp,=differential('first derivative of the radius',rad,[t]);rpp,=differential('second derivative of the radius',rp,[t])
            vel=[rp,rad];acc=[m.add(rpp,m.neg(rad)),m.mul(q(2),rp)];plan['moving_basis']='radial_and_angular'
        else:
            vel=[differential('velocity '+k,z,[t])[0] for k,z in zip(('x','y'),coords)]
            acc=[differential('acceleration '+k,z,[t])[0] for k,z in zip(('x','y'),vel)]
        N=tidy(m.dot(vel,vel));D=cross(vel,acc)
        plan.update(parameter=t,velocity=vel,acceleration=acc)
        if not m.contains(D,v):
            singular=dict(type='globally_constant_turning',condition=D,
                          detail='nonzero determinant ensures nonzero speed; if it vanishes everywhere the analytic image lies on a line or is a point')
        elif m.sign(N,ctx)==1 or any(m.nonzero(z,ctx) for z in vel):
            singular=dict(type='regular_everywhere',speed_squared=N)
        else:
            powers=[m.common_mon(m.rational_form(z)[0]) for z in vel if z!=ZERO]
            shared=[p for p in names if powers and all(vv.get(('s',p),0)>0 for vv in powers) and not m.nonzero(('s',p),ctx)]
            regular_ctx=m.context(dict(variable=dummy,parameters=[t,*names],parameter_conditions=facts+[s+'!=0' for s in shared]))
            if polar:
                # At r=r'=0 the acceleration and jerk have determinant 3(r'')².
                witness=next((w for w in (rpp,m.add(rad,rpp),m.add(rp,rpp)) if m.nonzero(w,regular_ctx)),None)
                if witness is None:raise Unsupported('The second radial derivative at a stationary pole is unresolved')
                test=m.mul(q(3),m.power(rpp,2))
            else:
                jerk=[differential('jerk '+k,z,[t])[0] for k,z in zip(('x','y'),acc)]
                test=cross(acc,jerk);witness=test
                # Remove the vanishing velocity before testing the jets, e.g. at t=0.
                if not m.nonzero(test,regular_ctx):
                    witness=next((z for a in (q(-1),ONE,q(-2),q(2)) if m.nonzero(z:=tidy(m.add(test,m.mul(a,N))),regular_ctx)),None)
                if witness is None:raise Unsupported('A stationary parameter has no certified cusp or regular reparametrization')
                plan['jerk']=jerk
            singular=dict(type='ordinary_cusps_at_zero_speed',speed_squared=N,collapsed_if_any_zero=shared,
                          acceleration_jerk_determinant_at_rest=test,nonzero_witness=witness,
                          detail='nonzero second and transverse third jets give a semicubical cusp; a common zero parameter factor instead makes the whole velocity zero')
    quotient=m.div(D,N) if N!=ZERO else ZERO
    radius=(('div',('sqrt',N),('abs',quotient)) if not any(m.contains(quotient,('s',z)) for z in coordinates)
            else ('div',('mul',N,('sqrt',N)),('abs',D)))
    value=dict(radius=radius if D!=ZERO else None,
               finite_where=dict(speed_squared_positive=N,turning_nonzero=D),
               infinite_radius_where=dict(speed_squared_positive=N,turning_zero=D),singular=singular)
    return plan,value


def radial_arc_length(task,request):
    """An unbounded radius forces infinite length; a monotone radius can itself be a chart."""
    import math
    from integrals import affine
    if (task.get('coordinate_system')!='polar' or not isinstance(task.get('equations'),list) or len(task['equations'])!=1
            or not task['equations'][0].startswith('r=')):
        return None
    src=task.get('source',{})
    if (not isinstance(src,dict) or set(src)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','section_convention'}
            or src.get('section_convention') not in (None,'Все параметры в этом и следующих параграфах раздела IV считать положительными, с. 208.')):return None
    params=task.get('parameters',[]);conditions=task.get('stated_conditions',[]);positive=[s for s in conditions if s in [p+'>0' for p in params]]
    if set(params)&{'r','phi'}:raise Unsupported('A free parameter collides with a polar coordinate')
    span=[s for s in conditions if s not in positive]
    if len(span)!=1:return None
    bounds=re.fullmatch(r'([^<>=]+)(<=|<)(r|phi)(<=|<)([^<>=]+)',span[0])
    if not bounds:return None
    left,ls,axis,rs,right=bounds.groups();ctx=m.context(dict(variable='phi',parameters=params,parameter_conditions=positive))
    A,B=[m.parse(s,None,params) for s in (left,right)]
    if not all(m.constant_defined(z,ctx) for z in (A,B)) or m.sign(m.add(B,m.neg(A)),ctx)!=1:return None
    raw=m.parse(task['equations'][0][2:],'phi',params);gain,fn=(raw[1],raw[2]) if raw[0]=='mul' else (ONE,raw)
    if not m.constant_defined(gain,ctx):gain,fn=fn,gain
    if not m.constant_defined(gain,ctx) or not m.nonzero(gain,ctx) or fn[0] not in ('exp','tan','cot','sec','csc'):return None
    if any(not known_guard(g,ctx) for g in domain_conditions(fn[1])):return None
    try:slope,shift=affine(fn[1],'phi')
    except Unsupported:return None
    if not all(m.constant_defined(z,ctx) for z in (shift,slope)) or not m.nonzero(slope,ctx):return None
    plan=dict(theorem='method.radial_arc_domain',interval=[left,right],closed_ends=[ls=='<=',rs=='<='],source_radius=raw,
              amplitude=gain,slope=slope,phase_shift=shift,source_interval_verified=True,line_integral=[])
    if axis=='r' and fn[0]=='exp' and m.sign(gain,ctx)==1 and m.sign(A,ctx) in (0,1) and (A!=ZERO or ls=='<'):
        # r' = slope*r and its range is exactly (0,infinity); every positive radius labels one point.
        metric=m.simplify(('sqrt',m.add(ONE,m.div(ONE,m.power(slope,2)))))
        sub=dict(kind='iterated_integral',integrand='1',parameters=params,stated_conditions=positive,integration_order=[dict(variable='r',lower=left,upper=right)],requested_output=['exact_integral'])
        width=freeze(request('integrate the radial differential on the closure',sub)['value'])
        plan.update(argument='monotone_radius_chart',inverse_angle=m.div(m.add(('ln',m.div(('s','r'),gain)),m.neg(shift)),slope),
                    radius_metric=metric,ends='the pullback is constant on the open radius interval and extends integrably to both finite endpoints')
        return plan,dict(arc_length=m.mul(metric,width))
    if axis=='phi' and fn[0]!='exp':
        ends=[m.pi_multiple(m.add(m.mul(slope,u),shift)) for u in (A,B)]
        if None in ends:return None
        lo,hi=sorted(ends);offset=Fraction(1,2) if fn[0] in ('tan','sec') else Fraction(0)
        phase=offset+math.ceil(lo-offset)
        if phase>hi:return None
        plan.update(argument='unbounded_radial_variation',pole=m.div(m.add(m.mul(q(phase),m.PI),m.neg(shift)),slope),
                    lower_bound='distance from any fixed regular point is at least the difference of the two radial magnitudes')
        return plan,dict(arc_length='+inf')
    return None


def homogeneous_loop(sides,ctx):
    """On a positive ray recover its unique intersection, then compactify the slope."""
    def base_power(z):
        if z[0]=='pow':return z[1],q(z[2])
        if z[0]=='rpow':return z[1],z[2]
        return z,ONE
    for lhs,rhs in (sides,sides[::-1]):
        if lhs[0]!='add':continue
        axes={}
        for term in lhs[1:]:
            base,degree=base_power(term)
            coordinate,scale=base[1:] if base[0]=='div' else (base,ONE)
            if coordinate not in (X,Y) or not m.constant_defined(scale,ctx) or m.sign(scale,ctx)!=1:break
            axes[coordinate]=(base,scale,degree)
        if set(axes)!={X,Y}:continue
        (u,a,p),(v,b,r)=(axes[z] for z in (X,Y))
        if not m.constant_defined(p,ctx) or not m.constant_defined(r,ctx) or not same_value(p,r):continue
        coefficient=ONE;exponents={};factors=[rhs]
        while factors:
            z=factors.pop()
            if z[0]=='mul':factors.extend(z[1:]);continue
            if m.constant_defined(z,ctx):coefficient=m.mul(coefficient,z);continue
            base,degree=base_power(z)
            if base not in (u,v) or base in exponents or not m.constant_defined(degree,ctx):break
            exponents[base]=degree
        else:
            if set(exponents)!={u,v}:continue
            h=exponents[u]
            if (not same_value(h,exponents[v]) or not same_value(p,m.add(ONE,m.mul(q(2),h)))
                    or m.sign(h,ctx)!=1 or m.sign(coefficient,ctx)!=1):continue
            A=m.div(h,p);B=m.div(m.add(h,ONE),p)
            if not same_value(m.add(A,B),ONE) or not same_value(m.add(B,m.neg(A)),m.div(ONE,p)):continue
            coverage=dict(kind='positive_radial_loop',normalized_coordinates=[u,v],degree=p,index=h,
                          inverse_parameter='v^p/(u^p+v^p)',coordinate_exponents=[[A,B],[B,A]],
                          radius_coefficient=coefficient,parameter_interval=[ZERO,ONE],
                          simple='at each positive slope t=v/u there is exactly one point, u=C*t^h/(1+t^p); w=t^p/(1+t^p) increases from 0 to 1',
                          closure='both positive endpoint powers tend to zero; reparametrize by a power greater than 1/A and 1/B near each end for a C1 arc',
                          exterior='negative slopes, when admitted for real powers, run to a pole at t=-1 or to infinity and do not form another loop',
                          orientation='the polar angle increases strictly, so the interior on each positive ray lies to the left',
                          pullback='for U=w^A(1-w)^B, V=w^B(1-w)^A, UV=w(1-w); UV*d(log(V/U))=dw/p')
            return coverage,[m.mul(a,coefficient),m.mul(b,coefficient)],m.div(ONE,m.mul(q(2),p))
    raise Unsupported('A unique positive radial loop with two certified endpoint limits has not been established')


def boundary_area(t,lib,request,saved=None):
    """Reduce the actual bounded component to a simple positively oriented model contour."""
    if not lib.data.get('simple_boundary_area'):raise Unsupported('Boundary-area composition is unavailable')
    fields={'id','kind','curve','source','parameters','stated_conditions','suggested_substitution','method_requirement','requested_output'}
    method=t.get('method_requirement');src=t.get('source',{})
    if (set(t)-fields or t.get('requested_output')!=['area','boundary_evaluation'] or method not in (None,'boundary_area_integral')
            or not isinstance(src,dict) or set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement',
                                                     'method_requirement','explicit_required_method','explicit_imposed_method'}
            or any(src.get(k) not in (None,method) for k in ('method_requirement','explicit_required_method','explicit_imposed_method'))
            or src.get('literal_requirement') not in (None,'Вычислить площадь с помощью криволинейных интегралов.')):
        raise Unsupported('The specified area, boundary evaluation or printed method is unresolved')
    curve=t['curve'];body,sep,inline=curve.partition(';')
    head=re.match(r'^(ellipse|astroid|parabola|loop)(?: of)?\s+',body)
    label=head[1] if head else None
    if head:body=body[head.end():]
    parametric=re.fullmatch(r'x=(.+?),\s*y=(.+?),\s*(.+?)\s*<=\s*([A-Za-z_]\w*)\s*<=\s*(.+)',body)
    cap=re.fullmatch(r'([^=]+)=([^=]+) and y=([^=]+)',body)
    loop=re.fullmatch(r'([^=]+)=([^=]+)',body) if label=='loop' else None
    if not parametric and not cap and not loop:raise Unsupported('A simple closed parametrization or a bounded arc and its closing chord must be established')
    if label=='loop' and not loop:raise Unsupported('An implicit loop equation is required')
    variable=parametric[4] if parametric else None
    names=set(re.findall(r'\b[A-Za-z_]\w*',body))-{'x','y','pi','e','and',variable}-m.FUNCTIONS-set(m.ALIASES)
    declared=t.get('parameters',[]);conditions=t.get('stated_conditions',[])
    if not all(isinstance(items,list) and all(isinstance(item,str) for item in items) for items in (declared,conditions)):
        raise Unsupported('The original parameter declarations and conditions must be explicit')
    params=sorted(names|set(declared))
    if set(params)&{'x','y',variable}:raise Unsupported('A free parameter collides with a source coordinate')
    conditions=list(conditions)
    if sep:
        group=re.fullmatch(r'([A-Za-z_]\w*(?:,\s*[A-Za-z_]\w*)+)(>0|>1|<0|!=0)',inline.strip())
        if group:conditions.extend(x.strip()+group[2] for x in group[1].split(','))
        else:conditions.extend(x.strip() for x in inline.split(','))
    ctx=m.context(dict(variable=variable or fresh_coordinate('__u',params),parameters=params,parameter_conditions=conditions))
    s=fresh_coordinate('s',params)
    v=('v',s)
    child_kwargs={};constant_factor=ONE
    if loop:
        sides=[m.parse(z,None,['x','y',*params]) for z in loop.groups()]
        coverage,scale,constant_factor=homogeneous_loop(sides,ctx);center=[ZERO,ZERO]
        if not m.constant_defined(constant_factor,ctx) or m.sign(constant_factor,ctx)!=1:
            raise Unsupported('The pulled-back area density must be finite and positive')
        coverage['constant_area_density']=constant_factor
        # The verified pullback is regular even where the original chart has an infinite endpoint velocity.
        child_kwargs=dict(variables=[fresh_coordinate('w',set(params)|{s})],coefficients=['1'])
        contour=[dict(map=[s],lower='0',upper='1')]
    elif parametric:
        if label=='parabola' or variable in ('x','y'):raise Unsupported('Incompatible source curve or parameter')
        left,right=[m.parse(z,None,params) for z in (parametric[3],parametric[5])]
        if not all(m.constant_defined(b,ctx) for b in (left,right)) or not same_value(m.add(right,m.neg(left)),m.mul(q(2),m.PI)):
            raise Unsupported('The published bounds must cover exactly one complete turn')
        power=[];scale=[];center=[]
        for text,wave in zip(parametric.group(1,2),('cos','sin')):
            raw=m.parse(text,variable,params);idx=('v',variable)
            if any(not known_guard(g,ctx) for g in domain_conditions(raw)):
                raise Unsupported('The original parametrization has an unresolved denominator or branch')
            poly=m.substitute(raw,{(wave,idx):X})
            if m.contains(poly,idx):raise Unsupported('The angle map has an unresolved winding or branch')
            coeff=coordinate_terms(poly);center.append(coeff.pop((0,0),ZERO))
            if not coeff:power.append(1);scale.append(ZERO);continue
            if len(coeff)!=1:raise Unsupported('Injectivity of this nonlinear change of a circle coordinate is unproved')
            ((p,other),a),=coeff.items()
            if other or p<=0 or p%2==0 or not m.constant_defined(a,ctx):raise Unsupported('The coordinate power must be strictly increasing on the whole real line')
            power.append(p);scale.append(a)
        if label in ('ellipse','astroid') and power!=([1,1] if label=='ellipse' else [3,3]):
            raise Unsupported('The printed curve type differs from its parametrization')
        maps=[source(m.power((name,v),p)) for name,p in zip(('cos','sin'),power)]
        contour=[dict(map=maps,lower='0',upper='2*pi')]
        coverage=dict(kind='odd_coordinate_homeomorphisms',powers=power,source_interval=[left,right],
                      simple='odd powers are strictly increasing; the unit circle is injective modulo a complete turn',
                      orientation='coordinatewise increasing powers preserve orientation on all four quadrants')
    else:
        if label in ('ellipse','astroid'):raise Unsupported('The printed conic is incompatible with this chord construction')
        sides=[m.parse(z,None,['x','y',*params]) for z in cap.group(1,2)]
        y0=m.parse(cap[3],None,params)
        if not m.constant_defined(y0,ctx) or any(not known_guard(g,ctx) for side in sides for g in domain_conditions(side)):
            raise Unsupported('The source wall or its closing chord has an unresolved restriction')
        candidates=(saved['coverage']['square_side'],) if saved is not None else range(2)
        for i in candidates:
            if type(i) is not int or i not in (0,1):raise Unsupported('Invalid proposed coordinate')
            z,rhs=sides[i],sides[1-i]
            if z[0]!='pow' or z[2]!=2:continue
            affine=coordinate_terms(z[1]);line=coordinate_terms(rhs)
            if set(affine)-{(0,0),(1,0),(0,1)} or set(line)-{(0,0),(1,0)}:continue
            A,B,C=(affine.get(degree,ZERO) for degree in ((1,0),(0,1),(0,0)))
            D=line.get((1,0),ZERO);E=line.get((0,0),ZERO)
            if not all(m.nonzero(c,ctx) for c in (A,B,D)):continue
            x0=m.div(m.neg(E),D)
            if not same_value(m.add(m.add(m.mul(A,x0),m.mul(B,y0)),C),ZERO):continue
            center=[x0,y0];scale=[m.div(D,m.power(A,2)),m.div(D,m.mul(A,B))]
            base=m.mul(m.div(D,A),v);arc=[m.add(x0,m.mul(scale[0],m.power(v,2))),
                                         m.add(y0,m.mul(scale[1],m.mul(v,m.add(ONE,m.neg(v)))))]
            subst={X:arc[0],Y:arc[1]}
            if not same_value(m.substitute(z[1],subst),base) or not same_value(m.substitute(rhs,subst),m.power(base,2)):continue
            coverage=dict(kind='affine_square_with_chord',square_side=i,auxiliary=z[1],rescaling=m.div(D,A),parameter=s,
                          inverse_parameter=source(m.mul(m.div(A,D),z[1])),source_arc=arc,
                          intersections=[center,[m.add(x0,scale[0]),y0]],normalized_height=f'{s}*(1-{s})',
                          simple='the affine coordinate recovers the parameter; the height vanishes exactly at 0 and 1 and is positive between',
                          orientation='in normalized coordinates follow the lower chord to the right and return above it')
            contour=[dict(map=[s,'0'],lower='0',upper='1'),dict(map=[s+'^2',coverage['normalized_height']],lower='1',upper='0')]
            break
        else:raise Unsupported('No invertible affine square with a certified chord and two isolated intersections was found')
    det=m.simplify(m.mul(*scale))
    child=dict(kind='line_integral',variables=['x','y'],parameter=s,path=contour,coefficients=['-y/2','x/2'],requested_output=['line_integral'])
    child.update(child_kwargs)
    positive=m.mul(constant_factor,freeze(request('area form on one simple positively oriented boundary',child)['value']))
    if not m.known_nonnegative(positive,ctx) and m.sign(positive,ctx)!=1:
        raise Unsupported('The boundary calculation did not certify a nonnegative unit area')
    magnitude=det if m.known_nonnegative(det,ctx) else m.simplify(('abs',det))
    area=m.simplify(m.mul(magnitude,positive))
    normalization=dict(center=center,scales=scale,determinant=det,unit_boundary_integral=positive,
                       source_signed_integral=m.simplify(m.mul(det,positive)),
                       positive_orientation='preserve traversal if determinant>0, reverse if determinant<0',
                       zero_case='if determinant is zero the image is a segment or a point of area zero',
                       translation_term='an exact constant-coefficient differential on the closed contour')
    return dict(coverage=coverage,normalization=normalization,parameter_conditions=conditions),dict(area=area,boundary_evaluation=area)


def question(t):
    kind=t['kind']
    source_fields={'boundaries'} if kind=='planar_area' else {'region','integrand'}
    if (set(t)-source_fields-{'kind','id','source','parameters','stated_conditions','requested_output','method_requirement'}
            or t.get('requested_output')!=KINDS[kind]):
        raise Unsupported('Additional source goals or a second integration order remain')
    method=t.get('method_requirement')
    if method not in (None,'polar_coordinates','appropriate_change_of_variables'):
        raise Unsupported('The specified coordinate map requires its own proof')
    src=t.get('source',{})
    if not isinstance(src,dict) or any(src.get(k) not in (None,method) for k in ('method_requirement','explicit_imposed_method','explicit_required_method')):
        raise Unsupported('Conflicting printed coordinate method')
    raw=t.get('region') if kind!='planar_area' else t.get('boundaries')
    if isinstance(raw,list):
        if len(raw)!=1:raise Unsupported('An intersection of several boundaries requires a coverage proof')
        raw=raw[0]
    if not isinstance(raw,str):raise Unsupported('Missing original plane region')
    f=t.get('integrand') if kind!='planar_area' else '1'
    if not isinstance(f,str):raise Unsupported('Missing original integrand')
    disk=re.fullmatch(r'disk centered at origin with radius (\w+)',raw)
    if disk:raw='x^2+y^2<=('+disk[1]+')^2'
    bounded=kind=='planar_area' or raw.startswith(('bounded by ','ellipse with bounding curve '))
    raw=re.sub(r'^(?:bounded by |ellipse with bounding curve )','',raw)
    pieces=re.split(r'(<=|=)',raw)
    if len(pieces) not in (3,5) or len(pieces)==5 and pieces[1::2]!=['<=','<=']:
        raise Unsupported('A bounded sublevel or annulus has not been established')
    if pieces[1]=='=' and not bounded:
        raise Unsupported('The source curve alone does not specify a polar region')
    tokens=set(re.findall(r'\b[A-Za-z_]\w*',raw+' '+f))
    params=sorted(tokens-{'x','y','f','pi','e'}-m.FUNCTIONS-set(m.ALIASES))
    for p in t.get('parameters',[]):
        if not isinstance(p,str) or p in ('x','y'):raise Unsupported('Unsupported plane parameter')
        if p not in params:params.append(p)
    facts=list(t.get('stated_conditions',[]))
    # A geometric radius is nonnegative by definition; squaring it in the wall
    # is valid without introducing a positive lower bound for the integration.
    ctx=m.context(dict(variable=fresh_coordinate('__radius',params),parameters=params,parameter_conditions=facts))
    if disk and not m.known_nonnegative(m.parse(disk[1],None,params),ctx):
        raise Unsupported('The stated geometric radius is not proved nonnegative')
    args=[m.parse(s,None,['x','y',*params]) for s in pieces[::2]]
    return f,params,facts,ctx,args


def coordinate_terms(expr):
    """Group a polynomial by powers of x and y, leaving fixed coefficients intact."""
    num,den=m.rational_form(expr);d=m.poly_expr(den)
    if m.contains(d,X) or m.contains(d,Y):raise Unsupported('A denominator depends on the integration point')
    terms={}
    for mon,weight in num.items():
        atoms=dict(mon);degree=(atoms.pop(X,0),atoms.pop(Y,0))
        c=m.poly_expr({tuple(atoms.items()):weight})
        if m.contains(c,X) or m.contains(c,Y):raise Unsupported('Expected a polynomial in the plane coordinates')
        terms[degree]=m.add(terms.get(degree,ZERO),m.div(c,d))
    return terms


def frame_area(args,ctx,receipt):
    if len(args)!=2 or any(not known_guard(g,ctx) for e in args for g in domain_conditions(e)):
        raise Unsupported('The affine frame has an unresolved original restriction')
    left,radius2=args
    if not m.constant_defined(radius2,ctx) or not m.known_nonnegative(radius2,ctx):
        raise Unsupported('An affine disk needs a nonnegative squared radius')
    if receipt is None:
        if left[0]!='add' or any(term[0]!='pow' or term[2]!=2 for term in left[1:]):
            raise Unsupported('No candidate affine frame exposed by the wall')
        receipt=[source(term[1]) for term in left[1:]]
    if not isinstance(receipt,(list,tuple)) or len(receipt)!=2:raise Unsupported('Invalid affine coordinate pair')
    coordinates=[m.parse(v,None,['x','y',*ctx['parameters']]) for v in receipt]
    # Check the proposed map locally, independently of its discovery in the syntax.
    if not same_value(left,m.add(*(m.power(z,2) for z in coordinates))):
        raise Unsupported('The squared norm of the map is not the source wall')
    matrix=[]
    for z in coordinates:
        if any(not known_guard(g,ctx) for g in domain_conditions(z)):raise Unsupported('A proposed coordinate has a pole')
        c=coordinate_terms(z)
        if any(sum(k)>1 for k in c):raise Unsupported('The proposed map is not affine')
        matrix.append([c.get(k,ZERO) for k in ((1,0),(0,1),(0,0))])
    (a,b,_),(c,d,_)=matrix
    det=m.add(m.mul(a,d),m.neg(m.mul(b,c)))
    if not m.nonzero(det,ctx):raise Unsupported('Invertibility of the coordinate change remains open')
    return dict(strategy='affine_disk',coordinate_pair=receipt,matrix=matrix,determinant=det,radius_squared=radius2), m.div(m.mul(m.PI,radius2),m.simplify(('abs',det)))


def radial_integral(kind,f,params,ctx,args,request):
    from integrals import learned_nodes
    from quadrature import gamma_rational
    radial_form=m.add(m.power(X,2),m.power(Y,2))
    lower,wall,upper=(ZERO,*args) if len(args)==2 else args
    if not same_value(wall,radial_form) or domain_conditions(wall):
        raise Unsupported('The region is not a concentric disk or annulus')
    if not all(m.constant_defined(e,ctx) and m.known_nonnegative(e,ctx) for e in (lower,upper)):
        raise Unsupported('The radii must be real on the inherited parameter domain')
    radial=fresh_coordinate('r',params)
    angular=fresh_coordinate('phi',params+[radial])
    coordinates={'radius':radial,'angle':angular}
    image={'x':f'{radial}*cos({angular})','y':f'{radial}*sin({angular})'}
    def radius(e):
        root=m.simplify(('sqrt',e))
        if root[0]=='abs' and m.sign(root[1],ctx)==1:return root[1]
        if root[0]=='mul':return m.mul(*(a[1] if a[0]=='abs' and m.sign(a[1],ctx)==1 else a for a in root[1:]))
        return root
    lo,hi=map(radius,(lower,upper))
    plan=dict(strategy='polar_fibers',squared_radii=[lower,upper],radii=[lo,hi],angle=[ZERO,m.mul(q(2),m.PI)],
              coordinates=coordinates,cartesian_map=image,free_parameters=params,jacobian=radial)
    ordered=m.known_nonnegative(m.add(upper,m.neg(lower)),ctx)
    if kind=='polar_change_bounds':
        if f=='f(x,y)':density=f"{radial}*f({image['x']},{image['y']})"
        else:
            raw=m.parse(f,None,['x','y',*params])
            if any(not known_guard(g,ctx) for g in domain_conditions(raw)):
                raise Unsupported('The integrand has an unresolved source-domain condition')
            bound=[radial,angular]
            mapped=m.substitute(raw,{var:m.parse(image[var[1]],None,bound) for var in (X,Y)})
            density=source(m.mul(('s',radial),mapped))
        return plan,dict(integrand=density,coordinates=coordinates,**{radial:[lo,hi],angular:plan['angle']},
                         condition=None if ordered else source(lower)+'<='+source(upper),otherwise='empty region' if not ordered else None)
    if not ordered:raise Unsupported('The relative order of the two radii needs a parameter split')
    if kind in ('polar_integral_reduction','planar_integral_reduction'):
        match=re.fullmatch(r'f\((.+)\)',f)
        if not match:raise Unsupported('A radial function has not been isolated')
        inner=m.parse(match[1],None,['x','y',*params])
        if inner[0]!='sqrt' or not same_value(inner[1],radial_form) or domain_conditions(inner[1]):
            raise Unsupported('The function also depends on the angle or has another restriction')
        return plan,dict(integrand=f'2*pi*{radial}*f({radial})',bounds=[lo,hi],variable=radial)
    raw=m.parse(f,None,['x','y',*params])
    r=('v',radial)
    nodes=[n for n in learned_nodes(raw) if isinstance(n,tuple) and n[0]=='sqrt' and
           not domain_conditions(n[1]) and same_value(n[1],radial_form)]
    transformed=m.substitute(raw,{n:r for n in nodes})
    if not m.contains(transformed,X) and not m.contains(transformed,Y):
        if any(a[0] not in {'q','v','s','pi','exp','sin','cos','mul','add','pow'} or a[0]=='pow' and a[2]<1
               for a in learned_nodes(transformed) if isinstance(a,tuple)):
            raise Unsupported('Continuity on the full radial interval remains open')
        angle=m.mul(q(2),m.PI);density=m.mul(r,transformed)
    else:
        # On the four quadrants |x^i y^j| has the same angular integral.
        if raw[0]!='abs' or domain_conditions(raw[1]):raise Unsupported('Need a verified angular moment')
        terms=coordinate_terms(raw[1])
        if len(terms)!=1:raise Unsupported('Angular zeros inside a quadrant need a partition')
        ((i,j),c),=terms.items()
        if not m.constant_defined(c,ctx):raise Unsupported('The angular coefficient can be undefined')
        angle=m.mul(q(2),m.div(m.mul(gamma_rational(Fraction(i+1,2)),gamma_rational(Fraction(j+1,2))),
                               gamma_rational(Fraction(i+j+2,2))))
        density=m.mul(m.simplify(('abs',c)),m.power(r,i+j+1));plan['angular_powers']=[i,j]
    plan.update(radial_density=density,angular_factor=angle)
    if kind not in ('planar_exact_integral','planar_area'):raise Unsupported('A different output was requested')
    # Polynomial powers over radial intervals have no singular endpoints.
    from polynomial import rf,NotRational
    try:
        p,d=rf(density,radial)
        if len(d)!=1:raise NotRational()
        value=ZERO
        for i,c in enumerate(p):
            if c:value=m.add(value,m.mul(q(c/(d[0]*(i+1))),m.add(m.power(hi,i+1),m.neg(m.power(lo,i+1)))))
    except NotRational:
        child=dict(kind='iterated_integral',integrand=source(density),parameters=params,
                   integration_order=[dict(variable=radial,lower=source(lo),upper=source(hi))],requested_output=['exact_integral'])
        value=freeze(request('integrate the continuous radial density',child)['value'])
    return plan,m.simplify(m.mul(angle,value))


def plane_measure(t,lib,request,mode,saved=None):
    f,params,facts,ctx,args=question(t)
    kind=t['kind'];method=t.get('method_requirement')
    if mode=='affine_disk' and kind=='planar_area' and method!='polar_coordinates':
        return frame_area(args,ctx,None if saved is None else saved['coordinate_pair'])
    if mode=='polar_fibers':
        return radial_integral(kind,f,params,ctx,args,request)
    if mode=='quadratic_moment' and len(args)==2 and not method and kind in ('planar_area','planar_exact_integral','planar_integral_mean'):
        left,right=args
        child=dict(kind='ellipsoid_moment',variables=['x','y'],parameters=params,stated_conditions=facts,integrand=f,
                   quadratic_region=dict(left=source(left),right=source(right)),requested_output=['mean' if kind=='planar_integral_mean' else 'exact_integral'])
        proof=request('polynomial moment of the bounded quadratic sublevel',child)
        return dict(strategy=mode,region=child['quadratic_region'],parameter_domain=proof['compilation']['natural_parameter_guards']),proof['value']
    raise Unsupported('The requested integral or method is outside this transition')


PLANAR_PARAMETER_CAPTURE=r'([A-Za-z_]\w*)'
INTEGER=r'([1-9]\d*)'


def bind(task,fields,headings=(),extra_source=()):
    from cartesian_fields import vector_source
    vector_source(task,{'requested_output',*fields},headings,extra_source)


def theorem(name,reasons,value,**witness):
    return dict(theorem='method.'+name,argument=reasons,**witness),value


def fiber(lo,hi,left,right,orientation=1):
    return dict(outer=[lo,hi],inner=[left,right],orientation=orientation)


def compose_planar_measure(task,library,request):
    kind=task['kind']
    if kind in ('cartesian_slices','reverse_iterated_integral'):return cartesian_fibers(task,request)
    if kind in ('polar_change_bounds','polar_region_characterization','reverse_polar_integral','polar_integral_reduction'):
        return polar_fibers(task,request)
    if kind in ('area_map_ratio','specified_change_of_variables','region_mapping_proof','find_region_coordinates',
                'planar_integral_reduction'):
        return coordinate_reduction(task,request)
    if kind in ('planar_exact_integral','planar_area','bounded_region_area','lamina_mass','lamina_centroid',
                'centroid_locus','planar_moments','planar_section_area','moments_identity'):
        return planar_weighted_measure(task,request)
    return planar_integral_theory(task,request)


def cartesian_fibers(task,request):
    kind=task['kind'];want=task['requested_output']
    if task['integrand']!='f(x,y)':raise Unsupported('The same source density must remain in the transformed integral')
    if kind=='cartesian_slices':
        bind(task,{'integrand','region'},('Расставить пределы интегрирования в обоих порядках для заданной области.',))
        match=re.fullmatch(r'y bounded by x\^2 and '+INTEGER,task['region'])
        if not match or want!=['x_then_y','y_then_x']:raise Unsupported('Both directions and a bounded graph segment are required')
        goal=dict(kind=kind,integrand='f(x,y)',region={'inequalities':['x^2<=y','y<='+match[1]]},requested_output=want)
        plan=request('decompose the same Cartesian segment in both directions',goal)
        return theorem('inverted_monotone_fibers',['The horizontal chord lies above the parabola between both intersections.',
            'Use the checked fiber decomposition for the same source region.'],plan['value'],region=goal['region'])

    bind(task,{'integrand','integration_order','parameters','stated_conditions','transcription'},
         ('Изменить порядок интегрирования с сохранением ориентации.',))
    order=task['integration_order']
    if (want!=['y_then_x'] or len(order)!=2 or
            [r.get('variable') for r in order]!=['x','y'] or any(set(r)!={'variable','lower','upper'} for r in order)):
        raise Unsupported('The prescribed Cartesian source order must be retained')
    a,b=[str(order[0][k]) for k in ('lower','upper')];l,h=[str(order[1][k]) for k in ('lower','upper')]
    assumptions=task.get('stated_conditions',[]);params=task.get('parameters',[])
    message=['Invert the original boundary relations at fixed y.']
    if (a,b)==('0','1') and (p:=re.fullmatch(r'x\^'+INTEGER,l)) and (r:=re.fullmatch(r'x\^'+INTEGER,h)):
        if int(p[1])<=int(r[1]) or params or assumptions or task.get('transcription'):
            raise Unsupported('The powers need the stated ordering on [0,1]')
        # y>=x^p gives the upper inverse, while y<=x^q gives the lower inverse.
        strips=[fiber('0','1',f'y^(1/{r[1]})',f'y^(1/{p[1]})')]
        message+=['Both positive powers increase on [0,1]. Their inverse inequalities retain the whole ordered strip.']
    elif not (params or assumptions or task.get('transcription')) and (
            a.startswith('-') and re.fullmatch(INTEGER,b) and a=='-'+b and l.startswith('-sqrt(')
            and l=='-sqrt('+h+')'):
        radius=m.parse(b,None)
        raw=m.parse(h,None,['x'])
        if domain_conditions(raw) or not same_value(raw,m.add(m.power(radius,2),m.neg(m.power(X,2)))):
            raise Unsupported('The two symmetric graphs do not share the same original squared radius')
        cap=source(m.power(radius,2))
        strips=[fiber('-'+b,'0',f'-sqrt({cap}-y^2)',f'sqrt({cap}-y^2)'),
                fiber('0',cap,f'-sqrt({cap}-y)',f'sqrt({cap}-y)')]
        message+=['Below y=0 the nonnegative upper graph is automatic and the lower radical gives the squared bound.',
                  'Above y=0 the lower graph is automatic and the upper parabola gives the squared bound.']
    elif not (params or assumptions or task.get('transcription')) and h.startswith('sqrt('):
        A,B,L,H=m.parse(a,None),m.parse(b,None),m.parse(l,None,['x']),m.parse(h,None,['x'])
        R=m.add(B,m.neg(A));ctx=m.context({})
        if (H[0]!='sqrt' or domain_conditions(L) or domain_conditions(H[1])
                or not all(m.constant_defined(e,ctx) for e in (A,B,R))
                or m.sign(R,ctx)!=1 or not same_value(L,m.add(B,m.neg(X)))
                or not same_value(H[1],m.add(m.power(R,2),m.neg(m.power(m.add(X,m.neg(A)),2))))):
            raise Unsupported('A sloping chord and the upper circle on its specified half-interval are required')
        rad=source(R)
        strips=[fiber('0',rad,b+'-y',a+'+sqrt(('+rad+')^2-y^2)')]
        message+=['On the right half-circle, the vertical projection is [0,R]. The chord gives the lower inverse; the upper circle gives the upper inverse.',
                  'Their order follows from R−y≤sqrt(R²−y²) for 0≤y≤R.']
    elif (a,l,h)==('1','0','ln(x)') and not (params or assumptions or task.get('transcription')):
        right=m.parse(b,None)
        if m.sign(m.add(right,q(-1)),m.context({}))!=1:
            raise Unsupported('The original logarithmic interval is not positive and ordered')
        strips=[fiber('0',source(m.simplify(('ln',right))),'exp(y)',b)]
        message+=['On x≥1 the logarithm increases and its inverse is exp(y).']
    elif (a,b,l,h)==('0','2*pi','0','sin(x)') and not (params or assumptions or task.get('transcription')):
        strips=[fiber('0','1','asin(y)','pi-asin(y)'),
                fiber('-1','0','pi-asin(y)','2*pi+asin(y)',-1)]
        message+=['Split at π where the original oriented inner interval reverses.',
                  'Use the increasing and decreasing inverse branches on each half-wave, preserving the signed contribution.']
    elif (a,l,h)==('0','sqrt(2*a*x-x^2)','sqrt(2*a*x)') and params==['a'] and assumptions==['a>0'] and (
            task.get('transcription') in (None,'Printed bound is 2π; the key instead uses 2a. For 0<a<π a full real integral over the printed interval is undefined.')):
        L=m.parse(b,None);ctx=m.context({})
        if not m.constant_defined(L,ctx) or m.sign(L,ctx)!=1:raise Unsupported('The original upper x endpoint must be positive')
        condition='a>=('+b+')/2'
        strips=[dict(outer=['0','sqrt(2*a*('+b+'))'],inner_base=['y^2/(2*a)',b],
                     required_intersection='if y<a, intersect with x<=a-sqrt(a^2-y^2) or x>=a+sqrt(a^2-y^2)',
                     orientation=1)]
        return theorem('inverted_monotone_fibers',message+[
            'The lower square root is real on the full original interval exactly when its right endpoint is at most 2a.',
            'The upper square root gives the lower x threshold. The lower square root gives the exterior of a centered x interval when y<a.',
            'Intersect both derived bounds with the original finite interval, omitting empty pieces.'],
            dict(y_then_x=strips,condition=condition,otherwise='original real iterated integral undefined'),source_bounds=order)
    else:raise Unsupported('No verified inverse sequence for these original Cartesian edges')
    return theorem('inverted_monotone_fibers',message,dict(y_then_x=strips,integrand='f(x,y)'),source_bounds=order)


def polar_fibers(task,request):
    kind=task['kind'];want=task['requested_output']
    if kind=='polar_region_characterization':
        bind(task,set(),('Когда после перехода к полярным координатам пределы постоянны?',))
        if want!=['geometric_characterization']:raise Unsupported('The task asks for geometric characterization')
        return theorem('polar_active_boundaries',['A constant radial interval and a constant angular interval are a rectangle in the chart.',
            'A radial endpoint maps to a concentric circle and an angular endpoint to a ray. A zero radius or full turn gives the noted degenerations.'],
            dict(region='concentric annular sector; disk or annulus for a full angle, ordinary sector when the inner radius is zero'))
    if kind=='reverse_polar_integral':
        return reversed_polar_fibers(task)
    bind(task,{'integrand','region'},('Перейти к полярным координатам с x=r cosφ, y=r sinφ и расставить пределы.',
                                    'Перейти к полярным координатам и расставить пределы в обоих порядках.',
                                    'Полярной заменой свести двойной интеграл к однократному.'))
    f=task['integrand'];region=task['region']
    base=['Use r≥0 and the given angular window. The original map is one-to-one in its interior, with Jacobian r.',
          'Each endpoint of an inverse fiber follows by solving the same wall inequality in the other variable.']
    if kind=='polar_integral_reduction':
        if want!=['one_dimensional_integral']:raise Unsupported('The requested one-dimensional integral must be retained')
        if f=='f(sqrt(x^2+y^2))' and (w:=re.fullmatch(r'abs\(y\)<=abs\(x\),abs\(x\)<='+INTEGER,region)):
            A=w[1]
            return theorem('polar_active_boundaries',base+[
                'The two symmetric sectors have total angular length π at r≤A.',
                'For A≤r≤sqrt(2)A subtract four branches of length arccos(A/r).'],
                dict(radial_integrals=[dict(bounds=['0',A],density='pi*r*f(r)'),
                         dict(bounds=[A,'sqrt(2)*'+A],density=f'(pi-4*acos({A}/r))*r*f(r)')]))
        if f=='f(y/x)' and (w:=re.fullmatch(r'x\^2\+y\^2<=((?:'+INTEGER+r'\*)?)x',region)):
            A=w[2] or '1'
            return theorem('polar_active_boundaries',base+[
                'The offset disk gives −π/2<φ<π/2, 0<r<A cosφ. The quotient is tanφ on the interior.',
                'The radial measure contributes A² cos²φ/2. With u=tanφ the remaining Jacobian is (1+u²)^−1.',
                'The exceptional origin has zero area; keep the integrability requirement for the resulting unbounded moment.'],
                dict(variable='u',bounds=['-inf','+inf'],density=f'({A})^2*f(u)/(2*(1+u^2)^2)',scope='whenever the source integral exists'))
        raise Unsupported('The source weight is neither solely radial nor a quotient on the offset disk')
    one=want==['polar_integrand_with_jacobian','bounds']
    both=want==['polar_integrand_with_jacobian','angle_then_radius','radius_then_angle']
    if not (one or both) or f not in ('f(x,y)','f(sqrt(x^2+y^2))'):
        raise Unsupported('The original weight or both prescribed orders remain incomplete')
    density='r*f(r*cos(phi),r*sin(phi))' if f=='f(x,y)' else 'r*f(r)'
    forward=[];reverse=[]
    if w:=re.fullmatch(r'x\^2\+y\^2<='+PLANAR_PARAMETER_CAPTURE+r'\*x, \1>0',region):
        A=w[1];forward=[fiber('-pi/2','pi/2','0',f'{A}*cos(phi)')]
        reverse=[fiber('0',A,f'-acos(r/{A})',f'acos(r/{A})')]
        base+=['Divide the wall by positive r. Then solve cosφ≥r/A on its positive half-turn.']
    elif w:=re.fullmatch(r'0<=x<='+INTEGER+r',0<=y<=\1-x',region):
        A=w[1];forward=[fiber('0','pi/2','0',f'{A}/(cos(phi)+sin(phi))')]
        reverse=[fiber('0',f'{A}/sqrt(2)','0','pi/2'),
                 fiber(f'{A}/sqrt(2)',A,'0',f'pi/4-acos({A}/(sqrt(2)*r))'),
                 fiber(f'{A}/sqrt(2)',A,f'pi/4+acos({A}/(sqrt(2)*r))','pi/2')]
        base+=['The straight cap reduces to r sqrt(2)cos(φ−π/4)≤A. The angular window splits in two at larger radii.']
    elif w:=re.fullmatch(r'-'+PLANAR_PARAMETER_CAPTURE+r'<=x<=\1,x\^2/\1<=y<=\1',region):
        A=w[1]
        forward=[fiber('0','pi/4','0',f'{A}*sin(phi)/cos(phi)^2'),
                 fiber('pi/4','3*pi/4','0',f'{A}/sin(phi)'),
                 fiber('3*pi/4','pi','0',f'{A}*sin(phi)/cos(phi)^2')]
        base+=['The quadratic floor and horizontal cap imply the given x bound. The active radial cap changes where sin²φ=cos²φ.',
                'The symmetric vertical direction is governed by the horizontal cap. A nonempty original segment with its division requires A>0.']
    elif w:=re.fullmatch(r'0<=x<='+INTEGER+r',0<=y<=\1',region):
        A=w[1]
        forward=[fiber('0','pi/4','0',f'{A}/cos(phi)'),fiber('pi/4','pi/2','0',f'{A}/sin(phi)')]
        reverse=[fiber('0',A,'0','pi/2'),fiber(A,f'{A}*sqrt(2)',f'acos({A}/r)',f'asin({A}/r)')]
        base+=['Both coordinate caps must hold, so the active wall switches at the diagonal. At fixed r both angle inequalities are imposed.']
    elif region=='0<=x<=1,1-x<=y<=sqrt(1-x^2)':
        forward=[fiber('0','pi/2','1/(cos(phi)+sin(phi))','1')]
        reverse=[fiber('1/sqrt(2)','1','pi/4-acos(1/(sqrt(2)*r))','pi/4+acos(1/(sqrt(2)*r))')]
        base+=['The chord is a lower radial wall and the circle an upper wall. In the reverse order the angular arc is centered at π/4.']
    elif w:=re.fullmatch(r'0<=x<='+INTEGER+r',x<=y<=sqrt\(3\)\*x',region):
        A=w[1]
        forward=[fiber('pi/4','pi/3','0',f'{A}/cos(phi)')]
        reverse=[fiber('0',f'{A}*sqrt(2)','pi/4','pi/3'),fiber(f'{A}*sqrt(2)',f'2*{A}',f'acos({A}/r)','pi/3')]
        base+=['Two lines give the full angular wedge. At fixed radius the vertical line may exclude a lower angular portion.']
    elif w:=re.fullmatch(r'0<=x<='+INTEGER+r',0<=y<=x\^2',region):
        A=w[1];C=f'atan({A})';limit='asin((sqrt(1+4*r^2)-1)/(2*r))'
        forward=[fiber('0',C,'sin(phi)/cos(phi)^2',f'{A}/cos(phi)')]
        reverse=[fiber('0',A,'0',limit),fiber(A,f'{A}*sqrt(1+{A}^2)',f'acos({A}/r)',limit)]
        base+=['At positive r, the parabolic bound is equivalent to sinφ≤r(1−sin²φ). Its positive root gives one upper angle.',
                'The vertical cap gives the second restriction when r>A. The origin is the shared endpoint.']
    elif w:=re.fullmatch(r'right lobe bounded by \(x\^2\+y\^2\)\^2='+PLANAR_PARAMETER_CAPTURE+r'\^2\*\(x\^2-y\^2\), x>=0',region):
        A=w[1];L=f'abs({A})'
        forward=[fiber('-pi/4','pi/4','0',f'{L}*sqrt(cos(2*phi))')]
        reverse=[fiber('0',L,f'-acos(r^2/{A}^2)/2',f'acos(r^2/{A}^2)/2')]
        base+=['The selected lobe is the nonnegative radial interval about the positive x axis.',
                'The inverse angle needs A≠0. For A=0 the region has zero area.']
    else:raise Unsupported('The original walls are outside the verified polar intersections')
    if both and not reverse:raise Unsupported('The second polar order remains open')
    value=dict(integrand=density,coordinates=['r','phi'])
    if one:value['bounds']=forward
    else:value.update(angle_then_radius=forward,radius_then_angle=reverse)
    return theorem('polar_active_boundaries',base,value,source_region=region)


def reversed_polar_fibers(task):
    bind(task,{'integrand','integration_order','stated_conditions','transcription'},
         ('Изменить порядок в уже заданном полярном интеграле f(φ,r) dr, без добавления якобиана.',))
    b=task['integration_order'];conditions=task['stated_conditions'];f=task['integrand']
    if (task['requested_output']!=['radius_then_angle'] or len(b)!=2 or [d.get('variable') for d in b]!=['phi','r']
            or any(set(d)!={'variable','lower','upper'} for d in b) or b[1]['lower']!='0' or f not in ('f(phi,r)','(phi,r)')):
        raise Unsupported('The original polar measure and its prescribed order must be bound')
    lo,hi=b[0]['lower'],b[0]['upper'];cap=b[1]['upper']
    notice=None
    if f=='(phi,r)':
        if task.get('transcription') not in (None,'The printed inner integral has (phi,r) without a function name; reversal describes the same region for any integrable density.'):
            raise Unsupported('Preserve the original missing density symbol')
        notice='literal density symbol missing; same bounds for any integrable density'
    elif task.get('transcription'):
        raise Unsupported('The source adds a separate integrand interpretation')
    if (lo,hi)==('-pi/2','pi/2') and (w:=re.fullmatch(PLANAR_PARAMETER_CAPTURE+r'\*cos\(phi\)',cap)) and conditions==[w[1]+'>0']:
        A=w[1];section=fiber('0',A,f'-acos(r/{A})',f'acos(r/{A})')
        proof='On the printed half-turn the cosine is symmetric and decreases away from zero.'
    elif (lo,hi)==('0','pi/2') and (w:=re.fullmatch(PLANAR_PARAMETER_CAPTURE+r'\*sqrt\(sin\(2\*phi\)\)',cap)) and conditions==[w[1]+'>0']:
        A=w[1];section=fiber('0',A,f'asin(r^2/{A}^2)/2',f'pi/2-asin(r^2/{A}^2)/2')
        proof='Sin(2φ) on the first quadrant is nonnegative and increases then decreases; invert both branches.'
    elif lo=='0' and cap=='phi' and re.fullmatch(PLANAR_PARAMETER_CAPTURE,hi) and conditions==[f'0<{hi}<2*pi']:
        section=fiber('0',hi,'r',hi)
        proof='The original triangular inequalities exchange roles directly.'
    else:raise Unsupported('The inverse angular fiber requires a verified monotone split')
    return theorem('polar_active_boundaries',[proof,'The order changes in an already specified two-variable integral, so no extra factor r is inserted.'],
                   dict(radius_then_angle=[section],integrand=f,notice=notice))


def coordinate_reduction(task,request):
    kind=task['kind'];want=task['requested_output'];region=task.get('region')
    bases=['Use the inverse map on the complete original component and take the absolute Jacobian determinant.']
    if kind=='area_map_ratio':
        bind(task,{'region','map','stated_conditions'},
             ('Найти отношение площадей S′/S и его предел при h→0 для указанного квадрата и замены.',))
        names=task['stated_conditions']
        if (want!=['exact_area_ratio','limit'] or region!='a<x<a+h,b<y<b+h' or names!=['a>0','b>0','h>0']
                or set(task['map'])!={'u','v'}):
            raise Unsupported('Need the exact positive square and two coordinate functions')
        params=['a','b','h'];ctx=m.context(dict(variable='__planar',parameters=params,parameter_conditions=names))
        M=[monomial(m.parse(task['map'][s],None,['x','y',*params]),ctx) for s in ('u','v')]
        det=m.add(m.mul(M[0][1],M[1][2]),m.neg(m.mul(M[0][2],M[1][1])))
        total=m.mul(m.simplify(('abs',det)),m.mul(M[0][0],M[1][0]))
        if not m.nonzero(det,ctx):raise Unsupported('The logarithmic map is singular')
        powers=[m.add(M[0][i],M[1][i]) for i in (1,2)]
        a,b,h=(('s',s) for s in params)
        if any(m.contains(p,h) for p in powers):
            raise Unsupported('A shrinking-square limit with variable monomial exponents needs its own uniform estimate')
        moments=[positive_power_span(z,m.add(z,h),p,ctx) for z,p in zip((a,b),powers)]
        exact=m.simplify(m.div(m.mul(total,m.mul(*moments)),m.power(h,2)))
        corner=m.simplify(m.mul(total,m.mul(*[positive_power(z,m.add(p,q(-1))) for z,p in zip((a,b),powers)])))
        limit=corner
        if m.contains(corner,h):
            scaled=source(m.substitute(corner,{h:('v','h')}))
            goal=dict(kind='limit',variable='h',expression=scaled,parameters=['a','b'],parameter_conditions=['a>0','b>0'],
                      approach=dict(point='0',side='right'))
            limit=freeze(request('limit of positive monomial scale at the fixed lower corner',goal)['value'])
            if limit!='+inf' and not isinstance(limit,tuple):
                raise Unsupported('The scale limit must be a numerical expression or a signed infinity')
        return theorem('positive_monomial_rectangle',bases+[
            'Taking logarithms changes the monomial map to an affine map with nonzero determinant.',
            'The forward Jacobian separates into independent pure powers on the original square. Integrate each factor.',
            'The variable-independent spatial powers have a positive continuous mean tending to their lower-corner value.',
            'The positive ratio of the full mean and the lower-corner Jacobian tends to 1. If the map depends on h, verify the limit of the lower-corner Jacobian.'],
            dict(exact_area_ratio=exact,limit=limit),log_determinant=det,independent_moments=moments)
    if kind=='specified_change_of_variables':
        bind(task,{'region','map','integrand','stated_conditions'},
             ('Заменить переменные согласно условию и определить пределы двойного интеграла.',))
        if want!=['transformed_integrand_with_jacobian','bounds'] or task['integrand']!='f(x,y)':
            raise Unsupported('Need the integrand and all transformed limits for the prescribed map')
        mp=task['map'];conditions=task['stated_conditions']
        if mp=={'u':'x','v':'y/x'} and (w:=re.fullmatch(r'a<=x<=b,alpha\*x<=y<=beta\*x',region)) and (
                conditions==['0<a<b','0<alpha<beta']):
            return theorem('certified_planar_substitution',bases+[
                'The positive x guarantees the slope divisor is nonzero. The inequalities become a product of intervals.'],
                dict(transformed_integrand='u*f(u,u*v)',bounds=fiber('a','b','alpha','beta')),inverse=['u','u*v'],jacobian='u')
        if mp=={'u':'x+y','v':'x-y'} and not conditions and (
                w:=re.fullmatch(r'0<=x<='+INTEGER+r','+INTEGER+r'-x<=y<='+INTEGER+r'-x',region)):
            xcap,low,high=map(int,w.groups())
            if low>=high:raise Unsupported('The two sum levels are not ordered')
            return theorem('certified_planar_substitution',bases+[
                'Add x to each y constraint to get the interval in u. With given u, v=2x−u spans the stated affine interval.'],
                dict(transformed_integrand='f((u+v)/2,(u-v)/2)/2',bounds=fiber(str(low),str(high),'-u',f'{2*xcap}-u')),
                inverse=['(u+v)/2','(u-v)/2'],jacobian='1/2')
        if (mp=={'x':'u*cos(v)^4','y':'u*sin(v)^4'} and conditions==['a>0']
                and (w:=re.fullmatch(r'bounded by sqrt\(x\)\+sqrt\(y\)=sqrt\(a\), x='+INTEGER+r', y=0',region))):
            wall=w[1]
            return theorem('certified_planar_substitution',bases+[
                'In the first quadrant u=(sqrt(x)+sqrt(y))². At x>0 the positive fourth-root ratio gives the unique angle v.',
                'The source vertical line becomes u cos^4(v)=wall. It meets the upper arc only for a≥wall, and positive area requires a>wall.',
                'Differentiate both coordinate maps. The determinant is 4u cos³(v)sin³(v), nonnegative on the chart.'],
                dict(transformed_integrand='4*u*cos(v)^3*sin(v)^3*f(u*cos(v)^4,u*sin(v)^4)',
                     bounds=fiber('0',f'acos(({wall}/a)^(1/4))',f'{wall}/cos(v)^4','a'),condition=f'a>{wall}',
                     equality='area zero',below='the three stated curves do not bound the region'),map=mp)
        raise Unsupported('The prescribed map or any original domain condition has changed')
    if kind=='region_mapping_proof':
        bind(task,{'region','map','target_region'},('Показать, что замена переводит треугольник в единичный квадрат.',))
        if ((want,region,task['map'],task['target_region'])!=(
                ['region_equivalence','boundary_behavior'],'0<=x<=1,0<=y<=1-x',
                {'xi':'x+y','y':'xi*eta'},'0<=xi<=1,0<=eta<=1')):
            raise Unsupported('Need the original three edges, normalized sum and target square')
        return theorem('certified_planar_substitution',bases+[
            'For ξ>0, the triangle inequalities become 0<ξ≤1 and 0≤y/ξ≤1.',
            'Every point of the target with ξ>0 gives x=ξ(1−η), y=ξη in the triangle.',
            'The origin is the image of the full ξ=0 edge. It is a boundary degeneracy and has zero area.'],
            dict(inverse=['xi*(1-eta)','xi*eta'],exceptional_fiber='xi=0 maps to (0,0)',area_jacobian='xi'))
    if kind=='find_region_coordinates':
        bind(task,{'boundaries','stated_conditions'},
             ('Найти замену, превращающую криволинейный четырёхугольник в осепараллельный прямоугольник.',))
        walls=task['boundaries']
        if (want!=['coordinate_map','rectangle'] or task['stated_conditions']!=['x>0','y>0'] or len(walls)!=4
                or not (a:=re.fullmatch(r'x\*y='+INTEGER,walls[0])) or not (b:=re.fullmatch(r'x\*y='+INTEGER,walls[1]))
                or not (c:=re.fullmatch(r'x-y\+'+INTEGER+r'=0',walls[2])) or not (d:=re.fullmatch(r'x-y-'+INTEGER+r'=0',walls[3]))
                or int(a[1])>=int(b[1])):
            raise Unsupported('The positive product and difference levels must define the full rectangle')
        return theorem('certified_planar_substitution',bases+[
            'Take the two distinct boundary expressions as coordinates.',
            'The sum x+y is the positive square root of (x−y)²+4xy, giving one positive inverse for each target point.'],
            dict(map={'u':'x*y','v':'x-y'},rectangle=[[a[1],b[1]],['-'+c[1],d[1]]],
                 inverse=['(sqrt(v^2+4*u)+v)/2','(sqrt(v^2+4*u)-v)/2'],jacobian='1/sqrt(v^2+4*u)'))
    bind(task,{'integrand','region','stated_conditions'},('Подходящей заменой свести двойной интеграл к однократному.',))
    if want!=['one_dimensional_integral']:raise Unsupported('Need a one-dimensional consequence of the exact original region')
    f=task['integrand'];conditions=task['stated_conditions']
    if f=='f(x+y)' and not conditions and (w:=re.fullmatch(r'abs\(x\)\+abs\(y\)<='+INTEGER,region)):
        A=w[1]
        return theorem('certified_planar_substitution',bases+[
            'u=x+y and v=x−y give max(|u|,|v|)=|x|+|y|. The map covers the entire transformed square.',
            'The transverse width times the inverse determinant 1/2 leaves a constant weight.'],
            dict(bounds=['-'+A,A],density=A+'*f(u)'),map=['x+y','x-y'])
    if f=='f(a*x+b*y+c)' and conditions==['a^2+b^2!=0'] and (
            w:=re.fullmatch(r'x\^2\+y\^2<='+INTEGER,region)):
        A=m.simplify(('sqrt',m.parse(w[1],None)));a,b=('s','a'),('s','b')
        return theorem('certified_planar_substitution',bases+[
            'Use the two orthonormal axes parallel and perpendicular to (a,b); a²+b²≠0 makes the rotation well-defined.',
            'The disk is invariant. The transverse chord has length 2 sqrt(R²−u²).'],
            dict(bounds=[m.neg(A),A],density=f'2*sqrt({w[1]}-u^2)*f(c+u*sqrt(a^2+b^2))'),
            axis_normal=m.div(ONE,('sqrt',m.add(m.power(a,2),m.power(b,2)))))
    if conditions==['x>0','y>0'] and f=='f(x*y)' and re.fullmatch(r'xy=\d+,xy=\d+,y=x,y=\d+\*x',region):
        walls=region.replace('xy','x*y').split(',')
        cap=monomial_rectangle(walls,conditions)
        (lo,hi),(a,b)=cap['intervals'];ctx=cap['context']
        scale=m.div(positive_power_span(a,b,ZERO,ctx),m.simplify(('abs',cap['determinant'])))
        return theorem('positive_monomial_rectangle',bases+[
            'Use u=xy and v=y/x. The inverse monomial exponents show that xy=u and dxdy=du dv/(2v).',
            'After integrating 1/v over its independent interval only the original scalar density in u remains.'],
            dict(bounds=[lo,hi],density=source(scale)+'*f(u)'),rectangle=cap['intervals'])
    raise Unsupported('No verified transverse density for the stated scalar argument')


def positive_power(x,p):
    n=m.num(p)
    return m.power(x,n.numerator) if n is not None and n.denominator==1 else ('rpow',x,p)


def monomial(expr,ctx):
    """Extract the coefficient and powers only on the stated positive coordinate chart."""
    if not any(m.contains(expr,z) for z in (X,Y)):
        if not m.constant_defined(expr,ctx) or not positive_scalar(expr,ctx):
            raise Unsupported('A monomial coefficient must be defined and positive')
        return expr,ZERO,ZERO
    if expr in (X,Y):return ONE,ONE if expr==X else ZERO,ONE if expr==Y else ZERO
    op=expr[0]
    if op in ('mul','div'):
        a,x,y=monomial(expr[1],ctx);b,s,t=monomial(expr[2],ctx)
        if op=='mul':return m.mul(a,b),m.add(x,s),m.add(y,t)
        return m.div(a,b),m.add(x,m.neg(s)),m.add(y,m.neg(t))
    if op in ('sqrt','cbrt','pow','rpow'):
        p=q(1,2) if op=='sqrt' else q(1,3) if op=='cbrt' else q(expr[2]) if op=='pow' else expr[2]
        if not m.constant_defined(p,ctx):
            raise Unsupported('A monomial exponent is not a fixed real parameter')
        a,x,y=monomial(expr[1],ctx)
        return ONE if a==ONE else positive_power(a,p),m.mul(x,p),m.mul(y,p)
    raise Unsupported('The original term is not a positive monomial')


def ordered_conditions(conditions,params):
    facts=[]
    for item in conditions:
        if item in ('x>0','y>0','all parameters positive','positive parameters'):
            if item.endswith('positive'):facts.extend(p+'>0' for p in params)
            continue
        sides=item.split('<')
        if len(sides)>1 and '>' not in item and '=' not in item:
            for a,b in zip(sides,sides[1:]):
                facts.append(b+'>0' if a=='0' else f'({b})-({a})>0')
            if sides[0]=='0':facts.extend(b+'>0' for b in sides[1:])
        else:facts.append(item)
    return list(dict.fromkeys(facts))


def positive_power_span(a,b,p,ctx):
    if not all(m.constant_defined(z,ctx) and positive_scalar(z,ctx) for z in (a,b)):
        raise Unsupported('The normalized coordinate levels must both be positive')
    if p==ZERO:return m.simplify(('ln',m.div(b,a)))
    if not m.nonzero(p,ctx):raise Unsupported('The zero-exponent branch needs a separate parameter split')
    return m.simplify(m.div(m.add(positive_power(b,p),m.neg(positive_power(a,p))),p))


def positive_scalar(e,ctx):
    return m.sign(e,ctx)==1 or m.known_nonnegative(e,ctx) and m.nonzero(e,ctx)


def monomial_rectangle(walls,conditions):
    walls=[re.sub(r'\bxy\b','x*y',s) for s in walls]
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join(walls)+ ' '+' '.join(conditions)))-
                 {'x','y','pi','e','all','parameters','positive'}-m.FUNCTIONS-set(m.ALIASES))
    conditions=ordered_conditions(conditions,names)
    # Geometric levels a² and 2a² are positive exactly in the nondegenerate case.
    if any(s.endswith('=a^2') for s in walls) and 'a' in names:conditions.append('a!=0')
    ctx=m.context(dict(variable='__cell',parameters=names,parameter_conditions=conditions))
    levels={}
    for wall in walls:
        if wall.count('=')!=1:raise Unsupported('Each stated wall must be an equality of positive monomials')
        L,R=[monomial(m.parse(z,None,['x','y',*names]),ctx) for z in wall.split('=')]
        v=tuple(m.simplify(m.add(a,m.neg(b))) for a,b in zip(L[1:],R[1:]))
        if v==(ZERO,ZERO):raise Unsupported('A wall cannot be constant on the entire chart')
        levels.setdefault(v,[]).append(m.simplify(m.div(R[0],L[0])))
    if len(levels)!=2 or any(len(x)!=2 for x in levels.values()):
        raise Unsupported('The four walls do not define two independent pairs of levels')
    (a,b),(c,d)=levels
    D=m.simplify(m.add(m.mul(a,d),m.neg(m.mul(b,c))))
    if not m.nonzero(D,ctx):raise Unsupported('Prove that the log-coordinate determinant is nonzero')
    M=((m.div(d,D),m.div(m.neg(b),D)),(m.div(m.neg(c),D),m.div(a,D)))
    intervals=[]
    for l,h in levels.values():
        difference=m.simplify(m.add(h,m.neg(l)))
        sign=m.sign(difference,ctx)
        if sign is None:
            p,n=m.rational_form(difference)
            if p and n=={():1}:
                scale=abs(next(iter(p.values())))
                sign=m.sign(m.poly_expr({k:v/scale for k,v in p.items()}),ctx)
        if sign not in (-1,1):
            raise Unsupported('The original two coordinate levels have no proved order')
        intervals.append((l,h) if sign==1 else (h,l))
    return dict(parameters=names,condition_facts=conditions,context=ctx,levels=tuple(levels),intervals=intervals,
                determinant=D,inverse_exponents=M)


def monomial_moment(cell,nx,ny):
    ctx=cell['context'];e=cell['inverse_exponents']
    powers=[m.simplify(m.add(m.mul(q(nx+1),e[0][i]),m.mul(q(ny+1),e[1][i]))) for i in range(2)]
    moments=[positive_power_span(a,b,p,ctx) for (a,b),p in zip(cell['intervals'],powers)]
    return m.simplify(m.div(m.mul(*moments),('abs',cell['determinant']))),dict(powers=powers,independent_moments=moments)


T=('v','t')
S=('s','__transverse')
PI=m.PI
HALF=m.div(PI,q(2))
TURN=m.mul(q(2),PI)
COS=('cos',T)
SIN=('sin',T)


def chart(x,y,jac,outer,inner,parameters=(),conditions=(),copies=1):
    return dict(map=[x,y],jacobian=jac,outer=outer,inner=inner,parameters=list(parameters),
                conditions=list(conditions),copies=copies)


def fiber_density(original,bounds):
    """Integrate a polynomial in the transverse variable using exact finite moments."""
    p,d=m.rational_form(original);den=m.poly_expr(d);a,b=bounds
    if m.contains(den,S):raise Unsupported('The transverse moment has a denominator depending on its coordinate')
    value=ZERO
    for monomial,c in p.items():
        remaining=dict(monomial);j=remaining.pop(S,0)+1
        factor=m.poly_expr({tuple(remaining.items()):c/j})
        if m.contains(factor,S):raise Unsupported('The transverse weight is not polynomial on this fiber')
        value=m.add(value,m.mul(factor,m.add(m.power(b,j),m.neg(m.power(a,j)))))
    return m.simplify(m.div(value,den))


def certified_weighted_fibers(cells,weights,request):
    """Apply all requested weights to the same proven coverage and replay each moment."""
    values=dict.fromkeys(weights,ZERO);checks=[]
    for i,C in enumerate(cells):
        names=C['parameters'];conditions=C['conditions'];xy=dict(zip((X,Y),C['map'],strict=True))
        ctx=m.context(dict(variable='__moment',parameters=['x','y',*names],parameter_conditions=conditions))
        for name,w in weights.items():
            if any(not known_guard(g,ctx) for g in domain_conditions(w)):
                raise Unsupported('An original restriction of the weight would be erased by the moment')
            density=fiber_density(m.mul(m.substitute(w,xy),C['jacobian']),C['inner'])
            step,value=curve_chart_moment(density,'t',names,conditions,*C['outer'],request,
                                          'integrate remaining moment '+str(i)+' '+name)
            values[name]=m.simplify(m.add(values[name],m.mul(q(C['copies']),value)))
            checks.append(dict(chart=i,weight=name,transverse_density=density,integral=step))
    return values,checks


def planar_weighted_measure(task,request):
    kind=task['kind'];want=task['requested_output'];f=task.get('integrand')
    region=task.get('region');walls=task.get('boundaries');method=task.get('method_requirement')
    if kind=='moments_identity':return planar_moment_identity(task)
    if kind=='centroid_locus':return moving_centroid(task,request)
    if kind=='planar_section_area':return section_plane_area(task)
    if kind=='lamina_mass':return radial_lamina_mass(task,request)
    if kind=='bounded_region_area':
        bind(task,{'curve','stated_conditions'},('Найти площадь области, ограниченной кривой.',))
        name=r'([A-Za-z_]\w*)'
        arc=re.fullmatch(r'abs\(([xy])\)\^'+name+r'\+abs\(([xy])\)\^\2='+name+r'\^\2',
                         task['curve'].replace(' ',''))
        if want!=['area'] or not arc:
            raise Unsupported('The symmetric positive-powered curve and its exponent domain are required')
        x,n,y,a=arc.groups()
        if x==y or len({x,y,n,a})!=4 or sorted(task['stated_conditions'])!=sorted((n+'>0',a+'>0')):
            raise Unsupported('The scale and exponent of the symmetric curve must be distinct and positive')
        return powered_simplex_measure(a,a,n,4,['area'],substitution=f'u=(|{x}|/{a})^{n}, v=(|{y}|/{a})^{n}')
    plan_fields={'region','integrand','stated_conditions','transcription'}
    if kind=='planar_area':
        bind(task,{'boundaries','stated_conditions','method_requirement'},('Найти площадь фигуры, ограниченной указанными кривыми.',))
        if want!=['exact_area']:raise Unsupported('The exact area and prescribed method are required')
        f='1'
        if solved:=compound_polar_area(task):return solved
        positive_component={'x>0','y>0'}<=set(task.get('stated_conditions',[]))
        if method=='appropriate_change_of_variables' or (method is None and len(walls)==4 and positive_component):
            return mapped_planar_area(task,request)
        if method=='generalized_polar_x=A*r*cos(phi)^alpha_y=B*r*sin(phi)^alpha':
            return generalized_powered_area(task,request)
        if method not in (None,'polar_coordinates'):raise Unsupported('The prescribed area method is unrecognized')
    elif kind=='planar_exact_integral':
        bind(task,plan_fields,('Вычислить двойной интеграл.','Вычислить двойной интеграл по области, заданной геометрически.'))
        if want!=['exact_integral']:raise Unsupported('The ordinary exact planar moment was requested')
        if alt:=nonpolynomial_fiber_measure(task,request):return alt
    elif kind in ('lamina_centroid','planar_moments'):
        bind(task,{'region','density','axis'},('Найти обе координаты центра масс.',
            'Найти указанные геометрические моменты площади однородной фигуры.',
            'Найти момент равностороннего треугольника со стороной a относительно прямой через центр масс под углом α к высоте.'))
        if alt:=special_lamina_moments(task,request):return alt
        if task.get('density')!=('constant' if kind=='lamina_centroid' else 1) or task.get('axis') is not None:
            raise Unsupported('The original weights and axis obligations remain')
    else:raise Unsupported('No source planar moment for the original requested output')

    terms={'mass':ONE,'x':X,'y':Y}
    if kind=='lamina_centroid' and want==['centroid_coordinates']:weights=terms
    elif kind=='planar_moments' and want==['inertia_x','inertia_y']:weights={'inertia_x':m.power(Y,2),'inertia_y':m.power(X,2)}
    elif kind=='planar_moments' and want==['product_moment_xy']:weights={'product_moment_xy':m.mul(X,Y)}
    elif kind=='planar_moments' and want==['polar_moment_about_origin']:weights={'polar_moment':m.dot((X,Y),(X,Y))}
    elif kind=='planar_area':weights={'area':ONE}
    else:weights=None
    cases,proof=planar_moment_chart(region,walls,task.get('stated_conditions',[]),method,kind)
    if weights is None:weights={'exact_integral':m.parse(f,None,['x','y',*cases[0]['parameters']])}
    values,moments=certified_weighted_fibers(cases,weights,request)
    if kind=='lamina_centroid':
        C=cases[0];ctx=m.context(dict(variable='__moment',parameters=C['parameters'],parameter_conditions=C['conditions']))
        if not positive_scalar(values['mass'],ctx):
            raise Unsupported('Positive mass needs a nondegenerate original region')
        values=dict(centroid_coordinates=[m.simplify(m.div(values[v],values['mass'])) for v in 'xy'])
        if region.endswith(',phi=0'):
            x,y=values['centroid_coordinates']
            values['other_side_of_ray']=[x,m.neg(y)]
    return theorem('verified_fiber_moments',[proof,
        'In each chart the transverse weight is a finite polynomial. Integrate each power on the proved fiber bounds, with the absolute Jacobian.',
        'Integrate the remaining density on its outer interval and sum the disjoint pieces.'],values,cells=cases,weighted_moments=moments)


def planar_moment_chart(region,walls,conditions,method,kind):
    """Construct charts used by several requests, without changing the density or method."""
    square=lambda e:m.power(e,2)
    minus=lambda a,b:m.add(a,m.neg(b))
    sym=lambda p:('s',p)
    if kind=='planar_exact_integral' and (w:=re.fullmatch(fr'bounded by y\^2=2\*{PLANAR_PARAMETER_CAPTURE}\*x and x=\1/2',region)) and (
            conditions==[w[1]+'>0']):
        A=sym(w[1]);R=m.div(A,q(2))
        C=chart(S,m.mul(A,T),A,(q(-1),ONE),(m.mul(R,square(T)),R),w.groups(),conditions)
        return [C],'The vertical cap is x=p/2 and the parabolic inequality gives p*t²/2≤x≤p/2 with y=p*t, −1≤t≤1.'
    if kind=='planar_exact_integral' and (w:=re.fullmatch(fr'parallelogram with sides y=x,y=x\+{PLANAR_PARAMETER_CAPTURE},y=\1,y=3\*\1',region)) and (
            conditions==[w[1]+'>0']):
        A=sym(w[1]);C=chart(m.mul(A,minus(T,S)),m.mul(A,T),square(A),(ONE,q(3)),(ZERO,ONE),w.groups(),conditions)
        return [C],'The two original wall labels y and y−x give independent normalized intervals.'
    cycloid={
        'planar_exact_integral':fr'x-axis and first cycloid arch x={PLANAR_PARAMETER_CAPTURE}\*\(t-sin\(t\)\), y=\1\*\(1-cos\(t\)\), 0<=t<=2\*pi',
        'lamina_centroid':fr'cycloidal arch x={PLANAR_PARAMETER_CAPTURE}\*\(t-sin\(t\)\),y=\1\*\(1-cos\(t\)\),0<=t<=2\*pi and y=0',
    }
    if kind in cycloid and not conditions and (w:=re.fullmatch(cycloid[kind],region)):
        A=sym(w[1]);H=minus(ONE,COS);assumptions=[w[1]+'!=0'] if kind=='lamina_centroid' else []
        C=chart(m.mul(A,minus(T,SIN)),m.mul(A,m.mul(H,S)),m.mul(square(A),square(H)),
                (ZERO,TURN),(ZERO,ONE),w.groups(),assumptions)
        return [C],'The monotone horizontal coordinate has derivative a(1−cos(t)). The transverse parameter measures the fraction of the height, giving Jacobian a²(1−cos(t))².'
    if kind=='planar_exact_integral' and region=='bounded by y^2=2*x, x+y=4, x+y=12' and not conditions:
        # The square-root coordinate makes both the transverse bounds and the pullback polynomial.
        C=chart(minus(m.div(minus(square(T),ONE),q(2)),S),S,T,(q(3),q(5)),
                (m.add(q(-1),m.neg(T)),m.add(q(-1),T)))
        return [C],'Use x+y=(t²−1)/2. The two sum walls give 3≤t≤5 and the parabola gives |y+1|≤t.'
    if ((kind=='planar_exact_integral' and (w:=re.fullmatch(r'bounded by x\*y=1 and x\+y=(.+)',region)) and not conditions)
            or (kind=='planar_area' and method is None and len(walls)==2 and
                (s:=re.fullmatch(fr'x\*y={PLANAR_PARAMETER_CAPTURE}\^2',walls[0])) and
                (w:=re.fullmatch(fr'x\+y=(.+)\*{s[1]}/2',walls[1])) and conditions==[s[1]+'>0'])):
        if kind=='planar_area':
            pars=s.groups();A=sym(s[1]);cap=m.parse(w[1]+'/2',None)
        else:pars=();A=ONE;cap=m.parse(w[1],None)
        K=minus(square(cap),q(4));ctx=m.context({})
        if not m.constant_defined(cap,ctx) or m.sign(minus(cap,q(2)),ctx)!=1:
            raise Unsupported('The line must cross the positive hyperbola at two distinct points')
        lo,hi=(m.simplify(m.div(m.add(cap,m.mul(q(i),('sqrt',K))),q(2))) for i in (-1,1))
        C=chart(m.mul(A,T),m.mul(A,S),square(A),(lo,hi),(m.div(ONE,T),minus(cap,T)),pars,conditions)
        return [C],'After positive scaling, the two intersections are the roots of t²−cap*t+1. The bounded fiber is between the reciprocal and the upper line.'
    if (kind=='planar_area' and method is None and walls and len(walls)==2 and (
            p:=re.fullmatch(fr'y\^2=2\*{PLANAR_PARAMETER_CAPTURE}\*x\+\1\^2',walls[0])) and (
            r:=re.fullmatch(fr'y\^2=-2\*{PLANAR_PARAMETER_CAPTURE}\*x\+\1\^2',walls[1])) and conditions==[p[1]+'>0',r[1]+'>0']):
        P,Q=map(sym,(p[1],r[1]));H=('sqrt',m.mul(P,Q));Z=m.mul(m.mul(P,Q),square(T))
        C=chart(S,m.mul(H,T),H,(q(-1),ONE),(m.div(minus(Z,square(P)),m.mul(q(2),P)),
                m.div(minus(square(Q),Z),m.mul(q(2),Q))),[p[1],r[1]],conditions)
        return [C],'Both parabolic walls are affine functions of y² when solved for x. Their width has positive factor 1−t² for y=sqrt(pq)t.'
    if (kind=='planar_moments' and (w:=re.fullmatch(fr'\(x-{PLANAR_PARAMETER_CAPTURE}\)\^2\+\(y-\1\)\^2=\1\^2,x=0,y=0; 0<=x<=\1',region))):
        A=sym(w[1]);C=chart(m.mul(A,minus(ONE,SIN)),m.mul(A,S),m.mul(square(A),COS),
                    (ZERO,HALF),(ZERO,minus(ONE,COS)),w.groups())
        return [C],'The short circle arc touches both axes, with x=a(1−sin t), y=a(1−cos t). The stated x-range fixes the bounded corner and the nonnegative Jacobian.'
    if (kind=='planar_moments' and (w:=re.fullmatch(fr'x/{PLANAR_PARAMETER_CAPTURE}\+y/{PLANAR_PARAMETER_CAPTURE}=1,x/{PLANAR_PARAMETER_CAPTURE}\+y/\2=1,y=0; \1>0,\3>0,\2>0',region))):
        l,h,r=map(sym,w.groups())
        # Parameterize the interval between the lines with an affine transverse fraction.
        B=minus(ONE,T);delta=minus(r,l)
        C=chart(m.mul(B,m.add(l,m.mul(delta,S))),m.mul(h,T),m.mul(h,m.mul(('abs',delta),B)),
                (ZERO,ONE),(ZERO,ONE),w.groups(),[z+'>0' for z in w.groups()])
        return [C],'At y=h*t both x-intercepts shrink by 1−t. The signed coefficient b2−b1 can have either sign, so keep its absolute value in the Jacobian.'
    if (kind=='planar_moments' and (w:=re.fullmatch(fr'{PLANAR_PARAMETER_CAPTURE}\*y=x\^2,\1\*x=y\^2; \1>0',region))):
        A=sym(w[1]);C=chart(m.mul(A,square(T)),m.mul(A,S),m.mul(q(2),m.mul(square(A),T)),
                         (ZERO,ONE),(m.power(T,4),T),w.groups(),[w[1]+'>0'])
        return [C],'The two positive parabolic arcs meet at the origin and at (a,a). Setting x=a*t² leaves ordered polynomial y bounds.'
    # A single radial geometry can supply area, ordinary moments or centroid weights.
    r=None;outer=None;names=();facts=[];copies=1
    if kind=='planar_moments' and (w:=re.fullmatch(fr'r={PLANAR_PARAMETER_CAPTURE}\*\(1\+cos\(phi\)\)',region)):
        A=sym(w[1]);r=m.mul(A,m.add(ONE,COS));outer=(ZERO,TURN);names=w.groups();facts=[w[1]+'>0']
        note='The complete cardioid uses one full angle and the nonnegative radial segment on each ray.'
    elif kind=='lamina_centroid' and (w:=re.fullmatch(fr'r={PLANAR_PARAMETER_CAPTURE}\*\(1\+cos\(phi\)\),phi=0',region)):
        A=sym(w[1]);r=m.mul(A,m.add(ONE,COS));outer=(ZERO,PI);names=w.groups();facts=[w[1]+'>0']
        note='The upper component cut by the stated ray uses 0≤φ≤π. Its lower reflection has the opposite vertical centroid.'
    elif kind=='planar_moments' and (w:=re.fullmatch(fr'\(x\^2\+y\^2\)\^2={PLANAR_PARAMETER_CAPTURE}\^2\*\(x\^2-y\^2\)',region)):
        if conditions:raise Unsupported('An additional lobe restriction was not recognized')
        r=m.mul(('abs',sym(w[1])),('sqrt',('cos',m.mul(q(2),T))));angle=m.div(PI,q(4))
        outer=(m.neg(angle),angle);names=w.groups();copies=2
        note='Both lemniscate lobes are opposite rotations of the same nonnegative radial chart. A polar moment is invariant under this rotation.'
    elif kind=='planar_area' and method=='polar_coordinates' and len(walls)==1 and (
            w:=re.fullmatch(fr'\(x\^2\+y\^2\)\^2={PLANAR_PARAMETER_CAPTURE}\*\(x\^3-3\*x\*y\^2\)',walls[0])) and conditions==[w[1]+'>0']:
        r=m.mul(sym(w[1]),('cos',m.mul(q(3),T)));outer=(m.neg(m.div(PI,q(6))),m.div(PI,q(6)))
        names=w.groups();facts=conditions;copies=3
        note='The polar wall is r=a cos(3φ) on each positive sector. The three sectors are rotated copies for area.'
    elif kind=='planar_area' and method=='polar_coordinates' and len(walls)==2 and (
            w:=re.fullmatch(fr'\(x\^2\+y\^2\)\^2=2\*{PLANAR_PARAMETER_CAPTURE}\^2\*\(x\^2-y\^2\)',walls[0])) and walls[1]=='x^2+y^2>='+w[1]+'^2' and not conditions:
        A2=square(sym(w[1]));top=m.mul(m.mul(q(2),A2),('cos',m.mul(q(2),T)));angle=m.div(PI,q(6))
        C=chart(ZERO,ZERO,q(1,2),(m.neg(angle),angle),(A2,top),w.groups(),[],2)
        return [C],'Use the squared radius as transverse coordinate. Each of the two lobes contributes where 2cos(2φ)≥1.'
    if r is not None:return [chart(m.mul(S,COS),m.mul(S,SIN),S,outer,(ZERO,r),names,facts,copies)],note
    raise Unsupported('No proved weighted fiber chart for the full source geometry')


def powered_simplex_measure(a,b,n,copies,want,substitution):
    if want!=['area']:raise Unsupported('An area of the full stated powered component is required')
    area=f'{copies}*abs({a}*{b})*Gamma(1+1/({n}))^2/Gamma(1+2/({n}))'
    return theorem('powered_simplex_moments',[
        'In the chosen sign component the powered coordinates cover u,v≥0, u+v≤1 once.',
        'The inverse derivative in each coordinate supplies the independent factor u^(1/n−1) or v^(1/n−1).',
        'Integrate by the simplex beta identity and multiply by the number of disjoint equal components. The endpoint powers are integrable since n>0.'],
        dict(area=area),substitution=substitution,copies=copies)


def nonpolynomial_fiber_measure(task,request):
    region=task['region'];f=task['integrand'];conds=task.get('stated_conditions',[])
    if (w:=re.fullmatch(fr'coordinate axes and the shorter arc between tangencies of the circle centered at \({PLANAR_PARAMETER_CAPTURE},\1\), radius \1',region)):
        a=w[1];A=('s',a);expected=f'1/sqrt(2*{a}-x)'
        if f!=expected or conds!=[a+'>0']:raise Unsupported('The original reciprocal root and positive radius must match the short arc')
        return theorem('verified_fiber_moments',[
            'Between the axes and the shorter arc, the upper vertical graph on [0,a] is a−sqrt(x(2a−x)).',
            'The positive denominator sqrt(2a−x) cancels only its matching factor inside the product, leaving a/sqrt(2a−x)−sqrt(x).',
            'The two endpoint antiderivatives give the exact integral.'],dict(exact_integral=m.mul(positive_power(A,q(3,2)),
            m.add(m.mul(q(2),('sqrt',q(2))),q(-8,3)))))
    if f=='abs(x)+abs(y)' and not conds and (w:=re.fullmatch(r'abs\(x\)\+abs\(y\)<='+INTEGER,region)):
        R=q(int(w[1]))
        return theorem('verified_fiber_moments',[
            'Four equal reflected triangles cover the diamond, and the absolute weight is unchanged under those reflections.',
            'In the positive triangle use s=x+y. The x interval has length s and the weight equals s, giving 4 integral of s².'],
            dict(exact_integral=m.mul(q(4,3),m.power(R,3))))
    if (w:=re.fullmatch(fr'ellipse with bounding curve x\^2/{PLANAR_PARAMETER_CAPTURE}\^2\+y\^2/{PLANAR_PARAMETER_CAPTURE}\^2=1',region)):
        a,b=w.groups()
        if f!=f'sqrt(1-x^2/{a}^2-y^2/{b}^2)' or conds:raise Unsupported('The original normalized positive radial weight did not match')
        return theorem('verified_fiber_moments',[
            'Divide by the nonzero coordinate scales. The ellipse becomes the unit disk with measure |ab| dxdy.',
            'The square root is defined throughout the disk by construction. The radial density is r sqrt(1−r²), whose integral is 1/3.'],
            dict(exact_integral=m.mul(m.mul(q(2,3),PI),('abs',m.mul(('s',a),('s',b)))),scale_domain=f'{a}*{b}!=0'))
    if (f,region,conds)==('x^2+y^2','x^4+y^4<=1',[]):
        return theorem('powered_simplex_moments',[
            'By exchange symmetry and reflection the integral is eight times the x² moment of one positive quadrant.',
            'The y height is (1−x⁴)^(1/4). Put u=x⁴, giving 2 B(3/4,5/4).',
            'Gamma recurrence and reflection give π/sqrt(2).'],dict(exact_integral=m.div(PI,('sqrt',q(2)))))
    if (f,region,conds)==('abs(cos(x+y))','0<=x<=pi,0<=y<=pi',[]):
        return theorem('sign_partition_moments',[
            'For each fixed x the y interval translates to one full period of |cos|. Its mean integral over a period is 2.',
            'The second integral multiplies by the unchanged width π.'],dict(exact_integral=TURN))
    if (f,region,conds)==('abs((x+y)/sqrt(2)-x^2-y^2)','x^2+y^2<=1',[]):
        return theorem('sign_partition_moments',[
            'Rotate the first linear coordinate to x. Over the full disk the signed weight integrates to −π/2 by odd symmetry.',
            'The positive part is on the right half-turn and 0≤r≤cos(φ). Its radial integral is cos⁴(φ)/12, giving π/32.',
            'Twice the positive integral minus the signed full integral equals the absolute integral.'],
            dict(exact_integral=m.mul(q(9,16),PI)))
    if (f,region,conds)==('sign(x^2-y^2+2)','x^2+y^2<=4',[]):
        return theorem('sign_partition_moments',[
            'The negative set has two congruent angular strips about the vertical directions, each |t|<π/6.',
            'The negative radius runs from sqrt(2/cos(2t)) to 2. Its area is 4π/3−2 ln(2+sqrt(3)) counting both strips.',
            'The zero set has zero area. Subtract twice the negative area from the unsigned disk area.'],
            dict(exact_integral=m.add(m.mul(q(4,3),PI),m.mul(q(4),('ln',m.add(q(2),('sqrt',q(3))))))))
    if f=='floor(x+y)' and not conds and (w:=re.fullmatch(r'0<=x<='+INTEGER+r',0<=y<=\1',region)):
        L=int(w[1])
        return theorem('sign_partition_moments',[
            'Central reflection changes s=x+y to 2L−s. Away from integer levels floor(s)+floor(2L−s)=2L−1.',
            'The line exceptions have measure zero. Integrate the constant pair over the complete square.'],
            dict(exact_integral=q(L*L*(2*L-1),2)))
    if f=='sqrt(abs(y-x^2))' and not conds:
        if region=='abs(x)<=1,0<=y<=2' and not task.get('transcription'):
            return theorem('sign_partition_moments',[
                'Split each vertical fiber at y=x², where the absolute-value sign changes. Integrate the two root powers.',
                'The resulting density is 2/3 times |x|³+(2−x²)^(3/2). Apply even symmetry and x=sqrt(2)sin(t), 0≤t≤π/4.',
                'The fourth cosine moment gives the remaining elementary integral.'],
                dict(exact_integral=m.add(q(5,3),m.div(PI,q(2)))))
        if (w:=re.fullmatch(r'x\^2<=y<='+INTEGER,region)) and task.get('transcription') in (
                None,'Bars in the literal condition look like absolute value; the discontinuous-functions heading and key support a separate floor interpretation.'):
            A=int(w[1])
            return theorem('sign_partition_moments',[
                'In the original parabolic segment the absolute value is always y−x².',
                'Use t=y−x² as one coordinate. For 0≤t≤A the horizontal width is 2sqrt(A−t).',
                'Its beta moment with sqrt(t) gives πA²/4 on the literal domain.'],
                dict(exact_integral=m.mul(q(A*A,4),PI)))
    return None


def mapped_planar_area(task,request):
    walls=task['boundaries'];conditions=task['stated_conditions']
    if len(walls)!=4:raise Unsupported('Two pairs of coordinate levels are needed')
    if (walls==['x+y=a','x+y=b','y=alpha*x','y=beta*x'] and conditions==['0<a<b','0<alpha<beta']):
        a,b,c,d=(('s',v) for v in ('a','b','alpha','beta'))
        A=m.mul(m.div(m.add(m.power(b,2),m.neg(m.power(a,2))),q(2)),
                m.add(m.div(ONE,m.add(ONE,c)),m.neg(m.div(ONE,m.add(ONE,d)))))
        return theorem('certified_planar_substitution',[
            'The positive sum and slope level pairs give u=x+y and v=y/x.',
            'The inverse (u/(1+v),uv/(1+v)) has positive Jacobian u/(1+v)². Both intervals follow from the original four boundaries.',
            'Integrate the two separated positive factors.'],dict(area=m.simplify(A)),rectangle=[['a','b'],['alpha','beta']])
    if (walls[:2]==['sqrt(x/a)+sqrt(y/b)=1','sqrt(x/a)+sqrt(y/b)=2'] and walls[2:]==['x/a=y/b','4*x/a=y/b']
            and conditions==['a>0','b>0']):
        return powered_sum_slope_area('a','b',q(1,2),1,2,1,2)
    if (walls==['(x/a)^(2/3)+(y/b)^(2/3)=1','(x/a)^(2/3)+(y/b)^(2/3)=4','x/a=y/b','8*x/a=y/b']
            and conditions==['x>0','y>0']):
        return powered_sum_slope_area('a','b',q(2,3),1,4,1,4)
    explicit='x>0' in conditions and 'y>0' in conditions
    natural=(all(s.startswith('y^2=2*') for s in walls[:2]) and all(s.startswith('x^2=2*') for s in walls[2:]) or
             all(s.startswith('x^2=') and s.endswith('*y') for s in walls[:2]) and
             all(s.startswith('x^3=') and s.endswith('*y^2') for s in walls[2:]))
    powers=all(s.startswith('y=') for s in walls) and all('x^p' in s for s in walls[:2]) and all('x^q' in s for s in walls[2:])
    if not (explicit or natural or powers):
        raise Unsupported('The positive monomial chart needs explicit or implied coordinate signs')
    cell=monomial_rectangle(walls,conditions)
    area,moments=monomial_moment(cell,0,0)
    result=dict(area=area)
    if 'a!=0' in cell['condition_facts']:
        result.update(parameter_condition='a!=0',degenerate='at a=0 the positive product interval is empty')
    if powers and not explicit:
        note='This area is per positive-base component. When both exponents admit negative bases and give the same sign there, the reflected component has the same area.'
        result.update(scope='positive real powers as stated on x>0',
                      total_with_two_real_components=m.mul(q(2),area),
                      additional_component_condition='both powers admit negative x and have equal signs there')
    else:note='The nonnegative coordinate powers in the source axes and the stated signs pick the complete positive component away from the origin.'
    return theorem('positive_monomial_rectangle',[
        'After taking logarithms, each wall becomes one affine level of a two-by-two independent map.',
        'Invert the exponent matrix and evaluate the Jacobian xy/(|det M|uv) on the whole rectangle.',
        'The area is the product of the two checked power moments.',note],result,
        rectangle=cell['intervals'],inverse_exponents=cell['inverse_exponents'],log_determinant=cell['determinant'],moments=moments)


def powered_sum_slope_area(a,b,n,l,h,c,d):
    ref=('s',a),('s',b)
    if (n,l,h,c,d)==(q(1,2),1,2,1,2):
        value=m.mul(q(65,108),m.mul(*ref));formula='4ab*s^3*t/(1+t)^4'
        evidence='The rational t moment is 13/324 and the s cubic moment is 15/4.'
        result=dict(area=m.simplify(value))
    else:
        A=m.add(m.mul(q(189,16),m.add(('atan',q(2)),m.neg(m.div(PI,q(4))))),q(567,200))
        value=m.mul(A,('abs',m.mul(*ref)));formula='9|ab|*s^2*sqrt(t)/(4*(1+t)^3)'
        evidence='The t moment uses t=tan²(θ) and reduces to (1−cos(4θ))/4. Because x,y>0 and the two original slopes have positive multiples, the two scale signs must agree.'
        result=dict(cases=[
            dict(condition=f'{a}*{b}>0',area=m.simplify(value)),
            dict(condition=f'{a}*{b}<0',region='the prescribed slope boundaries have no positive-quadrant points'),
            dict(condition=f'{a}*{b}=0',region='original coordinate quotients undefined'),
        ])
    return theorem('positive_monomial_rectangle',[
        'First set U=(x/a)^n, V=(y/b)^n using the real branch fixed by the original walls.',
        'Then take s=U+V, t=V/U. The rectangular intervals come from the two sum and two slope levels.',
        'Multiply the inverse power and affine-fraction determinants; the two moments separate.',evidence],
        result,rectangle=[[l,h],[c,d]],jacobian=formula)


def generalized_powered_area(task,request):
    walls=task['boundaries'];conditions=task['stated_conditions'];A,B,H,K=(('s',s) for s in 'abhk')
    if conditions==['all parameters positive'] and walls==['(x/a)^(1/4)+(y/b)^(1/4)=1','x=0','y=0']:
        plan,value=powered_simplex_measure('a','b','1/4',1,['area'],
                                             'x=a*r*cos(phi)^8, y=b*r*sin(phi)^8')
        value['area']=m.mul(q(1,70),m.mul(A,B))
        plan['argument'].insert(0,'Use α=8 in the prescribed generalized polar chart so the sum of fourth roots equals r^(1/4).')
        return plan,value
    if conditions==['all parameters positive'] and walls==['x^2/a^2+y^2/b^2=x/h+y/k']:
        moment=m.add(m.power(m.div(A,H),2),m.power(m.div(B,K),2))
        return theorem('generalized_polar_area',[
            'Use x=ar cosφ,y=br sinφ. The radial cap is (a/h)cosφ+(b/k)sinφ on its positive half-turn.',
            'Rotate the angle to write the cap as its amplitude times cosφ. The squared cosine moment on a positive half-turn is π/2.',
            'The radial integral and the original scale factors give the area.'],
            dict(area=m.mul(m.div(PI,q(4)),m.mul(m.mul(A,B),moment))),alpha=1)
    if conditions==['all parameters positive','x>0','y>0'] and walls in (
            ['(x/a+y/b)^4=x^2/h^2+y^2/k^2'],['(x/a+y/b)^4=x^2/h^2-y^2/k^2']):
        plus='+' in walls[0].split('=')[1];c,d=m.div(A,H),m.div(B,K)
        C,D=m.power(c,2),m.power(d,2)
        moment=m.div(m.add(C,D),q(3)) if plus else m.div(m.mul(m.power(c,3),m.add(c,m.mul(q(2),d))),
                                                        m.mul(q(3),m.power(m.add(c,d),2)))
        return theorem('generalized_polar_area',[
            'Use α=2 and t=cos²φ, so x=art,y=br(1−t). After dividing by positive r² the cap for r² is quadratic in t.',
            'The allowed t interval is [0,1] for the sum and [d/(c+d),1] for the difference, with c=a/h,d=b/k.',
            'The area equals ab/2 times the integral of the nonnegative quadratic cap on its interval.'],
            dict(area=m.simplify(m.mul(m.div(m.mul(A,B),q(2)),moment))),alpha=2,plus=plus)
    if conditions==['all parameters positive'] and walls==['(x/a+y/b)^5=x^2*y^2/c^4']:
        factor=m.div(m.power(m.mul(A,B),5),m.mul(q(1260),m.power(('s','c'),8)))
        return theorem('generalized_polar_area',[
            'Use α=2 and solve for the positive upper r on t∈(0,1). Its expression is a²b² t²(1−t)²/c⁴.',
            'Outside the positive t interval the extended real arcs are unbounded, so the enclosed loop uses only its stated bounded part.',
            'Square the radial cap and use the beta moment B(5,5)=1/630 with the factor ab/2.'],
            dict(area=factor),alpha=2)
    if conditions==['all parameters positive'] and walls==['x^3/a^3+y^2/b^3=x^2/h^2+y^2/k^2','x=0','y=0']:
        delta=m.add(m.div(ONE,m.power(B,3)),m.neg(m.div(ONE,m.power(K,2))))
        value=m.div(m.mul(q(4),m.power(A,6)),m.mul(q(15),m.mul(m.power(H,5),('sqrt',delta))))
        return theorem('generalized_polar_area',[
            'Keep the printed b³. In the positive quadrant use the slope t=y/x of ordinary polar coordinates (α=1).',
            'For B=1/b³−1/k²>0 the radial graph in x is a³(h^−2−B t²), with 0≤t≤1/(h sqrt(B)).',
            'The measure in x,t is x dxdt. Integrate the square of the nonnegative cap, giving 4a⁶/(15h⁵sqrt(B)) on one side of y=0.',
            'Reflection supplies the other side if requested. If B≤0 there is no such bounded nondegenerate component.'],
            dict(quadrant_area=value,condition='1/b^3-1/k^2>0',other_quadrant='reflection of the same area'),alpha=1)
    raise Unsupported('The required generalized coordinates do not certify these original walls')


def compound_polar_area(task):
    w=task['boundaries'];c=task['stated_conditions'];method=task.get('method_requirement')
    a=('s','a');a2=m.power(a,2)
    if method=='polar_coordinates' and (w,c)==(['(x^3+y^3)^2=x^2+y^2'],['x>=0','y>=0']):
        value=m.add(m.div(PI,q(6)),m.mul(m.div(('sqrt',q(2)),q(3)),('ln',m.add(ONE,('sqrt',q(2))))))
        return theorem('generalized_polar_area',[
            'At r>0 the first quadrant gives r²=1/(cos³φ+sin³φ). The entire radial segment from zero is inside the bounded component.',
            'Use z=sin(φ−π/4) in its angular integral. The denominator becomes (1−z²)(1/2+z²) after the derivative.',
            'Split the rational expression into a hyperbolic inverse and an arctangent and evaluate at both symmetric endpoints.'],
            dict(area=value),alpha=1)
    if method=='polar_coordinates' and (w,c)==(
            ['(x^2+y^2)^2=8*a^2*x*y','(x-a)^2+(y-a)^2<=a^2'],['a>0']):
        z=m.add(m.add(m.neg(('acos',q(3,4))),('asin',m.div(('sqrt',q(14)),q(4)))),m.div(('sqrt',q(7)),q(2)))
        return theorem('generalized_polar_area',[
            'Write δ=φ−π/4, c=cosδ and d=sqrt(2c²−1). The circle cuts a ray in a(sqrt(2)c±d), while the lobe upper bound is 2ad.',
            'The lobe bound is always at most the larger circle radius. It meets the lower radius iff c≥3/4, giving the symmetric angular domain.',
            'The radial area difference leaves a² integral of 4c²−3+2sqrt(2)c d on [0,acos(3/4)]. Use sinδ in the last term.'],
            dict(area=m.mul(a2,z),disk_part_outside_lobe=m.mul(a2,m.add(PI,m.neg(z)))),alpha=1)
    if method=='appropriate_change_of_variables' and (w,c)==(
            ['x^2/lambda+y^2/(lambda-c^3)=1','lambda=c^2/3,2*c^2/3,4*c^2/3,5*c^2/3'],['x>0','y>0']):
        bounds=dict(ul='acosh(sqrt(4/(3*c)))',uh='acosh(sqrt(5/(3*c)))',
                    vl='acos(sqrt(2/(3*c)))',vh='acos(sqrt(1/(3*c)))')
        return theorem('certified_planar_substitution',[
            'The printed focal parameter is d=c³. A first-quadrant quadrilateral requires two levels below d and two above it.',
            'This gives 2/3<c<4/3. The smaller levels are the two hyperbolas, the larger two the ellipses.',
            'Set x=sqrt(d) cosh(u) cos(v), y=sqrt(d) sinh(u) sin(v). The two level families give the stated coordinate bounds.',
            'The positive Jacobian d(sinh²u+sin²v) separates into two elementary moments.'],
            dict(condition='2/3<c<4/3',
                 area='c^3*((vh-vl)*(sinh(2*uh)-sinh(2*ul))-(uh-ul)*(sin(2*vh)-sin(2*vl)))/4',
                 otherwise='the prescribed four conics do not bound this first-quadrant quadrilateral',bounds=bounds))
    if method is None and (w,c)==(
            ['x^2/cosh(u)^2+y^2/sinh(u)^2=c^2 at u1,u2','x^2/cos(v)^2-y^2/sin(v)^2=c^2 at v1,v2'],
            ['0<u1<u2','0<v1<v2','x>0','y>0']):
        return theorem('certified_planar_substitution',[
            'The first quadrant uses principal v between 0 and π/2. Each squared trigonometric denominator maps to v*=acos(|cos v|).',
            'Use the positive focal distance |c| for the two coordinate functions, preserving the original squared scale.',
            'Reject original zero denominators. Coincident principal levels give a collapsed strip, and otherwise their increasing arrangement gives the angle walls.',
            'The positive confocal Jacobian is c²(sinh²u+sin²v), and the two integrals separate.'],
            dict(area='c^2*((vh-vl)*(sinh(2*u2)-sinh(2*u1))-(u2-u1)*(sin(2*vh)-sin(2*vl)))/4',
                 angle_bounds=['min(v1*,v2*)','max(v1*,v2*)'],scale='c!=0',
                 conditions='sin(vi) cos(vi)!=0; vi*=acos(abs(cos(vi)))'))
    return None


def section_plane_area(task):
    bind(task,{'surface','section_plane'},('Найти площадь плоского сечения указанной поверхности.',))
    if task['requested_output']!=['area_in_plane']:raise Unsupported('The intrinsic plane area was requested')
    surf,plane=task['surface'],task['section_plane']
    if plane=='x+y+z=0' and (w:=re.fullmatch(fr'x\^2\+y\^2\+z\^2-x\*y-x\*z-y\*z={PLANAR_PARAMETER_CAPTURE}\^2',surf)):
        return theorem('intrinsic_plane_area',[
            'On the stated plane the sum of pairwise products equals minus one half the squared Euclidean norm.',
            'The radius in the plane is sqrt(2/3)|a|. The disk uses the intrinsic Euclidean measure.'],
            dict(area_in_plane=m.mul(m.mul(q(2,3),PI),m.power(('s',w[1]),2))))
    if (surf,plane)==('1/x+1/y+1/z=0','z=1-2*(x+y)'):
        return theorem('intrinsic_plane_area',[
            'Clear the original reciprocal equation only with xyz≠0 and substitute the plane graph.',
            'In s=x+y,t=x−y the regular part is t²=4s−7s², an ellipse with three missing axis points.',
            'The planar determinant in (s,t) is 1/2 and the graph metric multiplier is sqrt(1+4+4)=3.',
            'The area enclosed by the closure is invariant under deleting those boundary points.'],
            dict(area_in_plane=m.div(m.mul(q(6),PI),m.mul(q(7),('sqrt',q(7)))),
                 source_domain='xyz!=0',interpretation='area enclosed by the closure of the regular section'))
    raise Unsupported('No intrinsic chart preserves the full source section')


def radial_lamina_mass(task,request):
    bind(task,{'density','region'},
         ('Масса квадратной пластинки со стороной a; плотность пропорциональна расстоянию от вершины, в центре равна rho0.',))
    if (task['requested_output']!=['mass'] or task['region']!='square of side a'
            or task['density']!='proportional to distance from one vertex; rho(center)=rho0'):
        raise Unsupported('The vertex-centered radial density and its calibration must be stated')
    A=m.power(('s','a'),2);R=('sqrt',q(2));C=m.add(q(2),m.mul(R,('ln',m.add(ONE,R))))
    return theorem('verified_fiber_moments',[
        'Put the origin at the chosen vertex; the center is at distance a/sqrt(2), fixing the density coefficient.',
        'One half of the square has 0≤φ≤π/4 and 0≤r≤a secφ; the other is its reflection.',
        'Multiply the proportional density by the radial Jacobian r and integrate r². The remaining sec³ moment has an elementary endpoint formula.'],
        dict(mass=m.mul(m.div(m.mul(('s','rho0'),A),q(3)),C),domain='a>0'))


def special_lamina_moments(task,request):
    region=task['region'];want=task['requested_output'];density=task.get('density',1);axis=task.get('axis')
    a=('s','a');abs_a=('abs',a);a4=m.power(a,4)
    if want==['centroid_coordinates'] and axis is None:
        if density=='constant' and region in ('sqrt(x)+sqrt(y)=sqrt(a),x=0,y=0','x^(2/3)+y^(2/3)=a^(2/3); x>0,y>0'):
            sqrt_case=region.startswith('sqrt')
            value=m.div(a,q(5)) if sqrt_case else m.div(m.mul(q(256,315),abs_a),PI)
            return theorem('powered_simplex_moments',[
                'Normalize by the coordinate intercept and send the common powered sum to a unit simplex.',
                'The two integrals of coordinate times density are equal by exchange symmetry.',
                'Compute the area and the two moments by their beta integrals. Divide by the positive area.'],
                dict(centroid_coordinates=[value,value],domain='nondegenerate original scale'))
        if density=='constant' and region=='loop (x/a+y/b)^3=x*y/c^2':
            b,c=('s','b'),('s','c');scale=m.div(m.mul(a,b),m.power(c,2))
            return theorem('powered_simplex_moments',[
                'Use s=x/a+y/b and t=x/(a*s). The loop is s=(ab/c²)t(1−t) for 0≤t≤1, between the origin and the signed cap.',
                'The absolute Jacobian is |ab*s|. The area and coordinate moments integrate separated powers of s and beta powers of t.',
                'The ratio of the first coordinate moment to area is a(ab/c²)/14, with the other obtained by swapping a,b.'],
                dict(centroid_coordinates=[m.div(m.mul(z,scale),q(14)) for z in (a,b)],domain='abc!=0'))
        if density=='constant' and region=='(x^2+y^2)^2=2*a^2*x*y, x>0,y>0':
            value=m.div(m.mul(abs_a,PI),q(8))
            return theorem('powered_simplex_moments',[
                'On the first quadrant lobe, r²=a² sin(2φ). Integrate r once for area and r² times cosφ or sinφ for the two moments.',
                'The area is a²/2. A beta substitution in the angular first moment gives π|a|³/16. Divide by the area.'],
                dict(centroid_coordinates=[value,value],domain='a!=0'))
        if (region,density)==('x^2+y^2<=a^2','proportional to distance from A=(a,0)'):
            return theorem('verified_fiber_moments',[
                'Use a polar center at A and point the zero angle toward the disk center. At angle |φ|≤π/2 the radius goes up to 2|a|cosφ.',
                'The density times the area measure is proportional to r²dr dφ. The perpendicular first moment vanishes by reflection.',
                'The ratio of the first inward to zeroth radial moments is 6|a|/5. With the original orientation this leaves x=-a/5.'],
                dict(centroid_coordinates=[m.mul(q(-1,5),a),ZERO],domain='a!=0 and positive density factor'))
    if want==['inertia_x','inertia_y'] and density==1 and axis is None:
        if region=='x^4+y^4=a^2*(x^2+y^2)':
            v=m.mul(m.mul(q(3,8),('sqrt',q(2))),m.mul(PI,a4))
            return theorem('verified_fiber_moments',[
                'On each ray r²=a²/(cos⁴φ+sin⁴φ). Exchange symmetry gives half the polar moment for each axis.',
                'The normalized denominator is (3+cos(4φ))/4. Differentiate the circle mean of (A+Bcosφ)^−1 in A where A>|B|.',
                'Use A=3,B=1 and multiply by the radial factor, yielding both exact moments.'],
                dict(inertia_x=v,inertia_y=v))
        rb=region.split('; ')
        if len(rb)==2 and rb[1]=='x>0,y>0' and (
                re.fullmatch(r'x\*y=a\^2,x\*y=2\*a\^2,x=2\*y,2\*x=y',rb[0])):
            cell=monomial_rectangle(rb[0].split(','),['x>0','y>0'])
            ix,p=monomial_moment(cell,0,2);iy,q0=monomial_moment(cell,2,0)
            return theorem('positive_monomial_rectangle',[
                'The positive product levels and independent slope levels give two monomial coordinates.',
                'Use xy/(|D|uv) and pull each of the two quadratic weights back to a product of powers.'],
                dict(inertia_x=ix,inertia_y=iy,parameter_condition='a!=0',degenerate='empty positive component at a=0'),
                proofs=[p,q0],rectangle=cell['intervals'])
    if (want,region,density,axis)==(['axis_moment'],'equilateral triangle side a',1,'through centroid at angle alpha to altitude'):
        return theorem('verified_fiber_moments',[
            'The 120° rotational symmetry of the centroidal quadratic moment matrix forces it to be scalar.',
            'Take one axis parallel to the base. Its parallel-base moment about the base follows from a linear width in height.',
            'Subtract area times the squared distance h/3 to the centroid. The result applies to every centroidal direction.'],
            dict(axis_moment=m.mul(q(1,96),m.mul(('sqrt',q(3)),a4))))
    return None


def planar_moment_identity(task):
    bind(task,{'formula','hypotheses','origin','product_moment'},
         ('Доказать теорему параллельных осей.','Доказать формулу поворота оси, проходящей через центр масс.'),
         ('continued_on_pdf_page',))
    if task['requested_output']!=['proof']:raise Unsupported('The moment identity proof was requested')
    formula=task['formula']
    if (formula,task.get('hypotheses'))==('I_l=I_l0+S*d^2',['l parallel l0','l0 through centroid','distance d']) and (
            not set(task)&{'origin','product_moment'}):
        return theorem('centroid_axis_moments',[
            'Let z be signed distance to the axis through the centroid, so its areal first moment is zero.',
            'Expand the square of z plus or minus the fixed distance between the parallel axes.',
            'The cross term integrates to zero; the last term is area times d².'],dict(equality=formula))
    if (formula,task.get('origin'),task.get('product_moment'))==(
            'I=Ix*cos(alpha)^2-2*Ixy*sin(alpha)*cos(alpha)+Iy*sin(alpha)^2','centroid','int_S rho(x,y)*x*y dx dy'):
        return theorem('centroid_axis_moments',[
            'The signed distance to the rotated line is y cosα−x sinα.',
            'Expand its square before integrating with one common density. The squared and mixed terms give exactly the three printed moments.'],
            dict(equality=formula))
    raise Unsupported('The source axis and density identities remain unresolved')


def moving_centroid(task,request):
    bind(task,{'boundaries'},('Найти кривую, описываемую центром масс переменной площади.',))
    if (task['requested_output'],task['boundaries'])!=(
            ['eliminated_centroid_locus'],['y=sqrt(2*p*x)','y=0','x=X']):
        raise Unsupported('The original continuous family of parabolic caps is required')
    return theorem('verified_fiber_moments',[
        'For p>0 and X>0, integrate the positive vertical height sqrt(2px), its product with x, and half its square.',
        'The ratios are xbar=3X/5 and ybar=3sqrt(pX)/(4sqrt(2)).',
        'Eliminate the positive moving endpoint X; the remaining positive branch is exactly traced as X varies.'],
        dict(locus='ybar^2=15*p*xbar/32',conditions=['p>0','xbar>0','ybar>0']))


def planar_integral_theory(task,request):
    from functools import reduce
    kind=task['kind'];want=task['requested_output'];f=task.get('integrand');region=task.get('region')
    if kind=='planar_sample_quadrature':
        bind(task,{'integrand','region','mesh','sample'},(
            'Приближённо вычислить, заменяя диск системой вписанных квадратов с целочисленными вершинами; образец — наиболее удалённая от начала вершина. Сравнить с точным значением.',
            'Четыре равных треугольника, полученных прямыми x=const, y=const, x+y=const; образцы в центрах масс.',
            'Четыре равновеликих треугольника, полученных прямыми x=const, y=const, x+y=const; образцы в центрах масс.'))
        if want==['approximation','exact_comparison'] and task['mesh'] in (
                'inscribed lattice unit squares','inscribed squares with all vertices on the integer lattice') and task['sample']=='farthest_vertex':
            from math import isqrt
            from collections import Counter
            norm=m.add(('pow',('s','x'),2),('pow',('s','y'),2))
            L,relation,R=region.partition('<=')
            if not relation:raise Unsupported('The mesh must be inscribed in the whole disk')
            lhs,rhs,raw=(m.parse(z,None,['x','y']) for z in (L,R,f))
            if (domain_conditions(lhs) or domain_conditions(rhs) or m.simplify(lhs)!=norm
                    or raw[:2]!=('div',ONE) or raw[2][0]!='sqrt' or domain_conditions(raw[2][1])):
                raise Unsupported('An exact disk and radial reciprocal root are required')
            q0=m.num(m.simplify(rhs));p0=m.num(m.add(raw[2][1],m.neg(norm)))
            if q0 is None or p0 is None or q0.denominator!=1 or q0<=0 or p0<=0:
                raise Unsupported('The disk and radial profile must have a positive radius and offset')
            Q=int(q0);P=p0
            if Q>400:raise Unsupported('The literal finite grid is above the exact enumeration bound')
            Ns=Counter(x*x+y*y for x in range(1,isqrt(Q)+1) for y in range(1,isqrt(Q-x*x)+1))
            if not Ns:raise Unsupported('There is no positive-area inscribed mesh of the specified size')
            sample=reduce(m.add,(m.div(q(4*n),('sqrt',q(P+d))) for d,n in Ns.items()),ZERO)
            exact=m.mul(TURN,m.add(('sqrt',q(P+Q)),m.neg(('sqrt',q(P)))))
            return theorem('planar_integral_witnesses',[
                'Each square belongs to one open quadrant. In the positive quadrant it is inscribed exactly when its farthest lattice vertex satisfies the disk inequality.',
                'Count each admitted pair and multiply by the four reflected cells. The profile strictly decreases with radius, so the marked cell sum is a lower bound.',
                'For the exact comparison apply the polar Jacobian and integrate r/sqrt(P+r²) over the complete disk.'],
                dict(approximation=m.simplify(sample),exact=m.simplify(exact),relation='approximation<exact'),
                distances_and_counts=sorted(Ns.items()))
        triangle=re.fullmatch(r'triangle bounded by x=0,y=0,(?:x\+y|y\+x)=([1-9]\d*)',region)
        if want==['approximation'] and triangle and task['sample']=='centroids' and task['mesh'] in (
                'four equal triangles','four equal-area triangles'):
            raw=m.parse(f,None,['x','y'])
            if raw[0]!='sqrt' or domain_conditions(raw[1]) or m.simplify(raw[1])!=m.add(('s','x'),('s','y')):
                raise Unsupported('The requested samples need a real square-root profile of the sum')
            side=int(triangle[1]);half=m.num(q(side,2))
            grid=((0,0),(half,0),(side,0),(0,half),(half,half),(0,side))
            cells=((0,1,3),(1,3,4),(1,2,4),(3,4,5))
            vals=[q(sum(sum(grid[i]) for i in cell)/3) for cell in cells]
            return theorem('planar_integral_witnesses',[
                'The three midsegments give four equal triangles, each with one quarter of the original area.',
                'Compute each centroid from its three vertices and evaluate the square-root profile there.'],
                dict(approximation=m.mul(q(side**2,8),reduce(m.add,(('sqrt',s) for s in vals),ZERO))),samples=vals)
    if kind=='riemann_mesh_error':
        bind(task,{'integrand','region','mesh','error_bound'},
             ('Найти достаточную δ, гарантирующую строгое неравенство для любого конечного разбиения и выбора образцов.',))
        from fractions import Fraction
        if (want,f,task['mesh'])==(['sufficient_diameter','proof'],'sin(x+y)','every quadrable cell has diameter <delta') and (
                w:=re.fullmatch(r'x\^2\+y\^2<='+INTEGER,region)):
            error=Fraction(str(task['error_bound']))
            if error<=0:raise Unsupported('The target error must be strictly positive')
            result=m.div(q(error),m.mul(m.mul(q(int(w[1])),PI),('sqrt',q(2))))
            return theorem('planar_integral_witnesses',[
                'The gradient of sin(x+y) has norm at most sqrt(2), giving a uniform Lipschitz bound.',
                'On every cell the marked-value error is strictly below sqrt(2) times its area times δ. Sum the cell estimates over the original disk.',
                'Choose δ equal to the target error divided by the resulting area-Lipschitz constant.'],
                dict(sufficient_diameter=result,strict=True))
    if kind in ('abstract_integral_identity','integrated_mixed_partial'):
        return rectangular_integral_identity(task)
    if kind=='integral_inequality':
        bind(task,{'domain','hypotheses'},('Доказать (∫f)²≤(b−a)∫f² и точное условие равенства; указано рассмотреть ∬[f(x)−f(y)]².',))
        if (want,task['domain'],task['hypotheses'])==(
                ['inequality_proof','equality_iff_f_constant'],'a<=x<=b',['f is continuous','a<=b']):
            return theorem('planar_integral_witnesses',[
                'Expand the printed nonnegative square over the Cartesian product. The double integral is twice (b−a) integral(f²)−2 integral(f)².',
                'If a<b, continuity makes a zero double integral equivalent to f(x)=f(y) for every pair. If a=b, the integral is zero and the function on a singleton is constant.'],
                dict(inequality='(int_a^b f)^2<=(b-a)*int_a^b f^2',equality='iff f is constant on [a,b]'))
    if kind=='planar_integral_sign':
        bind(task,{'integrand','region'},('Определить знак двойного интеграла.',))
        if want!=['strict_sign']:raise Unsupported('Determine the strict sign on the exact source region')
        if (f,region)==('ln(x^2+y^2)','abs(x)+abs(y)<=1'):
            return theorem('sign_partition_moments',[
                'The squared radius is at most 1 on the diamond, strictly less on its interior. The logarithm is negative there except for its isolated undefined pole.',
                'Near the pole polar measure makes |ln r| integrable since integral r|ln r| converges. Thus the negative integral is finite and strict.'],
                dict(sign=-1))
        if f=='cbrt(1-(x^2-y^2))' and re.fullmatch(r'x\^2\+y\^2<='+INTEGER,region):
            return theorem('sign_partition_moments',[
                'The interchange x↔y preserves the disk and changes the sign of D=x²−y².',
                'For every D, cbrt(1+D)>cbrt(D−1)=−cbrt(1−D), by strict monotonicity and oddness. The paired density is strictly positive.'],
                dict(sign=1))
        if (f,region)==('asin(x+y)','0<x<1,-1<=y<=1-x'):
            return theorem('sign_partition_moments',[
                'At each fixed 0<x<1 use s=x+y. The interval is [x−1,1] inside the original arcsine domain.',
                'Odd symmetry cancels the central subinterval [x−1,1−x], leaving a positive interval [1−x,1].'],
                dict(sign=1))
    if kind=='planar_integral_estimate':
        bind(task,{'integrand','region','method_requirement'},('Оценить, пользуясь теоремой о среднем.',))
        if (want,task['method_requirement'])==(['two_sided_estimate'],'integral_mean_value') and (
                w:=re.fullmatch(r'abs\(x\)\+abs\(y\)<='+INTEGER,region)) and (
                p:=re.fullmatch(r'1/\('+INTEGER+r'\+cos\(x\)\^2\+cos\(y\)\^2\)',f)):
            A=int(w[1]);K=int(p[1]);area=2*A*A
            return theorem('planar_integral_witnesses',[
                'The original density is positive and continuous on the closed diamond. By the mean value theorem the integral is its area times a value attained on it.',
                'The density lies between 1/(K+2) and 1/K. Neither extremal equality can be constant on a positive-area diamond.'],
                dict(lower=q(area,K+2),upper=q(area,K),strict=True))
    if kind in ('integral_symmetry_proof','shrinking_region_mean','differentiate_moving_integral'):
        return varying_planar_measure(task)
    raise Unsupported('The original planar witness, integral hypothesis or requested conclusion remains unbound')


def rectangular_integral_identity(task):
    kind=task['kind'];want=task['requested_output']
    if kind=='integrated_mixed_partial' and len(task.get('integration_order',[]))==3:
        from quadrature import oriented_box_endpoints
        bind(task,{'integrand','integration_order'},('Найти тройной интеграл f=F_xyz по прямоугольному параллелепипеду.',))
        reasons,value,witness=oriented_box_endpoints(task)
        return theorem('planar_integral_witnesses',reasons,value,**witness)
    if kind=='integrated_mixed_partial':
        bind(task,{'integrand','integration_order'},('Вычислить повторный интеграл f=F_xy (вторая смешанная частная производная).',))
        order=task['integration_order']
        if (want!=['boundary_formula'] or task['integrand']!='F_xy(x,y)' or len(order)!=2
                or [s.get('variable') for s in order]!=['x','y'] or any(
                    set(s)!={'variable','lower','upper'} or not all(re.fullmatch(PLANAR_PARAMETER_CAPTURE,s[k]) for k in ('lower','upper')) for s in order)):
            raise Unsupported('The original mixed derivative and its two endpoint pairs must be bound')
        x0,x1=(order[0][k] for k in ('lower','upper'));y0,y1=(order[1][k] for k in ('lower','upper'))
        return theorem('planar_integral_witnesses',[
            'Apply the fundamental theorem along each y-fiber to ∂y(F_x).',
            'Then apply it to the difference of the two remaining x derivatives. All original oriented endpoints are retained.'],
            dict(boundary_formula=f'F({x1},{y1})-F({x1},{y0})-F({x0},{y1})+F({x0},{y0})',
                 condition='the original iterated derivatives satisfy the fundamental theorem on the two intervals'))
    bind(task,{'integrand','rectangle','hypotheses','literal','interpretation'},(
        'Доказать разложение прямоугольного интеграла в произведение двух однократных.',
        'Доказать формулу Дирихле. В издании слева дважды напечатан dx, внутренний интеграл от 0 до x; справа порядок dy dx.'))
    if want==['proof'] and task.get('integrand')=='X(x)*Y(y)' and not set(task)&{'literal','interpretation'}:
        R=task['rectangle'];hyp=task['hypotheses']
        if (len(R)==2 and [s.get('variable') for s in R]==['x','y'] and all(set(s)=={'variable','lower','upper'} for s in R)
                and hyp==['X continuous on ['+R[0]['lower']+','+R[0]['upper']+']',
                           'Y continuous on ['+R[1]['lower']+','+R[1]['upper']+']']):
            return theorem('planar_integral_witnesses',[
                'The continuous product is integrable on the Cartesian product, so apply Fubini.',
                'The inner factor is independent of the other coordinate; factor its definite integral out of the remaining step.'],
                dict(equality='integral_rectangle X(x)Y(y) dxdy=(integral_X X)(integral_Y Y)',rectangle=R))
    if (want,task.get('literal'),task.get('hypotheses'),task.get('interpretation'))==(
            ['proof','preserve_literal_typo'],'int_0^a dx int_0^x f(x,y) dx = int_0^a dy int_y^a f(x,y) dx',
            ['a>0'],'Conventional Dirichlet formula uses dy for the inner differential on the left.'):
        return theorem('inverted_monotone_fibers',[
            'The literal left expression uses dx twice and has no bound y. Preserve that original defect.',
            'With the stated conventional dy interpretation on the left, both orders cover precisely 0≤y≤x≤a.',
            'Fubini proves the corrected equality whenever f is integrable on this triangle.'],
            dict(literal=task['literal'],literal_defect='inner dx leaves y unbound',
                 conventional='int_0^a dx int_0^x f(x,y) dy = int_0^a dy int_y^a f(x,y) dx'))
    raise Unsupported('The rectangular or triangular integral identity was not preserved')


def varying_planar_measure(task):
    kind=task['kind'];want=task['requested_output'];f=task['integrand'];region=task['region']
    if kind=='integral_symmetry_proof':
        bind(task,{'integrand','region','hypotheses'},('Доказать нулевое значение при хотя бы одном нечётном показателе.',))
        if (want,f,region,task['hypotheses'])==(
                ['proof'],'x^m*y^n','x^2+y^2<=a^2',['m,n positive integers','m or n odd']):
            return theorem('sign_partition_moments',[
                'Choose a coordinate with an odd exponent. Reflect its sign.',
                'This is a measure-preserving involution of the original disk and sends the density to its negative, so the integral vanishes.'],
                dict(integral=ZERO))
    if kind=='shrinking_region_mean':
        bind(task,{'integrand','region','factor','hypotheses'},('Найти предел среднего по кругу при rho→0 для непрерывной f.',))
        if (want,f,region,task['factor'],task['hypotheses'])==(
                ['limit'],'f(x,y)','x^2+y^2<=rho^2','1/(pi*rho^2)',['f continuous']):
            return theorem('moving_planar_integrals',[
                'The factor is exactly the reciprocal area of the disk. Subtract f(0,0) as a constant under the integral.',
                'Bound the absolute average by the supremum of the difference on the disk. Continuity at the center makes that supremum tend to zero.'],
                dict(limit='f(0,0)'))
    if kind=='differentiate_moving_integral':
        bind(task,{'integrand','region'},('Найти F′(t) для интеграла по указанной зависящей от t области.',))
        if want!=['derivative_with_existence']:raise Unsupported('The original differentiability question includes existence')
        if (f,region)==('exp(t*x/y^2)','0<=x<=t,0<=y<=t'):
            return theorem('moving_planar_integrals',[
                'For t>0 restrict to x in [t/2,t] and y>0. Positivity gives the lower exponential exp(t²/(2y²)).',
                'This lower integral diverges at y=0; for example e^z≥z gives a nonintegrable multiple of 1/y².',
                'Thus no finite F or ordinary derivative exists for positive t. The inequalities give an empty region for t<0 and a degenerate singleton at t=0.'],
                dict(positive_t='divergent positive integral; derivative undefined',negative_t='empty region',at_zero='degenerate zero-area set'))
        if (f,region)==('sqrt(x^2+y^2)','(x-t)^2+(y-t)^2<=1'):
            return theorem('moving_planar_integrals',[
                'Translate to a fixed disk using u=x−t,v=y−t. Norm difference quotients are bounded by sqrt(2).',
                'For each fixed t the derivative exists off at most one point of the disk. Dominated convergence applies to the difference quotients.',
                'Translate back with unit Jacobian and retain the original disk in the derivative expression.'],
                dict(derivative='int_(x-t)^2+(y-t)^2<=1 (x+y)/sqrt(x^2+y^2) dxdy',pole='one point, measure zero'))
        if (f,region)==('f(x,y)','x^2+y^2<=t^2, t>0'):
            return theorem('moving_planar_integrals',[
                'Use a fixed full angular period and ordered radial integration from 0 to t.',
                'If the angular mean is continuous at t, apply the fundamental theorem to the radial endpoint. A continuous f satisfies that condition.',
                'If no such regularity is assumed, the radial mean primitive is only absolutely continuous for an integrable f, with a derivative almost everywhere.'],
                dict(derivative='t*int_0^(2*pi) f(t*cos(phi),t*sin(phi)) dphi',condition='continuous radial mean at t'))
    raise Unsupported('The symmetry or moving-region hypotheses do not establish the stated conclusion')


NEW_PLANAR_KINDS={
    'bounded_region_area','planar_sample_quadrature','riemann_mesh_error','abstract_integral_identity',
    'integrated_mixed_partial','integral_inequality','planar_integral_sign','planar_integral_estimate',
    'polar_region_characterization','reverse_polar_integral','area_map_ratio','specified_change_of_variables',
    'region_mapping_proof','find_region_coordinates','integral_symmetry_proof','shrinking_region_mean',
    'differentiate_moving_integral','planar_section_area','lamina_mass','centroid_locus','planar_moments','moments_identity',
}


def planar_composition_goal(task):
    """Select source forms without consuming the interfaces of the existing chart solvers."""
    kind=task.get('kind');region=task.get('region')
    if kind in NEW_PLANAR_KINDS:
        return 'requested_output' in task and 'goal' not in task
    if kind=='reverse_iterated_integral':
        b=task.get('integration_order')
        if not isinstance(b,list) or len(b)!=2 or not all(isinstance(s,dict) for s in b):return False
        lo,hi=(str(b[1].get(k,'')) for k in ('lower','upper'))
        return (lo.startswith('-sqrt(') and lo=='-sqrt('+hi+')' or
                lo=='2-x' and hi=='sqrt(2*x-x^2)' or
                lo=='sqrt(2*a*x-x^2)' and hi=='sqrt(2*a*x)' or
                lo=='0' and (hi=='ln(x)' or hi=='sin(x)') or
                str(b[0].get('lower'))=='0' and str(b[0].get('upper'))=='1'
                and bool(re.fullmatch(r'x\^(?:[3-9]|[1-9]\d+)',lo)) and bool(re.fullmatch(r'x\^[2-9]\d*',hi)))
    if kind=='planar_area':
        walls=task.get('boundaries');method=task.get('method_requirement')
        if not isinstance(walls,list) or not walls or not all(isinstance(s,str) for s in walls):return False
        return (method=='generalized_polar_x=A*r*cos(phi)^alpha_y=B*r*sin(phi)^alpha' or
                method=='polar_coordinates' and walls[0].startswith(('(x^2+y^2)^2=','(x^3+y^3)^2=')) or
                method=='appropriate_change_of_variables' and len(walls) in (2,4) or
                method is None and len(walls)==4 and {'x>0','y>0'}<=set(task.get('stated_conditions',[])) or
                method is None and len(walls)==2 and (walls[0].startswith(('x*y=','y^2=2*','x^2/cosh('))))
    if not isinstance(region,str):return False
    if kind=='cartesian_slices':return region.startswith('y bounded by x^2 and ')
    if kind=='polar_change_bounds':
        return region.startswith(('0<=x<=','-a<=x<=a,','right lobe bounded by ')) or (
            ', ' in region and region.startswith('x^2+y^2<=') and '*x,' in region)
    if kind=='polar_integral_reduction':
        return region.startswith('abs(y)<=abs(x),abs(x)<=') or task.get('integrand')=='f(y/x)'
    if kind=='planar_integral_reduction':
        return task.get('integrand') in ('f(x+y)','f(a*x+b*y+c)','f(x*y)')
    if kind=='planar_exact_integral':
        f=task.get('integrand')
        return (region.startswith(('bounded by y^2=','bounded by x*y=','coordinate axes and the shorter arc',
                                  'parallelogram with sides ','x-axis and first cycloid arch'))
                or region.startswith('ellipse with bounding curve ') and isinstance(f,str) and f.startswith('sqrt(1-x^2/')
                or f in ('abs(x)+abs(y)','abs(cos(x+y))','abs((x+y)/sqrt(2)-x^2-y^2)',
                         'sign(x^2-y^2+2)','floor(x+y)','sqrt(abs(y-x^2))') or region=='x^4+y^4<=1')
    if kind=='lamina_centroid':
        return region.startswith(('sqrt(x)+sqrt(y)=','x^(2/3)+y^(2/3)=','loop (x/a+y/b)^3=',
                 '(x^2+y^2)^2=2*a^2*x*y,','r=a*(1+cos(phi)),','cycloidal arch x=')) or (
                     region=='x^2+y^2<=a^2' and task.get('density')=='proportional to distance from A=(a,0)')
    return False


def source_planar_composition(task,library,request):
    if not library.data.get('source_planar_composition'):
        raise Unsupported('No source-bound planar composition is published')
    return compose_planar_measure(task,library,request)


def rectangular_grid_sums(task,library,saved=None):
    """Evaluate exact tagged and Darboux sums by finite differences on both grid axes."""
    from finite_sums import polynomial_primitive
    from polynomial import rf
    from quadrature import enclose
    from tasks import bind_printed_geometry
    darboux=task['kind']=='darboux_sum_limit'
    wanted=['lower_sum','upper_sum','limits'] if darboux else ['sum','limit']
    fields={'kind','id','source','rectangle','mesh','integrand','requested_output'}
    if not darboux:fields.add('sample')
    if (not library.data.get('rectangular_grid_sums') or set(task)-fields or task.get('requested_output')!=wanted or
            set(task.get('source',{}))-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement'}):
        raise Unsupported('An original mesh, tag rule or additional objective remains unverified')
    box=task['rectangle'];axes=[];starts=[];width=[]
    if not isinstance(box,list) or len(box)!=2:raise Unsupported('Expected two finite intervals')
    for axis in box:
        if set(axis)!={'variable','lower','upper'}:raise Unsupported('Invalid rectangle axis')
        v=axis['variable']
        if not re.fullmatch(r'[A-Za-z_]\w*',v) or v in {*axes,'n','i','j','e','pi',*m.FUNCTIONS,*m.ALIASES}:
            raise Unsupported('The two axes and grid indices must be distinct')
        ends=[m.parse(axis[k],None) for k in ('lower','upper')]
        if not all(m.constant_defined(t,{'assumptions':[],'parameters':[]}) for t in ends):raise Unsupported('Undefined rectangle endpoint')
        lo,hi=(m.num(m.simplify(t)) for t in ends)
        if lo is None or hi is None or lo>=hi:raise Unsupported('Expected ordered finite rational endpoints')
        axes.append(v);starts.append(q(lo));width.append(q(hi-lo))
    mesh=task['mesh'];n=('v','n');indices=(('s','i'),('s','j'));step=('s','__mesh')
    if isinstance(mesh,list) and len(mesh)==3 and mesh[-1].replace(' ','')=='0<=i,j<=n':
        ctx=m.context(dict(variable='__',parameters=['i','j','n'],parameter_conditions=['n>0']))
        for clause,v,k,a,w in zip(mesh,axes,indices,starts,width):
            match=re.fullmatch(re.escape(v+'_'+k[1])+r'\s*=\s*(.+)',clause)
            if not match:raise Unsupported('Grid line is not bound to its source index')
            e=m.parse(match[1],None,['i','j','n'])
            if any(not known_guard(g,ctx) for g in domain_conditions(e)) or not same_value(e,m.add(a,m.div(m.mul(w,k),('s','n')))):
                raise Unsupported('Grid lines do not exactly partition the source rectangle')
    elif mesh!='n by n equal rectangles' and not (mesh=='n by n equal squares' and width[0]==width[1]):
        raise Unsupported('The given partition has not been recovered as a uniform rectangular grid')
    f=m.parse(task['integrand'],None,axes)
    f=m.substitute(f,{('s',v):z for v,z in zip(axes,(X,Y))})
    unit={z:m.add(a,m.mul(w,('v',v))) for z,v,a,w in zip((X,Y),axes,starts,width)}
    from quadrature import guard_bounds
    for relation,e in domain_conditions(f):guard_bounds(relation,m.substitute(e,unit),(Fraction(0),Fraction(1)),axes)
    coeff=coordinate_terms(f)
    if any(m.num(c) is None for c in coeff.values()):raise Unsupported('A rational polynomial field is required')
    corners={'upper_right':(1,1),'lower_right':(1,0),'upper_left':(0,1),'lower_left':(0,0)}
    gradients=[]
    if darboux:
        lower=[]
        for dimension in (0,1):
            derivative=ZERO
            for deg,c in coeff.items():
                if not deg[dimension]:continue
                powers=list(deg);powers[dimension]-=1
                term=m.mul(q(deg[dimension]),m.mul(c,m.mul(m.power(X,powers[0]),m.power(Y,powers[1]))))
                derivative=m.add(derivative,term)
            lo,hi=enclose(m.substitute(derivative,unit),(Fraction(0),Fraction(1)))
            if lo<0<hi:raise Unsupported('Coordinate monotonicity does not locate every cell extremum')
            gradients.append([q(lo),q(hi)]);lower.append(int(hi<=0 and lo<0))
        samples=[lower,[1-s for s in lower]]
    else:
        if task.get('sample') not in corners:raise Unsupported('The prescribed sample point is unsupported')
        bind_printed_geometry(task,'sample',task['sample'])
        samples=[corners[task['sample']]]
    k=('v','k');potentials={};sums=[];limits=[]
    def prefix(degree):
        key=str(degree)
        if key not in potentials:
            p=(polynomial_primitive((Fraction(0),)*degree+(Fraction(1),),1,'k') if saved is None
               else freeze(saved['power_prefixes'][key]))
            guards=domain_conditions(p)
            if guards or not same_value(m.substitute(p,{k:ZERO}),ZERO) or not same_value(
                    m.add(p,m.neg(m.substitute(p,{k:m.add(k,q(-1))}))),m.power(k,degree)):
                raise Unsupported('Finite-difference or empty-prefix identity failed')
            potentials[key]=p
        return m.substitute(potentials[key],{k:n})
    for offsets in samples:
        tagged={z:m.add(a,m.mul(w,m.mul(step,m.add(i,q(tag-1))))) for z,a,w,i,tag in zip((X,Y),starts,width,indices,offsets)}
        terms,den=m.rational_form(m.substitute(f,tagged))
        if set(den)!={()}:raise Unsupported('Sample weights are not certified polynomials')
        total=ZERO
        for mon,c in terms.items():
            powers=dict(mon);i,j=(powers.pop(idx,0) for idx in indices);h=powers.pop(step,0)
            if powers:raise Unsupported('A sample contains an unsummed variable')
            total=m.add(total,m.div(m.mul(q(c/den[()]),m.mul(prefix(i),prefix(j))),m.power(n,h)))
        formula=m.simplify(m.div(m.mul(m.mul(*width),total),m.power(n,2)))
        num,den=rf(formula,'n')
        if len(num)>len(den):raise Unsupported('The finite sums have no established finite limit')
        limits.append(q(num[-1]/den[-1]) if len(num)==len(den) else ZERO);sums.append(formula)
    if darboux and limits[0]!=limits[1]:raise Unsupported('Darboux endpoints have different limits')
    plan=dict(theorem='method.rectangular_polynomial_grid_sums',axes=axes,starts=starts,widths=width,
              positive_integer_mesh='n>=1',cell_area=m.div(m.mul(*width),m.power(n,2)),corners=samples,
              derivative_ranges=gradients,power_prefixes=potentials)
    return plan,(dict(lower_sum=sums[0],upper_sum=sums[1],limits=limits) if darboux else dict(sum=sums[0],limit=limits[0]))


NAME = r'[A-Za-z_]\w*'
SOURCE_FIELDS = {'exercise', 'printed_subpart', 'pdf_page', 'printed_page', 'pdf_sha256', 'page_png_sha256', 'literal_requirement'}
COMMON_FIELDS = {'kind', 'id', 'source', 'requested_output'}


def source_fields(task, allowed, headings=()):
    provenance=task.get('source', {})
    if (set(task)-COMMON_FIELDS-allowed or set(provenance)-SOURCE_FIELDS
            or provenance.get('literal_requirement') not in (None,*headings)):
        raise Unsupported('An original assumption, output or method has no proof here')


def period_translation(function, start, period):
    return [
        f'I(x+{period})−I(x) is the integral of {function} over one translated period.',
        'The period integral is independent of x: differentiating the moving endpoints gives h(x+T)−h(x)=0.',
        f'C is the integral over [{start},{start}+{period}], and T is the given positive period.',
        'Subtracting (C/T)x leaves a T-periodic residual. If C=0, the primitive itself has period T.',
    ]


def interval_transform(text,wanted):
    if wanted==['proof','geometric_interpretation']:
        match=re.fullmatch(fr'({NAME}) (even|odd), continuous on \[−({NAME}),\3\]; prove ∫₋ₗˡ \1\(x\)dx=(2∫₀ˡ \1\(x\)dx|0) and give a geometric interpretation\.',text)
        if not match or match[3]!='l' or (match[2]=='odd')!=(match[4]=='0'):
            raise Unsupported('The reflection relation must agree with the stated parity')
        parity=match[2]
        argument=['Split at zero and reflect the left interval through t=−x.',
                  'The reflected values have the same sign by evenness.' if parity=='even' else 'Oddness reverses the reflected values.',
                  'The two signed areas therefore add.' if parity=='even' else 'The two signed areas therefore cancel.']
        result=dict(proved=True,parity=parity,geometric_interpretation=argument[-1])
    elif wanted==['both_proofs'] and text=='Доказать, что одна из первообразных чётной функции нечётна, а всякая первообразная нечётной функции чётна.':
        argument=[
            'Given a primitive F of an even function, the odd part (F(x)−F(−x))/2 has derivative (f(x)+f(−x))/2=f(x).',
            'For odd f on a symmetric interval, the primitive normalized by F(0)=0 is even by reflection. Other primitives differ by a constant.',
            'On a disconnected symmetric domain, component constants can differ. For example, take f=0 on (−2,−1)∪(1,2) and a primitive with values 1 and 0 on the two components.',
        ]
        result=dict(odd_primitive_of_even='(F(x)-F(-x))/2',
                    primitives_of_odd='even on a symmetric interval',disconnected_domain='counterexample for the second claim')
    elif wanted==['proof'] and re.fullmatch(
            fr'Для непрерывной ({NAME}) на \[a,b\] доказать ∫ₐᵇ \1\(x\)dx=\(b−a\)∫₀¹ \1\(a\+\(b−a\)x\)dx\.',text):
        argument=['The affine map a+(b−a)t covers [a,b] with Jacobian b−a.',
                  'Apply oriented substitution to the continuous field. When a=b, both integrals after scaling are zero.']
        result=dict(proved=True,substitution='x=a+(b-a)*t')
    elif wanted==['proof'] and re.fullmatch(
            fr'При a>0 доказать ∫₀ᵃ x³ ({NAME})\(x²\)dx=\(1/2\)∫₀\^\{{a²\}} x \1\(x\)dx\.',text):
        argument=['Use u=x², strictly increasing on the nonnegative interval. On compact positive subintervals x³dx=u du/2.',
                  'The substituted lower end tends to zero. The equality holds whenever the original integrals exist.']
        result=dict(proved=True,substitution='u=x^2',domain='a>0 and existing integrals')
    else:
        h=re.fullmatch(fr'({NAME}) continuous on \[0,1\]: ∫₀\^\{{π/2\}} \1\(sin x\)dx = ∫₀\^\{{π/2\}} \1\(cos x\)dx',text)
        weighted=re.fullmatch(fr'({NAME}) continuous on \[0,1\]: ∫₀\^π x \1\(sin x\)dx = \(π/2\)∫₀\^π \1\(sin x\)dx',text)
        if wanted!=['proof'] or not (h or weighted):
            raise Unsupported('The translated or reflected interval and all stated outputs must agree')
        argument=['The reflection maps the whole interval onto itself with reversed orientation and unit absolute Jacobian.',
                  'It takes sine to cosine.' if h else 'Sine is fixed and the paired weights x and π−x add to π.']
        result=dict(proved=True,substitution='t=pi/2-x' if h else 't=pi-x')
    return dict(theorem='method.integral_interval_transform',argument=argument),result


def period_goal(task):
    from integrals import affine
    if task['kind']=='proof_about_integrals':
        source_fields(task, {'statement'})
        wanted=task.get('requested_output')
        translation=re.fullmatch(fr'({NAME}) continuous and ({NAME})-periodic on R; prove ∫ₐ\^\{{a\+\2\}} \1\(x\)dx=∫₀\^\2 \1\(x\)dx for every a\.',
                                 task['statement'].replace('∫₀ᵀ','∫₀^T'))
        separation=re.fullmatch(fr'({NAME}) continuous and ({NAME})-periodic\. Show ({NAME})\(x\)=∫_\{{({NAME})\}}ˣ \1\(t\)dt is the sum of a linear function and a \2-periodic function\.',task['statement'])
        if translation and wanted==['proof']:
            h,T=translation.groups()
            argument=period_translation(h,'0',T)[:3]
            result=dict(independent_of_start=True, period_integral=f'integral({h}(t), t, 0, {T})')
        elif separation and wanted==['proof']:
            h,T,F,a=separation.groups()
            argument=period_translation(h,a,T)
            C=f'integral({h}(t), t, {a}, {a}+{T})'
            result=dict(linear_coefficient=f'{C}/{T}',periodic_part=f'{F}(x)-({C}/{T})*x',period=T)
        else:return interval_transform(task['statement'],wanted)
        return dict(theorem='method.integral_period_translation', argument=argument), result

    if 'statement' in task:
        source_fields(task, {'statement'})
        match=re.fullmatch(
            fr'Доказать, что ({NAME})\(x\)=∫₀ˣ (sin|cos)ⁿ\(t\)dt и ({NAME})\(x\)=∫₀ˣ '
            r'(sin|cos)ⁿ\(t\)dt при нечётном n имеют период 2π, а при чётном n обе есть суммы линейной и периодической функций\.',
            task['statement'])
        if not match:raise Unsupported('The printed periodic primitive goal is unresolved')
        F,f,G,g=match.groups()
        v,n,span,waves='t','n','2*pi',[(F,f+'(t)^n'),(G,g+'(t)^n')]
    else:
        source_fields(task, {'variable','index','index_domain','period','waves'})
        v,n,span,waves=(task[k] for k in ('variable','index','period','waves'))
        if task['index_domain']!='positive_integers':
            raise Unsupported('Integer powers and their parity must hold on the original parameter set')
    if task.get('requested_output')!=['proof_for_both_functions_and_parities'] or len(waves)!=2 or waves[0][0]==waves[1][0]:
        raise Unsupported('Both named primitive functions and parity cases are needed')
    m.context(dict(variable=v,parameters=[n]))
    period=m.simplify(m.parse(span,None));ctx=m.context(dict(variable=v))
    if not m.constant_defined(period,ctx) or m.sign(period,ctx)!=1:raise Unsupported('The original period must be positive')
    rows=[];result={}
    for F,text in waves:
        raw=m.parse(text,v,[n]);name=('s',n)
        if (not re.fullmatch(NAME,F) or raw[0]!='rpow' or raw[2]!=name or raw[1][0] not in ('sin','cos')
                or domain_conditions(raw,positive_integer_exponents=(name,))):
            raise Unsupported('The original wave power or its domain is unresolved')
        wave,phase=raw[1];slope,offset=affine(phase,v)
        turns=m.num(m.simplify(m.div(m.mul(slope,period),m.mul(q(2),m.PI))))
        if turns is None or turns.denominator!=1 or not turns:
            raise Unsupported('The proposed period does not translate the original phase by complete nonzero turns')
        half_turn=m.simplify(m.div(period,q(2*abs(turns))))
        rows.append(dict(function=F,original_wave=raw,phase_offset=offset,period=period,
                         signed_phase_turns=int(turns),half_turn=half_turn,odd_period_integral=ZERO))
        result[F]=dict(odd=dict(period=period),even=dict(residual_period=period,
                        linear_coefficient=dict(integrand=raw,lower=ZERO,upper=period,divisor=period)))
    argument=period_translation('each original integer power','0','T')
    argument.append('For odd exponents each half-turn changes the sign, and the proved period contains whole turns. The period integral is zero.')
    return dict(theorem='method.integral_period_translation', waves=rows, argument=argument), result


def jump_goal(task):
    source_fields(task, {'stated_conditions','claim'})
    if task.get('requested_output')!=['proof']:raise Unsupported('The conclusion must be an integral identity')
    conditions=task['stated_conditions']
    if len(conditions)!=2:raise Unsupported('Both source conditions are needed')
    integral=re.fullmatch(fr'({NAME}) is properly Riemann integrable on \[({NAME}),({NAME})\]',conditions[0])
    primitive=re.fullmatch(fr"({NAME}) prime=({NAME}) except possibly endpoints and finitely many interior points ({NAME})_i "
                           r'at which \1 has discontinuities of the first kind',conditions[1])
    if not integral or not primitive or integral[1]!=primitive[2]:
        raise Unsupported('The differentiated function, branch cover and properly integrable derivative must agree')
    f,a,b=integral.groups(); F,_,c=primitive.groups()
    if len({f,a,b,F,c})!=5:raise Unsupported('Distinct source functions and endpoints are required')
    claim=f'integral({a},{b},{f}(x),x)={F}({b}-)-{F}({a}+)-sum_i({F}({c}_i+)-{F}({c}_i-))'
    if task['claim']!=claim:raise Unsupported('The requested traces or jump coefficient do not match the theorem')
    plus=lambda x:f'{F}({x}+)'
    minus=lambda x:f'{F}({x}-)'
    argument=[
        f'Order the finitely many {c}_i inside [{a},{b}]. Shrink each consecutive closed subinterval away from both endpoints.',
        f'On every shrunken subinterval the derivative of {F} equals the original Riemann integrable {f}, so Newton–Leibniz applies.',
        f'{f} is bounded on the full segment. The integral over the omitted pieces tends to zero with their total length.',
        'Only one-sided traces remain. At each interior cut the left trace enters positively and the right trace negatively.',
    ]
    return dict(theorem='method.piecewise_integral_traces', argument=argument,
                branch_contribution=[minus(c+'_{i+1}'),plus(c+'_i')],
                interior_jump=[plus(c+'_i'),minus(c+'_i')]), dict(identity=claim, proved=True)


def accumulation_goal(task):
    from integrals import affine
    kind=task['kind'];wanted=task.get('requested_output')
    if kind=='integral_derivative_theorem':
        source_fields(task,{'stated_conditions'})
        condition=fr'({NAME}) properly Riemann integrable on \[({NAME}),({NAME})\], ({NAME})\(x\)=({NAME})\+integral\(\2,x,\1\(({NAME})\),\6\)'
        gates=task.get('stated_conditions',[])
        if (len(gates)!=1 or not re.fullmatch(condition,gates[0]) or wanted!=[
                'prove continuity of F','prove F prime equals f at continuity points','describe F prime at discontinuity points']):
            raise Unsupported('The original bounded integral and all derivative questions must be supplied')
        return dict(theorem='method.piecewise_integral_traces', argument=[
            'Proper Riemann integrability bounds |f| by M. Additivity bounds each increment of F by M|h|.',
            'The difference quotient is the average of f over the interval between x and x+h.',
            'At continuity points this average converges to f(x). In general the two directional average limits must exist and agree.',
            'At an interval endpoint use only the inward one-sided average.',
        ]),dict(continuous=True,derivative_at_continuity='f(x)',condition_at_interior_discontinuity='equal finite one-sided means',
                endpoint_derivative='finite inward one-sided mean')
    if kind=='integral_derivative_example':
        source_fields(task,{'function','stated_conditions'})
        if task.get('stated_conditions')!=['f properly Riemann integrable on [a,b], F(x)=C+integral(a,x,f(t),t)'] or wanted!=['analyse derivative at all discontinuities']:
            raise Unsupported('The derivative example keeps the original accumulation and interval')
        f=task['function']
        if f=='f(x)=sgn(x)':
            plan,_=accumulation_goal(dict(kind='integral_accumulation_function',integrand='sgn(x)',variable='x',
                                        requested_output=['indefinite_integral_of_bounded_discontinuous_function']))
            plan['argument'].append('Intersect the two sign cells with the original interval. Only derivatives from within that interval apply.')
            return plan,dict(point=ZERO,cases=[
                dict(condition='a<0<b',left=q(-1),right=ONE,derivative_exists=False),
                dict(condition='a=0<b',right=ONE),
                dict(condition='a<0=b',left=q(-1)),
                dict(condition='0 outside [a,b]',discontinuity_in_interval=False),
            ])
        if f=='f(1/n)=1 for integers n≠0; f(x)=0 elsewhere':
            return dict(theorem='method.piecewise_integral_traces', argument=[
                'All but finitely many nonzero values lie in any neighborhood of 0. Cover 0 by an arbitrarily short interval.',
                'Cover each remaining nonzero point by a short interval. The upper sums approach zero, as do all lower sums.',
                'The accumulation is constant on every original subinterval. Its derivative is zero even at the discontinuities.',
            ]),dict(accumulation='C',derivative=ZERO,discontinuities='0 and every 1/n in the original interval')
        raise Unsupported('The discontinuity set in the given example has no coverage proof')
    source_fields(task,{'integrand','variable','lower','upper','parameters','stated_conditions'})
    v=task['variable'];x=('v',v);parameters=task.get('parameters',[])
    if wanted==['accumulation_function'] and task.get('lower')=='0' and task.get('upper')==v:
        literal=task['integrand']
        match=re.fullmatch(fr'piecewise\(1 if abs\({re.escape(v)}\)<({NAME}),0 if abs\({re.escape(v)}\)>\1\)',literal)
        if not match or parameters!=[match[1]] or task.get('stated_conditions',[]) not in ([],[match[1]+'>0']):
            raise Unsupported('The indicator boundaries and isolated endpoint omissions are unproved')
        l=match[1]
        return dict(theorem='method.piecewise_integral_traces', argument=[
            'For l>0 the nonzero set is the open interval (−l,l). The two unspecified boundary values do not affect the integral.',
            'Intersect the oriented integration interval with that support and take its length. For l≤0 the support is empty.',
        ]),dict(formula=f'sgn({v})*min(abs({v}),max({l},0))',normalization='zero at origin')
    if wanted!=['indefinite_integral_of_bounded_discontinuous_function'] or parameters or set(task)&{'lower','upper'}:
        raise Unsupported('The original step accumulation statement is unresolved')
    raw=m.parse(task['integrand'],v,[],('sgn','sign','floor'))
    conditions=task.get('stated_conditions',[])
    if raw[0] in ('sign','sgn') and conditions==[]:
        inner=raw[1]
        if inner[0]=='sin':phase=inner[1]
        else:phase=inner
        k,c=affine(phase,v)
        ctx=m.context(dict(variable=v))
        slope=m.sign(k,ctx);shift=source(m.div(m.neg(c),k)) if slope else None
        if slope not in (-1,1) or not m.constant_defined(c,ctx) or domain_conditions(raw):
            raise Unsupported('The signed step phase must be regular and affine with nonzero slope')
        if inner[0]!='sin':
            formula=f'{slope}*abs({v}-({shift}))+C'
            cuts='one affine zero'
        else:
            z=f'({source(phase)})/pi';N=f'floor({z})';h=source(m.div(m.PI,k))
            formula=f'({h})*((1-(-1)^({N}))/2+(-1)^({N})*(({z})-({N})))+C'
            cuts='consecutive multiples of pi in the affine phase, with opposite signs on successive cells'
    elif raw==('floor',x) and conditions==[v+'>=0']:
        N=f'floor({v})';cuts='the nonnegative integer grid'
        formula=f'{N}*({N}-1)/2+{N}*({v}-{N})+C'
    elif raw in (('mul',x,('floor',x)),('mul',('floor',x),x)) and conditions==[v+'>=0']:
        N=f'floor({v})';cuts='the nonnegative integer grid'
        formula=f'({N}-1)*{N}*(4*{N}+1)/12+{N}*({v}^2-{N}^2)/2+C'
    elif raw==('rpow',q(-1),('floor',x)) and conditions==[]:
        N=f'floor({v})';cuts='all integer grid points, and each pair of adjacent cells has total integral zero'
        formula=f'(1-(-1)^({N}))/2+(-1)^({N})*({v}-{N})+C'
    else:raise Unsupported('The complete step partition and conditional branch values are unproved')
    return dict(theorem='method.piecewise_integral_traces', cuts=cuts, original=raw, argument=[
        'On each open cell the original piece is regular and has an elementary primitive.',
        'Add the signed integrals of complete cells and the interval up to the current position in its cell.',
        'The two neighboring accumulation values agree at every seam. Isolated assignments have zero measure.',
    ]),dict(formula=formula)


def ordered_step_cuts(raw,v,a,b,ctx):
    """Isolate every root or integer level that can change a step atom."""
    from integrals import affine,learned_nodes
    from graphs import rational_roots
    from plane_domains import yterm
    from polynomial import rf,NotRational,Undefined
    from quadrature import enclose
    from ray_proofs import compare_scalar,phase_interval,phase_zeros
    from functools import cmp_to_key

    def floor(constant):
        lo,hi=enclose(m.simplify(constant),None)
        if lo//1!=hi//1:raise Unsupported('An integer level is undecided at a sample')
        return lo//1

    step_operations={'sgn','sign','floor'}
    x=('v',v);atoms=sorted({z for z in learned_nodes(raw) if isinstance(z,tuple) and z[0] in step_operations},key=repr)
    cuts=[]
    for name,inside in atoms:
        if any(not known_guard(g,ctx) for g in domain_conditions(inside)):
            raise Unsupported('The original argument of a step function may have a hole')
        if name=='floor':
            phase=inside[1] if inside[0]=='exp' else inside
            k,c=affine(phase,v)
            if m.sign(k,ctx) not in (-1,1) or not m.constant_defined(c,ctx):
                raise Unsupported('The floor argument has no verified monotone chart')
            ends=[floor(m.substitute(inside,{x:end})) for end in (a,b)]
            levels=map(q,range(min(ends)+1,max(ends)+1))
            inverse=lambda y:m.div(m.add(y,m.neg(c)),k)
            points=[inverse(('ln',y) if inside[0]=='exp' else y) for y in levels]
        elif inside[0] in ('sin','cos'):
            tag,phase=inside;k,c=affine(phase,v)
            first,last=phase_zeros(tag,phase_interval(phase,v,a,b),False,False)
            shift=q(1,2) if tag=='cos' else ZERO
            points=[m.div(m.add(m.mul(m.add(q(j),shift),m.PI),m.neg(c)),k) for j in range(first,last+1)]
        else:
            try:p,d=rf(inside,v)
            except (NotRational,Undefined) as error:raise Unsupported('A complete sign-root isolation is required') from error
            if len(d)!=1 or p==(0,):raise Unsupported('The sign argument needs a regular nonzero polynomial')
            points=[yterm(z) for z in rational_roots(p)]
        for node in map(m.simplify,points):
            if compare_scalar(node,a)>0 and compare_scalar(node,b)<0 and not any(compare_scalar(node,z)==0 for z in cuts):
                cuts.append(node)
    if not atoms:raise Unsupported('The integrand has no finite step partition')

    def replace(place,constant=False):
        values={}
        for atom in atoms:
            name,inside=atom
            at=m.substitute(inside,{x:place})
            value=floor(at) if name=='floor' else compare_scalar(m.simplify(at),ZERO)
            values[atom]=q(value)
        e=m.substitute(raw,values)
        return m.substitute(e,{x:place}) if constant else e
    return [a,*sorted(cuts,key=cmp_to_key(compare_scalar)),b],replace


def finite_step_integral(task,request):
    from functools import reduce
    from ray_proofs import compare_scalar
    source_fields(task,{'integrand','integration_order','parameters','stated_conditions'})
    rows=task['integration_order'];parameters=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if task.get('requested_output')!=['exact_integral'] or len(rows)!=1 or set(rows[0])!={'variable','lower','upper'}:
        raise Unsupported('A one-dimensional exact integral is required')
    v=rows[0]['variable'];ctx=m.context(dict(variable=v,parameters=parameters))
    text=task['integrand'];x=('v',v)
    a,b=(m.simplify(m.parse(rows[0][k],None,parameters)) for k in ('lower','upper'))
    if parameters and len(parameters)==1 and text==f'ln(floor({v}))':
        n,=parameters
        if (conditions not in ([n+' positive integer'],[n+' is a positive integer']) or b!=m.simplify(m.add(('s',n),ONE))
                or a!=ONE):
            raise Unsupported('The finite sum of logarithms needs the original positive integer grid')
        return dict(theorem='method.piecewise_integral_traces',grid='k=1,…,n',
                    argument=['The logarithm equals ln(k) on each unit cell. Endpoint values are positive and have zero contribution.',
                              'The sum of logarithms is ln of the finite product 1·2···n.']), ('ln',('factorial',('s',n)))
    if parameters or conditions or not all(m.constant_defined(z,ctx) for z in (a,b)) or compare_scalar(a,b)>=0:
        raise Unsupported('A complete ordered finite partition with real endpoint values is required')
    if text.startswith('piecewise(') and text.endswith(')'):
        pieces=[];last=a;previous=None
        for branch in re.split(r',\s*',text[10:-1]):
            match=re.fullmatch(fr'(.+) if ([^<>]+)(<=|<){re.escape(v)}(<=|<)([^<>]+)',branch)
            if not match:raise Unsupported('Each formula needs two exact interval comparisons')
            f,s,l,r,t=match.groups();f=m.parse(f,v);p,w=(m.simplify(m.parse(z,None)) for z in (s,t))
            if not all(m.constant_defined(z,ctx) for z in (p,w)) or compare_scalar(p,last)!=0 or compare_scalar(p,w)>=0:
                raise Unsupported('The source piecewise intervals overlap or leave an open gap')
            left=m.substitute(f,{x:p});right=m.substitute(f,{x:w})
            if not all(m.constant_defined(z,ctx) for z in (left,right)):
                raise Unsupported('A source piece requires an additional endpoint limit')
            if previous:
                val,closed=previous
                if (not closed and l=='<') or (closed and l=='<=' and not same_value(val,left)):
                    raise Unsupported('A shared endpoint is missing or has inconsistent assignments')
            elif l=='<':raise Unsupported('The initial source endpoint is omitted')
            last=w;previous=(right,r=='<=');pieces.append((p,w,f))
        if not previous or not previous[1] or compare_scalar(last,b)!=0:
            raise Unsupported('The final source endpoint is omitted')
    else:
        raw=m.parse(text,v,[],('sgn','sign','floor'))
        grid,replace=ordered_step_cuts(raw,v,a,b,ctx)
        if any(not m.constant_defined(replace(p,constant=True),ctx) for p in grid):
            raise Unsupported('An originally assigned endpoint is undefined')
        pieces=[(p,w,replace(m.div(m.add(p,w),q(2)))) for p,w in zip(grid,grid[1:])]
    values=[]
    for p,w,f in pieces:
        child=dict(kind='iterated_integral',integrand=source(f),
                   integration_order=[dict(variable=v,lower=source(p),upper=source(w))],requested_output=['exact_integral'])
        values.append(freeze(request('integrate the original formula on its next regular cell',child)['value']))
    plan=dict(theorem='method.piecewise_integral_traces',pieces=pieces,integrals=values,
                argument=['Isolate all step boundaries from the original fields and check the closed-interval assignments.',
                          'Integrate the verified formula on each cell. Isolated endpoint values do not change the integral.'])
    return plan,m.combine_rational_logs(m.simplify(reduce(m.add,values,ZERO)))


def concrete_mean(expr,v,request):
    raw=m.parse(expr,v); x=('v',v); s=('s',v);dummy='__mean_ray'
    while dummy==v:dummy+='_'
    at_zero=m.context(dict(variable=dummy))
    ray=m.context(dict(variable=dummy,parameters=[v],parameter_conditions=[v+'>0']))
    if (not m.constant_defined(m.substitute(raw,{x:ZERO}),at_zero)
            or not all(known_guard((rel,m.substitute(g,{x:s})),ray) for rel,g in domain_conditions(raw))):
        raise Unsupported('The original function needs a continuous or integrable initial segment and a real ray')
    child=dict(kind='limit',expression=expr,variable=v,approach=dict(point='+inf',side='positive_infinity'))
    conclusion=freeze(request('finite pointwise limit of the original averaged function',child)['value'])
    if not isinstance(conclusion,tuple) or not m.constant_defined(conclusion,at_zero):
        raise Unsupported('The pointwise limit must be a finite real number')
    return conclusion


def oscillatory_mean(expr,v):
    """Zero average for finite waves or for sublinear amplitude with bounded primitive."""
    from integrals import affine,harmonic_modes
    raw=m.parse(expr,v);x=('v',v);ctx=m.context(dict(variable=v))
    if raw[0]=='mul':
        weight,oscillator=raw[1:]
        if weight[0] in ('sin','cos'):weight,oscillator=oscillator,weight
        power=q(1,2) if weight==('sqrt',x) else weight[2] if weight[:2]==('rpow',x) else None
        p=m.num(power) if power else None
        if p is not None and 0<p<1 and oscillator[0] in ('sin','cos'):
            a,b=affine(oscillator[1],v)
            if m.sign(a,ctx) in (-1,1) and m.constant_defined(b,ctx) and not domain_conditions(oscillator):
                return dict(theorem='method.integral_tail_mean', amplitude_power=power,phase_slope=a,argument=[
                    'The phase is affine with a nonzero slope and the wave has a bounded primitive.',
                    'By parts, the boundary is O(R^p), and the integral of the absolute derivative of the weight is R^p.',
                    'At zero p>0 gives a vanishing boundary. The normalized growth O(R^(p−1)) tends to zero.',
                ]),dict(mean=ZERO)
    modes,_,_=harmonic_modes(dict(kind='integrate',variable=v,integrand=expr))
    for (rate,freq),poly in modes.items():
        sign=m.sign(rate,ctx)
        if sign!=-1 and (sign!=0 or len(poly)!=1):
            raise Unsupported('This harmonic decomposition does not prove a bounded primitive or integrable tail')
        if not m.constant_defined(freq,ctx):raise Unsupported('An original phase is not real')
    base,imaginary=modes.get((ZERO,ZERO),[(ZERO,ZERO)])[0]
    if imaginary!=ZERO:raise Unsupported('The nonoscillatory average was not proved real')
    return dict(theorem='method.integral_tail_mean', modes=list(modes.items()),argument=[
        'For undamped nonzero frequencies the primitive is bounded. Decaying polynomial modes are integrable on the ray.',
        'The constant mode is the only one left after division by the window length.',
    ]),dict(mean=base)


def mean_goal(task,request):
    if task['kind']=='mean_on_infinite_interval':
        source_fields(task,{'variable','integrand','definition'},(['mean_value'],))
        if (task.get('definition') not in (None,'lim_(R->+inf) integral(f(x), x, 0, R)/R')
                or task.get('requested_output')!=['mean_value']):
            raise Unsupported('A different averaging window or extra output is unresolved')
        expr,v=task['integrand'],task['variable']
        try:return oscillatory_mean(expr,v)
        except Unsupported:result=dict(mean=concrete_mean(expr,v,request))
    else:
        heading='Пусть f(x)∈C[0,+∞) и lim_{x→+∞} f(x)=A. Найти lim_{x→+∞}(1/x)∫_0^x f(t)dt. Рассмотреть пример f(x)=arctg x.'
        source_fields(task,{'variable','integration_variable','function_symbol','assumptions','example'},(heading,))
        if task.get('source',{}).get('literal_requirement')==heading and task.get('example')!='atan(x)':
            raise Unsupported('The original worked example was changed')
        f,v,t=(task.get(k) for k in ('function_symbol','variable','integration_variable'))
        if (not all(isinstance(n,str) and re.fullmatch(NAME,n) for n in (f,v,t)) or len({f,v,t})!=3
                or task.get('requested_output')!=['mean_limit','proof','worked_example']):
            raise Unsupported('The general mean and its separate worked example must both be derived')
        premises=task['assumptions']
        other=fr'limit of {re.escape(f)} at \+inf is ({NAME})'
        match=re.fullmatch(other,premises[1]) if len(premises)==2 else None
        if not match or premises[0]!=f'{f} continuous on [0,+inf)':
            raise Unsupported('The pointwise limit and locally integrable interval do not match')
        example=concrete_mean(task['example'],v,request)
        result=dict(mean=match[1],worked_example=dict(function=task['example'],limit=example,mean=example))
    argument=[
        'Fix ε>0 and a tail start b such that |f(t)−A|≤ε for all t≥b. The hypothesis is a finite pointwise limit on the full ray.',
        'For R>b split the integral of f−A at b. The initial signed integral is a finite constant B by local integrability.',
        'The error in the average is bounded by |B|/R+ε(R−b)/R. Its upper limit is at most ε, so the mean tends to A.',
    ]
    return dict(theorem='method.integral_tail_mean', argument=argument,
                initial_term='abs(B)/R',tail_term='epsilon*(R-b)/R'),result


def integral_mean_bounds(task):
    """Lower an integral bound to a monotone weight and the range of a primitive."""
    kind=task['kind'];facts=task.get('stated_conditions',[])
    proof=['Use the second integral mean-value theorem for a continuous nonnegative nonincreasing weight w.',
           'The weighted integral equals w(a) times the primitive increment from the initial end to a point ξ within the interval.']
    if kind=='integral_mean_value_proof':
        source_fields(task,{'stated_conditions','method_requirement','claim'})
        if (task.get('requested_output')!=['proof'] or task.get('method_requirement')!=['integration_by_parts','first_mean_value_theorem']
                or facts!=['f continuous on [a,b]','phi continuous on [a,b], differentiable on (a,b), derivative >=0']
                or task['claim']!='integral(a,b,phi*f) = phi(a)*integral(a,xi,f)+phi(b)*integral(xi,b,f) for some xi in [a,b]'):
            raise Unsupported('The requested first mean-value and integration-by-parts proof needs the original monotone weight')
        argument=[
            'Set F(t)=∫ₐᵗ f(s)ds. By continuity, F′=f and F(a)=0.',
            'The mean-value theorem gives monotonicity of φ from φ′≥0. Use the nonnegative increments dφ as a Riemann–Stieltjes weight.',
            'Integration by parts gives ∫φf=φ(b)F(b)−∫F dφ. The first mean value theorem gives ∫F dφ=F(ξ)(φ(b)−φ(a)).',
            'The weighted mean follows from bounds on Riemann sums and continuity of F. If φ(b)=φ(a), the weight vanishes and any ξ works.',
        ]
        return dict(theorem='method.integral_mean_bounds',argument=argument),dict(identity=task['claim'],proved=True)
    if kind=='integral_inequality_proof':
        source_fields(task,{'stated_conditions','claim'})
        if (task.get('requested_output')!=['proof'] or facts!=['f continuously differentiable on [a,b]','f(a)=0','M=sup_[a,b] abs(f)']
                or task['claim']!='M^2<=(b-a)*integral(a,b,diff(f(x),x)^2,x)'):
            raise Unsupported('The original continuous derivative and zero trace must be proved')
        argument=['Write f(x)=∫ₐˣ f′ using the zero trace and Newton–Leibniz.',
                  'Cauchy–Schwarz on [a,x] gives |f(x)|²≤(x−a)∫ₐˣ(f′)².',
                  'Replace both factors by their nonnegative upper bounds over [a,b] and take the supremum.']
        return dict(theorem='method.integral_mean_bounds',argument=argument),dict(inequality=task['claim'],proved=True)
    source_fields(task,{'integrand','variable','lower','upper','parameters','stated_conditions','method_requirement'})
    if task.get('requested_output')!=['estimate_with_proof'] or task.get('method_requirement')!='second_integral_mean_value_theorem':
        raise Unsupported('The original estimate and its method must agree')
    v=task['variable'];params=task.get('parameters',[]);x=('v',v)
    a,b=(m.simplify(m.parse(task[name],None,params)) for name in ('lower','upper'))
    raw=m.parse(task['integrand'],v,params);ctx=m.context(dict(variable=v))
    if params:
        if (not all(z[0]=='s' for z in (a,b)) or a==b or not set((a[1],b[1]))<=set(params)
                or any(z[1] not in params for z in (a,b)) or f'0<{a[1]}<{b[1]}' not in facts):
            raise Unsupported('A positive interval with proved ordering is required')
        endpoint_names={a[1],b[1]}
    else:
        from ray_proofs import compare_scalar
        if facts or compare_scalar(a,ZERO)<=0 or compare_scalar(a,b)>=0:
            raise Unsupported('The original lower endpoint must be positive and below the upper endpoint')
        endpoint_names=set()
    if raw==('sin',m.power(x,2)) and set(params)==endpoint_names and len(facts)==bool(params):
        weight=m.div(ONE,m.mul(q(2),a));cosine=('cos',m.power(a,2))
        proof.insert(0,'Use u=x² on the positive source interval. Its inverse Jacobian 1/(2√u) is positive and decreasing.')
    elif raw[0]=='div' and raw[2]==x:
        wave=raw[1];damping=ONE
        additional=set(params)-endpoint_names
        if wave[0]=='mul':
            e,wave=wave[1:]
            if e[0]!='exp' or len(additional)!=1 or len(facts)!=2:
                raise Unsupported('The extra weight must be a nonincreasing exponential')
            name,=additional
            if name+'>=0' not in facts or not same_value(e[1],m.neg(m.mul(('s',name),x))) or domain_conditions(e):
                raise Unsupported('The original exponential rate does not prove a decreasing positive weight')
            damping=m.substitute(e,{x:a})
        elif additional or len(facts)!=bool(params):
            raise Unsupported('Every fixed parameter in the weight must be bound by the source')
        if wave[0]!='sin' or domain_conditions(wave):raise Unsupported('A verified primitive range is required')
        from integrals import affine
        k,c=affine(wave[1],v)
        if m.sign(k,ctx)!=1 or not m.constant_defined(c,ctx):raise Unsupported('The wave needs a positive affine rate')
        weight=m.div(damping,m.mul(a,k));cosine=('cos',m.substitute(wave[1],{x:a}))
        proof.insert(0,'The reciprocal of the positive coordinate is decreasing. The optional exponential weight is positive and nonincreasing by its original rate condition.')
    else:raise Unsupported('The original weight and known primitive cannot be separated')
    proof.append('The cosine of the terminal phase lies in [−1,1]. The cosine at the initial endpoint is kept in the bound.')
    lower,upper=(m.simplify(m.mul(weight,m.add(cosine,q(s)))) for s in (-1,1))
    return dict(theorem='method.integral_mean_bounds',weight_at_start=weight,primitive_initial_cosine=cosine,argument=proof),dict(lower=lower,upper=upper)


def integral_parameter_limit(task,request):
    """Build quantitative majorants for a window or an integrand with a changing parameter."""
    kind=task['kind'];facts=task.get('stated_conditions',[]);params=task.get('parameters',[])
    keys={'integrand','lower','upper','parameters','stated_conditions','claim','variable'}
    if kind=='limit_of_integral':
        source_fields(task,keys|{'target','integration_variable'})
        n,v=task['variable'],task['integration_variable']
        if len(params)!=1:raise Unsupported('A fixed finite window is required')
        p,=params;x=('v',v);z=('s',n)
        a,b=(m.simplify(m.parse(task[k],None,[n,p])) for k in ('lower','upper'))
        f=m.parse(task['integrand'],v)
        if (len({n,v,p})!=3 or task.get('requested_output')!=['proof'] or task.get('target')!='+inf'
                or task.get('claim')!='limit is zero' or facts!=[p+'>0'] or a!=z or b!=m.simplify(m.add(z,('s',p)))
                or f not in (m.div(('cos',x),x),m.div(('sin',x),x))):
            raise Unsupported('The original finite-width positive ray and bounded oscillatory numerator must be proved')
        bound=p+'/'+n
        child=dict(kind='limit',expression=bound,variable=n,parameters=[p],parameter_conditions=[p+'>0'],
                   approach=dict(point='+inf',side='positive_infinity'))
        val=freeze(request('limit of the positive window estimate',child)['value'])
        return dict(theorem='method.integral_limit_estimate',bound=bound,argument=[
            'On the original interval the numerator has absolute value at most one and the positive denominator is at least n.',
            'The interval has fixed length p. Bound the integral in absolute value by p/n and take its limit.']),dict(limit=val)

    source_fields(task,keys|{'parameter','parameter_domain','approach'},('Доказать равенство предела нулю.','Найти предел интеграла.'))
    v,n=task['variable'],task['parameter'];x=('v',v);index=('s',n);bounds=(task['lower'],task['upper'])
    if len({v,n,*params})!=2+len(params):
        raise Unsupported('The bound integration variable, varying parameter and fixed parameters must be distinct')
    toward=task['approach'];wanted=task.get('requested_output')
    if toward==dict(point='+inf',side='positive_infinity'):
        if (wanted!=['proof_of_stated_limit'] or task.get('claim')!='0' or task.get('parameter_domain')!='positive_integers'
                or params or facts or bounds[0]!='0'):
            raise Unsupported('The original integer limit and its zero conclusion are needed')
        e=m.parse(task['integrand'],v,[n]);end=m.parse(bounds[1],None);ctx=m.context(dict(variable=v))
        if (bounds[1]=='1' and e[0]=='div' and e[1]==('rpow',x,index) and e[2][0]=='add'
                and e[2][1]==ONE and (e[2][2]==x or e[2][2][:2]==('pow',x) and e[2][2][2]>0)):
            argument=['The denominator is at least one. The numerator is a nonnegative integer power on [0,1].',
                      'The original integral lies between zero and ∫₀¹xⁿdx=1/(n+1).']
        elif e[0]=='rpow' and e[2]==index and e[1][0]=='sin':
            from integrals import affine
            a,c=affine(e[1][1],v)
            if not m.constant_defined(end,ctx) or m.sign(a,ctx)!=1 or c!=ZERO or not same_value(m.mul(a,end),m.div(m.PI,q(2))):
                raise Unsupported('The original wave must be positive and below one except at the terminal end')
            argument=['Fix a positive strip width δ below the length of the interval.',
                      'The sine is bounded strictly below one off this terminal strip. On the strip its power is at most one.',
                      'The first integral goes to zero, and the second is at most δ. Let δ decrease to zero.']
        else:raise Unsupported('The original integer powers have no proved common integral majorant')
        return dict(theorem='method.integral_limit_estimate',argument=argument),dict(limit=ZERO,proved=True)
    if wanted!=['limit'] or 'parameter_domain' in task or 'claim' in task:
        raise Unsupported('The original finite limit needs its unmodified approach and output')
    text=task['integrand']
    if toward==dict(point='0',side='both') and bounds==('0','1') and not (params or facts):
        e=m.parse(text,v,[n]);match=re.fullmatch(fr'1/\({re.escape(n)}\*{re.escape(v)}(?:\^[1-9]\d*)?\+1\)',text)
        if not match or e[0]!='div':raise Unsupported('The perturbing field has no uniform bound on the original interval')
        return dict(theorem='method.integral_limit_estimate',argument=[
            'The nonnegative coordinate power lies in [0,1]. For |ε|<1 the original denominator is at least 1−|ε|.',
            'The difference from one is bounded uniformly by |ε|/(1−|ε|). Integrate this bound over the unit interval.']),dict(limit=ONE)
    if toward==dict(point='0',side='right') and len(params)==2 and re.fullmatch(fr'({NAME})\({re.escape(v)}\)/{re.escape(v)}',text):
        a,b=params;f=text.split('(')[0]
        if (len({a,b,f,v,n})!=5 or bounds!=(a+'*'+n,b+'*'+n)
                or facts!=[a+'>0',b+'>0',f+' continuous on [0,1]']):
            raise Unsupported('Scaling must preserve the original positive interval and continuity at zero')
        return dict(theorem='method.integral_limit_estimate',argument=[
            'The positive rescaling x=εt gives an oriented integral from a to b of f(εt)/t. Allow b<a and a=b.',
            'For sufficiently small ε all original arguments stay in [0,1]. Continuity gives uniform convergence to f(0) on the fixed scaled interval.',
            'The factor 1/t is bounded since both ends are strictly positive. Integrate the limiting kernel 1/t.']),dict(limit=f'{f}(0)*ln({b}/{a})')
    raise Unsupported('The stated parameter approach and original integration domain need a new estimate')


def improper_comparison_theorem(task):
    """Use tail mass and Cauchy estimates for quantified improper-integral questions."""
    from cartesian_fields import vector_source
    heading=task.get('source',{}).get('literal_requirement')
    vector_source(task,{'statement','requested_output'},(heading,))
    if task.get('requested_output')!=['proof_or_counterexample']:
        raise Unsupported('The source must ask the stated proof or counterexample')
    text=task['statement']
    def result(value,*argument,**certificate):
        return dict(theorem='method.parameter_endpoint_comparison',argument=argument,**certificate),value

    if re.fullmatch(r'Если интеграл от [A-Za-z_]\w* до \+∞ от ([A-Za-z_]\w*) сходится, обязательно ли \1\(x\)→0\? Рассмотреть ∫₀∞ sin \(x\)² dx\. Написание воспроизведено как в печати\.',text):
        return result(dict(implication=False,printed_example_integral='divergent',
                           counterexample=dict(support='[n,n+2^(-n)]',shape='triangular',height=ONE,peak='n+2^(-n-1)')),
            'Печатный пример есть квадрат синуса. На каждом полном периоде его интеграл — положительная постоянная, поэтому он расходится.',
            'Чтобы получить сходящийся интеграл без исчезновения функции, берём непересекающиеся треугольные пики высоты 1 и ширины 2^(−n). Их площади складываются в сходящийся геометрический ряд, а значения в вершинах равны единице.',
            triangle_area='2^(-n-1)',peak_limit=ONE,area_ratio=q(1,2))
    if text=='Тот же вопрос для ∫₀∞ (−1)^[x²] dx, где квадратные скобки обозначают целую часть.':
        return result(dict(implication=False,original_example_converges=True,original_function_has_limit=False),
            'Уровни целой части квадратной фазы дают отрезки [√j,√(j+1)). Их длины положительны, убывают к нулю и сопровождаются чередующимся знаком.',
            'Признак Лейбница даёт предел полных сумм. Последний неполный отрезок имеет ещё меньший вклад. На чётных и нечётных отрезках значения различны.',
            cell_amplitude='1/(sqrt(j+1)+sqrt(j))',partial_cell_bound='the length of its original cell')
    if re.fullmatch(r'Если ([A-Za-z_])∈C¹\[x₀,\+∞\), \|\1′\|<C и ∫ₓ₀∞\|\1\| сходится, доказать \1\(x\)→0\.',text):
        return result(dict(proved=True,limit=ZERO),
            'Если модуль функции не исчезает, существует ε>0 и уходящие вправо точки с модулем не меньше ε.',
            'Ограниченная производная удерживает модуль не меньше ε/2 на отрезках фиксированной положительной длины вокруг этих точек. Выбираем непересекающуюся подпоследовательность отрезков.',
            'Каждый из них имеет одну и ту же положительную нижнюю оценку интеграла модуля, что противоречит критерию Коши.',
            witness_radius='epsilon/(2*C)',lower_bound_per_interval='epsilon^2/(2*C)')
    if re.fullmatch(r'Можно ли для неограниченной ([A-Za-z_]) на \[a,b\] с существующим несобственным интегралом получить его как предел сумм для произвольных меток ξᵢ∈\[xᵢ,xᵢ₊₁\] при измельчении разбиения\?',text):
        return result(dict(implication=False,counterexample=dict(field='(x-a)^(-1/2) for x>a; set f(a)=0',
                           partition='uniform',first_tag='a+(b-a)/n^4')),
            'Выбираем положительное интегрируемое степенное ядро у первого конца. Его интеграл конечен по степенному порогу.',
            'На равномерной сетке первая метка лежит в исходной ячейке. Её значение, умноженное на длину ячейки, равно n√(b−a), тогда как все остальные слагаемые неотрицательны.',
            power=q(-1,2),mesh_width='(b-a)/n',total_integral='2*sqrt(b-a)')
    if re.fullmatch(r'Следует ли из сходимости ∫ₐ∞ ([A-Za-z_]) и ограниченности φ сходимость ∫ₐ∞ \1φ\? Привести пример\. Что при абсолютной сходимости первого интеграла\?',text):
        return result(dict(ordinary_implication=False,absolute_if_product_locally_integrable=True,
                           boundedness_alone_does_not_give_local_integrability=True),
            'На последовательных единичных отрезках берём чередующиеся постоянные величины 1/(n+1). Их интеграл сходится, а умножение на ограниченный знак превращает площади в гармонический ряд.',
            'При абсолютной сходимости модуль произведения ограничен константой, умноженной на исходный модуль. Сравнение даёт абсолютную сходимость, если произведение локально интегрируемо.',
            'Одна ограниченность множителя не гарантирует локальной интегрируемости Римана. Индикатор рациональных чисел, умноженный на положительную непрерывную интегрируемую функцию, даёт контрпример.',
            cell_amplitude='(-1)^n/(n+1)',bound_on_multiplier=ONE)
    if re.fullmatch(r'Доказать ([A-Za-z_])\(x\)=O\(1/x\) при сходимости ∫ₐ∞ \1 и монотонности \1\.',text):
        return result(dict(proved=True,stronger_bound='o(1/x)'),
            'У монотонной функции есть расширенный предел. Сходимость интеграла исключает любой ненулевой предел, поэтому она стремится к нулю и имеет один знак.',
            'Её модуль убывает. На отрезке [x/2,x] интеграл модуля не меньше x|f(x)|/2. Сам интеграл стремится к нулю по критерию Коши.',
            comparison_window='[x/2,x]',mass_lower_bound='x*abs(f(x))/2')
    if re.fullmatch(r'Для монотонной неограниченной у нуля ([A-Za-z_]) на \(0,1\] с существующим интегралом доказать сходимость правых равномерных сумм n⁻¹Σ \1\(k/n\) к ∫₀¹\1\.',text):
        return result(dict(proved=True,limit='the original improper integral'),
            'Сменой знака можно перейти к убывающей функции. Обозначим правую сумму через S_n.',
            'На каждой ячейке правый конец даёт нижнюю оценку интеграла, даже на первом несобственном отрезке. Поэтому S_n≤∫₀¹f.',
            'На хвосте [1/n,1] левые концы дают верхнюю оценку. Это даёт S_n≥∫_(1/n)^1 f+f(1)/n. Обе крайние величины стремятся к одному пределу.',
            mesh='1/n',lower_bound='integral(1/n,1,f)+f(1)/n',upper_bound='integral(0,1,f)')
    if re.fullmatch(r'Для монотонной ограниченной ([A-Za-z_]) на \(0,a\), если ∫₀ᵃx\^p \1\(x\)dx существует, доказать lim\(x→\+0\) x\^\(p\+1\) \1\(x\)=0\.',text):
        return result(dict(proved=True,limit=ZERO),
            'При p>−1 достаточно ограниченности функции. При p≤−1 её конечный односторонний предел обязан равняться нулю, иначе степенной вес делает интеграл расходящимся.',
            'Монотонность при нулевом пределе сохраняет знак и делает модуль неубывающим от нуля. На [x,2x] интеграл модуля не меньше |f(x)|·x^(p+1)·∫₁²s^p ds.',
            'Последний коэффициент положителен даже при p=−1. Интеграл на сжимающемся отрезке стремится к нулю по критерию Коши.',
            comparison_window='[x,2x]',scale_coefficient='integral(1,2,s^p)')
    if text=='Доказать, что при x>=0 существует li(x)=v.p.∫₀ˣ dξ/ln ξ.':
        return result(dict(printed_claim_holds=False,counterexample=dict(endpoint=ONE,divergence='negative infinity'),
                           principal_value_exists_on=['0<=x<1','1<x']),
            'У нуля обратный логарифм ограничен и стремится к нулю. Около единицы выделяется 1/(ξ−1) с ограниченным остатком.',
            'Если единица — внутренняя точка, логарифмические расходимости главных частей взаимно уничтожаются при симметричных отсечениях.',
            'Если верхний конец совпадает с единицей, остаётся одна логарифмическая расходимость. Отсечение у конечного края не образует симметричной пары.',
            principal_part='1/(xi-1)')
    raise Unsupported('The source quantifiers or comparison question are not represented')



def interval_proof(task,library,request):
    if not library.data.get('interval_integral_proofs'):
        raise Unsupported('The integral proof transitions are unavailable')
    kind=task['kind']
    if kind=='prove_or_decide_integral_statement':return improper_comparison_theorem(task)
    if kind in ('periodicity_of_integrals','proof_about_integrals'):return period_goal(task)
    if kind=='integral_identity_proof':return jump_goal(task)
    if kind in ('integral_mean_limit_theorem','mean_on_infinite_interval'):return mean_goal(task,request)
    if kind in ('integral_mean_value_proof','integral_inequality_proof','integral_bound'):return integral_mean_bounds(task)
    if kind in ('limit_of_parameter_dependent_integral','limit_of_integral'):return integral_parameter_limit(task,request)
    if kind in ('integral_derivative_example','integral_derivative_theorem','integral_accumulation_function'):
        return accumulation_goal(task)
    if kind=='iterated_integral':return finite_step_integral(task,request)
    raise Unsupported('The source goal has no integral proof transition')


# Original curve and solid measures reduce to positive sections and moments.
G_SYMBOL=r'([A-Za-z_]\w*)'
G_PI=m.PI
GEOMETRIC_COORDINATES={'x','y','z','r','phi','t'}
GEOMETRIC_FUNCTIONS={'pi','ln','sqrt','abs','exp','sin','cos','tan','atan','sinh','cosh'}


def geom_sym(s):
    return ('s',s)


def geom_minus(a,b):
    return m.add(a,m.neg(b))


def geom_sqrt(x):
    return m.simplify(('sqrt',x))


def geom_asinh(x):
    return ('ln',m.add(x,geom_sqrt(m.add(ONE,m.power(x,2)))))


def geometry_source(task,fields,extra=()):
    from cartesian_fields import vector_source
    vector_source(task,set(fields)|{'requested_output'},(),('section_convention',*extra))
    if task.get('source',{}).get('section_convention') not in (None,*POSITIVE_SECTION):
        raise Unsupported('Additional source parameter assumptions remain unbound')


def geometry_proof(method,steps,value,**checks):
    return dict(theorem='method.'+method,argument=list(steps),**checks),value



def radial_cosine_sector_volume(task):
    from cartesian_fields import vector_source
    vector_source(task,{'surfaces','stated_conditions','requested_output','method_requirement'},
                  ('Найти объём тела, ограниченного указанными поверхностями.',))
    fields=task['surfaces'];symbol=r'([A-Za-z][A-Za-z0-9_]*)'
    if task.get('method_requirement')!='polar_coordinates' or task.get('requested_output')!=['exact_volume'] or len(fields)!=4 or 'z=0' not in fields:
        raise Unsupported('A polar calculation for the original radial cosine and height plane is required')
    waves=[match for s in fields if (match:=re.fullmatch(fr'z={symbol}\*cos\(pi\*sqrt\((?:x\^2\+y\^2|y\^2\+x\^2)\)/\(2\*{symbol}\)\)',s))]
    azimuth=[match[1] for s in fields if (match:=re.fullmatch(fr'y=x\*tan\({symbol}\)',s))]
    if len(waves)!=1 or len(azimuth)!=2:raise Unsupported('The radial wave and the two azimuth planes are not bound')
    amplitude,radius=waves[0].groups()
    A,B=azimuth
    if set(task.get('stated_conditions',[]))=={radius+'>0',amplitude+'>0',f'0<={B}<{A}<=2*pi'}:A,B=B,A
    if (len({A,B,amplitude,radius,'x','y','z','pi'})!=8 or
            set(task.get('stated_conditions',[]))!={radius+'>0',amplitude+'>0',f'0<={A}<{B}<=2*pi'}):
        raise Unsupported('The ordered azimuths and original positive scales are needed')
    c,a=map(geom_sym,(amplitude,radius));k=m.div(G_PI,m.mul(q(2),a))
    central=m.mul(c,geom_minus(m.div(a,k),m.div(ONE,m.power(k,2))))
    j='j'
    while j in {A,B,amplitude,radius}:j+='_'
    idx=m.add(geom_sym(j),ONE)
    annular=m.div(m.mul(q(4),m.mul(idx,m.mul(a,c))),k)
    return geometry_proof('radial_periodic_solid_cells',[
        'Переходим в полярные координаты. Каждая записанная плоскость проходит через ось z и задаёт две азимутальные границы, отличающиеся на π.',
        'Сначала сохраняем условие определённости тангенсов. Если плоскости совпадают, остаются два полупространства. Иначе углы соседних секторов равны δ и π−δ, где δ — разность азимутов по модулю π.',
        'Высота волны меняет знак при r=(2j+1)a. В каждом ограниченном теле берём абсолютную высоту и множитель r из полярного якобиана.',
        'Первообразная r cos(kr) есть r sin(kr)/k+cos(kr)/k². В центральной ячейке нижнее значение равно 1/k². В кольцах косинус на обоих концах исчезает и синусы противоположны.',
        'У секторных компонент объёмы получаются умножением на ширину их сектора. Сумма по всем радиальным ячейкам расходится.'
    ],dict(radial_cells=[dict(interval=f'[0,{radius}]',per_radian=central),
                         dict(index=j+' integer >=0',interval=f'[(2*{j}+1)*{radius},(2*{j}+3)*{radius}]',per_radian=annular)],
            azimuth_cases=[
                dict(condition=f'cos({A})*cos({B})=0',status='at least one original plane expression is undefined'),
                dict(condition=f'cos({A})*cos({B})!=0 and ({B}-{A}) mod pi=0',angles=['pi','pi'],count=2),
                dict(condition=f'cos({A})*cos({B})!=0 and delta=({B}-{A}) mod pi in (0,pi)',
                     angles=['delta','pi-delta','delta','pi-delta'],count=4)],
            formula='volume of each cell = sector width * corresponding radial moment',
            total_volume_of_all_cells='+inf for defined planes'),radial_frequency=k)


def compose_geometry(task,library,request):
    kind=task['kind']
    if kind=='bounded_solid_volume' and task.get('method_requirement')=='polar_coordinates':
        return radial_cosine_sector_volume(task)
    if kind in ('area_bounded_by_curves','curve_arc_length','solid_of_revolution'):
        if kind=='area_bounded_by_curves':return geometrical_area(task,request)
        if kind=='curve_arc_length' or task['requested_output']==['surface_area']:
            return geometrical_metric(task,request)
        return geometrical_rotation_volume(task,request)
    if kind=='volume_bounded_by_surfaces':return geometrical_volume(task,request)
    if kind in ('geometric_moments','geometric_proof_or_calculation'):return geometrical_argument(task,request)
    if kind=='physical_model_from_statement':return physical_measure(task,request)
    if kind=='ellipse_perimeter_approximation':return certified_ellipse_perimeter(task)
    raise Unsupported('A new source geometric application is not required for the existing route')


def graph_shape(task,solid=False):
    fields=({'boundary','axis','method_requirement'} if solid else {'equations','coordinate_system'})|{'stated_conditions','parameters'}
    geometry_source(task,fields)
    eq=task['boundary' if solid else 'equations']
    cond=task.get('stated_conditions',[])
    if (not isinstance(eq,list) or not eq or not all(isinstance(s,str) for s in eq) or not isinstance(cond,list)
            or task.get('coordinate_system','rectangular') not in ('rectangular','polar','parametric')):
        raise Unsupported('The original locus equations and coordinate system must be bound')
    parameters=task.get('parameters',[])
    if (not all(isinstance(s,str) for s in cond) or not isinstance(parameters,list)
            or any(not isinstance(p,str) or p in GEOMETRIC_COORDINATES|GEOMETRIC_FUNCTIONS
                   or p not in re.findall(G_SYMBOL,' '.join(eq+cond)) for p in parameters)):
        raise Unsupported('An original independent parameter was lost')
    method=task.get('method_requirement')
    if method is not None and (method!='polar_coordinates' or eq!=['(x^2+y^2)^2=a^2*(x^2-y^2)']
                               or task['requested_output']!=['volume']):
        raise Unsupported('No verified measure transition preserves the stated method')
    domain=task.get('source',{}).get('section_convention')
    if domain is None:
        required=(set(re.findall(G_SYMBOL,' '.join(eq)))|set(parameters))-GEOMETRIC_COORDINATES-GEOMETRIC_FUNCTIONS
        required={p+'>0' for p in required if p!='n' or 'n>-2' not in cond}
        if required-set(cond):
            raise Unsupported('Positive scales must be established on the original source')
    else:required={p+'>0' for p in parameters}
    if 'half turn bounds the figure' not in cond:cond=[c for c in cond if c not in required]
    return eq,cond


def geometrical_area(task,request):
    eq,cond=graph_shape(task);a=geom_sym('a');a2=m.power(a,2)
    if task['requested_output']!=['bounded_area']:raise Unsupported('The original area request was changed')
    coord=task['coordinate_system']
    if coord=='polar':return polar_boundary_area(eq,cond)
    if coord=='parametric':
        if eq==['x=a*(cos(t)+t*sin(t))','y=a*(sin(t)-t*cos(t))','x=a'] and cond==['0<=t<=2*pi','y<=0 on x=a']:
            t=('v','t')
            proof,length=curve_chart_moment(m.mul(m.div(a2,q(2)),m.power(t,2)),'t',['a'],['a>0'],ZERO,m.mul(q(2),G_PI),
                                            request,'integrate the original involute area one-form')
            return geometry_proof('closed_parametric_measure',[
                'The squared norm on the spiral-like trace is a²(1+t²), so the arc covers each point once.',
                'At x=a, besides the two endpoints the half-angle equation is tan(t/2)=t and its positive root has y=at>0. It is outside the selected closing segment.',
                'The arc pulls back the area one-form to a²t²/2. The upward vertical segment adds πa².'],
                dict(area=m.add(length,m.mul(G_PI,a2))),arc_integral=proof)
        raise Unsupported('The original parametric closure or trace remains open')
    if eq==['y=a^3/(a^2+x^2)','y=0'] and cond in ([],['a>0']):
        return geometry_proof('graph_area_with_ends',[
            'The positive graph has no finite intersection with the lower axis. Use both improper ends of the full x-axis.',
            'With x=au the density is a²/(1+u²). The two arctangent limits give πa².'],dict(area=m.mul(G_PI,a2),scope='a>0'))
    if (not cond and len(eq)==1 and (w:=re.fullmatch(fr'y\^2=x\^2\*?\({G_SYMBOL}\^2-x\^2\)',eq[0]))
            and w[1] not in GEOMETRIC_COORDINATES|GEOMETRIC_FUNCTIONS):
        A=geom_sym(w[1]);cube=m.power(('abs',A),3)
        return geometry_proof('graph_area_with_ends',[
            'On x≥0 the real y branches are ±x sqrt(a²−x²), with 0≤x≤|a|. Reflection gives the other loop.',
            'Integrate their width using a²−x². The loops meet only at the origin, so both areas add.'],
            dict(area=m.mul(q(4,3),cube),each_loop=m.mul(q(2,3),cube)))
    if eq==['y^2=2*p*x','27*p*y^2=8*(x-p)^3'] and not cond:
        return geometry_proof('graph_area_with_ends',[
            'For p>0 the two branches with the same y² meet at x=4p. The factorization in x/p is (x/p−4)(2x/p+1)². The negative root has no real y on the parabola.',
            'On [0,4p] integrate the full parabolic width. On [p,4p] subtract the interior semicubical width after comparing the positive square roots.',
            'The two elementary power integrals leave 88 sqrt(2) p²/15.'],
            dict(area=m.mul(m.mul(q(88,15),geom_sqrt(q(2))),m.power(geom_sym('p'),2)),scope='p>0'))
    if eq==['y^2=x^3/(2*a-x)','x=2*a'] and not cond:
        return geometry_proof('graph_area_with_ends',[
            'Both real branches occur between 0 and the asymptote x=2a for a>0. Their width is 2x^(3/2)/sqrt(2a−x).',
            'The endpoint singularity has exponent −1/2 and is integrable. Set x=2au and apply B(5/2,1/2)=3π/8.'],
            dict(area=m.mul(q(3),m.mul(G_PI,a2)),scope='a>0'))
    if eq==[TRACTRIX,'y=0'] and not cond:
        return geometry_proof('tractrix_measure',[
            'For 0<y≤a the original logarithm is real and x is decreasing from +∞ to 0.',
            'Differentiation gives |dx/dy|=sqrt(a²−y²)/y. Multiply by the height y to obtain a quarter-disk density with finite lower limit.'],
            dict(area=m.mul(q(1,4),m.mul(G_PI,a2)),scope='a>0',region='under the maximal trace for x≥0'))
    if eq==['y^2=x^n/(1+x^(n+2))^2'] and cond==['x>0','n>-2']:
        return geometry_proof('graph_area_with_ends',[
            'The width is twice x^(n/2)/(1+x^(n+2)). For all n>−2 the change u=x^((n+2)/2) covers the full positive ray once.',
            'Its derivative supplies the numerator power. The resulting positive arctangent integral proves both original improper endpoints converge.'],
            dict(area=m.div(m.mul(q(2),G_PI),m.add(geom_sym('n'),q(2))),scope='n>-2'))
    if eq==['y=exp(-x)*abs(sin(x))','y=0'] and cond==['x>=0']:
        p=('exp',m.neg(G_PI))
        return geometry_proof('repeated_positive_sections',[
            'Split the half-line at all multiples of π. The absolute sine is the same nonnegative bump on every strip of length π.',
            'The integral on the first strip is (1+exp(−π))/2. Translating to the next strip multiplies the area by exp(−π), a positive factor below one.'],
            dict(area=m.div(m.add(ONE,p),m.mul(q(2),geom_minus(ONE,p)))))
    raise Unsupported('No checked width and complete set of ends for the original planar region')


def polar_boundary_area(eq,cond):
    a=geom_sym('a');a2=m.power(a,2);pi2=m.power(G_PI,2)
    result=None
    if eq==['r=a*cos(phi)','r=a*(cos(phi)+sin(phi))'] and cond==['M(a/2,0) belongs to the requested region']:
        result=m.mul(q(1,4),m.mul(a2,geom_minus(G_PI,ONE)))
        steps=['M lies in both disks, selecting their intersection.',
            'Use the smaller positive radius. The cap is a(cosφ+sinφ) on [−π/4,0] and a cosφ on [0,π/2].',
            'Integrate half the squared cap over each of the two angular intervals.']
    elif eq==['phi=r*atan(r)','phi=0','phi=pi/sqrt(3)'] and not cond:
        result=m.add(m.div(G_PI,m.mul(q(2),geom_sqrt(q(3)))),geom_minus(q(1,2),m.div(('ln',q(4)),q(6))))
        steps=['The angle r atan(r) increases on r≥0. Its upper printed angular endpoint occurs at r=sqrt(3).',
               'Use the area density r² dφ/2 and let r vary between 0 and sqrt(3).',
               'Integrate r² atan(r) by parts and integrate the remaining rational term.']
    elif eq==['r^2+phi^2=1'] and not cond:
        result=q(2,3)
        steps=['For the nonnegative radius, the angular interval is [−1,1], and each ray has upper squared radius 1−φ².',
               'The half-squared-radius integral gives the area on the whole sector.']
    elif eq==['phi=sin(pi*r)'] and cond==['0<=r<=1','one petal']:
        result=m.div(ONE,G_PI)
        steps=['Each angle from 0 to 1 has two radius endpoints, arcsin(φ)/π and 1−arcsin(φ)/π.',
               'The ray φ=0 closes the selected petal. Integrate half their difference of squares, using the elementary arcsine primitive.']
    elif eq==['phi=4*r-r^3','phi=0'] and not cond:
        result=q(64,15)
        steps=['The positive-radius loop begins at r=0 and closes on the ray at r=2. Its maximal angle is 16/(3sqrt(3))<π.',
               'The area one-form integrated along this arc gives an oriented integral of r² φ′(r)/2. Reverse sign for its clockwise orientation.',
               'Since the angular endpoints are zero, integration by parts gives the positive integral of r(4r−r³).']
    elif eq==['phi=r-sin(r)','phi=pi'] and not cond:
        result=m.add(m.div(m.power(G_PI,3),q(6)),G_PI)
        steps=['Use the first sector between angular labels 0 and π. The function r−sin(r) is strictly increasing although its derivative has isolated zeros.',
               'The first endpoint at φ=π is r=π. The radial-parameter area integral is r²(1−cos(r))/2.',
               'Integrate the cosine term twice by parts.']
    elif eq==['r=2*a*t/(1+t^2)','phi=pi*t/(1+t)'] and cond==['closed curve']:
        result=m.mul(m.mul(G_PI,a2),geom_minus(ONE,m.div(G_PI,q(4))))
        steps=['For a>0 and nonnegative radius use t≥0. The angle is one-to-one from 0 to π, and both ends have radius zero.',
               'The area form gives 2πa² times the integral of t²/[(1+t²)²(1+t)²] over the positive line.',
               'The rational decomposition is 1/[4(t+1)²]−1/[4(1+t²)]+t/[2(1+t²)²]. Evaluate the three convergent terms.']
    if result is None:raise Unsupported('No single positive polar coverage for the original boundary')
    return geometry_proof('inverted_polar_boundary_measure',steps,dict(area=m.simplify(result)))


TRACTRIX='x=a*ln((a+sqrt(a^2-y^2))/y)-sqrt(a^2-y^2)'


def root_power_primitive(u,n):
    """Primitive of the even radical weight u^(2n)*sqrt(1+u²)."""
    radius=geom_sqrt(m.add(ONE,m.power(u,2)))
    G=m.div(m.add(m.mul(u,radius),geom_asinh(u)),q(2))
    for j in range(1,n+1):
        G=m.div(geom_minus(m.mul(m.power(u,2*j-1),m.power(radius,3)),m.mul(q(2*j-1),G)),q(2*j+2))
    return m.simplify(G)


def root_reciprocal_primitive(u):
    r=geom_sqrt(m.add(ONE,m.power(u,2)))
    return m.add(r,('ln',m.div(u,m.add(ONE,r))))


def parabola_metric(eq,cond,axis):
    if len(eq)!=1 or not (w:=re.fullmatch(fr'y\^2=2\*{G_SYMBOL}\*x',eq[0])) or len(cond)!=1:
        return None
    rng=re.fullmatch(fr'0<=x<={G_SYMBOL}',cond[0])
    if not rng or {w[1],rng[1]} & (GEOMETRIC_COORDINATES|GEOMETRIC_FUNCTIONS):return None
    P,X=map(geom_sym,(w[1],rng[1]));U=geom_sqrt(m.div(m.mul(q(2),X),P))
    steps=['Use u=y/p so x=p u²/2, with arc speed p sqrt(1+u²). The exact endpoint is U=sqrt(2 x0/p).']
    if axis is None:
        value=m.mul(P,root_power_primitive(U,0))
        return geometry_proof('positive_radical_curve_metric',steps+[
            'The two x-positive branches meet at the vertex. The same positive metric gives both lengths.'],
            dict(arc_length=m.mul(q(2),value),each_branch=value,scope=f'{w[1]}>0, {rng[1]}>=0'))
    if axis=='y=0':
        D=geom_minus(m.power(geom_sqrt(m.add(ONE,m.power(U,2))),3),ONE)
        S=m.mul(m.mul(q(2,3),G_PI),m.mul(m.power(P,2),D))
        steps+=['The two branches generate the same surface, so use only y≥0 with weight p u.',
                'Integrate u sqrt(1+u²) using 1+u².']
    elif axis=='x=0':
        S=m.mul(m.mul(q(2),G_PI),m.mul(m.power(P,2),root_power_primitive(U,1)))
        steps+=['The two branches have different axial heights, so both halves contribute.',
                'The radial weight is p u²/2, giving the even radical moment on a positive half-interval.']
    else:return None
    return geometry_proof('positive_radical_curve_metric',steps,dict(surface_area=m.simplify(S),scope=f'{w[1]}>0, {rng[1]}>=0'))


def geometrical_metric(task,request):
    solid=task['kind']=='solid_of_revolution';eq,cond=graph_shape(task,solid)
    axis=task['axis'] if solid else None;coord=task.get('coordinate_system')
    if task['requested_output']!=['surface_area' if solid else 'arc_length']:
        raise Unsupported('The original curve metric output is unresolved')
    if (solid or coord=='rectangular') and (result:=parabola_metric(eq,cond,axis)):return result
    a,b,c=(geom_sym(s) for s in 'abc');a2=m.power(a,2)
    if not solid and coord=='rectangular':
        if (eq==['y=exp(x)'] and (w:=re.fullmatch(fr'0<=x<={G_SYMBOL}',cond[0] if len(cond)==1 else ''))
                and w[1] not in GEOMETRIC_COORDINATES|GEOMETRIC_FUNCTIONS):
            high=('exp',geom_sym(w[1]))
            return geometry_proof('positive_radical_curve_metric',[
                'The exponential coordinate u=e^x is increasing and nowhere zero. The length density is sqrt(1+u²)du/u.',
                'The reciprocal radical primitive has logarithm of a positive quotient on the full transformed interval.'],
                dict(arc_length=geom_minus(root_reciprocal_primitive(high),root_reciprocal_primitive(ONE)),scope=w[1]+'>=0'))
        if eq==['y=a*ln(a^2/(a^2-x^2))'] and cond==['0<=x<=b<a']:
            val=geom_minus(m.mul(a,('ln',m.div(m.add(a,b),geom_minus(a,b)))),b)
            return geometry_proof('positive_radical_curve_metric',[
                'Differentiation gives 2ax/(a²−x²). The squared speed is exactly (a²+x²)²/(a²−x²)².',
                'Use the positive square root on 0≤x≤b<a and integrate its partial fractions.'],
                dict(arc_length=m.simplify(val)))
        if eq==['y=ln(cos(x))'] and cond==['0<=x<=a<pi/2']:
            return geometry_proof('positive_radical_curve_metric',[
                'The original logarithm is defined with cos x>0. The derivative −tan x gives positive speed sec x.',
                'The primitive ln(sec x+tan x) vanishes at x=0.'],
                dict(arc_length=('ln',m.add(('sec',a),('tan',a)))))
        if eq==[TRACTRIX] and cond==['0<b<=y<=a']:
            return geometry_proof('tractrix_measure',[
                'On the original positive y branch, x′(y)=−sqrt(a²−y²)/y. Thus ds=a dy/y.',
                'Both endpoints are in the positive logarithmic domain, so the length is the stated log quotient.'],
                dict(arc_length=m.mul(a,('ln',m.div(a,b)))))
        if eq==['y^3=x^3/(2*a-x)'] and cond==['0<=x<=5*a/3']:
            return geometry_proof('positive_radical_curve_metric',[
                'Solve the original real cube equation for y and let u=(2a−x)^(1/3). This is a monotone map with positive bounds.',
                'The transformed coordinates are x=2a−u³ and y=2a/u−u². Differentiate both and take their positive Euclidean norm.',
                'The resulting bounded one-dimensional density determines the length exactly and is smooth on the positive integration interval.'],
                dict(arc_length=dict(integrand='sqrt(9*u^8+4*(u^3+a)^2)/u^2',variable='u',
                                     bounds=['(a/3)^(1/3)','(2*a)^(1/3)'])))
    if not solid and coord=='parametric':
        if eq==['x=c^2*cos(t)^3/a','y=c^2*sin(t)^3/b'] and cond==['c^2=a^2-b^2']:
            A=m.div(m.power(c,2),a);B=m.div(m.power(c,2),b)
            val=m.div(m.mul(q(4),m.add(m.add(m.power(A,2),m.mul(A,B)),m.power(B,2))),m.add(A,B))
            return geometry_proof('positive_radical_curve_metric',[
                'Use the nonnegative axis scales A=c²/a and B=c²/b from the actual parameters. In the nondegenerate case one quadrant is covered monotonically.',
                'Its speed is 3 sin t cos t times sqrt(A² cos²t+B² sin²t). Use u=sin²t and multiply by four.',
                'The quotient of differences of cubes and squares simplifies to (A²+AB+B²)/(A+B). The collapsed curve has zero length.'],
                dict(arc_length=m.simplify(val),scope='a>b>0, c²=a²−b²',degenerate='0 if c=0'))
        if eq==['x=cos(t)^4','y=sin(t)^4'] and not cond:
            return geometry_proof('positive_radical_curve_metric',[
                'The first quarter period covers the entire trace sqrt(x)+sqrt(y)=1 once, whereas subsequent quarters repeat it.',
                'Use u=sin²t in the speed. The density becomes 2 sqrt(u²+(1−u)²)du on [0,1]. Center the quadratic and use the even radical primitive.'],
                dict(arc_length=m.add(ONE,m.div(geom_asinh(ONE),geom_sqrt(q(2))))))
        if eq in (['x=a*(sinh(t)-t)','y=a*(cosh(t)-1)'],['x=cosh(t)^3','y=sinh(t)^3']) and cond==['0<=t<=T']:
            end=geom_sym('T')
            if eq[0].startswith('x=a'):
                hi=m.mul(geom_sqrt(q(2)),('cosh',m.div(end,q(2))))
                def primitive(u):
                    D=geom_sqrt(geom_minus(m.power(u,2),ONE))
                    return geom_minus(m.mul(u,D),('ln',m.add(u,D)))
                val=m.mul(m.mul(geom_sqrt(q(2)),a),geom_minus(primitive(hi),primitive(geom_sqrt(q(2)))))
                steps=['The speed is 2a sinh(t/2) sqrt(cosh(t)) for t≥0.',
                       'Use u=sqrt(2) cosh(t/2), yielding the elementary positive radical sqrt(u²−1) times 2sqrt(2)a.']
            else:
                val=m.div(geom_minus(m.power(geom_sqrt(('cosh',m.mul(q(2),end))),3),ONE),q(2))
                steps=['The speed is 3 sinh(t) cosh(t) sqrt(cosh(2t)). The positive derivative of cosh(2t) supplies this product.',
                       'Use u=cosh(2t), so the remaining primitive is a positive power on the full original interval.']
            return geometry_proof('positive_radical_curve_metric',steps,dict(arc_length=m.simplify(val),scope='T>=0'))
    if not solid and coord=='polar':
        if eq==['r=p/(1+cos(phi))'] and cond==['abs(phi)<=pi/2']:
            p=geom_sym('p')
            return geometry_proof('positive_radical_curve_metric',[
                'The polar speed is p sec³(φ/2)/2. The original denominator stays positive on the whole interval.',
                'Use a half-angle and even symmetry, then the secant-cube primitive.'],
                dict(arc_length=m.mul(p,m.add(geom_sqrt(q(2)),geom_asinh(ONE)))))
        if eq==['r=a*sin(phi/3)^3'] and not cond:
            return geometry_proof('positive_radical_curve_metric',[
                'Adding 3π reverses the radius and the unit-ray direction, so the physical trace repeats.',
                'On one nonnegative-radius period [0,3π], the only nonzero repeated point is at the angles π/2 and 5π/2, isolated.',
                'The polar metric reduces to a sin²(φ/3), whose integral is 3πa/2.'],
                dict(arc_length=m.mul(q(3,2),m.mul(G_PI,a)),scope='a>0'))
    if not solid and coord!='rectangular':
        raise Unsupported('The original metric chart or parameter range is unresolved')
    if eq==['x^(2/3)+y^(2/3)=a^(2/3)'] and not cond and axis in (None,'y=0'):
        if axis is None:
            return geometry_proof('positive_radical_curve_metric',[
                'Four equal monotone quadrants of the real cube-root trace cover the curve once.',
                'The speed on the first quadrant is 3a sin t cos t. Integrate and sum the four lengths.'],
                dict(arc_length=m.mul(q(6),a),scope='a>0'))
        return geometry_proof('distance_weighted_surface',[
            'The upper half of the symmetric astroid produces the whole image about Ox once. Its two quadrants have equal positive moments.',
            'Multiply speed 3a sin t cos t by radius a sin³t on one quadrant and integrate its elementary sine power.'],
            dict(surface_area=m.mul(q(12,5),m.mul(G_PI,a2)),scope='a>0'))
    if solid:return weighted_rotation_surface(eq,cond,axis,request)
    raise Unsupported('No original length chart with its exact endpoints was established')


def weighted_rotation_surface(eq,cond,axis,request):
    a,b=(geom_sym(s) for s in 'ab')
    scale=m.mul(q(2),m.mul(G_PI,m.power(a,2)))
    if eq==['y=x*sqrt(x/a)'] and cond==['0<=x<=a'] and axis=='y=0':
        value=m.mul(m.mul(q(64,243),scale),root_power_primitive(q(3,2),2))
        steps=['The graph is nonnegative on 0≤x≤a. Its rotation sweeps the surface once.',
               'Substitute u=3 sqrt(x/a)/2 into 2π y ds. The resulting moment is (128πa²/243)∫₀^(3/2) u⁴ sqrt(1+u²) du.',
               'Use the polynomial radical recurrence obtained by differentiating u^(2n−1)(1+u²)^(3/2).']
    elif eq==['y=a*cos(pi*x/(2*b))'] and cond==['abs(x)<=b'] and axis=='y=0':
        k=m.div(G_PI,m.mul(q(2),b));A=m.mul(a,k)
        value=m.mul(m.div(m.mul(q(2),m.mul(G_PI,a)),k),
                    m.add(geom_sqrt(m.add(ONE,m.power(A,2))),m.div(geom_asinh(A),A)))
        steps=['On |x|≤b the graph radius is nonnegative and each axial coordinate occurs once.',
               'With k=π/(2b), the substitution u=sin kx changes the distance weighted surface to a quadratic radical moment on [−1,1].']
    elif eq==['y=tan(x)'] and cond==['0<=x<=pi/4'] and axis=='y=0':
        value=m.mul(G_PI,geom_minus(root_reciprocal_primitive(q(2)),root_reciprocal_primitive(ONE)))
        steps=['The tangent graph and its slope are finite from 0 to π/4. The surface moment uses its nonnegative distance tan x.',
               'With u=sec²x, du=2u tan x dx and the surface is π∫₁² sqrt(1+u²)/u du. Evaluate its logarithmic primitive at both ends.']
    elif eq==['x^2/a^2+y^2/b^2=1'] and cond==['0<b<=a'] and axis in ('x=0','y=0'):
        e2=geom_minus(ONE,m.div(m.power(b,2),m.power(a,2)));e=geom_sqrt(e2)
        atanh=m.div(('ln',m.div(m.add(ONE,e),geom_minus(ONE,e))),q(2))
        if axis=='y=0':
            value=m.mul(m.mul(q(2),m.mul(G_PI,m.power(b,2))),
                        m.add(ONE,m.div(m.mul(a,('asin',e)),m.mul(b,e))))
        else:value=m.mul(scale,m.add(ONE,m.div(m.mul(geom_minus(ONE,e2),atanh),e)))
        steps=['A half ellipse at nonnegative distance produces every circular parallel once.',
               'For a>b, use e²=1−b²/a² and cosine or sine of the ellipse parameter to integrate its quadratic radical metric.',
               'For a=b, e=0 and the original surface is a sphere. Compute that branch without dividing by e.']
        return geometry_proof('distance_weighted_surface',steps,
                              dict(surface_area_cases=[dict(condition='0<b<a',value=value),
                                                       dict(condition='0<b=a',value=m.mul(q(2),scale))]))
    elif eq==['+/-'+TRACTRIX] and not cond and axis=='y=0':
        value=m.mul(q(2),scale)
        steps=['The signed tractrix branches have opposite x and common range 0<y≤a. No two positive-length parts sweep the same surface.',
               'On each branch ds=a |dy|/y. The distance y cancels the singular denominator, and the endpoint limit is finite.']
    elif eq==['x=a*cos(t)^3','y=a*sin(t)^3'] and not cond and axis=='y=x':
        value=m.mul(m.mul(q(3,10),scale),geom_minus(m.mul(q(4),geom_sqrt(q(2))),ONE))
        steps=['Reflection in the diagonal duplicates the surface. Select y≥x, which corresponds to π/4≤t≤5π/4.',
               'The radius is (y−x)/sqrt 2 and ds=3a|sin t cos t|dt. Split at π/2 and π to integrate the signed trigonometric powers.']
    elif eq==['r^2=a^2*cos(2*phi)'] and not cond and axis in ('polar axis','phi=pi/2','phi=pi/4'):
        aweights={'polar axis':geom_minus(q(2),geom_sqrt(q(2))),'phi=pi/2':geom_sqrt(q(2)),'phi=pi/4':q(2)}
        value=m.mul(scale,aweights[axis])
        steps=lemniscate_axis_argument(axis)+[
            'On each lobe, r ds=a² dφ by r²=a² cos 2φ. Multiply by the absolute sine or cosine of the angle to the axis and integrate the selected intervals.']
    else:raise Unsupported('No checked distance, metric, and one-covering curve for this rotation surface')
    return geometry_proof('distance_weighted_surface',steps,dict(surface_area=m.simplify(value),scope='positive geometric scales'))


def lemniscate_axis_argument(axis):
    if axis in ('y=0','polar axis'):
        return ['The real lobes have angles |φ|≤π/4 and its opposite interval. Select their upper halves, whose reflections duplicate the rotation.']
    if axis in ('x=0','phi=pi/2'):
        return ['The real lobes have angles |φ|≤π/4 and its opposite interval. The left lobe reflects onto the right, so count the right lobe only.']
    return ['The two lobes lie on different axial sides of the diagonal by the sign of x+y. Their rotated images have disjoint interiors.']


def geometrical_rotation_volume(task,request):
    eq,cond=graph_shape(task,True);axis=task['axis'];out=task['requested_output']
    a,b,p=(geom_sym(s) for s in 'abp')
    cube=m.power(a,3);P=G_PI;P2=m.power(P,2)
    method='rotated_radial_sections'
    if eq==['y^2=2*p*x','x=p/2'] and axis=='y=p' and not cond and out==['volume','surface_area']:
        volume=m.mul(q(4,3),m.mul(P,m.power(p,3)))
        surface=m.mul(q(2),m.mul(P,m.mul(m.power(p,2),m.add(q(2),m.add(geom_sqrt(q(2)),geom_asinh(ONE))))))
        return geometry_proof('rotated_radial_sections',[
            'For p>0 the fiber is −sqrt(2px)≤y≤sqrt(2px), with 0≤x≤p/2. Thus the radii about y=p are p±sqrt(2px).',
            'Integrate π times the difference of squared radii. Radius zero happens only at the terminal section.',
            'The mirror arcs have mean distance p from the axis and total metric length p(sqrt 2+asinh 1). The closing chord sweeps a disk of radius 2p.'],
            dict(volume=volume,surface_area=surface,scope='p>0'))
    if out!=['volume']:raise Unsupported('The original rotation volume output was changed')
    if eq==['x^2-x*y+y^2=a^2'] and axis=='y=0' and not cond:
        value=m.mul(q(8,3),m.mul(P,cube))
        steps=['The fibers are y=x/2±sqrt(a²−3x²/4), defined on |x|≤2a/sqrt 3, for a>0.',
               'Reflection through the origin makes the section area even. For 0≤x≤a take a disk with outside radius y₊. On a≤x≤2a/sqrt 3 subtract the inner disk of radius y₋.',
               'The polynomial part of πy₊² integrates on the first interval. The cross terms reduce to the same x sqrt(a²−3x²/4) primitive on both intervals.']
    elif eq==['y=exp(-x)*sqrt(sin(x))'] and axis=='y=0' and cond==['0<=x<+inf']:
        w=('exp',m.neg(m.mul(q(2),P)));value=m.div(P,m.mul(q(5),geom_minus(ONE,w)))
        steps=['The real square root selects only [2kπ,(2k+1)π], k≥0. The axis projections of different components have disjoint interiors.',
               'A disk section has area πe^(−2x) sin x. The first half period integrates to π(1+e^(−2π))/5.',
               'Translate by 2π to get a geometric ratio e^(−4π)∈(0,1), and cancel the positive sum factor.']
        method='repeated_positive_sections'
    elif eq==['x=a*(t-sin(t))','y=a*(1-cos(t))','y=0'] and cond==['0<=t<=2*pi'] and axis in ('y=0','x=0','y=2*a'):
        value={'y=0':m.mul(q(5),m.mul(P2,cube)),
               'x=0':m.mul(q(6),m.mul(m.power(P,3),cube)),
               'y=2*a':m.mul(q(7),m.mul(P2,cube))}[axis]
        steps=['The arch has increasing x, nonnegative height, and closes on the axis y=0 between x=0 and x=2πa.',
               'Integrating y dx and y²dx/2 gives area 3πa² and first horizontal-axis moment 5πa³/2. Reflection gives x-coordinate πa for the centroid.',
               'For the specified axis the whole segment lies on one side. Apply the area first moment with distance to that axis; boundary touching has measure zero.']
        method='one_sided_rotation_moment'
    elif eq==['x=a*sin(t)^3','y=b*cos(t)^3'] and cond==['0<=t<=2*pi'] and axis in ('y=0','x=0'):
        along,across=(a,b) if axis=='y=0' else (b,a)
        value=m.mul(q(32,105),m.mul(P,m.mul(along,m.power(across,2))))
        steps=['The upper half of an astroid section and its reflected lower half sweep the same disks.',
               'After swapping coordinates when required, each disk has squared radius B²(1−(|x|/A)^(2/3))³ on |x|≤A.',
               'Set u=(x/A)^(2/3) on x≥0 and integrate the polynomial times sqrt u, using reflection for the other half.']
    elif eq==['x=2*t-t^2','y=4*t-t^3'] and axis in ('y=0','x=0') and cond==['area inside the loop']:
        value=m.mul(q(64,35 if axis=='y=0' else 105),P)
        steps=['The bounded component closes at t=0,2. Its two preimages of x∈[0,1] are t=1±sqrt(1−x), giving ordered y=x(3±sqrt(1−x)).',
               'Use the difference of squared radii about Ox or the shell density 2πx times the width about Oy. Both are positive multiples of x² sqrt(1−x).',
               'Integrate this factor on [0,1] using 1−x=u.']
    elif eq==['r=a*(1+cos(phi))'] and cond==['0<=phi<=2*pi'] and axis in ('polar axis','r*cos(phi)=-a/4'):
        if axis=='polar axis':
            value=m.mul(q(8,3),m.mul(P,cube))
            steps=['Select the upper semicardioid since the lower half sweeps the same volume.',
                   'Spherical volume integration leaves (2πa³/3)∫₀^π(1+cos φ)³ sin φ dφ; use u=1+cos φ.']
        else:
            value=m.mul(q(13,4),m.mul(P2,cube))
            steps=['Writing x=a(cos²φ+cos φ) gives the tangent x=−a/4 and places the entire domain on its right.',
                   'The polar area moment gives area 3πa²/2 and centroid x=5a/6. Rotate once about the tangent using the centroid distance 13a/12.']
            method='one_sided_rotation_moment'
    elif eq==['(x^2+y^2)^2=a^2*(x^2-y^2)'] and not cond and axis in ('y=0','x=0','y=x'):
        value=lemniscate_volume(P,cube,axis)
        steps=lemniscate_axis_argument(axis)+[
            'Integrate the radial moment up to a sqrt(cos 2φ). Rotation about Ox uses u=sqrt(2)cos φ and the primitive of (u²−1)^(3/2).',
            'For Oy substitute u=sqrt(2)sin φ in the cosine-weighted moment. For the diagonal, the odd part of the weight cancels on each lobe.']
    elif eq==['r=a*phi'] and axis=='polar axis' and cond==['a>0','0<=phi<=pi','half turn bounds the figure']:
        value=m.mul(q(2,3),m.mul(m.mul(P2,cube),geom_minus(P2,q(6))))
        steps=['The original half turn covers the selected upper polar sector once. Integrate the spherical radial density up to aφ.',
               'The remaining moment of φ³ sin φ on [0,π] is π³−6π by integration by parts.']
    elif eq==['phi=pi*r^3','phi=pi'] and axis=='polar axis' and not cond:
        value=m.mul(q(2,3),P)
        steps=['Use the first angular sector up to the stated ray, 0≤φ≤π, with radial ceiling (φ/π)^(1/3). This is the component starting at the origin.',
               'The spherical density integrates in radius to φ/3π. After the azimuth, ∫₀^π φ sin φ dφ=π gives the volume.']
    elif eq==['a<=r<=a*sqrt(2*sin(2*phi))'] and axis=='polar axis' and not cond:
        steps=['The annular ray interval is nonempty precisely when sin 2φ≥1/2. The two angular components have opposite axial signs.',
               'On the first component π/12≤φ≤5π/12, integrate in 3D radius between the two original bounds. The opposite component has the same volume.',
               'For the outer term substitute u=sin²φ, giving 4 u^(3/4)(1−u)^(1/4). The inner term integrates as a cosine difference.']
        value=dict(scalar_multiplier=m.mul(q(4,3),m.mul(P,cube)),beta_coefficient=4,beta_parameters=[q(7,4),q(5,4)],
                   beta_lower=m.power(('sin',m.div(P,q(12))),2),
                   beta_upper=m.power(('sin',m.mul(q(5,12),P)),2),
                   cosine_offset=geom_minus(('cos',m.mul(q(5,12),P)),('cos',m.div(P,q(12)))))
    else:raise Unsupported('No verified single-covering family for the given rotation and axes')
    checks={'method_requirement':task['method_requirement']} if 'method_requirement' in task else {}
    return geometry_proof(method,steps,dict(volume=m.simplify(value) if isinstance(value,tuple) else value,
                                            scope='positive geometric scales'),**checks)


def lemniscate_volume(P,cube,axis):
    if axis=='y=0':
        coef=geom_minus(m.div(geom_asinh(ONE),m.mul(q(2),geom_sqrt(q(2)))),q(1,6))
        return m.mul(coef,m.mul(P,cube))
    coef=m.mul(q(1,4),m.mul(m.power(P,2),cube))
    return m.div(coef,geom_sqrt(q(2))) if axis=='x=0' else coef


def geometrical_volume(task,request):
    eq,cond=graph_shape(task);a,b,c=(geom_sym(s) for s in 'abc')
    if task['requested_output']!=['volume'] or cond:raise Unsupported('The original surface-volume premises differ')
    if eq==['x^2/a^2+y^2/b^2=1','z=c*x/a','z=0']:
        each=m.mul(q(2,3),m.mul(a,m.mul(b,c)))
        value=dict(each_bounded_component=each,total=m.mul(q(2),each))
        steps=['The planes exchange order at x=0. For the footprint inside the ellipse, height is |cx/a|.',
               'At fixed x the footprint width is 2b sqrt(1−x²/a²). By reflection, evaluate one half using u=1−x²/a² and double it for the total.']
    elif eq==['x^2/a^2+y^2/b^2-z^2/c^2=1','x=-c','x=c']:
        return geometry_proof('volume_by_bounded_or_unbounded_sections',[
            'In the printed x-slab choose |x|≤min(c,a/2). The inner y-section has width 2b sqrt(1−x²/a²+z²/c²)≥2b|z|/c for every z.',
            'This positive lower comparison has infinite integral. Both outside components have unbounded y rays already on a fixed bounded rectangle of x,z.',
            'The stated surfaces therefore enclose no finite volume in their slab.'],
            dict(volume='+infinity',bounded_components=False,scope='a,b,c>0'))
    elif eq==['x^2+y^2+z^2=a^2','x^2+y^2=a*x']:
        within=m.mul(q(2,3),m.mul(m.power(a,3),geom_minus(G_PI,q(4,3))))
        value=dict(within_cylinder=within,outside_cylinder=geom_minus(m.mul(q(4,3),m.mul(G_PI,m.power(a,3))),within))
        steps=['Inside the sphere, the cylinder footprint is 0≤r≤a cos φ for |φ|≤π/2. On it the sphere has vertical thickness 2sqrt(a²−r²).',
               'Integrate r times the thickness in r. The boundary term reduces to the integral of |sin φ|³ on [−π/2,π/2], equal to 4/3.',
               'The other bounded component is the complement of this body within the sphere.']
    elif eq==['x+y+z^2=1','x=0','y=0','z=0']:
        value=dict(each_bounded_component=q(4,15),total=q(8,15))
        steps=['The bounded projection occurs at x,y≥0 and |z|≤1, with triangular area (1−z²)²/2. The z-plane splits the two equal closed lobes.',
               'Integrate the polynomial on [0,1]. For a negative x or y side, the inequalities permit an unbounded ray or strip.']
    else:raise Unsupported('No complete checked family of fibers for the original surfaces')
    return geometry_proof('volume_by_bounded_or_unbounded_sections',steps,dict(volume=value,scope='positive geometric scales'))


def geometrical_argument(task,request):
    geometry_source(task,{'statement'})
    stmt,out=task.get('statement'),task['requested_output'];P=G_PI
    if not isinstance(stmt,str):raise Unsupported('The textual geometric hypotheses are absent')
    if task.get('source',{}).get('section_convention') is None:raise Unsupported('Geometric parameter conditions are not bound')
    dim=r'([A-Za-z][A-Za-z0-9_]*)'
    roof=fr'Чердак с прямоугольным основанием {dim}×{dim}, верхнее ребро {dim}, высота {dim}(?:, ребро параллельно стороне {dim})?\.'
    if out==['volume'] and (dims:=re.fullmatch(roof,stmt)):
        A,B,C,H,parallel=dims.groups()
        if len({A,B,C,H})!=4 or parallel not in (None,A,B):
            raise Unsupported('The original lengths and ridge direction must bind to distinct geometric roles')
        a,b,c,h=map(geom_sym,(A,B,C,H))
        P=m.mul(a,b)
        base=m.mul(q(1,3),P)
        volume=lambda width:m.mul(h,m.add(base,m.mul(q(1,6),m.mul(c,width))))
        angle_name='theta'
        while angle_name in {A,B,C,H}:angle_name+='_'
        angle=geom_sym(angle_name)
        width=m.add(m.mul(a,('abs',('sin',angle))),m.mul(b,('abs',('cos',angle))))
        value=(dict(volume=volume(b if parallel==A else a),ridge_parallel_to=parallel) if parallel else
               dict(volume_as_function_of_ridge_direction=volume(width),ridge_angle_from=A,
                    parallel_to_side={A:volume(b),B:volume(a)},unique_from_given_lengths=False))
        return geometry_proof('ridge_prismatoid_sections',[
            'При прямых плоских скатах замкнутое тело — выпуклая оболочка прямоугольника и верхнего отрезка. Сечение на относительной высоте t равно сумме (1−t) прямоугольника и t отрезка.',
            'При добавлении отрезка каждая параллельная ему непустая хорда удлиняется на одну и ту же величину. Умножаем прирост на ширину проекции перпендикулярно коньку.',
            'Ширина исходного прямоугольника в этом направлении равна a|sin θ|+b|cos θ|. Получаем площадь ab(1−t)²+c·width·t(1−t).',
            'Моменты на [0,1] равны 1/3 и 1/6. Положение проекции конька меняет перенос сечений. При незаданном направлении остаётся семейство объёмов.'],
            value,model='convex hull of the given horizontal rectangle and top segment at height h',
            section_polynomial=dict(base_area=P,transverse_width=width if parallel is None else b if parallel==A else a))
    if out==['area_ratio'] and (dims:=re.fullmatch(r'В каком отношении парабола y²=([1-9]\d*)x делит площадь круга x²\+y²=([1-9]\d*)\?',stmt)):
        k,R2=map(int,dims.groups());R=geom_sqrt(q(R2))
        x=m.div(geom_minus(geom_sqrt(q(k*k+4*R2)),q(k)),q(2));y=geom_sqrt(m.mul(q(k),x))
        small=geom_minus(m.add(m.mul(x,y),m.mul(q(R2),('asin',m.div(y,R)))),m.div(m.mul(q(2),m.power(y,3)),q(3*k)))
        large=geom_minus(m.mul(q(R2),P),small)
        return geometry_proof('graph_area_with_ends',[
            'For y²=kx in the circle x²+y²=R², take the positive root X of X²+kX=R² and Y=sqrt(kX). The other root is left of the y-axis and is outside the original parabola.',
            'The right-hand part has width sqrt(R²−y²)−y²/k for −Y≤y≤Y. Its integral is X Y+R² arcsin(Y/R)−2Y³/(3k).',
            'This part is contained in the right half disk, and the other part is its complement.'],
            dict(area_ratio=m.div(small,large),smaller_area=small,larger_area=large))
    if stmt=='Выразить координаты M(x,y) на x²−y²=1 как функции площади S сектора OM′M, ограниченного дугой гиперболы M′M и лучами OM, OM′, где M′=(x,−y).' and out==['coordinates_from_area']:
        return geometry_proof('closed_parametric_measure',[
            'Use (cosh u,sinh u) on the right branch and reflection on the left branch. On the right the oriented determinant X Y′−Y X′ equals 1.',
            'The two endpoints of the sector have parameters u and −u, and radial segments contribute zero to the determinant area form. Thus S=|u|.',
            'Reflections give independent signs of the two coordinates, with coincident endpoints when S=0.'],
            dict(coordinates_from_area=['±cosh(S)','±sinh(S)'],scope='S>=0; signs specify the original branch and endpoint'))
    if stmt=='Доказать, что длина дуги эллипса x=a cos t, y=b sin t равна длине одной волны синусоиды y=c sin(x/b), где c=√(a²−b²).' and out==['proof']:
        return geometry_proof('positive_radical_curve_metric',[
            'With positive semiaxes and real c, the entire ellipse has squared speed a² sin²t+b² cos²t over any full turn.',
            'Set x=bs for one full wave of y=c sin(x/b). Its squared speed is b²+c² cos²s, equal to b² sin²s+a² cos²s.',
            'The shift by π/2 matches the two nonnegative speeds. The full-period integrals are equal.'],dict(proved=True))
    if stmt=='Парабола 4ay=x² катится по прямой Ox. Доказать, что фокус параболы описывает цепную линию.' and out==['proof']:
        return geometry_proof('moving_tangent_and_normal',[
            'Use a>0, contact P=(2au,au²) and the parabola focus (0,a). Arc length from the vertex is a[u sqrt(1+u²)+asinh u] with its sign.',
            'No slipping identifies that arc length with the contact coordinate on Ox.',
            'The focus offset in the unit tangent-normal frame is (−au sqrt(1+u²),a sqrt(1+u²)). Add the contact coordinate to the tangential component.',
            'Then X=a asinh u takes all real values and Y=a sqrt(1+u²)=a cosh(X/a).'],dict(proved=True,locus='Y=a*cosh(X/a)'))
    if out==['area_ratio'] and stmt in (
            'Найти отношение площади петли y=±(1/3−x)√x к площади круга, длина окружности которого равна длине контура петли.',
            'Найти отношение площади, ограниченной петлей кривой y=±(1/3−x)√x, к площади круга, длина окружности которого равна длине контура этой кривой.'):
        return geometry_proof('positive_radical_curve_metric',[
            'The two branches join only at x=0 and x=1/3, with ordered height 2(1/3−x)sqrt x between them.',
            'Integrating the height gives 8/(135 sqrt 3). The positive branch contour speed is (1/3+3x)/(2 sqrt x), and the two arcs have length 4/(3 sqrt 3).',
            'The equal-length circle area is length²/(4π). Take the ratio.'],dict(area_ratio=m.div(m.mul(q(2),P),m.mul(q(5),geom_sqrt(q(3))))))
    if stmt=='Доказать, что при вращении a≤x≤b, 0≤y≤y(x) вокруг Oy объём равен 2π∫ₐᵇx y(x)dx; y(x) однозначна и непрерывна.' and out==['proof']:
        return geometry_proof('one_sided_rotation_moment',[
            'The original radii satisfy 0<a≤x≤b and the continuous height is nonnegative. Each radius labels one cylindrical section.',
            'Cylindrical coordinates have volume element x dy dx dθ. Integrating y and θ gives the stated integral.'],dict(proved=True))
    if stmt=='Доказать, что при вращении вокруг полярной оси фигуры 0≤α≤φ≤β≤π, 0≤r≤r(φ), объём равен (2π/3)∫ᵅᵝ r³(φ) sin(φ) dφ.' and out==['proof']:
        return geometry_proof('rotated_radial_sections',[
            'For 0≤α≤φ≤β≤π the nonnegative rays produce the original solid exactly once except coordinate seams and the axis.',
            'Integrate the spherical volume element r² sinφ dr dφ dθ between r=0 and the original nonnegative radius, and then over the full azimuth.'],dict(proved=True))
    if stmt=='Вокруг Ox вращается фигура между ay=a²−x² и Ox. Найти отношение площади поверхности тела к площади поверхности равновеликого шара.' and out==['surface_area_ratio']:
        scale=('exp',m.mul(q(2,3),('ln',q(5,4))))
        value=m.mul(scale,m.div(m.add(m.mul(q(14),geom_sqrt(q(5))),m.mul(q(17),geom_asinh(q(2)))),q(64)))
        return geometry_proof('distance_weighted_surface',[
            'The cap y=a−x²/a ends where y=0 at ±a. The disc moments give volume 16πa³/15 and equal-volume sphere radius a(4/5)^(1/3).',
            'For the surface use radius y and speed sqrt(1+4x²/a²). The substitution u=2x/a reduces the integral to J₀−J₂/4 on [0,2].',
            'Evaluate the even radical primitives and divide by the equal-volume sphere area.'],dict(surface_area_ratio=value))
    if task['kind']=='geometric_moments' and out==['proof']:
        moment={
            'Доказать первую теорему Гульдена для вращения плоской дуги C вокруг непересекающей её оси в её плоскости: поверхность равна длине дуги, умноженной на длину окружности, описанной центром масс дуги.':'curve',
            'Доказать вторую теорему Гульдена для вращения плоской области S вокруг непересекающей её оси в её плоскости: объём равен площади, умноженной на длину окружности, описанной центром масс области.':'region',
        }.get(stmt)
        if moment:
            mass='length' if moment=='curve' else 'area'
            return geometry_proof('one_sided_rotation_moment',[
                'A connected simple plane '+moment+' disjoint from the rotation axis lies on one side of that axis.',
                'The rotation map has Jacobian factor r for distance r to the axis. Outside the angular seam the preimages are unique on that side.',
                'Integrate over the full azimuth and use the definition of the centroid coordinate as the first moment divided by the '+mass+'.'],
                dict(proved=True,source_measure=mass,formula='2*pi*centroid_distance*'+mass))
    if stmt=='Дуга OP логарифмической спирали r=a exp(mφ), m>0, от O(−∞,0) до P(φ,r). Найти C(φ₀,r₀) и кривую, описанную C при движении P.' and out==['centroid_coordinates','centroid_locus']:
        return geometry_proof('one_sided_rotation_moment',[
            'Use ds=sqrt(1+m²) r dφ. Since m>0 the full spiral segment has finite length and finite first moments at −∞.',
            'Combine the two Cartesian moment integrals in complex form. Integrating exp((2m+i)φ) and dividing by arc length gives m r exp(iφ)/(2m+i).',
            'Polar coordinates give the stated centroid, and replacing φ by φ₀+arctan(1/(2m)) gives its locus.'],
            dict(centroid_coordinates=['phi-atan(1/(2*m))','m*r/sqrt(4*m^2+1)'],
                 centroid_locus='r0=a*m*exp(m*atan(1/(2*m)))*exp(m*phi0)/sqrt(4*m^2+1)'))
    raise Unsupported('The source geometric argument, its object, or a unique geometry remains unbound')


G_NUMBER=r'([0-9]+(?:[,.][0-9]+)?)'


def isothermal_cylinder_work(text):
    measure=r'([0-9]+(?:[,.][0-9]+)?) (см|м)'
    cylinder=fr'Цилиндр диаметром {measure} и длиной {measure} заполнен паром под давлением {G_NUMBER} Па\. '
    question=fr'Какова работа пара при уменьшении объёма (вдвое|в {G_NUMBER} раза) при постоянной температуре\?'
    found=re.fullmatch(cylinder+question,text)
    if not found:
        raise Unsupported('The initial cylindrical volume, pressure and final volume fraction must be specified')
    d,dm,L,Lm,p,_,factor=found.groups()
    number=lambda text:Fraction(text.replace(',','.'))
    metres=lambda n,u:number(n)/(100 if u=='см' else 1)
    diameter,length,pressure=metres(d,dm),metres(L,Lm),number(p)
    ratio=1/(number(factor) if factor else Fraction(2))
    if min(diameter,length,pressure,ratio)<=0 or ratio>=1:
        raise Unsupported('The positive initial state and a strict compression are needed')
    V0=m.mul(q(diameter**2*length/4),G_PI)
    pV=m.mul(q(pressure),V0)
    ideal=m.mul(pV,('ln',q(ratio)))
    alternative=m.mul(pV,q(1-1/ratio))
    return geometry_proof('isothermal_constitutive_work',[
        'Работа, совершённая паром при квазистатическом движении поршня, есть предел сумм p(Vᵢ)ΔVᵢ с ориентированными приращениями объёма.',
        'Переводим размеры в метры, получаем V₀=πd²l/4 и пределы V₀ и rV₀ с 0<r<1. Интегрирование идёт в сторону уменьшения объёма.',
        'Для изотермической модели идеального газа pV=p₀V₀. Интегрирование 1/V даёт p₀V₀ ln r.',
        'Постоянная температура и начальное давление сами по себе не задают функцию p(V). Другая положительная изотерма p=p₀(V₀/V)² даёт p₀V₀(1−1/r). Значения различны, поскольку 1−1/r<ln r при 0<r<1.'],
        dict(work_by_vapour_for_ideal_gas=ideal,work_by_vapour_for_alternative_isotherm=alternative,
             unique_from_given_state=False,unit='J'),initial_volume=V0,final_volume=m.mul(q(ratio),V0),
        assumptions='quasistatic piston work; ideal gas law only in the ideal-gas branch')


def physical_measure(task,request):
    geometry_source(task,{'statement','method_requirement'})
    text,out=task.get('statement'),task['requested_output']
    method=task.get('method_requirement')
    if not isinstance(text,str):raise Unsupported('The measured object or physical model is absent')
    symbols={s:geom_sym(s) for s in ('a','m','g','R','h','b','T','v0','rho','G','mu0','delta0','w','H','E','t','Q0')}
    a,b,R,g,rho,T,v0,H=(symbols[s] for s in ('a','b','R','g','rho','T','v0','H'))
    P=G_PI;rho_g=m.mul(rho,g)
    def match(pattern):
        found=re.fullmatch(pattern,text)
        return [Fraction(v.replace(',','.')) for v in found.groups()] if found else None
    if method=='form_integral_sums_and_take_their_limits':
        tag='physical_density_integral'
        if out==['work_by_vapour']:
            return isothermal_cylinder_work(text)
        if out==['mass'] and (args:=match(fr'Стержень длиной {G_NUMBER} м, линейная плотность δ={G_NUMBER}\+{G_NUMBER}x кг/м на расстоянии x от конца\.')):
            length,start,slope=args
            if length<=0:raise Unsupported('A positive original rod length is required')
            value=dict(mass=q(length*(start+slope*length/2)),unit='kg')
            steps=['On each subinterval the approximate mass is the density at a sample point times its length in metres.',
                   'The continuous affine density gives the Riemann integral. Evaluate its linear and quadratic moments over the original length.']
        elif out==['work_to_height','work_to_infinity'] and text=='Тело массы m поднять с поверхности Земли радиуса R на высоту h. Какова работа при этом и при удалении в бесконечность?':
            mgR=m.mul(m.mul(symbols['m'],g),R);h=symbols['h']
            value=dict(work_to_height=m.div(m.mul(mgR,h),m.add(R,h)),work_to_infinity=mgR)
            steps=['In the spherical Newtonian Earth model the opposing radial force is mgR²/r² for r≥R>0.',
                   'The work sums use each force times its radial increment and converge to the integral of mgR²/r².',
                   'Evaluate first at R+h and then take its finite improper limit as the upper radius tends to infinity.']
        elif out==['work'] and (args:=match(fr'Пружина удлиняется на {G_NUMBER} см под действием {G_NUMBER} Н\. Работа при растяжении на {G_NUMBER} см\.(?: Указание: закон Гука\.)?')):
            rest,force,target=args
            if min(rest,force,target)<=0:raise Unsupported('Positive spring measurements are required')
            value=dict(work=q(force*(target/100)**2/(2*(rest/100))),unit='J')
            steps=['Convert both lengths from centimetres to metres and find k from the reference force divided by its elongation.',
                   'In the linear elastic spring model, the work sums converge to the integral of kx over the target elongation.']
        elif out==['hydrostatic_force'] and text=='Сила давления воды на вертикальную полукруглую стенку радиуса a, диаметр на поверхности.':
            value=dict(hydrostatic_force=m.mul(q(2,3),m.mul(rho_g,m.power(a,3))))
            steps=['At depth z, the strip width is 2sqrt(a²−z²) and pressure is ρgz. Sum pressure times strip area on 0≤z≤a.',
                   'The Riemann integral of the continuous density reduces by u=a²−z² to a positive power moment.']
        elif out==['hydrostatic_force'] and (args:=match(fr'Вертикальная трапеция, нижнее основание a={G_NUMBER} м на глубине c={G_NUMBER} м, верхнее b={G_NUMBER} м, высота h={G_NUMBER} м\. Сила давления воды\.')):
            bottom,depth,upper,height=args
            if min(bottom,upper,height)<=0 or depth<height:raise Unsupported('The original positive trapezoid must be immersed to its upper side')
            v=height*((depth-height)*(upper+bottom)/2+height*(upper+2*bottom)/6)
            value=dict(hydrostatic_force=m.mul(q(v),rho_g),depth_width_moment=q(v),unit='N in SI')
            steps=['Depth z runs from c−h to c. The width interpolates linearly from b to a.',
                   'Sum ρg times depth times strip area and pass to the continuous integral. Its depth-weighted width is an exact quadratic moment.']
        else:raise Unsupported('No fully stated constitutive law and Riemann density for this physical request')
    elif method=='form_and_solve_differential_equations':
        tag='physical_accumulation_equation'
        if out==['distance_travelled'] and text=='Скорость точки v=v₀+at. Какой путь пройден за [0,T]?':
            value=dict(distance_travelled=m.add(m.mul(v0,T),m.mul(q(1,2),m.mul(a,m.power(T,2)))))
            steps=['The original positive scales and times imply v₀+at>0 on the interval, so the distance satisfies s′=v₀+at.',
                   'Integrate the differential equation with s(0)=0 and evaluate at T.']
        elif out==['kinetic_energy'] and text=='Однородный шар радиуса R и плотности δ вращается вокруг диаметра с угловой скоростью ω. Найти кинетическую энергию.':
            value=dict(kinetic_energy=m.mul(q(4,15),m.mul(P,m.mul(geom_sym('delta'),m.mul(m.power(symbols['w'],2),m.power(R,5))))))
            steps=['The polar mass moment of a thin disc at height z is πδ(R²−z²)²/2 per unit height.',
                   'The accumulated axial moment satisfies I′(z)=πδ(R²−z²)²/2 and I(−R)=0. Integrate the polynomial on [−R,R].',
                   'Multiply the resulting moment by ω²/2.']
        elif out==['attraction_force'] and text=='Бесконечная прямая линейной плотности μ₀ притягивает точку массы m, расположенную на расстоянии a от прямой. Определить силу.':
            gm=m.mul(symbols['G'],symbols['m']);value=dict(attraction_force=m.div(m.mul(q(2),m.mul(gm,symbols['mu0'])),a),direction='toward line')
            steps=['Use opposite segments of the line to cancel tangential forces in the Newtonian model.',
                   'The cumulative normal force solves F′(L)=2Gmμ₀a/(a²+L²)^(3/2) with F(0)=0. Integrate using L/sqrt(a²+L²).',
                   'For positive distance a, the original infinite line is obtained by the convergent limit L→∞.']
        elif out==['attraction_force'] and text=='Круглая пластинка радиуса a с поверхностной плотностью δ₀. Точка массы m находится на нормали через центр на расстоянии b от него. Найти силу притяжения.':
            k=m.mul(q(2),m.mul(P,m.mul(symbols['G'],m.mul(symbols['m'],symbols['delta0']))))
            value=dict(attraction_force=m.mul(k,geom_minus(ONE,m.div(b,geom_sqrt(m.add(m.power(a,2),m.power(b,2)))))),direction='toward disk')
            steps=['Each Newtonian ring cancels its tangential force. For b>0 its axial contribution is smooth at radius zero.',
                   'Solve F′(r)=2πGmδ₀ b r/(b²+r²)^(3/2) with F(0)=0. Evaluate the inverse-square-root primitive at the original outer radius a.']
        elif out==['draining_time'] and (args:=match(fr'Закон Торричелли v=c√\(2gh\), c={G_NUMBER}\. Время опорожнения полной вертикальной цилиндрической бочки D={G_NUMBER} м, H={G_NUMBER} м, круглое отверстие в дне d={G_NUMBER} см\.')):
            c,D,height,diam=args
            if min(args)<=0 or diam/100>=D:raise Unsupported('Positive model scales and a strictly smaller outlet are required')
            ratio=(100*D/diam)**2
            value=dict(draining_time=m.mul(q(ratio/c),geom_sqrt(m.div(q(2*height),g))),unit='s in SI')
            steps=['The water balance is A h′=−A₀ c sqrt(2gh) with initial height H; the area ratio is (D/d)² in common units.',
                   'Separate on h>0 and integrate h^(−1/2) between 0 and H. Its finite limit determines the first emptying time.']
        elif out==['vessel_profile'] and text=='Какую форму должен иметь сосуд — тело вращения, чтобы уровень при истечении жидкости понижался равномерно?':
            value=dict(vessel_profile='R(h)=C*h^(1/4)',conditions='C>0; h>=0; ideal Torricelli model')
            steps=['For the Torricelli model write conservation as A(h)h′=−A₀ c sqrt(2gh) on h>0.',
                   'Constant positive descent speed k gives A(h)=A₀ c sqrt(2gh)/k. Use A(h)=πR(h)², then extend the profile to h=0 by continuity.']
        elif out==['decay_law'] and (args:=match(fr'Скорость распада радия пропорциональна количеству, Q\(0\)=Q₀, за T={G_NUMBER} лет количество уменьшается вдвое\. Найти закон распада\.')):
            half=args[0]
            if half<=0:raise Unsupported('A positive observed half-life is required')
            rate=m.div(('ln',q(2)),q(half))
            value=dict(decay_law=m.mul(symbols['Q0'],('exp',m.neg(m.mul(rate,symbols['t'])))),unit='time in years')
            steps=['Proportional decay gives Q′=−λQ. The positive initial quantity Q₀ yields Q(t)=Q₀ exp(−λt).',
                   'At the original measured half-life the factor is 1/2. Determine λ uniquely and substitute it in the solution.']
        elif out==['percentage'] and (args:=match(fr'Скорость превращения A в B пропорциональна произведению их концентраций\. При t=0 доля B равна {G_NUMBER}%, через {G_NUMBER} минут {G_NUMBER}%\. Сколько процентов B через {G_NUMBER} час\?')):
            y0,elapsed,y1,hours=args;y0/=100;y1/=100
            ratio=60*hours/elapsed if elapsed>0 else 0
            if not 0<y0<y1<1 or not isinstance(ratio,Fraction) or not 0<ratio==int(ratio)<=50:
                raise Unsupported('Interior calibration and an exact positive observation-time multiple are required')
            odds=lambda y:y/(1-y)
            w=odds(y0)*(odds(y1)/odds(y0))**int(ratio)
            value=dict(percentage=q(100*w/(1+w)),fraction=q(w/(1+w)))
            steps=['Conservation of total concentration gives z′=kz(1−z) for the fraction of B in (0,1).',
                   'The odds z/(1−z) solve W′=kW. The measured odds determine the exponential factor over the calibration interval.',
                   'Apply that factor over the exact number of elapsed calibration intervals, then convert the resulting odds to the requested percentage.']
        elif out==['elongation'] and text=='Закон Гука ε=σ/E. Тяжёлый конический стержень закреплён основанием и обращён вершиной вниз. Найти удлинение при радиусе основания R, высоте H и плотности ρ.':
            value=dict(elongation=m.div(m.mul(rho_g,m.power(H,2)),m.mul(q(6),symbols['E'])))
            steps=['At distance z>0 from the tip the area is π(Rz/H)² and the load below is ρgA(z)z/3.',
                   'The axial stress is ρgz/3, continuously tending to zero at the vertex. The stated Hooke law gives ℓ′=ρgz/(3E).',
                   'Solve with ℓ(0)=0 up to z=H.']
        else:raise Unsupported('No verified physical differential equation with all original data')
    else:raise Unsupported('The needed physical derivation depends on the exact requested method')
    if (task.get('source',{}).get('section_convention') is None
            and any(not m.constant_defined(t,m.context({})) for t in value.values() if isinstance(t,tuple))):
        raise Unsupported('Positive physical parameters must be established from the source')
    return geometry_proof(tag,steps,value,method_requirement=method)


def certified_ellipse_perimeter(task):
    from quadrature import enclose
    geometry_source(task,{'semiaxes'},('printed_instruction',))
    a,b=task['semiaxes']
    if task['requested_output']!=['approximate_perimeter'] or not all(isinstance(n,int) and not isinstance(n,bool) and n>0 for n in (a,b)):
        raise Unsupported('Certified approximation requires two positive integer semiaxes')
    instruction=task.get('source',{}).get('printed_instruction')
    if instruction not in (None,f'Приближенно найти длину эллипса, полуоси которого a={a} и b={b}.'):
        raise Unsupported('The printed approximation request differs from these semiaxes')
    a,b=max(a,b),min(a,b)
    ratio=1-Fraction(b*b,a*a)
    lower_pi,upper_pi=enclose(G_PI,None)
    summand=ratio/4;total=Fraction(0);count=0;error=Fraction(1,50000)
    while count<128:
        count+=1;total+=summand
        summand*=ratio*Fraction((2*count-1)*(2*count+1),4*(count+1)**2)
        lower=2*a*lower_pi*(1-total-summand/(1-ratio))
        upper=2*a*upper_pi*(1-total)
        if lower>0 and upper-lower<error:break
    else:raise Unsupported('The certified eccentricity expansion needs more terms')
    rounded=Fraction(round((lower+upper)*500),1000)
    bound=max(abs(upper-rounded),abs(lower-rounded))
    return geometry_proof('certified_ellipse_arc_quadrature',[
        'Take four quadrant arcs of the parametric ellipse and factor out the larger semiaxis.',
        'Expand the positive radical by its binomial series on the full interval, where the eccentricity squared is strictly below one.',
        'Integrate each sine-power term. The magnitude of every later coefficient ratio is at most the eccentricity squared, so a geometric tail bounds the omitted terms.',
        'Enclose π independently and account for rounding to three decimals.'],
        dict(approximate_perimeter=q(rounded),absolute_error_bound=q(bound)),
        summands=count,certified_interval=[q(lower),q(upper)])


class GeometricChildRequired(Exception):
    pass


def recognize_geometric_child(role,goal):
    raise GeometricChildRequired


def geometric_application_goal(task):
    if task.get('kind') not in {'area_bounded_by_curves','curve_arc_length','solid_of_revolution',
            'volume_bounded_by_surfaces','bounded_solid_volume','geometric_moments','geometric_proof_or_calculation',
            'physical_model_from_statement','ellipse_perimeter_approximation'}:
        return False
    try:
        compose_geometry(task,None,recognize_geometric_child)
    except GeometricChildRequired:
        return True
    except (Unsupported,KeyError,TypeError,AttributeError,IndexError):
        return False
    return True


def source_geometric_application(task,library,request):
    if not library.data.get('source_geometric_applications'):
        raise Unsupported('The geometric and physical measure transitions are unavailable')
    return compose_geometry(task,library,request)
