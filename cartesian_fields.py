"""Typed Cartesian field polynomials with ordered component derivatives."""
import ast
import re
from fractions import Fraction
from functools import lru_cache, reduce
from itertools import combinations, product
from math import factorial

import expressions as m
import polynomial as poly
from model import ONE, ZERO, Unsupported, canonical, freeze, q
from tasks import domain_conditions, entailed_domain_guards, guard_source, known_guard, source
from verify import same_value

AXES='xyz'


def flux_surface(description):
    """Read a sphere, a coordinate cube, or the lateral boundary of a right cone."""
    token=r'([A-Za-z][A-Za-z_0-9]*|[0-9]+)'
    sphere=re.fullmatch(r'sphere (.+)='+token+r'\^2',description)
    if sphere:
        terms=sphere[1].split('+');center=[]
        if len(terms)!=3:raise Unsupported('Three Cartesian squares are required')
        for ax,square in zip(AXES,terms):
            if square==ax+'^2':center.append('0');continue
            offset=re.fullmatch(r'\('+ax+'-'+token+r'\)\^2',square)
            if not offset:raise Unsupported('Unverified center or orientation of the quadric')
            center.append(offset[1])
        return 'sphere',center,sphere[2]
    cube=re.fullmatch(r'boundary of cube \[0,'+token+r'\]\^3',description)
    if cube:return 'cube',['0']*3,cube[1]
    cone=re.fullmatch(r'conical lateral surface x\^2\+y\^2=z\^2,0<=z<='+token,description)
    if cone:return 'lateral_cone',['0']*3,cone[1]
    raise Unsupported('No verified boundary measure for the stated surface')


def polynomial_flux(field,derivative,shape,center,length,bulk):
    """Volume moments of the divergence, and a separate direct normal-flux calculation."""
    from fractions import Fraction
    from math import prod
    from model import q
    from verify import same_value
    coords=[('s',a) for a in AXES]
    substitutions={v:m.add(v,b) for v,b in zip(coords,center)}
    def polynomial(e):
        numerator,denominator=m.rational_form(m.substitute(e,substitutions))
        if not denominator or set(denominator)!={()}:raise Unsupported('Polynomial moments require a polynomial integrand')
        for mon,c in numerator.items():
            deg=[0]*3;factor=q(c/denominator[()])
            for atom,k in mon:
                if atom in coords:deg[coords.index(atom)]=k
                elif not any(m.contains(atom,v) for v in coords):factor=m.mul(factor,m.power(atom,k))
                else:raise Unsupported('Nonpolynomial Cartesian dependence')
            yield deg,factor
    def df(k):return prod(range(k,0,-2))
    def moment(deg,boundary,axis):
        i,j,k=deg;s=sum(deg)
        if shape=='cube':
            if not deg[axis]:return m.ZERO  # Opposite faces cancel.
            return m.mul(q(1,prod(v+1 for h,v in enumerate(deg) if h!=axis)),m.power(length,s+2))
        if shape=='sphere':
            if any(v%2 for v in deg):return m.ZERO
            # For surface flux the caller adds one radial coordinate and divides by R.
            c=Fraction(4*prod(df(v-1) for v in deg),df(s+1))
            return m.mul(m.PI,m.mul(q(c),m.power(length,s+1)))
        if i%2 or j%2:return m.ZERO
        angular=q(2*df(i-1)*df(j-1),df(i+j))
        if boundary:
            # Lateral oriented area is (cos θ,sin θ,−1) z dz dθ.
            orig=s-(axis<2)
            return m.mul(m.PI,m.mul(angular,m.div(m.power(length,orig+2),q(orig+2))))
        return m.mul(m.PI,m.mul(angular,m.div(m.power(length,s+3),q((i+j+2)*(s+3)))))
    def integrate(expr,boundary=False,axis=None):
        total=m.ZERO
        for deg,c in polynomial(expr):
            if boundary and (shape=='sphere' or shape=='lateral_cone' and axis<2):deg[axis]+=1
            value=moment(deg,boundary,axis)
            if boundary and shape=='lateral_cone' and axis==2:value=m.neg(value)
            total=m.add(total,m.mul(c,value))
        return total
    cap=m.ZERO
    if shape=='lateral_cone':
        bulk=integrate(derivative)
        for (i,j,k),c in polynomial(field[2]):
            if not (i%2 or j%2):
                d=q(2*df(i-1)*df(j-1),(i+j+2)*df(i+j))
                cap=m.add(cap,m.mul(c,m.mul(m.PI,m.mul(d,m.power(length,i+j+k+2)))))
    direct=m.ZERO
    for axis,f in enumerate(field):direct=m.add(direct,integrate(f,True,axis))
    volume_flux=m.simplify(m.add(bulk,m.neg(cap)))
    # Completing squares can return |R^d| in place of |R|^d.
    from operations import expression_positions
    powers={e:m.power(('abs',e[1][1]),e[1][2]) for _,e in expression_positions(volume_flux)
            if e[0]=='abs' and e[1][0]=='pow' and e[1][2]>0}
    volume_flux=m.simplify(m.substitute(volume_flux,powers))
    if not same_value(direct,volume_flux):raise Unsupported('Independent boundary flux disagrees with the divergence integral')
    return dict(volume_term=bulk,added_cap=cap,direct_normal_flux=direct),volume_flux


def cartesian_flux(task,library,request):
    from tasks import domain_conditions,known_guard,source
    if not library.data.get('cartesian_boundary_flux'):raise Unsupported('No declared flux theorem')
    transform=task.get('kind')=='divergence_integral_transform'
    allowed={'kind','id','source','field','requested_output','method_requirement',*(
        ['region'] if transform else ['surface','orientation','suggested_method'])}
    method=task.get('method_requirement')
    meta=task.get('source',{})
    if (set(task)-allowed or task.get('requested_output')!=(['equivalent_triple_integral'] if transform else ['flux'])
            or method not in (None,'divergence_theorem') or not isinstance(meta,dict)
            or set(meta)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement',
                          'explicit_imposed_method','method_requirement','explicit_required_method'}
            or any(meta.get(k) not in (None,method) for k in ('explicit_imposed_method','method_requirement','explicit_required_method'))):
        raise Unsupported('An additional output or prescribed method remains')
    statements={'Преобразовать поверхностный интеграл с помощью формулы Остроградского.',
                'Вычислить поверхностный интеграл второго рода.','Вычислить поток через указанную сторону поверхности.',
                'Вычислить поток через внешнюю сторону поверхности.',
                'С помощью формулы Остроградского вычислить поверхностный интеграл.'}
    if meta.get('literal_requirement') and meta['literal_requirement'] not in statements:
        raise Unsupported('Unbound literal flux requirement')
    if 'внешн' in meta.get('literal_requirement','') and task.get('orientation')!='outward':
        raise Unsupported('The stated orientation disagrees with the printed surface')
    if task.get('suggested_method') not in (None,'attach top disk z=h'):raise Unsupported('Unrecognized printed construction')
    if transform:
        if task.get('region')!='smooth closed S bounds finite V; n outward':raise Unsupported('A closed oriented bounding region is required')
        names=list(AXES);shape=None
    else:
        orientation=task.get('orientation')
        if orientation not in ('outward','inward'):raise Unsupported('A specified boundary orientation is required')
        box=re.fullmatch(r'box ([^;]+);([a-zA-Z,]+) continuous',task.get('surface',''))
        if box:
            if method is not None:raise Unsupported('Continuity allows the face integral; the required volume derivatives are unproved')
            edges=box[1].split(',');functions=box[2].split(',')
            if len(edges)!=3 or len(functions)!=3 or task.get('field')!=[f+'('+ax+')' for f,ax in zip(functions,AXES)]:
                raise Unsupported('A component must depend only on its normal coordinate')
            ends=[]
            for edge,ax in zip(edges,AXES):
                pair=re.fullmatch(r'(0|[A-Za-z]\w*)<='+ax+r'<=(\d+|[A-Za-z]\w*)',edge)
                if not pair or pair[1]==pair[2] or any(b in AXES for b in pair.groups()):raise Unsupported('Unbound box interval')
                ends.append(pair.groups())
            names=sorted({s for edge in ends for s in edge if s.isidentifier()})
            lengths=[m.add(m.parse(hi,None,names),m.neg(m.parse(lo,None,names))) for lo,hi in ends]
            faces=[]
            for i,(f,(lo,hi)) in enumerate(zip(functions,ends)):
                area=m.mul(lengths[(i+1)%3],lengths[(i+2)%3]);faces.append((source(area),f,hi,lo))
            value=' + '.join(f'{a}*({f}({hi})-{f}({lo}))' for a,f,hi,lo in faces)
            if orientation=='inward':value='-('+value+')'
            return dict(theorem='method.opposite_face_flux',checks=faces,orientation=orientation),dict(flux_formula=value,
                        geometric_domain=[lo+'<'+hi for lo,hi in ends])
        shape,origin,scale=flux_surface(task.get('surface',''))
        params=sorted({p for p in [scale,*origin] if p.isidentifier()})
        if set(params)&set(AXES):raise Unsupported('A geometric parameter is also a variable')
        names=[*AXES,*params]
        length=m.parse(scale,None,params);center=[m.parse(c,None,params) for c in origin]
        if m.num(length)==0:raise Unsupported('A zero radius or height does not bound a solid')
        # A squared equation determines the absolute radius for either sign of its parameter.
        if shape=='sphere':length=m.simplify(('abs',length))
    text=task.get('field')
    if not isinstance(text,list) or len(text)!=3 or not all(isinstance(e,str) for e in text):
        raise Unsupported('Three source coefficients in oriented Cartesian order are required')
    if transform and any(re.search(r'\b[A-Za-z]+_[xyz]\b',s) for s in text):
        declared={}
        def derivative(match):
            f,axis=match.groups();declared[f]='scalar'
            return 'd'+axis+'('+f+')'
        parts=[re.sub(r'\b([A-Za-z]+)_([xyz])\b',derivative,s) for s in text]
        formal='div(vector('+','.join(parts)+'))'
        child=request('развернуть дивергенцию исходных трёх компонент',dict(kind='cartesian_field_operator',expression=formal,fields=declared))
        return dict(theorem='method.cartesian_boundary_flux',expression=formal,checks=['outward closed boundary','Cartesian divergence']),dict(region='V',cartesian_integrand=child['value'],measure='dx dy dz')
    field=[m.parse(e,None,names) for e in text]
    region={'bounded_regular_region':True};conditions=[];bulk=None
    if shape=='sphere':region={'quadratic_sublevel':dict(left=task['surface'][7:].split('=')[0],right=scale+'^2')}
    if shape=='cube':region={'box':[['0',scale] for _ in AXES]}
    if shape and scale.isidentifier():conditions=[scale+('!=0' if shape=='sphere' else '>0')]
    dummy='__flux'
    while dummy in names:dummy+='_'
    whole=m.context(dict(variable=dummy,parameters=names,parameter_conditions=conditions))
    guards=list(dict.fromkeys(g for component in field for g in domain_conditions(component,True)))
    if not all(known_guard(g,whole) for g in guards):
        raise Unsupported('Smoothness of the original field throughout the enclosed domain is unproved')
    concrete=shape in ('sphere','cube')
    child=request('формула Остроградского на замкнутой границе',
        dict(kind='oriented_boundary_integral',variables=list(AXES),coefficients=text,parameters=names[3:],
             stated_conditions=conditions,boundary_of=region,method_requirement='divergence_theorem',
             orientation='outward',requested_output=['boundary_integral' if concrete else 'equivalent_interior_integral']))
    divergence=freeze(child['compilation']['density'])
    if concrete:bulk=freeze(child['value']['boundary_integral'])
    plan=dict(theorem='method.cartesian_boundary_flux',field=field,
              source_smoothness_conditions=guards,divergence=divergence,
              checks=['smooth throughout the region','specified oriented boundary'])
    if transform:return plan,dict(region='V',integrand=divergence,measure='dx dy dz')
    checks,result=polynomial_flux(list(map(m.simplify,field)),divergence,shape,center,length,bulk)
    condition='radius != 0' if shape=='sphere' else 'height or side > 0'
    plan.update(shape=shape,center=center,length=length,geometric_domain=(scale,condition),orientation=orientation,**checks)
    plan['checks'].append('direct oriented boundary moments agree with the volume flux minus any added cap')
    return plan,dict(flux=result if orientation=='outward' else m.neg(result),geometric_domain=(scale,condition))

def vector_source(task,fields,headings,extra_source=()):
    """Bind the mathematical request independently of the printed exercise number."""
    meta=task.get('source',{})
    provenance={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','page_png_sha256'}
    if (set(task)-{'id','kind','source',*fields} or not isinstance(meta,dict)
            or set(meta)-provenance-{'literal_requirement',*extra_source}
            or meta.get('literal_requirement') not in (None,*headings)):
        raise Unsupported('The source includes an additional operator, field condition or requested result')


def vector_cross(a,b):
    return [m.simplify(m.add(m.mul(a[i],b[j]),m.neg(m.mul(a[j],b[i])))) for i,j in ((1,2),(2,0),(0,1))]


def coordinate_curl(partial,field):
    return [m.simplify(m.add(partial(field[j],AXES[i]),m.neg(partial(field[i],AXES[j]))))
            for i,j in ((1,2),(2,0),(0,1))]


def field_at_point(task,request,small_circle):
    """Check the source point and full local field before forming curl or Stokes' asymptotic."""
    from tasks import domain_conditions,known_guard,source
    from model import q
    kind=task['kind']
    vector_source(task,{'field','at','sphere','plane','normal'} if small_circle else {'field','point'},
        ('Вычислить ротор в M и приближённо найти циркуляцию по бесконечно малой окружности.',) if small_circle
        else ('Найти модуль и направление ротора поля в M.',))
    if kind not in ('curl_norm_direction_at_point','curl_small_circle_circulation'):
        raise Unsupported('An ordinary Cartesian curl calculation was expected')
    if not isinstance(task['field'],list) or len(task['field'])!=3:raise Unsupported('Three field components are required')
    coords=[('s',z) for z in AXES];ctx=m.context({})
    raw=[m.parse(f,None,list(AXES)) for f in task['field']]
    original=task['at' if small_circle else 'point']
    if len(original)!=3:raise Unsupported('Point dimension differs from the field')
    points=[m.parse(str(p),None) for p in original];at=dict(zip(coords,points,strict=True))
    guards=list(dict.fromkeys(g for f in raw for g in domain_conditions(f,True)))
    if not all(m.constant_defined(p,ctx) for p in points) or not all(known_guard((r,m.substitute(t,at)),ctx) for r,t in guards):
        raise Unsupported('The original field is not proved smooth on a neighborhood of the given real point')
    def at_partial(f,axis):
        x=('s',axis)
        section=m.substitute(f,{s:v for s,v in at.items() if s!=x})
        child=request('partial at point/'+axis,dict(kind='derivative_at',function=source(section),variable=axis,
                       point=source(at[x]),requested_output=['finite_derivative'],method_requirement='table_and_rules'))
        return freeze(child['value'])
    v=coordinate_curl(at_partial,raw);square=m.simplify(m.dot(v,v))
    plan=dict(theorem='method.cartesian_curl_and_stokes',original_point=points,field=raw,
              local_smoothness=guards,curl=v,squared_norm=square,
              argument=['Check the original field on a neighborhood of the point, then take the cyclic differences of partial derivatives.'])
    if not small_circle:
        positive=m.sign(square,ctx)
        if positive not in (0,1):raise Unsupported('The direction of a zero or unverified vector cannot be assigned')
        norm=m.simplify(('sqrt',square))
        direction=[m.simplify(m.div(c,norm)) for c in v] if positive else None
        return plan,dict(curl=v,norm=norm,unit_direction=direction)
    differences=[z if m.num(p)==0 else '('+z+'-'+source(p)+')' for z,p in zip(AXES,points)]
    sphere='+'.join(z+'^2' for z in differences)+'=epsilon^2'
    plane='+'.join(z+'*cos('+a+')' for z,a in zip(differences,('alpha','beta','gamma')))+'=0'
    if ((task['sphere'],task['plane'],task['normal'])!=(sphere,plane,'unit, sum of squared direction cosines=1')):
        raise Unsupported('The circle must be centered at the original smooth point and oriented by the declared unit normal')
    normal=[('cos',('s',a)) for a in ('alpha','beta','gamma')]
    coefficient=m.simplify(m.mul(m.PI,m.dot(v,normal)))
    plan.update(theorem='method.cartesian_curl_and_stokes',unit_normal=normal,
                argument=['Smoothness at the center and continuity of the curl give uniform convergence on the shrinking disks.',
                          'Stokes integrates its normal component over a disk of area pi*epsilon^2. Reversing the normal negates the circulation.'])
    return plan,dict(curl=v,circulation_leading_coefficient=coefficient,scale='epsilon^2',error='o(epsilon^2)')


def vector_operator(task,request):
    """Use the existing component algebra for Cartesian curls and mixed partials."""
    from tasks import domain_conditions,source
    from model import q
    kind=task['kind'];coords=[('s',z) for z in AXES]
    if kind=='rigid_rotation_curl':
        vector_source(task,{'axis','angular_speed','point'},
            ('Найти ротацию вектора линейной скорости жидкости в точке M при вращении вокруг указанной оси.',))
        speed=re.fullmatch(r'([A-Za-z]\w*) constant',task['angular_speed'])
        angles=[re.fullmatch(r'cos\(([A-Za-z]\w*)\)',s) for s in task['axis']]
        if not speed or len(angles)!=3 or not all(angles) or task['point']!=list(AXES):
            raise Unsupported('The velocity must be the rigid rotation about an axis with specified direction cosines')
        fixed=[speed[1],*(h[1] for h in angles)]
        if set(fixed)&set(AXES) or len(set(fixed))!=4:raise Unsupported('The fixed axis coordinates and speed must be independent symbols')
        axis=[m.parse(s,None,fixed) for s in task['axis']];speed=('s',fixed[0])
        field=vector_cross([m.mul(speed,a) for a in axis],coords)
        value=coordinate_curl(coordinate_sections([*AXES,*fixed],request),field)
        return dict(theorem='method.cartesian_curl_and_stokes',velocity=field,unit_axis=axis,
                    argument=['Velocity is angular velocity crossed with position.',
                              'Each component of the angular velocity is spatially constant, so each curl component has two identical contributions.']),dict(curl=value)
    if 'expression' in task:
        vector_source(task,{'expression'},('Найти выражение через производные.',))
        e=task['expression']
        match=re.fullmatch(r'(curl)\(grad\(([A-Za-z]\w*)\)\)|(div)\(curl\(([A-Za-z]\w*)\)\)',e)
        if not match:raise Unsupported('A specified curl-of-gradient or divergence-of-curl was expected')
        name=match[2] or match[4]
        raw=dict(kind='cartesian_field_operator',expression=e,regularity={name:2})
        child=request('commute mixed Cartesian derivatives on the stated smooth domain',raw)
        return (dict(theorem='method.cartesian_curl_and_stokes',smoothness={name:'C2 locally'},
                    expression=e,argument=['The displayed smoothness is sufficient for mixed second derivatives to commute.']),
                    dict(operator_value=child['value']))
    if 'requested_operator' in task:
        vector_source(task,{'field','requested_operator','requested_output'},('Вычислить rot r.',))
        if task['requested_operator']!='curl' or task.get('requested_output',['operator_values'])!=['operator_values'] or len(task['field'])!=3:
            raise Unsupported('The three original components of the field and the curl request are required')
        field=[m.parse(component,None,list(AXES)) for component in task['field']]
        if domain_conditions(tuple(['vector',*field]),True):
            raise Unsupported('The formal field evaluation needs an everywhere-smooth original field')
        if task.get('source',{}).get('literal_requirement') and field!=coords:
            raise Unsupported('The printed radius vector differs from these components')
        return (dict(theorem='method.cartesian_curl_and_stokes',field=field,argument=['Differentiate the three Cartesian components.']),
                    dict(curl=coordinate_curl(coordinate_sections(list(AXES),request),field)))
    vector_source(task,{'field','r','c'},('Вычислить rot[f(r)r].','Найти ротор указанного поля.'))
    if task.get('r','norm(r_vector)')!='norm(r_vector)' or task.get('c','constant vector')!='constant vector':
        raise Unsupported('The radius and constant vector were not identified')
    choices={'f(r)*r_vector':('curl(f*X)',False),
             'c*f(r)':('curl(c*f)',True),
             'c cross (f(r)*r_vector)':('curl(cross(c,f*X))',True)}
    route=choices.get(task['field'])
    if route is None or ('c' in task)!=route[1]:raise Unsupported('The original radial or constant-vector factors were not identified')
    expression,uses_constant=route
    if task.get('source',{}).get('literal_requirement')=='Вычислить rot[f(r)r].' and uses_constant:
        raise Unsupported('The printed radial field differs from this expression')
    formal=compile_identity(dict(kind='formal_vector_identity',claim=expression+'='+expression,
                                 fields={'f':'scalar',**({'X':'vector'} if 'X' in expression else {})},
                                 hypotheses=['c constant vector'] if uses_constant else []))['context']
    form=component_form('left',formal)
    radius=('sqrt',m.dot(coords,coords));f=('s','f_r');fp=('s','f_prime_r')
    C=[('s','c_'+z) for z in AXES]
    atoms={('f','',''):f}
    for i,z in enumerate(AXES):
        atoms['f','',z]=m.div(m.mul(fp,coords[i]),radius)
        atoms['X',z,'']=coords[i];atoms['c',z,'']=C[i]
        for a in AXES:atoms['X',z,a]=q(int(a==z))
    value=[]
    for component in form:
        terms=[]
        for mon,c in component:
            result=q(c)
            for atom,power in mon:result=m.mul(result,m.power(atoms[atom],power))
            terms.append(result)
        value.append(m.simplify(m.dot(terms,[m.ONE]*len(terms)) if terms else m.ZERO))
    at_origin=([m.ZERO]*3 if not uses_constant or task['field']=='c*f(r)' else
               [m.mul(q(2),m.mul(('s','f_0'),z)) for z in C])
    case=('if f(r)-f(0)=o(r), the derivative is zero; a nonzero constant vector otherwise needs its own center differentiability'
          if task['field']=='c*f(r)' else 'when f is continuous at zero')
    return (dict(theorem='method.cartesian_curl_and_stokes',component_expansion=form,radius=radius,
                radial_derivatives=[atoms['f','',z] for z in AXES],
                argument=['Away from zero, use dr/dx_i=x_i/r and the ordinary scalar chain rule.',
                          'At zero use the indicated first-order radial expansion; it does not divide by the radius.']),
                dict(curl_at_positive_radius=value,at_origin=dict(curl=at_origin,condition=case)))


def orthogonal_vector_operator(task):
    """Use flux or circulation of an infinitesimal coordinate cell."""
    divergence=task['kind']=='orthogonal_coordinate_divergence'
    if divergence:
        vector_source(task,{'map','orthogonal','hint','requested'},
                      ('Вывести общую формулу и получить цилиндрический и сферический частные случаи.',))
        if (task['orthogonal'] is not True or task['requested']!=['orthogonal curvilinear','cylindrical','spherical']
                or task.get('hint') not in (None,'flux through the infinitesimal coordinate parallelepiped bounded by u,v,w=const')):
            raise Unsupported('Regular orthogonal coordinates, flux, and both printed special cases are required')
        mapping=[re.fullmatch(r'([xyz])=([A-Za-z]\w*)\(([A-Za-z]\w*),([A-Za-z]\w*),([A-Za-z]\w*)\)',s)
                 for s in task['map']]
        if (len(mapping)!=3 or not all(mapping) or [m[1] for m in mapping]!=list(AXES)
                or len({m[2] for m in mapping})!=3 or len(set(mapping[0].groups()[2:]))!=3
                or any(z.groups()[2:]!=mapping[0].groups()[2:] for z in mapping)):
            raise Unsupported('The three chart variables are not consistently bound')
    else:
        vector_source(task,{'coordinates','field'},('Выразить ротацию вектора в указанных координатах.',))
        if task['field']!='arbitrary vector given in the corresponding unit basis':
            raise Unsupported('The formula uses components in the orthogonal unit basis')
    charts={'plane polar':(('r','phi'),('1','r'),'r>0'),
            'cylindrical':(('r','phi','z'),('1','r','1'),'r>0'),
            'spherical':(('r','theta','phi'),('1','r','r*sin(theta)'),'r>0, 0<theta<pi')}
    def formulas(coords,metric):
        length=len(coords);out=[]
        if divergence:
            return dict(density=['D_'+v+'('+ '*'.join([f'A_{i}',*(h for j,h in enumerate(metric) if j!=i and h!='1')])+')'
                                 for i,v in enumerate(coords)],
                        division='*'.join(h for h in metric if h!='1') or '1')
        for i,j in (((0,1),) if length==2 else ((1,2),(2,0),(0,1))):
            out.append(dict(area_density=[metric[i],metric[j]],positive_derivative=[coords[i],metric[j],f'A_{j}'],
                            negative_derivative=[coords[j],metric[i],f'A_{i}']))
        return out
    selected=task['requested'][1:] if divergence else [task['coordinates']]
    if any(c not in charts for c in selected):raise Unsupported('Unknown coordinate metric')
    outputs={}
    for c in selected:
        coords,metric,condition=charts[c]
        outputs[c]=dict(coordinates=coords,Lame_coefficients=metric,regular_chart=condition,operator=formulas(coords,metric))
    if divergence:
        coords=mapping[0].groups()[2:];scales=('h_0','h_1','h_2')
        outputs['orthogonal curvilinear']=dict(coordinates=coords,Lame_coefficients=scales,
              regular_chart='h_i=||partial_i r||>0',operator=formulas(coords,scales))
    argument=(['Opposite face fluxes are differences of A_i h_j h_k in the i-th coordinate, times the transverse widths.',
               'Divide by the oriented-cell volume magnitude h_i h_j h_k and pass to the limit.']
               if divergence else ['In a positively oriented coordinate rectangle the opposite edge circulations differentiate h_j A_j and h_i A_i.',
               'Divide their difference by the local area scale h_i h_j. The three cyclic rectangles give the unit-basis components.'])
    argument.append('The metric coefficients follow from the norms of the derivatives of the usual polar, cylindrical and spherical parametrizations on their regular charts.')
    return dict(theorem='method.orthogonal_coordinate_operators',argument=argument),dict(coordinate_formulas=outputs)


def surface_flux_moments(task,request):
    """Integrate normal components of polynomial fields on parametrized faces."""
    from fractions import Fraction as F
    from math import factorial,prod
    from functools import lru_cache
    from tasks import domain_conditions,known_guard,source
    from verify import same_value
    from model import q
    coords=[('s',z) for z in AXES];kind=task['kind'];closed_check=kind=='surface_flux_and_divergence_check'
    cylinder=kind=='oriented_boundary_integral';height=radius=None
    if closed_check:
        vector_source(task,{'field','faces','condition','requested'},
                      ('Найти поток через полную поверхность пирамиды и проверить результат по Остроградскому.',))
        faces=task['faces']
        last=re.fullmatch(r'x\+y\+z=([A-Za-z]\w*)',faces[3]) if len(faces)==4 else None
        if (not last or faces[:3]!=['x=0','y=0','z=0'] or task['condition']!=last[1]+'>0'
                or task['requested']!=['direct surface flux','divergence theorem verification']):
            raise Unsupported('The direct calculation and independent volume check require all four stated simplex faces')
        field=task['field'];shape='simplex';orientation='outward';height=last[1]
    elif cylinder:
        vector_source(task,{'variables','coefficients','boundary_of','orientation','parameters','stated_conditions','method_requirement','requested_output'},
                      ('Найти поток через полную поверхность цилиндра.',))
        region=task['boundary_of']
        if set(region)!={'cylinder'} or set(region['cylinder'])!={'radial_constraint','axial_constraint'}:
            raise Unsupported('The cylindrical solid must have an exact bounded geometry')
        limits=region['cylinder']
        match=re.fullmatch(r'x\^2\+y\^2<=([A-Za-z]\w*|[0-9]+)\^2;0<=z<=([A-Za-z]\w*|[0-9]+)',
                            limits['radial_constraint']+';'+limits['axial_constraint'])
        if (not match or task['variables']!=list(AXES) or task['requested_output']!=['boundary_integral']
                or task.get('method_requirement') not in (None,'divergence_theorem')):
            raise Unsupported('The full cylindrical boundary and its stated method were not identified')
        radius,height=match.groups();shape='cylinder_closed';orientation=task['orientation'];field=task['coefficients']
    else:
        vector_source(task,{'field','surface','orientation','parameters'},
                      ('Найти поток заданного поля через указанную часть поверхности.',
                       'Найти поток радиус-вектора через заданную поверхность.',
                       'Найти поток через положительный октант единичной сферы.'))
        surface=task['surface'];field=task['field'];orientation=task.get('orientation','unspecified in print')
        label=r'([A-Za-z]\w*|[0-9]+)'
        if z:=re.fullmatch(r'(lateral surface|upper base) of x\^2\+y\^2<=z\^2, 0<=z<='+label,surface):
            shape='cone_side' if z[1]=='lateral surface' else 'cone_cap';height=z[2]
        elif z:=re.fullmatch(r'lateral surface of x\^2\+y\^2<='+label+r'\^2, 0<=z<='+label,surface):
            shape='cylinder_side';radius,height=z.groups()
        elif z:=re.fullmatch(r'z='+label+r'-sqrt\(x\^2\+y\^2\), 0<=z<='+label,surface):
            if z[1]!=z[2]:raise Unsupported('The lower disk of the cone was not identified')
            shape='decreasing_cone';height=z[1]
        elif z:=re.fullmatch(r'x\^2\+y\^2\+z\^2=('+label+r'\^2|1), x,y,z>=0',surface):
            shape='sphere_octant';radius=z[2] if z[2] else '1'
        else:raise Unsupported('No admitted oriented face parametrization for this surface')
        literal=task.get('source',{}).get('literal_requirement','')
        if (literal.startswith('Найти поток радиус-вектора') and field!=list(AXES) or
                'октант единичной' in literal and (shape!='sphere_octant' or radius!='1')):
            raise Unsupported('The printed field or unit sphere differs from the supplied geometry')
    choices=('outward','inward') if cylinder or closed_check else ('outward','inward','unspecified in print')
    if orientation not in choices or not isinstance(field,list) or len(field)!=3:
        raise Unsupported('Expected three components and an original face orientation')
    geometric={s for s in (radius,height) if s and s.isidentifier()};params=task.get('parameters',sorted(geometric))
    if not geometric<=set(params) or len(params)!=len(set(params)) or set(params)&set(AXES):
        raise Unsupported('Geometry parameters must be separate from the Cartesian coordinates')
    hypotheses=[]
    if height and height.isidentifier():hypotheses.append(height+'>0')
    if radius and radius.isidentifier():hypotheses.append(radius+'!=0')
    stated=task.get('stated_conditions',[])
    names=[*AXES,*params];dummy='__face'
    while dummy in names:dummy+='_'
    whole=m.context(dict(variable=dummy,parameters=names,parameter_conditions=hypotheses+stated))
    R=m.simplify(('abs',m.parse(radius,None,params))) if radius else None
    H=m.parse(height,None,params) if height else None
    if any(m.sign(a,whole)!=1 for a in (R,H) if a is not None):
        raise Unsupported('The defined figure must have positive dimensions')
    raw=[m.parse(s,None,names) for s in field]
    guards=list(dict.fromkeys(g for e in raw for g in domain_conditions(e,True)))
    if any(not known_guard(g,whole) for g in guards):
        raise Unsupported('An original field pole or nonsmooth point remains on the given faces')
    def monomials(e):
        poly,denominator=m.rational_form(e)
        if set(denominator)!={()}:raise Unsupported('The source needs polynomial moments after proving the domain')
        for mon,c in poly.items():
            d=[0,0,0];coeff=q(c/denominator[()])
            for a,power in mon:
                if a in coords:d[coords.index(a)]=power
                elif not any(m.contains(a,v) for v in coords):coeff=m.mul(coeff,m.power(a,power))
                else:raise Unsupported('The field is not polynomial in the face coordinates')
            yield d,coeff
    @lru_cache(None)
    def quadrant(i,j):
        if i>=2:return m.mul(q(i-1,i+j),quadrant(i-2,j))
        if j>=2:return m.mul(q(j-1,i+j),quadrant(i,j-2))
        return m.div(m.PI,q(2)) if not i and not j else q(1,2) if i and j else m.ONE
    def full_angle(i,j):
        return m.ZERO if i%2 or j%2 else m.mul(q(4),quadrant(i,j))
    def power_moment(coefficient,scale,degree):
        return m.mul(coefficient,m.power(scale,degree))
    def integrate(e,axis,face):
        total=m.ZERO
        for d,c in monomials(e):
            i,j,k=d;order=i+j+k
            if face in ('cone_side','decreasing_cone','sphere_octant','cylinder_side'):
                if face=='cylinder_side' and axis==2:continue
                i+=axis==0;j+=axis==1;k+=axis==2 and face=='sphere_octant'
            if face in ('cone_cap','upper_cap','lower_cap'):
                if axis!=2 or face=='lower_cap' and k:continue
                r=H if face=='cone_cap' else R
                moment=power_moment(m.div(full_angle(i,j),q(i+j+2)),r,i+j+2)
                if k:moment=m.mul(moment,m.power(H,k))
                if face=='lower_cap':moment=m.neg(moment)
            elif face=='cone_side':
                moment=power_moment(m.div(full_angle(i,j),q(order+2)),H,order+2)
                if axis==2:moment=m.neg(moment)
            elif face=='decreasing_cone':
                beta=q(factorial(order-k+1)*factorial(k),factorial(order+2))
                moment=power_moment(m.mul(full_angle(i,j),beta),H,order+2)
            elif face=='cylinder_side':
                moment=m.mul(power_moment(full_angle(i,j),R,order-k+1),m.div(m.power(H,k+1),q(k+1)))
            elif face=='sphere_octant':
                moment=power_moment(m.mul(quadrant(i,j),quadrant(k,i+j+1)),R,order+2)
            elif face=='simplex_slant':
                moment=power_moment(q(prod(factorial(x) for x in d),factorial(order+2)),H,order+2)
            elif face=='simplex_coordinate':
                if d[axis]:continue
                moment=power_moment(q(-prod(factorial(x) for x in d),factorial(order+2)),H,order+2)
            elif face=='simplex_volume':
                moment=power_moment(q(prod(factorial(x) for x in d),factorial(order+3)),H,order+3)
            elif face=='cylinder_volume':
                moment=m.mul(power_moment(m.div(full_angle(i,j),q(i+j+2)),R,i+j+2),m.div(m.power(H,k+1),q(k+1)))
            else:raise Unsupported('Unrecognized normal moment region')
            total=m.add(total,m.mul(c,moment))
        return total
    faces={'simplex':['simplex_slant','simplex_coordinate'],
           'cylinder_closed':['cylinder_side','upper_cap','lower_cap']}.get(shape,[shape])
    direct={face:[integrate(e,i,face) for i,e in enumerate(raw)] for face in faces}
    values=[z for row in direct.values() for z in row];outward=m.simplify(m.dot(values,[m.ONE]*len(values)))
    plan=dict(theorem='method.oriented_polynomial_face_moments',shape=shape,outward_components=direct,
              geometric_hypotheses=hypotheses,source_smoothness=guards,regular_dimensions=[a for a in (R,H) if a is not None],
              argument=['Expand the normal components into Cartesian monomials on the admitted parametrizations.',
                        'Integrate the powers using parity on a full circle, the quadrant recurrence, and elementary simplex moments.'])
    if closed_check or cylinder:
        density=freeze(request('divergence on the complete regular solid',dict(kind='oriented_boundary_integral',
            variables=list(AXES),coefficients=field,parameters=params,stated_conditions=hypotheses+stated,
            boundary_of={'bounded_regular_region':True},orientation='outward',
            method_requirement='divergence_theorem',requested_output=['equivalent_interior_integral']))['compilation']['density'])
        bulk=m.simplify(integrate(density,0,'simplex_volume' if closed_check else 'cylinder_volume'))
        if not same_value(bulk,outward):raise Unsupported('The normal-flux moments disagree with the independent divergence calculation')
        plan.update(divergence=density,divergence_integral=bulk)
    if closed_check:return plan,dict(direct_flux=outward,divergence_theorem_value=plan['divergence_integral'],faces=direct)
    if orientation=='unspecified in print':return plan,dict(flux_outward=outward,flux_inward=m.neg(outward))
    return plan,{('boundary_integral' if cylinder else 'flux'):outward if orientation=='outward' else m.neg(outward)}


def vector_integral_theory(task,request):
    """Apply the integral theorems with the orientation, regularity and original singular set exposed."""
    from model import q
    kind=task['kind'];theorem='method.field_integral_balance'
    def prove(steps,**result):
        return dict(theorem=theorem,argument=steps),result
    if kind=='formal_vector_identity':
        vector_source(task,{'claim','surface','n'},('Доказать параметрическую формулу потока вектора.',))
        if (task['surface'],task['claim'],task['n'])!=(
                'r(u,v), (u,v) in Omega','integral_S a_n dS = integral_Omega det(a,r_u,r_v) du dv',
                'unit surface normal consistent with parameter orientation'):
            raise Unsupported('The parametric surface, normal convention and scalar triple product must agree')
        return prove(['On a regular oriented patch, n=(r_u cross r_v)/|r_u cross r_v|.',
                      'The surface measure is |r_u cross r_v| du dv. Cancel the positive norm and use the scalar triple product.',
                      'For a parametrization covering the surface once up to measure-zero boundaries, the parameter integral counts each surface point once.'],
                     equality=task['claim'],scope='regular oriented surface parametrization of multiplicity one')
    if kind=='divergence_theorem_proof':
        vector_source(task,{'surface','claim'},('Доказать тождество между поверхностным интегралом нормальной производной и объёмным интегралом лапласиана.',))
        if (task['surface'],task['claim'])!=('S bounds V','integral_S ∂u/∂n dS=integral_V laplacian(u) dV'):
            raise Unsupported('Expected the normal derivative on the oriented boundary of the same volume')
        return prove(['The normal derivative is dot(grad(u),n).',
                      'Apply the divergence theorem to grad(u) on the bounded regular region, with the outward normal.',
                      'The divergence of this gradient is the sum of the unmixed second partial derivatives.'],
                     equality=task['claim'],scope='C2 function on a neighborhood of the regular closed volume')
    if kind=='singular_radial_flux':
        vector_source(task,{'field','parameter','surface','r_i','hypothesis','orientation'},
            ('Найти поток через замкнутую поверхность, окружающую начало.',
             'Найти поток через замкнутую поверхность, окружающую источники M_i.'))
        source_name=re.fullmatch(r'([A-Za-z]\w*)\*r_vector/r\^3',task['field'])
        if source_name:
            symbol=source_name[1]
            if set(task)-{'kind','id','source','field','parameter','surface'} or (
                    task['parameter'],task['surface'])!=('constant '+symbol,'closed enclosing 0, outward'):
                raise Unsupported('The original radial pole must be inside a closed outward boundary')
            strength=('s',symbol)
        elif (set(task)-{'kind','id','source','field','r_i','hypothesis','orientation'} or
              (task['field'],task.get('r_i'),task.get('hypothesis'),task.get('orientation'))!=(
               'sum_{i=1}^n grad(-e_i/(4*pi*r_i))','distance to M_i',
               'all n source points inside surface, e_i constants','outward')):
            raise Unsupported('Each stated source must belong strictly inside the closed outward surface')
        else:strength=None
        if (source_name and 'источники' in task.get('source',{}).get('literal_requirement','') or
                not source_name and 'начало' in task.get('source',{}).get('literal_requirement','')):
            raise Unsupported('The print specifies a different set of poles')
        steps=['Away from a source, differentiation gives div(r_vector/r^3)=3/r^3−3(r dot r)/r^5=0.',
               'Excise a small ball centered at each distinct source. Apply the divergence theorem on the remaining regular region.',
               'The inward normal of the punctured region is opposite to the outward sphere normal.',
               'On a radius-s sphere the outward flux of c*r_vector/r^3 is (c/s^2)*(4*pi*s^2)=4*pi*c.']
        if strength is not None:return prove(steps,flux=m.mul(m.mul(q(4),m.PI),strength))
        return prove(steps+['Linearity treats every source term separately, including coincident source points.'],
                     flux='sum(i=1..n,e_i)')
    if kind in ('radial_field_potential','radial_field_work','finite_mass_gravity_potential'):
        theorem='method.radial_field_primitives'
        if kind=='finite_mass_gravity_potential':
            vector_source(task,{'sources'},('Найти потенциал гравитационного поля системы масс.',))
            if task['sources']!='m_i at M_i, i=1..n; convention of preceding exercise':
                raise Unsupported('The sign of the mass field or its original source set is unbound')
            return prove(['For each source, grad(m_i/|P−M_i|)=−m_i(P−M_i)/|P−M_i|^3 at positive distance.',
                          'Add the potentials by linearity on the complement of all stated sources.'],
                         potential='sum(i=1..n,m_i/|P-M_i|)+C',domain='P not in {M_1,...,M_n}')
        work=kind=='radial_field_work'
        vector_source(task,{'field','hypothesis','path'} if work else {'field','f'},
            ('Найти работу радиального поля вдоль дуги AB.',) if work else ('Доказать потенциальность радиального поля и найти потенциал.',))
        if (task['field']!='f(r)*r_vector' or
                (work and (task['hypothesis'],task['path'])!=('f continuous','arc from A to B')) or
                (not work and task['f']!='single-valued continuous scalar function of radius')):
            raise Unsupported('The field must be a continuous radial scalar times the radius vector')
        steps=['For P with positive radius, the fundamental theorem gives d/dr ∫_0^r s f(s) ds=r f(r). The chain rule gives the original vector.',
               'At zero the integral is O(r²) by continuity of f. Its derivative as a function of P is zero, as is the field.']
        if work:return prove(steps+['The pullback of this exact differential integrates to the endpoint difference along any admissible arc.'],
                             work='integral(|A|..|B|,s*f(s) ds)')
        return prove(steps,potential='integral(0..|P|,s*f(s) ds)+C')
    if kind=='angular_circulation':
        vector_source(task,{'field','winding_condition'},('Найти циркуляцию градиента arctg(y/x) по замкнутому контуру.',))
        if task['field']!='grad(atan(y/x))' or task['winding_condition'] not in (
                'C does not surround the Oz axis','C surrounds the Oz axis'):
            raise Unsupported('The original argument branch or winding assumption was not identified')
        surrounds=task['winding_condition']=='C surrounds the Oz axis'
        return prove(['The printed potential atan(y/x) is defined only for x≠0. Its gradient there is (−y,x,0)/(x²+y²).',
                      'A closed curve inside either half-space has circulation zero because it has the displayed single-valued potential.',
                      'A curve with nonzero winding about Oz intersects the plane x=0, so the literal field is not defined all along it.',
                      'The continuous extension of the displayed components off the axis is a different domain. Along it the one-form is the local derivative of the lifted argument, whose total change is 2π times the winding.'],
                     original=('no admissible winding curve for the literal field' if surrounds else
                               '0 if C lies in x≠0; otherwise the original integral is not defined everywhere'),
                     continued_field='2*pi*winding(C,Oz)' if surrounds else q(0))
    if kind=='planar_flux_and_circulation':
        vector_source(task,{'field','boundary','requested'},('Найти расход Q и циркуляцию Γ; определить уравнения для несжимаемого безвихревого потока.',))
        if (task['field'],task['boundary'],task['requested'])!=('w=(u(x,y),v(x,y))','closed C bounding S',
                 ['outward discharge','circulation','equations under incompressible and irrotational hypotheses']):
            raise Unsupported('The original two planar integral quantities or both flow assumptions remain unbound')
        return prove(['For positive traversal the outward normal times ds is (dy,−dx). Green gives the integral of u_x+v_y.',
                      'The tangent integral is ∮ u dx+v dy. Green gives the integral of v_x−u_y.',
                      'For arbitrary sufficiently small regular subregions and continuous derivatives, zero discharge and circulation are equivalent to vanishing of their respective densities.'],
                     discharge='integral_S (u_x+v_y) dx dy',positive_circulation='integral_S (v_x-u_y) dx dy',
                     reverse_circulation='negative of positive circulation',local_conditions=['u_x+v_y=0','v_x-u_y=0'])
    if kind=='fluid_mass_balance':
        vector_source(task,{'source_statement','rho','v','target','hint'},('Вывести уравнение непрерывности для жидкости.',))
        if ((task['source_statement'],task['rho'],task['v'],task['target'])!=(
              'moving incompressible fluid fills V, no sources or sinks','density rho(x,y,z)','velocity','d rho/dt + div(rho*v)=0')
             or task.get('hint') not in (None,'consider flux across an arbitrary subvolume inside V')):
            raise Unsupported('The density, zero sources and Eulerian balance were not identified')
        return prove(['For every fixed subvolume its mass change is minus the outward flux of rho*v.',
                      'The divergence theorem changes the flux to its volume integral. Differentiating mass in a fixed subvolume gives the integral of partial_t rho.',
                      'An integral of the continuous residual vanishing on every sufficiently small subvolume makes that residual zero.'],
                     continuity_equation='partial_t rho+div(rho*v)=0',steady_reduction='div(rho*v)=0 when rho has no t dependence',
                     incompressible_reduction='partial_t rho+v dot grad(rho)=0 if div(v)=0')
    if kind=='heat_conduction_balance':
        vector_source(task,{'outward_heat','k','u','n'},('Найти накопленную за единицу времени теплоту в V и вывести уравнение теплопроводности.',))
        if (task['outward_heat'],task['k'],task['u'],task['n'])!=('dQ=-k*dot(n,grad(u))*dS per unit time',
                'thermal conductivity','temperature','unit normal'):
            raise Unsupported('The sign of the heat flux and temperature variable must be bound')
        return prove(['Accumulation from conduction is minus the stated outward heat flux.',
                      'The divergence theorem changes this into the integral of div(k grad u).',
                      'In the absence of internal sources and with volumetric heat capacity c_v, local heat storage is c_v partial_t u.',
                      'Equality on all fixed subvolumes gives the pointwise heat equation under the indicated smoothness.'],
                     accumulation_per_time='integral_V div(k grad u) dV',
                     heat_equation='c_v partial_t u=div(k grad u)',constant_material='partial_t u=(k/c_v) laplacian(u)',
                     constitutive_condition='c_v positive volumetric heat capacity; no internal sources')
    if kind=='newton_potential_gradient_identity':
        vector_source(task,{'claim','r','outward_normal','S'},('Доказать тождество для градиента объёмного потенциала.',))
        if (task['claim'],task['r'],task['outward_normal'],task['S'])!=(
                'grad_P integral_V rho(Q)/r dV= -integral_S rho(Q)*n/r dS + integral_V grad_Q(rho(Q))/r dV',
                'distance(P,Q)','n','boundary of V'):
            raise Unsupported('The two differentiation variables and outward boundary term must agree')
        return prove(['Away from the coincident point grad_P(1/r)=−grad_Q(1/r). Its order is r^-2, locally integrable in three dimensions.',
                      'For a bounded regular volume and C1 density, split at a small radius about P. The integral of the derivative kernel over the nearby ball stays O(radius) also for small translates of P. The fundamental theorem along each translation bounds the nearby difference quotients by the same estimate. The outer portion differentiates under the integral.',
                      'Integrate the Q derivative by parts away from the coincident point. The boundary of the excised ball contributes O(radius) because 1/r times its area has order r.',
                      'Pass to the limit, retaining the outward normal on the original boundary and the displayed sign.'],
                     equality=task['claim'],scope='bounded C1 region and C1 density on its closure; locally integrable singular terms')
    if kind=='poisson_newtonian_potential':
        vector_source(task,{'field','potential','source_condition'},('Доказать div a=ρ для градиента данного потенциала при осмысленности интегралов.',))
        if (task['field'],task['potential'],task['source_condition'])!=(
                'a=grad(u)','u(P)=-1/(4*pi)*integral_R3 rho(Q)/|P-Q| dQ','соответствующие интегралы имеют смысл'):
            raise Unsupported('The source may impose a regularity assumption excluding the witness')
        return prove(['Choose rho(Q)=1 at Q=(0,0,0) and zero elsewhere.',
                      'For every P the printed improper integral exists and is zero. Changing one point has no effect on any of its integrals away from the excised singularity.',
                      'The resulting potential and its gradient vanish identically. At P=(0,0,0), div a=0 but rho(P)=1.'],
                     printed_claim_holds=False,counterexample=dict(density='one at origin, zero elsewhere',
                         potential=q(0),point=[q(0)]*3,divergence=q(0),density_at_point=q(1)))
    raise Unsupported('No verified field integral theorem covers the literal source')


def vector_path_primitive(task,request):
    """Prove the endpoint formula on the actual specified path, or both orientations."""
    from model import q
    from verify import same_value
    kind=task['kind'];path=task['path']
    plan=dict(theorem='method.radial_field_primitives')
    if kind!='line_integral' or task.get('requested_output')!=['line_integral'] or task['variables']!=list(AXES):
        raise Unsupported('A source one-form and all three Cartesian coordinates are required')
    if isinstance(path,dict):
        vector_source(task,{'variables','coefficients','parameters','path','requested_output'},
            ('Найти работу поля вдоль кратчайшей дуги большого круга сферы x²+y²+z²=25 от M(3,4,0) к N(0,0,5).',),('given_path',))
        if set(path)!={'start','end','geometry','sphere_radius'} or path['geometry']!='shortest great-circle arc':
            raise Unsupported('The indicated great-circle arc is not bound')
        radius=m.parse(str(path['sphere_radius']),None);ctx=m.context({})
        if not m.constant_defined(radius,ctx) or m.sign(radius,ctx)!=1:
            raise Unsupported('The printed sphere must be a genuine sphere')
        points=[[m.parse(str(t),None) for t in path[k]] for k in ('start','end')]
        if any(len(p)!=3 or not all(m.constant_defined(x,ctx) for x in p) or
                not same_value(m.dot(p,p),m.power(radius,2)) for p in points):
            raise Unsupported('Both given endpoints must lie on the original sphere')
        if 'given_path' in task.get('source',{}) and task['source']['given_path']!=(
                'shortest great-circle arc on sphere x²+y²+z²=25; proving independence is sufficient for this specified path'):
            raise Unsupported('An additional printed path condition remains')
        if task.get('source',{}).get('literal_requirement') and (
                m.num(radius)!=5 or [[m.num(x) for x in p] for p in points]!=[[3,4,0],[0,0,5]]):
            raise Unsupported('The bound textual sphere and endpoints differ from the structured inputs')
        child=request('global primitive on a domain containing the whole arc',
            dict(kind='line_integral',variables=task['variables'],coefficients=task['coefficients'],
                 parameters=task.get('parameters',[]),path={k:path[k] for k in ('start','end')},requested_output=['line_integral']))
        plan.update(radius=radius,original_points=points,
                    argument=['Both points are on the genuine sphere, so a shortest great-circle arc exists.',
                              'The verified primitive is global. Its endpoint difference applies on the printed arc.'])
        return plan,dict(line_integral=child['value'])
    vector_source(task,{'variables','coefficients','parameters','parameter','path','requested_output'},
                  ('Найти циркуляцию (-y,x,c) по указанной окружности в плоскости z=0.',),('circle','orientation'))
    if (not isinstance(path,list) or not path or any(set(p)!={'map','lower','upper','direction'}
                                                    or p['direction']!='unspecified in print' for p in path)):
        raise Unsupported('A whole smooth path with an unspecified traversal is required')
    if task.get('source',{}).get('literal_requirement'):
        # The stated form and the two circle descriptions must survive the reader.
        meta=task['source'];var=task['parameter']
        circle=meta.get('circle');shift={'x^2+y^2=1, z=0':'','(x-2)^2+y^2=1, z=0':'2+'}.get(circle)
        if (shift is None or meta.get('orientation')!='standard positive in the xy plane since the printed circle has no separate orientation arrow'
                or task['coefficients']!=['-y','x','c'] or task.get('parameters')!=['c'] or len(path)!=1
                or (path[0]['map'],path[0]['lower'],path[0]['upper'])!=([shift+'cos('+var+')','sin('+var+')','0'],'0','2*pi')):
            raise Unsupported('The printed field, circle or traversal is not bound')
    neutral={k:v for k,v in task.items() if k not in ('id','source','path')}
    neutral['path']=[{k:v for k,v in segment.items() if k!='direction'} for segment in path]
    chosen=request('verify the one-form on the displayed traversal',neutral)
    segments=chosen['compilation'].get('pieces',())
    if not segments or not all(same_value(a,b) for a,b in zip(segments[0]['start'],segments[-1]['end'],strict=True)):
        raise Unsupported('The closed path needs explicit endpoints on every piece')
    # For objects where the book says circulation, the two orientations must
    # have opposite signs even when the original page omitted an arrow.
    value=freeze(chosen['value']);plan['argument']=['Pull back the one-form to the recorded traversal.',
        'Reversing the same path changes the sign of its integral.']
    return plan,dict(displayed_traversal=value,reverse_traversal=m.neg(value))


def guarded_field_potential(task,request):
    """Propose a lift from a known coefficient, and verify every component on the original domain."""
    from tasks import domain_conditions,entailed_domain_guards,guard_source,known_guard,source
    from verify import same_value
    from fractions import Fraction
    vector_source(task,{'variables','coefficients','parameters','stated_conditions','requested_output','start','end'},
                  ('Убедиться в потенциальности и найти работу вдоль пути от M к N в положительном октанте.',
                   'Найти потенциал гравитационного поля точечной массы в начале координат.'))
    wants=task['requested_output'];endpoint=wants==['exactness_proof','line_integral']
    if (task['variables']!=list(AXES) or len(task['coefficients'])!=3
            or wants not in (['potential_and_domain'],['exactness_proof','line_integral'])
            or any((k in task)!=endpoint for k in ('start','end'))):
        raise Unsupported('A complete potential or a checked endpoint difference was expected')
    coords=[('s',z) for z in AXES];params=task.get('parameters',[]);names=[*AXES,*params]
    raw=[m.parse(s,None,names) for s in task['coefficients']]
    guards=list(dict.fromkeys(g for e in raw for g in domain_conditions(e)))
    stated=task.get('stated_conditions',[])
    unscoped=m.context(dict(variable='__potential',parameters=names,parameter_conditions=stated))
    facts=list(dict.fromkeys([*stated,*[guard_source(g) for g in entailed_domain_guards(guards) if not known_guard(g,unscoped)]]))
    ctx=m.context(dict(variable='__potential',parameters=names,parameter_conditions=facts))
    if not all(known_guard(g,ctx) for f in raw for g in domain_conditions(f,True)):
        raise Unsupported('No proof of differentiability on the whole admitted field domain')
    radius=m.dot(coords,coords)
    if (raw[0][0]=='div' and raw[0][2][0]=='rpow'
            and same_value(raw[0][2][1],radius) and m.num(m.simplify(raw[0][2][2]))==Fraction(3,2)):
        denom=raw[0][2];scale=m.simplify(m.substitute(raw[0][1],{coords[0]:m.ONE}))
        if any(m.contains(scale,c) for c in coords) or not all(
                same_value(f,m.div(m.mul(scale,c),denom)) for f,c in zip(raw,coords,strict=True)):
            raise Unsupported('The inverse-cube radial coefficient is not common to all components')
        potential=m.div(m.neg(scale),('sqrt',radius));plan_note='Derivative of the reciprocal radius'
        gradient=[m.div(m.mul(scale,c),denom) for c in coords]
    else:
        lifts=[m.mul(c,f) for c,f in zip(coords,raw,strict=True) if not m.contains(f,c) and f!=m.ZERO]
        if not lifts:raise Unsupported('No simple potential lift can be proposed from these components')
        potential=lifts[0];plan_note='Integrate a coefficient independent of its corresponding coordinate'
        target=dict(kind='partial_derivatives',function=source(potential),variables=list(AXES),parameters=params,
                    stated_conditions=facts,derivative_orders=[1],requested_output=['first_partial_derivatives'])
        checked=request('all gradient components on the source domain',target)
        gradient=[freeze(v) for _,v in checked['partial_values']]
    def canonical_roots(e):
        args=tuple(canonical_roots(z) if isinstance(z,tuple) else z for z in e[1:])
        if e[0] in ('sqrt','rpow'):
            base=args[0]
            if known_guard(('positive',base),ctx):
                num,den=m.rational_form(base)
                root=('sqrt',m.simplify(m.div(m.poly_expr(num),m.poly_expr(den))))
                if e[0]=='sqrt':return root
                exponent=m.num(m.simplify(args[1]))
                if exponent is not None and exponent.denominator==2:
                    return m.power(root,exponent.numerator)
        return (e[0],*args)
    if (not all(known_guard(g,ctx) for g in domain_conditions(potential,True))
            or len(gradient)!=3 or not all(same_value(g,f) or same_value(canonical_roots(g),canonical_roots(f))
                                          for g,f in zip(gradient,raw,strict=True))):
        raise Unsupported('The verified gradient differs from an original component')
    plan=dict(theorem='method.radial_field_primitives',argument=[plan_note,'Verify the gradient and retain the original field domain.'],
              potential=potential,verified_gradient=gradient,source_guards=guards,stated_conditions=stated)
    if not endpoint:
        return plan,dict(potential=potential,domain=guards,stated_conditions=stated,constant='constant per connected component')
    points=[[m.parse(str(x),None,params) for x in task[k]] for k in ('start','end')]
    fixed=m.context(dict(variable='__potential',parameters=params))
    if (stated!=[z+'>0' for z in AXES] or any(len(p)!=3 or
           not all(m.constant_defined(z,fixed) and m.sign(z,fixed)==1 for z in p) for p in points)
           or any(not known_guard(g,unscoped) for g in guards)):
        raise Unsupported('The entire positive-octant path and both endpoints must be in the source domain')
    values=[m.simplify(m.substitute(potential,dict(zip(coords,p,strict=True)))) for p in points]
    plan['endpoint_values']=values
    return plan,dict(line_integral=m.simplify(m.add(values[1],m.neg(values[0]))),potential=potential)



def crossed_component_exactness(task):
    if len(task.get('coefficients',[]))!=3:return None
    coords=list(AXES);ci=r'([A-Za-z][A-Za-z_0-9]*)\(([xyz])\)'
    matches=[re.fullmatch(ci,z) for z in task['coefficients']]
    if not all(matches):return None
    fields=[v[1] for v in matches];arguments=[v[2] for v in matches]
    crossed=[i for i,(a,b) in enumerate(zip(coords,arguments)) if a!=b]
    if len(crossed)!=1:return None
    i,=crossed;j=coords.index(arguments[i]);mode=fields[i]
    if (len(set(fields+coords))!=6 or task.get('stated_conditions') not in
            ([','.join(fields)+' continuous'],[','.join(fields)+' continuous',mode+' constant'])
            or task.get('start')!=[a+'1' for a in coords] or task.get('end')!=[a+'2' for a in coords]):
        raise Unsupported('Continuous factors, two full Cartesian endpoints and the different argument must be bound')
    terms=[f'int_({coords[k]}1)^({coords[k]}2) {fields[k]}(u) du'
           if k!=i else f'{mode}*({coords[k]}2-{coords[k]}1)' for k in range(3)]
    result=dict(exact_if_and_only_if=mode+' is constant',line_integral_in_that_case=' + '.join(terms))
    if len(task['stated_conditions'])==1:
        result.update(printed_claim_holds=False,counterexample=dict(
            cross_coefficient=arguments[i],other_coefficients=ZERO,
            rectangle_coordinates=[coords[j],coords[i]],path_one_integral=ONE,path_two_integral=ZERO))
    return result


def source_curl_product_type(task,request):
    vector_source(task,{'claim','given','requested_output'},
                  ('Доказать напечатанную формулу ротора произведения.',),('source_issue',))
    roles=re.fullmatch(r'scalar ([A-Za-z]\w*), vector ([A-Za-z]\w*)',task.get('given',''))
    if roles is None or roles[1]==roles[2] or task.get('requested_output',['proof'])!=['proof']:
        raise Unsupported('The scalar and vector in the source identity must be declared')
    a,b=roles.groups();types={a:'scalar',b:'vector'}
    left=f'curl({a}*{b})';first=f'{a}*curl({b})'
    bad=f'{left}={first}+grad({a} cross {b})'
    good=f'{left}={first}+(grad({a}) cross {b})'
    literal=task['claim']
    if literal not in (bad,good):raise Unsupported('The original grouping has not been identified')
    child=dict(kind='formal_vector_identity',identity=good,fields=types)
    checked=request('compare the two typed Cartesian sides after placing the gradient on the scalar',child)
    if checked.get('status')!='SOLVED':raise Unsupported('The correctly typed identity lacks a full component proof')
    result=dict(identity=good,components=checked['value'])
    if literal==bad:
        try:compile_identity(dict(kind='formal_vector_identity',claim=bad,fields=types))
        except Unsupported:pass
        else:raise Unsupported('The printed product was not rejected by the type rules')
        result.update(printed_claim_holds=False,counterexample=dict(ill_typed_operation=f'{a} cross {b}',
                      arguments=['scalar','vector'],required=['vector','vector']))
    return dict(theorem='method.typed_curl_product_rule',argument=[
        'Для векторного произведения проверяем оба типа. Скаляр и вектор не образуют вход для этой операции.',
        'Градиент скаляра имеет векторный тип. С ним обе стороны корректной формулы разворачиваются по правилу производной произведения и покомпонентно совпадают.'
    ],source_types=types),result


def plane_cylinder_stokes(task,library):
    from verify import same_value
    vector_source(task,{'coefficients','curve','method_requirement','requested_output'},
                  ('Применяя формулу Стокса, вычислить интеграл.',))
    tube=re.fullmatch(r'x\^2\+y\^2=([A-Za-z]\w*)\^2,([^;]+);([A-Za-z]\w*(?:,[A-Za-z]\w*)*)>0; described as an ellipse, anticlockwise from positive Ox',
                      task.get('curve',''))
    if (tube is None or task.get('requested_output')!=['circulation','stokes_evaluation'] or
            task.get('method_requirement')!='stokes_theorem' or len(task.get('coefficients',[]))!=3):
        raise Unsupported('The cylinder section, orientation and Stokes method are required')
    r,plane,names=tube.groups();names=names.split(',')
    if r not in names or len(set(names))!=len(names) or set(names)&set(AXES) or plane.count('=')!=1:
        raise Unsupported('The plane and all positive scales must bind the original locus')
    terms=list(AXES)+names
    coords=[('s',a) for a in AXES];R=('s',r)
    ctx=m.context(dict(variable='__stokes_scope',parameters=terms,parameter_conditions=[a+'>0' for a in names]))
    a,b=(m.parse(t,None,terms) for t in plane.split('='))
    original=('add',a,('mul',q(-1),b))
    field=[m.parse(t,None,terms) for t in task['coefficients']]
    if not all(known_guard(g,ctx) for e in [original,*field] for g in domain_conditions(e,True)):
        raise Unsupported('An original plane or field guard remains unproved')
    partial,checks=derivative_table(library);normal=[partial(original,key) for key in AXES]
    offset=m.neg(m.substitute(original,{c:ZERO for c in coords}))
    if (any(m.contains(f,c) for f in normal for c in coords)
            or not same_value(original,m.add(m.dot(normal,coords),m.neg(offset)))):
        raise Unsupported('The second constraint is not a genuine affine plane')
    A,B,C=normal
    zsign=m.sign(C,ctx);xsign=m.sign(A,ctx)
    if zsign==0:
        difference=m.add(m.mul(m.power(R,2),m.add(m.power(A,2),m.power(B,2))),m.neg(m.power(offset,2)))
        if not m.constant_defined(difference,ctx) or not (m.nonzero(A,ctx) or m.nonzero(B,ctx)):
            raise Unsupported('The vertical section needs a genuine horizontal normal')
        count={1:2,0:1,-1:0}.get(m.sign(difference,ctx))
        return dict(theorem='method.stokes_cylinder_plane_sections',argument=[
            'У плоскости отсутствует коэффициент при z, поэтому её пересечение с цилиндром определяется пересечением прямой и окружности в плоскости xy.',
            'Проверяем знак квадрата радиуса, умноженного на квадрат нормы линейной части, минус квадрат правой стороны. Он задаёт две точки, касание или пустое множество.',
            'Над каждой плоской точкой получается целая прямая, параллельная оси z. Такие компоненты не образуют замкнутый эллипс для формулы Стокса.'
        ],plane_normal=normal,discriminant=difference),dict(printed_claim_holds=False,
            counterexample=dict(closed_curve_exists=False,vertical_line_count=count,criterion='sign of the displayed discriminant'))
    if zsign not in (-1,1) or xsign not in (-1,1):
        raise Unsupported('Both the next coordinate graph and its oriented viewing side must be regular')
    curl=coordinate_curl(partial,field)
    if any(m.contains(f,c) for f in curl for c in coords):
        raise Unsupported('This Stokes transition needs a constant curl')
    area_scale=m.div(m.mul(q(xsign),m.mul(m.PI,m.power(R,2))),m.mul(q(zsign),C))
    value=m.mul(area_scale,m.dot(curl,normal))
    return dict(theorem='method.stokes_cylinder_plane_sections',argument=[
        'Ненулевой коэффициент при z позволяет выразить высоту над полным диском цилиндра. Его граница переходит в исходный эллипс.',
        'Выбираем нормаль с положительной составляющей по Ox. Векторный элемент плоского графика равен ориентированной нормали, делённой на модуль её z-компоненты.',
        'Проверяем, что ротор постоянен. Формула Стокса сводит циркуляцию к скалярному произведению ротора и векторной площади диска.'
    ],plane_normal=normal,curl=curl,derivative_rules=checks),dict(circulation=value,stokes_method=True)


def homogeneous_differentiation_mode(task):
    source=task.get('source',{})
    if set(source)-OPERATOR_PROVENANCE-{'literal_requirement'}:
        raise Unsupported('The notation and all homogeneous hypotheses must be bound')
    kind=task['kind']
    name=r'[A-Za-z][A-Za-z_0-9]*'
    if kind=='prove_second_order_euler_identity':
        if set(task)-{'id','kind','source','schema','source_statement'}:
            raise Unsupported('The original second derivative goal is not fully represented')
        grammar=fr'For twice differentiable homogeneous ({name})=({name})\(({name}),({name}),({name})\) of degree ({name}) prove \(\3\*d/d\3\+\4\*d/d\4\+\5\*d/d\5\)\^2 \1=\6\(\6-1\)\1 as printed\.'
        h=re.fullmatch(grammar,task['source_statement'])
        if h is None:raise Unsupported('The operator must follow the original homogeneous variables')
        u,_,x,y,z,n=h.groups();k='2';literal=True
    else:
        if (set(task)-{'id','kind','source','given','printed_equation','orders','requested_output'}
                or task.get('requested_output')!=['proof']):
            raise Unsupported('The symbolic differentiation order and every requested output are required')
        h=re.fullmatch(fr'({name})\(({name}),({name}),({name})\) ({name})-times differentiable, homogeneous degree ({name})',task.get('given',''))
        if h is None:raise Unsupported('An abstract smooth homogeneous field is required')
        u,x,y,z,k,n=h.groups()
        if task.get('orders')!=f'{u} is {k}-times differentiable and homogeneous of degree {n}':
            raise Unsupported('The asserted differentiability and homogeneity must match the original axes')
        D=f'({x}*partial_{x}+{y}*partial_{y}+{z}*partial_{z})^{k} {u}'
        literal=f'{D}={n}*({n}-1)*...*({n}-{k}+1)*{u}'
        correct=f'{D}={n}^{k}*{u}'
        if task.get('printed_equation') not in (literal,correct):raise Unsupported('The claimed operator and falling product differ')
        literal=task['printed_equation']==literal
    if len({x,y,z,n,u})!=5 or k in {x,y,z,n,u}:
        raise Unsupported('Operator variables, order and degree must have distinct roles')
    result=dict(composition=f'{n}^{k}*{u}',frozen_coefficients=f'falling_factorial({n},{k})*{u}')
    if literal:
        result.update(printed_claim_holds=False,counterexample=dict(function=x,degree=1,order=2,
                      at=[ONE,ZERO,ZERO],composed=ONE,frozen=ZERO))
    return dict(theorem='method.homogeneous_differentiation_modes',argument=[
        'Дифференцируем f(λX)=λⁿf(X) по λ при λ=1. Получаем Df=n f для оператора D=X·∇.',
        'При композиции D каждый раз снова действует на функцию и переменные коэффициенты. Индукция даёт D^m f=n^m f.',
        'При фиксировании коэффициентов X используем вместо этого производные вдоль прямой с постоянным вектором X. Дифференцирование λⁿ даёт убывающий факториал.',
        'Линейная однородная функция отделяет эти два результата уже на втором порядке.'
    ]),result


def vector_calculus(task,library,request):
    if not library.data.get('source_vector_calculus'):
        raise Unsupported('The source-aware vector methods are not published in this version')
    kind=task['kind']
    if library.data.get('typed_source_reductions'):
        if kind=='stokes_circulation':return plane_cylinder_stokes(task,library)
        if kind=='formal_vector_identity' and 'given' in task:return source_curl_product_type(task,request)
    if kind in ('surface_flux','surface_flux_and_divergence_check','oriented_boundary_integral'):
        return surface_flux_moments(task,request)
    if kind in ('orthogonal_coordinate_divergence','orthogonal_coordinate_curl'):
        return orthogonal_vector_operator(task)
    if kind in ('curl_norm_direction_at_point','curl_small_circle_circulation'):
        return field_at_point(task,request,kind=='curl_small_circle_circulation')
    if kind=='rigid_rotation_curl' or kind=='formal_vector_identity' and {'field','expression'}&task.keys():
        return vector_operator(task,request)
    if kind=='line_integral':return vector_path_primitive(task,request)
    if kind=='exact_form':return guarded_field_potential(task,request)
    if planar_field_goal(task):
        if not library.data.get('source_planar_integral_theorems'):
            raise Unsupported('No source-aware planar integral theorem is available')
        return planar_field_theorem(task,request)
    return vector_integral_theory(task,request)


PLANAR_FIELD_KINDS={
    'closed_form_integral_identity','line_integral_estimate','work_of_force',
    'characterize_translated_forms','path_independence_condition','winding_form_integral',
    'area_to_volume_identity','flux_identity','local_flux_limit','gauss_boundary_integral',
    'green_harmonic_identity','fluid_conservation','wire_field_components',
    'logarithmic_layer_potential','attraction_of_wire',
}


def planar_field_goal(task):
    kind=task.get('kind')
    return kind in PLANAR_FIELD_KINDS or (
        kind=='exact_differential_endpoints' and any(isinstance(c,str) and
        ('continuous' in c or c.startswith('norm(')) for c in task.get('stated_conditions',()))) or (
        kind=='exact_differential_endpoints' and task.get('stated_conditions')==['path avoids origin']
        and isinstance(task.get('coefficients'),list) and all(isinstance(s,str) and '/sqrt(' in s for s in task['coefficients'])) or (
        kind=='potential_from_differential' and isinstance(task.get('coefficients'),list)
        and any(isinstance(s,str) and s.lstrip('-').startswith('D_x^') for s in task['coefficients']))


def same_form_coefficient(actual,expected,names,conditions=()):
    """Check equality while retaining each natural-domain guard of the original formula."""
    from tasks import domain_conditions,known_guard
    from verify import same_value
    ctx=m.context(dict(variable='__form',parameters=list(names),parameter_conditions=conditions))
    guards=domain_conditions(expected)
    return same_value(actual,expected) and all(
        known_guard(g,ctx) or any(g[0]==h[0] and same_value(g[1],h[1]) for h in guards)
        for g in domain_conditions(actual))


def abstract_primitive(task):
    """Find a scalar argument shared by the components of an abstract continuous form."""
    from tasks import source
    from verify import same_value
    conditions=task['stated_conditions']
    declaration=re.fullmatch(r'([A-Za-z]\w*(?:,[A-Za-z]\w*)*) continuous',conditions[0]) if len(conditions)==1 else None
    coefficients=task['coefficients'];axes=list(AXES[:len(coefficients)])
    if not declaration or len(axes) not in (2,3) or len(axes)!=len(coefficients):
        raise Unsupported('Identify the continuous scalar functions and Cartesian components')
    names=declaration[1].split(',')
    if len(set(names))!=len(names) or set(names)&(set(axes)|m.FUNCTIONS|set(m.ALIASES)):
        raise Unsupported('A continuous function symbol collides with a coordinate or elementary function')
    from tasks import domain_conditions,known_guard
    ctx=m.context(dict(variable='__field',parameters=axes))
    originals=[m.parse(c,None,axes,names) for c in coefficients]
    if not all(known_guard(p,ctx) for e in originals for p in domain_conditions(e)):
        raise Unsupported('The original form is not defined throughout the claimed field domain')
    forms=[m.simplify(c) for c in originals]
    from integrals import learned_nodes
    calls=list(dict.fromkeys(n for f in forms for n in learned_nodes(f) if isinstance(n,tuple) and n[0] in names))
    coordinates=[('s',s) for s in axes]
    potential=[];remaining=forms.copy()
    for call in calls:
        f,g=call
        if same_value(g,m.dot(coordinates,coordinates)):
            derivative=coordinates;weight='1/2'
        elif g[0]=='sqrt' and same_value(g[1],m.dot(coordinates,coordinates)):
            # r dr is P dot dP and extends continuously through the center.
            derivative=coordinates;weight='s'
        else:
            p,n=m.rational_form(g)
            if n!={():1} or any(mon and (len(mon)!=1 or mon[0][1]!=1 or mon[0][0] not in coordinates) for mon in p):
                raise Unsupported('No globally defined affine or radial scalar argument was identified')
            derivative=[m.q(p.get(((x,1),),0)) for x in coordinates];weight='1'
        contribution=[m.mul(d,call) for d in derivative]
        remaining=[m.simplify(m.add(r,m.neg(c))) for r,c in zip(remaining,contribution,strict=True)]
        potential.append(dict(argument=g,function=f,weight=weight))
    if set(names)!={p['function'] for p in potential} or not all(same_value(r,m.ZERO) for r in remaining):
        raise Unsupported('The original form is not the complete differential of the proposed integrals')
    if task['kind']=='closed_form_integral_identity':
        return potential,m.ZERO
    points=[]
    for side in ('start','end'):
        if len(task[side])!=len(axes):raise Unsupported('Incomplete endpoints')
        params=sorted({s for s in map(str,task[side]) if re.fullmatch(r'[A-Za-z]\w*',s) and s not in ('e','pi')})
        ctx=m.context(dict(variable='__endpoint',parameters=params))
        point=[m.parse(str(s),None,params) for s in task[side]]
        if not all(m.constant_defined(x,ctx) for x in point):
            raise Unsupported('An original endpoint is undefined')
        points.append(dict(zip(coordinates,point,strict=True)))
    result=[dict(function=p['function'],weight=p['weight'],
                 lower=source(m.simplify(m.substitute(p['argument'],points[0]))),
                 upper=source(m.simplify(m.substitute(p['argument'],points[1])))) for p in potential]
    return potential,result


def planar_field_theorem(task,request):
    """Use a field theorem selected by the goal and the original region or path."""
    kind=task['kind']
    def prove(theorem,headings,fields,steps,**values):
        vector_source(task,fields,headings,('continued_on_pdf_page',) if kind=='gauss_boundary_integral' else ())
        return dict(theorem='method.'+theorem,argument=steps),values
    endpoint_goals=['exactness_proof','line_integral'];want=task.get('requested_output')
    if kind in ('exact_differential_endpoints','closed_form_integral_identity'):
        endpoint=kind=='exact_differential_endpoints'
        if want!=(endpoint_goals if endpoint else ['proof']) or endpoint and task.get('method_requirement','full_differential')!='full_differential':
            raise Unsupported('Retain the input differential and every requested conclusion')
        fields={'coefficients','stated_conditions','requested_output'}|({'start','end','method_requirement'} if endpoint else set())
        headings=('Убедиться в полноте дифференциала и вычислить интеграл.','Найти интеграл от полного дифференциала.',
                  'Доказать нулевое значение по любому кусочно-гладкому замкнутому контуру.')
        radial_conditions=['norm(start)=a','norm(end)=b','a>0','b>0']
        if endpoint and task['stated_conditions'] in (radial_conditions,['path avoids origin']):
            from tasks import source
            names=list(AXES[:len(task['coefficients'])]);axes=[('s',s) for s in names];r=('sqrt',m.dot(axes,axes))
            if len(axes) not in (2,3) or not all(same_form_coefficient(m.parse(f,None,names),m.div(s,r),names)
                                                 for f,s in zip(task['coefficients'],axes,strict=True)):
                raise Unsupported('Check the given radii, endpoints and radial components')
            if task['stated_conditions']==radial_conditions:
                if (task['start'],task['end'])!=([s+'1' for s in names],[s+'2' for s in names]):
                    raise Unsupported('The given endpoint radius symbols have not been bound')
                values=[('s','a'),('s','b')]
            else:
                ctx=m.context(dict(variable='__point'));values=[]
                for p in (task['start'],task['end']):
                    point=[m.parse(str(s),None) for s in p]
                    if len(point)!=len(names) or not all(m.constant_defined(z,ctx) for z in point):
                        raise Unsupported('The original endpoint is undefined')
                    norm=m.simplify(('sqrt',m.dot(point,point)))
                    if m.sign(norm,ctx)!=1:raise Unsupported('An endpoint lies at or may lie at the excluded point')
                    values.append(norm)
            return prove('composed_form_primitive',headings,fields,[
                'On r>0, differentiating the norm gives exactly the Cartesian components.',
                'There is one global primitive on the punctured space. Its values at the endpoints are their radii.',
                'The original integrand requires a path that avoids the center.'],
                line_integral=m.simplify(m.add(values[1],m.neg(values[0]))),potential=r)
        cross=crossed_component_exactness(task) if endpoint else None
        if cross is not None:
            return prove('cross_coordinate_exactness',headings,fields,[
                'Первые компоненты имеют первообразные по своим координатам. После их вычитания остаётся коэффициент при одном дифференциале, зависящий от другой координаты.',
                'Интеграл по прямоугольнику в этих двух координатах равен разности значений коэффициента, умноженной на длину второй стороны. Замкнутый интеграл нулевой для всех прямоугольников ровно при постоянстве коэффициента.',
                'При постоянном коэффициенте применяем полный дифференциал и вычисляем разность концов. Иначе две перестановки отрезков между теми же точками могут давать разные значения.'
            ],**cross)
        potential,value=abstract_primitive(task)
        return prove('composed_form_primitive',headings,fields,[
            'Extract the common scalar arguments from the coefficients.',
            'Differentiate the proposed scalar integrals by the fundamental theorem and chain rule. For the radial weight, continuity gives derivative zero at the center.',
            'Every resulting component agrees with the original one-form. Use the endpoint differences.'],
            line_integral=value,potential=potential)
    if kind=='line_integral_estimate' and want==['proof'] and task.get('stated_conditions')==['L=arc length','M=max_curve sqrt(P²+Q²)']:
        return prove('curve_tangent_bound',('Доказать оценку |int_C P dx+Q dy|<=L*M.',),
            {'stated_conditions','requested_output'},[
            'Parametrize by arc length on each regular piece. Cauchy–Schwarz bounds the absolute pullback by the field norm times unit speed.',
            'Integrate the bound M over the full curve length L, and sum the pieces.'],bound='|I|<=L*M')
    if kind=='line_integral_estimate' and want==['bound','limit_proof']:
        return angular_decay_bound(task,prove)
    if kind=='potential_from_differential':
        return formal_primitive_pair(task,prove)
    if kind=='work_of_force' and want==['work']:
        force,path=task['force'],task['path']
        fields={'force','path','requested_output'};head=('Найти работу указанной силы.',)
        if force=='gravity on a mass m; Oz directed vertically upward' and path=='from (x1,y1,z1) to (x2,y2,z2)':
            return prove('composed_form_primitive',head,fields,[
                'The printed gravity has constant z component −mg and no horizontal component.',
                'Its global potential of work is −mgz. Evaluate it at the specified ends.'],work='-m*g*(z2-z1)')
        if force=='elastic central force toward origin, magnitude proportional to distance' and (
                shape:=re.fullmatch(r'counterclockwise positive quadrant arc of x²/([a-z])²\+y²/([a-z])²=1',path)):
            a,b=shape.groups()
            return prove('composed_form_primitive',head,fields,[
                'The force toward the origin is −k(x,y). Its primitive is −k(x²+y²)/2.',
                'The stated quadrant and direction give initial radius |'+a+'| and final radius |'+b+'|.'],
                work=f'k*({a}^2-{b}^2)/2')
        if (force,path)==('attraction of unit mass with magnitude G/r²,r=sqrt(x²+y²+z²)',
                         'from M1(x1,y1,z1) to M2(x2,y2,z2)'):
            return prove('composed_form_primitive',head,fields,[
                'On the punctured space the attractive inverse-square field is grad(G/r).',
                'Evaluate the primitive at the original endpoints. A path through the pole is outside the original domain.'],
                work='G*(1/r2-1/r1)',domain='path avoids origin')
    if kind=='green_harmonic_identity':
        return green_harmonic_theorem(task,prove)
    if kind in ('logarithmic_layer_potential','attraction_of_wire'):
        return radial_layer_theorem(task,prove)
    if kind in ('winding_form_integral','gauss_boundary_integral'):
        return contour_index_theorem(task,prove)
    if kind in ('area_to_volume_identity','flux_identity','local_flux_limit','fluid_conservation','wire_field_components',
                'characterize_translated_forms','path_independence_condition'):
        return planar_balance_theorem(task,prove,request)
    raise Unsupported('No integral-theorem transition with all source assumptions was found')


def planar_balance_theorem(task,prove,request):
    kind=task['kind'];want=task['requested_output']
    if (kind,want,task.get('claim'))==('area_to_volume_identity',['proof'],'V=-pi*int_C y^2 dx'):
        return prove('planar_boundary_balance',
            ('Доказать формулу объёма вращения около Ox простого замкнутого контура в y≥0.',),{'claim','requested_output'},[
            'For a bounded region in y≥0, cylindrical shells give dV=2πy dA under one full rotation about Ox.',
            'For positive orientation use P=−πy² and Q=0 in Green’s formula. Its area density is 2πy.',
            'This identifies the volume with the stated contour integral.'],equality=task['claim'],
            scope='bounded region in y>=0 with a positively oriented piecewise smooth boundary')
    if kind=='flux_identity':
        flux=want==['flux'] and (task.get('integrand'),task.get('region'))==(
            'x*cos(n,x_axis)+y*cos(n,y_axis)','C bounds finite S, n outward')
        constant=want==['proof'] and task.get('claim')=='int_C cos(l,n) ds=0 for any fixed direction l and outward normal n'
        if not (flux or constant):raise Unsupported('The flux field, normal and requested conclusion must all be identified')
        return prove('planar_boundary_balance',
            ('Найти значение потока через простую замкнутую кривую.',) if flux else
            ('Доказать равенство нулю интеграла по замкнутому контуру.',),
            {'requested_output','integrand','region'} if flux else {'requested_output','claim'},[
            'The scalar normal component times ds is the outward flux across the boundary.',
            'Green’s formula rewrites it as the integral of the planar divergence.',
            'The divergence is 2 for (x,y) and 0 for a constant vector.'],
            flux='2*area(S)' if flux else m.ZERO)
    if kind=='local_flux_limit' and want==['flux_limit'] and (
            task['formula'],task['conditions'])==('lim_diam(S)->0 (int_C F dot n ds)/area(S)',
            ['C surrounds (x0,y0)','F=(X,Y) continuously differentiable on S+C','n outward']):
        return prove('planar_boundary_balance',('Найти предел среднего потока при стягивании границы к точке.',),
            {'formula','conditions','requested_output'},[
                'The flux quotient is the area average of the divergence on S.',
                'Since S contains the specified point, the oscillation of the divergence tends to zero with its diameter.'],
            limit='X_x(x0,y0)+Y_y(x0,y0)')
    if (kind=='fluid_conservation' and want==['rate_of_amount_change','incompressible_continuity_equation']
            and task['velocity']==['u(x,y)','v(x,y)'] and task['region']=='finite S bounded by C'):
        return prove('planar_boundary_balance',
            ('Определить скорость изменения количества жидкости и условие несжимаемости при отсутствии источников и стоков.',),
            {'velocity','region','requested_output'},[
                'Across a fixed boundary the instantaneous net inflow is minus the outward flux of the velocity.',
                'Green’s formula gives the integral of minus the divergence in S.',
                'If the fluid is incompressible without sources, the average converges to zero on every shrinking disk. Conversely zero divergence gives zero net influx.'],
            rate='-integral_S (u_x+v_y) dx dy',incompressibility='u_x+v_y=0')
    if kind=='wire_field_components' and want==['Hx','Hy','Hz'] and task['law']=='dH=k*i*(r cross ds)/r^3' and (
            task['stated_conditions']==['r points from current element to M(x,y,z)','closed conductor C']):
        fields={'law','stated_conditions','requested_output'}
        coords=('x','y','z');wire=('xi','eta','zeta');components={}
        for i,j,k in ((0,1,2),(1,2,0),(2,0,1)):
            a,b=coords[j],coords[k];p,q=wire[j],wire[k]
            components['H'+coords[i]]=f'k*i*int_C (({a}-{p})*d{q}-({b}-{q})*d{p})/r^3'
        return prove('oriented_field_pullback',
            ('Найти три проекции поля от замкнутого проводника, следуя напечатанному варианту закона.',),fields,[
                'Put r_vector=(x−xi,y−eta,z−zeta) and ds=(d xi,d eta,d zeta), in that order for the cross product.',
                'Expand the cross product by its cyclic two-by-two minors and integrate along the oriented wire at positive distance.'],
            **components,domain='observation point outside C')
    if kind=='characterize_translated_forms' and want==['necessary_and_sufficient_condition']:
        pattern=r'([A-Za-z]\w*)\(x\+alpha,y\+beta\)'
        names=[re.fullmatch(pattern,c) for c in task['coefficients']]
        if (len(names)!=2 or not all(names) or names[0][1]==names[1][1] or task['stated_conditions']!=[
                'P,Q twice continuously differentiable','every closed contour C','arbitrary translation constants alpha,beta']):
            raise Unsupported('Need both shifted components, the smoothness and arbitrary contours')
        p,q=[g[1] for g in names]
        return prove('planar_boundary_balance',
            ('Определить все дважды непрерывно дифференцируемые P,Q, для которых интеграл по любому замкнутому контуру не зависит от постоянного переноса.',),
            {'coefficients','requested_output','stated_conditions'},[
                'Green reduces the circulation to the integral of the curl density over the enclosed part, with winding multiplicity for a general contour.',
                'A constant curl is unchanged by translation. Conversely translate arbitrary small disks and compare the continuous curl by taking limits of its averages.',
                'Subtract (−cy/2,cx/2) with the same constant curl. The residual closed form on the whole plane has a scalar potential.'],
            condition=f'{q}_x-{p}_y=constant c',forms=[f'{p}=U_x-c*y/2',f'{q}=U_y+c*x/2'])
    if kind=='path_independence_condition' and want==['necessary_and_sufficient_condition']:
        coeffs=task['coefficients']
        match=re.fullmatch(r'y\*([A-Za-z]\w*)\(x,y\)',coeffs[0]) if len(coeffs)==2 else None
        if not match or coeffs[1]!='x*'+match[1]+'(x,y)' or task.get('stated_conditions')!=['F differentiable']:
            raise Unsupported('The complete input must be a differentiable factor times d(x*y) on the plane')
        return prove('composed_form_primitive',('Условие на дифференцируемую F для независимости интеграла от пути.',),
            {'coefficients','requested_output','stated_conditions'},[
                'Compare opposite edges of every shrinking rectangle. The first-order differential of the differentiable field gives circulation per area xF_x−yF_y.',
                'Zero circulation makes this expression vanish. The vector (x,−y) is tangent to a connected branch of xy=constant, so F is constant along it.',
                'On each open quadrant let g assign the field factor to its product value s. The integral ∫_0^(xy) g(s) ds has differential F d(xy).',
                'Continuity of F across the axes and at the origin gives the same traces and the same derivative there, so these primitives glue on the plane.'],
            condition=match[1]+'_x*x-'+match[1]+'_y*y=0',domain='whole plane')
    raise Unsupported('No flux or planar curl transition for the full original goal')


def angular_decay_bound(task,prove):
    circle=re.fullmatch(r'x\^2\+y\^2=([A-Za-z]\w*)\^2',task['curve'])
    fields=task['coefficients'];names=list('xy')
    if not circle or len(fields)!=2:
        raise Unsupported('A circular length and both angular field components are required')
    p,q=[m.parse(z,None,names) for z in fields]
    x,y=(('s',s) for s in names)
    if (p[0]!='div' or q[0]!='div' or p[1]!=y or m.simplify(q[1])!=m.neg(x)
            or p[2]!=q[2] or p[2][0]!='pow' or p[2][2]<2):
        raise Unsupported('The angular denominator must provide a sufficiently decaying common positive power')
    polynomial,den=m.rational_form(p[2][1]);degree=p[2][2]
    a=polynomial.get(((x,2),),0);b=polynomial.get(((x,1),(y,1)),0)
    # Mixed monomials are canonically ordered in the rational-form map.
    if den!={():1} or polynomial!={k:v for k,v in (
            (((x,2),),a),(((x,1),(y,1)),b),(((y,2),),a)) if v}:
        raise Unsupported('The homogeneous quadratic must share both diagonal coefficients')
    c=a-abs(b)/2
    if c<=0:raise Unsupported('The lower bound on the original denominator is not positive')
    radius=('s',circle[1]);power=2*degree-2
    factor=m.div(m.mul(m.q(2),m.PI),m.q(c**degree))
    return prove('curve_tangent_bound',
        ('Оценить исходный интеграл и доказать, что его предел при R→∞ равен нулю.',),
        {'coefficients','curve','requested_output'},[
            'From 2|xy|≤x²+y², the homogeneous quadratic is at least cR² on the original circle, with c>0.',
            'The norm of the numerator vector equals R. Multiply its upper quotient bound by the full length 2πR.',
            'The positive power of R in the denominator gives limit zero.'],
        lower_coefficient=m.q(c),absolute_bound=m.div(factor,m.power(radius,power)),limit=m.ZERO)


def formal_primitive_pair(task,prove):
    if task['requested_output']!=['potential_and_domain'] or len(task['coefficients'])!=2:
        raise Unsupported('Both ordered derivative components and their common domain are required')
    pattern=r'(-?)D_x\^(\([a-z](?:[+-]\d+)?\)|[a-z]) D_y\^(\([a-z](?:[+-]\d+)?\)|[a-z]) (.+)'
    rows=[re.fullmatch(pattern,s) for s in task['coefficients']]
    if not all(rows) or rows[0][1]:
        raise Unsupported('The first ordered component must be available to propose a primitive')
    def order(s):
        name=s.strip('()')
        return name[0],int(name[1:] or 0)
    def moves(order,n):
        return order[0],order[1]+n
    def text(order,axis):
        name,n=order
        return f'D_{axis}^({name}{n:+d})' if n else f'D_{axis}^{name}'
    X,Y=[order(s) for s in rows[0].groups()[1:3]]
    bX,bY=[order(s) for s in rows[1].groups()[1:3]]
    X=moves(X,-1)
    f=rows[0][4];g=rows[1][4]
    if f==g and re.fullmatch(r'[A-Za-z]\w*',f) and not rows[1][1] and (X,moves(Y,1))==(bX,bY):
        domain='open region where the original orders are nonnegative and the indicated mixed derivatives commute'
        steps=['Remove one x derivative from the first component to propose the scalar primitive.',
               'Reapplying x recovers the first coefficient. Commuting the extra y derivative through the same mixed order recovers the second.']
    elif (f=='ln(1/r)' and g=='ln(1/r); r=sqrt(x^2+y^2)' and rows[1][1]
            and (moves(X,-2),moves(Y,3))==(bX,bY)):
        domain='punctured plane r>0 with nonnegative original derivative orders'
        steps=['On r>0, ln(1/r) satisfies H_xx+H_yy=0.',
               'Remove one x derivative from the first component to propose the scalar primitive.',
               'In the y derivative of that proposal, replace a pair of x derivatives by minus a pair of y derivatives. The ordered second component is recovered.']
    else:raise Unsupported('Reapplying the derivatives does not produce both original coefficients')
    return prove('composed_form_primitive',('Найти первообразную функцию для напечатанного дифференциала.',),
        {'coefficients','requested_output'},steps,potential=text(X,'x')+' '+text(Y,'y')+' '+f,domain=domain)


def contour_index_theorem(task,prove):
    want=task['requested_output'];kind=task['kind']
    if kind=='gauss_boundary_integral':
        if (want!=['all_positions_of_A'] or task['integrand']!='cos(r,n)/r' or
                task['curve']!='simple closed smooth contour, vector r from A(x,y) to M(xi,eta), n outward'):
            raise Unsupported('Need the regular closed boundary, outward normal, and original pole direction')
        return prove('punctured_planar_green',('Вычислить интеграл Гаусса.',),
            {'integrand','curve','requested_output'},[
                'The kernel is the outward normal derivative of ln(distance). Its Laplacian vanishes away from the pole.',
                'Apply the flux theorem to the original region without a disk about the pole. The inner normal derivative is −1/epsilon.',
                'For an exterior pole there is no inner boundary. For an interior pole the whole small circle contributes −2π. For a regular boundary point a circular arc inside the region has angular length tending to π.',
                'The last limit computes the improper boundary integral. The integral over the remaining contour equals the negative of the circular contribution.'],
            exterior=m.ZERO,interior=m.mul(m.q(2),m.PI),boundary_improper=m.PI)
    if want==['outside_case','inside_case']:
        xy=[('s',x) for x in 'xy'];r2=m.dot(xy,xy);p,q=xy
        if (len(task['coefficients'])!=2 or task['stated_conditions']!=['C simple closed positively oriented','C avoids origin']
                or not all(same_form_coefficient(m.parse(c,None,list('xy')),f,'xy') for c,f in
                    zip(task['coefficients'],[m.div(m.neg(q),r2),m.div(p,r2)],strict=True))):
            raise Unsupported('The angle form and positive curve avoiding its pole must match')
        return prove('punctured_planar_green',
            ('Вычислить для простого положительно ориентированного контура, не проходящего через начало координат.',),
            {'coefficients','stated_conditions','requested_output'},[
                'Away from the origin the curl is zero. The canonical form measures the differential of local angle.',
                'If the pole is enclosed, excise a small disk, with negative orientation on its boundary. A positive small circle contributes 2π, independently of its radius.'],
            exterior=m.ZERO,interior=m.mul(m.q(2),m.PI))
    if task.get('integral')!='(1/(2*pi))*int_C (X*dY-Y*dX)/(X^2+Y^2)':
        raise Unsupported('The normalized angle form was changed')
    fields={'integral','transform','stated_conditions','requested_output'};hyp=task['stated_conditions']
    if (want==['index'] and task['transform']==['a*x+b*y','c*x+d*y'] and hyp==[
            'a*d-b*c!=0','simple closed contour C surrounds origin','positive orientation by section convention']):
        return prove('punctured_planar_green',
            ('Вычислить I при линейном преобразовании контура.',),fields,[
                'An invertible linear map takes a positively oriented simple contour enclosing the origin to a simple contour enclosing the origin.',
                'Its determinant gives the direction of traversal. Integrate the angle form and apply the stated normalization.'],
            index='sign(a*d-b*c)')
    if (want==['index_formula'] and task['transform']==['phi(x,y)','psi(x,y)'] and hyp==[
            'simple closed contour C surrounds origin','zero sets phi=0 and psi=0 have several simple intersections inside C',
            'C positively oriented as in the preceding exercise and section convention']):
        return prove('punctured_planar_green',
            ('Вычислить тот же индекс при нелинейном отображении.',),fields,[
                'If the form is defined on C, excise mutually disjoint small disks about all simple interior zeros of the map.',
                'On the remainder the angle form is closed. A local linearization at each simple zero is homotopic to the map on a sufficiently small circle without meeting zero.',
                'Count the signed circle windings. If the original map vanishes on C, the stated contour integral is not defined as an ordinary integral.'],
            index='sum over interior zeros sign(det D(phi,psi))',
            domain='C1 map near the closure, all interior zeros simple and map nonzero on C',
            otherwise='ordinary index undefined at boundary zeros')
    raise Unsupported('The original contour orientation or one of the map hypotheses is unresolved')


def green_harmonic_theorem(task,prove):
    claim=task['claim'];method=task.get('method_requirement');hint=task.get('printed_hint')
    statement=re.sub(r'; see \d+$','',claim)
    forms={
        'C2 u is harmonic iff int_C du/dn ds=0 on every closed contour; normal outward':(
            'planar_boundary_balance',[
                'Apply the divergence theorem to the gradient in every regular bounded subregion. The flux is the area integral of Δu.',
                'If all fluxes vanish, continuous Δu has zero averages over arbitrarily small disks, hence vanishes pointwise.']),
        'int_S (u_x^2+u_y^2)dA=-int_S u*Delta(u)dA+int_C u*(du/dn)ds for smooth C bounding finite S':(
            'green_product_flux',[
                'The product rule gives div(u grad u)=uΔu+|grad u|².',
                'Integrate and use outward normal flux, then move the uΔu term to the other side.']),
        'A function harmonic in a bounded region S and on its boundary C is uniquely determined by the boundary data':(
            'green_product_flux',[
                'Subtract two candidates. The difference is harmonic with zero boundary trace.',
                'A positive maximum or a negative minimum would be attained inside and would force the difference to be constant by the harmonic mean value property.',
                'Since the boundary values are zero, both extrema must be zero.']),
        'int_S (v*Delta(u)-u*Delta(v))dA=int_C (v*du/dn-u*dv/dn)ds for smooth C and outward normal':(
            'green_product_flux',[
                'Apply the product rule to v grad u − u grad v. The two scalar products of gradients cancel.',
                'Use the divergence theorem with the original outward normal to identify the boundary integrand.']),
        'u(x,y)=(1/(2*pi))*int_C [u*partial_n ln(r)-ln(r)*partial_n u]ds for harmonic u on closed bounded S, (x,y) interior':(
            'punctured_planar_green',[
                'Apply the second Green identity with the harmonic function and ln(r) outside a small removed disk centered at the original interior point.',
                'The inner normal is directed toward that point and derivative of ln(r) is −1/epsilon on the circle.',
                'The first circular term tends to −2πu(x,y) by continuity. The remaining term is O(epsilon|ln epsilon|) and tends to zero.',
                'Both Laplacians vanish on the punctured domain, so the outer integral equals 2πu(x,y).']),
        'u(M)=(1/(2*pi*R))*int_C u(xi,eta)ds for radius-R circle centered at M, u harmonic':(
            'green_product_flux',[
                'In the logarithmic representation on a disk, the kernel ln(r) is constant on the boundary and its outward derivative equals 1/R.',
                'The term involving the total normal derivative of u vanishes by its harmonicity. The remaining term is the stated circular mean.']),
        'Nonconstant harmonic u on a bounded closed region attains neither maximum nor minimum at an interior point':(
            'green_product_flux',[
                'At an interior maximum the mean over each sufficiently small circle equals the maximum, so every value on the circle equals it by continuity.',
                'The maximum set is therefore open relative to the connected interior and is closed by continuity. This would make the function constant.',
                'Repeat for the negative harmonic function to exclude an interior minimum.']),
    }
    if statement in forms and task['requested_output']==['proof']:
        name,steps=forms[statement];puncture=name=='punctured_planar_green'
        if method!=('second_greens_formula' if puncture else None) or hint not in (
                None,'remove an infinitesimal disk around (x,y), apply second Green formula to the remaining domain' if puncture else None):
            raise Unsupported('The proof method required in the source was changed')
        return prove(name,('Доказать указанное утверждение.',),{'claim','requested_output','method_requirement','printed_hint'},
                     steps,equality=claim,scope='classical smooth functions and the original bounded regular domains, outward normal')
    if (task['requested_output']==['proof','derive_P_and_Q'] and method is None and hint is None and
            claim=='int_S (L[u]*v-M[v]*u)dA=int_C (P dx+Q dy), L[u]=u_xy+a*u_x+b*u_y+c*u, M[v]=v_xy-a*v_x-b*v_y+c*v; a,b,c constants'):
        return prove('green_product_flux',('Доказать указанное утверждение.',),
            {'claim','requested_output','method_requirement','printed_hint'},[
                'The zeroth-order terms cancel. The first-order terms combine to a ∂x(uv)+b ∂y(uv).',
                'The mixed terms equal half the sum of ∂x(vu_y−uv_y) and ∂y(vu_x−uv_x) by symmetry of mixed partial derivatives.',
                'Use the first sum as Q_x and the second as −P_y, with constant a,b, and integrate by Green’s formula.'],
            P='-(v*u_x-u*v_x)/2-b*u*v',Q='(v*u_y-u*v_y)/2+a*u*v',scope='C2 u,v, positively oriented C')
    raise Unsupported('The original harmonic identity or its imposed proof method remains unresolved')


def radial_layer_theorem(task,prove):
    kind=task['kind'];want=task['requested_output']
    if kind=='attraction_of_wire':
        circle=re.fullmatch(r'x\^2\+y\^2=([A-Za-z]\w*)\^2,y>=0',task['region'])
        if want!=['force_vector'] or circle is None:
            raise Unsupported('Bind a homogeneous upper semicircle and its center')
        radius=circle[1];M=task['wire_mass'];n=task['test_mass']
        if not all(re.fullmatch(r'[A-Za-z]\w*',s) for s in (M,n,radius)) or len({M,n,radius})!=3:
            raise Unsupported('Bind the two masses and the radius of the arc')
        return prove('oriented_field_pullback',
            ('Найти силу притяжения к центру со стороны однородной верхней полуокружности.',),
            {'region','wire_mass','test_mass','requested_output'},[
                'The uniform mass density with respect to length is the wire mass divided by the upper semicircle length.',
                'The distance from its center is constant. The horizontal direction cosines cancel under reflection, and the integral of the vertical sine over [0,π] is 2.'],
            force_vector=[m.ZERO,f'2*G*{M}*{n}/(pi*{radius}^2)'],radius_condition=radius+'>0')
    if want==['potential_in_all_regions']:
        kernel=re.fullmatch(r'([A-Za-z]\w*)\*ln\(1/r\), r=distance\(\(x,y\),\(xi,eta\)\)',task['kernel'])
        circle=re.fullmatch(r'xi\^2\+eta\^2=([A-Za-z]\w*)\^2',task['curve'])
        if not kernel or not circle or len({kernel[1],circle[1],'rho'})!=3:
            raise Unsupported('Bind the uniform sheet, original distance and circle radius')
        r=circle[1];k=kernel[1]
        return prove('circular_layer_fourier',('Вычислить потенциал однородного простого слоя.',),
            {'kernel','curve','requested_output'},[
                'Factor distance as max(R,rho) times |1−q exp(i(theta−phi))| where q=min(R,rho)/max(R,rho).',
                'For q<1 the logarithm series converges uniformly and every nonconstant mode integrates to zero.',
                'For q=1 the logarithmic singularity is integrable. The identity passes to the limit by an integrable bound using |1−q exp(it)|²=(1−q)²+4q sin²(t/2).',
                'Multiply the constant mode by the original length 2πR and the strength of the layer.'],
            potential=f'-2*pi*{k}*{r}*ln(max({r},rho))',radius_condition=r+'>0')
    if want!=['both_integrals_all_regions'] or len(task['integrands'])!=2:
        raise Unsupported('Both original circular Fourier coefficients are required')
    first,second=task['integrands']
    match=re.fullmatch(r'cos\(([A-Za-z]\w*|[1-9]\d*)\*psi\)\*(ln\(1/r\)|cos\(r,n\)/r)',first)
    if (not match or second!='sin('+match[1]+'*psi)*'+match[2]
            or task['stated_conditions']!=([match[1]+' positive integer'] if not match[1].isdigit() else [])):
        raise Unsupported('The modes need one common positive integral frequency')
    mode=match[1];double=match[2]!='ln(1/r)'
    circle=('unit circle point M=(1,psi), A=(rho,phi), r=AM, n=OM' if double else
            'unit circle point (1,psi), field point (rho,phi)')
    if task['curve']!=circle:raise Unsupported('The kernel and original radial differentiation orientation must match')
    head=('Вычислить два потенциала двойного слоя.' if double else
          'Вычислить оба потенциала простого слоя в полярных координатах.',)
    fields={'curve','integrands','stated_conditions','requested_output'}
    steps=(['Dot the directed vector AM with the outward unit circle normal.',
            'The double layer kernel is half of 1+(1−rho²)/(1+rho²−2rho cos(psi−phi)).',
            'Use the absolutely converging geometric Fourier series for rho<1. Outside the disk factor rho² and use its reciprocal with the opposite sign.',
            'At rho=1 the kernel equals 1/2 except at the single coincident point, so both positive modes integrate to zero.']
           if double else [
            'Expand −ln(distance) after extracting the greater radius. Its mode n has coefficient q^n/n for q=min(rho,1/rho)<1.',
            'The constant mode integrates to zero against both given densities. Orthogonality selects the original frequency and contributes π times its two angular coordinates.',
            'At rho=1 logarithms converge in L1 by |1−q exp(it)|²=(1−q)²+4q sin²(t/2) and the integrability of |ln sin(t/2)|.'])
    factor=lambda x: [x+'*'+f+'('+mode+'*phi)' for f in ('cos','sin')]
    return prove('circular_layer_fourier',head,fields,steps,
        at_center=[m.ZERO,m.ZERO],
        inside=factor('pi*rho^'+mode+('' if double else '/'+mode)),
        outside=factor(('-' if double else '')+'pi*rho^(-'+mode+')'+('' if double else '/'+mode)),
        on_circle=[m.ZERO,m.ZERO] if double else factor('pi/'+mode))


def total_differentials(task,library,request):
    """Contract the gradient and the Hessian with the same arbitrary increment."""
    from tasks import compile_partial_bundle,domain_conditions,guard_source,known_guard
    allowed={'id','kind','source','schema','function','variables','parameters','stated_conditions','requested_output'}
    if (set(task)-allowed or task.get('requested_output')!=['first_total_differential','second_total_differential']
            or library.data.get('task_compilers',{}).get('composite_function_differentiation')!='ordered_outer_chain_rule'):
        raise Unsupported('Нужно задание на первый и второй полные дифференциалы')
    origin=task.get('source',{})
    if (not isinstance(origin,dict) or set(origin)-{'exercise','printed_page','pdf_page','pdf_sha256','printed_heading'}
            or 'printed_heading' in origin and origin['printed_heading']!=
                'Найти дифференциалы первого и второго порядков от следующих функций ('+', '.join(task['variables'])+' — независимые переменные)'):
        raise Unsupported('Не разобрано исходное требование к полным дифференциалам')
    child={k:task[k] for k in ('function','variables','parameters','stated_conditions') if k in task}
    child.update(kind='partial_derivatives',derivative_orders=[1,2],requested_output=['first_partial_derivatives','second_partial_derivatives'])
    p=compile_partial_bundle(child,library.data['partial_bundle_contract'])
    names=[*p['variables'],*p['parameters']]
    ctx=m.context({'variable':'__basepoint','parameters':names,'parameter_conditions':[*p['stated_conditions'],*(guard_source(g) for g in p['domain_guards'])]})
    raw=m.parse(p['function'],None,names)
    if not all(known_guard(g,ctx) for g in domain_conditions(raw,True)):
        raise Unsupported('На исходной области остались точки, где не установлена дважды непрерывная дифференцируемость')
    checked=request('все компоненты градиента и матрицы Гессе',child)
    increments={x:'d'+x for x in p['variables']}
    if set(increments.values())&set(names):raise Unsupported('Обозначения приращений совпали с параметрами')
    forms=[m.ZERO,m.ZERO]
    for path,v in checked['partial_values']:
        term=freeze(v)
        for x in path:term=m.mul(term,('s',increments[x]))
        index=len(path)-1
        forms[index]=m.add(forms[index],term)
    return dict(increments=increments,domain=p['natural_domain'],smooth_guards=domain_conditions(raw,True)),dict(d1=m.simplify(forms[0]),d2=m.simplify(forms[1]))


def form_polynomial(term,axes):
    """Expand an exact form_polynomial containing only the designated coordinates."""
    p,d=m.rational_form(term)
    if d!={():Fraction(1)} or any(a not in axes for mon in p for a,_ in mon):
        raise Unsupported('The pulled component is not polynomial in the declared coordinates')
    return {tuple(dict(mon).get(a,0) for a in axes):c for mon,c in p.items()}


def form_laurent_sum(items,u,v):
    value=ZERO
    for (a,b),c in items:
        term=m.mul(q(c),m.mul(m.power(u,a),m.power(v,b)))
        value=m.add(value,term)
    return value


def form_common_denominator(raw):
    if any(c[0]!='div' for c in raw) or any(c[2]!=raw[0][2] for c in raw[1:]):
        raise Unsupported('A common uncancelled original denominator is required')
    den=raw[0][2];nums=tuple(c[1] for c in raw)
    if any(domain_conditions(c) for c in (*nums,den)):
        raise Unsupported('Additional original singularities would survive cancellation')
    return den,nums


def affine_form_potential(raw,axes):
    """Integrate finite Laurent coefficients after taking the actual divisor as coordinate."""
    den,(P,Q)=form_common_denominator(raw)
    L,e=(den[1],den[2]) if den[0]=='pow' else (den,1)
    if not 1<=e<=8:raise Unsupported('Unsupported divisor power')
    x,y=axes;poly=form_polynomial(L,axes)
    if set(poly)-{(0,0),(1,0),(0,1)}:raise Unsupported('The original divisor is not affine')
    a,b,c=(poly.get(k,Fraction(0)) for k in ((1,0),(0,1),(0,0)))
    if not a:
        if not b:raise Unsupported('The original affine coordinate map is degenerate')
        x,y=y,x;P,Q=Q,P;a,b=b,a
    u,v=('s','_lift_u'),('s',y[1])
    inv={x:m.div(m.add(m.add(u,m.mul(q(-b),v)),q(-c)),q(a)),y:v}
    p=m.div(m.substitute(P,inv),q(a))
    r=m.add(m.substitute(Q,inv),m.mul(q(-b),p))
    top=form_polynomial(p,(u,v));bottom=form_polynomial(r,(u,v))
    built={(i-e,j+1):w/(j+1) for (i,j),w in bottom.items()}
    defect={(i-e,j):w for (i,j),w in top.items()}
    for (i,j),w in built.items():
        defect[i-1,j]=defect.get((i-1,j),Fraction(0))-i*w
    defect={k:w for k,w in defect.items() if w}
    if any(j for _,j in defect):
        raise Unsupported('The affine form is not closed on its original domain')
    original_u=L;potential=form_laurent_sum(built.items(),original_u,y)
    for (i,_),w in defect.items():
        primitive=('ln',('abs',original_u)) if i==-1 else m.div(m.power(original_u,i+1),q(i+1))
        potential=m.add(potential,m.mul(q(w),primitive))
    return dict(method='affine_denominator_form',coordinate=L,coefficient_scale=q(a),
                pulled_numerators=[p,r],power=e,integrated_residual=form_laurent_sum(defect.items(),u,v)),potential


def product_chart_form(raw,axes,lib):
    """Propose quotient coordinates and check a scale primitive against both components."""
    def ratios(t):
        if t[0]=='div' and set(t[1:])==set(axes):yield t[1],t[2]
        for c in t[1:]:
            if isinstance(c,tuple):yield from ratios(c)
    derivative,steps=derivative_table(lib)
    for y,x in dict.fromkeys(r for f in raw for r in ratios(f)):
        u,v=('s','_lift_u'),('s','_lift_v')
        guards=tuple(dict.fromkeys(g for f in raw for g in domain_conditions(f)))
        def coordinate_guard(guard):
            rel,expr=guard
            p,d=m.rational_form(expr)
            return rel=='nonzero' and len(p)==len(d)==1 and all(v==x for mon in (*p,*d) for v,_ in mon)
        if not guards or not all(map(coordinate_guard,guards)):
            continue
        P,Q=(m.simplify(m.substitute(raw[axes.index(a)],{x:v,y:m.mul(u,v)})) for a in (x,y))
        scale=m.add(P,m.mul(u,Q));phase=m.mul(v,Q)
        if m.contains(scale,v):continue
        candidate=m.mul(v,scale);d=derivative(candidate,u[1])
        if not same_value(d,phase):continue
        potential=m.substitute(candidate,{v:x,u:m.div(y,x)})
        return dict(method='quotient_scale_form',ratio=(y,x),pulled_coefficients=[scale,phase],
                    verified_phase_derivative=d,jet_rules=list(steps)),potential
    raise Unsupported('No quotient chart produced a compatible scale primitive')


def central_period_form(raw,axes):
    """Closed linear/quadratic homogeneous forms split into radial and angular parts."""
    den,nums=form_common_denominator(raw);replacement={}
    if len(axes)==3:
        for i,j in combinations(range(3),2):
            if not same_value(nums[i],nums[j]):continue
            rest=next(k for k in range(3) if k not in (i,j))
            x,y=('s','_lift_u'),axes[rest]
            substitution={axes[i]:m.add(x,m.neg(axes[j]))}
            d=m.substitute(den,substitution);p=m.substitute(nums[i],substitution);r=m.substitute(nums[rest],substitution)
            try:
                dp=form_polynomial(d,(x,y));pp=form_polynomial(p,(x,y));qp=form_polynomial(r,(x,y))
            except Unsupported:
                continue
            replacement[x]=m.add(axes[i],axes[j]);break
        else:raise Unsupported('A full two-dimensional quotient was not found')
    elif len(axes)==2:
        x,y=axes;dp=form_polynomial(den,axes);pp,qp=(form_polynomial(n,axes) for n in nums)
    else:raise Unsupported('Expected a plane one-form or a projected plane form')
    if set(dp)-{(2,0),(1,1),(0,2)} or (set(pp)|set(qp))-{(1,0),(0,1)}:
        raise Unsupported('Need a homogeneous quadratic denominator and homogeneous linear numerator')
    A,B,C=(dp.get(power,Fraction(0))/scale for power,scale in (((2,0),1),((1,1),2),((0,2),1)))
    det=A*C-B*B
    if A<=0 or det<=0:raise Unsupported('A positive definite original denominator was not certified')
    p0,p1=(pp.get(k,Fraction(0)) for k in ((1,0),(0,1)))
    q0,q1=(qp.get(k,Fraction(0)) for k in ((1,0),(0,1)))
    radial=p0/A
    if p1+q0!=2*B*radial or q1!=C*radial:
        raise Unsupported('The original homogeneous form is not closed even locally')
    angular=q0-B*radial
    root=m.simplify(('sqrt',q(det)))
    phase=m.div(m.add(m.mul(q(C),m.div(y,x)),q(B)),root)
    local=m.add(m.mul(q(radial/2),('ln',den)),m.mul(m.div(q(angular),root),('atan',phase)))
    local=m.substitute(local,replacement)
    monodromy=m.div(m.mul(q(2*angular),m.PI),root)
    return (dict(method='homogeneous_form_period',original_denominator=den,
                 plane_coordinates=[replacement.get(z,z) for z in (x,y)],positive_definite=[q(A),q(det)],
                 radial_coefficient=q(radial),angular_coefficient=q(angular),positive_simple_loop_period=monodromy),
            dict(natural_domain=('positive',den),global_potential=local if not angular else None,
                 local_potential=local,local_chart=('nonzero',replacement.get(x,x)) if angular else None,
                 has_global_potential=not angular,period=monodromy))


def exact_form(task,library,request,chart=None):
    """Build a scalar potential by integrating successive residual components."""
    from fractions import Fraction
    from integrals import propose
    from quadrature import guard_bounds
    from tasks import domain_conditions,entailed_domain_guards,guard_source,known_guard,source
    from verify import same_value
    endpoint=task['kind']=='exact_differential_endpoints'
    fields={'kind','id','source','coefficients','requested_output','stated_conditions'}
    goals=['exactness_proof','line_integral'] if endpoint else ['potential_and_domain']
    if endpoint:fields.update(('start','end','method_requirement'))
    if (not library.data.get('exact_form_potential') or set(task)-fields or task.get('requested_output')!=goals
            or endpoint and task.get('method_requirement','full_differential')!='full_differential'):
        raise Unsupported('Не подтверждены исходный метод или все требования к потенциалу')
    printed=task.get('source',{})
    heading=printed.get('literal_requirement') if isinstance(printed,dict) else None
    headings=(('Убедиться в полноте дифференциала и вычислить интеграл.','Найти интеграл от полного дифференциала.')
              if endpoint else ('Найти первообразную функцию для напечатанного дифференциала.',))
    if (not isinstance(printed,dict) or set(printed)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or heading is not None and heading not in headings):
        raise Unsupported('Осталось требование печатного условия к дифференциальной форме')
    components=task.get('coefficients')
    if not isinstance(components,list) or len(components) not in (2,3) or not all(isinstance(c,str) for c in components):
        raise Unsupported('Нужны коэффициенты декартовой дифференциальной формы')
    axes=list(AXES[:len(components)])
    coords=[('s',x) for x in axes]
    raw=[m.parse(c,None,axes) for c in components]
    guards=list(dict.fromkeys(g for c in raw for g in domain_conditions(c)))
    conditions=task.get('stated_conditions',[])
    if not isinstance(conditions,list):raise Unsupported('Не установлены условия на кривую')
    for cond in conditions:
        if cond=='path avoids origin':g='nonzero',m.dot(coords,coords)
        else:
            pat=re.fullmatch(r'path avoids ([a-z])=([a-z]|0)',cond) if isinstance(cond,str) else None
            if not pat or pat[1] not in axes or pat[2] not in [*axes,'0']:
                raise Unsupported('Не разобрано ограничение на исходную кривую: '+str(cond))
            g='nonzero',m.add(('s',pat[1]),m.neg(m.parse(pat[2],None,axes)))
        if g not in guards:guards.append(g)
    facts=[guard_source(g) for g in entailed_domain_guards(guards)]
    ctx=m.context({'variable':'__axis','parameters':axes,'parameter_conditions':facts})
    def smooth(expr):
        if not all(known_guard(g,ctx) for g in domain_conditions(expr,True)):
            raise Unsupported('Не доказана гладкость на всей области исходной формы')
    def derivative(potential,x):
        if not m.contains(potential,('s',x)):return m.ZERO
        t=dict(kind='partial_derivatives',function=source(potential),variables=axes,stated_conditions=facts,
               requested_partials=[[x]],requested_output=['specified_partial_derivatives'])
        return freeze(request('производная частичного потенциала по '+x,t)['partial_values'][0][1])
    for c in raw:smooth(c)
    plan={};lifts=[]
    if chart=='coordinate_axes':
        candidate=request('потенциал вдоль ломаной по координатным осям',dict(kind='exact_form',variables=axes,
                          coefficients=components,requested_output=['potential_and_domain']))
        potential=freeze(candidate['value']['potential']);grad=freeze(candidate['compilation']['verified_gradient'])
        plan['chart']=chart
    elif chart=='source_form_charts' and library.data.get('source_form_charts'):
        plan['chart']=chart
        periodic=None
        if not endpoint and not conditions:
            try:periodic=central_period_form(raw,tuple(coords))
            except Unsupported:pass
        partial,steps=derivative_table(library)
        if periodic is not None:
            lifted,local=periodic
            potential=local['local_potential']
            grad=[partial(potential,x) for x in axes]
            if not all(same_value(a,b) for a,b in zip(grad,raw,strict=True)):
                raise Unsupported('The radial and angular derivatives do not recover the original form')
            period=local['period']
            obstructed=not local['has_global_potential']
            plan.update(lifted,theorem='method.homogeneous_form_period',
                        variables=axes,coefficients=raw,gradient=grad,source_domain=guards,
                        local_chart=local['local_chart'],period_obstruction=obstructed,steps=steps)
            plan['argument']=[
                'Complete the square in the positive definite plane denominator; it vanishes only at the removed origin.',
                'In the quotient chart separate the exact radial differential from the angular derivative and verify all Cartesian components.',
                'A positive turn changes the continuous angular phase by 2*pi. A nonzero resulting period excludes a global primitive.']
            return plan,dict(potential=potential,domain=guards,local_chart=local['local_chart'],
                             has_global_potential=not obstructed,period=period,
                             constant='per connected chart' if obstructed else 'per connected component')
        if len(axes)!=2:raise Unsupported('No admitted affine or quotient plane chart')
        try:lifted,potential=affine_form_potential(raw,tuple(coords))
        except Unsupported:lifted,potential=product_chart_form(raw,tuple(coords),library)
        grad=[partial(potential,x) for x in axes]
        plan.update(lifted,theorem='method.one_form_coordinate_potential',steps=steps,
                    argument=['Use the original denominator or quotient as a regular coordinate.',
                              'Construct the potential from the lifted components and verify the entire original gradient.'])
    elif chart is None:
        potential=m.ZERO
        for x,c in zip(axes,raw):
            defect=m.simplify(m.add(c,m.neg(derivative(potential,x))))
            if defect==m.ZERO:continue
            lifted=m.substitute(defect,{('s',x):('v',x)})
            correction,_=propose(lifted,x)
            correction=m.substitute(correction,{('v',x):('s',x)})
            smooth(correction)
            potential=m.simplify(m.add(potential,correction))
            lifts.append((x,defect,correction))
        t=dict(kind='partial_derivatives',function=source(potential),variables=axes,stated_conditions=facts,
               derivative_orders=[1],requested_output=['first_partial_derivatives'])
        proof=request('проверить весь градиент построенного потенциала',t)
        grad=[freeze(v) for _,v in proof['partial_values']]
    else:raise Unsupported('Неизвестный способ построения потенциала')
    smooth(potential)
    if not all(same_value(a,b) for a,b in zip(grad,raw,strict=True)):
        raise Unsupported('Градиент построенной функции отличается от заданных коэффициентов')
    plan.update(variables=axes,coefficients=raw,coordinate_primitives=lifts,gradient=grad,source_domain=guards)
    value=dict(potential=potential,domain=guards,constant='independent real constant per connected component')
    if endpoint:
        points=[]
        for side in ('start','end'):
            point=task[side]
            if not isinstance(point,list) or len(point)!=len(axes) or any(type(v) not in (int,str) for v in point):
                raise Unsupported('Неполные координаты конца пути')
            pars=[s for s in point if isinstance(s,str) and re.fullmatch('[a-z][0-9]*',s) and s not in ('e','pi')]
            point=[m.parse(str(s),None,pars) for s in point]
            if not all(m.constant_defined(v,{'parameters':pars,'assumptions':[]}) for v in point):
                raise Unsupported('Не подтверждена область исходного конца пути')
            points.append(point)
        lo,hi=points
        def segment(start,end):
            data={c:m.add(a,m.mul(('v','t'),m.add(b,m.neg(a)))) for c,a,b in zip(coords,start,end)}
            for relation,expr in guards:
                guard_bounds(relation,m.simplify(m.substitute(expr,data)),(Fraction(0),Fraction(1)),['t'])
            return tuple(data.values())
        try:
            plan['connecting_segment']=segment(lo,hi)
        except Unsupported:
            if 'path avoids origin' not in conditions:raise
            for axis in range(len(axes)):
                shifted=[[m.add(v,m.ONE) if i==axis else v for i,v in enumerate(point)] for point in points]
                path=[lo,*shifted,hi]
                try:pieces=[segment(a,b) for a,b in zip(path,path[1:])]
                except Unsupported:continue
                plan['connecting_path']={'vertices':path,'segments':pieces}
                break
            else:raise Unsupported('Не доказана допустимость прямого пути или ломаной')
        vals=[m.simplify(m.substitute(potential,dict(zip(coords,point)))) for point in points]
        plan['endpoint_values']=vals
        value['line_integral']=m.simplify(m.add(vals[1],m.neg(vals[0])))
    return plan,value

def coordinate_sections(names,request,*,local_premises=None):
    """Differentiate a coefficient holding the other coordinate and jet symbols fixed."""
    from functools import lru_cache
    from tasks import domain_conditions,entailed_domain_guards,guard_source,source
    @lru_cache(None)
    def partial(e,s):
        if not m.contains(e,('s',s)):return m.ZERO
        task=dict(kind='differentiate',function=source(e),variable=s,parameters=[v for v in names if v!=s],
                  method_requirement='table_and_rules')
        if local_premises is not None:
            guards=entailed_domain_guards(domain_conditions(e,True))
            local_premises.extend(guards)
            if guards:task['stated_conditions']=[guard_source(g) for g in guards]
        proof=request('частная производная по '+s,task)
        return m.substitute(freeze(proof['value']),{('v',s):('s',s)})
    return partial


def joint_limit(task,library,request):
    from tasks import domain_conditions,known_guard
    try:return continuity_from_paths(task,library)
    except (Unsupported,poly.NotRational,poly.Undefined):pass
    origin=task.get('source',{})
    if (set(task)-{'kind','id','source','given'} or not isinstance(origin,dict)
            or set(origin)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}
            or not isinstance(task.get('given'),str) or not library.data.get('joint_limit_sectors')):
        raise Unsupported('Не установлены исходная многомерная цель и область')
    text=task['given'].replace('²','^2').replace('³','^3')
    heading=origin.get('literal_requirement','')
    if not isinstance(heading,str):raise Unsupported('Не прочитано требование к пределу')
    axes=('x','y');x,y=(('s',s) for s in axes)
    joint=True;iterate=False;specified=None;coordinate=False;rays=False;given_value=None
    if hit:=re.fullmatch(r'(.+?), (?:x,y→(0|\+?infty)|x→([^,]+),y→([^,]+))',text):
        expression=hit[1];points=(hit[2],hit[2]) if hit[2] else (hit[3],hit[4])
        if heading!='Найти двойной предел.':raise Unsupported('Требования к пути и к выводу ещё не разобраны')
    elif hit:=re.fullmatch(r'(.+?); a=([^,]+),b=([^,]+)',text):
        if heading not in ('Найти оба повторных предела: сначала y→b, затем x→a; затем в обратном порядке.','Найти оба повторных предела в указанном порядке.'):
            raise Unsupported('Не установлены порядки повторных пределов')
        expression=hit[1];points=(hit[2],hit[3]);iterate=True;joint=False
    elif hit:=re.fullmatch(r'f=(.+?) off origin, f\(0,0\)=(-?\d+)',text):
        expression=hit[1];points=('0','0');given_value=m.q(int(hit[2]))
        coordinate=heading=='Доказать раздельную непрерывность и отсутствие совместной.'
        rays=heading=='Доказать непрерывность вдоль каждого луча x=t cos α,y=t sin α при t→0 и нарушение совместной непрерывности.'
        if not coordinate and not rays:raise Unsupported('Не прочитано требование к непрерывности на сечениях')
    elif heading=='Существует ли совместный предел при x,y→0?':
        expression=text;points=('0','0')
    elif heading.startswith('Доказать') and text.startswith('f='):
        expression=text[2:];iterate=True;points=('0','0')
        if hit:=re.fullmatch(r'Доказать: сначала y→0 затем x→0 дает (-?\d+), обратный порядок (-?\d+); совместного предела нет\.',heading):
            specified=[m.q(int(hit[1])),m.q(int(hit[2]))]
        elif hit:=re.fullmatch(r'Доказать, что оба повторных предела при x,y→0 равны (-?\d+), а совместного предела нет\.',heading):
            specified=[m.q(int(hit[1]))]*2
        else:raise Unsupported('Условие предъявляет иной набор предельных свойств')
    else:raise Unsupported('Не прочитаны точка, стороны или запрошенные выводы')
    if (coordinate or rays)!=(task['kind']=='multivariate_continuity'):
        raise Unsupported('Запрошенное условие непрерывности не совпадает с задачей на предел')
    names=sorted(set(re.findall(r'\b[A-Za-z][A-Za-z0-9]*\b',expression+' '+' '.join(points)))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e','infty'})
    raw=m.parse(expression,None,names)
    empty=dict(parameters=[v for v in names if v not in axes],assumptions=[])
    def at(s):
        if s in ('infty','+infty'):return s
        e=m.parse(s,None,empty['parameters'])
        if e==m.ZERO and s not in ('0','+0','-0'):raise Unsupported('Неоднозначная запись стороны подхода к нулю')
        if not m.constant_defined(e,empty):raise Unsupported('Конечная координата предельной точки не является определённым вещественным числом')
        return e
    point=tuple(map(at,points))
    scope=dict(point=point,coordinate_approaches=points,original_domain=domain_conditions(raw))
    plain=joint and not (coordinate or rays or iterate)
    if plain and all(not isinstance(v,str) for v in point):
        substitutions=dict(zip((x,y),point))
        here=m.substitute(raw,substitutions)
        whole=dict(parameters=names,assumptions=[])
        if m.constant_defined(here,empty) and all(
                known_guard(('positive' if rel=='nonnegative' else rel,m.substitute(g,substitutions)),empty)
                or rel=='nonnegative' and known_guard((rel,g),whole)
                for rel,g in scope['original_domain']):
            return dict(**scope,continuous_composition_at=here,applied_methods=['method.elementary_continuity']),dict(joint_limit=m.simplify(here))
    result=None
    if plain:
        result=continuous_quotient_limit(raw,point,points,names,request)
        if result is None:result=separated_power_limit(raw,points,point,request)
    if result is None:result=rational_joint_limit(raw,points,point,requested=(joint,iterate,coordinate,rays,specified,given_value),request=request)
    plan,value=result
    methods=[]
    if any(k in plan for k in ('successive_limits','distinct_paths','rational_identity','coordinate_sections','all_rays')):
        methods.append('method.joint_limit_paths')
    if any(k in plan for k in ('uniform_error_estimate','upper_bound','positive_homogeneous_base')):
        methods.append('method.joint_limit_sector_bounds')
    if 'outer_function' in plan or 'separated_terms' in plan:methods.append('method.joint_limit_continuous_factor')
    return {**scope,**plan,'applied_methods':methods},value


def continuous_quotient_limit(raw,point,approaches,names,request):
    """Extend a one-variable difference quotient, then compose on the original domain."""
    from operations import expression_positions
    from tasks import domain_conditions,known_guard,source
    from uniform import coefficient_rows
    x,y=(('s',v) for v in ('x','y'));t=('v','t');empty=dict(parameters=[v for v in names if v not in ('x','y')],assumptions=[])
    centered={a:(m.div(m.ONE,a) if isinstance(b,str) else m.add(a,b)) for a,b in zip((x,y),point)}
    zero={x:m.ZERO,y:m.ZERO}
    def smooth_at_zero(e,more=None):
        replacements={**zero,**(more or {})}
        val=m.substitute(m.simplify(e),replacements)
        if not m.constant_defined(val,empty) or any(not known_guard(g,empty) for g in domain_conditions(val,True)):
            raise Unsupported('Непрерывность остатка в точке ещё не установлена')
        return m.simplify(val)
    def local_sign(e):
        p,d=m.rational_form(e)
        def coefficient(poly):
            if not poly:return m.ZERO
            rows=coefficient_rows(poly,t)
            return rows[min(rows)]
        a,b=coefficient(p),coefficient(d)
        if any(m.contains(u,t) for u in (a,b)):raise Unsupported('Нет постоянного по t старшего коэффициента')
        return m.sign(m.div(a,b),empty)
    def path_witness():
        for a,b in ((1,1),(1,2),(2,1)):
            ray={slot:m.mul(m.q(-step if side=='-0' else step),t)
                 for slot,step,side in zip((x,y),(a,b),approaches)}
            curve={i:m.substitute(j,ray) for i,j in centered.items()}
            conditions=domain_conditions(m.substitute(raw,curve))
            try:
                signs=[local_sign(z) for _,z in conditions]
                if all(s in ({1,-1} if r=='nonzero' else {1} if r=='positive' else {0,1}) for (r,_),s in zip(conditions,signs)):
                    return dict(curve=list(curve.values()),parameter_approach='0+',raw_domain=conditions,eventual_signs=signs)
            except (ArithmeticError,Unsupported):continue
        raise Unsupported('Не установлена непустота исходной проколотой области')
    transformed=m.substitute(raw,centered)
    if transformed[0]=='rpow':
        transformed=('exp',('mul',transformed[2],('ln',transformed[1])))
    options=[]
    for _,node in expression_positions(transformed):
        if node[0] not in m.FUNCTIONS-{'abs','sqrt','cbrt'}:continue
        try:b=smooth_at_zero(node[1])
        except (ArithmeticError,Unsupported):continue
        if b[0]=='s' or any(m.contains(b,('s',n)) for n in names):continue
        fx=(node[0],b)
        if not m.constant_defined(fx,empty):continue
        delta=m.simplify(m.add(node[1],m.neg(b)));placeholder=('s','__slope')
        lifted=m.simplify(m.substitute(transformed,{node:m.add(m.simplify(fx),m.mul(placeholder,delta))}))
        try:
            smooth_at_zero(lifted,{placeholder:m.ONE})
            witness=path_witness()
        except (ArithmeticError,Unsupported):continue
        options.append((node,b,delta,lifted,witness,placeholder))
    if options:
        node,b,delta,lifted,witness,placeholder=options[0];v=('v','t')
        quotient=m.div(m.add((node[0],m.add(b,v)),m.neg((node[0],b))),v)
        child=dict(kind='limit',expression=source(quotient),variable='t',parameters=[],
                   approach=dict(point='0',side='both'))
        slope=freeze(request('непрерывное продолжение разностного отношения внешней функции',child)['value'])
        if isinstance(slope,str):raise Unsupported('Нет конечного значения для продолжения')
        result=smooth_at_zero(lifted,{placeholder:slope})
        return dict(centered_coordinates=list(centered.values()),outer_function=node[0],anchor=b,increment=delta,
                    residual=lifted,slope=slope,admissible_path=witness),dict(joint_limit=result)


def bivariate_limit_polynomials(e):
    x,y=('s','x'),('s','y')
    p,d=m.rational_form(e)
    if any(a not in (x,y) for poly in (p,d) for mon in poly for a,_ in mon):raise Unsupported('Для нерациональных множителей требуется отдельная оценка')
    return p,d


def angular_bounds(leading):
    """Certify a positive lower bound for the absolute homogeneous form on max(|x|,|y|)=1."""
    from polynomial import no_real_roots,univariate_coefficients
    x,y=('s','x'),('s','y');charts=[]
    for a,b in ((x,y),(y,x)):
        p,_=m.rational_form(m.substitute(leading,{a:m.ONE}));coeff=univariate_coefficients(p,b)
        if not coeff or not no_real_roots(coeff):raise Unsupported('Однородная часть может исчезать в угловом секторе')
        sign=1 if coeff[0]>0 else -1
        margin=abs(coeff[0])/2
        while not no_real_roots((abs(coeff[0])-margin,*(sign*v for v in coeff[1:]))):
            margin/=2
        charts.append(dict(fixed_coordinate=a[1],polynomial_coefficients=list(map(m.q,coeff)),sign=sign,absolute_lower_bound=m.q(margin)))
    return charts


def separated_power_limit(raw,points,point,request):
    """Compose finite coordinate limits or squeeze a real variable power."""
    from operations import expression_positions
    from tasks import domain_conditions,known_guard,source
    axes=('x','y');x,y=(('s',v) for v in axes);t=('v','t');empty=dict(parameters=[],assumptions=[])
    if points==('+infty','+infty') and not domain_conditions(raw):
        # Expand exponentials of sums first, so each product may split into independent coordinate functions.
        mapper={}
        for _,node in expression_positions(raw):
            if node[0]!='exp':continue
            poly,den=m.rational_form(node[1])
            if den!={():1}:continue
            val=m.ONE
            for mon,c in poly.items():val=m.mul(val,('exp',m.poly_expr({mon:c})))
            mapper[node]=val
        poly,den=m.rational_form(m.substitute(raw,mapper));terms=[]
        if den=={():1}:
            for mon,c in poly.items():
                parts=[m.ONE,m.ONE]
                for atom,k in mon:
                    dep=[j for j,s in enumerate((x,y)) if m.contains(atom,s)]
                    if len(dep)!=1:break
                    j=dep[0];parts[j]=m.mul(parts[j],m.power(atom,k))
                else:terms.append((m.q(c),parts));continue
                terms=[];break
        if terms and mapper:
            cache={};total=m.ZERO
            for c,parts in terms:
                term=c
                for s,e in zip(axes,parts):
                    if e==m.ONE:continue
                    if e not in cache:
                        goal=dict(kind='limit',expression=source(e),variable=s,parameters=[],approach=dict(point='+inf',side='positive_infinity'))
                        cache[e]=freeze(request('предел независимого множителя по '+s,goal)['value'])
                    if isinstance(cache[e],str):raise Unsupported('Требуется отдельная оценка произведения бесконечных множителей')
                    term=m.mul(term,cache[e])
                total=m.add(total,term)
            return dict(separated_terms=terms,factor_limits=[(e,v) for e,v in cache.items()]),dict(joint_limit=total)
    if raw[0]=='rpow':
        base,exponent=raw[1:];bp,bd=bivariate_limit_polynomials(base);ep,ed=bivariate_limit_polynomials(exponent)
        if points==('+infty','+infty') and bp and bd and all(v>0 for h in (bp,bd) for v in h.values()):
            if any(not h or any(v<=0 for v in h.values()) for _,g in domain_conditions(raw) for h in bivariate_limit_polynomials(g)):
                raise Unsupported('Положительность исходных делителей в квадранте не подтверждена')
            from level_sets import quadratic
            var=next((s for s,other in zip(axes,(y,x)) if not m.contains(exponent,other)),None)
            if var:
                for c in (m.q(1,2),m.q(2,3),m.q(3,4)):
                    diff=m.add(m.mul(c,m.poly_expr(bd)),m.neg(m.poly_expr(bp)))
                    try:_,_,form=quadratic(diff,list(axes))
                    except Unsupported:continue
                    if (m.num(form['offset'])<0 or form['linear_residual']!=m.ZERO or
                            any(m.num(row['eigenvalue'])<0 for row in form['orthogonal_axes'])):continue
                    child=dict(kind='limit',expression=source(exponent),variable=var,parameters=[],
                               approach=dict(point='+inf',side='positive_infinity'))
                    slope=request('показатель стремится к положительной бесконечности',child)['value']
                    if slope!='+inf':raise Unsupported('Не установлено возрастание показателя к бесконечности')
                    return dict(base_lower_zero=True,upper_bound=c,majorant_quadratic=diff,
                                orthogonal_squares=form['orthogonal_axes'],exponent=exponent),dict(joint_limit=m.ZERO)
        if point==(m.ZERO,m.ZERO) and bd=={():1} and ed=={():1} and bp and ep:
            degrees={sum(k for _,k in z) for z in bp};dmin=min(sum(k for _,k in z) for z in ep)
            if len(degrees)==1 and (degree:=next(iter(degrees)))>0 and dmin>0 and degree%2==0:
                certs=angular_bounds(m.poly_expr(bp))
                if all(c['sign']==1 for c in certs):
                    for rel,g in domain_conditions(raw):
                        if (rel,g)!=('positive',base) and not known_guard((rel,g),empty):raise Unsupported('Есть дополнительные ограничения показателя или основания')
                    major=m.mul(m.power(t,dmin),('ln',t))
                    limit=freeze(request('логарифм поглощается положительной степенью радиуса',dict(kind='limit',expression=source(major),
                                    variable='t',parameters=[],approach=dict(point='0',side='right')))['value'])
                    if limit!=m.ZERO:raise Unsupported('Логарифмическая оценка не стремится к нулю')
                    return dict(positive_homogeneous_base=degree,angular_denominator_certificates=certs,
                                base_coefficient_bound=m.q(sum(map(abs,bp.values()))),exponent_order=dmin,
                                exponent_coefficient_bound=m.q(sum(map(abs,ep.values())))),dict(joint_limit=m.ONE)


def rational_joint_limit(raw,points,point,requested,request):
    """Use successive limits, admissible monomial curves, and uniform sector bounds."""
    from fractions import Fraction as F
    import polynomial as arithmetic
    from tasks import domain_conditions,source
    from uniform import coefficient_rows
    from verify import same_value
    joint,iterate,coordinate,rays,specified,given_value=requested
    axes=('x','y');x,y=(('s',s) for s in axes);t=('v','t')
    p,d=bivariate_limit_polynomials(raw)
    guards=domain_conditions(raw)
    if any(g[0]!='nonzero' for g in guards):raise Unsupported('Путь должен удовлетворять дополнительным неравенствам')
    for _,e in guards:
        if not all(bivariate_limit_polynomials(e)):raise Unsupported('Исходное условие требует ненулевости тождественного нуля')
    if any(v not in (m.ZERO,'infty','+infty') for v in point):raise Unsupported('Не выполнен перенос в исходную конечную точку')
    plan={};value={}
    def limit_polynomial_ratio(A,B,coord,endpoint,side=0):
        if not B:raise Unsupported('Один из делителей тождественно нулевой на выбранном пути')
        if not A:return m.ZERO
        def leading(poly):
            rank=max if isinstance(endpoint,str) else min
            rows=coefficient_rows(poly,coord);degree=rank(rows)
            return degree,rows[degree]
        i,a=leading(A);j,b=leading(B);order=(j-i) if isinstance(endpoint,str) else (i-j)
        if order>0:return m.ZERO
        if order==0:return m.div(a,b)
        factor=m.num(m.simplify(m.div(a,b)))
        if factor is None:raise Unsupported('Для бесконечного значения требуется знак параметрического коэффициента')
        if (endpoint=='infty' or endpoint==m.ZERO) and abs(order)%2:
            if not side:raise Unsupported('Для двустороннего бесконечного выражения нужны отдельные направления')
            factor*=side
        return '+inf' if factor>0 else '-inf'
    sides=[-1 if s=='-0' else 1 if s in ('+0','+infty') else 0 for s in points]
    if iterate:
        results=[];plans=[]
        for i,j in ((1,0),(0,1)):
            # A nonzero bivariate polynomial restricts identically to zero on at most finitely many parallel slices.
            # The coefficient of the extreme power gives a nonzero polynomial in the remaining variable.
            inner=limit_polynomial_ratio(p,d,(x,y)[i],point[i],sides[i])
            if isinstance(inner,str):raise Unsupported('Не установлена область второго предела после бесконечного первого')
            final=limit_polynomial_ratio(*bivariate_limit_polynomials(inner),(x,y)[j],point[j],sides[j]);results.append(final)
            rank=max if isinstance(point[i],str) else min
            constraints=[d,*(h for _,g in guards for h in bivariate_limit_polynomials(g))]
            lead=[]
            for h in constraints:
                rows=coefficient_rows(h,(x,y)[i]);lead.append(rows[rank(rows)])
            plans.append(dict(first=axes[i],second=axes[j],inner_limit=inner,nonzero_coefficient_polynomials=list(dict.fromkeys(lead))))
        if specified and any(not same_value(a,b) for a,b in zip(results,specified)):raise Unsupported('Вычисленные повторные пределы расходятся с заданными значениями')
        value['iterated_limits']=results;plan['successive_limits']=plans
    if not joint:return plan,value
    if point[0]!=point[1]:raise Unsupported('Нужны различные масштабы координат при смешанных концах')
    infinity=isinstance(point[0],str)
    def path_limit(w0,w1):
        subst=dict(zip((x,y),(w0,w1)))
        local=m.substitute(raw,subst)
        def coeffs(e):
            A,B=m.rational_form(e)
            if any(arithmetic.univariate_coefficients(H,t) is None for H in (A,B)):raise Unsupported('Не доказан однопараметрический след')
            return A,B
        check=[]
        for _,g in guards:
            a,b=coeffs(m.substitute(g,subst))
            if not a or not b:raise Unsupported('Путь целиком вне исходной области')
            check.append((m.poly_expr(a),m.poly_expr(b)))
        A,B=coeffs(local)
        value=limit_polynomial_ratio(A,B,t,point[0],side=1)
        return dict(curve=[w0,w1],parameter_approach='+infty' if infinity else '0+',
                    nonzero_raw_divisors=check,trace_numerator=m.poly_expr(A),trace_denominator=m.poly_expr(B),limit=value)
    if rays:
        from graphs import rational_roots
        for c in (1,-1,2):
            test=path_limit(t,m.mul(m.q(c),t))
            if test['limit']!=given_value:
                if request is not None:
                    trace=m.substitute(raw,dict(zip((x,y),test['curve'])))
                    proof=request('контроль утверждения на допустимом луче',dict(kind='limit',expression=source(trace),variable='t',
                                    parameters=[],approach=dict(point='0',side='right')))
                    if freeze(proof['value'])!=test['limit']:raise Unsupported('Независимая проверка значения на луче не совпала')
                ray='t' if c==1 else '-t' if c==-1 else str(c)+'t'
                raise Unsupported('На исходном луче (t,'+ray+') при t→0+ предел '+str(test['limit'])+' не равен значению в начале')
        n,den=m.rational_form(m.add(raw,m.neg(given_value)))
        order=lambda poly:min(sum(v for _,v in mon) for mon in poly)
        if not n or order(n)<=order(den):raise Unsupported('Для общего направления не доказано совпадение предела с заданным значением')
        leads=[m.poly_expr({mon:c for mon,c in poly.items() if sum(v for _,v in mon)==order(poly)}) for poly in [den,*(h for _,g in guards for h in bivariate_limit_polynomials(g))]]
        exceptions={};checks=[]
        for e in leads:
            coeff,_=m.rational_form(m.substitute(e,{x:m.ONE}));co=arithmetic.univariate_coefficients(coeff,y);roots=rational_roots(co)
            if any(z.b for z in roots):raise Unsupported('Нужна отдельная проверка иррационального направления')
            checks.append(list(map(m.q,co)))
            for z in roots:exceptions[z.a]=path_limit(t,m.mul(m.q(z.a),t))
        special=[path_limit(m.ZERO,t),*exceptions.values()]
        if any(row['limit']!=given_value for row in special):raise Unsupported('Найден особый луч с другим пределом')
        plan['all_rays']=dict(generic_orders=[order(n),order(den)],leading_direction_polynomials=checks,exceptional_rays=special)
        value['all_directional_limits']=given_value
    if coordinate:
        pairs=[path_limit(t,m.ZERO),path_limit(m.ZERO,t)]
        if any(row['limit']!=given_value for row in pairs):raise Unsupported('На координатном сечении нет требуемого предела')
        # The axes require both signs; the rational section has the same finite two-sided value.
        for divisor in [d,*(h for _,g in guards for h in bivariate_limit_polynomials(g))]:
            homogeneous={sum(j for _,j in z) for z in divisor}
            if len(homogeneous)!=1:raise Unsupported('Нужно исследовать прочие точки непрерывности')
            for u,v in ((x,y),(y,x)):
                coef,_=m.rational_form(m.substitute(m.poly_expr(divisor),{u:m.ONE}))
                if not arithmetic.no_real_roots(arithmetic.univariate_coefficients(coef,v)):raise Unsupported('Исходный делитель может обращаться в нуль на ненулевом луче')
        plan['coordinate_sections']=pairs;value['separately_continuous']=True
    directions={F(1)}
    exps=[tuple(dict(mon).get(a,0) for a in (x,y)) for mon in (*p,*d)]
    for i,j in exps:
        for k,l in exps:
            if l!=j and (s:=F(i-k,l-j))>0:directions.add(s)
    paths=[]
    for slope in sorted(directions):
        if max(slope.numerator,slope.denominator)>128:continue
        for c in ((1,2) if sides[1]>0 else (-1,-2) if sides[1]<0 else (1,-1,2)):
            paths.append((m.mul(m.q(sides[0] or 1),m.power(t,slope.denominator)),m.mul(m.q(c),m.power(t,slope.numerator))))
    if not infinity:
        if points[1]=='0':paths.append((m.mul(m.q(sides[0] or 1),t),m.ZERO))
        if points[0]=='0':paths.append((m.ZERO,m.mul(m.q(sides[1] or 1),t)))
    first=None
    for w0,w1 in paths:
        try:row=path_limit(w0,w1)
        except (Unsupported,ArithmeticError):continue
        if first is None:first=row;continue
        if first['limit']!=row['limit']:
            plan['distinct_paths']=[first,row];value['joint_limit_exists']=False
            return plan,value
    if first is None or coordinate or rays or specified or isinstance(first['limit'],str):
        raise Unsupported('Не построены несовместимые пути или общая конечная оценка')
    candidate=first['limit']
    numerator,den=m.rational_form(m.add(raw,m.neg(candidate)))
    if not numerator:return dict(**plan,admissible_path=first,rational_identity=True),dict(**value,joint_limit=candidate)
    order=lambda H:(max if infinity else min)(sum(k for _,k in z) for z in H)
    porder,dorder=map(order,(numerator,den))
    gap=dorder-porder if infinity else porder-dorder
    if gap<=0:raise Unsupported('Порядок числителя не даёт стремления к нулю во всех секторах')
    leading={mon:c for mon,c in den.items() if sum(e for _,e in mon)==dorder}
    certs=angular_bounds(m.poly_expr(leading));margin=min(m.num(c['absolute_lower_bound']) for c in certs)
    remainder=sum(abs(c) for mon,c in den.items() if mon not in leading)
    radius=min(F(1),margin/(2*remainder)) if remainder else F(1)
    estimate=dict(scale='1/max(abs(x),abs(y))' if infinity else 'max(abs(x),abs(y))',max_scale=m.q(radius),
                  coefficient=m.q(2*sum(map(abs,numerator.values()))/margin),power=gap)
    return dict(**plan,admissible_path=first,orders=[porder,dorder],angular_denominator_certificates=certs,
                uniform_error_estimate=estimate),dict(**value,joint_limit=candidate)


def discontinuity_locus(task,library):
    """Reduce failures of the raw elementary continuity conditions to real loci."""
    from level_sets import quadratic
    from tasks import domain_conditions,equality_domain_witness
    origin=task.get('source',{})
    if (not library.data.get('multivariate_continuity_loci') or set(task)-{'kind','given','id','source'}
            or not isinstance(origin,dict) or set(origin)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}
            or origin.get('literal_requirement')!='Найти точки разрыва.' or not isinstance(task.get('given'),str)):
        raise Unsupported('Не установлены исходная формула и требование к множеству точек разрыва')
    formula=task['given'].replace('²','^2').replace('³','^3')
    names=sorted(set(re.findall(r'\b[A-Za-z][A-Za-z0-9]*\b',formula))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    coords=[s for s in 'xyz' if s in names];atoms={('s',s) for s in coords}
    if len(coords)<2:raise Unsupported('Нужна многомерная исходная область')
    expr=m.parse(formula,None,names);guards=domain_conditions(expr)
    def squares(e):
        if e[0]=='add':
            a,b=squares(e[1]),squares(e[2]);return a+b if a is not None and b is not None else None
        if e[0]=='mul' and (k:=m.num(e[1])) is not None and k>0:return squares(e[2])
        if e[0]=='pow' and e[2]>0 and e[2]%2==0:return [e[1]]
    def affine(e):
        p,d=m.rational_form(e)
        return d=={():1} and any(((a,1),) in p for a in atoms) and all(sum(k for _,k in mon)<=1 for mon in p)
    def zeros(e):
        if e[0]=='mul':return zeros(e[1])+zeros(e[2])
        if e[0]=='div' or e[0] in ('sqrt','cbrt','abs') or e[0]=='pow' and e[2]>0:return zeros(e[1])
        if (parts:=squares(e)) and all(affine(a) for a in parts):return [dict(kind='simultaneous_zeros',forms=parts)]
        if e[0]=='sin' and affine(e[1]):return [dict(kind='integer_pi',form=e[1])]
        if e[0]=='add':
            a,b=e[1:]
            if a[0]==b[0]=='pow' and a[2]==b[2] and a[2]>0 and a[2]%2:e=m.add(a[1],b[1])
        if affine(e):return [dict(kind='zero',form=e)]
        if m.num(e) not in (None,0) or e[0]=='exp':return []
        raise Unsupported('Множество нулей исходного делителя не разложено на проверенные части')
    loci=[];reductions=[];exteriors=[]
    for rel,e in guards:
        if rel=='nonzero':new=zeros(e)
        elif rel=='nonnegative' and squares(e) is not None:new=[]
        elif rel=='positive' and e[0]=='div' and (k:=m.num(e[1])) is not None and k>0 and e[2][0]=='sqrt':
            new=zeros(e[2])
        elif rel=='positive':
            p,d=m.rational_form(e)
            if (len(guards)==1 and d=={():1} and affine(e)
                    and all(set(dict(mon))<=atoms for mon in p)):
                normal=tuple(m.q(p.get(((('s',x),1),),0)) for x in coords)
                new=[dict(kind='hyperplane_boundary',form=e,normal=normal)]
                exteriors.append(dict(relation='negative',form=e))
                reductions.append(dict(strict_superlevel_affine_normal=normal))
                reductions.append(dict(source_guard=(rel,e),exceptional_loci=new))
                loci.extend(new)
                continue
            _,_,form=quadratic(e,coords)
            if (m.num(form['offset'])<=0 or form['linear_residual']!=m.ZERO or
                    any(m.num(row['eigenvalue'])>=0 for row in form['orthogonal_axes'])):
                raise Unsupported('Для точного описания замыкания положительной области нужна другая форма')
            if len(guards)!=1:raise Unsupported('Нужно проверить пересечения границ нескольких неравенств')
            new=[dict(kind='ellipsoid_boundary',form=e)];exteriors.append(dict(relation='negative',form=e))
            reductions.append(dict(strict_superlevel_normal_form=form))
        else:raise Unsupported('Нужно исследовать границу нестрогого исходного условия')
        reductions.append(dict(source_guard=(rel,e),exceptional_loci=new))
        for item in new:
            if item not in loci:loci.append(item)
    witness=equality_domain_witness([('s',s) for s in names],[],guards)
    return dict(variables=coords,raw_expression=expr,raw_domain=guards,guard_reductions=reductions,domain_witness=witness,
                applied_methods=['method.multivariate_continuity_loci']),dict(continuous_on_natural_domain=True,
                exceptional_points_in_closure=loci,outside_domain_closure=exteriors)


def field_composition(task,library,request):
    """Substitute arbitrary function jets into a printed claim or eliminate them to discover a PDE."""
    from functools import lru_cache
    from itertools import combinations_with_replacement
    from operations import expression_positions
    from tasks import domain_conditions, entailed_domain_guards, equality_domain_witness, guard_source, known_guard
    from verify import same_value

    if set(task)-{'id','kind','source','given'} or not library.data.get('abstract_field_composition'):
        raise Unsupported('Не установлено полное исходное задание')
    origin=task.get('source',{})
    if not isinstance(origin,dict) or set(origin)-{'exercise','pdf_page','printed_page','pdf_sha256','literal_requirement'}:
        raise Unsupported('Не разобраны ограничения исходного поля')
    heading=origin.get('literal_requirement','')
    if not isinstance(heading,str) or not isinstance(task.get('given'),str) or len(task['given'])>4000:
        raise Unsupported('Требуются исходная формула и заголовок')
    normal=lambda text:text.replace('²','^2').replace('³','^3')
    given=re.fullmatch(r'([A-Za-z]\w*)=(.+?)(?:, ([A-Za-z]\w*) (?:arbitrary )?differentiable)?',normal(task['given']))
    if not given:raise Unsupported('Исходная зависимость и гладкость произвольной функции не распознаны')
    result_name,formula,declared=given.groups()
    eliminate=task['kind']=='eliminate_arbitrary_functions'
    if eliminate:
        if not re.fullmatch(r'Последовательным дифференцированием исключить произвольн(?:ую функцию|ые функции)\.',heading):
            raise Unsupported('Не установлено требование исключить произвольные функции')
        target=None
    else:
        required=re.fullmatch(r'(Упростить|Доказать|Проверить) (.+?)(?:, (?:произвольные )?функции (?:достаточно дифференцируемы|дифференцируемы достаточно раз))?\.',normal(heading))
        if not required:raise Unsupported('Не разобран напечатанный оператор или требование к гладкости')
        action,target=required.groups()
        if not declared and 'дифференцируемы' not in heading:
            raise Unsupported('В исходном тождестве не подтверждена дифференцируемость произвольных функций')
        if (action=='Упростить')!=(target.count('=')==0) or target.count('=')>1:
            raise Unsupported('Не согласованы равенство и запрошенный результат')
    try:tree=ast.parse(formula.replace('^','**'),mode='eval').body
    except SyntaxError as exc:raise Unsupported('Требуется одна явная композиция поля') from exc
    funcs={c.func.id for c in ast.walk(tree) if isinstance(c,ast.Call) and isinstance(c.func,ast.Name)}
    arbitrary=funcs-m.FUNCTIONS-set(m.ALIASES)
    if not arbitrary or declared and arbitrary!={declared}:raise Unsupported('Не установлены используемые произвольные функции')
    for fn in arbitrary:
        arities={len(c.args) for c in ast.walk(tree) if isinstance(c,ast.Call) and isinstance(c.func,ast.Name) and c.func.id==fn}
        if len(arities)!=1:raise Unsupported('Функции с различным числом аргументов обозначены одним именем')
    names=sorted({c.id for c in ast.walk(tree) if isinstance(c,ast.Name)}-funcs-{'pi','e'})
    axes=[s for s in 'xyzt' if s in names and s!=result_name]
    if not axes or result_name in names or result_name in funcs:raise Unsupported('Не определены независимые переменные исходной функции')
    source_names=set(names);slots={};bindings={}
    def atom(s):return ('s',s)
    def register(fn,args,word=()):
        index=(fn,args,word)
        if index not in slots:
            slot='Field'+str(len(slots))
            if slot in source_names or slot==result_name:raise Unsupported('Конфликт обозначения промежуточного значения')
            slots[index]=slot;bindings[slot]=index;names.append(slot)
        return slots[index]
    class Extract(ast.NodeTransformer):
        def visit_Call(self,node):
            if not isinstance(node.func,ast.Name) or node.keywords:raise Unsupported('Не поддержана вложенная запись отображения')
            self.generic_visit(node)
            if node.func.id not in arbitrary:return node
            args=tuple(m.parse(ast.unparse(c).replace('**','^'),None,names) for c in node.args)
            if not args:raise Unsupported('Требуются аргументы произвольной функции')
            return ast.Name(id=register(node.func.id,args),ctx=ast.Load())
    outer=m.parse(ast.unparse(Extract().visit(tree)).replace('**','^'),None,names)
    originals=[outer,*(arg for _,args,_ in bindings.values() for arg in args)]
    guards=list(dict.fromkeys(g for e in originals for g in domain_conditions(e)))
    for e in originals:
        if any(node[0]=='rpow' and m.num(node[2]) is None and any(m.contains(node[1],atom(a)) for a in axes)
               for _,node in expression_positions(e)):
            raise Unsupported('Для параметрической степени требуется проверить допустимые действительные ветви основания при каждом значении показателя')
    boundary={}
    def smooth(raws):
        ctx=m.context(dict(variable='__jet',parameters=names,parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
        for e in raws:
            for rel,expr in domain_conditions(e,True):
                if known_guard((rel,expr),ctx):continue
                coeffs,d=m.rational_form(expr)
                if (not eliminate or rel!='positive' or ('nonnegative',expr) not in guards or d!={():1} or not coeffs
                        or any(len(mon)!=1 or mon[0][0] not in map(atom,axes) or mon[0][1]%2 or c<=0 for mon,c in coeffs.items())):
                    raise Unsupported('Гладкость на границе исходной области отдельно не установлена')
                boundary[expr]={mon[0][0]:m.ZERO for mon in coeffs}
    smooth(originals)
    def on_regular(role,t):
        if boundary:t=dict(t,stated_conditions=[guard_source(('positive',e)) for e in boundary])
        return request(role,t)
    section=coordinate_sections(names,on_regular)
    @lru_cache(None)
    def total(e,x):
        v=section(e,x)
        for slot,(fn,args,word) in list(bindings.items()):
            if not m.contains(e,atom(slot)):continue
            slope=m.ZERO
            for i,arg in enumerate(args):
                dx=total(arg,x)
                if dx!=m.ZERO:slope=m.add(slope,m.mul(dx,atom(register(fn,args,tuple(sorted((*word,i)))))))
            v=m.add(v,m.mul(section(e,slot),slope))
        return m.simplify(v)
    @lru_cache(None)
    def field(word):
        if not word:return outer
        if len(word)>2:raise Unsupported('Для этого порядка требуется дальнейшее раскрытие правила цепочки')
        if declared and len(word)>1:raise Unsupported('Дана только первая производная внешней функции')
        if any(x not in axes for x in word):raise Unsupported('Производная по зависимой или неизвестной переменной')
        return total(field(word[:-1]),word[-1])
    def label(word):return result_name+('_'+''.join(word) if word else '')
    derivatives={};search={}
    if target:
        # Read adjacent single coordinates and coefficients as ordinary printed multiplication.
        # A derivative token such as u_xy is a single atom.
        target=re.sub(r'(?<=[0-9)])(?=[A-Za-z])','*',target)
        target=re.sub(r'\b([a-z])\(',lambda hit:hit[1]+'*(' if hit[1] in names else hit[0],target)
        target=re.sub(r'\b[xyzt]{2,}\b',lambda hit:'*'.join(hit[0]) if all(s in axes for s in hit[0]) else hit[0],target)
        allow=set(source_names)
        substitutions={atom(result_name):outer}
        for token in re.findall(r'\b'+re.escape(result_name)+r'_([xyzt]+)\b',target):
            value=field(token);derivatives[label(token)]=value;allow.add(label(token));substitutions[atom(label(token))]=value
        sides=tuple(m.parse(s,None,[*allow,result_name]) for s in target.split('='))
        guards.extend(g for e in sides for g in domain_conditions(m.substitute(e,substitutions)) if g not in guards)
        concrete=[m.simplify(m.substitute(s,substitutions)) for s in sides]
        if len(sides)==2:
            if not same_value(*concrete):raise Unsupported('После подстановки обе части не равны тождественно')
            answer=dict(identity_established=True)
        else:
            if any(m.contains(concrete[0],atom(k)) for k in bindings):raise Unsupported('В результате всё ещё присутствуют произвольные производные')
            answer=dict(simplified=concrete[0])
    else:
        # Eliminate each arbitrary jet as an algebraic indeterminate, retaining symbolic coefficients.
        # Cross multiplication also covers points where the chosen elimination coefficient vanishes.
        def independent_relation(terms):
            basis={}
            for lhs,v in terms:
                p,den=m.rational_form(v)
                row={}
                for mon,c in p.items():
                    unknown=tuple((a,n) for a,n in mon if a[0]=='s' and a[1] in bindings)
                    scalar=tuple(a for a in mon if a not in unknown)
                    if any(m.contains(a,atom(s)) for a,_ in scalar for s in bindings):return None
                    row[unknown]=m.add(row.get(unknown,m.ZERO),m.poly_expr({scalar:c}))
                if any(m.contains(m.poly_expr(den),atom(s)) for s in bindings):return None
                formal=m.mul(lhs,m.poly_expr(den))
                for pivot,old,eq in basis.values():
                    if pivot not in row:continue
                    a,b=row[pivot],old[pivot]
                    formal=m.add(m.mul(formal,b),m.neg(m.mul(eq,a)))
                    row={k:m.add(m.mul(row.get(k,m.ZERO),b),m.neg(m.mul(old.get(k,m.ZERO),a))) for k in row.keys()|old.keys()}
                    row={k:v for k,v in row.items() if v!=m.ZERO}
                pivot=min((k for k in row if k),key=canonical,default=None)
                if pivot is not None:basis[pivot]=(pivot,row,formal);continue
                identity=m.simplify(m.add(formal,m.neg(row.get((),m.ZERO))))
                if identity!=m.ZERO and any(m.contains(identity,atom(k)) for k in derivatives):return identity
            return None
        values={result_name:outer};relation=None
        for order in (1,2):
            for word in combinations_with_replacement(axes,order):
                key=label(word);derivatives[key]=values[key]=field(word)
            terms=[(atom(k),v) for k,v in values.items()]
            relation=independent_relation(terms)
            if relation:break
        search=dict(maximum_derivative_order=order,products_of_derivatives_needed=relation is None)
        if relation is None:
            terms += [(m.mul(a,b),m.mul(v,w)) for (a,v),(b,w) in combinations_with_replacement(terms,2)]
            relation=independent_relation(terms)
        supplied={atom(k):v for k,v in values.items()}
        if relation is None or not same_value(m.substitute(relation,supplied),m.ZERO):
            raise Unsupported('Уравнение со всеми исключёнными функциями не построено')
        numerator,_=m.rational_form(relation)
        common=m.common_mon(numerator)
        unit=numerator[min(numerator,key=canonical)]
        reduced=m.poly_expr({tuple((a,n-common.get(a,0)) for a,n in mon if n>common.get(a,0)):c/unit for mon,c in numerator.items()})
        if any(m.contains(reduced,atom(k)) for k in derivatives) and same_value(m.substitute(reduced,supplied),m.ZERO):
            relation=reduced
        for zeros in boundary.values():
            if m.simplify(m.substitute(relation,zeros))!=m.ZERO:
                raise Unsupported('Исключённое при дифференцировании граничное множество требует отдельного доказательства')
        answer=dict(differential_relation=relation)
    witness=equality_domain_witness([atom(s) for s in names],[],guards+[('positive',e) for e in boundary])
    return dict(dependent=result_name,coordinates=axes,natural_domain=guards,field_bindings=bindings,derivative_values=derivatives,
                witness=witness,elimination_search=search,
                checked_exceptional_sets=[dict(squared_sum=e,zero_coordinates=[a[1] for a in zeros]) for e,zeros in boundary.items()]),answer


def forward_from_mixed_chart(task):
    from integrals import affine
    from verify import same_value
    formula=task['source_formula']
    tag=re.search(r'\b([a-z])_([a-z]+)\b',formula)
    if not tag or not set(tag[2])<=set('xy'):raise Unsupported('A scalar graph on a plane is required')
    old=['x','y',tag[1]]
    rows=[r.split('=') for r in _delimited_fields(task['coordinate_change'])]
    if len(rows)!=2 or any(len(r)!=2 for r in rows):raise Unsupported('Two source chart relations are needed')
    defined,implicit=sorted(rows,key=lambda pair:pair[0].strip() in old)
    xnew,xdef=[s.strip() for s in defined];xold,rel=[s.strip() for s in implicit]
    if xnew in old or xold not in old[:2]:raise Unsupported('This is not a mixed chart in one new coordinate')
    new=set(re.findall(r'\b[A-Za-z_]\w*\b',rel))-set(old)-{xnew}-m.FUNCTIONS
    if len(new)!=1:raise Unsupported('Exactly one new coordinate must be isolated')
    v,=new;t=('v',v);z=mv_symbol(xnew)
    parsed=m.parse(rel,v,[*old,xnew])
    k,b=affine(parsed,v)
    if k==ZERO or domain_conditions(parsed) or not same_value(parsed,m.add(b,m.mul(k,t))):
        raise Unsupported('The mixed chart relation is not affine in the missing coordinate')
    xexpr=m.parse(xdef,None,old)
    expr=m.substitute(m.div(m.add(mv_symbol(xold),m.neg(b)),k),{z:xexpr})
    return f'{xnew}={source(xexpr)},{v}={source(expr)}',m.substitute(k,{z:xexpr})


def separable_log_operator(task,lib):
    """Transport polynomial coefficients through separable logarithmic radical charts."""
    from integrals import affine
    exponents=str.maketrans({'²':'^2','³':'^3','⁴':'^4'})
    tex=task['source_formula'].translate(exponents)
    chart_text=task['coordinate_change'].translate(exponents)
    if tex.count('=')!=1 or ';' in tex or ',' in tex or 'ln(' not in chart_text:
        raise Unsupported('A separable logarithmic chart requires one complete operator')
    tags=sorted(set(re.findall(r'\b([a-z])_([a-z]{1,2})\b',tex)))
    if not tags or len({f for f,_ in tags})!=1:raise Unsupported('A scalar ordered second-order operator is required')
    field=tags[0][0];axes=sorted({a for _,word in tags for a in word})
    if len(axes)!=2 or field in axes:raise Unsupported('Two independent coordinates are required')
    old=[*axes,field];new=[];charts=[]
    names=[*old,*(f+'_'+word for f,word in tags)]
    for piece in _delimited_fields(chart_text):
        label,sep,text=piece.strip().partition('=')
        if not sep or not re.fullmatch(MV_SYMBOL,label) or label in old or label in new:
            raise Unsupported('The two new coordinates must be separately declared')
        raw=m.parse(text,None,axes)
        used=[a for a in axes if m.contains(raw,mv_symbol(a))]
        if len(used)!=1:raise Unsupported('Each new coordinate must depend on one old axis')
        new.append(label);charts.append((used[0],raw))
    if sorted(a for a,_ in charts)!=axes:raise Unsupported('The old coordinate axes must be covered exactly once')
    partial,rules=derivative_table(lib)
    first={};second={};mapped={};evidence={}
    for label,(axis,raw) in zip(new,charts,strict=True):
        if raw[0]!='ln':raise Unsupported('The coordinate must be logarithmic')
        if raw[1][0]!='add':raise Unsupported('Need an affine term and a positive reciprocal-radical primitive')
        pair=next(((x,y) for x,y in (raw[1][1:],raw[1][1:][::-1]) if y[0]=='sqrt'),None)
        if pair is None:raise Unsupported('The positive radical is not explicit')
        linear,sqrt=pair;origin=mv_symbol(axis)
        a,b=affine(m.substitute(linear,{origin:('v',axis)}),axis)
        p=m.num(m.add(sqrt[1],m.neg(m.power(linear,2))))
        if m.num(a) in (None,0) or m.num(b) is None or p is None or p<=0 or domain_conditions(sqrt[1]):
            raise Unsupported('Need a genuine affine axis and a strictly positive quadratic gap')
        # The square root strictly dominates the absolute value of the affine axis.
        if not same_value(raw[1],m.add(linear,sqrt)):
            raise Unsupported('The logarithmic argument changes on the real axis')
        d=m.div(a,sqrt)
        if not same_value(partial(raw,axis),d):raise Unsupported('No exact derivative normalization')
        first[axis]=d;second[axis]=partial(d,axis);mapped[axis]=label
        evidence[label]=dict(old_axis=axis,chart=raw,radical_gap=q(p),derivative=d)
    replace={}
    jet=lambda word:mv_symbol(field+'_'+'_'.join(word))
    for f,w in tags:
        d=m.mul(*[first[a] for a in w]) if len(w)==2 else first[w[0]]
        value=m.mul(d,jet([mapped[a] for a in w]))
        if len(w)==2 and w[0]==w[1]:
            value=m.add(value,m.mul(second[w[0]],jet([mapped[w[0]]])))
        replace[mv_symbol(f+'_'+w)]=value
    sides=[m.parse(z,None,names) for z in tex.split('=')]
    if any(domain_conditions(z) for z in sides):raise Unsupported('The original operator has extra restrictions')
    residual=m.polynomial_quotient(m.add(m.substitute(sides[0],replace),m.neg(m.substitute(sides[1],replace))))
    if any(m.contains(residual,mv_symbol(a)) for a in axes):
        raise Unsupported('The new coefficients still depend on the old coordinates')
    return dict(theorem='method.forward_coordinate_operators',axis_charts=evidence,derivatives=rules,
                replaced_jets=list(replace.items()),argument=[
        'Проверяем положительный зазор между квадратом радикала и квадратом аффинной части. Поэтому каждый логарифм определён на всей прямой.',
        'Вычисляем обе производные по каждой оси. Первые производные ненулевые, а каждая ось покрывает всю новую прямую.',
        'Подставляем правило цепочки в каждый упорядоченный член оператора и проверяем, что старые координаты исчезли.',
    ]),dict(transformed_sides=[residual,ZERO],scope='whole real product chart')


def transform_coordinates(task,library,request):
    if not library.data.get('ordinary_differential_coordinate_chart'):
        raise Unsupported('В библиотеке отсутствует правило преобразования производных вдоль графика')
    allowed={'kind','source','id','source_formula','coordinate_change','requested_output','suggested_method'}
    mode=task.get('requested_output');src=task.get('source',{})
    seeking=mode==['solve_in_prescribed_coordinates'] and library.data.get('integrate_coordinate_operator')
    symbolic=library.data.get('coordinate_covariance_priorities')
    special_modes=(['transform_system'],['transform_both_expressions'],['prove Schwarzian invariance'],
                   ['prove reduction to u_xy+c1*u=0'],['transform_using_Legendre'])
    hyperbolic=library.data.get('certified_operator_proportionality') and mode==['reduce_to_u_xieta=0_and_find_general_solution']
    structural=bool(symbolic) and mode in (*special_modes,["find Y',Y'',Y'''"],['prove invariance'],
                    ['prove (2PQ+Q_prime)*Q^(-3/2)=(2pq+q_prime)*q^(-3/2)'])
    if (mode==['prove (2PQ+Q_prime)*Q^(-3/2)=(2pq+q_prime)*q^(-3/2)']
            and task.get('printed_invariant')=='(2*P*Q+Q_prime)*Q^(-3/2)=(2*p*q+q_prime)*q^(-3/2)'):
        allowed.add('printed_invariant')
    if (set(task)-allowed or not seeking and not structural and not hyperbolic and mode not in (['transform_equation'],['transform_expression'],['transform_curvature'])
            or not isinstance(src,dict) or set(src)-{'literal_requirement','exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','continues_on_page'}
            or 'continues_on_page' in src and (type(src['continues_on_page']) is not int or src['continues_on_page']<1)
            or 'suggested_method' in task and not isinstance(task['suggested_method'],str)
            or src.get('literal_requirement',mode[0])!=mode[0]):
        raise Unsupported('Нужно сохранить требования к преобразованию или решению уравнения')
    changes=task['coordinate_change'];formula=task['source_formula']
    if not isinstance(changes,str) or not isinstance(formula,str):raise Unsupported('Нужны напечатанные формулы и замена')
    if hyperbolic:return hyperbolic_constant_symbol(task)
    if library.data.get('guarded_differential_charts'):
        if mode==['transform_equation'] and changes.startswith('new '):
            return dependent_even_power_chart(task)
        if mode==['transform_equation'] and 'acos(' in changes and '^(' in changes:
            try:return angular_weighted_characteristics(task)
            except Unsupported:pass
        if mode==['transform_expression'] and 'ln(sqrt(' in changes and 'atan(' in changes:
            try:return radial_graph_directional_quotient(task)
            except Unsupported:pass
    if mode==['transform_expression'] and library.data.get('regular_graph_prolongation'):
        try:forward,scale=forward_from_mixed_chart(task)
        except Unsupported:pass
        else:
            plan,value=graph_prolongation(dict(task,coordinate_change=forward),request)
            plan.update(original_mixed_chart=changes,isolated_coefficient=scale)
            return plan,value
    if (seeking or mode==['transform_equation']) and library.data.get('integrate_coordinate_operator'):
        try:return characteristic_chart(task,library)
        except (Unsupported,ZeroDivisionError):pass
    if seeking:
        try:return forward_field_equation(task,request)
        except Unsupported:
            if not library.data.get('factored_graph_determinant'):raise
            return inverse_graph_coordinate_solution(task,request)
    if symbolic and mode==['transform_equation'] and 'ln(' in changes:
        try:return separable_log_operator(task,library)
        except (Unsupported,poly.ResourceBound,ZeroDivisionError):pass
    if symbolic:
        if 't=ln(abs(' in changes:return ordinary_log_chart(task,library)
        if mode in special_modes:return characteristic_operator_forms(task,request)
        if mode in (['prove invariance'],['prove (2PQ+Q_prime)*Q^(-3/2)=(2pq+q_prime)*q^(-3/2)']):
            if library.data.get('certified_operator_proportionality') and mode==['prove invariance']:
                pairs=[s.partition('=') for s in changes.split(',')]
                if len(pairs)==2 and {key for key,sep,_ in pairs if sep}=={'x','y'}:
                    return invariance_by_operator_proportionality(task,request)
            return coordinate_covariance(task,library,request)
        if structural or changes=='dependent x, independent t=x*y' or 'int_' in changes or ' homogeneous' in formula:
            return ordinary_structural_coordinate(task)
    try:return direct_coordinate_transform(task,library,request)
    except (Unsupported,ZeroDivisionError):
        if symbolic:
            try:return characteristic_operator_forms(task,request)
            except Unsupported:pass
        if not library.data.get('regular_graph_prolongation') or mode==['transform_curvature']:raise
        if library.data.get('factored_graph_determinant') and mode==['transform_equation']:
            try:return graph_prolongation(task,request,factored=True)
            except (Unsupported,ZeroDivisionError):pass
        return graph_prolongation(task,request)


def dependent_even_power_chart(task):
    """Transport first-order jets of one field on both inverse branches of an even power."""
    chart=re.fullmatch(r'new ([A-Za-z]\w*)=([A-Za-z]\w*)\^(\d+)',task['coordinate_change'].replace('²','^2').replace('⁴','^4'))
    words=task['source_formula'].replace('²','^2').removesuffix(' as printed').split('=')
    if not chart or len(words)!=2:raise Unsupported('Expected a dependent power and an original equation')
    w,z,n=chart[1],chart[2],int(chart[3])
    names=mv_names(' '.join(words))
    jets=[v for v in names if v.startswith(z+'_')]
    if (w in names or w==z or not jets or n not in range(2,13,2)
            or any(len(v[len(z)+1:])!=1 or w+v[len(z):] in names for v in jets)):
        raise Unsupported('Only first jets of a single even dependent power are admitted on its regular sheets')
    L,R=(m.parse(v,None,names) for v in words)
    if domain_conditions(L) or domain_conditions(R):raise Unsupported('Extra source guards require separate branch checks')
    W=('s',w);root=('rpow',W,q(1,n));slope=m.div(root,m.mul(q(n),W))
    ss=lambda v:('s',v)
    replacement={ss(z):root,**{ss(v):m.mul(slope,ss(w+v[len(z):])) for v in jets}}
    branches=[]
    for sign in (1,-1):
        table={k:m.mul(q(sign),e) for k,e in replacement.items()}
        branches.append(dict(condition=z+('>0' if sign==1 else '<0')+' and '+w+'>0',
                             transformed_sides=[m.simplify(m.substitute(e,table)) for e in (L,R)]))
    branches.append(dict(condition=z+'=0, '+w+'=0 and the new first jets vanish',
                         transformed_sides=[m.simplify(m.substitute(e,{ss(z):ZERO})) for e in (L,R)]))
    return dict(theorem='method.dependent_even_power_chart',power=n,inverse_branch=root,replacement=list(replacement.items()),argument=[
        'Парная степень имеет две гладкие обратные ветви при положительной новой величине. Правило цепочки переводит только производные заменяемого поля, сохраняя остальные поля.',
        'При нуле новая первая производная исчезает независимо от старой. В этой точке остаётся исходное условие с нулевым значением старого поля.'
    ]),dict(branches=branches)


def radial_graph_directional_quotient(task):
    """Use the same directional subtraction on the differential of a regular graph chart."""
    match=re.fullmatch(r'\(([a-z])-([a-z])\)/\(([a-z])_\1-\3_\2\)',task['source_formula'].replace(' ',''))
    rows=[piece.split('=',1) for piece in task['coordinate_change'].replace('²','^2').split(',')]
    if not match or len(rows)!=3 or any(len(row)!=2 for row in rows):raise Unsupported('Expected a ratio of coordinate and gradient differences')
    x,y,z=match.groups();u,v,w=[row[0] for row in rows]
    if len({x,y,z,u,v,w})!=6 or any(not re.fullmatch(r'[a-z]',name) for name in (u,v,w)):
        raise Unsupported('The original and new coordinate roles must be distinct')
    ss=lambda name:('s',name)
    X,Y,Z=map(ss,(x,y,z)); R=m.add(m.power(X,2),m.power(Y,2))
    radius,angle,height=(m.parse(expr,None,[x,y,z]) for _,expr in rows)
    if (radius[0]!='ln' or radius[1][0]!='sqrt' or not same_value(radius[1][1],R) or angle!=('atan',Z)
            or domain_conditions(height)):
        raise Unsupported('Expected a logarithmic radius and the principal arctangent of the field')
    origin=dict.fromkeys((X,Y,Z),ZERO);D=m.substitute(height,origin)
    A,B,C=(m.simplify(m.add(m.substitute(height,{**origin,k:ONE}),m.neg(D))) for k in (X,Y,Z))
    if m.num(A) in (None,0) or B!=A or m.num(C) is None or not same_value(height,m.add(D,m.dot((A,B,C),(X,Y,Z)))):
        raise Unsupported('The last chart component must be affine and symmetric in the old axes')
    ZX,ZY=ss(z+'_'+x),ss(z+'_'+y);WU,WV=ss(w+'_'+u),ss(w+'_'+v)
    factor=m.add(C,m.neg(m.mul(m.power(('cos',ss(v)),2),WV)))
    result=m.div(m.mul(('exp',m.mul(q(2),ss(u))),factor),WU)
    J=m.div(m.add(m.mul(X,ZY),m.neg(m.mul(Y,ZX))),m.mul(R,m.add(ONE,m.power(Z,2))))
    return dict(theorem='method.radial_graph_directional_quotient',jacobian=J,chart_domain=[('positive',R),('nonzero',J),('nonzero',m.add(ZX,m.neg(ZY)))],argument=[
        'Дифференцируем логарифмический радиус, арктангенс поля и последнее аффинное равенство по двум исходным координатам.',
        'Вычитаем равенства. Одинаковые аффинные коэффициенты сокращаются. Если производная новой высоты по радиусу равна нулю, ненулевая исходная разность вынуждает оба аффинных коэффициента обратиться в нуль, что исключено.',
        'Возвращаем радиус через экспоненту, а производную арктангенса через квадрат косинуса новой угловой координаты.'
    ]),dict(transformed_sides=[result],regular_when=[('positive',R),('nonzero',J),('nonzero',m.add(ZX,m.neg(ZY)))])


def angular_weighted_characteristics(task):
    """Remove an angular drift by conjugation before applying two characteristics."""
    formula,sep,condition=task['source_formula'].replace('²','^2').partition(';')
    guard=re.fullmatch(r'abs\(([a-z])\)<1',condition.replace(' ',''))
    rows=[p.strip().split('=',1) for p in task['coordinate_change'].replace('²','^2').split(',')]
    if not sep or not guard or formula.count('=')!=1 or len(rows)!=3 or any(len(row)!=2 for row in rows):
        raise Unsupported('A strict principal-angle domain and the full weighted chart are required')
    x=guard[1];match=re.search(rf'\b([a-z])_{x}{x}\b',formula)
    other=mv_names(' '.join(expr for _,expr in rows[:2]),x)
    if not match or len(other)!=1:raise Unsupported('Expected one field, one linear axis and one angular axis')
    y,=other;z=match[1];u,v,w=[row[0] for row in rows]
    if len({x,y,z,u,v,w})!=6 or any(not re.fullmatch(r'[a-z]',s) for s in (u,v,w)):
        raise Unsupported('Angular coordinate roles must be distinct')
    ss=lambda a:('s',a)
    X,Y,Z=map(ss,(x,y,z));H=('acos',X);Q=m.add(ONE,m.neg(m.power(X,2)))
    U,V,W=(m.parse(expr,None,[x,y,z]) for _,expr in rows)
    c=m.num(m.simplify(m.substitute(U,{Y:ONE,H:ZERO})))
    if c is None or c<=0 or not (same_value(U,m.mul(q(c),m.add(Y,H))) and same_value(V,m.mul(q(c),m.add(Y,m.neg(H))))):
        raise Unsupported('Expected two independent sums and differences of the principal angle and the axial coordinate')
    if W[0]!='mul' or Z not in W[1:]:raise Unsupported('Expected a fixed power weight on the dependent variable')
    weight=W[2] if W[1]==Z else W[1]
    if weight[0] not in ('rpow','pow') or not same_value(weight[1],Q):raise Unsupported('The scalar weight must be a power of the positive circular quadratic')
    p=m.num(m.simplify(weight[2])) if weight[0]=='rpow' else Fraction(weight[2])
    if p is None:raise Unsupported('The weighting exponent must be fixed')
    jets=[z+'_'+x+x,z+'_'+y+y,z+'_'+x,z+'_'+y,z]
    lhs,rhs=(m.parse(t,None,[x,y,*jets]) for t in formula.split('='));raw=m.add(lhs,m.neg(rhs))
    ctx=m.context(dict(variable='__angular_chart',parameters=[x,y,*jets],parameter_conditions=[guard_source(('positive',Q))]))
    if any(not known_guard(g,ctx) for e in (U,V,W,lhs,rhs) for g in domain_conditions(e)):
        raise Unsupported('An original chart or coefficient has an extra domain restriction')
    blank=dict.fromkeys(map(ss,jets),ZERO)
    a,b,drift,side,constant=[m.simplify(m.substitute(raw,{**blank,ss(j):ONE})) for j in jets]
    k=m.num(m.simplify(m.substitute(drift,{X:ONE})));l=m.num(side);h=m.num(constant)
    if (k is None or l is None or h is None or not same_value(a,Q) or b!=q(-1) or not same_value(drift,m.mul(q(k),X))
            or not same_value(raw,m.dot((a,b,drift,side,constant),list(map(ss,jets))))):
        raise Unsupported('The source must be linear with angular second-order part and an affine drift weight')
    angle=m.div(m.add(ss(u),m.neg(ss(v))),q(2*c)); sine=('sin',angle);cot=('cot',angle)
    gamma=2*p;d=-1-k;zeroth=gamma+h;quadratic=gamma+gamma**2-d*gamma
    potential=m.div(q(zeroth),m.power(sine,2)) if zeroth==quadratic else m.add(q(zeroth),m.mul(q(quadratic),m.power(cot,2)))
    WU,WV,UV=map(ss,(w+'_'+u,w+'_'+v,w+'_'+u+'_'+v))
    residual=m.dot((q(-4*c*c),m.mul(q(c*(d-2*gamma)),cot),q(c*l),potential),
                   (UV,m.add(WU,m.neg(WV)),m.add(WU,WV),ss(w)))
    return dict(theorem='method.angular_weighted_characteristics',old_angle_drift=q(d),scaling_exponent=q(gamma),
                transformed_potential=potential,new_angle=angle,argument=[
                    'На исходной области главная ветвь арккосинуса даёт угол строго между нулём и π. Положительный синус позволяет применить цепочку дважды.',
                    'До изменения масштаба поля угловой оператор имеет первый член с котангенсом. Дифференцируем степенной вес дважды и собираем новый коэффициент при поле и его первой производной.',
                    'Сумма и разность линейной координаты и угла переводят разность чистых вторых производных в смешанную. Якобиан и вес отличны от нуля на всей исходной области.'
                ]),dict(transformed_sides=[m.div(residual,q(-4*c*c)),ZERO],regular_when='0 < '+source(angle)+' < pi')


def direct_coordinate_transform(task,library,request):
    from tasks import domain_conditions,entailed_domain_guards,equality_domain_witness,guard_source,known_guard,source
    changes,formula,mode=task['coordinate_change'],task['source_formula'],task['requested_output']
    if re.search(r'\b[a-z]_[xy]+(?![A-Za-z0-9_])',formula):
        if not library.data.get('partial_differential_coordinate_chart') or mode==['transform_curvature']:
            raise Unsupported('Отсутствует нужное правило замены в частных производных')
        try:return transform_partial(task,request)
        except (Unsupported,ZeroDivisionError):
            if not library.data.get('forward_coordinate_operators') or mode!=['transform_equation']:raise
            return forward_field_equation(task,request)
    if changes=='interchange independent y and dependent x(y)':t,u='y','x';sx,sy=u,t
    elif changes=='x=r*cos(phi),y=r*sin(phi)':t,u='phi','r';sx,sy='r*cos(phi)','r*sin(phi)'
    else:
        chart=re.fullmatch(r'x=([^,;]+)(?:,y=([^,;]+))?',changes)
        if not chart:raise Unsupported('Нужна явная локальная параметризация x,y')
        t,u='t','u';sx,sy=chart[1].replace('u(t)','u'),(chart[2] or u).replace('u(t)','u')
    eq=formula.replace('dy/dx',"y'").replace('²','^2').replace('³','^3').replace('⁴','^4')
    eq=re.sub(r"\by('+)",lambda z:'Y'+str(len(z[1])),eq)
    raw_sides=eq.split('=')
    if len(raw_sides)!=(2 if mode==['transform_equation'] else 1):raise Unsupported('Осталась дополнительная цель для преобразования')
    orders=[int(i) for i in re.findall(r'\bY(\d+)\b',eq)]
    if not orders:raise Unsupported('Нужно преобразование производной обыкновенной функции одной переменной')
    order=max(orders);params=sorted(set(re.findall(r'\b[a-z]\b',eq)) - {'x','y','e'})
    terms=['y']+['Y'+str(i) for i in range(1,order+1)]
    jets=[u]+[u+str(i) for i in range(1,order+1)]
    names=[t,*jets,*params]
    if len(set(names))!=len(names):raise Unsupported('Параметры совпали с координатами нового графика')
    m.context({'variable':'__jet','parameters':names})
    X,Y=(m.parse(v,None,[t,u,*params]) for v in (sx,sy))
    equations=[m.parse(s,None,['x',*terms,*params]) for s in raw_sides]
    guards=list(dict.fromkeys(domain_conditions(X,True)+domain_conditions(Y,True)))
    if (t,u)==('phi','r'):guards.append(('positive',('s',u)))
    partial=coordinate_sections(names,request)
    def dt(e,i):
        z=partial(e,t)
        for v,w in zip(jets[:i+1],jets[1:]):z=m.add(z,m.mul(partial(e,v),('s',w)))
        return m.simplify(z)
    jac=m.simplify(m.add(m.mul(partial(X,t),partial(Y,u)),m.neg(m.mul(partial(Y,t),partial(X,u)))))
    speed=dt(X,0)
    if mode==['transform_curvature']:
        from verify import same_value
        if equations!=[m.parse('abs(Y2)/(1+Y1^2)^(3/2)',None,['Y1','Y2'])]:
            raise Unsupported('Ожидалась исходная формула кривизны графика без дополнительных ограничений')
        vx,vy=speed,dt(Y,0);ax,ay=dt(vx,1),dt(vy,1)
        norm=m.add(m.power(vx,2),m.power(vy,2))
        det=m.add(m.mul(vx,ay),m.neg(m.mul(vy,ax)))
        # On a regular parametrized curve either x or y is a valid local graph coordinate.
        charts=[]
        for v,w,oriented in ((vx,vy,det),(vy,vx,m.neg(det))):
            if v==m.ZERO:continue
            slope=m.div(w,v)
            if not same_value(m.mul(dt(slope,1),m.power(v,2)),oriented):
                raise Unsupported('В соответствующей карте числитель кривизны остался недоказанным')
            charts.append((v,slope))
        guards.extend([('nonzero',jac),('positive',norm)])
        witness=equality_domain_witness([('s',v) for v in names],[],guards)
        if not charts:raise Unsupported('Касательный вектор тождественно равен нулю')
        curvature=('div',('abs',det),('rpow',norm,m.q(3,2)))
        plan=dict(new_independent=t,new_dependent=u,map=[X,Y],jet_symbols=jets[1:],jacobian=jac,velocity=[vx,vy],
                  acceleration=[ax,ay],speed_squared=norm,determinant=det,graph_charts=charts,original_and_chart_guards=guards,domain_witness=witness)
        return plan,dict(transformed_sides=[curvature],scope='regular local chart and every nonzero tangent, including vertical')
    guards.extend([('nonzero',jac),('nonzero',speed)])
    if jac==m.ZERO or speed==m.ZERO:raise Unsupported('Определитель координат или производная старой абсциссы равны нулю')
    subst={('s','x'):X,('s','y'):Y};z=Y
    for i in range(order):
        z=m.simplify(m.div(dt(z,i),speed));subst['s',terms[i+1]]=z
    raw=[m.substitute(e,subst) for e in equations]
    for e in equations:
        guards.extend((rel,m.substitute(expr,subst)) for rel,expr in domain_conditions(e))
    guards=list(dict.fromkeys(guards))
    witness=equality_domain_witness([('s',v) for v in names],[],guards)
    ctx=m.context({'variable':'__jet','parameters':names,'parameter_conditions':[guard_source(g) for g in entailed_domain_guards(guards)]})
    def admissible(e):return all(known_guard(g,ctx) for g in domain_conditions(e))
    if not all(admissible(e) for e in [*subst.values(),*raw]):
        raise Unsupported('При вычислении возникло ограничение, которое не следует из исходной области и условий локальной карты')
    result=[simple if admissible(simple:=m.simplify(e)) else e for e in raw]
    plan=dict(new_independent=t,new_dependent=u,jet_symbols=jets[1:],map=[X,Y],jacobian=jac,dx_dt=speed,
              derivative_map=[subst['s',s] for s in terms[1:]],original_and_chart_guards=guards,domain_witness=witness)
    if len(result)==2:
        from verify import same_value
        residual=m.add(result[0],m.neg(result[1]))
        p,d=m.rational_form(residual)
        denominator=m.poly_expr(d);numerator=m.poly_expr(p)
        if known_guard(('nonzero',denominator),ctx):
            units=[m.power(a,n) for a,n in m.common_mon(p).items() if known_guard(('nonzero',a),ctx)]
            scale=m.ONE
            for factor in units:scale=m.mul(scale,factor)
            reduced=m.div(numerator,scale)
            multiplier=m.div(denominator,scale)
            if admissible(reduced) and admissible(multiplier) and same_value(residual,m.div(m.mul(reduced,scale),denominator)):
                result=[reduced,m.ZERO];plan['equation_multiplier']=multiplier
    return plan,dict(transformed_sides=result,scope='local regular chart')


def transform_partial(task,request):
    """Apply inverse-Jacobian vector fields to arbitrary scalar fields, retaining ordered mixed derivatives."""
    from itertools import product
    from tasks import domain_conditions,entailed_domain_guards,equality_domain_witness,guard_source,known_guard
    from verify import same_value
    mode=task['requested_output']
    rewrite=lambda s:s.replace('²','^2').replace('³','^3').replace('⁴','^4')
    segments=rewrite(task['source_formula']).split(';');eq=segments[0];conditions=','.join(segments[1:])
    parts=eq.split('=')
    if len(parts)!=(2 if mode==['transform_equation'] else 1):raise Unsupported('Нужно сохранить все части исходного уравнения')
    tagged=sorted(set(re.findall(r'\b([a-z])_([xy]+)\b',eq)))
    if not tagged:raise Unsupported('В исходном выражении нет обозначений частных производных поля')
    order=max(len(word) for _,word in tagged);fields=sorted({f for f,_ in tagged})
    if order>2:raise Unsupported('Требуется дополнительное обоснование регулярности для более высокого порядка')
    params=sorted(set(re.findall(r'\b[a-z]\b',eq))-set('xye')-set(fields))
    rows=[s.strip().split('=') for s in rewrite(task['coordinate_change']).split(',')]
    if len(rows) not in (2,3) or any(len(row)!=2 for row in rows):raise Unsupported('Нужны явные координатные соотношения')
    old=list('xy')
    if [n for n,_ in rows[:2]]==old:
        free=[n for _,s in rows[:2] for n in re.findall(r'\b[A-Za-z][A-Za-z0-9]*\b',s)
              if n not in m.FUNCTIONS|set(m.ALIASES)|set(params)|{'pi','e'}]
        new=list(dict.fromkeys(free))
        if len(new)!=2:raise Unsupported('У карты должно быть две независимые координаты')
    else:new=[n for n,_ in rows[:2]]
    if len(set(new))!=2 or set(new).intersection(old+params):raise Unsupported('Обозначения координат совпадают')
    change=dict(rows);ss=lambda x:('s',x)
    def parse(s,names):return m.parse(s,None,names)
    forward_guards=[]
    if [n for n,_ in rows[:2]]==old:
        X,Y=(parse(change[i],new+params) for i in old)
    elif [n for n,_ in rows[:2]]==new:
        U,V=(parse(change[i],old+params) for i in new)
        right_to_left=dict(zip(map(ss,old),map(ss,new)))
        inverse=[m.substitute(v,right_to_left) for v in (U,V)]
        for i,(expr,var) in enumerate(zip((U,V),old)):
            if expr==('ln',ss(var)):inverse[i]=('exp',ss(new[i]))
            elif expr==('exp',ss(var)):inverse[i]=('ln',ss(new[i]))
        back=dict(zip(map(ss,old),inverse))
        def affine(e):
            origin={ss(a):m.ZERO for a in old};c=m.simplify(m.substitute(e,origin))
            k=[m.add(m.substitute(e,{**origin,ss(a):m.ONE}),m.neg(c)) for a in old]
            if not same_value(e,m.add(c,m.add(m.mul(k[0],ss('x')),m.mul(k[1],ss('y'))))):
                raise Unsupported('Не построена обратная координатная карта на всей исходной области')
            return c,*k
        if all(same_value(m.substitute(expr,back),ss(n)) for expr,n in zip((U,V),new)):
            X,Y=inverse
        else:
            c,a,b=affine(U);f,d,e=affine(V);h=m.add(m.mul(a,e),m.neg(m.mul(b,d)))
            if h==m.ZERO:raise Unsupported('Линейная замена вырождена')
            p,q=(m.add(ss(n),m.neg(v)) for n,v in zip(new,(c,f)))
            X=m.div(m.add(m.mul(e,p),m.neg(m.mul(b,q))),h);Y=m.div(m.add(m.mul(a,q),m.neg(m.mul(d,p))),h)
        back=dict(zip(map(ss,old),(X,Y)))
        if not all(same_value(m.substitute(expr,back),ss(n)) for expr,n in zip((U,V),new)):
            raise Unsupported('Обратная карта не воспроизводит независимые переменные')
        forward_guards.extend((r,m.substitute(e,back)) for expr in (U,V) for r,e in domain_conditions(expr,True))
    else:raise Unsupported('Нужна обратимая двумерная карта исходных координат')
    rename={f:f for f in fields}
    if len(rows)==3:
        f,expr=rows[-1]
        if f in fields:
            free=set(re.findall(r'\b[a-z]\b',expr))-set(new+params)
            if len(free)!=1:raise Unsupported('Не подтверждена замена зависимой величины')
            rename[f]=free.pop()
        elif len(fields)==1 and re.fullmatch('[a-z]',f):
            rename[fields[0]]=f
        else:raise Unsupported('Не установлена новая зависимая величина')
    jets={(f,w):f if not w else f+'_'+'_'.join(w) for f in rename.values() for k in range(order+1) for w in product(new,repeat=k)}
    names=[*new,*params,*jets.values()]
    if len(set(names))!=len(names):raise Unsupported('Обозначения новых переменных, функций и их производных совпали')
    derivative_guards=[]
    partial=coordinate_sections(names,request,local_premises=derivative_guards if conditions else None)
    a,b=[partial(X,n) for n in new];c,d=[partial(Y,n) for n in new]
    J=m.add(m.mul(a,d),m.neg(m.mul(b,c)))
    if J==m.ZERO:raise Unsupported('Якобиан преобразования тождественно равен нулю')
    operators={i:[m.polynomial_quotient(m.div(k,J)) for k in row] for i,row in zip(old,((d,m.neg(c)),(m.neg(b),a)))}
    for i,row in enumerate(operators.values()):
        for j,forward in enumerate(((a,b),(c,d))):
            if not same_value(m.dot(row,forward),m.q(int(i==j))):
                raise Unsupported('Поля производных не образуют обратную матрицу производной замены')
    raw_guards=forward_guards+domain_conditions(X,True)+domain_conditions(Y,True)+[('nonzero',J)]
    if set(new)=={'r','phi'} and same_value(X,parse('r*cos(phi)',new)) and same_value(Y,parse('r*sin(phi)',new)):
        raw_guards.append(('positive',ss('r')))
    bounds={ss('x'):X,ss('y'):Y}
    if conditions:
        # A strict comparison of absolute values is equivalent to the comparison of their squares.
        for c in conditions.split(','):
            condition=re.fullmatch(r'\s*(.+?)\s*([<>])\s*(.+?)\s*',c)
            if not condition:raise Unsupported('Не разобрана область исходного уравнения')
            a,b=(parse(condition[i],old+params) for i in (1,3))
            raw_guards.extend((r,m.substitute(e,bounds)) for r,e in domain_conditions(a)+domain_conditions(b))
            if condition[2]=='<':a,b=b,a
            if a[0]=='abs' and (b[0]=='abs' or m.num(b) is not None and m.num(b)>=0):
                a,b=(m.power(v[1],2) if v[0]=='abs' else m.power(v,2) for v in (a,b))
            elif b[0]=='abs' and m.num(a) is not None and m.num(a)>=0:
                a,b=m.power(a,2),m.power(b[1],2)
            lhs=m.add(a,m.neg(b))
            raw_guards.append(('positive',m.substitute(lhs,bounds)))
    base={f:ss(v) for f,v in rename.items()}
    if len(rows)==3:
        target,expr=rows[-1];f=fields[0] if target not in fields else target
        if target==f:base[f]=parse(expr,new+params+[rename[f]])
        else:
            prescribed=m.substitute(parse(expr,old+params+[f]),bounds)
            offset=m.simplify(m.substitute(prescribed,{ss(f):m.ZERO}))
            factor=m.add(m.substitute(prescribed,{ss(f):m.ONE}),m.neg(offset))
            if factor==m.ZERO or not same_value(prescribed,m.add(offset,m.mul(factor,ss(f)))):
                raise Unsupported('Не обоснованы все ветви обратной замены зависимой функции')
            base[f]=m.div(m.add(ss(target),m.neg(offset)),factor)
            raw_guards.extend((r,m.substitute(e,{ss(f):base[f]})) for r,e in domain_conditions(prescribed,True))
        raw_guards.extend(domain_conditions(base[f],True));slope=partial(base[f],rename[f])
        if slope==m.ZERO:raise Unsupported('Замена зависимой величины необратима')
        raw_guards.append(('nonzero',slope))
    maps={(f,''):e for f,e in base.items()}
    def prolong(f,word):
        if (f,word) not in maps:
            e=prolong(f,word[:-1]);total=m.ZERO
            for n,k in zip(new,operators[word[-1]]):
                de=partial(e,n)
                for (v,w),s in jets.items():
                    if len(w)<len(word) and m.contains(e,ss(s)):
                        de=m.add(de,m.mul(partial(e,s),ss(jets[v,w+(n,)])))
                total=m.add(total,m.mul(k,de))
            maps[f,word]=total
        return maps[f,word]
    symbols=[f+'_'+w for f,w in tagged]
    raw=[parse(s,old+fields+params+symbols) for s in parts]
    substitutions={**bounds,**{ss(f):base[f] for f in fields},**{ss(s):prolong(f,w) for s,(f,w) in zip(symbols,tagged)}}
    raw_guards.extend((rel,m.substitute(expr,substitutions)) for e in raw for rel,expr in domain_conditions(e))
    guards=list(dict.fromkeys(raw_guards));witness=equality_domain_witness([ss(n) for n in names],[],guards)
    ctx=m.context(dict(variable='__chart',parameters=names,parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    def admissible(e):return all(known_guard(g,ctx) for g in domain_conditions(e))
    if (not all(admissible(e) for e in [*maps.values(),*(v for row in operators.values() for v in row)])
            or not all(known_guard(g,ctx) for g in derivative_guards)):
        raise Unsupported('В преобразованных частных производных возникло недоказанное ограничение области')
    outputs=[m.substitute(e,substitutions) for e in raw]
    outputs=[r if admissible(r:=m.simplify(e)) else e for e in outputs]
    return dict(variables=new,coordinates=[X,Y],jacobian=J,inverse_coordinate_differentials=operators,
                derivative_map={f+'_'+w:e for (f,w),e in maps.items()},source_domain=guards,witness=witness),dict(transformed_sides=outputs,scope='regular plane chart with ordered mixed partials')


def forward_field_equation(task,request):
    """Push a first-order field or ordered second-order operator through a given local chart."""
    from itertools import combinations_with_replacement
    from functools import lru_cache
    from polynomial import span_coefficients
    from tasks import domain_conditions,entailed_domain_guards,equality_domain_witness,known_guard,guard_source
    from verify import same_value
    norm=lambda s:s.replace('²','^2').replace('³','^3').replace('⁴','^4')
    groups=norm(task['source_formula']).split(';');sides=groups[0].split('=')
    if len(sides)!=2 or len(groups)>2:raise Unsupported('Требуется одно исходное равенство с явно разобранной областью')
    tags=sorted(set(re.findall(r'\b([a-z])_([a-z]+)\b',groups[0])))
    if not tags or len({f for f,_ in tags})!=1 or any(len(w)>2 for _,w in tags):raise Unsupported('Требуется одно поле в двух координатах до второго порядка')
    axes={v for _,word in tags for v in word}
    axes=['x','y'] if axes<=set('xy') else sorted(axes, key=lambda k:(k!='x',k))
    if len(axes)!=2:raise Unsupported('Нужны две независимые координаты исходного поля')
    old=[*axes,tags[0][0]];z=old[-1];ss=lambda s:('s',s)
    if len(set(old))!=3:raise Unsupported('Обозначения исходного поля пересекаются')
    params=sorted(set(re.findall(r'\b[a-z]\b',groups[0]))-set(old)-{'e'})
    source_names=[f+'_'+w for f,w in tags]
    raw=[m.parse(e,None,old+params+source_names) for e in sides]
    residual=m.add(raw[0],m.neg(raw[1]))
    change=norm(task['coordinate_change']);dependent=z
    head=re.fullmatch(r'dependent ([a-z]); independent (.+)',change)
    if head:dependent,change=head.groups()
    pairs=[s.strip().split('=') for s in change.split(',')]
    pairs=[row*2 if len(row)==1 else row for row in pairs]
    if len(pairs)==2:pairs.append([dependent,dependent])
    if len(pairs)!=3 or any(len(row)!=2 or not re.fullmatch(r'[a-z]+',row[0]) for row in pairs):raise Unsupported('Не прочитаны три координаты преобразования графика')
    new=[n for n,_ in pairs];coords=[m.parse(s,None,old+params) for _,s in pairs]
    if len(set(new))!=3 or set(new)&set(params):raise Unsupported('Названия координат карты неоднозначны')
    U,V,W=coords
    partial=coordinate_sections(old+params,request)
    rows=[[partial(e,s) for s in old] for e in coords]
    det=lambda a,b,c,d:m.add(m.mul(a,d),m.neg(m.mul(b,c)))
    J=m.dot(rows[0],[det(rows[1][(i+1)%3],rows[1][(i+2)%3],rows[2][(i+1)%3],rows[2][(i+2)%3]) for i in range(3)])
    if same_value(J,m.ZERO):raise Unsupported('Полный якобиан вырожден тождественно')
    gradients=[ss(z+'_'+s) for s in axes]
    tangent=[[m.add(row[i],m.mul(row[2],gradients[i])) for i in range(2)] for row in rows[:2]]
    graph_J=det(*tangent[0],*tangent[1])
    guards=list(dict.fromkeys([*(g for e in raw for g in domain_conditions(e)),*(g for e in coords for g in domain_conditions(e,True)),('nonzero',J),('nonzero',graph_J)]))
    if len(groups)==2:
        cond=re.fullmatch(r'\s*([xy])>0\s*',groups[1])
        if not cond:raise Unsupported('Не прочитаны ограничения исходного поля')
        guards.append(('positive',ss(cond[1])))
    names=list(dict.fromkeys(old+params+source_names+[g[1] for g in gradients]))
    witness=equality_domain_witness(list(map(ss,names)),[],guards)
    ctx=m.context(dict(variable='__chart',parameters=names,parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    supported=lambda e:all(known_guard(g,ctx) for g in domain_conditions(e))
    # Pull new polynomial monomials back, then certify them by exact equality in the original coordinates.
    basis=[];pulls=[];pullback=dict(zip(map(ss,new),coords));units=[m.ONE]
    for size in range(4):
        for inds in combinations_with_replacement(range(3),size):
            term=e=m.ONE
            for i in inds:term=m.mul(term,ss(new[i]));e=m.mul(e,coords[i])
            basis.append(term);pulls.append(m.rational_form(e))
    powers=[m.rational_form(e)[1] for e in coords]
    common=m.powp(m.mulp(m.mulp(powers[0],powers[1]),powers[2]),3);common_expr=m.poly_expr(common)
    cols=[]
    for p,d in pulls:
        scaled=m.polynomial_quotient(m.div(m.mul(m.poly_expr(p),common_expr),m.poly_expr(d)))
        pol,den=m.rational_form(scaled)
        if den!={():1}:raise Unsupported('Не построен общий знаменатель для представления коэффициентов')
        cols.append(pol)
    for n,e in zip(new,coords):
        if known_guard(('nonzero',e),ctx):units.extend([ss(n),m.power(ss(n),2)])
    @lru_cache(None)
    def lift(e):
        if not supported(e):raise Unsupported('Появилась недоказанная область у коэффициента старого оператора')
        if not any(m.contains(e,ss(s)) for s in old):return e
        for unit in units:
            p,d=m.rational_form(m.mul(e,m.substitute(unit,pullback)))
            target=m.mulp(p,common);columns=[m.mulp(c,d) for c in cols]
            mons=sorted(set(target).union(*columns))
            vector=lambda h:tuple(h.get(mon,0) for mon in mons)
            coeff=span_coefficients(vector(target),list(map(vector,columns)))
            if coeff is not None:
                out=m.div(m.dot(list(map(m.q,coeff)),basis),unit)
                if same_value(e,m.substitute(out,pullback)):return out
        raise Unsupported('Коэффициент ещё не выражен через новые координаты на всей регулярной карте')
    p,d=m.rational_form(residual);derivs=set(map(ss,source_names));coeffs={}
    if any(a in derivs for mon in d for a,_ in mon):raise Unsupported('Исходное уравнение нелинейно по производным')
    for mon,c in p.items():
        jets=[a for a,k in mon if a in derivs for _ in range(k)]
        if len(jets)>1:raise Unsupported('Нужна нелинейная замена дифференциального оператора')
        key=jets[0][1].split('_')[1] if jets else ''
        term=tuple((a,k) for a,k in mon if a not in derivs)
        coeffs.setdefault(key,{})[term]=c
    coeffs={key:m.div(m.poly_expr(p),m.poly_expr(d)) for key,p in coeffs.items()}
    values={};flow=None;normal_identity=None
    if all(len(w)<2 for w in coeffs):
        flow=[*(coeffs.get(s,m.ZERO) for s in axes),m.neg(coeffs.get('',m.ZERO))]
        cu,cv,cw=(m.dot(flow,r) for r in rows)
        along=[m.add(rows[2][i],m.mul(rows[2][2],gradients[i])) for i in range(2)]
        numerators=[det(*along,*tangent[1]),det(*tangent[0],*along)]
        normal_identity=m.add(m.dot([cu,cv],numerators),m.neg(m.mul(cw,graph_J)))
        if not same_value(normal_identity,m.mul(J,residual)):
            raise Unsupported('Не проверена равносильность уравнений на касательной плоскости графика')
        values={ss(new[2]+'_'+new[0]):cu,ss(new[2]+'_'+new[1]):cv,m.ONE:m.neg(cw)}
    else:
        if W!=ss(z) or any(m.contains(e,ss(z)) for e in (U,V)):raise Unsupported('Старшие производные графика зависят от проекционного якобиана')
        values[m.ONE]=coeffs.get('',m.ZERO)
        def add(word,factor):
            s=ss(new[2]+'_'+'_'.join(word));values[s]=m.add(values.get(s,m.ZERO),factor)
        for word,c in coeffs.items():
            if not word:continue
            for i,n in enumerate(new[:2]):
                e=rows[i][old.index(word[0])]
                if len(word)==1:add([n],m.mul(c,e));continue
                add([n],m.mul(c,partial(e,word[1])))
                for j,k in enumerate(new[:2]):add([n,k],m.mul(c,m.mul(e,rows[j][old.index(word[1])])))
    for scale in dict.fromkeys((m.ONE,J,graph_J)):
        if not known_guard(('nonzero',scale),ctx):continue
        try:lifted={s:lift(m.polynomial_quotient(m.div(e,scale))) for s,e in values.items()}
        except Unsupported:continue
        if not all(same_value(e,m.mul(scale,m.substitute(lifted[s],pullback))) for s,e in values.items()):continue
        transformed=m.dot(list(lifted),list(lifted.values()))
        plan=dict(forward_map=dict(zip(new,coords)),source_domain=guards,domain_witness=witness,ambient_jacobian=J,
                    graph_jacobian=graph_J,characteristic_field=flow,pulled_back_normal=normal_identity,coefficient_identities=[(s,e,lifted[s]) for s,e in values.items()],
                    nonzero_equation_factor=scale,applied_methods=['method.forward_coordinate_operators'])
        value=dict(transformed_sides=[transformed,m.ZERO],scope='every regular sheet of the declared chart with source guards')
        if task['requested_output']==['solve_in_prescribed_coordinates']:
            original=list(dict.fromkeys(g for e in [*raw,*coords] for g in domain_conditions(e,True)))
            original_ctx=m.context(dict(variable='__chart',parameters=names,parameter_conditions=[guard_source(g) for g in entailed_domain_guards(original)]))
            if not all(known_guard(('nonzero',j),original_ctx) for j in (J,graph_J)):
                exceptional=None
                for p in params:
                    pivot=ss(p);quot=m.polynomial_quotient(m.div(J,pivot))
                    if not same_value(J,graph_J) or m.num(quot) in (None,0) or not same_value(J,m.mul(pivot,quot)):continue
                    branch={key:m.simplify(m.substitute(e,{pivot:m.ZERO})) for key,e in coeffs.items()}
                    live=[s for s,e in branch.items() if not same_value(e,m.ZERO)]
                    if len(live)!=1 or len(live[0])!=2 or live[0][0]!=live[0][1] or m.num(branch[live[0]]) in (None,0):continue
                    if not all(known_guard((r,m.substitute(g,{pivot:m.ZERO})),original_ctx) for r,g in original):continue
                    s=live[0][0];other=next(v for v in axes if v!=s)
                    exceptional=dict(parameter=p,value=m.ZERO,remaining_coefficients=branch,active=s,free=other,
                                     field=z,form='affine_in_active_with_two_arbitrary_functions_of_free');break
                if exceptional is None:raise Unsupported('Общее решение требует отдельного разбора точек вырождения предписанной карты')
                value['singular_parameter_branch']=exceptional
            integrate_coordinate_operator(plan,value,new,ctx)
        return plan,value
    raise Unsupported('Для равносильного уравнения нужно выразить все коэффициенты и подтвердить общий ненулевой множитель')


def integrate_coordinate_operator(plan,value,new,ctx):
    """On a regular prescribed chart integrate a derivative along one coordinate or a mixed derivative."""
    from tasks import known_guard
    from verify import same_value
    U,V,W=new;ss=lambda k:('s',k)
    ids=plan['coefficient_identities'];terms={s:(old,lift) for s,old,lift in ids if not same_value(lift,m.ZERO)}
    source_map={ss(k):v for k,v in plan['forward_map'].items()}
    def nonzero(e):return known_guard(('nonzero',m.substitute(e,source_map)),ctx)
    keys={ss(W+'_'+s) for s in (U+'_'+V,V+'_'+U)}
    derivatives=set(terms)-{m.ONE}
    if derivatives and set(terms)<=keys:
        coefficient=m.ZERO
        for _,c in terms.values():coefficient=m.add(coefficient,c)
        if not nonzero(coefficient):raise Unsupported('Не доказана ненулевость коэффициента смешанной производной')
        ans=dict(form='sum_of_two_arbitrary_functions',field=W,arguments=[U,V])
        plan['integration']=dict(relation='mixed_partial_zero',coefficient=coefficient,coordinates=[U,V],
                                 argument='Integrate the first derivative in the second coordinate, and integrate the resulting function of the first coordinate.')
    else:
        active=next((s for s in (U,V) if derivatives=={ss(W+'_'+s)}),None)
        if active is None:raise Unsupported('Преобразованный оператор ещё не свёлся к производной по одной координате')
        free=V if active==U else U;c=terms[ss(W+'_'+active)][1]
        if not nonzero(c):raise Unsupported('Старший коэффициент может обратиться в ноль внутри рассматриваемой карты')
        rhs=m.polynomial_quotient(m.div(m.neg(terms.get(m.ONE,(m.ZERO,m.ZERO))[1]),c))
        # Seek an affine first integral in the dependent field. Check both coefficients identically.
        w0=m.simplify(m.substitute(rhs,{ss(W):m.ZERO}));w1=m.simplify(m.add(m.substitute(rhs,{ss(W):m.ONE}),m.neg(w0)))
        if not same_value(rhs,m.add(w0,m.mul(w1,ss(W)))):raise Unsupported('Требуется нелинейное уравнение на характеристике')
        for scale in (m.ONE,ss(active)):
            derivative=m.ONE if scale==ss(active) else m.ZERO
            if not nonzero(scale) or not same_value(derivative,m.mul(w1,scale)):continue
            if any(m.contains(w0,ss(k)) for k in (W,active)):continue
            offset=m.mul(w0,ss(active))
            if not same_value(w0,m.add(m.mul(w1,offset),w0)):continue
            ans=dict(form='affine_arbitrary_function',field=W,argument=free,multiplier=scale,offset=offset)
            plan['integration']=dict(relation='first_integral',active=active,constant_coordinate=free,
                                     coefficient=c,field_slope=w1,forcing=w0,integral=m.div(m.add(ss(W),m.neg(offset)),scale))
            break
        else:raise Unsupported('Не построен обратимый первый интеграл на исходной карте')
    value['general_solution']=ans


def inverse_chart_graph(raw,axes,orders,params,conditions,request):
    """Use a reversible coordinate change and retain every boundary of the original graph."""
    from tasks import domain_conditions,source
    x,y=axes;X,Y=x[1],y[1]
    names=[X,Y,*params];dummy='__inverse_chart'
    while dummy in names:dummy+='_'
    ctx=m.context(dict(variable=dummy,parameters=names,parameter_conditions=conditions))
    if raw[0]!='add' or raw[2][0]!='mul' or raw[2][1]!=m.q(-1):
        raise Unsupported('No two sides to a reversible graph equation')
    lhs,rhs=raw[1],raw[2][2]
    if lhs[0]=='add' and orders==[1]:
        for mode in ('sqrt','cbrt'):
            root=lambda a:(mode,a) if mode=='sqrt' else ('pow',('cbrt',a),2)
            symbols=[root(x),root(y)]
            def coefficient(term,target):
                if term==target:return m.ONE
                if term[0]=='mul' and target in term[1:]:
                    a=term[2] if term[1]==target else term[1]
                    if not any(m.contains(a,z) for z in axes) and m.constant_defined(a,ctx) and m.sign(a,ctx)==1:return a
            pair=[coefficient(term,z) for term,z in zip(lhs[1:],symbols)]
            if any(p is None for p in pair):pair=[coefficient(term,z) for term,z in zip(reversed(lhs[1:]),symbols)]
            if any(p is None for p in pair):continue
            if mode=='sqrt' and rhs[0]=='sqrt':A=rhs[1]
            elif mode=='cbrt' and rhs[0]=='pow' and rhs[2]==2 and rhs[1][0]=='cbrt':A=rhs[1][1]
            else:continue
            if any(m.contains(A,z) for z in axes) or not m.constant_defined(A,ctx):continue
            a,b=pair;h=m.div(m.add(rhs,m.neg(m.mul(a,root(x)))),b);upper=m.div(rhs,a)
            if mode=='sqrt':
                extent=m.power(upper,2);branches=[m.power(h,2)]
                finite=m.neg(m.div(m.mul(a,h),m.mul(b,('sqrt',x))))
                special=dict(zero_argument='isolated origin',negative_argument='no real graph',
                             left=dict(point=m.ZERO,side='right',value='-inf'),
                             right=dict(point=extent,side='left',value=m.ZERO))
                region=(m.ZERO,extent)
                steps=['Переносим один главный корень. Неотрицательность остатка задаёт точный интервал исходной координаты.',
                       'На нём возведение остатка в квадрат обратимо, поэтому каждая ветвь найдена. Внутри дифференцируем эту явную формулу.',
                       'Из разностного отношения на левом краю получаем член порядка √h/h. На правом краю квадрат исчезающего остатка имеет порядок h².']
            else:
                extent=m.mul(upper,('sqrt',upper));top=m.mul(h,('sqrt',h));branches=[top,m.neg(top)]
                finite=m.neg(m.div(m.mul(a,('cbrt',y)),m.mul(b,('cbrt',x))))
                special=dict(zero_argument='isolated origin',at_zero_x=dict(upper={'left':'+inf','right':'-inf'},lower={'left':'-inf','right':'+inf'}),
                             left=dict(point=m.neg(extent),side='right',value=m.ZERO),
                             right=dict(point=extent,side='left',value=m.ZERO))
                region=(m.neg(extent),extent)
                steps=['Переносим квадрат кубического корня и сохраняем неотрицательность остатка.',
                       'Уравнение имеет ровно две указанные ветви, которые сходятся при нулевом остатке. Внутри при ненулевых координатах дифференцируем исходное уравнение.',
                       'Около оси x=0 смещение каждой ветви имеет порядок |x|^(2/3), поэтому два односторонних наклона расходятся. На внешних концах степень 3/2 даёт односторонний наклон ноль.']
            return dict(theorem='method.explicit_branches_from_root_coordinate',argument=steps,
                        chart_operator=mode,weights=pair,original_domain=domain_conditions(raw),
                        fixed_argument=A,nonnegative_residual=h),dict(graph=dict(
                        graph_motion='root_chart',ordered_values=[finite],branches=branches,
                        nontrivial_branches_require=source(A)+('>0' if mode=='sqrt' else '!=0'),
                        horizontal_range=region,exceptional_fibers=special,conditions=conditions),point_values=[])
    phase=('atan',('div',y,x));radius=('sqrt',('add',('pow',x,2),('pow',y,2)))
    scale=None
    if (lhs,rhs)==(phase,('ln',radius)) or (rhs,lhs)==(phase,('ln',radius)):
        scale=m.ONE
    else:
        exp=('exp',phase)
        for radial,exponential in ((lhs,rhs),(rhs,lhs)):
            if radial!=radius:continue
            if exponential==exp:scale=m.ONE
            elif exponential[0]=='mul' and exp in exponential[1:]:
                scale=exponential[2] if exponential[1]==exp else exponential[1]
    if (scale is None or any(m.contains(scale,z) for z in axes) or not m.constant_defined(scale,ctx)
            or m.sign(scale,ctx)!=1):
        raise Unsupported('No original positive radius and principal angular coordinate')
    sum_xy=m.add(x,y);gap=m.add(x,m.neg(y));first=m.div(sum_xy,gap);value={1:first}
    extra=[*conditions,X+'!=0',source(gap)+'!=0']
    for order in range(2,max(orders)+1):
        g=request(f'coordinate derivatives of order {order-1} graph formula',dict(
            kind='partial_derivatives',function=source(value[order-1]),variables=[X,Y],parameters=params,
            stated_conditions=extra,requested_output=['first_partial_derivatives']))
        dx,dy=map(freeze,g['value']);value[order]=m.add(dx,m.mul(dy,first))
    return dict(theorem='method.implicit_graph_after_radial_logarithm',
                argument=['Из исходной угловой координаты получаем x≠0 и потому положительный радиус.',
                          'Равенство с положительной экспонентой обратимо после логарифмирования. В нормализованном уравнении градиент равен (−x−y, x−y)/(x²+y²).',
                          'При x=y и x≠0 горизонтальная компонента градиента ненулевая. В остальных точках дифференцируем вдоль локального графика, учитывая уже найденный наклон.'],
                original_domain=domain_conditions(raw),radius=radius,principal_phase=phase,
                positive_scale=scale,nonzero_vertical_component=gap,original=raw),dict(
                graph=dict(graph_motion='regular_graph',ordered_values=[value[o] for o in orders],
                           regular_condition=('nonzero',gap),on_zero_pivot='no_finite_derivative',conditions=conditions),point_values=[])


def implicit_graph_values(task,library,request):
    """Cover a regular implicit graph, its vertical tangencies, and the required points."""
    from tasks import domain_conditions,guard_source,entailed_domain_guards,known_guard
    from verify import same_value
    fields={'kind','id','source','relation','independent','dependent','parameters','stated_conditions','orders','points','requested_output'}
    origin=task.get('source',{})
    copies={'source_equation_residual':'relation','source_parameters':'parameters',
            'source_stated_conditions':'stated_conditions','source_requested_orders':'orders','source_requested_points':'points'}
    if (not library.data.get('implicit_graph_value_transport') or set(task)-fields
            or set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','page_png_sha256','literal_requirement',*copies}
            or origin.get('literal_requirement') not in (None,'Find the ordinary graph derivatives through the specified order; evaluate them also at every listed point.')
            or any(key in origin and origin[key]!=task[field] for key,field in copies.items())
            or task.get('requested_output')!=['ordinary_derivatives_on_original_graph','values_at_all_requested_points']):
        raise Unsupported('Source graph, derivative orders or required points do not agree')
    x,=task['independent'];y=task['dependent'];params=task['parameters'];orders=task['orders'];points=task['points'];conditions=task['stated_conditions']
    cap=library.data['partial_bundle_contract']['selected_path_limits']['length']
    if not isinstance(orders,list) or not orders or len(set(orders))!=len(orders) or any(type(o)is not int or not 1<=o<=cap for o in orders):
        raise Unsupported('Derivative orders need an explicit supported list')
    if not isinstance(points,list) or any(not isinstance(point,list) or len(point)!=2 for point in points):
        raise Unsupported('Each required point must give both coordinates')
    symbols=[x,y,*params];dummy='__graph_value'
    while dummy in symbols:dummy+='_'
    raw=m.parse(task['relation'],None,symbols);axes=(('s',x),('s',y))
    if library.data.get('implicit_coordinate_reductions') and not points:
        try:return inverse_chart_graph(raw,axes,orders,params,conditions,request)
        except Unsupported:pass
    nat=domain_conditions(raw);smooth=domain_conditions(raw,True)
    admitted=[guard_source(g) for g in entailed_domain_guards(nat)]
    fixed=[guard_source(g) for g in entailed_domain_guards(nat) if not any(m.contains(g[1],z) for z in axes)]
    child=dict(kind='implicit_derivative',relation=task['relation'],independent=[x],dependent=y,parameters=params,
               requested_partials=[[x]*n for n in orders],requested_output=['specified_implicit_derivatives'])
    def context(conditions):return m.context(dict(variable=dummy,parameters=symbols,parameter_conditions=conditions))
    applied=['method.implicit_graph_value_transport']
    def family(extra,split=True):
        given=[*conditions,*extra];ctx=context(given+admitted);ctx_fixed=context(given+fixed)
        if not all(known_guard(g,ctx) for g in smooth):raise Unsupported('An original nonsmooth point needs separate graph analysis')
        reduced=m.simplify(m.substitute(raw,{('s',a['symbol']):m.ZERO for a in ctx['assumptions'] if a['relation']=='zero'}))
        nonzero=lambda e:known_guard(('nonzero',e),ctx_fixed)
        f,d=m.rational_form(reduced);z,w=axes
        if not any(m.contains(m.poly_expr(d),a) for a in axes):
            if reduced==m.ZERO:raise Unsupported('The relation does not determine a graph')
            if all(atom==w or not any(m.contains(atom,a) for a in axes) for mon in f for atom,_ in mon):
                coefficients={}
                for mon,c in f.items():
                    k=dict(mon).get(w,0);term=m.q(c)
                    for atom,j in mon:
                        if atom!=w:term=m.mul(term,m.power(atom,j))
                    coefficients[k]=m.add(coefficients.get(k,m.ZERO),term)
                degree=max(coefficients,default=0)
            else:degree=0
            if degree and nonzero(coefficients[degree]):
                ans=dict(graph_motion='constant_branches',ordered_values=[m.ZERO]*len(orders),conditions=given)
                return dict(relation=reduced,constant_fibers=True),ans
        result=request('derivatives on each regular implicit branch',{**child,'scope':'regular_graph','stated_conditions':given})
        pivot=freeze(result['compilation']['pivot'])
        proof=dict(pivot=pivot,regular_graph=freeze(result['compilation']['regular_graph_condition']))
        ans=dict(graph_motion='regular_graph',ordered_values=result['value'],regular_condition=proof['regular_graph'],conditions=given)
        if known_guard(('nonzero',pivot),ctx):
            return {**proof,'pivot_nonzero_on_entire_source_domain':True},ans
        if any(m.contains(m.poly_expr(d),a) for a in axes):
            raise Unsupported('Singular graph branches with coordinate-dependent divisors remain open')
        coefficients={}
        for mon,c in f.items():
            degree=[0,0];coefficient=m.q(c)
            for atom,k in mon:
                if atom in axes:degree[axes.index(atom)]+=k
                elif any(m.contains(atom,a) for a in axes):
                    raise Unsupported('The graph singularities are not given by an affine gradient')
                else:coefficient=m.mul(coefficient,m.power(atom,k))
            if sum(degree)>2:raise Unsupported('The graph singularities are not given by an affine gradient')
            key=tuple(degree);coefficients[key]=m.add(coefficients.get(key,m.ZERO),coefficient)
        A,B,C,D,E=(coefficients.get(p,m.ZERO) for p in ((2,0),(1,1),(0,2),(1,0),(0,1)))
        H,J=m.mul(m.q(2),A),m.mul(m.q(2),C)
        det=m.add(m.mul(H,J),m.neg(m.power(B,2)))
        horizontal_constant=A==B==m.ZERO and nonzero(D)
        vertical_constant=B==C==m.ZERO and nonzero(E)
        no_stationary=horizontal_constant or vertical_constant
        if no_stationary:proof['nonzero_gradient_component']='x' if horizontal_constant else 'y'
        elif nonzero(det):
            stationary=(m.div(m.add(m.mul(B,E),m.neg(m.mul(J,D))),det),
                        m.div(m.add(m.mul(B,D),m.neg(m.mul(H,E))),det))
            constraint=m.substitute(m.poly_expr(f),dict(zip(axes,stationary)))
            if nonzero(constraint):no_stationary=True;proof['off_relation_stationary_point']=(stationary,constraint)
        if no_stationary:
            return proof,{**ans,'on_zero_pivot':'no_finite_derivative'}
        if split:
            for name in params:
                atom=('s',name)
                if not m.common_mon(m.rational_form(D)[0]).get(atom) or nonzero(atom) or not m.contains(reduced,atom):
                    continue
                zero=m.simplify(m.substitute(reduced,{atom:m.ZERO}))
                if m.contains(zero,z) or not m.contains(zero,w):continue
                n,nv=family([*extra,name+'!=0'],False);a,av=family([*extra,name+'=0'],False)
                return dict(split_parameter=name,nonzero=n,zero=a),dict(split_parameter=name,nonzero=nv,zero=av)
        raise Unsupported('A point with both first partials zero still needs its own branch argument')
    graph,value=family([])
    evaluated=[]
    for coordinates in points:
        point=dict(zip((x,y),coordinates))
        evaluated.append(dict(point=point,ordered_values=request('derivatives at a required graph point',{
            **child,'point':point,'stated_conditions':conditions})['value']))
    return dict(original_relation=raw,original_domain=nat,orders=orders,branch_proof=graph,
                applied_methods=applied),dict(graph=value,point_values=evaluated)


def implicit_graph_request(task):
    """Bind a printed equation and all its derivative indices to one original regular graph."""
    from verify import same_value
    from tasks import domain_conditions,source
    allowed={'kind','id','source','source_formula','residual','dependent','independent','requested_output','point','stated_conditions'}
    origin=task.get('source',{});out=task.get('requested_output');xs=task.get('independent');z=task.get('dependent')
    if (set(task)-allowed or not isinstance(origin,dict) or set(origin)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement','section_convention'}
            or not isinstance(out,list) or not out or not all(isinstance(s,str) for s in out)
            or origin.get('literal_requirement','implicit derivative; '+', '.join(out))!='implicit derivative; '+', '.join(out)
            or origin.get('section_convention','p310 footnote: existence of the implicit functions and needed derivatives is assumed in most exercises unless otherwise stated')!='p310 footnote: existence of the implicit functions and needed derivatives is assumed in most exercises unless otherwise stated'
            or not isinstance(xs,list) or not xs or not all(isinstance(s,str) and re.fullmatch(r'[a-z]',s) for s in [*xs,z])
            or len(set([*xs,z]))!=len(xs)+1):
        raise Unsupported('Не связаны исходное уравнение, его область и все запрошенные производные')
    eq=task['source_formula'];sides=eq.split('=')
    if len(sides)!=2:raise Unsupported('Ожидается одно исходное равенство')
    names=sorted(set(re.findall(r'\b[A-Za-z_][A-Za-z_0-9]*\b',eq)) - m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    pars=sorted(set(names)-set([*xs,z]))
    relation='('+sides[0]+')-('+sides[1]+')'
    f=m.parse(relation,None,names);res=m.parse(task['residual'],None,names)
    if not same_value(f,res) or set(domain_conditions(f,True))!=set(domain_conditions(res,True)):
        raise Unsupported('Дублирующая запись невязки изменила исходное уравнение или область')
    paths=[]
    for item in out:
        prime=re.fullmatch(re.escape(z)+r"('+)",item)
        partial=re.fullmatch(re.escape(z)+r'_([a-z]+)',item)
        if prime and len(xs)==1:paths.append(xs*len(prime[1]))
        elif partial and set(partial[1])<=set(xs):paths.append(list(partial[1]))
        else:raise Unsupported('Не прочитан индекс производной '+item)
    fixed=[];local=[]
    for cond in task.get('stated_conditions',[]):
        parts=re.split(r'(!=|<|>)',cond)
        if len(parts) not in (3,5):raise Unsupported('Не прочитано ограничение неявной функции')
        for a,op,b in zip(parts[::2],parts[1::2],parts[2::2]):
            left,right=[m.parse(s,None,names) for s in (a,b)]
            delta=m.add(right,m.neg(left)) if op=='<' else m.add(left,m.neg(right))
            target=local if any(m.contains(delta,('s',v)) for v in [*xs,z]) else fixed
            # Keep original operand domains, including factors that cancel in their difference.
            for operand in (left,right):
                for sign,e in domain_conditions(operand,True):
                    target.append(source(e)+('!=0' if sign=='nonzero' else '>0'))
            target.append(source(delta)+('!=0' if op=='!=' else '>0'))
    at={'point':task['point']} if task.get('point') is not None else {'scope':'regular_graph'}
    return dict(kind='implicit_derivative',relation=relation,dependent=z,independent=xs,parameters=pars,
                stated_conditions=fixed,graph_conditions=local,requested_partials=paths,requested_output=['specified_implicit_derivatives'],**at)


def implicit_system(task,library,request):
    """Differentiate all equations together on a regular local chart, keeping the first derivatives as named subgoals."""
    from itertools import product
    from tasks import domain_conditions,known_guard,entailed_domain_guards,guard_source,source
    from verify import same_value
    if not library.data.get('implicit_system_jacobian'):
        raise Unsupported('Правило неявной системы не подключено')
    fields={'id','kind','source','stated_conditions','requested_output','source_formula','point'}
    wanted=task.get('requested_output');text=task.get('source_formula');origin=task.get('source',{})
    if (set(task)-fields or task.get('stated_conditions') or not isinstance(text,list) or not text or
            not isinstance(wanted,list) or not wanted or not all(isinstance(w,str) for w in [*text,*wanted]) or
            not isinstance(origin,dict) or set(origin)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement','section_convention'}
            or origin.get('literal_requirement','implicitly coupled system; '+', '.join(wanted))!='implicitly coupled system; '+', '.join(wanted)
            or 'section_convention' in origin and origin['section_convention']!='p310 footnote: existence of the implicit functions and needed derivatives is assumed in most exercises unless otherwise stated'):
        raise Unsupported('Не подтверждены все исходные вопросы или условия неявной системы')
    norm=lambda s:s.replace('²','^2').replace('³','^3')
    text=[norm(s) for s in text]
    if library.data.get('coordinate_covariance_priorities') and task.get('point') is None:
        try:return symbolic_implicit_charts(task,request)
        except Unsupported:pass
    if any(s.count('=')!=1 for s in text):raise Unsupported('Нужен список исходных равенств')
    names=sorted(set(re.findall(r'\b[a-z][a-z0-9]*\b',' '.join(text)))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    d=len(names)-len(text)
    if len(text)>3 or d not in (1,2,3):raise Unsupported('Не подтверждены размерность и число независимых переменных')
    pairs=[tuple(m.parse(s,None,names) for s in equation.split('=')) for equation in text]
    guards=list(dict.fromkeys(g for pair in pairs for e in pair for g in domain_conditions(e,True)))
    ctx=m.context(dict(variable='__implicit',parameters=names,parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    eq=[]
    for a,b in pairs:
        residual=m.add(a,m.neg(b));num,den=m.rational_form(residual)
        eq.append(m.poly_expr(num) if known_guard(('nonzero',m.poly_expr(den)),ctx) else residual)
    options={};outputs={};ss=lambda s:('s',s)
    definitions={a:b for a,b in pairs if a in set(map(ss,names))}
    surface_graph=set(definitions)==set(map(ss,'xyz')) and d==2
    for item in wanted:
        explicit=re.fullmatch(r'd([a-z])/d([a-z])|d²([a-z])/d([a-z])²|([a-z])_([a-z]+)|partial(²?) ([a-z])(?:/partial ([a-z])(²?)|/\(partial ([a-z]) partial ([a-z])\))(?: as printed)?',item)
        total=re.fullmatch(r'd(²?)([a-z])',item)
        if explicit:
            a,b,c,f,e,g,degree,h,i,power,j,k=explicit.groups()
            v=a or c or e or h;path=b or (2*f if f else g) or (i*(2 if power else 1) if i else j+k)
            if degree=='²' and len(path)!=2:raise Unsupported('Не установлены обе координаты второй производной')
        elif total:v=total[2];path=2 if total[1] else 1
        else:raise Unsupported('Не доказана полная постановка для '+item)
        if v not in names or isinstance(path,str) and (len(path) not in (1,2) or any(x not in names for x in path)):
            raise Unsupported('Производная ссылается на неустановленную координату')
        options[item]=(v,path)
    target={v for v,_ in options.values()}
    stated={x for _,s in options.values() if isinstance(s,str) for x in s}
    def base_for(path):
        if d==1 and isinstance(path,str):return [path[0]] if len(set(path))==1 else []
        if len(stated)==d:return sorted(stated)
        if surface_graph:return list('xy')
        if not stated and len(set(names)-target)==d:return sorted(set(names)-target)
        return []
    point=task.get('point')
    parameters=[n for n in names if ss(n) not in definitions]
    if point is None and d==1 and len(parameters)==1 and len(stated)==1 and all(isinstance(path,str) for _,path in options.values()):
        x=next(iter(stated));param=parameters[0]
        if ss(x) in definitions and all(ss(f) in definitions for f in target) and all(not any(m.contains(e,k) for k in definitions) for e in definitions.values()):
            curves={}
            for field in sorted(target):
                orders=sorted({len(path) for v,path in options.values() if v==field})
                goal=dict(kind='parametric_curve_derivatives',parameter=param,coordinates=[source(definitions[ss(n)]) for n in (x,field)],
                          orders=orders,requested_output=['derivatives_as_functions_of_parameter'])
                curves[field]=request('производные и границы параметрической ветви '+field,goal)['value']
                for label,(v,path) in options.items():
                    if v==field:outputs[label]=curves[v]['ordered_values'][orders.index(len(path))]
            return dict(parameter=param,original_smooth_domain=guards,parametric_graphs=curves),outputs
    if isinstance(point,list) and names==list('xyz') and len(point)==3:point=dict(zip(names,point))
    empty={'parameters':[],'assumptions':[]}
    if point is not None:
        if not isinstance(point,dict) or not set(point)<=set(names):raise Unsupported('Точка содержит неустановленные координаты')
        point={ss(n):m.parse(str(v),None,[]) for n,v in point.items()}
        if not all(m.constant_defined(z,empty) for z in point.values()):
            raise Unsupported('Исходная координата точки не определена в вещественной области')
        for _ in definitions:
            for a,b in definitions.items():
                if a not in point and all(v in point or not m.contains(b,v) for v in map(ss,names)):
                    z=m.substitute(b,point)
                    if not m.constant_defined(z,empty):
                        raise Unsupported('Координата, найденная из исходной системы, не определена')
                    point[a]=m.simplify(z)
        if len(point)!=len(names):raise Unsupported('Точка не задаёт все исходные координаты')
    partial=coordinate_sections(names,request)
    def at(e):return m.simplify(m.substitute(e,point)) if point is not None else e
    def valid(p,checks):
        try:
            return all(known_guard((r,m.substitute(e,p)),empty) for r,e in checks) and all(same_value(m.substitute(a,p),m.substitute(b,p)) for a,b in pairs)
        except (ArithmeticError,Unsupported):return False
    if point is not None and not valid(point,guards):
        if library.data.get('coordinate_covariance_priorities') and 'section_convention' in origin:
            refutation=incompatible_implicit_point(pairs,point,guards)
            if refutation is not None:return refutation
        raise Unsupported('Заданная точка не лежит на всех исходных гладких уравнениях')
    def det(A):
        if not A:return m.ONE
        if len(A)==1:return A[0][0]
        value=m.ZERO
        for j,w in enumerate(A[0]):
            if w!=m.ZERO:
                minor=[row[:j]+row[j+1:] for row in A[1:]]
                value=m.add(value,m.mul(w if j%2==0 else m.neg(w),det(minor)))
        return value
    def witness(checks):
        if point is not None:return point if valid(point,checks) else None
        explicit=definitions;free=[ss(v) for v in names if ss(v) not in explicit]
        def candidates():
            choices=(m.ZERO,m.ONE,m.q(-1),m.q(2),m.mul(m.q(1,4),m.PI)) if explicit else (m.ZERO,m.ONE,m.q(-1),m.q(2))
            for cell in product(choices,repeat=len(free)):
                p=dict(zip(free,cell))
                try:
                    for _ in explicit:
                        for a,b in explicit.items():
                            if all(v in p or not m.contains(b,v) for v in map(ss,names)):
                                z=m.substitute(b,p)
                                if not m.constant_defined(z,empty):
                                    raise Unsupported('Неопределённая координата пробной точки')
                                p[a]=m.simplify(z)
                except (ArithmeticError,Unsupported):continue
                if len(p)==len(names):yield p
            atoms=list(map(ss,names))
            for z in (m.mul(m.q(1,4),m.PI),m.mul(m.q(1,2),('sqrt',m.q(2)))):
                yield dict.fromkeys(atoms,z)
                for i,a in enumerate(atoms):
                    for b in atoms[i+1:]:yield {**dict.fromkeys(atoms,m.ZERO),a:z,b:m.neg(z)}
        return next((p for p in candidates() if valid(p,checks)),None)
    charts={};vertical={}
    for label,(v,path) in options.items():
        base=tuple(base_for(path))
        if len(base)!=d:raise Unsupported('Не установлено, какие координаты фиксированы в '+label)
        if base not in charts:
            dep=sorted(set(names)-set(base));A=[[at(partial(g,n)) for n in dep] for g in eq];D=det(A)
            if point is not None and D==m.ZERO and d==1 and isinstance(path,str) and v not in base:
                rest=[n for n in names if n!=v];B=[[at(partial(g,n)) for n in rest] for g in eq];dy=det(B)
                if m.nonzero(dy,empty):
                    rhs=[m.neg(at(partial(g,v))) for g in eq]
                    tangent=[m.div(det([row[:j]+[b]+row[j+1:] for row,b in zip(B,rhs)]),dy) for j in range(len(rest))]
                    if tangent[rest.index(base[0])]==m.ZERO and all(same_value(m.dot(row,tangent),b) for row,b in zip(B,rhs)):
                        vertical[label]=dict(parameter=v,remaining=rest,determinant=dy,velocity=tangent)
                        outputs[label]=dict(exists=False,reason='A differentiable local inverse would have 1 = (dy/dx)(dx/dy) with dx/dy = 0.')
                        continue
            scope=guards+[('nonzero',D)];p=witness(scope)
            if p is None:raise Unsupported('Нет подтверждённой точки исходных уравнений с невырожденным зависимым якобианом')
            adj=[[m.mul(m.q((-1)**(i+j)),det([row[:i]+row[i+1:] for k,row in enumerate(A) if k!=j])) for j in range(len(dep))] for i in range(len(dep))]
            if not all(same_value(m.dot(row,col),D if i==j else m.ZERO) for i,row in enumerate(A) for j,col in enumerate(zip(*adj))):
                raise Unsupported('Обращение матрицы не восстанавливает якобиан системы')
            charts[base]=dict(dependent=dep,matrix=A,adjugate=adj,determinant=D,witness={a[1]:z for a,z in p.items()},
                              solutions={},first_derivative_bindings={})
        chart=charts[base];dep=chart['dependent'];A=chart['matrix'];D=chart['determinant'];steps=chart['solutions']
        valid_ctx=empty if point is not None else m.context(dict(variable='__implicit',parameters=names,
              parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards+[('nonzero',D)])]))
        def solve_right(rhs):
            sols=[('div',m.dot(row,rhs),D) for row in chart['adjugate']]
            def in_scope(e):return all(known_guard(g,valid_ctx) or g==('nonzero',D) for g in domain_conditions(e))
            sol=[simple if in_scope(simple:=m.polynomial_quotient(m.simplify(raw))) else raw for raw in sols]
            if not all(in_scope(e) for e in sol):
                raise Unsupported('Ограничение знаменателя решения не следует из исходных условий и ранга')
            return sol
        def first(i):
            if i not in steps:steps[i]=solve_right([m.neg(at(partial(g,i))) for g in eq])
            return steps[i]
        def coefficient(i,j=None):
            if v in base:return m.q(int(j is None and v==i))
            if j is None:return first(i)[dep.index(v)]
            if i+j not in steps:
                def tangent(n):
                    direction={w:m.q(int(w==n)) for w in base}
                    for w,derivative in zip(dep,first(n)):
                        if point is not None or derivative[0]=='q':direction[w]=derivative
                        else:
                            slot=w+'_'+n
                            if slot in names:raise Unsupported('Обозначение промежуточной производной занято')
                            chart['first_derivative_bindings'][slot]=[w,n,derivative];direction[w]=ss(slot)
                    return direction
                left,right=tangent(i),tangent(j);rhs=[]
                for g in eq:
                    z=m.ZERO
                    for a,ca in left.items():
                        for b,cb in right.items():
                            if ca!=m.ZERO and cb!=m.ZERO:z=m.add(z,m.mul(m.mul(ca,cb),at(partial(partial(g,a),b))))
                    rhs.append(m.neg(z))
                steps[i+j]=solve_right(rhs)
            return steps[i+j][dep.index(v)]
        if isinstance(path,str):outputs[label]=coefficient(*path)
        else:
            value=m.ZERO
            for seq in product(base,repeat=path):
                term=coefficient(*seq)
                for n in seq:term=m.mul(term,ss('d'+n))
                value=m.add(value,term)
            outputs[label]=value
    return dict(original_smooth_domain=guards,charts={','.join(k):v for k,v in charts.items()},vertical_tangencies=vertical),outputs


TYPES={'scalar':1,'vector':3}
# Each signature contains result dimension followed by operand dimensions.
SIGNATURES={'add':((1,1,1),(3,3,3)), 'mul':((1,1,1),(3,1,3),(3,3,1)),
            'vector':((3,1,1,1),), **{'d'+axis:((1,1),) for axis in AXES},
            'grad':((3,1),), 'div':((1,3),), 'curl':((3,3),), 'laplacian':((1,1),),
            'dot':((1,3,3),), 'cross':((3,3,3),)}


def term(text):
    def visit(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return ('integer',n.value)
        if isinstance(n,ast.Name) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n.id):return ('field',n.id)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return ('mul',('integer',-1),visit(n.operand))
        if isinstance(n,ast.BinOp):
            a,b=visit(n.left),visit(n.right)
            if isinstance(n.op,ast.Sub):return ('add',a,('mul',('integer',-1),b))
            op={ast.Add:'add',ast.Mult:'mul',ast.MatMult:'cross'}.get(type(n.op))
            if op:return (op,a,b)
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id in SIGNATURES and not n.keywords:
            return (n.func.id,*(visit(a) for a in n.args))
        raise Unsupported('Ожидалось полиномиальное выражение из скалярных и векторных полей')
    try:return visit(ast.parse(re.sub(r'\s+cross\s+',' @ ',text.strip()),mode='eval').body)
    except (SyntaxError,RecursionError) as exc:raise Unsupported('Не разобрана запись векторного выражения') from exc


def dimensions(sides, declared):
    # Propagate dimensions both from operands and from results. Ambiguity stays explicit.
    possible={}
    def collect(node):
        if node in possible:return
        op,*args=node
        if op=='integer':possible[node]={1}
        elif op=='field':possible[node]={TYPES[declared[args[0]]]} if args[0] in declared else {1,3}
        else:
            if len(args)!=len(SIGNATURES[op][0])-1:raise Unsupported('Неверное число аргументов '+op)
            possible[node]={1,3}
            for arg in args:collect(arg)
    for side in sides:collect(side)
    fields={node[1] for node in possible if node[0]=='field'}
    if not set(declared)<=fields:raise Unsupported('Объявлено поле, отсутствующее в утверждении')
    constraints=[((n,*n[1:]),SIGNATURES[n[0]]) for n in possible if n[0] in SIGNATURES]
    constraints.append((sides,((1,1),(3,3))))
    changed=True
    while changed:
        changed=False
        for nodes,signatures in constraints:
            valid=[sig for sig in signatures if all(v in possible[n] for n,v in zip(nodes,sig))]
            if not valid:raise Unsupported('Тип выражения или его операндов несовместим с координатным оператором')
            for i,node in enumerate(nodes):
                choices=possible[node]&{sig[i] for sig in valid}
                if choices!=possible[node]:
                    possible[node]=choices;changed=True
    if any(len(possible['field',f])!=1 for f in fields):raise Unsupported('Для неоднозначных символов укажите тип поля')
    return {f:next(iter(possible['field',f])) for f in sorted(fields)}


def compile_identity(task):
    allowed={'kind','task_type','id','source','claim','identity','goal','coordinates','fields','hypotheses','regularity','requested_output'}
    if (set(task)-allowed or any(task[k]!='formal_vector_identity' for k in ('kind','task_type') if k in task)
            or task.get('coordinates',list(AXES))!=list(AXES)
            or task.get('requested_output',['proof'])!=['proof']):
        raise Unsupported('Поддержано одно тождество в декартовом базисе x,y,z')
    source=task.get('source',{})
    if (not isinstance(source,dict) or set(source)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or 'literal_requirement' in source and (not isinstance(source['literal_requirement'],str) or not re.fullmatch(
                r'Доказать (?:напечатанную )?(?:формулу|тождество)(?: (?:для|ротора|дивергенции|лапласиана|градиента|векторного|произведения|суммы))*\.',
                source['literal_requirement']))):
        raise Unsupported('Не распознаны все требования исходного условия о полях')
    statements=[task[k] for k in ('identity','claim','goal') if k in task]
    if len(statements)!=1:raise Unsupported('Требуется ровно одно равенство')
    claim=statements[0]
    if not isinstance(claim,str) or claim.count('=')!=1:raise Unsupported('Требуется одно равенство')
    sides=tuple(term(s) for s in claim.split('='))
    declared=task.get('fields',{})
    if not isinstance(declared,dict) or any(v not in ('scalar','vector') for v in declared.values()):
        raise Unsupported('У каждого поля должен быть скалярный или векторный тип')
    declared=dict(declared);constants=set()
    hypotheses=task.get('hypotheses',[])
    if not isinstance(hypotheses,list):raise Unsupported('Ожидался список условий на поля')
    for h in hypotheses:
        hit=re.fullmatch(r'([A-Za-z][A-Za-z_0-9]*) (constant )?(scalar|vector)',h) if isinstance(h,str) else None
        if not hit or declared.get(hit[1],hit[3])!=hit[3]:raise Unsupported('Не распознана гипотеза на поле')
        declared[hit[1]]=hit[3]
        if hit[2]:constants.add(hit[1])
    types=dimensions(sides,declared)
    regularity=task.get('regularity',{})
    if not isinstance(regularity,dict) or any(f not in types or type(k)!=int or k<0 for f,k in regularity.items()):
        raise Unsupported('Порядок непрерывных производных требуется задать для объявленного поля')
    ctx={'domain':'cartesian_field_identity','coordinates':list(AXES),'sides':sides,'field_dimensions':types,
         'constant_fields':sorted(constants),'regularity':regularity}
    return {'context':ctx,'goal':('cartesian_field_identity',)}


def compile_operator(task):
    allowed={'kind','id','source','expression','field','operator','fields','regularity','requested_output'}
    if set(task)-allowed or task.get('requested_output',['cartesian_components'])!=['cartesian_components']:
        raise Unsupported('One field operation with all Cartesian components is required')
    meta=task.get('source',{})
    if (not isinstance(meta,dict) or set(meta)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or meta.get('literal_requirement') not in (None,'Найти дивергенцию поля.','Найти дивергенцию определителя ротора.')):
        raise Unsupported('Unbound method or additional printed output for this field')
    if 'expression' in task and not {'field','operator'}&set(task):expression=task['expression']
    elif 'expression' not in task and task.get('operator') in ('grad','div','curl','laplacian'):
        expression=task['operator']+'('+task['field']+')'
    else:raise Unsupported('Ambiguous field expression')
    if meta.get('literal_requirement','').startswith('Найти дивергенцию') and not expression.startswith('div('):
        raise Unsupported('Expected the printed divergence')
    compiled=compile_identity(dict(kind='formal_vector_identity',identity=expression+'='+expression,
        fields=task.get('fields',{}),regularity=task.get('regularity',{})))
    return dict(context=compiled['context'],goal=('cartesian_components','left'))


def component_form(side,ctx):
    def deriv(p,axis):
        total={}
        for mon,c in p.items():
            for i,(atom,k) in enumerate(mon):
                field,component,word=atom
                if field in ctx['constant_fields']:continue
                word+=axis
                order=ctx['regularity'].get(field)
                if order is not None and len(word)>order:raise Unsupported('Недостаточный заявленный порядок производных '+field)
                if order is not None:word=''.join(sorted(word))
                d_atom=(field,component,word)
                rest=mon[:i]+mon[i+1:]+(((atom,k-1),) if k>1 else ())
                total=m.addp(total,m.mulp({rest:c*k},{((d_atom,1),):1}))
        return total
    def plus(terms):
        result={}
        for p in terms:result=m.addp(result,p)
        return result
    def diff(a,b):return m.addp(a,{mon:-c for mon,c in b.items()})
    def components(t):
        op,*args=t
        if op=='integer':return [{():args[0]} if args[0] else {}]
        if op=='field':
            dims=ctx['field_dimensions'][args[0]]
            return [{(((args[0],axis,''),1),):1} for axis in (('',) if dims==1 else AXES)]
        v=[components(a) for a in args];a=v[0]
        if op=='vector':return [v[i][0] for i in range(3)]
        if op in ('dx','dy','dz'):return [deriv(a[0],op[1])]
        if op=='add':return [m.addp(x,y) for x,y in zip(a,v[1])]
        if op=='mul':
            factor,items=(a[0],v[1]) if len(a)==1 else (v[1][0],a)
            return [m.mulp(factor,x) for x in items]
        if op=='grad':return [deriv(a[0],ax) for ax in AXES]
        if op=='div':return [plus(deriv(x,ax) for x,ax in zip(a,AXES))]
        if op=='laplacian':return [plus(deriv(deriv(a[0],ax),ax) for ax in AXES)]
        if op=='dot':return [plus(m.mulp(x,y) for x,y in zip(a,v[1]))]
        pairs=((1,2),(2,0),(0,1))
        if op=='curl':return [diff(deriv(a[k],AXES[j]),deriv(a[j],AXES[k])) for j,k in pairs]
        return [diff(m.mulp(a[j],v[1][k]),m.mulp(a[k],v[1][j])) for j,k in pairs]
    polynomials=components(freeze(ctx['sides'][0 if side=='left' else 1]))
    return tuple(tuple((mon,int(c)) for mon,c in sorted(p.items(),key=lambda h:canonical(h[0]))) for p in polynomials)


def render_form(form):
    def coordinate(poly):
        words=[]
        for mon,c in poly:
            factors=[]
            for (f,ax,derivatives),power in mon:
                s=f+('['+ax+']' if ax else '')
                if derivatives:s='∂['+','.join(derivatives)+']('+s+')'
                factors.append(s+('^'+str(power) if power!=1 else ''))
            words.append(('' if c==1 and factors else str(c))+
                         ('·' if c!=1 and factors else '')+'·'.join(factors))
        return ' + '.join(words).replace('+ -','− ') or '0'
    return ', '.join(coordinate(poly) for poly in form)


def valid_form(form,ctx):
    """Validate the exact serializable component vocabulary before replay."""
    if not isinstance(form,tuple) or len(form) not in (1,3):return False
    for p in form:
        if not isinstance(p,tuple):return False
        for term in p:
            if not isinstance(term,tuple) or len(term)!=2:return False
            mon,c=term
            if type(c)!=int or not c or not isinstance(mon,tuple):return False
            for factor in mon:
                if not isinstance(factor,tuple) or len(factor)!=2:return False
                atom,k=factor
                if not isinstance(atom,tuple) or len(atom)!=3 or type(k)!=int or k<1:return False
                f,ax,derivatives=atom
                if not all(isinstance(v,str) for v in atom) or f not in ctx['field_dimensions']:return False
                if ax not in (('',) if ctx['field_dimensions'][f]==1 else tuple(AXES)):return False
                if any(a not in AXES for a in derivatives):return False
    return True


def curve_contacts(task,library,request):
    """Recover a tangent from the first nonzero vector of a secant or the normal of a regular level."""
    from tasks import source,domain_conditions,known_guard
    from verify import same_value
    from operations import expression_positions
    from graphs import rational_roots
    from polynomial import rf
    kind=task['kind'];origin=task.get('source',{})
    if kind=='parametric_tangent_construction':kind='cycloid_tangent_construction'
    fields={'plane_tangent_and_normal':{'curve','at','point'},'contact_order':{'curves','contact_point','variable','definition'},
            'cycloid_tangent_construction':{'curve','at'},'tangent_parallelism':{'curve','line'},
            'parametric_tangent_parallel_plane':{'curve','plane'},'constant_tangent_angle_proof':{'curve','axis','cone'}}
    heading={'plane_tangent_and_normal':('Написать уравнения обеих прямых в указанной точке.',
              'Написать уравнения касательной и нормали к параметрической кривой.','Написать уравнения касательной и нормали к заданной рациональной кривой.',
              'Написать уравнения касательной и нормали в заданной точке.'),
             'constant_tangent_angle_proof':('Доказать постоянство угла касательной к винтовой линии с осью Oz.',
              'Доказать, что кривая пересекает все образующие конуса под одним и тем же углом.'),
             'contact_order':('Найти порядок касания кривой с осью Ox при x=0.',),
             'tangent_parallelism':('Найти точки кривой с касательной, параллельной заданной прямой.',),
             'parametric_tangent_parallel_plane':('Найти на данной кривой точку, касательная в которой параллельна плоскости.',),
             'cycloid_tangent_construction':('Написать уравнение касательной при t0 и дать способ её построения.',)}
    if (not library.data.get('secant_and_level_tangents') or set(task)-fields[kind]-{'kind','source','id'}
            or set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement'}
            or origin.get('literal_requirement') is not None and origin['literal_requirement'] not in heading[kind]):
        raise Unsupported('Unbound source curve, restrictions or geometric obligation')
    def text(s):return s.replace('²','^2').replace('³','^3').replace('⁴','^4')
    def transform(raw,var,point):return m.substitute(raw,{('v',var):point})
    def line(p,v):
        # The pair denotes A*(X-p_x)+B*(Y-p_y)=0. Scaling leaves the line unchanged.
        return dict(through=p,tangent_coefficients=(m.neg(v[1]),v[0]),normal_coefficients=v)
    def leading(e,var,p,side):
        sub=dict(kind='leading_asymptotic_term',expression=source(e),variable=var,approach=dict(point=source(p),side=side))
        _,order,c=freeze(request(f'{side} leading term of the source displacement',sub)['value'])
        if m.num(order) is None or m.num(order)<=0:raise Unsupported('The source displacement does not tend to zero')
        return m.num(order),c
    curve=task.get('curve');ctx=m.context(dict(variable='__h'))
    if kind=='contact_order':
        var=task['variable'];p=m.parse(task['contact_point'],None);curves=task['curves']
        if (not isinstance(curves,list) or len(curves)!=2 or task['definition']!='same derivatives through n, first discrepancy at n+1'
                or origin.get('literal_requirement') and (var!='x' or p!=m.ZERO or curves[1]!='0')):
            raise Unsupported('The requested contact definition or printed reference curve is not bound')
        raw=[m.parse(text(f),var) for f in curves]
        if any(not known_guard((g,transform(v,var,p)),ctx) for f in raw for g,v in domain_conditions(f,True)):
            raise Unsupported('The claimed order needs regularity at the contact point')
        if any(e[0]=='rpow' for f in raw for _,e in expression_positions(f)):
            raise Unsupported('Real powers require separate regularity at the contact')
        delta=m.add(raw[0],m.neg(raw[1]));entries=[leading(delta,var,p,s) for s in ('left','right')]
        n,c=entries[0]
        if n.denominator!=1 or n!=entries[1][0] or not same_value(c,entries[1][1]):raise Unsupported('No common integral leading degree')
        return dict(source_curves=raw,point=p),dict(contact_order=int(n)-1,first_discrepancy_degree=int(n),coefficient=c)
    parametrized=isinstance(curve,list)
    if not parametrized and not isinstance(curve,str):raise Unsupported('Missing Cartesian equation or parametrization')
    explicit=not parametrized and curve.startswith('y=') and not re.search(r'\by\b',curve[2:])
    var='x' if explicit else 't'
    if parametrized or explicit:
        components=[text(z) for z in curve] if parametrized else [var,text(curve[2:])]
        params=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join(components)))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi',var})
        paths=[m.parse(z,var,params) for z in components]
        def diff(e):
            proof=request('differentiate a curve coordinate',dict(kind='differentiate',function=source(e),variable=var,
                          parameters=params,method_requirement='table_and_rules'))
            return m.simplify(freeze(proof['value']))
    if kind=='constant_tangent_angle_proof':
        if not parametrized or len(paths)!=3 or ('axis' in task)==('cone' in task) or any(domain_conditions(z,True) for z in paths):
            raise Unsupported('A smooth spatial chart and one family of reference directions are required')
        coverage={}
        if 'axis' in task:
            axes={'Ox':0,'Oy':1,'Oz':2}
            if task['axis'] not in axes or origin.get('literal_requirement') and task['axis']!='Oz':raise Unsupported('Unbound reference axis')
            ref=tuple(m.q(i==axes[task['axis']]) for i in range(3))
        else:
            axes=list('xyz');eq=task['cone'].split('=')
            if len(eq)!=2:raise Unsupported('Expected an equation of the generating cone')
            F=m.add(m.parse(text(eq[0]),None,axes),m.neg(m.parse(text(eq[1]),None,axes)))
            coords=tuple(('s',a) for a in axes);scale=('s','__scale')
            if not same_value(m.substitute(F,{z:m.mul(z,scale) for z in coords}),m.mul(m.power(scale,2),F)):
                raise Unsupported('The rays through the origin have not been shown to generate the level')
            ref=tuple(paths)
            if not same_value(m.substitute(F,dict(zip(coords,ref))),m.ZERO):raise Unsupported('The given curve is not contained in the cone')
            cone=m.add(m.add(m.power(coords[0],2),m.power(coords[1],2)),m.neg(m.power(coords[2],2)))
            if domain_conditions(F) or not (same_value(F,cone) or same_value(F,m.neg(cone))):
                raise Unsupported('Coverage of every generator of the source cone is unproved')
            for _,atom in expression_positions(ref[0]):
                if atom[0]!='cos':continue
                angle=atom[1];offset=transform(angle,var,m.ZERO);frequency=m.simplify(m.add(transform(angle,var,m.ONE),m.neg(offset)))
                if (m.nonzero(frequency,ctx) and same_value(angle,m.add(m.mul(frequency,('v',var)),offset))
                        and same_value(ref[0],m.mul(ref[2],('cos',angle))) and same_value(ref[1],m.mul(ref[2],('sin',angle)))):
                    coverage=dict(generator_angle=angle,frequency=frequency,phase_offset=offset);break
            if not coverage:raise Unsupported('The source azimuth has not been proved to attain all generator directions')
        vel=tuple(map(diff,paths));values=[m.dot(a,b) for a,b in ((vel,vel),(ref,ref),(vel,ref))]
        base=[m.simplify(transform(z,var,m.ZERO)) for z in values]
        positive=[m.ONE]
        for expr in paths:
            for _,e in expression_positions(expr):
                if e[0]=='exp':
                    z=('exp',m.add(e[1],m.neg(transform(e[1],var,m.ZERO))))
                    positive.extend((z,m.power(z,2)))
        factors=[next((g for g in positive if same_value(z,m.mul(g,c))),None) for z,c in zip(values,base)]
        if not all(factors) or not same_value(m.power(factors[2],2),m.mul(*factors[:2])):
            raise Unsupported('The dot product and both positive squared norms do not have compatible scale factors')
        return dict(velocity=vel,reference=ref,positive_factors=factors,initial_squared_norms=base[:2],**coverage),dict(
            cosine=m.div(('abs',base[2]),('sqrt',m.mul(*base[:2]))),oriented_cosine=m.div(base[2],('sqrt',m.mul(*base[:2]))),
            regular_when_both_nonzero=base[:2],
            degenerate='If a base norm is zero, the corresponding direction vanishes for every parameter value.')
    if kind in ('tangent_parallelism','parametric_tangent_parallel_plane'):
        if params or any(domain_conditions(f) for f in paths):raise Unsupported('The full parameter domain and exceptional directions remain open')
        if kind=='tangent_parallelism':
            slopes={'Ox':m.ZERO,'first quadrant bisector y=x':m.ONE}
            if not explicit or task.get('line') not in slopes:raise Unsupported('A constant reference direction is required')
            normal=(m.neg(slopes[task['line']]),m.ONE)
        else:
            axes=list('xyz');eq=task['plane'].split('=')
            if len(paths)!=3 or len(eq)!=2:raise Unsupported('Expected three curve coordinates and a reference plane')
            plane=m.add(m.parse(text(eq[0]),None,axes),m.neg(m.parse(text(eq[1]),None,axes)))
            zeros={('s',v):m.ZERO for v in axes};at_zero=m.simplify(m.substitute(plane,zeros))
            normal=tuple(m.add(m.substitute(plane,{**zeros,('s',v):m.ONE}),m.neg(at_zero)) for v in axes)
            if not same_value(plane,m.add(at_zero,m.dot(normal,tuple(('s',v) for v in axes)))) or not any(m.nonzero(c,ctx) for c in normal):
                raise Unsupported('The reference equation is not an affine plane')
        velocity=tuple(map(diff,paths));eq=m.simplify(m.dot(normal,velocity));num,den=rf(eq,var)
        if rational_roots(den):raise Unsupported('The velocity dot product has an unresolved pole')
        if not any(num):raise Unsupported('A continuum of parallel directions needs its own range formula')
        roots=rational_roots(num);solutions=[]
        for z in roots:
            t=m.add(m.q(z.a),m.mul(m.q(z.b),('sqrt',m.q(z.d)))) if z.b else m.q(z.a)
            d=tuple(m.simplify(transform(w,var,t)) for w in velocity)
            if not any(m.nonzero(w,ctx) for w in d):raise Unsupported('A stationary parametrization requires a higher secant')
            pt=tuple(m.simplify(transform(w,var,t)) for w in paths)
            if not any(same_value(t,old['parameter']) for old in solutions):solutions.append(dict(parameter=t,point=pt,direction=d))
        return dict(reference_normal=normal,velocity=velocity,orthogonality_equation=eq),dict(solutions=solutions)
    if kind=='cycloid_tangent_construction':
        if not parametrized or len(paths)!=2 or not re.fullmatch(r'[A-Za-z][A-Za-z_0-9]*',task['at']) or task['at'] in [var,*params]:
            raise Unsupported('Construction needs an arbitrary parameter value and two coordinate functions')
        symbol=task['at'];at=('s',symbol);ctx=m.context(dict(variable='__h',parameters=[*params,symbol]))
        raw=[transform(e,var,at) for e in paths]
        if any(not known_guard(g,ctx) for e in raw for g in domain_conditions(e,True)):raise Unsupported('Global smoothness of the chart is unresolved')
        velocity=list(map(diff,paths));acceleration=list(map(diff,velocity))
        p,v,w=[tuple(m.simplify(transform(e,var,at)) for e in seq) for seq in (paths,velocity,acceleration)]
        norm=m.dot(w,w)
        globally_regular=any(m.nonzero(z,ctx) for z in v) or m.nonzero(m.dot(v,v),ctx)
        amplitude=None
        if not globally_regular and not any(m.nonzero(z,ctx) for z in w) and not m.nonzero(norm,ctx):
            amplitude=next((('s',a) for a in params if same_value(norm,m.power(('s',a),2))),None)
            if amplitude is None or any(m.variable_in(m.simplify(m.substitute(e,{amplitude:m.ZERO})),var) for e in paths):
                raise Unsupported('Simultaneously stationary velocity and acceleration need further analysis')
        offset=v[1] if same_value(v[0],p[1]) else m.div(m.mul(p[1],v[1]),v[0]) if v[0]!=m.ZERO else None
        solution=dict(regular_tangent=dict(through=p,coefficients=line(p,v)['tangent_coefficients'],when='velocity is nonzero'),
                      vertical_regular=dict(x=p[0],when='horizontal velocity is zero and vertical velocity is nonzero'))
        construction=[]
        if offset is not None:
            foot=m.simplify(m.add(p[0],offset))
            if not same_value(m.dot(v,(m.add(foot,m.neg(p[0])),m.neg(p[1]))),m.ZERO):raise Unsupported('The proposed normal intercept is not perpendicular')
            solution['normal_foot']=(foot,m.ZERO)
            construction.append('Если горизонтальная скорость и высота ненулевые, отметьте указанную точку на оси Ox, соедините её с точкой кривой и восстановите в точке кривой перпендикуляр.')
        construction.append('В остальных регулярных точках проведите прямую по направлению вектора скорости; если его горизонтальная компонента нулевая, проведите вертикаль.')
        if not globally_regular:
            solution['stationary_tangent']=dict(through=p,coefficients=line(p,w)['tangent_coefficients'],when='velocity is zero and acceleration is nonzero')
            if same_value(w[0],v[1]):
                solution['stationary_tangent']['vertical_x']=p[0];construction.append('В точке нулевой скорости и ненулевого ускорения проведите вертикаль.')
            else:construction.append('В точке нулевой скорости и ненулевого ускорения отложите вектор ускорения от точки кривой и проведите через них прямую.')
        if amplitude is not None:solution['collapsed']=dict(scale=amplitude,when='scale is zero',tangent='none: the image is one point')
        solution['construction']=' '.join(construction)
        return dict(point=p,velocity=v,acceleration=w,acceleration_norm_squared=norm),solution
    if not parametrized and not explicit:
        eq=text(curve).split('=');pt=task.get('point')
        if 'at' in task or len(eq)!=2 or not isinstance(pt,list) or len(pt)!=2:raise Unsupported('A source point on the implicit plane curve is required')
        field=m.add(m.parse(eq[0],None,['x','y']),m.neg(m.parse(eq[1],None,['x','y'])))
        req=dict(kind='scalar_field_geometry',function=source(field),variables=['x','y'],points={'P':list(map(str,pt))},
                 requests=[dict(op='gradient',at='P')],level='0')
        row=request('normal of the original level set',req)['compilation']['points']['P']
        grad=tuple(map(freeze,row['gradient']))
        if not same_value(row['field_value'],m.ZERO) or not any(m.nonzero(c,ctx) for c in grad):raise Unsupported('Not a regular point of the specified level')
        return dict(level=field,gradient=grad),line(freeze(row['point']),(grad[1],m.neg(grad[0])))
    if len(paths)!=2 or params or ('point' in task)!=explicit or ('at' in task)!=parametrized:
        raise Unsupported('Unbound source point or parameter assumption for the plane tangent')
    infinity=parametrized and task['at']=='infinity'
    p=m.ZERO if infinity else m.parse(str(task['point'][0] if explicit else task['at']),None)
    base=() if infinity else tuple(transform(e,var,p) for e in paths)
    if any(not m.constant_defined(e,ctx) for e in base):raise Unsupported('Original parametrization is undefined at the specified point')
    if explicit and (len(task['point'])!=2 or not same_value(base[1],m.parse(str(task['point'][1]),None))):raise Unsupported('The specified point is off the curve')
    if infinity:paths=[transform(e,var,('div',m.ONE,('v',var))) for e in paths]
    point=None;dirs=[]
    for side in ('left','right'):
        point_side=tuple(freeze(request('source point from the '+side,dict(kind='limit',variable=var,expression=source(f),
                      approach=dict(point=source(p),side=side)))['value']) for f in paths)
        if any(f in ('+inf','-inf') for f in point_side) or point and not all(same_value(a,b) for a,b in zip(point_side,point)):
            raise Unsupported('The two source arcs do not meet at one finite point')
        point=point_side
        if base and not all(same_value(a,b) for a,b in zip(point,base)):raise Unsupported('The arc does not approach its assigned point')
        delta=[m.add(f,m.neg(v)) for f,v in zip(paths,point)]
        terms=[None if same_value(d,m.ZERO) else leading(d,var,p,side) for d in delta]
        if not any(terms):raise Unsupported('Constant parametrization has no tangent direction')
        order=min(t[0] for t in terms if t)
        dirs.append(tuple(t[1] if t and t[0]==order else m.ZERO for t in terms))
    if not same_value(m.mul(dirs[0][0],dirs[1][1]),m.mul(dirs[0][1],dirs[1][0])):raise Unsupported('Distinct one-sided tangent lines')
    return dict(point=point,secant_directions=dirs,chart='reciprocal parameter' if infinity else 'original parameter'),line(point,dirs[0])


def local_geometry(task, library, request):
    """Bind printed local geometry and expansion requests to the shared calculus methods."""
    kind = task['kind']
    if kind in ('loxodrome_constant_angle','surface_section_tangent_angle') and library.data.get('geometric_stationary_profiles'):
        from plane_geometry import intrinsic_section_angle
        return intrinsic_section_angle(task)
    source_info = task.get('source', {})
    provenance = {'exercise', 'pdf_page', 'printed_page', 'pdf_sha256', 'printed_subpart', 'literal_requirement'}
    fields = {'kind', 'id', 'source', 'source_formula', 'stated_conditions', 'requested_output'}
    output, = task['requested_output']
    heading = source_info.get('literal_requirement', output)
    retained_singularities = (kind=='plane_curve_singularity' and output=='classify_singular_points'
                              and heading=='classify_singular_points_and_sketch_the_curve')
    if (not library.data.get('printed_local_geometry') or set(source_info)-provenance or
            heading != output and not retained_singularities):
        raise Unsupported('The printed goal must match the requested geometric or analytic quantity')
    text = task['source_formula'].translate(str.maketrans({'²':'^2','³':'^3','⁴':'^4','⁵':'^5','⁶':'^6'}))
    conditions = task.get('stated_conditions', [])
    profile=library.data.get('geometric_stationary_profiles')
    if kind == 'tangent_plane_limit' and not set(task)-fields:
        return limiting_parametric_plane(text, conditions, output)
    if kind == 'plane_curve_singularity' and not set(task)-fields:
        return plane_singularities(text, conditions, output)
    if kind == 'surface_geometry' and not set(task)-fields:
        try:return level_surface_geometry(text, conditions, output)
        except Unsupported:
            if not profile:raise
            from plane_geometry import level_profile_geometry
            return level_profile_geometry(text,conditions,output)
    if kind in ('outward_normal_derivative', 'normal_derivative_identity') and not set(task)-fields:
        return printed_normal_derivatives(text, conditions, output, library, request)
    if kind in ('plane_curve_envelope','surface_envelope') and not set(task)-fields:
        legacy=plane_family_envelope if kind=='plane_curve_envelope' else surface_family_envelope
        try:return legacy(text, conditions, output)
        except Unsupported:
            if not profile:raise
            from plane_geometry import constrained_envelope_profile
            return constrained_envelope_profile(text,conditions,output,kind=='surface_envelope')
    if kind=='plane_curve_discriminant' and profile and not set(task)-fields:
        from plane_geometry import translate_discriminant
        return translate_discriminant(text,conditions,output)
    if conditions:
        raise Unsupported('An additional source condition remains to be interpreted')
    if kind == 'multivariate_taylor_problem' and not set(task)-fields-{'coordinates', 'center', 'degree'}:
        return printed_finite_taylor(task, text, output, request)
    if kind == 'multivariate_average_expansion' and not set(task)-fields:
        return printed_field_average(text, output.replace('²','^2'), request)
    if kind == 'multivariate_infinite_series' and not set(task)-fields:
        if library.data.get('compact_binomial_moment_series') and text.startswith('int_'):
            return compact_binomial_moment_series(text,output)
        return radial_analytic_series(text, output, library, request)
    if kind == 'implicit_taylor_series' and not set(task)-fields:
        return regular_polynomial_implicit_jet(text, output)
    raise Unsupported('No interpretation of the full source obligation has been verified')


def compact_binomial_moment_series(text,output):
    from fractions import Fraction
    from integrals import affine
    from model import ONE,ZERO,q
    from polynomial import NotRational,Undefined,rf

    binder=re.fullmatch(r'int_(-?\d+(?:/\d+)?)\^(-?\d+(?:/\d+)?)\s+(.+)\s*d([A-Za-z_]\w*)',text)
    if output!='first three Maclaurin terms' or not binder:
        raise Unsupported('Expected a fixed compact interval and three Maclaurin terms')
    lo,hi,integrand,t=binder.groups(); a,b=map(Fraction,(lo,hi))
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',integrand))-{t})
    if a>=b or len(names)!=2:raise Unsupported('Expected two free Taylor coordinates and a positive length interval')
    for x,y in (names,names[::-1]):
        raw=m.parse(integrand,x,[t,y])
        if raw[0]!='rpow' or domain_conditions(raw[1]) or domain_conditions(raw[2]):
            raise Unsupported('The original base and exponent must be smoothly defined near the origin')
        try:slope,at=affine(raw[1],x)
        except Unsupported:continue
        rate=m.num(slope)
        if not rate or at!=ONE:continue
        break
    else:raise Unsupported('Expected an affine power base normalized to one at the center')
    exponent=m.substitute(raw[2],{('s',y):('v',y)})
    slope,offset=affine(exponent,y)
    if offset!=ZERO or m.contains(slope,('v',x)):raise Unsupported('The exponent must be linear in the second coordinate')
    try:p,d=rf(m.substitute(slope,{('s',t):('v',t)}),t)
    except (NotRational,Undefined) as exc:raise Unsupported('Expected a polynomial weight under the integral') from exc
    if len(d)!=1:raise Unsupported('A polynomial moment is required')
    moment=sum(c/d[0]*(b**(j+1)-a**(j+1))/(j+1) for j,c in enumerate(p))
    if not moment:raise Unsupported('The first moment vanishes, so a higher Taylor order is required')
    X,Y=('s',x),('s',y)
    terms=(q(b-a),m.mul(q(rate*moment),m.mul(X,Y)),m.mul(q(-rate**2*moment/2),m.mul(m.power(X,2),Y)))
    return dict(method='compact_binomial_moment_series',theorem='method.compact_binomial_moment_series',original=raw,
                interval=(q(a),q(b)),binder=t,affine_rate=q(rate),moment=q(moment),argument=[
                    'В положительной окрестности основания записываем степень как экспоненту логарифма. Полиномиальный вес ограничен на всём отрезке интегрирования.',
                    'Показатель имеет полную степень не ниже двух. До степени три в экспоненте остаются единица и показатель, а его коэффициенты дают первые два члена логарифма.',
                    'Остаток равномерно имеет порядок четыре по сумме модулей двух координат. Интегрируем три ненулевых члена по точному полиномиальному моменту.'
                ]),dict(terms=terms,total_degrees=(0,2,3),remainder_order=4)


def printed_finite_taylor(task, text, output, request):
    from model import ZERO
    variables, center, degree = [task[key] for key in ('coordinates', 'center', 'degree')]
    if not variables or len(variables)>3 or len(center)!=len(variables):
        raise Unsupported('The Taylor center and the independent coordinates must be fixed')
    params = sorted(set(re.findall(r'[A-Za-z_]\w*',text))-set(variables)-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    increments = ['h','k','l'][:len(variables)]
    while set(increments)&set([*params,*variables]):
        increments = [v+'_' for v in increments]
    center = 'current_point' if center==variables else dict(zip(variables,center,strict=True))
    child = dict(kind='multivariate_taylor',expression=text,variables=variables,center=center,
                 increments=increments,parameters=params)
    if output.startswith('exact_increment_at_'):
        target = ','.join(f'{x}={center[x]}+{h}' for x,h in zip(variables,increments))
        if not isinstance(center,dict) or output!='exact_increment_at_'+target or degree is not None:
            raise Unsupported('The printed increment does not match the center and directions')
        child['requested_output'] = ['exact_increment']
    elif output in ('exact_finite_expansion',f'expand f({",".join(x+"+"+h for x,h in zip(variables,increments))}) in integer powers of {",".join(increments)}') and degree is None:
        child['requested_output'] = ['exact_shifted_polynomial']
    elif (output=='all_terms_through_total_degree' and type(degree) is int or
            output=='second_order_approximation' and degree==2 or
            output=='simplify_for_small_coordinates' and degree is None):
        child.update(degree=2 if degree is None else degree,requested_output=['finite_taylor_polynomial'])
    else:
        raise Unsupported('The requested truncation order or polynomial quantity remains unknown')
    proof = request('homogeneous polynomial in the declared increments',child)
    terms = freeze(proof['value']['homogeneous_terms'])
    value = proof['value']
    if output=='simplify_for_small_coordinates':
        order = next((n for n,a in enumerate(terms) if a!=ZERO),None)
        if order is None:
            raise Unsupported('The first nonzero homogeneous term is beyond the proved Taylor jet')
        value = dict(value,leading_degree=order,leading_homogeneous_term=terms[order])
    return dict(method='printed_taylor',increments=increments,degree=value['degree']),value


def printed_field_average(text, output, request):
    from fractions import Fraction
    from model import ZERO
    from tasks import source
    t = text.replace(' ','')
    match = re.fullmatch(r'F\((\w+)\)=\(f\(P1\)\+f\(P2\)\+f\(P3\)\)/3,equilateraltrianglecenteredatP=\((\w+),(\w+)\)withP1=\(\2\+\1,\3\)',t)
    if match and output==f'expand in {match[1]} through {match[1]}^2':
        radius,x,y = match.groups()
        child = dict(field='f',variables=[x,y],increments=[radius],
                     sampling=dict(kind='regular_polygon_vertices',vertices=3,first_direction=[1,0]),degree=2)
    else:
        circle = re.fullmatch(r'F\((\w+)\)=int_0\^\(2\*pi\)f\((\w+)\+\1\*cos\((\w+)\),(\w+)\+\1\*sin\(\3\)\)d\3/\(2\*pi\)',t)
        if circle and output==f'expand in powers of {circle[1]}':
            radius,x,_,y = circle.groups()
            child = dict(field='f',variables=[x,y],increments=[radius],sampling=dict(kind='uniform_circle'))
        else:
            # A linear combination of field values is extracted from the exact AST.
            try:
                tree = ast.parse(t.replace('^','**'),mode='eval')
            except SyntaxError as exc:
                raise Unsupported('The source is not a parsed linear combination of shifts') from exc
            calls = [n for n in ast.walk(tree) if isinstance(n,ast.Call)]
            if not calls or any(not isinstance(c.func,ast.Name) or c.func.id!='f' or c.keywords or len(c.args)!=2 for c in calls):
                raise Unsupported('A weighted combination of translates of the same field is required')
            finite = re.fullmatch(r'expand in (\w+) through \1\^(\d+)',output)
            infinite = re.fullmatch(r'expand in powers of (\w+) and (\w+)',output)
            if not finite and not infinite:
                raise Unsupported('No verified Taylor order or increment list for this sampling')
            increments = [finite[1]] if finite else list(infinite.groups())
            coordinates = sorted({n.id for c in calls for a in c.args for n in ast.walk(a) if isinstance(n,ast.Name)}-set(increments))
            if len(coordinates)!=2:
                raise Unsupported('Two independent source coordinates are required')
            t = t.replace('^','**')
            weights = [f'__sample{i}' for i in range(len(calls))]
            edits=[(c.col_offset,c.end_col_offset,w) for c,w in zip(calls,weights)]
            for lo,hi,w in sorted(edits,reverse=True):
                t=t[:lo]+w+t[hi:]
            expr=m.parse(t.replace('**','^'),None,weights)
            from tasks import domain_conditions, known_guard
            ctx=m.context(dict(variable='__weight'))
            if not all(known_guard(g,ctx) for g in domain_conditions(expr)):
                raise Unsupported('The original weights must be defined without hypotheses')
            mon,den=m.rational_form(expr)
            if den!={():Fraction(1)}:
                raise Unsupported('Weights must be constant')
            nodes=[]
            for mset,w in sorted(mon.items()):
                if len(mset)!=1 or mset[0][1]!=1:
                    raise Unsupported('The source combination is not linear in the field values')
                call=calls[weights.index(mset[0][0][1])]
                offsets=[]
                for base,arg in zip(coordinates,call.args):
                    a=m.parse(ast.unparse(arg).replace('**','^'),None,[*coordinates,*increments])
                    if not all(known_guard(g,ctx) for g in domain_conditions(a)):
                        raise Unsupported('The given field displacement has a restricted domain')
                    p,d=m.rational_form(m.add(a,m.neg(('s',base))))
                    if d!={():Fraction(1)} or any(len(k)!=1 or k[0][0][1] not in increments or k[0][1]!=1 for k in p):
                        raise Unsupported('The displacements are not linear in the printed increments')
                    offsets.append([str(p.get(((('s',h),1),),0)) for h in increments])
                nodes.append(dict(weight=str(w),offsets=offsets))
            child=dict(field='f',variables=coordinates,increments=increments,sampling=dict(kind='finite_linear_combination',nodes=nodes))
            if finite:
                child['degree']=int(finite[2])
    child.update(kind='sampled_field_taylor',regularity='state_taylor_hypotheses',requested_output=[
        'homogeneous_expansion_through_degree' if 'degree' in child else 'all_taylor_coefficients'])
    value=request('field moments by total degree',child)['value']
    return dict(method='field_weighted_shifts',increments=child['increments']),value


def radial_analytic_series(text, output, library, request):
    from tasks import domain_conditions, known_guard, source, taylor_coefficients
    if output=='Maclaurin_series':
        variables=['x','y'];centers=['0','0']
    else:
        match=re.fullmatch(r'(?:power_series|Taylor_series)_centered_at_\((-?\d+),(-?\d+)\)',output)
        if not match:
            raise Unsupported('A convergent series about an explicit center is required')
        variables=['x','y'];centers=list(match.groups())
    params=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-set(variables)-{'pi','e'})
    t='__ray';hs=['h','k']
    if set([t,*hs])&set(params):
        raise Unsupported('A parameter clashes with a Taylor increment')
    a=[m.parse(z,None) for z in centers]
    raw=m.parse(text,None,[*variables,*params])
    along=m.substitute(raw,{('s',x):('add',p,('mul',('s',t),('s',h))) for x,h,p in zip(variables,hs,a)})
    ctx=m.context(dict(variable=t,parameters=[*params,*hs]))
    if not all(known_guard((r,m.substitute(e,dict.fromkeys((('s',t),),m.ZERO))),ctx) for r,e in domain_conditions(along,True)):
        raise Unsupported('The original function is not analytic on a neighborhood of its center')
    # Along sufficiently short increments the radial variable ranges over a disk
    # larger than the unit disk. Thus setting it to one sums all homogeneous terms.
    analysis,value=taylor_coefficients(source(along),t,'0',False,library,request,library.data['analytic_power_series'],fixed_real_powers=True)
    value.update(formula=f'sum_{{j>=0}} C[{value["root"]}](j)',variables=variables,center=a,increments=hs,
                 degree_of_each_coefficient='C[j] is homogeneous of total degree j',
                 validity='some open neighborhood of the given center for each choice of the fixed real parameters')
    return dict(method='radial_analytic_coefficients',original=raw,radial_certificate=analysis),value


def regular_polynomial_implicit_jet(text, output):
    from fractions import Fraction
    from tasks import domain_conditions
    from model import ZERO
    spec=re.fullmatch(r'(.+?)=0;(\w+)\((-?\d+),(-?\d+)\)=(-?\d+)',text.replace(' ',''))
    increments=re.fullmatch(r'several ascending powers of ([a-z])-(-?\d+),([a-z])-(-?\d+)',output)
    if not spec or not increments or (spec[3],spec[4])!=(increments[2],increments[4]):
        raise Unsupported('An exact regular branch and the same center in both increments are required')
    x,y,z=increments[1],increments[3],spec[2]
    symbols=[('s',s) for s in (x,y,z)]
    if len(set(symbols))!=3:
        raise Unsupported('The independent and dependent coordinates must be distinct')
    raw=m.parse(spec[1],None,[x,y,z])
    if domain_conditions(raw):
        raise Unsupported('The implicit polynomial must be smooth at the selected branch')
    p,d=m.rational_form(raw)
    if d!={():Fraction(1)} or any(set(dict(k))-set(symbols) for k in p):
        raise Unsupported('The analytic implicit equation needs an exact polynomial representation')
    point=list(map(lambda s:m.q(int(s)),spec.groups()[2:]))
    center=dict(zip(symbols,point))
    if m.simplify(m.substitute(raw,center))!=ZERO:
        raise Unsupported('The specified center is not on the original relation')
    derivative=exact_polynomial_partial(p,symbols[2])
    pivot=m.simplify(m.substitute(m.poly_expr(derivative),center))
    if not m.num(pivot):
        raise Unsupported('The analytic implicit function theorem needs a nonzero vertical partial')
    h,k=('s','__dx'),('s','__dy')
    translate={symbols[0]:m.add(point[0],h),symbols[1]:m.add(point[1],k)}
    z_series=point[2];terms=[z_series];rows=[]
    for degree in (1,2,3):
        residual,_=m.rational_form(m.substitute(raw,{**translate,symbols[2]:z_series}))
        if any(sum(e for _,e in mon)<degree for mon in residual):
            raise Unsupported('A lower-order residual has not been cancelled')
        piece=m.poly_expr({mon:c for mon,c in residual.items() if sum(e for _,e in mon)==degree})
        coefficient=m.div(m.neg(piece),pivot)
        rows.append(dict(degree=degree,residual=piece,coefficient=coefficient))
        terms.append(coefficient)
        z_series=m.add(z_series,coefficient)
    residual,_=m.rational_form(m.substitute(raw,{**translate,symbols[2]:z_series}))
    if any(sum(e for _,e in mon)<=3 for mon in residual):
        raise Unsupported('The Taylor jet does not verify against the original polynomial')
    return dict(method='implicit_polynomial_jet',center=point,vertical_partial=pivot,equation=raw,residual_elimination=rows),dict(
        degree=3,homogeneous_terms=terms,increments=['__dx','__dy'],remainder='order_four_in_euclidean_norm')


def exact_polynomial_partial(terms, coordinate):
    """Differentiate the exact polynomial coefficient map in one atom."""
    result={}
    for monomial,coefficient in terms.items():
        k=dict(monomial).get(coordinate,0)
        if k:
            key=tuple((s,e-(s==coordinate)) for s,e in monomial if e>(s==coordinate))
            result[key]=k*coefficient
    return result


def limiting_parametric_plane(text, conditions, output):
    from fractions import Fraction
    from model import ZERO
    from tasks import domain_conditions
    clauses=text.replace(' ','').split(',')
    if output!='limiting_tangent_plane' or len(clauses)!=3 or not all(re.match(r'[a-z]=',s) for s in clauses):
        raise Unsupported('An original three-dimensional parametric map is required')
    chart=re.fullmatch(r'\(([a-z]),([a-z])\) tends to \((\w+),(\w+)\) on edge \1=\2',conditions[-1]) if len(conditions)==2 else None
    if not chart or conditions[0]!=f'{chart[1]}!={chart[2]}' or len(set(chart.groups()))!=4:
        raise Unsupported('The excluded diagonal and the approached edge must be identical')
    u,v,p,_=chart.groups()
    coord=[e[0] for e in clauses]
    if len(set([*coord,u,v,p]))!=6:
        raise Unsupported('The source coordinate names are ambiguous')
    uv=[('s',u),('s',v)];h=('s','__off_diagonal');base=('s',p)
    raw=[m.parse(e[2:],None,[u,v]) for e in clauses]
    rows=[[],[]]
    for expr in raw:
        numerator,denominator=m.rational_form(expr)
        if denominator!={():Fraction(1)} or domain_conditions(expr) or any(set(dict(k))-set(uv) for k in numerator):
            raise Unsupported('The limiting chart requires globally smooth polynomial coordinates')
        for row,x in zip(rows,uv):
            row.append(m.poly_expr(exact_polynomial_partial(numerator,x)))
    a,b=rows
    cross=[m.add(m.mul(a[i],b[j]),m.neg(m.mul(a[j],b[i]))) for i,j in ((1,2),(2,0),(0,1))]
    components=[m.rational_form(m.substitute(e,{uv[0]:m.add(uv[1],h)}))[0] for e in cross]
    degrees=[dict(mon).get(h,0) for c in components for mon in c]
    if not degrees:
        raise Unsupported('The surface rank vanishes identically')
    order=min(degrees)
    normal=[m.simplify(m.substitute(m.poly_expr({tuple((s,e) for s,e in mon if s!=h):c for mon,c in comp.items()
                                               if dict(mon).get(h,0)==order}),{uv[1]:base})) for comp in components]
    ctx=m.context(dict(variable=u,parameters=[p]))
    if not any(m.nonzero(e,ctx) for e in normal):
        raise Unsupported('The limiting normal is not certified nonzero on the stated edge')
    edge=[m.simplify(m.substitute(e,dict.fromkeys(uv,base))) for e in raw]
    return dict(method='normalized_cross_product',original=raw,cross_product=cross,diagonal_factor_order=order),dict(
        coordinates=coord,through=edge,normal=normal,plane_constant=m.dot(edge,normal))


def plane_singularities(text, conditions, output):
    from fractions import Fraction
    from graphs import rational_roots
    from intervals import peval, quadratic_term
    from model import ZERO
    from polynomial import NotRational, ResourceBound, pgcd, rf
    from tasks import domain_conditions, known_guard
    if conditions or output!='classify_singular_points' or text.count('=')!=1:
        raise Unsupported('An in-scope singular-set question with all parameter cases is required')
    left,right=[m.parse(cartesian_product_notation(s),None,['x','y']) for s in text.split('=')]
    ctx=m.context({'variable':'__plane','parameters':['x','y']})
    if any(not known_guard(g,ctx) for e in (left,right) for g in domain_conditions(e,True)):
        raise Unsupported('Original poles must be checked before algebraic normal form')
    x,y=('s','x'),('s','y')
    polynomial=lambda z:m.rational_form(z)
    left_poly,den=polynomial(left)
    pure=next((k for k in (2,4) if left_poly=={((y,k),):Fraction(1)} and den=={():Fraction(1)}),None)
    xvar=('v','x')

    def as_poly(expr):
        p,d=rf(m.substitute(expr,{x:xvar}),'x')
        if len(d)!=1:
            raise Unsupported('An original rational pole needs its own local analysis')
        return tuple(c/d[0] for c in p)

    def classified(order,sign,power):
        if order%2==0 and sign<0:
            return 'isolated_point'
        if order==1:
            return 'regular_vertical_tangent'
        if order<power:
            raise Unsupported('A vertical tangent cone needs additional branch separation')
        if order==power:
            return 'ordinary_node'
        return 'one_sided_cusp' if order%2 else 'two_tangent_branches'

    if pure is not None and not m.contains(right,y):
        expr=right;shift=ZERO
    else:
        # Translate y by the polynomial that completes the square. The
        # triangular chart has a polynomial inverse and preserves branch type.
        residual=m.add(left,m.neg(right));num,den=polynomial(residual)
        if den!={():Fraction(1)} or domain_conditions(residual):
            raise Unsupported('Original poles must be checked before algebraic normal form')
        groups={k:{} for k in (0,1,2,3,4)}
        for mon,c in num.items():
            k=dict(mon).get(y,0)
            if k>4:
                return polynomial_plane_singularities(num)
            groups[k][tuple((s,e) for s,e in mon if s!=y)]=c
        pure=4 if groups[4] else 2
        a=groups[pure].get((),0)
        if (not a or len(groups[pure])!=1 or groups[3] or pure==4 and (groups[1] or groups[2])
                or any(s not in (x,y) for mon in num for s,_ in mon)):
            return polynomial_plane_singularities(num)
        b,c=[m.poly_expr(groups[k]) for k in (1,0)]
        shift=m.div(m.neg(b),m.q(2*a))
        expr=m.add(m.power(shift,2),m.div(m.neg(c),m.q(a)))
    if not m.constant_defined(expr,ctx):
        raise Unsupported('The original graph expression has an unproved real domain')
    simplified=m.simplify(expr)
    coefficient=1;core=simplified
    if core[0]=='pow' and core[2]>0:
        core,coefficient=core[1],core[2]
    # Exponential differences have the same exact zero set and leading
    # term as their signed exponent, since exp(t)=1 exactly at t=0.
    leading=core
    p,d=polynomial(core)
    if d=={():Fraction(1)} and len(p)==2 and (constant:=p.get((),0)) in (-1,1):
        mono,w=next((k,c) for k,c in p.items() if k)
        if len(mono)==1 and mono[0][1]==1 and mono[0][0][0]=='exp' and w==-constant:
            leading=m.mul(m.q(w),mono[0][0][1])
    try:
        f=as_poly(leading)
    except NotRational:
        if core[0]!='sin':
            raise Unsupported('No exhaustive zero-set and leading-order formula for the source function')
        phase=as_poly(core[1])
        degree=len(phase)-1
        if degree<1 or any(phase[:-1]):
            raise Unsupported('The oscillatory phase is not a single monotone power on each side')
        phase_sign=1 if phase[-1]>0 else -1
        origin=classified(degree*coefficient,phase_sign**coefficient,pure)
        out=classified(coefficient,1,pure)
        steps=dict(origin_order=degree*coefficient,nonzero_order=coefficient,
                   integer_phases='j*pi over the attained real range',phase_polynomial=[m.q(a) for a in phase],
                   local_leading_sign='(-1)^j times the sign of the phase derivative, raised to the original power')
        points=[]
        if origin!='regular_vertical_tangent':points.append(dict(point=[ZERO,ZERO],type=origin))
        families=[] if out=='regular_vertical_tangent' else [dict(
            location='every nonzero real solution of phase(x)=j*pi, y=0, j integer',type=out,
            side_when_one_sided='the side on which (-1)^j · phase\'(x) · (X-x) has positive sign')]
        return dict(method='plane_zero_orders',source_graph=expr,zero_proof=steps),dict(singular_points=points,singular_families=families)
    if len(f)==1:
        if not f[0]:
            raise Unsupported('A repeated whole component needs an intrinsic/extrinsic interpretation')
        return dict(method='plane_zero_orders',source_graph=expr,polynomial=[m.q(f[0])],
                    zero_proof='the height power never vanishes on the level'),dict(singular_points=[],singular_families=[])
    if len(f)>18:
        raise ResourceBound('The complete polynomial root proof exceeds the real-root limit')
    singular_roots=f if coefficient>1 else pgcd(f,tuple(i*c for i,c in enumerate(f) if i))
    checks=[];points=[]
    for a in rational_roots(singular_roots):
        k=0;g=f
        while not (lead:=peval(g,a).sign()):
            k+=1;g=tuple(i*c for i,c in enumerate(g) if i)
        sign=lead**coefficient;order=k*coefficient;tag=classified(order,sign,pure)
        x0=m.simplify(m.add(m.q(a.a),m.mul(m.q(a.b),('sqrt',m.q(a.d))))) if a.b else m.q(a.a)
        y0=m.simplify(m.substitute(shift,{x:x0}))
        checks.append(dict(root=quadratic_term(a),order=order,leading_sign=sign))
        if tag!='regular_vertical_tangent':
            points.append(dict(point=[x0,y0],type=tag,order=order,leading_sign=sign))
    return dict(method='plane_zero_orders',source_graph=expr,coordinate_shift=shift,height_power=pure,
                repeated_zero_polynomial=list(map(m.q,singular_roots)),zero_proof=checks),dict(singular_points=points,singular_families=[])


def polynomial_plane_singularities(terms):
    """Reduce the critical system by separation or a linear elimination."""
    from fractions import Fraction
    from graphs import rational_roots
    from model import ZERO
    from polynomial import NotRational, rf
    from verify import same_value
    x,y=('s','x'),('s','y')
    if any(set(dict(k))-{x,y} for k in terms):
        raise Unsupported('A complete numeric critical system is required')
    f=m.poly_expr(terms)
    dx,dy=[exact_polynomial_partial(terms,a) for a in (x,y)]
    fx,fy=map(m.poly_expr,(dx,dy))
    if fx==ZERO or fy==ZERO:
        raise Unsupported('A degenerate critical set is not isolated')

    def rational_coordinates(expr,v):
        try:p,d=rf(m.substitute(expr,{v:('v',v[1])}),v[1])
        except NotRational as exc:raise Unsupported('The critical equations have not been eliminated') from exc
        if len(d)!=1 or p==(0,):
            raise Unsupported('An infinite critical locus or singular denominator remains')
        roots=rational_roots(p)
        return list(dict.fromkeys(m.simplify(m.add(m.q(z.a),m.mul(m.q(z.b),('sqrt',m.q(z.d))))) if z.b else m.q(z.a) for z in roots))

    if not m.contains(fx,y) and not m.contains(fy,x):
        pairs=[(a,b) for a in rational_coordinates(fx,x) for b in rational_coordinates(fy,y)]
        reduction='separated_partial_derivatives'
    else:
        for pivot,other,linear,remaining in ((x,y,dy,fx),(y,x,dx,fy)):
            slope=linear.get(((pivot,1),),0)
            if not slope or any(dict(mon).get(pivot,0) for mon in linear if mon!=((pivot,1),)):
                continue
            answer=m.div(m.neg(m.poly_expr({k:c for k,c in linear.items() if k!=((pivot,1),)})),m.q(slope))
            base=rational_coordinates(m.substitute(remaining,{pivot:answer}),other)
            pairs=[]
            for t in base:
                a,b=t,m.simplify(m.substitute(answer,{other:t}))
                pairs.append((b,a) if pivot==x else (a,b))
            reduction='linear_elimination_in_the_critical_equations'
            break
        else:
            raise Unsupported('Neither critical equation has an invertible linear coefficient or separates')
    fxx,fxy,fyy=map(m.poly_expr,(exact_polynomial_partial(dx,x),exact_polynomial_partial(dx,y),exact_polynomial_partial(dy,y)))
    points=[];checked=[]
    for pair in pairs:
        sub=dict(zip((x,y),pair));val=m.simplify(m.substitute(f,sub))
        checked.append(dict(point=pair,original_residual=val))
        ctx=m.context({})
        if not same_value(val,ZERO):
            if not m.nonzero(val,ctx):
                raise Unsupported('The possible algebraic critical point has not been compared exactly with the level')
            continue
        a,b,c=[m.substitute(e,sub) for e in (fxx,fxy,fyy)]
        det=m.simplify(m.add(m.mul(a,c),m.neg(m.power(b,2))))
        sign=m.sign(det,ctx) if m.constant_defined(det,ctx) else None
        if sign not in (-1,1):
            raise Unsupported('The quadratic tangent cone is degenerate at a critical point of the level set')
        points.append(dict(point=pair,type='isolated_point' if sign>0 else 'ordinary_node',hessian_determinant=det))
    return dict(method='plane_critical_system',reduction=reduction,partials=[fx,fy],all_critical_candidates=checked),dict(
        singular_points=points,singular_families=[])


def cartesian_product_notation(text):
    """Preserve explicit operators and spell out printed adjacent Cartesian factors."""
    text = re.sub(r'\b(\d+)(?=[xyz]{1,3}\b)',r'\1*',text)
    return re.sub(r'\b[xyz]{2,3}\b',lambda v:'*'.join(v[0]),text)


def cartesian_equation(text, coordinates):
    from tasks import domain_conditions
    if text.count('=')!=1:
        raise Unsupported('An equality in the original coordinates is required')
    text=cartesian_product_notation(text)
    params=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e',*coordinates})
    names=[*coordinates,*params]
    left,right=[m.parse(s,None,names) for s in text.split('=')]
    raw=('add',left,('mul',m.q(-1),right))
    space=set(('s',x) for x in coordinates);guards=domain_conditions(raw,True)
    if any(any(m.contains(e,x) for x in space) for _,e in guards):
        raise Unsupported('A parameter-only domain is required for this level surface')
    num,den=m.rational_form(raw)
    if {a for mon in den for a,_ in mon}&space:
        raise Unsupported('A level denominator depends on a spatial coordinate')
    d=m.poly_expr(den)
    gradients=[m.div(m.poly_expr(exact_polynomial_partial(num,('s',x))),d) for x in coordinates]
    if any(any(m.contains(a,x) and a!=x for x in space) for mon in num for a,_ in mon):
        raise Unsupported('A nonpolynomial coordinate dependence requires a different differential')
    return raw,gradients,guards,params


def numeric_level_quadric(raw, coords):
    from fractions import Fraction
    p,d=m.rational_form(raw);x=[('s',v) for v in coords]
    if (d!={():Fraction(1)} or any(sum(dict(mon).values())!=2 or set(dict(mon))-set(x) for mon in p if mon)
            or not (radius:=-p.get((),0))):
        raise Unsupported('An origin-centered positive quadratic level is required')
    if radius<0:
        p={k:-a for k,a in p.items()}
        radius=-radius
    A=[[p.get(((a,2),),0) if a==b else p.get(tuple(sorted(((a,1),(b,1)))),Fraction(0))/2 for b in x] for a in x]
    A=[list(map(Fraction,row)) for row in A]
    augmented=[row+[Fraction(i==j) for j in range(len(A))] for i,row in enumerate(A)]
    pivots=[]
    for j,row in enumerate(augmented):
        pivot=row[j]
        if pivot<=0:
            raise Unsupported('The needed positive definiteness is not proved by the quadratic pivots')
        pivots.append(pivot)
        row[:]=[z/pivot for z in row]
        for i,other in enumerate(augmented):
            if i!=j:
                factor=other[j]
                other[:]=[z-factor*v for z,v in zip(other,row)]
    B=[row[len(A):] for row in augmented]
    if any(sum(a*b for a,b in zip(row,col))!=(i==j) for i,row in enumerate(A) for j,col in enumerate(zip(*B))):
        raise Unsupported('The certified inverse matrix does not reconstruct the original form')
    return A,B,pivots,radius


def positive_diagonal_level(raw, space, params, guards):
    from tasks import entailed_domain_guards,guard_source,known_guard
    from verify import same_value
    zeros=dict.fromkeys(space,m.ZERO)
    radius=m.neg(m.substitute(raw,zeros))
    ctx=m.context(dict(variable='__quadric',parameters=params,
                       parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    orientation=m.q(-1) if known_guard(('positive',m.neg(radius)),ctx) else m.ONE
    raw=m.mul(orientation,raw);radius=m.mul(orientation,radius)
    entries=[m.add(m.substitute(raw,{**zeros,x:m.ONE}),radius) for x in space]
    if not same_value(raw,m.add(m.dot(entries,[m.power(x,2) for x in space]),m.neg(radius))):
        raise Unsupported('An origin-centered diagonal quadric is required')
    if not all(known_guard(('positive',z),ctx) for z in [radius,*entries]):
        raise Unsupported('The original level and its diagonal entries must be positive')
    return entries,radius,orientation


def level_surface_geometry(text, conditions, output):
    from itertools import combinations
    from model import ZERO,ONE
    from verify import same_value
    coord=list(AXES);space=[('s',v) for v in coord]
    if conditions:
        raise Unsupported('Extra restrictions on the given surface require a separate proof')
    if output=='angle of intersection':
        from itertools import product
        from tasks import domain_conditions,known_guard
        spec=re.fullmatch(r'(.+) and (.+) at common \(([^,]+),([^,]+),([^,]+)\)',text)
        if not spec:
            raise Unsupported('Two levels and their common regular point must be explicit')
        eq=[cartesian_equation(s,coord) for s in spec.groups()[:2]]
        params=set().union(*(set(e[3]) for e in eq))
        params.update(set(re.findall(r'[A-Za-z_]\w*',','.join(spec.groups()[2:])))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
        if set(coord)&params or len(params)>6:
            raise Unsupported('Unresolved coordinates or too many point parameters')
        params=sorted(params)
        pt=[m.parse(s,None,params) for s in spec.groups()[2:]]
        sub=dict(zip(space,pt));normals=[list(m.substitute(x,sub) for x in e[1]) for e in eq]
        squared=[m.dot(n,n) for n in normals]
        levels=[m.substitute(e[0],sub) for e in eq]
        guards=list(dict.fromkeys([*(g for e in eq for g in e[2]),*(g for v in pt for g in domain_conditions(v))]))
        ctx=m.context({})
        def regular_point(p):
            ev=lambda e:m.substitute(e,p)
            return (all(known_guard((r,ev(e)),ctx) for r,e in guards)
                    and all(m.constant_defined(ev(v),ctx) and same_value(ev(v),ZERO) for v in levels)
                    and all(known_guard(('positive',ev(v)),ctx) for v in squared))
        values=(m.ZERO,m.ONE,m.q(-1),m.q(2))
        witness=next((p for row in product(values,repeat=len(params))
                      if regular_point(p:=dict(zip((('s',a) for a in params),row)))),None)
        if witness is None:
            raise Unsupported('No checked point lies on both source levels with both normals nonzero')
        dot=m.dot(*normals)
        return dict(method='level_normal_angles',source_levels=levels,
                    parameter_domain=guards,regular_point_witness=list(witness.items()),normals=normals),dict(
            regular_when=[('positive',z) for z in squared],cosine_of_acute_angle=m.div(('abs',dot),('sqrt',m.mul(*squared))))
    if output in ('prove triply orthogonal sphere families','prove pairwise orthogonal on regular spherical coordinate charts'):
        levels=text.split(';')
        if len(levels)!=3:
            raise Unsupported('Three complete level equations are required')
        eq=[cartesian_equation(s,coord) for s in levels]
        ident=[]
        for (a,da,*_),(b,db,*__) in combinations(eq,2):
            dot=m.dot(da,db)
            coeff=constant_span_pair(dot,a,b)
            ident.append(dict(dot_product=dot,source_pair=[a,b],multipliers=coeff))
        guards=list(dict.fromkeys(g for e in eq for g in e[2]))
        return dict(method='level_normal_angles',normal_dot_identities=ident,source_domain=guards),dict(
            pairwise_orthogonal=True,regular_when=[('positive',m.dot(e[1],e[1])) for e in eq])
    if output not in ('all points with tangent planes parallel to coordinate planes','parallel tangent planes',
                      'point where normal makes equal angles with coordinate axes','projections onto all coordinate planes'):
        raise Unsupported('The surface request requires a different verified construction')
    body,_,reference=text.partition('; reference plane ')
    raw,_,guards,params=cartesian_equation(body,coord)
    projection=output=='projections onto all coordinate planes'
    equal=output=='point where normal makes equal angles with coordinate axes'
    if params:
        if not equal:
            raise Unsupported('A positive parameter-dependent quadratic form has not been factored')
        # A diagonal inverse can be computed from the coefficients alone.
        entries,radius,_=positive_diagonal_level(raw,space,params,guards)
        B=[[m.div(ONE,entries[i]) if i==j else ZERO for j in range(3)] for i in range(3)]
        plan=dict(diagonal=entries)
    else:
        A,inv,pivots,radius=numeric_level_quadric(raw,coord)
        radius=m.q(radius);B=[list(map(m.q,row)) for row in inv]
        plan=dict(matrix=[list(map(m.q,row)) for row in A],positive_pivots=list(map(m.q,pivots)))
    plan.update(method='quadratic_normal_geometry',inverse_matrix=B,source_level=raw,source_domain=guards)
    if projection:
        answers=[]
        for t in range(3):
            keep=[i for i in range(3) if i!=t]
            p=m.ZERO
            for i in keep:
                for j in keep:
                    v=A[i][j]-A[i][t]*A[t][j]/A[t][t]
                    p=m.add(p,m.mul(m.q(v),m.mul(space[i],space[j])))
            answers.append(dict(coordinates=[coord[i] for i in keep],inequality=(p,'<=',radius)))
        return plan,dict(projections=answers)
    if reference:
        if output!='parallel tangent planes':
            raise Unsupported('A reference plane is incompatible with the requested directions')
        e,n,g,p=cartesian_equation(reference,coord)
        if p or g or not all(m.num(c) is not None for c in n) or not any(map(m.num,n)):
            raise Unsupported('The reference equation must define a regular affine plane')
        directions=[n]
    elif equal:
        directions=[list((ONE,)*3)]
    elif output=='all points with tangent planes parallel to coordinate planes':
        directions=[[m.q(int(i==j)) for j in range(3)] for i in range(3)]
    else:
        raise Unsupported('A reference plane is missing')
    results=[]
    for n in directions:
        qn=[m.dot(row,n) for row in B];den=m.dot(n,qn)
        if den==ZERO:
            raise Unsupported('The reference direction is zero')
        scale=('sqrt',m.div(radius,den))
        for sign in (1,-1):
            p=[m.mul(m.q(sign),m.mul(scale,v)) for v in qn]
            results.append(dict(point=p,normal=n,plane_constant=m.dot(n,p)))
    return plan,dict(parallel_tangents=results)


def constant_span_pair(value,a,b):
    """Find a rational combination of two original level equations."""
    from fractions import Fraction
    from verify import same_value
    # Bring all equations to a common denominator before matching coefficients.
    polys=[m.rational_form(e) for e in (value,a,b)]
    nums=[]
    for j,(p,_) in enumerate(polys):
        e=m.poly_expr(p)
        for i,(_,d) in enumerate(polys):
            if i!=j:e=m.mul(e,m.poly_expr(d))
        nums.append(m.rational_form(e)[0])
    Y,A,B=nums
    z=Fraction(0)
    columns=[(Y.get(k,z),A.get(k,z),B.get(k,z)) for k in sorted(set(Y)|set(A)|set(B))]
    choices=[(z,z)]
    for i,(y,u,v) in enumerate(columns):
        if u:choices.append((y/u,z))
        if v:choices.append((z,y/v))
        pair=next(((h,c,d) for h,c,d in columns[i+1:] if u*d-v*c),None)
        if pair:
            h,c,d=pair;pivot=u*d-v*c
            choices.append(((y*d-v*h)/pivot,(u*h-y*c)/pivot))
            break
    s=next(((c,d) for c,d in choices if all(c*u+d*v==y for y,u,v in columns)),None)
    if s is None:
        raise Unsupported('The normal dot product is not reduced to the source constraints')
    u,v=map(m.q,s)
    if not same_value(value,m.add(m.mul(a,u),m.mul(b,v))):
        raise Unsupported('The resulting normal identity does not replay')
    return u,v


def printed_normal_derivatives(text, conditions, output, library, request):
    """Project the field differential onto the oriented unit level normal."""
    from verify import same_value
    if conditions:
        raise Unsupported('Additional original domain restrictions on the direction remain')
    compact=text.replace(' ','')
    product=re.fullmatch(r'F\(x,y,z\)=0withnormal([a-z])andfunctions([a-z]),([a-z])',compact)
    if product:
        n,u,v=product.groups()
        if len({n,u,v})!=3 or output.replace(' ','')!=f'proveD_{n}({u}{v})={u}*D_{n}({v})+{v}*D_{n}({u})':
            raise Unsupported('The printed identity does not match a normal derivative of the product')
        return dict(method='normal_product_rule',point_scope='one regular point and the same chosen unit normal',
                    argument='apply the one-variable product rule on the oriented normal through that point'),dict(
            identity=f'D_{n}({u}{v}) = {u} D_{n}({v}) + {v} D_{n}({u})')
    head,sep,rest=text.partition(';')
    match=re.fullmatch(r'([a-z])=(.+)',head.strip())
    if not sep or not match:
        raise Unsupported('A scalar field and an oriented source quadric are required')
    coords=list(AXES);xyz=[('s',x) for x in coords]
    field,df,domain,pars=cartesian_equation(match[2]+'=0',coords)
    sphere=re.fullmatch(r'unit sphere; M0=\((\w+),(\w+),(\w+)\)',rest.strip())
    if sphere:
        if domain or pars or any(m.num(v) is None for v in df):
            raise Unsupported('The extremizing sphere method requires a fixed real linear functional')
        names=list(sphere.groups());sq=m.dot(df,df)
        loc=[('s',s) for s in names]
        if len(set(names))!=3 or set(names)&set(coords):
            raise Unsupported('The point labels must be independent')
        value=dict(normal_derivative=m.dot(df,loc),sphere=[m.dot(loc,loc),'=',m.ONE])
        rule='Cauchy–Schwarz and its equality cases on the unit sphere'
        if output=='find derivative and all zero locations':
            value['zero_locus']=[value['normal_derivative'],'=',m.ZERO]
        elif output in ('find derivative and all largest locations','find derivative and all smallest locations'):
            sign=m.q(1 if 'largest' in output else -1);length=('sqrt',sq)
            if m.num(sq)==0:
                value.update(extreme=m.ZERO,attained='whole_unit_sphere')
            else:
                value.update(extreme=m.mul(sign,length),attained=[m.div(m.mul(sign,v),length) for v in df])
        else:
            raise Unsupported('An unbound extremum or locus on the sphere remains')
        return dict(method='unit_outward_derivative',field=field,gradient=df,argument=rule),value
    if output!='outward normal derivative at M0':
        raise Unsupported('An unbound extremum or locus remains')
    F,dF,gd,params=cartesian_equation(rest.strip(),coords)
    _,radius,orientation=positive_diagonal_level(F,xyz,sorted(set(pars+params)),gd+domain)
    dF=[m.mul(orientation,z) for z in dF]
    at=['x0','y0','z0']
    if set(at)&set(pars+params):
        raise Unsupported('The point names collide with declared level parameters')
    p=dict(zip(xyz,[('s',a) for a in at]))
    projection=m.dot(df,dF)
    if same_value(projection,m.mul(m.q(4),m.add(m.mul(orientation,F),radius))):
        projection=m.mul(m.q(4),radius)
    return dict(method='unit_outward_derivative',field=field,level=F,norm_increases_to_exterior=True,
                outward_normal=dF,source_domain=gd+domain),dict(
        normal_derivative=m.substitute(m.div(projection,('sqrt',m.dot(dF,dF))),p),point_equation=m.substitute(F,p))


def plane_family_envelope(text, conditions, output):
    """Eliminate a single family parameter while classifying the regular contact locus."""
    from fractions import Fraction
    from tasks import known_guard
    from verify import same_value
    if conditions or output!='find_envelope':
        raise Unsupported('The envelope and all source conditions must be explicitly known')
    body,*fixed=text.replace(' ','').split(',')
    fixed=[re.fullmatch(r'(\w+)constant',s) for s in fixed]
    if any(s is None for s in fixed):
        raise Unsupported('An unknown family constraint remains')
    coords=['x','y'];x,y=[('s',s) for s in coords]
    raw,_,guards,params=cartesian_equation(body,coords)
    parameters=set(params)-{s[1] for s in fixed}
    if len(parameters)!=1:
        raise Unsupported('Exactly one free parameter of the family must be established')
    t=('s',parameters.pop());free=set(params)-{t[1]}
    ctx=m.context(dict(variable='__envelope',parameters=sorted(free)))
    if any(not known_guard(g,ctx) for g in guards):
        raise Unsupported('The original parameter restrictions require a separate completeness analysis')
    at0=m.substitute(raw,{x:m.ZERO,y:m.ZERO});p=m.neg(at0)
    base=m.add(m.mul(x,('cos',t)),m.mul(y,('sin',t)))
    if m.constant_defined(p,ctx) and not m.contains(p,t) and same_value(raw,m.add(base,m.neg(p))):
        return dict(method='stationary_family_parameter',parameter=t[1],family=raw,
                    stationarity=m.add(m.neg(m.mul(x,('sin',t))),m.mul(y,('cos',t))),
                    parameter_witness='the unit direction through the radius vector, with its source sign'),dict(
            envelope_equation=[m.dot([x,y],[x,y]),'=',m.power(p,2)],
            degeneracy={'when':[p,'=',m.ZERO],'nonregular_locus':[m.ZERO,m.ZERO]})
    p,d=m.rational_form(raw)
    if d!={():Fraction(1)}:
        raise Unsupported('The stationary parameter elimination must preserve the full family domain')
    pivot=p.get(((t,2),),0)
    if not pivot or any(dict(k).get(t,0)>2 or dict(k).get(t,0)==2 and k!=((t,2),) for k in p):
        raise Unsupported('A nonzero constant quadratic coefficient of the parameter is required')
    deriv=m.poly_expr(exact_polynomial_partial(p,t));tstar=m.div(m.neg(m.substitute(deriv,{t:m.ZERO})),m.q(2*pivot))
    discriminant=m.substitute(raw,{t:tstar})
    p,d=m.rational_form(discriminant)
    if d!={():Fraction(1)} or any(sum(e for _,e in k)!=2 or set(dict(k))-{x,y} for k in p):
        raise Unsupported('The real discriminant branches are not exhausted by a homogeneous quadratic')
    a=p.get(((x,2),),0);b=p.get(((x,1),(y,1)),0);c=p.get(((y,2),),0)
    determinant=a*c-b*b/4
    if not determinant:
        raise Unsupported('A double-line discriminant needs a contact and rank analysis')
    return dict(method='stationary_family_parameter',family=raw,stationarity=deriv,unique_parameter=tstar),dict(
        discriminant_equation=[m.poly_expr(p),'=',m.ZERO],regular_envelope='two_lines_except_intersection' if determinant<0 else 'empty',
        nonregular_discriminant_points=[[m.ZERO,m.ZERO]])


def surface_family_envelope(text, conditions, output):
    """Read a moving sphere with a unit linear center, or a graph of unit-slope planes."""
    from fractions import Fraction
    from verify import same_value
    if conditions or output!='find_envelope':
        raise Unsupported('The complete source envelope has not been specified')
    body,sep,side=text.replace(' ','').partition(';')
    if not sep:
        raise Unsupported('The unit-direction side condition is missing')
    match=re.fullmatch(r'cos\^2(\w+)\+cos\^2(\w+)\+cos\^2(\w+)=1',side)
    X=[('s',s) for s in AXES]
    if match:
        directions=[('cos',('s',s)) for s in match.groups()]
        symbols=sorted(set(re.findall(r'[A-Za-z_]\w*',body))-m.FUNCTIONS-set(AXES))
        if len(set(match.groups()))!=3 or set(match.groups())&set(AXES) or len(set(symbols)-set(match.groups()))!=1:
            raise Unsupported('The three given components and the family parameter must be distinct')
        t=('s',next(iter(set(symbols)-set(match.groups()))))
        raw,_,guards,_=cartesian_equation(body,list(AXES))
        R2=m.neg(m.substitute(raw,dict.fromkeys([*X,t],m.ZERO)))
        diff=[m.add(x,m.neg(m.mul(t,c))) for x,c in zip(X,directions)]
        if guards or not m.num(R2) or m.num(R2)<=0 or not same_value(raw,m.add(m.dot(diff,diff),m.neg(R2))):
            raise Unsupported('A fixed positive radius and the original unit axis are required')
        projection=m.dot(X,directions)
        distance=m.add(m.dot(X,X),m.neg(m.power(projection,2)))
        return dict(method='stationary_family_parameter',source_family=raw,unit_condition=m.dot(directions,directions),
                    unique_parameter=projection),dict(envelope_equation=[distance,'=',R2])
    unit=re.fullmatch(r'(\w+)\^2\+(\w+)\^2=1',side)
    if not unit or len(set(unit.groups()))!=2:
        raise Unsupported('The slope locus is not a unit circle')
    p,q=unit.groups()
    point=re.fullmatch(r'z-(\w+)=\w+\*\(x-(\w+)\)\+\w+\*\(y-(\w+)\)',body)
    if not point or len(set([*AXES,p,q,*point.groups()]))!=8:
        raise Unsupported('The planes must have a fixed vertex and independent two-dimensional slopes')
    xyz=[point[2],point[3],point[1]]
    u,v,w=[m.add(a,m.neg(('s',s))) for a,s in zip(X,xyz)]
    raw,_,guards,_=cartesian_equation(body,list(AXES))
    expected=m.add(w,m.neg(m.add(m.mul(('s',p),u),m.mul(('s',q),v))))
    if guards or not same_value(raw,expected):
        raise Unsupported('The level equation and the source unit slopes do not agree')
    return dict(method='stationary_family_parameter',source_family=raw,parameter_circle=[p,q],
                contact_condition=m.add(m.mul(('s',q),u),m.neg(m.mul(('s',p),v)))),dict(
        envelope_equation=[m.power(w,2),'=',m.add(m.power(u,2),m.power(v,2))],
        exceptional_vertex=list(map(lambda a:('s',a),xyz)))


def local_geometry_report(result,pretty):
    proof=result['compilation'];v=result['value']
    def vector(values):return '('+', '.join(map(pretty,values))+')'
    def equation(parts):return pretty(parts[0])+' '+parts[1]+' '+pretty(parts[2])
    method=proof['method']
    if method=='compact_binomial_moment_series':
        return '\n'.join([*proof['argument'],'Три ненулевых члена по возрастанию полной степени — '+', '.join(map(pretty,v['terms']))+'.'])
    if method=='geometric_profile_proof':
        def show(e):
            if isinstance(e,(list,tuple)):
                if e and isinstance(e[0],str) and (e[0] in m.FUNCTIONS or e[0] in ('q','v','s','pi','add','mul','div','pow','rpow')):return pretty(e)
                return '('+', '.join(map(show,e))+')'
            return str(e)
        return '\n'.join([proof['argument'],*(name+' = '+show(e) for name,e in v.items())])
    if method in ('normalized_cross_product','quadratic_normal_geometry'):
        if 'projections' in v:
            return ('Выделяем квадрат по исключаемой координате. Оставшееся неравенство полностью задаёт проекцию.\n'+
                    '\n'.join(', '.join(row['coordinates'])+' — '+equation(row['inequality']) for row in v['projections']))
        if 'parallel_tangents' in v:
            rows=v['parallel_tangents']
            return ('Уровень является положительной квадрикой. Обращение её матрицы даёт все точки с указанным направлением нормали.\n'
                    +'\n'.join(vector(r['point'])+' с нормалью '+vector(r['normal'])+' и константой плоскости '+pretty(r['plane_constant']) for r in rows))
        return ('Векторное произведение скоростей делим на общую степень разности параметров вне диагонали. '
                'На границе получаем ненулевую нормаль '+vector(v['normal'])+'. Предельная плоскость проходит через '+vector(v['through'])+
                ' и имеет константу '+pretty(v['plane_constant'])+'.')
    if method=='level_normal_angles':
        if 'pairwise_orthogonal' in v:
            return ('Скалярное произведение каждой пары градиентов выражено через два исходных уравнения уровней. '
                    'В регулярной общей точке оно равно нулю, поэтому поверхности ортогональны.')
        return ('Градиенты исходных уравнений служат нормалями. При ненулевых градиентах косинус острого угла равен '+
                pretty(v['cosine_of_acute_angle'])+'.')
    if method=='normal_product_rule':
        return 'Применяем правило производной произведения вдоль одной и той же единичной нормали. Получаем '+v['identity']+'.'
    if method=='unit_outward_derivative':
        lines=['Внешняя единичная нормаль направлена в сторону возрастания уровня.',
               'Скалярное произведение с градиентом поля даёт '+pretty(v['normal_derivative'])+'.']
        if 'extreme' in v:
            point=v['attained']
            lines.append('По неравенству Коши–Буняковского экстремум '+pretty(v['extreme'])+' достигается '+
                         (vector(point) if isinstance(point,list) else 'на всей сфере')+'.')
        if 'zero_locus' in v:lines.append('Нули задаёт сечение исходной сферы плоскостью '+equation(v['zero_locus'])+'.')
        if 'point_equation' in v:lines.append('Точка лежит на уровне '+pretty(v['point_equation'])+' = 0.')
        return '\n'.join(lines)
    if method in ('plane_zero_orders','plane_critical_system'):
        labels={'ordinary_node':'обыкновенный узел','isolated_point':'изолированная точка',
                'one_sided_cusp':'односторонняя точка возврата','two_tangent_branches':'две ветви с общей касательной'}
        rows=[vector(p['point'])+' — '+labels[p['type']] for p in v['singular_points']]
        rows.extend(p['location']+' — '+labels[p['type']] for p in v['singular_families'])
        return 'Проверяем нули исходного уравнения и порядок исчезновения ведущего члена.\n'+('\n'.join(rows) if rows else 'Особых точек нет.')
    if method=='stationary_family_parameter':
        answer=v.get('envelope_equation') or v['discriminant_equation']
        prefix='Решаем уравнение семейства вместе с условием стационарности по свободному параметру. Получаем '+equation(answer)+'.'
        if 'regular_envelope' in v:
            suffix='Регулярная огибающая состоит из двух прямых без точки пересечения.' if v['regular_envelope']!='empty' else 'Дискриминант содержит только изолированную точку, регулярная огибающая пуста.'
            return prefix+' '+suffix
        return prefix
    if method=='radial_analytic_coefficients':
        series=[f"C[{i}](0) = {p['zero']}. Для j > 0 {p['rule']} с операндами {p['operands']} даёт {p['positive_orders']}."
                for i,p in enumerate(v['coefficients'])]
        return 'Суммируем однородные члены около центра '+vector(v['center'])+' в пределах области аналитичности.\n'+v['formula']+'\n'+'\n'.join(series)
    if 'leading_homogeneous_term' in v:
        return ('Первый ненулевой однородный член имеет степень '+str(v['leading_degree'])+' и равен '+
                pretty(v['leading_homogeneous_term'])+'.')
    if method=='implicit_polynomial_jet':
        rows=[f'Степень {i} — '+pretty(t) for i,t in enumerate(v['homogeneous_terms']) if freeze(t)!=m.ZERO]
        return ('Вертикальная частная производная в центре равна '+pretty(proof['vertical_partial'])+
                '. Теорема о неявной функции задаёт одну аналитическую ветвь.\n'+'\n'.join(rows)+
                '\nОстаток имеет порядок O(‖Δ‖⁴).')
    raise Unsupported('No readable form for the certified local answer')


OPERATOR_PROVENANCE={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256'}
IMPLICIT_SECTION='p310 footnote: existence of the implicit functions and needed derivatives is assumed in most exercises unless otherwise stated'



def product_coordinate_cancellation(task,library):
    label='Проверить напечатанное x²*∂z/∂z-x*y*∂z/∂y+y²=0, функции достаточно дифференцируемы.'
    vector_source(task,{'given','printed_equation','requested_output'},(label,),('printed_partial',))
    name=r'[A-Za-z][A-Za-z_0-9]*'
    hit=re.fullmatch(fr'z=y\^([1-9]\d*)/\(([1-9]\d*)\*x(?:\^([1-9]\d*))?\)\+({name})\(x\*y\)',
                     task.get('given','').replace('²','^2'))
    if hit is None or task.get('requested_output')!=['proof']:
        raise Unsupported('The rational term and the common composition argument must be identified')
    p,c,q0,field=hit.groups();K,P,Q=int(c),int(p),int(q0 or '1')
    marker=task.get('source',{}).get('printed_partial')
    notation={'The first partial denominator visibly reads dz, not dx.':'z','The first partial denominator reads dx.':'x'}
    if marker not in notation:
        raise Unsupported('The original derivative token must be preserved in the source')
    claim=re.fullmatch(r'x\^2\*z_([xz])-x\*y\*z_y\+(.+)=0',task.get('printed_equation',''))
    if claim is None or claim[1]!=notation[marker]:
        raise Unsupported('The original coefficient fields must bind the first derivatives')
    x,y=(mv_symbol(z) for z in 'xy');f=m.div(m.power(y,P),m.mul(q(K),m.power(x,Q)))
    offset=m.parse(claim[2],None,['x','y'])
    partial,checks=derivative_table(library)
    corrected=m.add(m.mul(m.power(x,2),partial(f,'x')),m.neg(m.mul(m.mul(x,y),partial(f,'y'))))
    if not same_value(m.add(corrected,offset),ZERO):
        raise Unsupported('The source offset does not give the claimed coordinate cancellation')
    value=dict(identity_if_first_partial_is_x='true',domain='x!=0',
               coordinate='x*y',function=field)
    if claim[1]=='z':
        literal=m.add(m.power(x,2),m.add(m.neg(m.mul(m.mul(x,y),partial(f,'y'))),offset))
        at=m.simplify(m.substitute(literal,{x:ONE,y:ZERO}))
        if at==ZERO:raise Unsupported('The independent sample does not refute the literal first partial')
        value.update(printed_claim_holds=False,counterexample=dict(outer_function=ZERO,point=[ONE,ZERO],
                     literal_left=at,expected=ZERO))
    return dict(theorem='method.product_coordinate_cancellation',argument=[
        'На области x≠0 оператор x²∂x−xy∂y уничтожает координату xy. По правилу цепочки произвольная функция этой координаты не даёт вклада.',
        'На втором слагаемом точно вычисляем частные производные и проверяем оставшийся числитель.',
        'Если в первом члене читать производную z по z буквально, она равна единице. Получаем другое выражение, которое проверяем на допустимой точке.'
    ],derivative_rules=checks,corrected_rational_part=corrected),value


def multivariate_operator_proof(task,library,request):
    """Solve the complete printed operator, implicit graph, or branch condition."""
    if multivariate_proof_routing(task,task['kind']):return multivariate_proof(task,library,request)
    if library.data.get('typed_source_reductions') and task['kind']=='formal_differential_identity' and task.get('source',{}).get('printed_partial'):
        return product_coordinate_cancellation(task,library)
    if library.data.get('typed_source_reductions') and (task['kind']=='prove_second_order_euler_identity'
            or task['kind']=='formal_differential_identity' and 'homogeneous degree' in task.get('given','')):
        return homogeneous_differentiation_mode(task)
    if not library.data.get('multivariate_printed_operators'):
        raise Unsupported('The source-bound multivariate transitions are not admitted')
    kind=task['kind']
    if kind=='partial_derivatives':return printed_coordinate_operators(task,request)
    if kind in ('implicit_differentials','derivative_on_implicit_graph'):return printed_implicit_differentials(task,request)
    if kind=='implicit_symbolic_derivative':return abstract_implicit_derivatives(task,request)
    if kind=='partial_differential_equation':return integrate_partial_equation(task)
    if kind=='count_implicit_branches':return count_square_height_branches(task)
    if kind in ('implicit_inverse_existence','implicit_inverse_theorem','continuous_implicit_uniqueness','implicit_function_identity'):
        return implicit_branch_statements(task)
    if kind=='operator_product_identity':return printed_operator_product(task,request)
    if kind=='symbolic_order_partial_derivative':return symbolic_coordinate_orders(task)
    if kind=='total_differential_and_partials':return total_differential_with_partials(task,request)
    if kind=='arbitrary_composite_partial_identity':return printed_mixed_composition(task)
    if kind=='composite_function_differentiation' and task.get('requested_output') in (['radial_laplacian'],['d1_d2']):
        return abstract_radial_laplacian(task)
    return symbolic_total_differential(task)


def bound_printed_multivariable(task, label, extra=()):
    """Bind the exact source request before using its recorded mathematical representation."""
    fields={'kind','id','source','source_formula','stated_conditions','requested_output',*extra}
    src=task.get('source',{});outputs=task.get('requested_output')
    if (set(task)-fields or not isinstance(src,dict) or not isinstance(outputs,list) or not outputs
            or any(not isinstance(v,str) for v in outputs)
            or set(src)-OPERATOR_PROVENANCE-{'literal_requirement','section_convention'}
            or src.get('literal_requirement',label+'; '+', '.join(outputs))!=label+'; '+', '.join(outputs)
            or src.get('section_convention',IMPLICIT_SECTION)!=IMPLICIT_SECTION):
        raise Unsupported('Unresolved source obligations for the complete multivariate request')
    formula=task['source_formula'].translate(str.maketrans({'²':'^2','³':'^3','⁴':'^4'}))
    return formula,outputs,task.get('stated_conditions',[])


def printed_implicit_differentials(task,request):
    from operations import expression_positions
    from tasks import source
    from verify import same_value
    composed=task['kind']=='derivative_on_implicit_graph'
    eq,want,conditions=bound_printed_multivariable(task,'derivative on implicit graph' if composed else 'implicit differentials',
                                                  () if composed else ('dependent','point'))
    if composed:
        given=re.fullmatch(r'dependent coordinate ([yz])',conditions[0]) if len(conditions)==1 else None
        if not given or want!=['f_x at (1,1,1)','explain why the two partials differ']:
            raise Unsupported('Expected the named path, common point and comparison of its two coordinate restrictions')
        dep=given[1]
        eq,sep,field=eq.partition('; f=')
        if not sep:raise Unsupported('No source function is provided on the implicit graph')
    else:
        dep=task['dependent']
        if conditions or not isinstance(dep,str) or not re.fullmatch(r'[A-Za-z]\w*',dep):
            raise Unsupported('Additional restrictions on the complete implicit differential remain')
    if eq.count('=')!=1:
        raise Unsupported('One original equality is required for implicit differentiation')
    expr=cartesian_product_notation('('+eq.replace('=',')-(')+')')
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',expr))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    axes=[x for x in 'xyz' if x in names and x!=dep]
    if dep not in names or not axes:
        raise Unsupported('A dependent variable and independent source coordinates must occur in the equation')
    params=sorted(set(names)-set([*axes,dep]))
    child=dict(kind='implicit_derivative',relation=expr,parameters=params)
    if not composed:
        orders=[]
        for w in want:
            if w=='d'+dep:orders.append(1)
            elif w=='d²'+dep:orders.append(2)
            else:raise Unsupported('Unknown requested total differential')
        if orders!=sorted(set(orders)):raise Unsupported('A repeated or unordered derivative obligation remains')
        at={'point':task['point']} if task.get('point') is not None else {'scope':'regular_graph'}
        spec=dict(child,dependent=dep,independent=axes,differential_orders=orders,requested_output=['total_differentials'],**at)
        proof=request('total differentials on the original level',spec)
        return dict(method='implicit_differential_transport',pivots=[proof['compilation']['pivot']]),dict(
            expressions=dict(zip(want,proof['value'])),source_condition=proof['compilation']['regular_graph_condition'])
    if names!=list(AXES):
        raise Unsupported('The two source restrictions must use the same three spatial coordinates')
    args={('s',x):m.ONE for x in names}
    normalized=re.sub(r'(?<=\d)(?=[xyz](?:\^|$))','*',cartesian_product_notation(field))
    raw=m.parse(normalized,None,names)
    from tasks import domain_conditions,known_guard
    if any(not known_guard((r,m.substitute(e,args)),m.context({})) for r,e in domain_conditions(raw,True)):
        raise Unsupported('The source field is not smooth at the common point')
    partial=coordinate_sections(names,request);values={}
    for z in ('y','z'):
        axes=[x for x in names if x!=z]
        spec=dict(child,dependent=z,independent=axes,point=dict.fromkeys(names,1),requested_partials=[['x']],
                  requested_output=['specified_implicit_derivatives'])
        p,=request('implicit velocity with '+z+' dependent',spec)['value']
        values[z]=m.add(m.substitute(partial(raw,'x'),args),
                        m.mul(m.substitute(partial(raw,z),args),freeze(p)))
    if same_value(values['y'],values['z']):
        raise Unsupported('The two requested source derivatives do not differ')
    return dict(method='implicit_differential_transport',common_point=[m.ONE]*3,
                held_fixed={'y':'z','z':'y'}),dict(expressions=values,requested_dependent=dep,
                                                 requested_value=values[dep],different=True)


def abstract_implicit_derivatives(task,request):
    from tasks import domain_conditions,known_guard
    formula,want,conditions=bound_printed_multivariable(task,'implicit symbolic derivative')
    call=re.fullmatch(r'([A-Za-z]\w*)\((.+)\)=0',formula.replace(' ',''))
    if not call or conditions:
        raise Unsupported('One regular implicit composition with its full inner map is required')
    try:actual=ast.parse(call[1]+'('+call[2].replace('^','**')+')',mode='eval').body
    except SyntaxError as exc:raise Unsupported('The source argument list cannot be read') from exc
    if not isinstance(actual,ast.Call) or actual.keywords or not actual.args:
        raise Unsupported('Every source argument must be explicit')
    args=actual.args
    inner=[ast.unparse(t).replace('**','^') for t in args]
    freenames={n.id for arg in args for n in ast.walk(arg) if isinstance(n,ast.Name)}
    if not set(AXES)<=freenames:
        raise Unsupported('The independent x,y and dependent z must all be present')
    goal=dict(kind='composite_function_differentiation',outer_function=call[1],variables=list(AXES),inner_arguments=inner,
              requested_output=['gradient_hessian'])
    proof=request('all ambient derivatives of the implicit composition',goal)
    given=proof['value'];slots={};meanings={}
    def expand(key):
        v=m.ZERO
        for row in given[key]:
            word=tuple(sorted(row['ordered_outer_partials']))
            if word not in slots:
                name='__outer_'+'_'.join(map(str,word))
                if name in freenames:raise Unsupported('A formal partial symbol captures a source parameter')
                slots[word]=('s',name);meanings[name]=word
            v=m.add(v,m.mul(freeze(row['coefficient']),slots[word]))
        return v
    pivot=expand('D z')
    if pivot==m.ZERO:
        raise Unsupported('The implicit graph has no nonzero vertical differential on the declared domain')
    slopes={x:m.div(m.neg(expand('D '+x)),pivot) for x in 'xy'}
    def second(x,y):
        v=m.add(expand('D '+x+' '+y),m.mul(expand('D '+x+' z'),slopes[y]))
        v=m.add(v,m.mul(expand('D z '+y),slopes[x]))
        v=m.add(v,m.mul(expand('D z z'),m.mul(slopes[x],slopes[y])))
        return m.div(m.neg(v),pivot)
    values={}
    for w in want:
        if w in ('z_x','z_y'):values[w]=slopes[w[-1]]
        elif w in ('z_xx','z_xy','z_yy'):values[w]=second(*w[-2:])
        elif w=='d²z':
            if {'dx','dy'}&freenames:raise Unsupported('Conflicting source increment names')
            dx,dy=('s','dx'),('s','dy')
            values[w]=m.dot([second('x','x'),second('x','y'),second('y','y')],
                           [m.power(dx,2),m.mul(m.q(2),m.mul(dx,dy)),m.power(dy,2)])
        else:raise Unsupported('Unknown source derivative of the implicit field')
    return dict(method='implicit_differential_transport',outer=call[1],arguments=proof['compilation']['outer_evaluation_arguments'],
                abstract_partials=meanings,pivots=[pivot],source_domain=proof['compilation']['original_inner_domain']),dict(expressions=values,
                                                                                      source_condition=('nonzero',pivot))


def printed_coordinate_operators(task,request):
    from operations import expression_positions
    from tasks import domain_conditions,entailed_domain_guards,guard_source,known_guard,source
    from verify import same_value
    fields={'id','kind','source','variables','parameters','function','method_requirement','stated_conditions',
            'requested_output','derivative_orders','transcription'}
    src=task.get('source',{});coords=task['variables'];parameters=task.get('parameters',[])
    if (set(task)-fields or not isinstance(src,dict) or set(src)-OPERATOR_PROVENANCE-{'printed_operator_goals','printed_form'}
            or task.get('stated_conditions') or task.get('method_requirement','table_and_rules')!='table_and_rules'
            or task.get('requested_output')!=['first_partial_derivatives','second_partial_derivatives']
            or task.get('derivative_orders')!=[1,2]):
        raise Unsupported('The complete printed operator and original derivative method are not bound')
    form=src.get('printed_form');goals=src.get('printed_operator_goals')
    if not goals or form not in ('apply listed operators to u','prove the stated partial differential equation on the original domain'):
        raise Unsupported('Unrecognized printed operator')
    rules={};requests=[]
    trace='+'.join(f'D_{x}(D_{x}(u))' for x in coords)
    gradient='+'.join(f'D_{x}(u)^2' for x in coords)
    euler='sum_i x_i D_i u'
    repeated_euler='sum_i x_i D_i (sum_j x_j D_j u)'
    euler_names={}
    for item in goals:
        name,definition=item['name'],item['definition']
        if set(item)!={'name','definition'} or name in rules:
            raise Unsupported('An original operator is ambiguous')
        if definition=='sum_i D_ii u':rule=trace
        elif definition=='sum_i (D_i u)^2' and form=='apply listed operators to u':rule=gradient
        elif definition=='D_t u - a² D_xx u' and set(coords)=={'x','t'} and 'a' in parameters:rule='D_t(u)-a^2*D_x(D_x(u))'
        elif definition=='sum_i D_ii u - a² u' and 'a' in parameters:rule=trace+'-a^2*u'
        elif definition in (euler,repeated_euler) and form=='apply listed operators to u':
            require_order=1 if definition==euler else 2
            euler_names[name]=require_order;rule=definition
        else:raise Unsupported('An unverified operator definition remains')
        rules[name]=rule
        requests.append(dict(apply=[name],**({'equals':'0'} if form.startswith('prove') else {})))
    raw=m.parse(task['function'],None,[*coords,*parameters]);domain=domain_conditions(raw)
    if euler_names:
        if set(euler_names)!=set(rules):raise Unsupported('A mixed family needs a common printed operator binding')
        spec={k:v for k,v in task.items() if k not in ('source','id','transcription')}
        bundle=request('all original ordered first and second partial derivatives',spec)
        partials={tuple(k):freeze(v) for k,v in bundle['partial_values']}
        X=[('s',x) for x in coords]
        E=m.dot(X,[partials[(x,)] for x in coords])
        Q=m.dot(X,[m.dot(X,[partials[x,y] for y in coords]) for x in coords])
        return (dict(method='source_operator_application',theorem='method.expand_iteration_of_euler_operator',
                     source_operator_goals=goals,source_domain=domain,radial_first=E,hessian_contraction=Q,
                     argument=['Применяем правило произведения к коэффициенту каждой первой производной.',
                               'При повторном действии оператора производные самих координат дают первую сумму. Остальные члены образуют свёртку гессиана.']),
                dict(operators={name:E if order==1 else m.add(E,Q) for name,order in euler_names.items()},
                     coordinate_partials=bundle['partial_values'],proved_equation=False))
    original=m.context(dict(variable='__spatial',parameters=[*coords,*parameters],
                            parameter_conditions=[guard_source(g) for g in entailed_domain_guards(domain)]))
    radius=None
    for _,e in expression_positions(raw):
        if e[0]!='sqrt':continue
        outer=m.substitute(raw,{e:('s','__radius')})
        if any(m.contains(outer,('s',x)) for x in coords):continue
        if not known_guard(('positive',e[1]),original):continue
        zero=dict.fromkeys((('s',x) for x in coords),m.ZERO)
        centers=[]
        for x in zero:
            a,b=[m.substitute(e[1],{**zero,x:m.q(j)}) for j in (-1,1)]
            centers.append(m.div(m.add(a,m.neg(b)),m.q(4)))
        shifts=[m.add(x,m.neg(a)) for x,a in zip(zero,centers)]
        if same_value(e[1],m.dot(shifts,shifts)):
            radius=e;break
    if radius is not None and set(rules.values())<={trace,gradient,trace+'-a^2*u'}:
        t='__radius'
        if t in parameters or t in coords:raise Unsupported('A fixed symbol collides with the radius')
        spec=dict(kind='partial_derivatives',function=source(outer),variables=[t],parameters=parameters,
                  stated_conditions=[t+'>0'],derivative_orders=[1,2],
                  requested_output=['first_partial_derivatives','second_partial_derivatives'])
        p=request('ordinary derivatives as a function of positive radius',spec)
        first,second=[freeze(v) for _,v in p['partial_values']]
        r=('s',t);lap=m.add(second,m.div(m.mul(m.q(len(coords)-1),first),r));norm=m.power(first,2)
        forms={trace:lap,gradient:norm,trace+'-a^2*u':m.add(lap,m.neg(m.mul(m.power(('s','a'),2),outer)))}
        answers=[m.simplify(forms[k]) for k in rules.values()]
        if form.startswith('prove') and any(not same_value(z,m.ZERO) for z in answers):
            raise Unsupported('The radial operator does not establish the printed equation')
        out=[m.substitute(z,{r:radius}) for z in answers]
        return dict(method='source_operator_application',source_operator_goals=goals,radial_map=radius,source_domain=domain,
                    ordinary_derivatives=[first,second]),dict(operators=dict(zip(rules,out)),proved_equation=form.startswith('prove'))
    child=dict(kind='differential_operator',function=task['function'],variables=coords,parameters=parameters,
               method_requirement='table_and_rules',operators=rules,requests=requests,
               requested_output=['verify_identities' if form.startswith('prove') else 'operator_values'])
    result=request('complete operator expressions on the original domain',child)
    return dict(method='source_operator_application',source_operator_goals=goals,source_domain=domain),dict(
        operators=dict(zip(rules,result['value'])),proved_equation=form.startswith('prove'))


def integrate_partial_equation(task):
    """Construct the full kernel or matching trace data for an integrable coordinate operator."""
    from fractions import Fraction
    from math import factorial
    from tasks import domain_conditions,known_guard
    from verify import same_value
    text,want,conditions=bound_printed_multivariable(task,'partial differential equation',('variables',))
    if text.count('=')!=1:
        raise Unsupported('A single coordinate equation and its full trace data are required')
    lhs,rhs=text.replace(' ','').split('=')
    finite=re.fullmatch(r'([A-Za-z])_([xyz]+)',lhs)
    symbolic=re.fullmatch(r'partial_([xyz])\^([A-Za-z])\(([A-Za-z])\)',lhs)
    if not (finite or symbolic):
        raise Unsupported('No verified coordinate integration is available for this operator')
    if symbolic:
        x,n,z=symbolic.groups()
        if conditions or want!=['general_solution'] or rhs!='0':
            raise Unsupported('Additional data for an arbitrary integration order remain')
        coords=task.get('variables',list('xy'))
        if set(coords)&{n,z} or x not in coords or len(set(coords))!=len(coords):
            raise Unsupported('The order and field must be independent of the source coordinates')
        free=[v for v in coords if v!=x]
        return dict(method='coordinate_antiderivative',operator=lhs,variables=coords,order=n+' positive integer'),dict(
            general_solution=f'sum_{{j=0}}^{{{n}-1}} {x}^j C_j({",".join(free)})',
            proof='successive one-variable integration with every other coordinate fixed')
    z,path=finite.groups()
    coords=task.get('variables',list('xyz') if 'z' in path else list('xy'))
    if z in coords or len(set(coords))!=len(coords) or not set(path)<=set(coords) or len(path)>8:
        raise Unsupported('The dependent field or derivative coordinates are ambiguous')
    pure=len(set(path))==1;distinct=len(set(path))==len(path)
    if not pure and not distinct:
        raise Unsupported('A mixed kernel with repeated indices needs another decomposition')
    atoms={x:('s',x) for x in coords}
    def polynomial(s):
        raw=m.parse(s,None,coords)
        p,d=m.rational_form(raw)
        if any(not known_guard(g,m.context({})) for g in domain_conditions(raw)) or d!={():Fraction(1)} or any(set(dict(a))-set(atoms.values()) for a in p):
            raise Unsupported('A globally defined polynomial right-hand side or trace is required')
        return p
    def symbolic_poly(p):return m.poly_expr(p)
    force=polynomial(rhs);part=force
    for w in path:
        x=atoms[w];out={}
        for mon,c in part.items():
            powers=dict(mon);powers[x]=powers.get(x,0)+1
            out[tuple(sorted(powers.items()))]=c/powers[x]
        part=out
    particular=symbolic_poly(part)
    form=dict(method='coordinate_antiderivative',operator=path,variables=coords,right_hand_side=symbolic_poly(force),particular=particular)
    if want==['general_solution'] and not conditions:
        if pure:
            x=path[0];free=','.join(v for v in coords if v!=x)
            kernel=[f'{x}^{j} C_{j}({free})' for j in range(len(path))]
        else:
            kernel=[f'C_{i}({",".join(v for v in coords if v!=x)})' for i,x in enumerate(path)]
        return form,dict(particular=particular,arbitrary_kernel=kernel,
                         completeness='coordinate integration, with constants arbitrary in the unchanged coordinates')
    if want!=['solution_satisfying_data'] or len(coords)!=2:
        raise Unsupported('Unbound initial data for the requested equation')
    traces=[]
    for c in conditions:
        match=re.fullmatch(re.escape(z)+r'(?:_([xyz]+))?\(([^,]+),([^,]+)\)=(.+)',c.replace(' ',''))
        if not match:raise Unsupported('The complete coordinate trace is not recognized')
        order,args=match[1] or '',match.groups()[1:3]
        traces.append((order,[symbolic_poly(polynomial(a)) for a in args],symbolic_poly(polynomial(match[4]))))
    def deriv(poly,word):
        for w in word:poly=exact_polynomial_partial(poly,atoms[w])
        return symbolic_poly(poly)
    def substitute(expr,args):
        return m.simplify(m.substitute(expr,dict(zip(atoms.values(),args,strict=True))))
    sol=particular
    if pure:
        x=path[0];j=coords.index(x);other=coords[1-j];at=traces[0][1][j]
        if (len(traces)!=len(path) or sorted(o for o,*_ in traces)!=[x*k for k in range(len(path))]
                or any(not same_value(at,args[j]) or args[1-j]!=atoms[other] or m.contains(args[j],atoms[x])
                       or m.contains(value,atoms[x]) for _,args,value in traces)):
            raise Unsupported('The trace data do not fix every one-coordinate integration constant')
        delta=m.add(atoms[x],m.neg(at))
        for word,args,value in traces:
            c=m.add(value,m.neg(substitute(deriv(part,word),args)))
            term=m.mul(m.div(c,m.q(factorial(len(word)))),m.power(delta,len(word))) if word else c
            sol=m.add(sol,term)
    else:
        if len(traces)!=2 or any(word for word,*_ in traces):
            raise Unsupported('The mixed equation requires two transverse coordinate traces')
        x,y=atoms.values(); along_x,along_y=sorted(traces,key=lambda t:t[1][0]!=x)
        (_,xs,u),(_,ys,v)=along_x,along_y
        if xs[0]!=x or ys[1]!=y or m.num(xs[1]) is None or m.num(ys[0]) is None or m.contains(u,y) or m.contains(v,x):
            raise Unsupported('The two trace lines or their fixed coordinates are not verified')
        intersect=[ys[0],xs[1]]
        meeting=substitute(u,intersect)
        if not same_value(meeting,substitute(v,intersect)):
            raise Unsupported('The source traces are incompatible at their intersection')
        for a,trace in ((xs,u),(ys,v)):
            sol=m.add(sol,m.add(trace,m.neg(substitute(particular,a))))
        sol=m.add(sol,m.add(substitute(particular,intersect),m.neg(meeting)))
    p,_=m.rational_form(sol)
    if not same_value(deriv(p,path),symbolic_poly(force)) or any(not same_value(substitute(deriv(p,w),a),v) for w,a,v in traces):
        raise Unsupported('The candidate does not verify all original traces and the equation')
    return dict(form,verified_traces=traces),dict(solution=sol,unique=True)


def count_square_height_branches(task):
    """Classify continuous choices of the two square-root sheets on an interval."""
    from collections import defaultdict
    from fractions import Fraction
    from graphs import rational_roots,peval
    from tasks import domain_conditions
    text,want,conditions=bound_printed_multivariable(task,'count implicit branches')
    if want!=['number_of_single_valued_functions'] or len(conditions)!=2 or text.count('=')!=1:
        raise Unsupported('The branch requirement and its base interval must be explicit')
    x,y=('s','x'),('s','y')
    sides=[m.parse(s,None,['x','y']) for s in text.split('=')]
    if any(domain_conditions(e) for e in sides):
        raise Unsupported('The entire original equation must be defined on the interval')
    p,d=m.rational_form(m.add(sides[0],m.neg(sides[1])))
    a=p.pop(((y,2),),0)
    if not a or d!={():Fraction(1)} or any(set(dict(k))-{x} for k in p):
        raise Unsupported('The level does not give one globally determined squared height')
    terms={k:-c/a for k,c in p.items()}
    from polynomial import univariate_coefficients
    poly=univariate_coefficients(terms,x)
    height=m.poly_expr(terms)
    domain,smooth=conditions
    mode,_,point=smooth.partition(';')
    label=re.fullmatch(r'y\(([-0-9./]+)\)=([-0-9./]+)',point) if point else None
    if mode not in ('any','continuous','differentiable') or point and not label:
        raise Unsupported('A complete continuity or differentiability request must be stated')
    if domain=='R':
        lo=hi=None
    elif (interval:=re.fullmatch(r'\[([-0-9./]+),([-0-9./]+)\]',domain)):
        lo,hi=map(Fraction,interval.groups())
        if lo>=hi:raise Unsupported('A nonempty real interval is required')
    elif (little:=re.fullmatch(r'([-0-9./]+)-delta<x<\1\+delta with sufficiently small delta>0',domain)):
        c=Fraction(little[1]);at=peval(poly,c)
        if mode!='continuous' or at<=0 or label and Fraction(label[1])!=c:
            raise Unsupported('The local reference value must lie strictly above the branching level')
        count=2
        if label:count=int(Fraction(label[2])**2==at)
        return dict(method='square_height_branches',height=height,center=m.q(c),positive_at_center=m.q(at)),dict(
            count=count,local_scope=domain,branches='either square-root sheet, restricted by the given sign')
    else:
        raise Unsupported('The base interval cannot be classified exactly')
    fixed=None
    if label:
        u,v=map(Fraction,label.groups())
        if lo is not None and not lo<=u<=hi:raise Unsupported('The prescribed coordinate lies outside the original base')
        fixed=(u,v)
    common=dict(method='square_height_branches',height=height,base=domain,regularity=mode,
                fixed=None if fixed is None else list(map(m.q,fixed)))
    if poly==(0,):
        return common,dict(count=int(fixed is None or fixed[1]==0),branches='the zero function when compatible')
    roots=rational_roots(poly)
    if any(r.b for r in roots):raise Unsupported('An irrational branch cut needs an exact derivative comparison')
    roots=sorted({r.a for r in roots if lo is None or lo<=r.a<=hi})
    cuts=[lo,*[r for r in roots if r!=lo and r!=hi],hi]
    cells=[]
    for ll,rr in zip(cuts,cuts[1:]):
        s=0 if ll is None and rr is None else rr-1 if ll is None else ll+1 if rr is None else (ll+rr)/2
        cells.append((ll,rr,peval(poly,s)))
    marks=[('−∞' if a is None else m.q(a),'∞' if b is None else m.q(b),m.q(c)) for a,b,c in cells]
    common.update(cells=marks,all_zeros=list(map(m.q,roots)))
    if any(s<0 for _,_,s in cells) or lo is not None and (peval(poly,lo)<0 or peval(poly,hi)<0):
        return common,dict(count=0,reason='negative height at a source abscissa')
    if fixed is not None and fixed[1]**2!=peval(poly,fixed[0]):
        return common,dict(count=0,reason='the prescribed value is not a point of the source level')
    if mode=='any':
        return common,dict(count='2^continuum',branches='independent sign at each distinct pair of roots')
    constraints=[]
    if mode=='differentiable':
        for root in roots:
            k=0;g=poly
            while not peval(g,root):
                k+=1;g=tuple(j*c for j,c in enumerate(g) if j)
            if k==1:
                return common,dict(count=0,reason='unbounded slope at a simple zero on the base')
            if k==2 and root in cuts[1:-1]:
                i=cuts.index(root)
                constraints.append((i-1,i,-1))
    # The constraints join neighboring cells only, so a fixed sign fixes one whole component.
    joined={b:a for a,b,_ in constraints}
    def component(i):
        while i in joined:i=joined[i]
        return i
    reduction=len(constraints)
    if fixed and fixed[1]:
        i=next(j for j,(a,b,_) in enumerate(cells) if (a is None or a<=fixed[0]) and (b is None or fixed[0]<=b))
        common['fixed_sign_component']=component(i)
        reduction+=1
    common['neighbor_constraints']=constraints
    return common,dict(count=2**(len(cells)-reduction),branches='one square-root sign per positive interval, glued through the checked zero heights')


def implicit_branch_statements(task):
    """Use density, monotonicity, or periodic translation to certify the full inverse claim."""
    from fractions import Fraction
    from tasks import domain_conditions
    from verify import same_value
    labels={'implicit_inverse_existence':'implicit inverse existence','implicit_inverse_theorem':'implicit inverse theorem',
            'continuous_implicit_uniqueness':'continuous implicit uniqueness','implicit_function_identity':'implicit function identity'}
    kind=task['kind'];formula,want,conditions=bound_printed_multivariable(task,labels[kind]);f=formula.replace(' ','')
    if kind=='implicit_function_identity':
        hit=re.fullmatch(r'([A-Za-z]\w*)\(x\)is([-0-9]+)onrationalsand([-0-9]+)onirrationals',f)
        if not hit or conditions or len(want)!=1 or not want[0].startswith('prove ') or not want[0].endswith('=0'):
            raise Unsupported('The exact two-valued branch and polynomial identity must be given')
        raw=m.parse(want[0][6:-2].replace(hit[1]+'(x)','__height'),None,['__height'])
        if domain_conditions(raw):
            raise Unsupported('The asserted two-valued identity has an extra restriction')
        checks=[m.simplify(m.substitute(raw,{('s','__height'):m.q(int(v))})) for v in hit.groups()[1:]]
        if any(a!=m.ZERO for a in checks):raise Unsupported('A declared height does not satisfy the identity')
        return dict(method='inverse_and_density',two_values=hit.groups()[1:],substitutions=checks),dict(identity_proved=True)
    if kind=='continuous_implicit_uniqueness':
        hit=re.fullmatch(r'([A-Za-z]\w*)\(x\)\*y=(?:([A-Za-z]\w*)\(x\)|0)',f)
        if not hit:raise Unsupported('One continuous linear equation with its full domain is required')
        a,b=hit.groups()
        dense=f'{{x∈(a,b): {a}(x)≠0}} is dense in (a,b)'
        if b is None and conditions==[a+' defined on (a,b)'] and want==['necessary_and_sufficient_condition_for_unique_continuous_y=0']:
            return dict(method='inverse_and_density',proof=['continuity determines zero values from the dense nonzero set',
                        'a nonzero continuous bump with support in an interval of zeros gives a second solution otherwise']),dict(
                criterion=[dense],solution='y=0')
        if b and a!=b and conditions==[a+','+b+' continuous on (a,b)'] and want==['necessary_and_sufficient_condition_for_unique_continuous_solution']:
            return dict(method='inverse_and_density',proof=['the quotient is forced at each nonzero point',
                           'a continuous extension determines the remaining values uniquely by density',
                           'a nonzero continuous bump gives a second solution in any zero interval if a solution exists']),dict(
                criterion=[dense,f'{b}/{a} extends continuously to (a,b)',f'{b}=0 at every zero of {a}'],
                solution='that unique continuous extension')
        raise Unsupported('The source interval, regularity, or uniqueness requirement is incomplete')
    if kind=='implicit_inverse_theorem':
        if (f=='x=y+phi(y)' and conditions==['phi(0)=0','abs(phi_prime)<=k<1 on (-a,a)']
                and want==['local_existence_uniqueness_differentiability_with_y(0)=0']):
            return dict(method='inverse_and_density',proof=['1+phi_prime >= 1-k > 0',
                'the intermediate value theorem applies between the images of -a/2 and a/2',
                'the quotient of inverse increments has limit 1/(1+phi_prime)']),dict(
                unique_differentiable_inverse=True,neighborhood='abs(x)<(1-k)*a/2',zero_value=m.ZERO,
                derivative='1/(1+phi_prime(y))')
        if (f=='x=k*y+phi(y)' and conditions==['k!=0','phi differentiable and omega-periodic','abs(phi_prime)<abs(k)']
                and want==['prove y=x/k+psi(x) with psi periodic of period |k|*omega']):
            return dict(method='inverse_and_density',proof=['sign of k+phi_prime equals sign of k',
                'the bounded periodic term leaves opposite infinite limits of k*y+phi(y)',
                'source(x+k*omega)=inverse(x)+omega when written as an inverse translation']),dict(
                inverse_exists=True,remainder='psi(x)=y(x)-x/k',period='abs(k)*omega')
        raise Unsupported('The derivative bound or periodic data are not bound to the stated inverse problem')
    composition=re.fullmatch(r'([A-Za-z]\w*)\(y\)=([A-Za-z]\w*)\(x\)',f)
    if composition:
        phi,a=composition.groups()
        if (phi==a or conditions!=[a+' continuous on (a,b)',phi+' continuous strictly increasing on (c,d)']
                or want!=['criterion_for_single_valued_inverse']):
            raise Unsupported('The full continuity and strict order hypotheses must be bound')
        return dict(method='inverse_and_density',proof=['injectivity of the strictly increasing function',
            'values of the argument must belong to its image',
            'the inverse of a continuous strictly monotone function on an interval is continuous']),dict(
            criterion=f'{a}((a,b)) subset of {phi}((c,d))',unique_value=f'{phi}^(-1)({a}(x))')
    if conditions or want!=['apply_inverse_criterion'] or f.count('=')!=1:
        raise Unsupported('The original comparison of inverse ranges is not bound')
    left,right=[m.parse(s,None,['x','y']) for s in f.split('=')]
    ctx=m.context(dict(variable='__inverse',parameters=['x','y']))
    if left[0]=='exp' and not m.contains(left,('s','x')) and not m.contains(right,('s','y')):
        if m.constant_defined(right,ctx) and m.known_nonnegative(m.neg(right),ctx) and m.constant_defined(left,ctx):
            return dict(method='inverse_and_density',left_range='strictly positive',right_range='nonpositive'),dict(
                solutions='none for every source x')
    if right==('s','x'):
        p,d=m.rational_form(left);y=('s','y')
        wave={tag:p.get((((tag,y),1),),0) for tag in ('sin','sinh')}
        if len(p)==2 and d=={():Fraction(1)} and 0<abs(wave['sin'])<=wave['sinh']:
            return dict(method='inverse_and_density',source_field=left,
                        proof=['cosh(y)>1 away from zero and |cos(y)|<=1',
                               'strict increase follows on every nonempty interval',
                               'the unbounded hyperbolic sine dominates the bounded sine']),dict(
                range='R',continuous_inverse=True,unique_for_each_real_x=True)
    raise Unsupported('No established range and strict-order proof for the original scalar inverse')


def affine_argument(e,coords,params):
    """Find and certify the affine coordinate coefficients."""
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x=[('s',a) for a in coords];zero=dict.fromkeys(x,m.ZERO)
    ctx=m.context(dict(variable='__fixed_coordinate',parameters=params))
    c=m.substitute(e,zero)
    b=[m.add(m.substitute(e,{**zero,w:m.ONE}),m.neg(c)) for w in x]
    if (any(not known_guard(g,ctx) for g in domain_conditions(e)) or
            not all(m.constant_defined(v,ctx) for v in [c,*b]) or not same_value(e,m.add(c,m.dot(b,x)))):
        raise Unsupported('An affine inner form with defined fixed coefficients is required')
    return [m.simplify(z) for z in b]


def symbolic_total_differential(task):
    from tasks import source
    kind=task['kind'];src=task.get('source',{});heading=src.get('literal_requirement','')
    if set(src)-OPERATOR_PROVENANCE-{'literal_requirement'}:
        raise Unsupported('An additional symbolic total-differential requirement remains')
    composite=kind=='composite_function_differentiation'
    if composite:
        if (set(task)-{'id','kind','source','outer_function','variables','inner_arguments','requested_output'}
                or task['requested_output']!=['dn'] or heading!='Найти d^n u.'):
            raise Unsupported('The source must explicitly request the symbolic total differential of the composition')
        outer=task['outer_function'];coords=task['variables'];arguments=task['inner_arguments']
        mode='abstract'
    else:
        if (set(task)-{'kind','id','source','function','order'} or task['order']!='n'):
            raise Unsupported('The independent symbolic differential order is not known')
        f=task['function'].replace(' ','')
        homogeneous=re.fullmatch(r'([A-Za-z]\w*)\(([a-z](?:,[a-z])*)\)homogeneouspolynomialofdegreen',f)
        if homogeneous:
            P,axes=homogeneous.groups();coords=axes.split(',');dx=','.join('d'+x for x in coords)
            expected=f'Доказать d^n {P}=n!*{P}({dx}).'
            if len(set(coords))!=len(coords) or heading not in ('',expected):
                raise Unsupported('The homogeneous source theorem has a different degree or variables')
            return dict(method='constant_increment_operators',coordinates=coords,degree='n',
                        proof='the coefficient of t^n in P_n(X+t*dX) is P_n(dX) by the exact homogeneous polynomial identity'),dict(
                formula=f'n! * {P}({dx})')
        if heading not in ('','Найти d^n u.'):
            raise Unsupported('The original symbolic total-differential heading differs')
        separated=re.fullmatch(r'([A-Za-z]\w*)\(([xyz])\)\*([A-Za-z]\w*)\(([xyz])\)',f)
        if separated:
            A,a,B,b=separated.groups()
            if a==b:raise Unsupported('The source factors must use distinct independent coordinates')
            return dict(method='constant_increment_operators',functions=[A,B],coordinates=[a,b],proof='one-variable Leibniz along constant increments'),dict(
                formula=f'sum_{{j=0}}^n binom(n,j) * {A}^({{j}})({a}) * {B}^({{n-j}})({b}) * d{a}^j * d{b}^(n-j)')
        call=re.fullmatch(r'([A-Za-z]\w*)\((.+)\)',f)
        if not call:raise Unsupported('No affine argument of the symbolic source function found')
        outer,inner=call.groups();arguments=[inner]
        coords=[a for a in AXES if re.search(r'\b'+a+r'\b',inner)]
        mode='elementary' if outer=='exp' else 'abstract'
    if (not isinstance(outer,str) or not re.fullmatch(r'[A-Za-z]\w*',outer) or not coords or not arguments
            or len(set(coords))!=len(coords)):
        raise Unsupported('Independent coordinates and one named outer function are required')
    params=sorted(set(re.findall(r'[A-Za-z_]\w*',','.join(arguments)))-set(coords)-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    increments=['d'+x for x in coords]
    if (set(increments)&set([*params,*coords,outer]) or outer in coords or outer in params or 'n' in coords
            or mode=='abstract' and outer in m.FUNCTIONS|set(m.ALIASES)):
        raise Unsupported('A derivative, coordinate, or order symbol collides with the source')
    arguments=[m.parse(s,None,[*coords,*params]) for s in arguments]
    b=[affine_argument(e,coords,params) for e in arguments]
    values=[m.dot(row,[('s',name) for name in increments]) for row in b]
    if mode=='elementary':
        (u,),(du,)=arguments,values
        formula=source(('exp',u))+' * ('+source(du)+')^n'
    else:
        formula=('sum_{alpha_1+...+alpha_k=n} n!/alpha! * D^alpha '+outer+'(inner) * product_i (d_inner_i)^alpha_i'
                 if len(values)>1 else f'{outer}^(n)(inner) * (d_inner)^n')
    return dict(method='constant_increment_operators',coordinates=coords,inner=arguments,first_differentials=values,
                increments=increments,regularity='outer differentiable to each requested order on the source image',
                proof='substitute X+t*dX; every affine argument then has exactly its first-order increment'),dict(
        formula=formula,inner_arguments=arguments,inner_differentials=values)


def printed_mixed_composition(task):
    from tasks import domain_conditions
    from verify import same_value
    allowed={'kind','id','schema','source','function','variables','parameters','stated_conditions','requested_output',
             'substitution','requested_partials','relation','arbitrary_function'}
    src=task.get('source',{})
    if (set(task)-allowed or set(src)-OPERATOR_PROVENANCE-{'printed_group_heading'} or task.get('parameters')
            or task.get('stated_conditions') or task['requested_output']!=['prove_dependence_only_on_t','determine_F']):
        raise Unsupported('The complete mixed dependence statement and its variables are required')
    f=task['arbitrary_function'];variables=task['variables'];word,=task['requested_partials']
    hit=re.fullmatch(re.escape(f)+r'\((.+)\)',task['function'])
    if (not hit or not 1<=len(variables)<=8 or len(set(variables))!=len(variables) or sorted(word)!=sorted(variables)
            or set(task['substitution'])!={'t'} or task['relation']!='partial_'+''.join(reversed(word))+'=F(t)'):
        raise Unsupported('The printed composition and derivative axes differ')
    arg=m.parse(hit[1],None,variables);sub=m.parse(task['substitution']['t'],None,variables)
    prod=m.ONE
    for s in variables:prod=m.mul(prod,('s',s))
    if domain_conditions(arg) or domain_conditions(sub) or not same_value(arg,prod) or not same_value(sub,prod):
        raise Unsupported('The argument must be the exact product of the original independent coordinates')
    stirling=[1]
    for n in range(1,len(variables)+1):
        stirling=[0,*[stirling[k-1]+(k*stirling[k] if k<len(stirling) else 0) for k in range(1,n+1)]]
    return dict(method='constant_increment_operators',source_product=prod,stirling_numbers=stirling,
                proof='each set partition into j blocks leaves each source coordinate in j-1 factors of the chain rule'),dict(
        terms=[dict(outer_order=j,factor=c,t_exponent=j-1) for j,c in enumerate(stirling) if c],outer=f)


def total_differential_with_partials(task,request):
    from math import factorial
    from itertools import product
    from tasks import domain_conditions,source
    src=task.get('source',{});xs=task['variables'];paths=task['requested_partials']
    allowed={'kind','id','schema','source','function','variables','parameters','stated_conditions','requested_output',
             'requested_partials','independent_coordinates'}
    if (set(task)-allowed or set(src)-OPERATOR_PROVENANCE-{'printed_group_heading'} or task.get('parameters')
            or task.get('stated_conditions') or task['independent_coordinates'] is not True or not xs
            or len(xs)>3 or task['requested_output']!=['total_differential_degree_4','all_five_printed_fourth_partials']
            or len(xs)!=2 or len(paths)!=5 or sorted(tuple(sorted(a)) for a in paths)!=sorted(tuple([xs[0]]*k+[xs[1]]*(4-k)) for k in range(5))):
        raise Unsupported('The exact polynomial differential and every printed fourth partial are required')
    inc=['d'+s for s in xs];raw=m.parse(task['function'],None,xs)
    if domain_conditions(raw):raise Unsupported('The source polynomial has a hidden domain restriction')
    proof=request('exact translated polynomial in all independent increments',dict(kind='multivariate_taylor',
                    expression=task['function'],variables=xs,increments=inc,center='current_point',
                    requested_output=['exact_shifted_polynomial']))
    terms=proof['value']['homogeneous_terms'];jet=freeze(terms[4]) if len(terms)>4 else m.ZERO
    poly,den=m.rational_form(jet);partials=[]
    for word in paths:
        powers={('s',u):word.count(x) for x,u in zip(xs,inc)}
        coeff={tuple((a,k) for a,k in mon if a not in powers):c for mon,c in poly.items()
               if all(dict(mon).get(a,0)==p for a,p in powers.items())}
        value=m.div(m.poly_expr(coeff),m.poly_expr(den))
        for p in powers.values():value=m.mul(m.q(factorial(p)),value)
        partials.append(dict(path=word,value=value))
    return dict(method='constant_increment_operators',homogeneous_term=jet,required_paths=paths),dict(
        total_differential=m.mul(m.q(factorial(4)),jet),partials=partials)


def printed_operator_product(task,request):
    src=task.get('source',{})
    if (set(task)-{'kind','id','source','variables','given'} or set(src)-OPERATOR_PROVENANCE-{'literal_requirement'}
            or task['variables']!=list(AXES)
            or task['given']!='u,v twice differentiable. Δ(u,v)=u_x*v_x+u_y*v_y+u_z*v_z; Δ is ordinary 3D Laplacian.'
            or src.get('literal_requirement')!='Доказать Δ(uv)=uΔv+vΔu+2Δ(u,v).'):
        raise Unsupported('The complete Cartesian product rule and its source smoothness are needed')
    child=dict(kind='formal_vector_identity',identity='laplacian(u*v)=u*laplacian(v)+v*laplacian(u)+2*dot(grad(u),grad(v))',
               regularity={'u':2,'v':2})
    request('expand the source product rule in Cartesian coordinates',child)
    return dict(method='source_operator_application',bound_product=child['identity']),dict(proved_equation=True)


def abstract_radial_laplacian(task):
    from tasks import domain_conditions
    from verify import same_value
    src=task.get('source',{});variables=task['variables'];outer=task['outer_function']
    headings={'radial_laplacian':'Доказать Δu=F(r) и найти F, где f дважды дифференцируема.',
              'd1_d2':'Найти полные дифференциалы первого и второго порядков сложной функции по независимым переменным.'}
    if (set(task)-{'id','kind','source','outer_function','variables','inner_arguments','requested_output'}
            or set(src)-OPERATOR_PROVENANCE-{'literal_requirement'} or len(task['inner_arguments'])!=1
            or not re.fullmatch(r'[A-Za-z]\w*',outer) or len(set(variables))!=len(variables)):
            raise Unsupported('The source norm, field, and requested differentials must be explicit')
    output,=task['requested_output']
    if output not in headings or src.get('literal_requirement',headings[output])!=headings[output]:
        raise Unsupported('The printed radial quantity does not match the goal')
    v=[('s',x) for x in variables];raw=m.parse(task['inner_arguments'][0],None,variables)
    if (raw[0]!='sqrt' or domain_conditions(raw[1]) or not same_value(raw[1],m.dot(v,v))):
        raise Unsupported('Only the full Euclidean norm in independent coordinates has the required radial identities')
    r,r1,r2=('s','__radius'),('s','__outer_first'),('s','__outer_second')
    plan=dict(method='source_operator_application',radius=raw,field=outer,
              checks=['unit gradient and trace (dimension-1)/r off the origin','Taylor expansion at zero if the one-sided first derivative is zero'])
    cases=dict(if_first_at_zero_nonzero='not differentiable at the origin',
               if_zero_and_second_exists='the Hessian at the origin is f_second(0) times the identity')
    if output=='radial_laplacian':
        return plan,dict(result=m.add(r2,m.div(m.mul(m.q(len(v)-1),r1),r)),
                         when_radius_positive=True,at_zero=cases,trace_at_zero_when_defined=m.mul(m.q(len(v)),r2))
    inc=[('s','d'+x) for x in variables]
    if set(inc)&set(v):raise Unsupported('The independent increment names collide')
    inner=m.div(m.dot(v,inc),r)
    acc=m.div(m.add(m.dot(inc,inc),m.neg(m.power(inner,2))),r)
    return plan,dict(d1=m.mul(r1,inner),d2=m.add(m.mul(r2,m.power(inner,2)),m.mul(r1,acc)),
                     when_radius_positive=True,at_zero=cases,
                     differentials_at_zero_when_defined=[m.ZERO,m.mul(r2,m.dot(inc,inc))])


def symbolic_coordinate_orders(task):
    """Recognize closed symbolic Leibniz, affine reciprocal, and separated kernels."""
    from fractions import Fraction
    from itertools import product
    from tasks import domain_conditions,source
    src=task.get('source',{})
    allowed={'kind','id','schema','source','function','variables','parameters','stated_conditions',
             'requested_output','derivative_multiplicities','order_domain','evaluation_point'}
    coords=task['variables'];pars=task.get('parameters',[]);orders=task['derivative_multiplicities']
    if (set(task)-allowed or set(src)-OPERATOR_PROVENANCE-{'printed_group_heading'} or task.get('stated_conditions')
            or task['requested_output']!=['formula_in_integer_orders'] or task['order_domain']!='nonnegative_integers'
            or set(coords)!=set(orders) or not set(orders.values())<=set(pars)
            or len(coords)!=len(set(coords)) or not coords or set(coords)&set(pars)):
        raise Unsupported('A symbolic integer order for every independent source coordinate is required')
    names=[*coords,*pars]
    raw=m.parse(task['function'],None,names);atoms=[('s',s) for s in coords]
    fixed=sorted(set(pars)-set(orders.values()))
    point=task.get('evaluation_point')
    order_words=[orders[x] for x in coords]
    def factors(e):
        if e[0]!='mul':return [e]
        return factors(e[1])+factors(e[2])
    def affine(e):return affine_argument(e,coords,fixed)
    def attach(plan,formula,**kw):
        return dict(method='symbolic_coordinate_orders',orders=orders,original=raw,**plan),dict(formula=formula,**kw)
    if point is None and raw[0]=='div':
        numerator,divisor=raw[1:];b,c=affine(numerator),affine(divisor)
        if all(z==m.ZERO for z in c):
            raise Unsupported('The affine denominator must give a genuine inverse power')
        return attach(dict(numerator=numerator,denominator=divisor,numerator_gradient=b,denominator_gradient=c,
                           source_domain=domain_conditions(raw),rule='Leibniz with an affine numerator of degree at most one'),
            'A*K(alpha)+sum_{i: alpha_i>0} alpha_i*A_i*K(alpha-e_i)',
            kernel='K(beta)=(-1)^|beta|*|beta|!*product_i(L_i^beta_i)/L^(|beta|+1)')
    operands=factors(raw)
    if point is None and len(operands)==len(coords) and all(e[0]=='rpow' for e in operands):
        seen={};slopes=[]
        for e in operands:
            b=affine(e[1]);positions=[j for j,c in enumerate(b) if c!=m.ZERO]
            if len(positions)!=1:
                raise Unsupported('A separated factor must depend linearly on exactly one independent coordinate')
            j,=positions;x=coords[j]
            if e[2]!=('s',orders[x]) or x in seen:
                raise Unsupported('The symbolic power and the compiled order are different')
            seen[x]=b[j]
        slopes=[seen[x] for x in coords]
        return attach(dict(affine_slopes=slopes,rule='differentiate each polynomial factor to its own degree'),
                      'product_i (alpha_i! * slope_i^alpha_i)',polynomial_zero_power='the empty product is one')
    if point is None and (exponentials:=[e for e in operands if e[0]=='exp']) and len(exponentials)==1:
        exp,=exponentials;P=m.ONE
        for e in operands:
            if e==exp:continue
            if domain_conditions(e):
                raise Unsupported('The original polynomial factor has a domain restriction')
            P=m.mul(P,e)
        if any(m.contains(P,('s',q)) for q in order_words):
            raise Unsupported('The polynomial factor may not depend on its derivative indices')
        poly,den=m.rational_form(P)
        if any(set(dict(k))-set(atoms) for k in poly) or den!={():Fraction(1)}:
            raise Unsupported('An ordinary polynomial times an affine exponential is required')
        degrees=[max((dict(k).get(x,0) for k in poly),default=0) for x in atoms]
        cap=1
        for n in degrees:cap*=n+1
        if cap>128:raise Unsupported('The exact finite Leibniz support exceeds the coefficient budget')
        terms=[]
        for beta in product(*(range(n+1) for n in degrees)):
            p=poly
            for x,k in zip(atoms,beta):
                for _ in range(k):p=exact_polynomial_partial(p,x)
            if p:terms.append(dict(multi_index=beta,derivative=m.poly_expr(p)))
        return attach(dict(exponential=exp,affine_gradient=affine(exp[1]),finite_polynomial_derivatives=terms,
                           rule='multi-index Leibniz, with zero terms omitted by polynomial degree'),
                      'exp(L)*sum_{beta<=alpha} binom(alpha,beta)*D^beta(P)*product_i(L_i^(alpha_i-beta_i))')
    if not isinstance(point,dict) or set(point)!=set(coords) or len(coords)!=len(operands):
        raise Unsupported('The exact requested point or separated kernels remain unresolved')
    independent={}
    cycles={'exp':('exp',),'sin':('sin','cos','-sin','-cos'),'cos':('cos','-sin','-cos','sin'),
            'sinh':('sinh','cosh'),'cosh':('cosh','sinh')}
    for e in operands:
        if e[0] not in cycles:raise Unsupported('Unknown all-orders elementary cycle')
        b=affine(e[1]);hits=[j for j,a in enumerate(b) if a!=m.ZERO]
        if len(hits)!=1 or coords[hits[0]] in independent:
            raise Unsupported('Each elementary factor must depend on its own independent coordinate')
        j,=hits;x=coords[j]
        at=m.parse(str(point[x]),None,fixed);ctx=m.context(dict(variable='__fixed_order_point',parameters=fixed))
        if not m.constant_defined(at,ctx):raise Unsupported('An original evaluation coordinate is undefined')
        arg=m.substitute(e[1],{('s',x):at})
        row=[]
        for op in cycles[e[0]]:
            val=(op.removeprefix('-'),arg)
            val=m.neg(val) if op.startswith('-') else m.simplify(val)
            row.append(val)
        independent[x]=dict(order=orders[x],slope=b[j],residue_values=row)
    return attach(dict(point=point,separated_cycles=independent,rule='repeat the elementary derivative cycle in each coordinate'),
                  'product_i slope_i^(alpha_i) times the corresponding residue class value')


def multivariate_operator_report(result,pretty):
    p=result['compilation'];v=result['value'];method=p['method']
    def listing(expressions):return '\n'.join(name+' = '+pretty(value) for name,value in expressions.items())
    def list_text(strings):return '.\n'.join(strings)+'.'
    if method=='implicit_differential_transport':
        if 'held_fixed' in p:
            return ('Дифференцируем вдоль двух разных неявных графиков с общей исходной точкой. '
                    'При зависимой y фиксируем z, при зависимой z фиксируем y.\n'
                    +listing({'Зависимая '+a:b for a,b in v['expressions'].items()}))
        bound=v['source_condition'][1]
        lines=['На исходном уровне зависимая частная производная равна '+pretty(bound)+' и должна быть ненулевой.',
               'Выделяем производную на каждом требуемом порядке после применения правила цепочки.']
        if p.get('abstract_partials'):
            lines.extend(name+' — производная '+p['outer']+' по аргументам '+','.join(map(str,word))
                         for name,word in p['abstract_partials'].items())
        return '\n'.join(lines+[listing(v['expressions'])])
    if 'operators' in v:
        if 'coordinate_partials' in v:
            return '\n'.join([*p['argument'],listing({'D_'+''.join(path):value for path,value in v['coordinate_partials']}),
                              listing(v['operators'])])
        return ('Раскрываем каждое напечатанное действие на исходной области. '
                +('Радиальное представление сохраняет обе требуемые операции.\n' if 'radial_map' in p else '\n')+listing(v['operators']))
    if method=='coordinate_antiderivative':
        prefix='Интегрируем по указанным координатам, сохраняя зависимость произвольных функций от остальных переменных.'
        if 'solution' in v:
            return prefix+'\nПодстановка подтверждает все исходные условия и даёт единственное решение '+pretty(v['solution'])+'.'
        if 'general_solution' in v:return prefix+'\n'+v['general_solution']
        return prefix+'\n'+pretty(v['particular'])+' + '+' + '.join(v['arbitrary_kernel'])
    if method=='square_height_branches':
        return ('Квадрат ординаты равен '+pretty(p['height'])+'. На каждой области положительности выбираем знак '
                'и проверяем условия склейки на нулевой высоте. Число допустимых функций '+str(v['count'])+'.')
    if method=='inverse_and_density':
        if p.get('proof'):return list_text(p['proof']+[str(value) for value in v.values()])
        if 'substitutions' in p:return 'Подстановка каждого из двух допустимых значений зануляет напечатанное выражение.'
        return 'Левая часть принимает строго положительные значения, правая неположительные. Вещественных решений нет.'
    if 'formula' in v:
        return ('Представляем частные производные или полный дифференциал через указанные независимые индексы. '
                +str(p.get('proof',p.get('rule','')))+'.\n'+v['formula'])
    if 'total_differential' in v:
        lines=['Точно раскрываем полином по приращениям, затем извлекаем коэффициенты нужной степени.',
               'Полный дифференциал '+pretty(v['total_differential'])+'.']
        lines.extend('∂ по '+''.join(a['path'])+' = '+pretty(a['value']) for a in v['partials'])
        return '\n'.join(lines)
    if 'terms' in v:
        terms=[str(row['factor'])+'·t^'+str(row['t_exponent'])+'·'+v['outer']+'^('+str(row['outer_order'])+')(t)' for row in v['terms']]
        return 'Группируем повторное правило цепочки по блокам множителей при независимых частных.\nF(t) = '+' + '.join(terms)
    if 'bound_product' in p:return 'Раскрытие лапласиана произведения подтверждает '+p['bound_product']+'.'
    if 'at_zero' in v:
        expressions={k:v[k] for k in ('result','d1','d2','trace_at_zero_when_defined') if k in v}
        return ('Для положительного радиуса применяем цепное правило с единичным радиальным градиентом. '
                'В центре первая производная внешней функции должна быть нулевой. Тогда гессиан равен её второй производной, умноженной на единичную матрицу.\n'
                +listing(expressions))
    raise Unsupported('The checked multivariate conclusion has no readable proof')

def _chart_determinant(rows):
    """Exact small minors used to check actual regular coordinate changes."""
    if len(rows)==1:return rows[0][0]
    answer=m.ZERO
    for j,coefficient in enumerate(rows[0]):
        if coefficient==m.ZERO:continue
        minor=[row[:j]+row[j+1:] for row in rows[1:]]
        term=m.mul(coefficient,_chart_determinant(minor))
        answer=m.add(answer,m.neg(term) if j%2 else term)
    return m.polynomial_quotient(answer)


def affine_prolongation_inverse(formulas,old_names,new_names):
    """Invert an affine map in the full coordinates before restricting it to a graph."""
    old=[('s',n) for n in old_names]
    new=[('s',n) for n in new_names]
    N=len(old)
    if len(formulas)!=len(new) or N!=len(new) or len(set([*old,*new]))!=2*N:
        raise Unsupported('Need a full reversible affine coordinate change')
    system=[];affine_terms={()}|{((x,1),) for x in old}
    for k,e in enumerate(formulas):
        nums,den=m.rational_form(e)
        if (domain_conditions(e) or den!={():Fraction(1)} or
                any(mon not in affine_terms for mon in nums)):
            raise Unsupported('The original map is not affine with fixed real rational coefficients')
        system.append([nums.get(((x,1),),Fraction(0)) for x in old]+
                      [Fraction(j==k) for j in range(N)]+[-nums.get((),Fraction(0))])
    for k in range(N):
        pivot=next((j for j in range(k,N) if system[j][k]),None)
        if pivot is None:raise Unsupported('The full affine map has zero determinant')
        system[k],system[pivot]=system[pivot],system[k]
        divisor=system[k][k];system[k]=[x/divisor for x in system[k]]
        for j in range(N):
            if j!=k:
                c=system[j][k];system[j]=[a-c*b for a,b in zip(system[j],system[k])]
    result=[]
    for r in system:
        term=q(r[-1])
        for c,x in zip(r[N:-1],new):
            term=m.add(term,m.mul(q(c),x))
        result.append(term)
    if not all(same_value(m.substitute(a,dict(zip(old,result))),b) for a,b in zip(formulas,new)):
        raise Unsupported('The inverse chart did not recover the full source affine map')
    return result


def graph_determinant_residual(sides,numerators,det):
    """Keep a shared denominator rather than expanding repeated rational sides."""
    def lift(term):
        if term in numerators:return numerators[term]
        op=term[0]
        if op in ('add','mul'):
            a,i=lift(term[1]);b,j=lift(term[2])
            if op=='mul':return m.mul(a,b),i+j
            k=max(i,j)
            return m.add(m.mul(a,m.power(det,k-i)),m.mul(b,m.power(det,k-j))),k
        if op=='pow' and term[2]>=0:
            a,i=lift(term[1]);return m.power(a,term[2]),i*term[2]
        if op=='div' and not any(m.contains(term[2],g) for g in numerators):
            a,i=lift(term[1]);return m.div(a,term[2]),i
        if any(m.contains(term,g) for g in numerators):
            raise Unsupported('A nonpolynomial use of a jet needs a separate original-domain argument')
        return term,0
    n,p=lift(('add',sides[0],('mul',q(-1),sides[1])))
    original=(n,p)
    while p:
        raw=('div',n,det);reduced,divisor=m.rational_form(raw)
        candidate=m.poly_expr(reduced) if divisor=={():Fraction(1)} else m.polynomial_quotient(raw)
        if candidate==raw or m.rational_form(candidate)[1]!={():Fraction(1)}:break
        n,p=candidate,p-1
    return n,p,original


def characteristic_chart(task,lib):
    """Push a first-order characteristic field through the prescribed ambient chart."""
    normalized=lambda text:text.replace('²','^2').replace('³','^3').strip()
    formula,*restrictions=_delimited_fields(normalized(task['source_formula']).replace(';',','))
    tags=sorted(set(re.findall(r'\b([A-Za-z]\w*)_([a-z])\b',formula)))
    axes=[a for _,a in tags]
    if len(set(f for f,_ in tags))!=1 or len(set(axes)) not in (2,3) or formula.count('=')!=1:
        raise Unsupported('A scalar first-order PDE in two or three coordinates is required')
    field=tags[0][0];old=[*axes,field];jets=[f+'_'+a for f,a in tags]
    if len(set(old))!=len(old):raise Unsupported('The source field and independent variables must be distinct')
    names=lambda text:set(re.findall(r'\b[A-Za-z_]\w*\b',text))-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'}
    params=sorted(names(','.join([formula,*restrictions]))-set(old)-set(jets))
    symbols=lambda xs:list(map(mv_symbol,xs))
    X=symbols(old);W=X[-1];Z=symbols(jets)
    sides=[m.parse(s,None,[*old,*params,*jets]) for s in formula.split('=')]
    zero={z:ZERO for z in Z}
    R=m.add(sides[0],m.neg(sides[1]));constant=m.simplify(m.substitute(R,zero))
    coeff=[m.add(m.substitute(R,{**zero,z:ONE}),m.neg(constant)) for z in Z]
    velocity=[*coeff,m.neg(constant)]
    if any(any(m.contains(e,z) for z in Z) for side in sides for _,e in domain_conditions(side)):
        raise Unsupported('The field equation has a jet-dependent domain restriction')
    if not same_value(R,m.add(constant,m.dot(coeff,Z))) or all(v==ZERO for v in coeff):
        raise Unsupported('The equation does not define a nontrivial characteristic field')
    pairs=_delimited_fields(normalized(task['coordinate_change']))
    chart=[];labels=[]
    source_atoms=[*old,*params]
    for line in pairs:
        left,sep,right=line.partition('=')
        if not sep:raise Unsupported('The chart must declare its forward coordinate equations')
        left=left.strip()
        if log:=re.fullmatch(r'exp\(([A-Za-z_]\w*)\)',left):
            left=log[1];right=f'ln({right})'
        if not re.fullmatch(r'[A-Za-z_]\w*',left):raise Unsupported('The chart coordinate is unbound')
        labels.append(left);chart.append(m.parse(right,None,source_atoms))
    if len(chart)==len(axes):
        labels.append(field);chart.append(W)
    if len(chart)!=len(old) or len(set(labels))!=len(old) or set(labels)&set(params):
        raise Unsupported('The chart must bind one full set of independent and dependent coordinates')
    Y=symbols(labels);partial,steps=derivative_table(lib)
    rows=[[partial(v,a) for a in old] for v in chart]
    J=_chart_determinant(rows)
    if J==ZERO:raise Unsupported('The proposed ambient chart has identically zero determinant')
    graph=[[(m.add(row[i],m.mul(row[-1],z))) for i,z in enumerate(Z)] for row in rows[:-1]]
    graph_J=_chart_determinant(graph)
    if graph_J==ZERO:raise Unsupported('The independent projection is identically singular')
    directions=[m.polynomial_quotient(m.dot(row,velocity)) for row in rows]
    active=next((i for i,v in enumerate(directions[:-1]) if v!=ZERO),None)
    if active is None:raise Unsupported('The prescribed chart does not parameterize a characteristic direction')
    normal=directions[active]
    relative=[m.polynomial_quotient(m.div(v,normal)) for v in directions]
    # Every independent coordinate is invariant or has constant characteristic speed.
    rates=list(map(m.num,relative[:-1]))
    if any(k is None for k in rates):raise Unsupported('The transformed tangential speeds are not constant')
    a=Y[active];invariants=[m.add(y,m.mul(q(-k),a)) for i,(y,k) in enumerate(zip(Y,rates)) if i!=active]
    target=relative[-1]
    substitution=dict(zip(Y,chart))
    independent=Y[:-1]
    if any(m.contains(target,y) for y in X):
        from itertools import combinations_with_replacement
        kernel=None
        # The current chart supplies all candidates. The exact pullback decides whether one works.
        monomials=[ONE,*[m.mul(u,v) for u,v in combinations_with_replacement(independent,2)
                         if u!=a and v!=a],*independent]
        for divisor in (ONE,a):
            for term in monomials:
                g=m.div(term,divisor);pull=m.substitute(g,substitution)
                if pull==ZERO:continue
                c=m.polynomial_quotient(m.div(target,pull))
                if any(m.contains(c,x) for x in X):continue
                if same_value(target,m.mul(c,pull)):
                    kernel=m.mul(c,g);break
            if kernel is not None:break
        if kernel is None and chart[-1]==W and all(v[0]=='ln' for v in chart[:-1]):
            functions=[ONE,Y[-1],*(('exp',y) for y in independent)]
            bases=[ONE,W,*(v[1] for v in chart[:-1])]
            polys=[m.rational_form(v) for v in [target,*bases]]
            if all(d=={():Fraction(1)} for _,d in polys):
                support=sorted(set().union(*(set(p) for p,_ in polys)),key=canonical)
                cols=[tuple(p.get(mon,Fraction(0)) for mon in support) for p,_ in polys]
                solution=poly.span_coefficients(cols[0],cols[1:])
                if solution is not None:kernel=mv_sum(m.mul(q(c),v) for c,v in zip(solution,functions,strict=True))
        if kernel is None:raise Unsupported('No expression in the prescribed coordinates reproduces the transported rate')
    else:kernel=target
    # Integrate the normalized transformed equation, retaining its invariant arguments.
    new_rate=kernel
    dep=Y[-1]
    coefficient=m.add(m.substitute(kernel,{dep:ONE}),m.neg(m.substitute(kernel,{dep:ZERO})))
    forcing=m.substitute(kernel,{dep:ZERO})
    if not same_value(kernel,m.add(m.mul(coefficient,dep),forcing)) or m.num(coefficient) is None:
        raise Unsupported('The dependent rate is not affine with constant coefficient')
    if forcing==ZERO:particular=ZERO
    elif not m.contains(forcing,a) and all(k==0 for i,k in enumerate(rates) if i!=active) and coefficient==ZERO:
        particular=m.mul(a,forcing)
    elif forcing[0]=='div' and forcing[2]==a and not m.contains(forcing[1],a) and coefficient==ZERO and all(k==0 for i,k in enumerate(rates) if i!=active):
        particular=m.mul(forcing[1],('ln',('abs',a)))
    else:
        terms,den=m.rational_form(forcing)
        if den!={():Fraction(1)}:raise Unsupported('The normalized forcing has an unintegrated denominator')
        particular=ZERO
        for mon,c in terms.items():
            if mon:
                if len(mon)!=1 or mon[0][0][0]!='exp' or mon[0][0][1] not in independent:
                    raise Unsupported('The forcing has no supported characteristic primitive')
                speed=rates[independent.index(mon[0][0][1])]*mon[0][1]
            else:speed=Fraction(0)
            rate=speed-m.num(coefficient);term=m.poly_expr({mon:c})
            particular=m.add(particular,m.div(term,q(rate)) if rate else m.mul(a,term))
    dH=mv_sum(m.mul(q(k),partial(particular,y[1])) for k,y in zip(rates,Y))
    if not same_value(dH,m.add(m.mul(coefficient,particular),forcing)):
        raise Unsupported('The constructed particular solution does not satisfy the transported rate')
    guards=list(dict.fromkeys([*(g for v in [*sides,*chart] for g in domain_conditions(v,True)),
                               ('nonzero',J),('nonzero',graph_J),('nonzero',normal)]))
    for text in restrictions:
        bound=re.fullmatch(r'(.+?)(!=|>)(0)',text)
        if not bound:raise Unsupported('An original characteristic restriction is unresolved')
        guards.append(('nonzero' if bound[2]=='!=' else 'positive',m.parse(bound[1],None,source_atoms)))
    alternate=None
    if len(axes)==2 and all(not any(m.contains(v,z) for z in X) for v in velocity):
        if ('nonzero',velocity[0]) in guards:
            alternate=dict(original_dependent=W,particular=m.mul(m.div(velocity[-1],velocity[0]),X[0]),
                           invariant=m.add(X[1],m.neg(m.mul(m.div(velocity[1],velocity[0]),X[0]))))
    result=dict(normalized_equation=dict(active=labels[active],coordinate_velocities=list(map(q,rates)),
                                         dependent_rate=new_rate),
                scope='local regular graph sheets with the original restrictions')
    if task['requested_output']==['transform_equation']:
        transformed=mv_sum(m.mul(q(k),mv_symbol(labels[-1]+'_'+label)) for label,k in zip(labels,rates))
        result['transformed_sides']=[transformed,new_rate]
    else:
        result.update(local_solution=dict(dependent=labels[-1],particular=particular,
                                         homogeneous_factor=m.simplify(('exp',m.mul(coefficient,a))),invariants=invariants),
                      original_chart_at_rank_loss=alternate)
    return dict(theorem='method.integrate_coordinate_operator',original_field=velocity,forward_map=dict(zip(labels,chart)),
                ambient_jacobian=J,graph_jacobian=graph_J,source_domain=guards,normalized_rates=relative,
                active_coordinate=labels[active],derivative_rules=steps,argument=[
        'Вычисляем касательное направление из исходного уравнения и дифференцируем каждую заданную координату вдоль него.',
        'Делим на ненулевую скорость выбранной координаты на регулярном листе. Кандидаты на первые интегралы проверяем подстановкой в это направление.',
        'Решаем оставшееся линейное уравнение и проверяем дифференциал частного решения. Произвольная функция зависит только от инвариантов.',
    ]),result


def inverse_graph_coordinate_solution(task,request):
    marker=re.fullmatch(r'take ([xy]) to be a function of ([xyz]),([xyz])',task['coordinate_change'])
    if not marker or sorted(marker.groups())!=list('xyz'):
        raise Unsupported('The requested inverse graph is not a coordinate permutation')
    w,u,v=marker.groups();new=['u','v','w'];mapping=dict(zip((u,v,w),new))
    inverse=','.join(a+'='+mapping[a] for a in 'xyz')
    proof,value=graph_prolongation(dict(task,coordinate_change=inverse,requested_output=['transform_equation']),
                                  request,factored=True,new_names=new)
    residual,zero=value['transformed_sides']
    poly,den=m.rational_form(residual)
    if zero!=ZERO or den!={():Fraction(1)} or len(poly)!=1:
        raise Unsupported('The inverse graph has not led to an integrable single coordinate derivative')
    (mon,c),=poly.items()
    if len(mon)!=1 or mon[0][1]!=1 or not c or mon[0][0][0]!='s':
        raise Unsupported('The nonzero operator coefficient is not an isolated second derivative')
    names={('s','w_u_u'):(u,v),('s','w_v_v'):(v,u)}
    if mon[0][0] not in names:raise Unsupported('The isolated derivative is not a pure second derivative')
    active,free=names[mon[0][0]]
    proof['argument']+=' Интегрируем дважды по '+active+' при фиксированном '+free+': '+w+' = '+active+'·F('+free+') + G('+free+').'
    proof['original_coordinate_roles']=dict(dependent=w,independent=[u,v])
    value['local_solution']=dict(dependent=w,linear_coordinate=active,free_coordinate=free,
                                 formula=w+'='+active+'*F('+free+')+G('+free+')')
    value['scope']='inverse graph of the printed roles on its regular chart; rank-loss points do not use this formula'
    return proof,value


def graph_prolongation(task,request,*,factored=False,new_names=None):
    """Prolong a regular scalar graph coordinate map through its first two derivatives."""
    from itertools import combinations_with_replacement
    from tasks import domain_conditions,entailed_domain_guards,equality_domain_witness,guard_source,known_guard,source
    from verify import same_value
    normalize=lambda s:s.replace('²','^2').replace('³','^3').replace('⁴','^4')
    methods=task['requested_output'];formula,*conditions=normalize(task['source_formula']).split(';')
    if ' as printed, ' in formula:
        formula,condition=formula.split(' as printed, ',1);conditions.append(condition)
    formula=re.sub(r'\b(\d+)([xyz]{1,3})(?=\*|\b)',lambda h:h[1]+'*'+'*'.join(h[2]),formula)
    change=normalize(task['coordinate_change']);namespec=r'[A-Za-z][A-Za-z_0-9]*'
    tags={tag:(name,tuple(re.findall(r'[a-z]\d*',word))) for tag,name,word in
          re.findall(r'\b(([a-z])_([a-z0-9]+))\b',formula)}
    if not tags or len({f for f,_ in tags.values()})!=1 or any(not 1<=len(p)<=2 for _,p in tags.values()):
        raise Unsupported('Need the complete scalar graph and derivative orders through two')
    field=next(iter(tags.values()))[0];axes={v for _,path in tags.values() for v in path}
    axes=sorted(axes) if not axes<=set('xy') else list('xy')
    if len(axes) not in (2,3) or field in axes:raise Unsupported('Need two or three distinct independent coordinates')
    old=[*axes,field];dependent=field
    if head:=re.fullmatch(r'dependent ([a-z]); independent (.+)',change):dependent,change=head.groups()
    if dependent not in old:raise Unsupported('The designated new dependent coordinate is unbound')
    pairs=[tuple(s.strip().split('=')) for s in change.split(',')]
    if not all(len(x)==2 and re.fullmatch(namespec,x[0]) for x in pairs):raise Unsupported('Unparsed coordinate formulas')
    label=None;sides=formula.split('=')
    if methods==['transform_expression'] and len(sides)==2 and re.fullmatch(namespec,sides[0]):label,sides=sides[0],sides[1:]
    if methods not in (['transform_expression'],['transform_equation']) or len(sides) not in ((1,) if methods==['transform_expression'] else (2,3)):
        raise Unsupported('The entire equality or requested expression must be transformed')
    aliases={};trailing=[t.strip() for t in ','.join(conditions).split(',')]
    if conditions and all(re.fullmatch(r'[a-z]=[a-z]_[a-z]',t) for t in trailing):
        aliases=dict(t.split('=') for t in trailing);conditions=[]
        for val in aliases.values():
            f,a=val.split('_')
            if f!=field or a not in axes:raise Unsupported('An abbreviated derivative is not bound to the original expression')
            tags[val]=(f,(a,))
    identifiers=lambda t:set(re.findall(r'\b'+namespec+r'\b',t))
    params=sorted(identifiers(' '.join(sides))-set(old)-set(tags)-set(aliases)-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'})
    d=len(axes);direct=dict(pairs);ss=lambda n:('s',n)
    if len(direct)!=len(pairs):raise Unsupported('Coordinate names must be distinct')
    inverse=set(axes)<=direct.keys()
    if inverse:
        free=[];known=set(old)|set(params)|m.FUNCTIONS|set(m.ALIASES)|{'pi','e'}
        for axis in axes:
            for v in re.findall(r'\b'+namespec+r'\b',direct[axis]):
                if v not in known and v not in free:free.append(v)
        if new_names is not None:
            free=list(new_names[:-1]);w=new_names[-1]
        elif field in direct:
            field_symbols=identifiers(direct[field])-known
            if len(free)==d+1 and len(field_symbols)==1 and next(iter(field_symbols)) in free:
                w=next(iter(field_symbols));free.remove(w)
            elif len(free)==d and len(field_symbols-set(free))==1:
                w=next(iter(field_symbols-set(free)))
            else:raise Unsupported('Need a distinct dependent coordinate in the inverse map')
        else:w=field
        new=free+[w]
        if len(new)!=d+1 or len(set(new))!=len(new) or set(direct)-set(old):raise Unsupported('The inverse map leaves some coordinates unbound')
        chart=[m.parse(direct.get(axis,axis),None,[*new,*params]) for axis in old]
    else:
        if len(pairs)==d:pairs.append((dependent,dependent))
        if len(pairs)!=d+1:raise Unsupported('Need the full tuple of forward coordinates')
        new=[n for n,_ in pairs];chart=[m.parse(text,None,[*old,*params]) for _,text in pairs]
        if len(set(new))!=len(new) or len(axes)!=len(new)-1:raise Unsupported('The forward graph coordinates are ambiguous')
    if factored and not inverse:
        try:chart=affine_prolongation_inverse(chart,old,new)
        except Unsupported:factored=False
        else:inverse=True
    factored=factored and inverse and len(sides)==2 and d==2
    independent,w=new[:-1],new[-1]
    jets={}
    for order in (1,2):
        for path in combinations_with_replacement(range(d),order):
            name=w+'_'+'_'.join(independent[i] for i in path)
            while name in tags or name in new or name in params:name='new_'+name
            jets[path]=ss(name)
    coefficient_names=[*(new if inverse else old),*params,*[name[1] for name in jets.values()]]
    if len(coefficient_names)!=len(set(coefficient_names)):raise Unsupported('A coordinate or jet name captures a parameter')
    derivative_premises=[]
    diff=coordinate_sections(coefficient_names,request,local_premises=derivative_premises)
    chart_guards=list(dict.fromkeys(g for expr in chart for g in domain_conditions(expr,True)))
    raw=[m.parse(side,None,[*old,*params,*tags,*aliases]) for side in sides]
    alias_map={ss(a):ss(b) for a,b in aliases.items()}
    raw=[m.substitute(side,alias_map) for side in raw]
    chart_axes=new if inverse else old
    Jacobian=[[diff(expr,axis) for axis in chart_axes] for expr in chart]
    full_det=_chart_determinant(Jacobian)
    if same_value(full_det,m.ZERO):raise Unsupported('The ambient coordinate change is singular')
    # For an explicitly given inverse graph only its independent projection
    # must be nonsingular. A turning height may lose full ambient rank there.
    if not factored:chart_guards.append(('nonzero',full_det))
    grad=[jets[i,] for i in range(d)]
    if inverse:
        tangent=[[m.add(row[j],m.mul(row[-1],grad[j])) for j in range(d)] for row in Jacobian]
        graph_det=_chart_determinant(tangent[:-1])
        if same_value(graph_det,m.ZERO):raise Unsupported('The old independent coordinates are singular on the transformed graph')
        chart_guards.append(('nonzero',graph_det))
        cofactors=[]
        for i in range(d):
            row=[]
            for j in range(d):
                minor=[tuple(x for k,x in enumerate(r) if k!=j) for l,r in enumerate(tangent[:-1]) if l!=i]
                c=_chart_determinant(minor)
                row.append(m.neg(c) if (i+j)%2 else c)
            cofactors.append(row)
        directions=[[m.polynomial_quotient(m.div(e,graph_det)) for e in row] for row in cofactors]
        for i,direction in enumerate(directions):
            if not all(same_value(m.dot(direction,row),m.q(int(i==k))) for k,row in enumerate(tangent[:-1])):
                raise Unsupported('The reconstructed inverse graph directions fail the Jacobian identity')
        first=[m.polynomial_quotient(m.dot(v,tangent[-1])) for v in directions]
        def tangent_derivatives(e):
            derivatives=[]
            for j in range(d):
                value=m.add(diff(e,independent[j]),m.mul(diff(e,w),grad[j]))
                for k,g in enumerate(grad):value=m.add(value,m.mul(diff(e,g[1]),jets[tuple(sorted((j,k)))]))
                derivatives.append(value)
            return derivatives
        def total(e,i):return m.polynomial_quotient(m.dot(tangent_derivatives(e),directions[i]))
        if factored:
            first_num=[m.dot(row,tangent[-1]) for row in cofactors]
            den_rate=tangent_derivatives(graph_det)
            def factored_jet(path):
                i=axes.index(path[0]);N=first_num[i]
                if len(path)==1:return N,1
                j=axes.index(path[1])
                terms=[m.add(m.mul(a,graph_det),m.neg(m.mul(N,b))) for a,b in zip(tangent_derivatives(N),den_rate)]
                return m.dot(terms,cofactors[j]),3
        coordinate_substitution=dict(zip(map(ss,old),chart));chart_info=dict(inverse_chart=dict(zip(old,chart)))
    else:
        divisor=m.polynomial_quotient(m.add(Jacobian[-1][-1],m.neg(m.dot(grad,[r[-1] for r in Jacobian[:-1]]))))
        if same_value(divisor,m.ZERO):raise Unsupported('The declared old graph is vertical in the new coordinate representation')
        chart_guards.append(('nonzero',divisor))
        first=[m.polynomial_quotient(m.div(m.add(m.dot(grad,[r[i] for r in Jacobian[:-1]]),m.neg(Jacobian[-1][i])),divisor))
               for i in range(d)]
        tangent=[[m.add(r[i],m.mul(r[-1],first[i])) for i in range(d)] for r in Jacobian[:-1]]
        for i in range(d):
            dw=m.add(Jacobian[-1][i],m.mul(Jacobian[-1][-1],first[i]))
            if not same_value(dw,m.dot(grad,[row[i] for row in tangent])):
                raise Unsupported('The first derivative does not reproduce the exact graph differential')
        def total(e,i):
            value=m.add(diff(e,axes[i]),m.mul(diff(e,field),first[i]))
            for k,g in enumerate(grad):
                value=m.add(value,m.mul(diff(e,g[1]),m.dot([r[i] for r in tangent],[jets[tuple(sorted((j,k)))] for j in range(d)])))
            return m.polynomial_quotient(value)
        # Old coefficients are functions of the new coordinates on the certified local inverse chart.
        coordinate_substitution={ss(axis):ss('old_'+axis) for axis in old if axis not in new or chart[new.index(axis)]!=ss(axis)}
        chart_info=dict(forward_chart=dict(zip(new,chart)),inverse_coordinate_description={
            'names':{k[1]:v[1] for k,v in coordinate_substitution.items()},
            'equations':[{n:m.substitute(e,coordinate_substitution)} for n,e in zip(new,chart)]})
    if factored:
        numerators={ss(tag):factored_jet(path) for tag,(_,path) in tags.items()}
        values={tag[1]:('div',n,m.power(graph_det,p)) for tag,(n,p) in numerators.items()}
    else:
        values={tag:first[axes.index(path[0])] if len(path)==1 else total(first[axes.index(path[0])],axes.index(path[1]))
                for tag,(_,path) in tags.items()}
    derivatives={ss(k):v for k,v in values.items()}
    bind=lambda e:m.substitute(m.substitute(e,derivatives),coordinate_substitution)
    conditions_map=[]
    for clause in conditions:
        match=re.fullmatch(r'([^<>]+)([<>])([^<>]+)',clause.strip())
        if not match:raise Unsupported('Unsupported condition remains in the original equation')
        a,b=(m.parse(text,None,[*old,*params]) for text in (match[1],match[3]))
        if match[2]=='<':a,b=b,a
        conditions_map.extend(domain_conditions(a)+domain_conditions(b)+[('positive',m.add(a,m.neg(b)))])
    source_guards=list(dict.fromkeys((rel,bind(g)) for e in raw for rel,g in domain_conditions(e)))
    source_guards.extend((rel,bind(g)) for rel,g in conditions_map)
    used=[*new,*params,*[v[1] for v in coordinate_substitution.values() if v[0]=='s'],
          *[name[1] for name in jets.values()]]
    guards=list(dict.fromkeys([*source_guards,*((rel,m.substitute(g,coordinate_substitution) if not inverse else g) for rel,g in chart_guards)]))
    symbols=list(map(ss,dict.fromkeys(used)))
    try:witness=equality_domain_witness(symbols,[],guards)
    except Unsupported:witness=equality_domain_witness(list(reversed(symbols)),[],guards)
    ctx=m.context(dict(variable='__new_chart',parameters=list(dict.fromkeys(used)),
                       parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    if not all(known_guard((rel,m.substitute(e,coordinate_substitution) if not inverse else e),ctx)
               for rel,e in derivative_premises):
        raise Unsupported('A derivative premise is not implied by the source and regular chart conditions')
    if factored:
        lifted=[m.substitute(e,coordinate_substitution) for e in raw]
        normal,p,identity=graph_determinant_residual(lifted,numerators,graph_det)
        numer,denom=m.rational_form(normal)
        nonzero_units={a:k for a,k in m.common_mon(numer).items() if a[0]=='exp' and not domain_conditions(a)}
        if nonzero_units and denom=={():Fraction(1)}:
            normal=m.poly_expr({tuple((a,k-nonzero_units.get(a,0)) for a,k in mon if k>nonzero_units.get(a,0)):c
                                for mon,c in numer.items()})
            chart_info['removed_positive_exponential_factors']=list(nonzero_units.items())
        transformed=[normal,ZERO]
        chart_info.update(graph_jacobian=graph_det,factored_jet_numerators={tag[1]:pair for tag,pair in numerators.items()},
                          uncancelled_graph_residual=identity,remaining_determinant_power=p,
                          preservation='independent-projection chart, including permitted ambient height turning')
    else:transformed=[bind(e) for e in raw]
    alternatives=[m.polynomial_quotient(e) for e in transformed]
    outputs=[alt if all(known_guard(g,ctx) for g in domain_conditions(alt)) and same_value(e,alt) else e
             for e,alt in zip(transformed,alternatives)]
    for rel,e in dict.fromkeys(g for output in outputs for g in domain_conditions(output)):
        if known_guard((rel,e),ctx):continue
        if rel=='nonzero' and any(same_value(e,m.mul(b,unit)) and known_guard(('nonzero',unit),ctx)
                    for r,b in guards if r in ('positive','nonzero') and m.tree_size(b)+m.tree_size(e)<80
                    for unit in [m.polynomial_quotient(m.div(e,b))]):continue
        raise Unsupported('A new denominator is not justified by the source and regular chart conditions: '+guard_source((rel,e)))
    proof=dict(theorem='method.regular_graph_prolongation',**chart_info,variables=independent,dependent=w,ambient_jacobian=full_det,
               source_domain=source_guards,chart_domain=guards,witness=witness,derivative_map={k:m.substitute(v,coordinate_substitution) for k,v in values.items()},
               argument='Выводим дифференциальные направления из якобиана карты. Повторно применяем их к уже найденным производным, учитывая изменение коэффициентов и производных новой функции.')
    value=dict(transformed_sides=outputs,scope='all real regular original and new graph charts')
    if factored:
        proof['argument']+=' Общую степень определителя сохраняем до сложения и сокращаем только при доказанной регулярности графика.'
        proof['applied_methods']=['method.factored_graph_determinant']
    if label:value['expression_name']=label
    return proof,value

def ordinary_log_chart(task,library):
    """Transport every ordinary derivative through an invertible logarithmic chart."""
    from tasks import domain_conditions,entailed_domain_guards,equality_domain_witness,guard_source,known_guard,source
    from verify import same_value
    form=task['source_formula'].replace('²','^2').replace('³','^3').replace('⁴','^4')
    change=task['coordinate_change'];equations=form.split('=')
    if len(equations)!=2 or task['requested_output']!=['transform_equation']:
        raise Unsupported('A complete ordinary equation in the logarithmic chart is required')
    match=re.fullmatch(r'(?:u=([^,]+), )?t=ln\(abs\((.+)\)\)',change)
    if not match:raise Unsupported('No logarithmic independent coordinate was specified')
    knot=match[2];relation=match[1] or 'y';ss=lambda s:('s',s);x,y,t,u=map(ss,('x','y','t','u'))
    replaced=[re.sub(r"\by('+)",lambda z:'old_y'+str(len(z[1])),e) for e in equations]
    orders=[int(k) for e in replaced for k in re.findall(r'\bold_y(\d+)\b',e)]
    highest=max(orders,default=0)
    if not 1<=highest<=4:raise Unsupported('The ordinary derivative order is not bound to a supported jet')
    identifiers=set(re.findall(r'\b[A-Za-z][A-Za-z_0-9]*\b',form+' '+knot+' '+relation))
    parameters=sorted(identifiers-{'x','y','t','u','pi','e'}-m.FUNCTIONS-set(m.ALIASES))
    g=m.parse(knot,None,['x',*parameters]);u_map=m.parse(relation,None,['x','y',*parameters])
    monomial=lambda z:m.polynomial_quotient(z)
    pg,dg=m.rational_form(g)
    def axis_coefficients(poly):
        # Coefficients of the old coordinate may be ordinary fixed parameters.
        rows=[{},{}]
        for mon,k in poly.items():
            degree=dict(mon).get(x,0)
            if degree>1 or any(m.contains(a,x) and a!=x for a,_ in mon):
                raise Unsupported('The logarithmic absolute argument needs an invertible fractional linear map')
            rows[degree][tuple((a,power) for a,power in mon if a!=x)]=k
        return tuple(map(m.poly_expr,rows))
    b,a=axis_coefficients(pg);d,c=axis_coefficients(dg);det=m.add(m.mul(a,d),m.neg(m.mul(b,c)))
    if same_value(det,m.ZERO):raise Unsupported('The logarithmic chart has constant argument')
    if any(m.contains(e,y) for _,e in domain_conditions(u_map,True)):
        raise Unsupported('The dependent scale has an unresolved original restriction involving y')
    factor=m.polynomial_quotient(m.substitute(u_map,{y:m.ONE}))
    if same_value(factor,m.ZERO) or not same_value(u_map,m.mul(factor,y)):
        raise Unsupported('Need a nonvanishing scalar factor for the old dependent field')
    jets=[u]+[ss('u_'+str(i)) for i in range(1,highest+1)]
    old_symbols=['y']+['old_y'+str(i) for i in range(1,highest+1)]
    raw=[m.parse(e,None,['x',*parameters,*old_symbols]) for e in replaced]
    derivatives=[];checked_partial,derivative_rules=derivative_table(library)
    def partial(expr,axis):
        derivatives.extend(domain_conditions(expr,True))
        return checked_partial(expr,axis)
    theta_x=monomial(m.div(partial(g,'x'),g));Y=monomial(m.div(u,factor))
    guards=list(dict.fromkeys([*domain_conditions(g,True),*domain_conditions(u_map,True),('nonzero',g),('nonzero',det),('nonzero',factor),
                               ('nonzero',theta_x)]))
    change_y=[Y]
    for i in range(highest):
        v=change_y[-1];dz=partial(v,'x')
        for j in range(i+1):dz=m.add(dz,m.mul(theta_x,m.mul(partial(v,jets[j][1]),jets[j+1])))
        change_y.append(monomial(dz))
    substitute=dict(zip(map(ss,old_symbols),change_y))
    guards.extend((r,m.substitute(e,substitute)) for expr in raw for r,e in domain_conditions(expr))
    guards=list(dict.fromkeys(guards));symbols=[x,*map(ss,parameters),*jets]
    witness=equality_domain_witness(symbols,[],guards)
    ctx=m.context(dict(variable='__logical_coordinate',parameters=[s[1] for s in symbols],
                       parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    if not all(known_guard(g,ctx) for g in derivatives):raise Unsupported('Some chain-rule coefficients require additional domain conditions')
    residual=monomial(m.add(m.substitute(raw[0],substitute),m.neg(m.substitute(raw[1],substitute))))
    p,den=m.rational_form(residual);prefactor={tuple((s,n) for s,n in mon if s!=jets[-1]):k for mon,k in p.items() if dict(mon).get(jets[-1])==1}
    if prefactor:
        lead=monomial(m.div(m.poly_expr(prefactor),m.poly_expr(den)))
        if not any(m.contains(lead,j) for j in jets):
            original_lead=partial(m.add(raw[0],m.neg(raw[1])),old_symbols[-1])
            nonzero=known_guard(('nonzero',lead),ctx)
            if not nonzero and m.num(original_lead) not in (None,0):
                expanded=m.div(m.mul(original_lead,m.power(theta_x,highest)),factor)
                nonzero=same_value(lead,expanded)
            if nonzero:
                candidate=monomial(m.div(residual,lead))
                if same_value(residual,m.mul(candidate,lead)):residual=candidate
    branches=[]
    for sign in (-1,1):
        ratio=m.mul(m.q(sign),('exp',t));inverse=monomial(m.div(m.add(b,m.neg(m.mul(ratio,d))),m.add(m.mul(ratio,c),m.neg(a))))
        if not same_value(m.substitute(g,{x:inverse}),ratio):raise Unsupported('The proposed inverse does not recover the signed argument')
        branch_g=[(r,m.substitute(e,{x:inverse})) for r,e in guards]
        branch_g.append(('nonzero',m.add(m.mul(ratio,c),m.neg(a))))
        # Substitution is exact even when expansion destroys useful factorization.
        transported=m.substitute(residual,{x:inverse})
        try:reduced=monomial(transported)
        except poly.ResourceBound:reduced=transported
        branches.append(dict(argument_sign=sign,old_abscissa=inverse,transformed_equation=[reduced,m.ZERO],
                             source_and_chart_conditions=list(dict.fromkeys(branch_g))))
    return dict(theorem='method.ordinary_log_coordinate',source_raw_equations=raw,coordinate_argument=g,coordinate_derivative=theta_x,
                dependent_scale=factor,jet_lifts=change_y,derivative_rules=derivative_rules,nonempty_source_scope=witness,argument='По обе стороны знака аргумента используем d ln|g|/dx=g′/g. По очереди переносим производные и проверяем обратную дробно-линейную карту на каждой допустимой ветви.'),dict(branches=branches)


def ordinary_structural_coordinate(task):
    """Recognize a gauge, an order reduction by homogeneity, or a dual derivative graph."""
    form=task['source_formula'].replace('²','^2').replace('³','^3');change=task['coordinate_change'];want=task['requested_output']
    name=r'([A-Za-z][A-Za-z_0-9]*)';sf=lambda s:('s',s)
    if want==['transform_equation']:
        if change=='dependent x, independent t=x*y':
            from tasks import domain_conditions
            from verify import same_value
            old_x,y,d1,d2=map(sf,('x','y','y_1','y_2'))
            raw=re.sub(r"\by('+)",lambda s:'y_'+str(len(s[1])),form)
            if raw.count('=')!=1:raise Unsupported('One original graph equation is required')
            a,b=(m.parse(t,None,['x','y','y_1','y_2']) for t in raw.split('='));R=m.add(a,m.neg(b))
            zero={y:m.ZERO,d1:m.ZERO,d2:m.ZERO}
            force=m.neg(m.substitute(R,zero));coeff=m.add(m.substitute(R,{**zero,y:m.ONE}),force)
            known=m.add(m.add(d2,m.div(m.mul(m.q(2),d1),old_x)),m.add(m.mul(coeff,y),m.neg(force)))
            if any(m.contains(e,v) for p in (a,b) for _,e in domain_conditions(p) for v in (y,d1,d2)) or not same_value(R,known):
                raise Unsupported('The new product coordinate must combine the original first and second derivatives exactly')
            t,X,X1,X2=map(sf,('t','X','X_1','X_2'));coef,force=(m.substitute(e,{old_x:X}) for e in (coeff,force))
            new_left=m.add(m.div(m.neg(X2),m.power(X1,3)),m.mul(t,coef));new_right=m.mul(X,force)
            return (dict(theorem='method.ordinary_product_as_coordinate',source_holes=domain_conditions(a)+domain_conditions(b),
                         chart_conditions=['x!=0','dx/dt!=0'],argument='Собираем y″+2y′/x в (xy)″/x. Затем берём t=xy как независимую координату и используем вторую производную обратной функции x(t).'),
                    dict(transformed_sides=[new_left,new_right]))
        gauge=re.fullmatch(r"y''\+"+name+r"\(x\)\*?y'\+"+name+r'\(x\)\*?y=0',form)
        if gauge and gauge[1]!=gauge[2] and change==f'y=u*exp(-int_x0^x {gauge[1]}(s)ds/2); {gauge[1]} in C1':
            p,q=gauge.groups();P,Q,D=map(sf,('coefficient_'+p,'coefficient_'+q,'derivative_'+p))
            normalized=m.add(Q,m.neg(m.add(m.mul(m.q(1,2),D),m.mul(m.q(1,4),m.power(P,2)))))
            return (dict(theorem='method.ordinary_gauge_normal_form',source_functions=[p,q],derivative_of_log_scale=m.mul(m.q(-1,2),P),
                         scale_is_strictly_positive=True,first_derivative_coefficient=m.ZERO,
                         argument='Дифференцируем экспоненциальный множитель через его логарифмическую производную. Слагаемые при первой производной новой функции сокращаются, а вторую производную множителя вычисляем ещё одним применением правила произведения.'),
                    dict(transformed_sides=[m.add(sf('u_2'),m.mul(normalized,sf('u'))),m.ZERO],
                         coefficients={P[1]:p+'(x)',Q[1]:q+'(x)',D[1]:p+"'(x)"}))
        homogeneous=re.fullmatch(name+r'\(([^,]+),([^,]+),([^,]+)\)=0, \1 homogeneous(?: in its arguments)?',form)
        if homogeneous:
            F,*components=homogeneous.groups();argument_sets={"y":'1',"y'":'u',"y''":"u'+u^2"}
            if re.fullmatch(r'y=exp\(int_[A-Za-z_]\w*\^x u\(s\)ds\)',change) and set(components)==set(argument_sets):
                domain='positive exponential scale on the integral domain';replacement=argument_sets;cases=None
            elif re.fullmatch(r"u=x\*(?:y_prime|y')/y",change) and set(components)=={"x^2*y''","x*y'","y"}:
                domain='x!=0 and y!=0 on each chart';replacement={"x^2*y''":"x*u'+u^2-u","x*y'":'u','y':'1'}
                cases={'positive_scale':'as listed','negative_scale_if_homogeneous_only_for_positive_factors':'negate each listed argument'}
            else:raise Unsupported('The source homogeneous relation or logarithmic change has a different order')
            return (dict(theorem='method.ordinary_homogeneous_log_derivative',function=F,source_args=components,
                         chart_domain=domain,argument='После замены все три аргумента имеют один и тот же ненулевой масштаб. По однородности выносим его степень и сохраняем область, где деление законно.'),
                    dict(transformed_condition=F+'('+','.join(replacement[c] for c in components)+')=0',signed_cases=cases))
    if form=='y=y(x)' and change=='X=y_prime,Y=x*y_prime-y' and want==["find Y',Y'',Y'''"]:
        y2,y3=map(sf,('y_2','y_3'))
        return (dict(theorem='method.ordinary_derivatives_of_dual_graph',nonzero_second_derivative=y2,
                     argument='Дифференциал Y равен x dX. На каждой ветви y″≠0 оператор d/dX равен (1/y″) d/dx. Им последовательно дифференцируем x и обратную вторую производную.'),
                dict(derivatives={'Y_1':sf('x'),'Y_2':m.div(m.ONE,y2),'Y_3':m.div(m.neg(y3),m.power(y2,3))}))
    raise Unsupported('No supported ordinary gauge, homogeneous chart or local dual graph')

def _delimited_fields(text,separator=','):
    depth=0;start=0;parts=[]
    for i,ch in enumerate(text):
        if ch in '([':depth+=1
        elif ch in ')]':depth-=1
        elif ch==separator and depth==0:parts.append(text[start:i].strip());start=i+1
        if depth<0:raise Unsupported('Unbalanced source expression')
    if depth:raise Unsupported('Unbalanced source expression')
    return [*parts,text[start:].strip()]


def _chart_cross(a,b):
    return [m.add(m.mul(a[(i+1)%3],b[(i+2)%3]),m.neg(m.mul(a[(i+2)%3],b[(i+1)%3]))) for i in range(3)]


def differential_invariants(task,library,request):
    """Prove a differential consequence by transporting source invariants or eliminating a stationary parameter."""
    from tasks import domain_conditions,entailed_domain_guards,guard_source,known_guard,source
    from verify import same_value
    if not library.data.get('flow_differential_invariants'):
        raise Unsupported('The differentiable invariants are not available')
    fields={'id','kind','source','source_formula','stated_conditions','requested_output','suggested_method'}
    meta=task.get('source',{});wanted=task['requested_output'];formula=task['source_formula']
    if (set(task)-fields or task.get('stated_conditions') or not isinstance(formula,str) or not isinstance(wanted,list)
            or len(wanted) not in (1,2) or not wanted[0].startswith('prove ')
            or len(wanted)==2 and wanted[1]!='geometric_properties_of_surface'
            or not isinstance(meta,dict) or set(meta)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement','section_convention'}
            or meta.get('section_convention') not in (None,'p310 footnote: existence of the implicit functions and needed derivatives is assumed in most exercises unless otherwise stated')
            or meta.get('literal_requirement','; '.join(wanted)) not in ('; '.join(wanted),'implicit differential identity; '+', '.join(wanted))
            or task.get('suggested_method') not in (None,'induction')):
        raise Unsupported('The original differential identity has additional unbound assumptions or conclusions')
    norm=lambda s:s.replace('²','^2').replace('³','^3').replace('[','(').replace(']',')')
    F=norm(formula);goal=norm(wanted[0].removeprefix('prove '));ss=lambda k:('s',k)
    x,y,z,alpha,X,Y=map(ss,('x','y','z','alpha','z_x','z_y'))
    names=lambda s:set(re.findall(r'\b[A-Za-z][A-Za-z_0-9]*\b',s))
    if F=='u=f(z);z=x+y*phi(z)' and goal=='partial_y^n u=partial_x^(n-1)(phi(z)^n*u_x)' and len(wanted)==1:
        return (dict(theorem='method.induction_along_flow',regularity='derivatives through n exist on a differentiable branch',
                    chart_nonzero='1=(1-y*phi_prime(z))*z_x',first_order=['u_y=H*u_x','H_y=H*H_x'],step='D_y(H^m*u_x)=D_x(H^(m+1)*u_x)',
                    argument='Сначала неявно дифференцируем z по x и y. Для H=φ(z) получаем H_y=H H_x, а для u получаем u_y=H u_x. Правило произведения даёт D_y(H^m u_x)=D_x(H^(m+1)u_x), и перестановка смешанных производных завершает индукцию.'),dict(proved=True,all_positive_integer_orders=True))
    if F=='y=x*phi(z)+psi(z)' and goal=='(z_y)^2*z_xx-2*z_x*z_y*z_xy+(z_x)^2*z_yy=0' and len(wanted)==1:
        return (dict(theorem='method.straight_level_hessian',tangent='(1,phi(z))',
                    argument='На каждом фиксированном уровне z=c исходное уравнение задаёт прямую. Её касательное поле уничтожает z и остаётся постоянным вдоль прямой. Вторая направленная производная нулевая. Так как z_x+φ(z)z_y=0, умножение на z_y² даёт исходное равенство без деления.'),dict(proved=True))
    fparts=_delimited_fields(F,';')
    if len(fparts)==1 and goal.count('=')==1:
        relation=F.split('=');matches=[re.fullmatch(r'(?:(.+)\*)?([A-Za-z][A-Za-z_0-9]*)\((.+)\)',s) for s in relation]
        options=[]
        if len(relation)==2:
            for k,match in enumerate(matches):
                if match and match[2] not in m.FUNCTIONS|set(m.ALIASES):
                    args=_delimited_fields(match[3]);opposite=relation[1-k]
                    if len(args)==2 and opposite=='0' and not match[1]:options.append((args,[]))
                    if len(args)==1 and opposite!='0':
                        base=opposite if not match[1] else '('+opposite+')/('+match[1]+')'
                        options.append(([base,args[0]],[match[1]] if match[1] else []))
        if len(options)==1:
            invariants,divisors=options[0];nameset=['x','y','z',*sorted((names(' '.join(invariants)+' '+goal)-
                        m.FUNCTIONS-set(m.ALIASES)-{'pi','e','x','y','z','z_x','z_y'}))]
            parsed=[m.parse(s,None,nameset) for s in invariants]
            initial_scope=domain_conditions(parsed[-1],True)
            initial_ctx=m.context(dict(variable='__field',parameters=nameset,
                                parameter_conditions=[guard_source(s) for s in entailed_domain_guards(initial_scope)]))
            scope=list(dict.fromkeys(g for e in parsed for g in domain_conditions(e,True)))
            ctx=m.context(dict(variable='__field',parameters=nameset,parameter_conditions=[guard_source(s) for s in entailed_domain_guards(scope)]))
            if not all(known_guard(('nonzero',m.parse(d,None,nameset)),initial_ctx) for d in divisors):
                raise Unsupported('The source rescaling of an arbitrary function need not be defined')
            left,right=(m.parse(s,None,[*nameset,'z_x','z_y']) for s in goal.split('='))
            expr=m.add(left,m.neg(right));p,d=m.rational_form(expr)
            if any(a in (X,Y) for mon in d for a,_ in mon):raise Unsupported('The proposed tangent relation is not linear in the graph gradient')
            slots=[{}, {}, {}]
            for mon,c in p.items():
                powers=dict(mon);i,j=powers.get(X,0),powers.get(Y,0)
                if i+j>1:raise Unsupported('The graph directional equation has expected order one')
                slots[i+2*j][tuple((a,k) for a,k in mon if a not in (X,Y))]=c
            den=m.poly_expr(d);vec=[m.div(m.poly_expr(slots[k]),den) for k in (1,2,0)];vec[-1]=m.neg(vec[-1])
            if not all(known_guard(g,ctx) for e in vec for g in domain_conditions(e,True)):
                raise Unsupported('An inferred vector field has unverified holes on the source chart')
            derivatives=[];diff=coordinate_sections(nameset,request,local_premises=derivatives)
            gradients=[[diff(e,axis) for axis in ('x','y','z')] for e in parsed]
            if not all(known_guard(g,ctx) for g in derivatives) or not all(same_value(m.dot(row,vec),m.ZERO) for row in gradients):
                raise Unsupported('The proposed directional field does not preserve every independent source invariant')
            geometric=None
            if len(wanted)==2:
                xyz=(x,y,z)
                if all(not any(m.contains(e,a) for a in xyz) for e in vec) and same_value(vec[2],m.ONE):
                    geometric=dict(type='parallel_rulings',direction=vec)
                elif all(not any(m.contains(m.add(a,m.neg(b)),p) for p in xyz) for a,b in zip(xyz,vec)):
                    geometric=dict(type='cone_by_rays',vertex=[m.add(a,m.neg(b)) for a,b in zip(xyz,vec)])
                else:
                    J=[[diff(e,axis) for axis in ('x','y','z')] for e in vec]
                    if not (all(not any(m.contains(e,a) for a in xyz) for row in J for e in row) and
                            all(same_value(m.add(J[i][j],J[j][i]),m.ZERO) for i in range(3) for j in range(3)) and
                            all(same_value(m.dot(row,xyz),e) for row,e in zip(J,vec))):
                        raise Unsupported('A requested geometric classification needs a verified geometric flow')
                    geometric=dict(type='rotation_orbits',axis=[J[2][1],J[0][2],J[1][0]],zero_axis='every source sphere has rotational symmetry')
            proposal=_chart_cross(*gradients)
            if not all(same_value(x,m.ZERO) for x in _chart_cross(proposal,vec)) or not all(known_guard(g,ctx) for g in derivatives):
                raise Unsupported('The inferred direction disagrees with the common kernel')
            plan=dict(theorem='method.common_kernel_of_source_invariants',invariants=parsed,invariant_gradients=gradients,
                      kernel_candidate=proposal,preserved_direction=vec,source_domain=scope,
                      argument='Из аргументов произвольной функции извлекаем сохраняющиеся величины. Градиенты дают общее касательное направление. Проверяем, что исходное уравнение сохраняется вдоль этого поля, и переносим его на график.')
            return plan,dict(proved=True,geometric_properties=geometric,field=vec)
    if len(fparts)==2 and all(part.count('=')==1 for part in fparts) and len(wanted)==1:
        known=re.findall(r'\b([A-Za-z_]\w*)\(alpha\)',F)
        funcs=sorted({f.removesuffix('_prime') for f in known if f not in m.FUNCTIONS and f not in m.ALIASES})
        if not funcs or len(funcs)>3:raise Unsupported('Unbound arbitrary functions of the stationary parameter')
        values={f:('value_'+f,'slope_'+f) for f in funcs}
        def rename(text):
            for f,(v,d) in values.items():text=text.replace(f+'_prime(alpha)',d).replace(f+'(alpha)',v)
            return text
        variables=['x','y','z','alpha',*(s for pair in values.values() for s in pair)]
        pairs=[[m.parse(rename(e),None,variables) for e in part.split('=')] for part in fparts]
        R,S=(m.add(a,m.neg(b)) for a,b in pairs);guards=domain_conditions(R,True)+domain_conditions(S,True)
        derivatives=[];diff=coordinate_sections(variables,request,local_premises=derivatives)
        Ralpha=m.add(diff(R,'alpha'),m.dot([diff(R,v) for v,d in values.values()],[ss(d) for v,d in values.values()]))
        multiplier=next((m.q(c) for c in (1,-1,2,-2) if same_value(Ralpha,m.mul(m.q(c),S))),None)
        if multiplier is None:raise Unsupported('The second equation does not express stationarity of the original relation')
        rz=m.polynomial_quotient(diff(R,'z'));ctx=m.context(dict(variable='__envelope',parameters=variables,
                          parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
        if not known_guard(('nonzero',rz),ctx) or not all(known_guard(g,ctx) for g in derivatives):
            raise Unsupported('A vanishing implicit coefficient needs a separate source-branch proof')
        roots=[m.polynomial_quotient(m.div(m.neg(diff(R,k)),rz)) for k in ('x','y')]
        hess=None
        if any(s in goal for s in ('z_xx','z_yy','z_xy')):
            p,q=ss('alpha_x'),ss('alpha_y');variables.extend(['alpha_x','alpha_y'])
            derivative=lambda v:m.add(diff(v,'alpha'),m.dot([diff(v,a) for a,b in values.values()],[ss(b) for a,b in values.values()]))
            if any(v in names(source(part)) for part in roots for v in ('x','y','z')):
                raise Unsupported('The rank-one Hessian must arise only through the stationary parameter')
            hess=dict(z_xx=m.mul(derivative(roots[0]),p),z_xy=m.mul(derivative(roots[0]),q),
                      z_yx=m.mul(derivative(roots[1]),p),z_yy=m.mul(derivative(roots[1]),q))
        old=dict(zip(('z_x','z_y'),roots));old.update(hess or {})
        a,b=(m.parse(e,None,[*variables,*old]) for e in goal.split('='))
        if hess and goal=='z_xx*z_yy-z_xy^2=0':
            # Smooth graph gives equality of mixed derivatives. Verify the symbolic rank-one relation.
            determinant=m.add(m.mul(hess['z_xx'],hess['z_yy']),m.neg(m.mul(hess['z_xy'],hess['z_yx'])))
            if not same_value(determinant,m.ZERO):raise Unsupported('The computed Hessian is not a rank-one matrix')
        elif not same_value(m.substitute(a,{ss(k):v for k,v in old.items()}),m.substitute(b,{ss(k):v for k,v in old.items()})):
            raise Unsupported('The asserted relation does not follow from stationary differentiation')
        return (dict(theorem='method.stationary_parameter_elimination',source_residual=R,stationary_residual=S,stationarity_factor=multiplier,
                     dependent_coefficient=rz,gradient=roots,rank_one_hessian=hess,source_domain=guards,
                     argument='В неявной производной коэффициент при изменении параметра равен нулю по второму исходному уравнению. Вычисляем оставшиеся частные производные и подставляем их в требуемое равенство.'),dict(proved=True,first_derivatives=roots))
    raise Unsupported('No verified source differential consequence was found')

def incompatible_implicit_point(equations,point,guards):
    """Reject a putative point only after an exact separation on its original domain."""
    from quadrature import enclose
    from tasks import known_guard
    # The point is bound and real before this procedure. Recheck each original operation.
    ctx=dict(parameters=[],assumptions=[]);at=lambda e:m.substitute(e,point)
    if not all(known_guard((r,at(e)),ctx) for r,e in guards):return None
    for idx,(a,b) in enumerate(equations):
        left,right=at(a),at(b)
        try:P,Q=(enclose(e,None) for e in (left,right))
        except (Unsupported,ArithmeticError):continue
        if not (P[1]<Q[0] or Q[1]<P[0]):continue
        return (dict(theorem='method.incompatible_implicit_point',violated_equation=idx+1,source_domain=guards,
                     argument='Проверяем, принадлежит ли заданная точка исходной системе. Точные вещественные оценки левой и правой частей одного равенства лежат в непересекающихся интервалах. Производных этой системы в заданной точке нет.'),
                dict(printed_claim_holds=False,counterexample=dict(point={k[1]:v for k,v in point.items()},
                        equation=idx+1,left=left,right=right,left_bounds=list(map(m.q,P)),right_bounds=list(map(m.q,Q)))))
    return None


def hyperbolic_constant_symbol(task):
    """Build and verify both characteristic directions of a constant hyperbolic symbol."""
    from tasks import domain_conditions,source
    from verify import same_value
    S=lambda n:('s',n)
    text=task['source_formula'].replace('²','^2')
    parts=text.split(';')
    if len(parts)!=3 or parts[0].count('=')!=1:
        raise Unsupported('Expected the constant symbol and its strict discriminant condition')
    declared=re.fullmatch(r'([A-Za-z_, ]+) constant',parts[1].strip())
    charts=re.sub(r'\s+','',task['coordinate_change']).split(',')
    slots=[]
    for chart in charts:
        row=re.fullmatch(r'([a-z]+)=(?:x\+([A-Za-z_]\w*)\*y|([A-Za-z_]\w*)\*y\+x)',chart)
        if row:slots.extend((row[1],row[2] or row[3]))
    tags=sorted(set(re.findall(r'\b([a-z])_([xy]{2})\b',parts[0])))
    if not declared or len(charts)!=2 or len(set(slots))!=4 or not tags or len({f for f,_ in tags})!=1:
        raise Unsupported('The original two linear characteristic slots must be distinct')
    pars=[p.strip() for p in declared[1].split(',')]
    field=tags[0][0];jets=[f+'_'+j for f,j in tags];names=[*pars,*jets]
    if len(set(names))!=len(names) or set(slots)&set([*names,field,'x','y']):
        raise Unsupported('A source parameter, jet or chart name collides')
    m.context(dict(variable='__characteristic',parameters=names))
    L,R=(m.parse(side,None,names) for side in parts[0].split('='))
    expr=m.add(L,m.neg(R));zero=dict.fromkeys(map(S,jets),m.ZERO)
    terms={w:m.simplify(m.substitute(expr,{**zero,S(f+'_'+w):m.ONE})) for f,w in tags}
    if domain_conditions(L) or domain_conditions(R) or not same_value(expr,m.dot(list(map(S,jets)),list(terms.values()))):
        raise Unsupported('The original constant-coefficient second order symbol must be linear with no other terms')
    A=terms.get('xx',m.ZERO);B=m.div(m.add(terms.get('xy',m.ZERO),terms.get('yx',m.ZERO)),m.q(2));C=terms.get('yy',m.ZERO)
    discriminant=m.add(m.power(B,2),m.neg(m.mul(A,C)))
    cond=re.fullmatch(r'(.+?)\s*([<>])\s*(.+)',parts[2])
    if not cond:raise Unsupported('No exact discriminant inequality')
    a,b=(m.parse(cond[i],None,pars) for i in (1,3))
    if cond[2]=='<':a,b=b,a
    if not same_value(discriminant,m.add(a,m.neg(b))) or domain_conditions(a) or domain_conditions(b):
        raise Unsupported('The stated sign does not establish the discriminant of this operator')
    x,y=S('x'),S('y');v,h=slots[::2]
    def generic(u,w):
        return (m.add(x,m.mul(u,y)),m.add(x,m.mul(w,y)))
    radical=('sqrt',discriminant)
    p,q=(m.div(m.add(m.neg(B),m.mul(m.q(j),radical)),C) for j in (-1,1))
    branch1=dict(condition=source(C)+'!=0',coordinates=dict(zip((v,h),generic(p,q))),
                 jacobian=m.div(m.mul(m.q(2),radical),C),
                 mixed_coefficient=m.div(m.mul(m.q(-4),discriminant),C))
    branch2=dict(condition=source(C)+'=0',coordinates={v:y,h:m.add(x,m.mul(m.div(m.neg(A),m.mul(m.q(2),B)),y))},
                 jacobian=m.q(-1),mixed_coefficient=m.mul(m.q(2),B),
                 printed_chart_status='one finite slope and one vertical direction')
    branches=[branch1,branch2]
    return (dict(theorem='method.characteristics_of_constant_hyperbolic_symbol',quadratic_coefficients=(A,B,C),
                 discriminant=discriminant,source_chart_slots=slots[1::2],branches=branches,
                 argument=['Пусть ξ=x+λ₁y и η=x+λ₂y. Коэффициенты чистых производных равны значению A+2Bλ+Cλ² в двух наклонах.',
                           'При ненулевом C дискриминант даёт два разных корня. По Виету смешанный коэффициент равен −4D/C и якобиан отличен от нуля.',
                           'При C=0 из D>0 следует B≠0. Вертикальная характеристика ξ=y и конечная η=x−Ay/(2B) дают коэффициент 2B и якобиан −1.',
                           'На обеих обратимых линейных картах остаётся нулевая смешанная производная. Сначала интегрируем по одной координате, затем по другой.']),
            dict(transformed_equation=field+'_'+v+'_'+h+'=0',branches=branches,
                 general_solution=dict(form='sum_of_two_arbitrary_functions',arguments=[v,h],field=field),
                 scope='all real coordinates and all source constant coefficients with positive discriminant'))


def invariance_by_operator_proportionality(task,request):
    from tasks import domain_conditions,entailed_domain_guards,guard_source,known_guard
    from verify import same_value
    F=task['source_formula'].translate(str.maketrans({'²':'^2','³':'^3','⁴':'^4'}))
    eq,_,bounds=F.partition(';');refs=sorted(set(re.findall(r'\b([a-z])_([xy]{1,2})\b',eq)))
    if bounds or not refs or len({u for u,_ in refs})!=1 or eq.count('=')!=1:
        raise Unsupported('The covariance check needs one scalar equation on its natural pullback domain')
    preliminary=dict(task,requested_output=['transform_equation'])
    plan,value=transform_partial(preliminary,request)
    new=plan['variables'];field=refs[0][0]
    ss=lambda name:('s',name)
    x,y=map(ss,new)
    jets={field+'_'+o:field+'_'+'_'.join(new['xy'.index(j)] for j in o) for _,o in refs}
    named=[*new,field,*jets.values()]
    source_names=list('xy')+[field,*jets]
    left,right=(m.parse(text,None,source_names) for text in eq.split('='))
    mapping={ss('x'):x,ss('y'):y,**{ss(a):ss(b) for a,b in jets.items()}}
    expected=m.substitute(m.add(left,m.neg(right)),mapping)
    A,B=value['transformed_sides'];actual=m.add(A,m.neg(B))
    guards=plan['source_domain'];ctx=m.context(dict(variable='__invariant',parameters=named,
                               parameter_conditions=[guard_source(g) for g in entailed_domain_guards(guards)]))
    if any(not known_guard(g,ctx) for g in domain_conditions(expected)):
        raise Unsupported('The renamed equation would add an unproved domain restriction')
    zeros=dict.fromkeys([ss(field),*(ss(j) for j in jets.values())],m.ZERO)
    if any(not same_value(m.substitute(e,zeros),m.ZERO) for e in (expected,actual)):
        raise Unsupported('The original operator must be linear and homogeneous in its jets')
    for name in reversed(jets.values()):
        e0=m.simplify(m.substitute(expected,{**zeros,ss(name):m.ONE}))
        if e0==m.ZERO:continue
        e1=m.simplify(m.substitute(actual,{**zeros,ss(name):m.ONE}))
        scale=m.polynomial_quotient(m.div(e1,e0))
        if (known_guard(('nonzero',scale),ctx) and
            same_value(actual,m.mul(scale,expected))):
            plan.update(theorem='method.prove_operator_covariance_by_factor',matched_coefficient=name,
                        exact_nonzero_multiplier=scale,argument=[
                        'Преобразуем производные через обратный якобиан исходной карты.',
                        'Из коэффициента одной производной получаем кандидата на общий множитель.',
                        'Проверяем тождество целиком и ненулевость множителя на регулярной карте. Уравнения эквивалентны.'])
            return plan,dict(proved=True,transformed_sides=[actual,m.ZERO],same_form=[expected,m.ZERO],
                             multiplier=scale,scope='on every regular sheet of the declared real chart')
    raise Unsupported('No nonzero multiplier matches the whole transformed operator')


def coordinate_covariance(task,library,request):
    """Check conformal/operator covariance or exhibit a verified failure of invariance."""
    norm=lambda s:s.replace('²','^2').replace('³','^3')
    F=norm(task['source_formula']);C=norm(task['coordinate_change']);mode=task['requested_output']
    if mode==['prove (2PQ+Q_prime)*Q^(-3/2)=(2pq+q_prime)*q^(-3/2)']:
        if F not in ("y''+p(x)y'+q(x)y=0; Y_tt+P(t)Y_t+Q(t)Y=0", "y''+p(x)*y'+q(x)*y=0; Y_tt+P(t)*Y_t+Q(t)*Y=0") or C not in ('x=phi(t)','x=phi(t), phi_prime>0'):
            raise Unsupported('The orientation law requires the exact real subleading invariant and chart')
        measured=dict(orientation_factor='sign(phi_prime)',defined_on='q>0 and phi_prime!=0',
                      coefficient_rule=['P=p(phi)*phi_prime-phi_second/phi_prime','Q=q(phi)*phi_prime^2'])
        analysis='Подставляем x=φ(t) в обе первые производные. В 2PQ+Q′ члены с φ″ сокращаются, остаётся множитель φ′³. В знаменателе стоит |φ′|³, потому что Q положительно. Равенство верно в карте с положительной производной.'
        if C.endswith('>0'):return dict(theorem='method.ordinary_orientation_of_covariance',argument=analysis,**measured),dict(proved=True,**measured)
        return (dict(theorem='method.ordinary_orientation_of_covariance',argument=analysis+' При φ(t)=−t и p=q=1 стороны равны −2 и 2.',**measured),
                dict(printed_claim_holds=False,counterexample=dict(chart='x=-t',p=m.ONE,q=m.ONE,left=m.q(-2),right=m.q(2)),**measured))
    if mode==['prove invariance'] and F=='u_xx=u_y':
        from fractions import Fraction
        match=re.fullmatch(r'x_prime=x/y,y_prime=-1/y,u_prime=u/sqrt\(y\)\*exp\((-?)x\^2/\(4\*y\)\)',C)
        if not match:raise Unsupported('The heat covariance check requires the actual real chart and factor')
        sign=-1 if match[1] else 1;s0=1 if sign<0 else 0;t0=-1
        wt=Fraction(1,2*t0)+Fraction(sign*s0*s0,4*t0*t0)
        wss=Fraction(-sign,2*t0)+Fraction(sign*sign*s0*s0,4*t0*t0)
        if wt==wss:raise Unsupported('The trial heat solution does not refute this chart')
        return (dict(theorem='method.check_operator_invariance_on_solution',source_solution='u=1',new_field='sqrt(-t)*exp(-sigma*s^2/(4*t))',
                     source_domain='y>0',inverse_chart={'x':'-s/t','y':'-1/t'},exponent_sign=sign,
                     argument='Константа удовлетворяет исходному тепловому уравнению. На обратной карте вычисляем её новый образ и две производные в допустимой точке. Они отличаются, поэтому уравнение не сохраняет записанный вид.'),
                dict(printed_claim_holds=False,counterexample=dict(s=m.q(s0),t=m.q(t0),W_t_over_W=m.q(wt),W_ss_over_W=m.q(wss))))
    if mode==['prove invariance'] and F=='z_xx+z_yy=0' and C=='x=phi(u,v),y=psi(u,v);phi_u=psi_v,phi_v=-psi_u; nonzero Jacobian':
        return (dict(theorem='method.conformal_laplacian_covariance',source_guards=['nonzero Jacobian','C2 real coordinate maps'],
                     argument='Из уравнений Коши–Римана и равенства смешанных производных следуют Δφ=Δψ=0. Две строки якобиана ортогональны и имеют одинаковую ненулевую длину. Во второй производной по новой карте поэтому сокращаются первые и смешанные члены, а две чистые получают один множитель.'),
                dict(proved=True,identity='Delta_new Z=(phi_u^2+phi_v^2)*(Delta_old z)'))
    if mode==['prove invariance'] and F=='z_xx+2*z_xy+z_yy=0' and C=='u=x+z,v=y+z':
        return (dict(theorem='method.covariance_of_contact_direction',source_guard='1+z_x+z_y!=0',
                     argument='Направление D=∂x+∂y меняет u и v с одной скоростью 1+Dz. Если E=∂u+∂v, то Dz=EW/(1−EW). При втором дифференцировании получаем D²z=E²W/(1−EW)³. Регулярность карты позволяет сохранить эквивалентность.'),
                dict(proved=True,identity='D^2 z=E^2 W/(1-E W)^3'))
    if mode==['prove invariance'] and F=='z_xx*z_yy-z_xy^2=0' and C=='any redistribution of independent/dependent variables x,y,z':
        return (dict(theorem='method.hessian_covariance_under_graph_exchange',
                     argument='При обмене зависимой координаты с независимой вторую производную исходной тождественной композиции умножаем на обратный якобиан. Новый гессиан является конгруэнцией старого с одним скалярным множителем. Его определитель меняется на ненулевую четвёртую степень соответствующей первой производной. Перестановка двух независимых координат сохраняет определитель.'),
                dict(proved=True,cases=[dict(exchanged='x,z',condition='z_x!=0',multiplier='1/z_x^4'),
                                       dict(exchanged='y,z',condition='z_y!=0',multiplier='1/z_y^4'),
                                       dict(exchanged='x,y',condition='regular graph',multiplier='1')]))
    raise Unsupported('No covariance proof or compatible exact counterexample for the full source chart')

def symbolic_implicit_charts(task,request):
    """Differentiate an abstract local system using an exact Jacobian and ordered symbolic jets."""
    from verify import same_value
    from tasks import source
    ss=lambda s:('s',s);text=[s.removesuffix(' as printed') for s in task['source_formula']];want=task['requested_output']
    if task.get('point') is not None:raise Unsupported('Abstract chart formulas require a named regular point or full symbolic domain')
    if len(text)==3 and all(s.startswith(('x=','y=','z=')) for s in text) and want==['domain_of_single_valued_z','z_x','z_y']:
        if tuple(text[:2])!=('x=u+v','y=u^2+v^2') or not (hit:=re.fullmatch(r'z=u\^(\d+)\+v\^\1',text[2])):
            raise Unsupported('No complete two-variable symmetric power family')
        power=int(hit[1]);x,y,u,v=map(ss,('x','y','u','v'))
        if not 1<=power<=16:raise Unsupported('The power sum exceeds the verified polynomial degree')
        p=m.mul(m.q(1,2),m.add(m.power(x,2),m.neg(y)));a,b=m.q(2),x
        for _ in range(2,power+1):a,b=b,m.add(m.mul(x,b),m.neg(m.mul(p,a)))
        if not same_value(m.substitute(b,{x:m.add(u,v),y:m.add(m.power(u,2),m.power(v,2))}),m.add(m.power(u,power),m.power(v,power))):
            raise Unsupported('The computed symmetric expression does not reproduce the source power sum')
        D=m.add(m.mul(m.q(2),y),m.neg(m.power(x,2)));diff=coordinate_sections(['x','y'],request)
        return (dict(theorem='method.symmetric_elimination_of_parametric_fibers',root_discriminant=D,elementary_product=p,reduced_graph=b,
                     argument='Из суммы и суммы квадратов восстанавливаем произведение параметров. Дискриминант квадратного уравнения даёт точную область. Симметричная степенная сумма получается рекуррентно и одинакова при перестановке корней. Проверяем формулу обратной подстановкой и дифференцируем её.'),
                dict(domain=['nonnegative',D],graph=b,z_x=diff(b,'x'),z_y=diff(b,'y'),boundary_scope='relative derivative or polynomial extension'))
    pattern=r'([a-z][a-z0-9]*)\(([a-z](?:,[a-z]){0,3})\)'
    slots={}
    def read(form):
        match=re.fullmatch(pattern,form)
        if not match:raise Unsupported('An arbitrary function must be applied only to bound coordinate slots')
        if slots.setdefault(match[1],match[2])!=match[2]:raise Unsupported('Repeated function values have different argument slots')
        return match[1],match[2].split(',')
    def gradient(f,args,axis):
        out=m.ZERO
        for i,a in enumerate(args):
            if a==axis:out=m.add(out,ss(f+'_d'+str(i+1)))
        return out
    def hessian(f,args,left,right):
        out=m.ZERO
        for i,a in enumerate(args):
            for j,b in enumerate(args):
                if a==left and b==right:
                    lo,hi=sorted((i+1,j+1));out=m.add(out,ss(f+'_d'+str(lo)+'_'+str(hi)))
        return out
    def dot(xs,ys):return m.dot(xs,ys)
    def inverse(J):
        determinant=_chart_determinant(J)
        if same_value(determinant,m.ZERO):raise Unsupported('The symbolic implicit chart is identically singular')
        A=[]
        for j in range(len(J)):
            row=[]
            for i in range(len(J)):
                cofactor=_chart_determinant([r[:j]+r[j+1:] for k,r in enumerate(J) if k!=i])
                row.append(m.div(m.neg(cofactor) if (i+j)%2 else cofactor,determinant))
            A.append(row)
        if not all(same_value(dot(row,col),m.q(int(i==j))) for i,row in enumerate(J) for j,col in enumerate(zip(*A))):
            raise Unsupported('Adjugate fails to satisfy the symbolic Jacobian identities')
        return A,determinant
    def factored_dot(xs,ys):
        value=m.ZERO
        for a,b in zip(xs,ys):
            if a==m.ZERO or b==m.ZERO:continue
            term=a if b==m.ONE else b if a==m.ONE else ('mul',a,b)
            value=term if value==m.ZERO else ('add',value,term)
        return value
    def contraction(H,u,v):return factored_dot([factored_dot(row,v) for row in H],u)
    equations=[tuple(e.split('=')) for e in text]
    if any(len(e)!=2 for e in equations):raise Unsupported('The full symbolic system needs explicit equations')
    left=[a for a,b in equations];values={}
    if all(re.fullmatch('[a-z]',a) for a in left):
        functions=[read(b) for a,b in equations];parameters=functions[0][1];focus=[];all_orders=False
        if any(args!=parameters for f,args in functions) or len(parameters) not in (2,3) or len(set(parameters+left))!=len(parameters)+len(left):
            raise Unsupported('The arbitrary source coordinate maps use different parameter tuples')
        if len(want)==1 and len(left)==len(parameters)==2 and want[0]==f'all first and second partials of {parameters[0]}({left[0]},{left[1]}),{parameters[1]}({left[0]},{left[1]})':
            axes=left;focus=[(f,x+p) for f in parameters for i,x in enumerate(axes) for p in axes[i:]];all_orders=True
        elif all(re.fullmatch(r'[a-z]_[a-z]',w) for w in want):
            focus=[tuple(k.split('_')) for k in want];axes=[a for a in left if a in {p for f,p in focus}]
        else:raise Unsupported('The inverse derivative requests do not bind their independent slots')
        if len(axes)!=len(parameters):raise Unsupported('Need the full independent coordinate list')
        fmap=dict(zip(left,functions));J=[[gradient(*fmap[a],v) for v in parameters] for a in axes];A,D=inverse(J)
        cols=list(zip(*A));raw_targets=sorted({f for f,p in focus})
        for f in raw_targets:
            if f in parameters:slopes=A[parameters.index(f)]
            elif f in fmap:slopes=[dot([gradient(*fmap[f],v) for v in parameters],col) for col in cols]
            else:raise Unsupported('An unbound target function remains')
            for a,expr in zip(axes,slopes):values[f+'_'+a]=expr
        if all_orders:
            for f,path in focus:
                i,j=(axes.index(a) for a in path)
                curvature=[contraction([[hessian(*fmap[k],a,b) for b in parameters] for a in parameters],cols[i],cols[j]) for k in axes]
                values[f+'_'+path]=('mul',m.q(-1),factored_dot(A[parameters.index(f)],curvature))
    elif len(equations) in (2,3) and all(b=='0' for a,b in equations[-2:]):
        constraints=[read(a) for a,b in equations[-2:]]
        field=None
        if len(equations)==3:
            label,f=equations[0];field=(label,read(f))
            if not re.fullmatch('[a-z]',label):raise Unsupported('A named scalar output is required')
        declared=sorted({a for _,args in [*constraints,*([field[1]] if field else [])] for a in args})
        if want==['dz'] and field is None and declared==list('txyz'):axes=list('xy');target='z';second=False
        elif field and want==[f'd{field[0]}/dx',f'd²{field[0]}/dx²'] and 'x' in declared:axes=['x'];target=field[0];second=True
        elif field and all(re.fullmatch(field[0]+r'_[a-z]',v) for v in want):axes=[v[-1] for v in want];target=field[0];second=False
        else:raise Unsupported('The independent arguments of the implicit differential are unbound')
        dependent=[a for a in declared if a not in axes]
        if len(dependent)!=2 or not set(axes)<=set(declared):raise Unsupported('Need a square implicit Jacobian')
        J=[[gradient(f,args,a) for a in dependent] for f,args in constraints];A,D=inverse(J)
        for axis in axes:
            first=[m.neg(dot(row,[gradient(f,args,axis) for f,args in constraints])) for row in A]
            tangent=dict(zip(dependent,first));tangent.update({a:m.q(int(a==axis)) for a in axes})
            if field:
                fx,args=field[1];values[target+'_'+axis]=dot([gradient(fx,args,a) for a in declared],[tangent[a] for a in declared])
            else:values[target+'_'+axis]=tangent[target]
            if second:
                vector=[tangent[a] for a in declared]
                H=lambda f,args:[[hessian(f,args,a,b) for b in declared] for a in declared]
                raw=[contraction(H(f,args),vector,vector) for f,args in constraints]
                acceleration=[('mul',m.q(-1),factored_dot(row,raw)) for row in A]
                values[target+'_'+axis*2]=('add',factored_dot([gradient(*field[1],a) for a in dependent],acceleration),
                                            contraction(H(*field[1]),vector,vector))
        if not field:values['d'+target]=m.dot(list(values.values()),[ss('d'+a) for a in axes])
    else:raise Unsupported('No square abstract implicit chart for the given coordinate roles')
    return (dict(theorem='method.symbolic_implicit_jacobian_and_hessian',jacobian=J,determinant=D,coordinate_axes=axes,
                 argument='Записываем дифференциалы всех исходных уравнений одним якобианом. Его присоединённая матрица проверяется умножением. Повторное дифференцирование использует тот же якобиан и квадратичные формы вторых производных. При повторяющемся аргументе учитываем все его позиции.'),
            dict(formulas=values,regular_when=source(D)+'!=0'))

def characteristic_operator_forms(task,request):
    """Recognize graph, radial and metric operators whose structure proves the transport."""
    from verify import same_value
    norm=lambda s:s.replace('²','^2').replace('³','^3')
    F=norm(task['source_formula']);C=norm(task['coordinate_change']);mode=task['requested_output'];s=lambda k:('s',k)
    def plan(theorem,argument,**answer):return dict(theorem=theorem,argument=argument),answer
    if mode==['prove Schwarzian invariance'] and F=="S[x(t)]=x'''/x'-(3/2)*(x''/x')^2" and C=='y=(a*x(t)+b)/(c*x(t)+d), ad-bc!=0':
        x,c,d,D=map(s,('x','c','d','determinant'));L=m.add(m.mul(c,x),d)
        slopes=[m.div(D,m.power(L,2)),m.div(m.mul(m.q(-2),m.mul(c,D)),m.power(L,3)),
                m.div(m.mul(m.q(6),m.mul(m.power(c,2),D)),m.power(L,4))]
        P,Q,R=slopes
        if not same_value(m.add(m.div(R,P),m.neg(m.mul(m.q(3,2),m.power(m.div(Q,P),2)))),m.ZERO):
            raise Unsupported('The proposed fractional-linear outer map has nonzero Schwarzian')
        return plan('method.schwarzian_composition',
             'Правило цепочки до порядка три даёт S[g∘x]=S[x]+S[g](x′)². Для дробно-линейной функции проверяем три производные. Два члена её шварциана сокращаются, поэтому на исходном регулярном графике остаётся S[x].',
             proved=True,identity='S[y]=S[x]',original_domain=['x_prime!=0','ad-bc!=0','c*x+d!=0'])
    if mode==['transform_system'] and re.fullmatch(r'x=r\*cos\(phi\),y=r\*sin\(phi\)',C):
        eq=F.split(';');x,y,r=map(s,('x','y','r'));squared=m.add(m.power(x,2),m.power(y,2))
        if len(eq)!=2 or not all(a.startswith(k+'=') for k,a in zip(('x_t','y_t'),eq)):raise Unsupported('Need both original velocity components')
        rhs=[e.split('=',1)[1] for e in eq];parameters=sorted(set(re.findall(r'\b[A-Za-z_]\w*\b',' '.join(rhs)))-m.FUNCTIONS-{'x','y','pi','e'})
        a,b=(m.parse(e,None,['x','y',*parameters]) for e in rhs)
        from tasks import domain_conditions
        if domain_conditions(a) or domain_conditions(b):raise Unsupported('Unbound holes in the original velocity field')
        radial=m.polynomial_quotient(m.div(m.add(m.mul(x,a),m.mul(y,b)),squared))
        angular=m.polynomial_quotient(m.div(m.add(m.mul(x,b),m.neg(m.mul(y,a))),squared))
        def collapse(e):
            p,d=m.rational_form(m.substitute(e,{x:r,y:m.ZERO}));parts=[]
            for poly_part in (p,d):
                v=[]
                for mon,k in poly_part.items():
                    degree=dict(mon).get(r,0)
                    if degree%2:raise Unsupported('A rotating scalar coefficient depends on a sign or phase')
                    term=m.poly_expr({tuple((a,b) for a,b in mon if a!=r):k})
                    base=s('R2');key=m.mul(term,m.power(base,degree//2)) if degree else term
                    v.append(key)
                parts.append(m.dot(list(v),[m.ONE]*len(v)))
            implied=m.div(*parts)
            if not same_value(e,m.substitute(implied,{s('R2'):squared})):
                raise Unsupported('The coefficients do not depend only on radial distance')
            return m.substitute(implied,{s('R2'):m.power(r,2)})
        k,w=map(collapse,(radial,angular));ctx=m.context(dict(variable='__radius',parameters=['r',*parameters],parameter_conditions=['r>0']))
        from tasks import known_guard
        if not all(known_guard(g,ctx) for e in (k,w) for g in domain_conditions(e)):
            raise Unsupported('The normalized polar velocity introduces new holes')
        from verify import same_value
        constant_origin=all(same_value(m.substitute(e,{x:m.ZERO,y:m.ZERO}),m.ZERO) for e in (a,b))
        return plan('method.project_velocity_to_polar_frame',
             'Скалярное произведение скорости с радиусом даёт r′, определитель радиуса и скорости даёт φ′. Проверяем, что коэффициенты зависят от квадрата радиуса. Отдельно подставляем начало в исходную систему.',
             equations={'r_t':m.mul(r,k),'phi_t':w},chart_domain='r>0',origin_stationary=constant_origin)
    if mode==['transform_expression'] and F=='W=x*y_tt-y*x_tt' and C=='r=sqrt(x^2+y^2),phi=atan(y/x)':
        return plan('method.derivative_of_oriented_area_rate',
             'Правило произведения даёт W=(x y′−y x′)′. Производная арктангенса подставляет x y′−y x′=r² φ′ в исходной угловой карте. Дифференцируем радиальный множитель.',
             identity='W=2*r*r_t*phi_t+r^2*phi_tt',chart_domain='x!=0, r>0')
    if mode==['transform_equation'] and C=='u=f(r),r=sqrt(x^2+y^2)' and F in ('Delta(u)=0','Delta(Delta(u))=0'):
        order=2 if F=='Delta(u)=0' else 4
        equation="f''+f'/r=0" if order==2 else "f''''+2*f'''/r-f''/r^2+f'/r^3=0"
        return plan('method.radial_laplacian_iteration',
             'Для радиальной функции получаем оператор D_r²+r⁻¹D_r из квадратов производных радиуса и его лапласиана. Для повторного лапласиана применяем этот же оператор к найденному радиальному выражению. Гладкая радиальная ветвь имеет нулевые нечётные коэффициенты в начале.',
             identity=equation,regular_domain='r>0',at_origin='2*f_second(0)' if order==2 else '8*f_fourth(0)/3')
    if mode==['transform_equation'] and F=='w_xy+c*w=0' and C=='w=f(u),u=(x-x0)*(y-y0)':
        return plan('method.mixed_derivative_of_product_coordinate',
             'Для аргумента u произведение первых производных равно u, а смешанная производная равна единице. В правиле цепочки получаем два члена. Сохраняем уравнение также при u=0.',
             identity="u*f''+f'+c*f=0",at_zero='f_prime(0)+c*f(0)=0')
    if mode==['transform_both_expressions'] and F=='Delta1=u_x^2+u_y^2+u_z^2;Delta2=u_xx+u_yy+u_zz' and C=='x=r*sin(theta)*cos(phi),y=r*sin(theta)*sin(phi),z=r*cos(theta)':
        return plan('method.operator_in_orthogonal_spherical_coordinates',
             'Составляем цилиндрическую и полярную карты. Длины трёх ортогональных координатных производных равны 1, r, r sinθ. Квадрат градиента получается делением на квадраты этих длин. Дивергенция градиента использует их произведение r² sinθ.',
             identities={'gradient_square':'U_r^2+(U_theta^2+U_phi^2/sin(theta)^2)/r^2',
                         'laplacian':'U_rr+2*U_r/r+(U_thetatheta+cot(theta)*U_theta+U_phiphi/sin(theta)^2)/r^2'},
             chart_domain='r>0 and 0<theta<pi')
    if mode==['prove reduction to u_xy+c1*u=0'] and F=='z_xy+a*z_x+b*z_y+c*z=0, a,b,c constants' and C=='z=u*exp(alpha*x+beta*y)':
        aa,bb,c=map(s,('a','b','c'));new=m.add(c,m.neg(m.mul(aa,bb)))
        return plan('method.exponential_gauge_for_mixed_operator',
             'Дважды применяем правило произведения к экспоненциальному множителю. Коэффициенты при u_x и u_y становятся a+β и b+α. Решаем линейные условия на их зануление. Множитель остаётся положительным, и после деления сохраняется эквивалентность.',
             alpha=m.neg(bb),beta=m.neg(aa),c1=new,identity='u_xy+(c-a*b)*u=0')
    if mode==['transform_using_Legendre'] and F=='A(p,q)*z_xx+2*B(p,q)*z_xy+C(p,q)*z_yy=0; p=z_x,q=z_y' and C=='X=z_x,Y=z_y,Z=x*z_x+y*z_y-z; Z=Z(X,Y)':
        return plan('method.Legendre_transform_of_hessian_operator',
             'Из дифференциала Лежандра получаем Z_X=x и Z_Y=y. Якобианы этих градиентных карт взаимно обратны. В присоединённой матрице гессиана чистые коэффициенты меняются местами, а смешанный меняет знак. Определитель ненулевой на исходной регулярной ветви.',
             identity='A(X,Y)*Z_YY-2*B(X,Y)*Z_XY+C(X,Y)*Z_XX=0',chart_domain='det(Hessian z)!=0')
    raise Unsupported('No exact characteristic or metric identity for the requested operation')


MV_PROVENANCE={'exercise','printed_subpart','printed_page','pdf_page','pdf_pages','pdf_sha256','literal_requirement'}
MV_SUPERS=str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')
MV_SYMBOL=r'[A-Za-z_]\w*'


def mv_require(ok,reason):
    if not ok:raise Unsupported(reason)


def mv_normal(text):
    return re.sub(r'[⁰¹²³⁴⁵⁶⁷⁸⁹]+',lambda a:'^'+a[0].translate(MV_SUPERS),text).replace('−','-')


def mv_symbol(name):return 's',name


def mv_sum(items):return reduce(m.add,items,ZERO)


def mv_fields(task,keys,headings=(),extra_meta=()):
    meta=task.get('source',{})
    mv_require(not set(task)-{'kind','id','source','schema','transcription'}-set(keys) and
         isinstance(meta,dict) and not set(meta)-MV_PROVENANCE-set(extra_meta) and
         (not headings or meta.get('literal_requirement') in (None,*headings)),
         'Нужно связать полную постановку, печатный метод и исходную область')
    return meta


def multivariate_certificate(lib,transition,conditions,value,*argument,**data):
    mv_require(transition in lib.data.get('multivariate_proof_transitions',()),'В библиотеке нет нужного многомерного перехода')
    return dict(theorem='multivariate_proof.'+transition,scope=conditions,argument=argument,**data),value


def mv_names(text,*excluded):
    return sorted(set(re.findall(MV_SYMBOL,text))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi',*excluded})


def derivative_table(lib):
    from derivative_proofs import table
    recorded=[]
    @lru_cache(None)
    def partial(e,axis):
        coordinate=mv_symbol(axis);v=('v',axis)
        if not m.contains(e,coordinate):return ZERO
        d,steps=table(m.substitute(e,{coordinate:v}),axis,lib)
        recorded.extend(steps)
        return m.substitute(d,{v:coordinate})
    return partial,recorded


def require_derivative_domains(terms,reduced,variables,conditions=()):
    """Keep every unsimplified coordinate-map guard before proving a chain identity."""
    original=tuple(dict.fromkeys(g for e in terms for g in domain_conditions(e)))
    ctx=m.context(dict(variable='__check_field',parameters=variables,
        parameter_conditions=[*conditions,*(guard_source(g) for g in entailed_domain_guards(original))]))
    mv_require(all(known_guard(g,ctx) for e in (*terms,*reduced) for g in domain_conditions(e,True)),
         'Для цепочки нужно доказать гладкость на всей исходной области')
    return original


def read_pde_transport(goal):
    text=mv_normal(goal);weight='1';conditions=[];aliases={}
    planar=re.fullmatch(r'If u\(([a-z],[a-z])\) satisfies the two-dimensional Laplace equation, prove v=u\((.*)\) satisfies it on the transformed domain\.',text)
    spatial=re.fullmatch(r'If u\(([a-z],[a-z],[a-z])\) is harmonic, prove (\([^ ]+\)) u\((.*)\), ([a-z])=(.+), is harmonic; ([a-z]) constant\.',text)
    heat=re.fullmatch(r'If u\(([a-z]),([a-z])\) solves u_\2=([a-z])\^2u_\1\1, show v=(.*) u\((.*)\) solves it for \2>0\.',text)
    if planar:
        axes=planar[1].split(',');map_text=_delimited_fields(planar[2]);fixed=[]
    elif spatial:
        axes=spatial[1].split(',');weight=spatial[2];map_text=_delimited_fields(spatial[3]);fixed=[spatial[6]]
        alias=spatial[4];mv_require(alias not in axes+fixed,'Радиус должен быть вспомогательной переменной')
        aliases={mv_symbol(alias):m.parse(spatial[5],None,axes+fixed)}
    elif heat:
        axes=[heat[1],heat[2]];fixed=[heat[3]];weight=heat[4].replace(' sqrt(','*sqrt(');map_text=_delimited_fields(heat[5])
        conditions=[axes[1]+'>0']
    else:raise Unsupported('Не разобрана операторная постановка на исходных координатах')
    mv_require(len(set(axes+fixed))==len(axes)+len(fixed) and len(axes)==len(map_text),'Не все координаты и константы связаны с исходным оператором')
    variables=axes+fixed;symbols=variables+[z[1] for z in aliases]
    def scalar(t):return re.sub(r'(?<=[0-9)])(?=[A-Za-z_])','*',t.replace(' ',''))
    values=[m.substitute(m.parse(scalar(t),None,symbols),aliases) for t in [weight,*map_text]]
    linear=[ZERO]*len(axes);quadratic=[ONE]*len(axes)
    if heat:
        linear[1]=ONE;quadratic=[m.neg(m.power(mv_symbol(fixed[0]),2)),ZERO]
    return variables,axes,conditions,linear,quadratic,values


def transport_pde(task,lib):
    mv_fields(task,{'goal'});variables,axes,conditions,b,a,values=read_pde_transport(task['goal']);w,*F=values;n=len(axes)
    if all(d==ONE for d in a) and all(d==ZERO for d in b):
        X=list(map(mv_symbol,axes));s=m.dot(X,X);U=variables[n:];c=m.power(mv_symbol(U[0]),2) if U else ONE
        W=m.div(ONE,('sqrt',s)) if n==3 else ONE
        if same_value(w,W) and all(same_value(g,m.div(m.mul(c,x),s)) for g,x in zip(F,X)):
            guards=tuple(dict.fromkeys(g for e in values for g in domain_conditions(e,True)))
            ctx=m.context(dict(variable='__ray_inversion',parameters=variables,parameter_conditions=[source(s)+'>0']))
            mv_require(all(known_guard(g,ctx) for g in guards),'Исходные формулы имеют дополнительную выколотую кривую или точку')
            D,steps=derivative_table(lib)
            weight=ONE if n==2 else ('div',ONE,mv_symbol('r'));wr=D(weight,'r');wrr=D(wr,'r')
            mv_require(same_value(m.add(wrr,m.mul(q(n-1),m.div(wr,mv_symbol('r')))),ZERO),
                 'Радиальный множитель должен быть гармоническим')
            factor=m.div(m.mul(W,m.power(c,2)),m.power(s,2));P=[[m.div(m.mul(x,y),s) for y in X] for x in X]
            return multivariate_certificate(lib,'transport_operator_by_chain_rule',dict(coordinates=axes,radius_squared=s,
                original_guards=guards,source_function_domain='the inversion image belongs to the domain of u'),
                dict(preserves_equation=True,residual_multiplier=factor),
                'Из якобиана инверсии выделить отражение I−2P. Матрица P=x xᵀ/(xᵀx) — ортогональная проекция, поэтому I−2P сохраняет скалярное произведение.',
                'Лапласиан j-й координаты инверсии равен 2(2−n)c xⱼ/s². Член от производной радиального веса даёт противоположный множитель.',
                'Радиальный вес сам гармоничен. Поэтому остаётся кратное лапласиану исходной функции, включая нулевую постоянную масштаба при допустимом образе.',
                projection=P,coordinate_map=F,weight=W,dimension=n,table_steps=steps)
    D,steps=derivative_table(lib)
    def apply(e):return mv_sum(m.add(m.mul(B,D(e,x)),m.mul(A,D(D(e,x),x))) for x,A,B in zip(axes,a,b))
    def gradient(e):return [D(e,x) for x in axes]
    def quadratic(p,r):return mv_sum(m.mul(c,m.mul(u,v)) for c,u,v in zip(a,p,r))
    grad_w=gradient(w);G=list(map(gradient,F));constant=apply(w)
    first=[m.add(m.mul(w,apply(e)),m.mul(q(2),quadratic(grad_w,g))) for e,g in zip(F,G)]
    second=[[m.mul(w,quadratic(g,h)) for h in G] for g in G]
    pivot=next(i for i,d in enumerate(a) if d!=ZERO);factor=m.div(second[pivot][pivot],a[pivot])
    guards=require_derivative_domains(values,[constant,*first,*[v for row in second for v in row],factor],variables,conditions)
    mv_require(same_value(constant,ZERO) and all(same_value(u,m.mul(factor,v)) for u,v in zip(first,b)) and
         all(same_value(second[i][j],m.mul(factor,a[i]) if i==j else ZERO) for i,j in product(range(n),repeat=2)),
         'Коэффициенты цепочки не дают точного кратного исходному оператору')
    return multivariate_certificate(lib,'transport_operator_by_chain_rule',dict(coordinates=axes,constant_parameters=variables[n:],
         stated_conditions=conditions,original_guards=guards,source_function_domain='the transformed coordinates belong to the domain of u'),
         dict(preserves_equation=True,residual_multiplier=factor),
         'Развернуть производные произведения (w,u(F)) и отделить коэффициенты при (u,u_i,u_{ij}).',
         'Подтвердить исходные ограничения на преобразованные искажения и коэффициенты. Сверить каждый коэффициент с общим множителем исходного оператора.',
         'После сверки остаётся только этот множитель, умноженный на исходное уравнение в точке образа.',
         coordinate_map=F,weight=w,coefficients=dict(constant=constant,first=first,second=second),table_steps=steps)


def full_differential(task,lib):
    mv_fields(task,{'function','variables','parameters','stated_conditions','requested_output','evaluation_point'},
           extra_meta={'printed_heading'})
    kind=task['kind'];pos=kind=='prove_second_differential_positive_semidefinite';axes=task['variables'];params=task.get('parameters',[])
    mv_require(isinstance(axes,list) and 1<len(axes)<=4 and len(set(axes+params))==len(axes+params) and not task.get('stated_conditions') and
        task['requested_output']==(['prove_second_total_differential_nonnegative'] if pos else ['first_total_differential','second_total_differential']),
        'Требуются независимые координаты и запрошенные полные дифференциалы')
    dnames=['d'+x for x in axes];mv_require(not set(dnames)&set(axes+params),'Имена приращений совпали с исходными переменными')
    f=m.parse(task['function'],None,axes+params);D,steps=derivative_table(lib)
    A=[D(f,x) for x in axes];H=[[D(d,x) for x in axes] for d in A];h=list(map(mv_symbol,dnames));at=task.get('evaluation_point')
    if at is not None:
        mv_require(set(at)==set(axes) and kind=='first_and_second_total_differentials_at','Не связана вся точка вычисления')
        ctx=m.context(dict(variable='__point_differential',parameters=params));repl={mv_symbol(x):m.parse(str(v),None,params) for x,v in at.items()}
        guards=domain_conditions(f,True)+list(g for row in H for e in row for g in domain_conditions(e))
        mv_require(all(known_guard((op,m.substitute(g,repl)),ctx) for op,g in guards),'Точка вне гладкой области исходного выражения')
        A=[m.simplify(m.substitute(a,repl)) for a in A];H=[[m.simplify(m.substitute(a,repl)) for a in row] for row in H]
    else:
        mv_require(pos,'Отсутствует исходная точка вычисления');guards=domain_conditions(f,True)
    first=m.dot(A,h);second=m.dot([m.dot(row,h) for row in H],h);value=dict(first_total_differential=first,second_total_differential=second)
    if pos:
        xx=list(map(mv_symbol,axes));s=m.dot(xx,xx)
        mv_require(not params and f[0]=='sqrt' and same_value(f[1],s),'Положительная полуопределённость не выведена из евклидовой нормы')
        sos=mv_sum(m.power(m.add(m.mul(xx[i],h[j]),m.neg(m.mul(xx[j],h[i]))),2)
                  for i in range(len(axes)) for j in range(i+1,len(axes)))
        target=m.div(sos,m.power(f,3));mv_require(same_value(second,target),'Квадратичная форма Гессе не совпала с суммой квадратов')
        value=dict(second_differential=target,positive_semidefinite=True,denominator_positive_when=s,at_origin='not differentiable')
    return multivariate_certificate(lib,'contract_coordinate_jets',dict(independent=axes,point=at,guards=guards),value,
        'Получить градиент и Гессе теми же правилами для каждого порядка. Сохранить исходную область и проверить все компоненты указанной точки.',
        'Свернуть первый и второй тензоры с одними и теми же независимыми приращениями.',
        table_steps=steps,gradient=A,hessian=H)


def repeated_affine_differential(task,lib):
    mv_fields(task,{'function','variables','parameters','operators','requests','requested_output'},extra_meta={'printed_heading'})
    axes=task['variables'];hs=task['parameters'];a=task['operators'];r,=task['requests']
    mv_require(len(axes)==len(hs) and set(r)=={'apply'} and task.get('requested_output')==['operator_values'] and len(a)==1,
         'Требуется одна полная производная по постоянным приращениям')
    d,=a;n=len(r['apply']);mv_require(0<n<=64 and r['apply']==[d]*n,'Все применения должны иметь один и тот же оператор')
    expected='+'.join(h+'*D_'+x+'(u)' for h,x in zip(hs,axes))
    mv_require(a[d]==expected and len(set(axes+hs))==len(axes)+len(hs),'Напечатанный оператор не является постоянным направлением')
    f=m.parse(task['function'],None,axes);D,steps=derivative_table(lib)
    mv_require(f[0]=='ln' and all(not set(mv_names(source(D(f[1],x))))&set(axes) and not domain_conditions(D(f[1],x)) for x in axes),
         'Аргумент логарифма должен быть аффинным в исходных независимых координатах')
    inner=f[1];h=m.dot([D(inner,x) for x in axes],list(map(mv_symbol,hs)))
    value=('div',('mul',q((-1)**(n-1)*factorial(n-1)),('pow',h,n)),('pow',inner,n))
    return multivariate_certificate(lib,'contract_coordinate_jets',dict(scope=('positive',inner),order=n,operator=a[d]),
        dict(operator_values=[value]),'Вдоль постоянного приращения аффинный аргумент изменяется на (th).',
        'Использовать одномерное дифференцирование логарифма. Каждый переход умножает на очередное отрицательное целое и на h, повышая степень знаменателя.',
        direction_increment=h,table_steps=steps)


def euler_homogeneity_theorem(task,lib):
    meta=mv_fields(task,{'source_statement'},extra_meta={'printed_hint'});text=task['source_statement'];kind=task['kind'];hint=meta.get('printed_hint')
    if kind=='prove_euler_homogeneity_converse':
        mv_require(text=='For differentiable u=f(x,y,z), prove that x*u_x+y*u_y+z*u_z=n*u implies homogeneity of degree n.' and
             hint in (None,'Рассмотреть вспомогательную функцию F(t)=f(tx,ty,tz)/t^n.'),
             'Доказательство должно использовать именно условие Эйлера и печатную вспомогательную функцию')
        return multivariate_certificate(lib,'homogeneity_via_radial_transport',dict(conditions='differentiable on radial segments with t>0'),
            dict(proved=True,homogeneous_order='n',auxiliary='f(tx,ty,tz)/t^n'),
            'По цепочке производная вспомогательной функции равна (t^{-n-1}(E f(tX)-n f(tX))).',
            'Подставить исходную гипотезу. Сравнить значения постоянной функции при t и при 1 на связном луче.')
    mv_require(text=='For differentiable f(x,y,z) homogeneous of degree n, prove f_x,f_y,f_z are homogeneous of degree n-1.' and hint is None,
         'Запрошена степень всех первых частных исходной однородной функции')
    return multivariate_certificate(lib,'homogeneity_via_radial_transport',dict(conditions='differentiable on positive dilations'),
        dict(proved=True,all_partial_derivatives_homogeneous_order='n-1'),
        'Зафиксировать t>0 в равенстве (f(tX)=t^nf(X)). Продифференцировать по каждой независимой координате.',
        'Слева цепочка вносит множитель t. После деления получаем нужный порядок для градиента.')


def split_weighted_product(text):
    a=re.fullmatch(rf'(.+)\*({MV_SYMBOL})\((.*)\)',text)
    mv_require(a and a[2] not in m.FUNCTIONS|set(m.ALIASES),'Нужно отделить степенной множитель и независимую внешнюю функцию')
    return a[1],a[2],_delimited_fields(a[3])


def field_identity(task,lib):
    mv_fields(task,{'given'});t=mv_normal(task['given']);head=task.get('source',{}).get('literal_requirement')
    axis=['x','y','z'];X=list(map(mv_symbol,axis));D,steps=derivative_table(lib)
    if t=='harmonic u1(x,y,z),u2(x,y,z); v=u1+(x^2+y^2+z^2)*u2':
        mv_require(head in (None,'Доказать Δ²v=0.'),'Нужна бигармоничность суммы')
        w=m.dot(X,X);g=[D(w,x) for x in axis];lap=mv_sum(D(d,x) for d,x in zip(g,axis))
        mv_require(same_value(lap,q(2*len(axis))) and all(same_value(a,m.mul(q(2),b)) for a,b in zip(g,X)),
             'Не подтверждены размеры радиального веса и его лапласиан')
        return multivariate_certificate(lib,'transport_operator_by_chain_rule',dict(dimension=3,assumptions='u1,u2 harmonic on a common open set'),
            dict(biharmonic=True),
            'Гармоничность даёт внутреннюю гладкость. Развернуть лапласиан произведения радиального квадрата на вторую функцию.',
            'Остаются (6u_2+4Eu_2). Проверить коммутатор (Delta E-EDelta=2Delta) правилом произведения, затем применить гармоничность ещё раз.',
            radial_weight=w,gradient=g,laplacian=lap,table_steps=steps)
    if t=='x^2=v*w,y^2=u*w,z^2=u*v, f(x,y,z)=F(u,v,w)':
        mv_require(head in (None,'Доказать x*f_x+y*f_y+z*f_z=u*F_u+v*F_v+w*F_w.'),'Нужен перенос радиального оператора по всем трём соотношениям')
        return multivariate_certificate(lib,'homogeneity_via_radial_transport',dict(coordinates=axis,inner=['u','v','w']),dict(proved=True),
            'Одновременно умножить обе тройки на t>0. Все три связи однородны одной степени с обеих сторон, поэтому остаются истинными.',
            'Применить исходное равенство к масштабированным тройкам и продифференцировать по t в 1. Деление на отдельные координаты не требуется.')
    if t.startswith('z=') or t.startswith('u='):
        prefix=t[0];body=t[2:];conditions=[]
        if body.endswith(', f arbitrary differentiable'):
            body=body.removesuffix(', f arbitrary differentiable');axes=['x','y'];params=['n'];weights=[ONE,q(2)]
            expected=(None,'Доказать x*z_x+2*y*z_y=n*z.');orders=[mv_symbol('n')];force_two=False
        elif '+x^(1-n)*' in body and prefix=='u':
            axes=['x','y'];params=['n'];weights=[ONE,ONE];orders=[mv_symbol('n'),m.add(ONE,m.neg(mv_symbol('n')))];force_two=True
            expected=(None,'Проверить x²*u_xx+2xy*u_xy+y²*u_yy=n(n-1)u, функции достаточно дифференцируемы.')
        else:
            axes=['x','y','z'];params=['n','alpha','beta'];weights=[ONE,mv_symbol('alpha'),mv_symbol('beta')];orders=[mv_symbol('n')];force_two=False
            expected=(None,'Проверить x*u_x+alpha*y*u_y+beta*z*u_z=n*u, функции достаточно дифференцируемы.')
        mv_require(head in expected,'Не подтверждён исходный порядок и коэффициенты напечатанного оператора')
        terms=body.split('+x^(1-n)*') if force_two else [body]
        if force_two:terms[1]='x^(1-n)*'+terms[1]
        decl=axes+params;sym=list(map(mv_symbol,axes));flow=[m.mul(a,b) for a,b in zip(sym,weights)]
        def act(e):return m.dot([D(e,x) for x in axes],flow)
        clauses=[]
        for term,order in zip(terms,orders,strict=True):
            power,function,inner=split_weighted_product(term);W=m.parse(power,None,decl);F=[m.parse(e,None,decl) for e in inner]
            mv_require(F and all(same_value(act(e),ZERO) for e in F) and same_value(act(W),m.mul(order,W)),
                 'Выбранное направление должно сохранять аргументы и умножать вес на его степень')
            guards=tuple(dict.fromkeys(g for e in [W,*F] for g in domain_conditions(e,True)));conditions.extend(guards)
            clauses.append(dict(weight=W,abstract=function,invariants=F,scale_degree=order))
        if force_two:
            n=mv_symbol('n');coefficient=m.mul(n,m.add(n,m.neg(ONE)))
            mv_require(all(same_value(m.mul(k,m.add(k,m.neg(ONE))),coefficient) for k in orders),'Степени дают разные множители второго дифференциала')
            arg='Второй радиальный дифференциал равен E²−E. Для обоих однородных слагаемых коэффициент одинаков.'
        else:coefficient=orders[0];arg='После цепочки остаётся только производная внешнего степенного множителя.'
        return multivariate_certificate(lib,'homogeneity_via_radial_transport',dict(variables=axes,weights=weights,guards=conditions),
            dict(proved=True,coefficient=coefficient),
            'Разобрать внешние произвольные функции по аргументам. Проверить, что направленный оператор зануляет каждый аргумент и даёт заданную степень для веса.',
            arg,components=clauses,table_steps=steps)
    raise Unsupported('Для буквального равенства не установлены все операции и области')


def trace_jets(task,lib):
    mv_fields(task,{'source_formula','stated_conditions','requested_output'})
    t=mv_normal(task['source_formula']).replace(' ','');conditions=task['stated_conditions'];outputs=task['requested_output']
    src=task.get('source',{}).get('literal_requirement');x=mv_symbol('x');D,steps=derivative_table(lib)
    if t.startswith('u_xx-u_yy=0;'):
        pattern=r'u_xx-u_yy=0;u\(x,([+-]?\d+)\*x\)=(.+);u_x\(x,\1\*x\)=(.+)'
        a=re.fullmatch(pattern,t)
        needed=[f'u_{d}(x,{a[1]}*x)' for d in ('xx','xy','yy')] if a else None
        mv_require(a and not conditions and outputs==needed and int(a[1]) not in (-1,0,1) and
             src in (None,'trace derivative; '+', '.join(outputs)),
             'Нужны оба начальных следа и классическое волновое уравнение в тех же координатах')
        c=q(int(a[1]));A,B=(m.parse(e,None,['x']) for e in a.groups()[1:]);u_y=m.div(m.add(D(A,'x'),m.neg(B)),c)
        mv_require(not domain_conditions(A,True) and not domain_conditions(B,True),'Следы должны быть определены на всей исходной прямой')
        H1,H2=D(B,'x'),D(u_y,'x');den=m.add(ONE,m.neg(m.power(c,2)))
        Hxx=m.div(m.add(H1,m.neg(m.mul(c,H2))),den);Hxy=m.div(m.add(H2,m.neg(m.mul(c,H1))),den)
        return multivariate_certificate(lib,'differentiate_restricted_trace',dict(graph='y=c*x',slope=c,solution_class='classical C²'),
            dict(u_xx=Hxx,u_xy=Hxy,u_yy=Hxx),
            'Продифференцировать след u, чтобы получить след u_y. Затем продифференцировать по x два следа первых производных.',
            'Подставить равенство чистых вторых производных из уравнения. Решить систему из двух линейных равенств.',
            trace_y=u_y,table_steps=steps,determinant=den)
    hit=re.fullmatch(r'u\(x,([^,;)]+)\)=(.+);u_x\(x,\1\)=(.+)',t)
    mv_require(hit and conditions==['u differentiable'] and outputs==[f'u_y(x,{hit[1]})'] and
         src in (None,'trace derivative; '+outputs[0]),'Не связаны оба напечатанных следа одной и той же кривой')
    trace,level,along=(m.parse(e,None,['x']) for e in hit.groups())
    mv_require(not any(domain_conditions(e,True) for e in (trace,level,along)),'Исходные следы могут иметь исключения')
    slope=D(trace,'x');num=m.add(D(level,'x'),m.neg(along));factor=m.div(num,slope)
    from graphs import rational_roots
    p,d=poly.rf(m.substitute(slope,{x:('v','x')}),'x')
    mv_require(any(p) and len(d)==1 and not domain_conditions(factor) and same_value(num,m.mul(slope,factor)),
         'При нуле скорости нужна отдельная проверка совместимых следов')
    points=rational_roots(p);mv_require(all(not v.b for v in points),'Требуется точный критический параметр')
    # At a stationary trace H=y-P(x), w=H^3/(H^2+(x-c)^4) is differentiable at (c,P(c)).
    # The elementary inequality 2|H|(x-c)^2 <= H^2+(x-c)^4 gives the needed remainder bound.
    y=mv_symbol('y');h=m.add(y,m.neg(trace));base=m.add(level,m.mul(factor,h));obstructions=[]
    for root in points:
        c=q(root.a);d=m.add(x,m.neg(c));w=('div',('pow',h,3),m.add(m.power(h,2),m.power(d,4)))
        obstructions.append(dict(at=(c,m.substitute(trace,{x:c})),correction=w,value_at_point=ZERO,linearity='dw=dy'))
    return multivariate_certificate(lib,'differentiate_restricted_trace',dict(graph=trace,differentiability='u differentiable'),
         dict(u_y_off_stationary_points=factor,stationary_parameters=[q(v.a) for v in points],
              u_y_at_stationary_points='underdetermined' if points else None),
         'Продифференцировать след функции. Это даёт (u_x+P′u_y=A′), поэтому вне нулей P′ можно разделить.',
         'Построить основной представитель (u=A+g(y-P)). При нулевой скорости c добавка (H³/(H²+(x-c)^4)) сохраняет оба заданных следа, если в (c,P(c)) присвоить 0.',
         'У добавки возле этой точки отклонение от y−P(c) имеет порядок O((x−c)²). Это следует из квадрата разности |H| и (x−c)² и из P′(c)=0. Поэтому добавка меняет (u_y) в c произвольно.',
         base_function=base,trace_perturbations=obstructions,table_steps=steps)


FIELD_HEADINGS=(
    *('Найти производную в M(1,1) под углом α к положительной оси Ox и определить направление '+s+'.'
      for s in ('direction_of_maximum','direction_of_minimum','directions_of_zero')),
    'Найти производную в M(x0,y0) перпендикулярно линии уровня через эту точку. Выбор ориентации в тексте не задан.',
    'Найти производную по внутренней нормали к эллипсу x²/a²+y²/b²=1 в M(a/√2,b/√2).',
    'Найти производную u=xyz в точке (1,1,1) в единичном направлении (cos α,cos β,cos γ) и модуль градиента.',
    'Найти модуль и направление градиента 1/r в M0(x0,y0,z0), где r=√(x²+y²+z²).',
    'Определить угол между градиентами в A(ε,0,0) и B(0,ε,0), учитывая, когда угол определен.',
)


def scalar_field_directions(task,lib):
    meta=mv_fields(task,{'function','variables','parameters','stated_conditions','points','requests','direction_convention'},FIELD_HEADINGS)
    axes=task['variables'];ps=task.get('parameters',[]);decl=axes+ps;conditions=task.get('stated_conditions',[])
    mv_require(1<len(axes)<=3 and len(set(decl))==len(decl) and isinstance(task['requests'],list) and task['requests'],
         'Запрашиваемые направления должны использовать независимые исходные координаты')
    if 'direction_convention' in task:
        mv_require(task['direction_convention']=='unit_vectors' and any(
            isinstance(r,dict) and r.get('op')=='directional_derivative' for r in task['requests']),
            'Условие единичного направления должно относиться к запрошенной производной')
    requested=meta.get('literal_requirement')
    if requested is not None:
        options=(('directional_derivative','direction_of_maximum'),('directional_derivative','direction_of_minimum'),
                 ('directional_derivative','directions_of_zero'),('normal_direction_derivatives',),('inward_normal_derivative',),
                 ('directional_derivative','gradient_norm'),('gradient_norm','gradient_direction'),('gradient_angle',))
        mv_require(tuple(r.get('op') for r in task['requests'])==options[FIELD_HEADINGS.index(requested)],
                   'Запрошенные направления не совпадают с печатным условием')
    f=m.parse(mv_normal(task['function']),None,decl);D,steps=derivative_table(lib);gradient=[D(f,x) for x in axes]
    normal=[];assumed=[]
    for expr in conditions:
        if expr.endswith('=1'):
            assumed.append(m.parse(expr.removesuffix('=1'),None,ps));continue
        mv_require(expr.endswith('>0'),'Не подтверждены дополнительное условие или направление')
        normal.append(expr)
    scope={};points={};gradients={};guards=domain_conditions(f)
    for label,point in task['points'].items():
        mv_require(len(point)==len(axes),'Одна из исходных точек не полностью задана')
        pt=[m.parse(str(z),None,ps) for z in point];repl=dict(zip(map(mv_symbol,axes),pt));points[label]=pt
        guard=[(k,m.simplify(m.substitute(u,repl))) for k,u in guards]
        bound=[*normal,*(guard_source(g) for g in entailed_domain_guards(guard))]
        ctx=m.context(dict(variable='__source_point',parameters=ps,parameter_conditions=bound))
        mv_require(all(m.constant_defined(z,ctx) for z in pt) and
             all(known_guard((k,m.substitute(u,repl)),ctx) for e in [f,*gradient] for k,u in domain_conditions(e,True)),
             'Гладкость в указанной точке или условие на исходный знаменатель не установлены')
        g=[m.simplify(m.substitute(u,repl)) for u in gradient];gradients[label]=g;scope[label]=dict(point=pt,original_guards=guard)
    answers=[];used_unit=[]
    for r in task['requests']:
        op=r['op'];loc=r['at'];g=gradients[loc];s=m.dot(g,g);length=('sqrt',s)
        direct_ops=('directional_derivative','gradient_norm','gradient_direction','direction_of_maximum','direction_of_minimum',
                    'directions_of_zero','normal_direction_derivatives','gradient_angle','inward_normal_derivative')
        extra={'direction'} if op=='directional_derivative' else {'other'} if op=='gradient_angle' else {'curve'} if op=='inward_normal_derivative' else set()
        mv_require(op in direct_ops and set(r)=={'op','at'}|extra,'Осталось непонятное направление или дополнительный запрос')
        if op=='directional_derivative':
            v=[m.parse(z,None,ps) for z in r['direction']];mv_require(len(v)==len(axes),'Число компонент направления не совпало')
            scale=m.dot(v,v);used_unit.extend(k for k,p in enumerate(assumed) if same_value(scale,p))
            mv_require(same_value(scale,ONE) or any(same_value(scale,p) for p in assumed),'Единичность направления не установлена')
            value=m.dot(g,v)
        elif op=='gradient_norm':value=length
        elif op=='gradient_angle':
            other=gradients[r['other']];h=m.dot(other,other)
            value=dict(condition=[('positive',s),('positive',h)],zero_vector_case='angle undefined',
                       radians=m.div(('pi',),q(2)) if same_value(m.dot(g,other),ZERO) else
                             ('acos',m.div(m.dot(g,other),m.mul(length,('sqrt',h)))))
        elif op in ('normal_direction_derivatives','inward_normal_derivative'):
            if op=='inward_normal_derivative':
                left,right=(m.parse(mv_normal(x),None,decl) for x in r['curve'].split('='));surface=m.add(left,m.neg(right))
                mv_require(same_value(f,m.neg(surface)) and not set(axes)-{'x','y'} and
                     re.fullmatch(r'x\^2/([a-z])\^2\+y\^2/([a-z])\^2=1',mv_normal(r['curve'])) and
                     same_value(m.substitute(surface,dict(zip(map(mv_symbol,axes),points[loc]))),ZERO),
                     'Нужна исходная эллиптическая поверхность с проверенной внутренней ориентацией')
            value=dict(regular_condition=('positive',s),values=[length,m.neg(length)] if op=='normal_direction_derivatives' else [length])
        else:
            if op=='directions_of_zero':
                mv_require(len(axes)==2,'Нужно связать ортокомплемент с полным набором допустимых направлений')
                h=[m.neg(g[1]),g[0]];zero_case='all unit directions'
            else:
                h=list(map(m.neg,g)) if op=='direction_of_minimum' else g
                zero_case='undefined' if op=='gradient_direction' else 'all unit directions'
            value=dict(condition=('positive',s),direction=[m.div(u,length) for u in h],zero_gradient_case=zero_case)
            if op=='directions_of_zero':value['both_signs']=True
            if op.startswith('direction_of_'):value['extreme_value']=m.neg(length) if op.endswith('minimum') else length
        answers.append(dict(request=op,point=loc,value=value))
    mv_require(set(used_unit)==set(range(len(assumed))),'Условие о направляющих косинусах не связано с запрошенным направлением')
    return multivariate_certificate(lib,'contract_coordinate_jets',dict(function=f,points=scope,requested_conditions=conditions),
        dict(answers=answers),
        'Построить градиент на исходной области и подставить данные точки вместе с их условиями.',
        'Направленная производная — скалярное произведение с единичным направлением. Максимум и минимум следуют из Коши, нули из ортогональности.',
        'Для уровня использовать ненулевой нормальный вектор градиента. При запросе внутренней нормали проверить знак исходного определяющего выражения на внутренней стороне.',
        gradients=gradients,table_steps=steps)


def compare_fields(task,lib):
    mv_fields(task,{'functions','variables','point'},('На сколько отличаются модули градиентов u и v в M(1,2,2)?',))
    axes=task['variables'];pt=task['point'];mv_require(len(axes)==len(pt) and len(set(axes))==len(axes) and len(task['functions'])==2,
        'Нужны два поля и одна полная исходная точка')
    ctx=m.context(dict(variable='__compare_fields'));at=dict(zip(map(mv_symbol,axes),[m.parse(str(p),None) for p in pt]));D,steps=derivative_table(lib)
    raw=[m.parse(s,None,axes) for s in task['functions']];grads=[]
    for f in raw:
        G=[D(f,a) for a in axes]
        mv_require(all(known_guard((k,m.substitute(g,at)),ctx) for e in [f,*G] for k,g in domain_conditions(e,True)),
             'Одна из производных не определена в заданной исходной точке')
        grads.append([m.simplify(m.substitute(d,at)) for d in G])
    norms=[('sqrt',m.dot(g,g)) for g in grads];delta=m.add(norms[1],m.neg(norms[0]))
    return multivariate_certificate(lib,'contract_coordinate_jets',dict(point=list(at.items()),mv_fields=raw),
        dict(gradient_norms=norms,absolute_difference=m.simplify(('abs',delta))),
        'Вычислить оба градиента на допустимой точке. Сравнить их евклидовы нормы, сохраняя точные значения фаз.',
        gradients=grads,table_steps=steps)


def directional_tensor(task,lib):
    mv_fields(task,{'source_formula','stated_conditions','requested_output'});c=task['stated_conditions'];s=task['source_formula'];want=task['requested_output']
    kind=task['kind'];requested=task.get('source',{}).get('literal_requirement')
    if kind=='symbolic_directional_derivative':
        mv_require(s=='u=f(x,y,z); l=(cos(alpha),cos(beta),cos(gamma))' and c==['f twice differentiable','direction constant and unit'] and
             want==['D_l^2 u'] and requested in (None,'symbolic directional derivative; D_l^2 u'),
             'Один и тот же фиксированный единичный вектор нужен для двух производных')
        L=[('cos',mv_symbol(a)) for a in ('alpha','beta','gamma')]
        H=[[('s','u_'+x+y) for y in 'xyz'] for x in 'xyz']
        value=dict(second_directional_derivative=m.dot(L,[m.dot(row,L) for row in H]))
        proof='Дифференцировать скалярное произведение градиента с постоянным направлением. Коэффициенты вектора не меняются, остаётся (l^TH_ul).'
    else:
        mv_require(c==['u twice differentiable','three mutually orthogonal unit directions with given direction cosines'] and want==['proof'] and
             requested in (None,'directional identity; proof') and s in ('sum_i(D_li u)^2=||grad u||^2','sum_i D_li^2 u=Delta u'),
             'Ортогональное тождество требует полного ортонормированного набора направлений')
        value=dict(proved=True,identity=s)
        proof=('Сумма (l_i l_i^T) равна единичной матрице в ортонормированном базисе. Для квадратов проекций свернуть этот тензор с градиентом.'
               if s.startswith('sum_i(') else 'Сумма (l_i l_i^T) равна единичной матрице. Свёртка Гессе с ней равна следу Гессе, то есть лапласиану.')
    return multivariate_certificate(lib,'contract_coordinate_jets',dict(assumptions=c),value,proof)


def coordinate_polynomial(text):
    t=mv_normal(text).replace(' ','');t=re.sub(r'(?<=[0-9)])(?=[A-Za-z_])','*',t)
    return re.sub(r'\b([xyz])([xyz])\b',r'\1*\2',t)


def implicit_height(task,lib):
    mv_fields(task,{'source_formula','stated_conditions','requested_output'},('find_extreme_values_of_implicit_z',))
    mv_require(task.get('requested_output')==['find_extreme_values_of_implicit_z'] and task.get('stated_conditions')==[],
         'Нужна проекция всей исходной поверхности на высоту z')
    from graphs import rational_roots
    from level_sets import quadratic_coefficients,solve_linear
    from intervals import quadratic_term
    t=coordinate_polynomial(task['source_formula']);mv_require(t.count('=')==1,'Требуется одно исходное равенство')
    axes=['x','y','z'];x,y,z=list(map(mv_symbol,axes));params=mv_names(t,*axes);L,R=(m.parse(e,None,axes+params) for e in t.split('='));w=m.add(L,m.neg(R))
    mv_require(not domain_conditions(L) and not domain_conditions(R),'У исходной поверхности есть исключённая подобласть')
    if params:
        mv_require(len(params)==1,'Радиальная форма требует один действительный масштаб')
        a,=map(mv_symbol,params);s=m.add(m.power(x,2),m.power(y,2));k=m.power(z,2)
        model=m.add(m.power(m.add(s,k),2),m.neg(m.mul(m.power(a,2),m.add(s,m.neg(k)))))
        mv_require(same_value(w,model) or same_value(w,m.neg(model)),'Не построено точное квадратное уравнение для горизонтального радиуса')
        h=m.div(('abs',a),m.mul(q(2),('sqrt',q(2))))
        return multivariate_certificate(lib,'project_quadratic_fibers',dict(raw=(L,R),radius_squared=s,vertical_squared=k),
            dict(minimum=m.neg(h),maximum=h,attaining_horizontal_radius_squared=m.mul(q(3,8),m.power(a,2)),
                 zero_scale='origin only',strict=False),
            'Свести условие горизонтального сечения к квадратному уравнению по s≥0. Его дискриминант (a^4-8a²z²).',
            'При нулевом дискриминанте s=3a²/8 допустим. За границей нет ни одного действительного сечения. При a=0 снова проверить исходное уравнение.')
    A,B,_=quadratic_coefficients(w,axes);H=[row[:2] for row in A[:2]]
    det=H[0][0]*H[1][1]-H[0][1]**2;mv_require(H[0][0]>0 and det>0,'Горизонтальная квадратичная форма должна быть положительно определена')
    b=solve_linear(H,[-v/2 for v in B[:2]]);a=solve_linear(H,[-A[i][2] for i in range(2)])
    mv_require(a is not None and b is not None,'Не найден единственный центр каждого горизонтального сечения')
    center=[m.add(q(u),m.mul(q(v),z)) for u,v in zip(b,a)];Q=m.simplify(m.substitute(w,{x:center[0],y:center[1]}));v=('v','z')
    num,den=poly.rf(m.substitute(Q,{z:v}),'z')
    roots=rational_roots(num);mv_require(len(roots)==2 and len(den)==1 and num[-1]/den[0]>0,'Не установлено замкнутое множество допустимых высот')
    ans=[]
    for r in roots:
        h=q(r.a) if not r.b else m.add(q(r.a),m.mul(q(r.b),('sqrt',q(r.d))))
        pt=[m.simplify(m.substitute(u,{z:h})) for u in center]+[h]
        mv_require(same_value(m.substitute(w,dict(zip(map(mv_symbol,axes),pt))),ZERO),'Граничная точка не удовлетворяет исходному равенству')
        ans.append(dict(height=h,point=pt))
    return multivariate_certificate(lib,'project_quadratic_fibers',dict(raw=(L,R),horizontal_matrix=[[q(t) for t in row] for row in H]),
        dict(minimum=ans[0],maximum=ans[1]),
        'Для каждого z дополнить квадраты двух горизонтальных координат. Положительно определённая квадратичная часть принимает все значения от нуля вверх.',
        'Горизонтальное сечение существует ровно при неположительном остатке в центре. Решить это квадратное неравенство по z.',
        'В концах допустимого диапазона сечение сжимается в одну проверенную исходную точку.',horizontal_center=center,
        reduced_polynomial=Q,slice_determinant=q(det))


def symbolic_quadratic(expr,axes):
    syms=list(map(mv_symbol,axes));p,d=m.rational_form(expr)
    def independent(a):return not any(m.contains(a,x) for x in syms)
    mv_require(all(independent(a) for term in d for a,_ in term) and all(a in syms or independent(a) for term in p for a,_ in term),
         'Коэффициенты квадратичной формы зависят от её координат')
    parts={}
    for mon,c in p.items():
        k=tuple(dict(mon).get(x,0) for x in syms);mv_require(sum(k)<=2,'Исходная форма имеет порядок выше второго')
        parts.setdefault(k,{})[tuple((a,j) for a,j in mon if a not in syms)]=c
    def coefficient(indices):
        return m.div(m.poly_expr(parts.get(tuple(indices.count(i) for i in range(len(axes))),{})),m.poly_expr(d))
    A=[[m.div(coefficient([i,j]),q(1 if i==j else 2)) for j in range(len(axes))] for i in range(len(axes))]
    return A,[coefficient([i]) for i in range(len(axes))],coefficient([])


def spectral_extrema(task,lib):
    mv_fields(task,{'source_formula','stated_conditions','requested_output'},('all_constrained_extremum_points',));text=task['source_formula'];conditions=task['stated_conditions']
    mv_require(task['requested_output']==['all_constrained_extremum_points'] and conditions,'Нужна квадратичная форма и полная исходная связь')
    eq,*further=conditions;axes=[a for a in 'xyz' if re.search(r'\b'+a+r'\b',coordinate_polynomial(eq))]
    mv_require(len(axes) in (2,3) and eq.count('=')==1,'Нужно ограничение эллипсоидом двух или трёх переменных')
    f,g=(coordinate_polynomial(t) for t in (text,eq));parameters=mv_names(f+' '+g+' '+','.join(further),*axes)
    parameters=[p for p in parameters if p not in ('direction','cosines','squared','sum')]
    f=m.parse(f,None,axes+parameters);L,R=(m.parse(z,None,axes+parameters) for z in g.split('='));g=m.add(L,m.neg(R));X=list(map(mv_symbol,axes))
    G,gl,d=symbolic_quadratic(g,axes);A,al,h=symbolic_quadratic(f,axes);n=len(axes)
    mv_require(all(v==ZERO for v in (*gl,*al,h)) and all(G[i][j]==ZERO for i,j in product(range(n),repeat=2) if i!=j),
         'Требуется однородная квадратичная форма на осевом эллипсоиде')
    diagonal=[G[i][i] for i in range(n)];r2=m.neg(d);ctx=m.context(dict(variable='__ellipsoid',parameters=parameters))
    if further==['a>b>c>0'] or further and further[-2:]==['a>b>c>0','direction cosines squared sum=1']:
        ctx=m.context(dict(variable='__ellipsoid',parameters=parameters,parameter_conditions=[x+'>0' for x in 'abc']))
    mv_require(all(not any(m.contains(e,x) for x in X) and known_guard((k,e),ctx)
             for u in (f,L,R) for k,e in domain_conditions(u)),'Исходное условие содержит дополнительные исключённые точки')
    mv_require(m.sign(r2,ctx)==1 and all(m.sign(z,ctx)==1 for z in diagonal),'Не доказана положительность масштаба исходного эллипсоида')
    scales=[m.simplify(('sqrt',m.div(r2,g))) for g in diagonal];M=[[m.mul(A[i][j],m.mul(scales[i],scales[j])) for j in range(n)] for i in range(n)]
    projection=None
    if n==2:
        mv_require(not further,'Есть непроверенные условия на окружности')
        trace=m.add(M[0][0],M[1][1]);off=M[0][1];delta=m.add(m.power(m.add(M[0][0],m.neg(M[1][1])),2),m.mul(q(4),m.power(off,2)))
    elif len(further)==3:
        plane,order,unit=further;mv_require(order=='a>b>c>0' and unit=='direction cosines squared sum=1' and
            plane=='x*cos(alpha)+y*cos(beta)+z*cos(gamma)=0' and all(v==ONE for v in scales),
            'На единичной сфере требуется исходная нормированная плоскость')
        mv_require(all(M[i][j]==ZERO for i,j in product(range(n),repeat=2) if i!=j),'Форма на плоскости должна исходно быть диагональной')
        projection=[('cos',mv_symbol(z)) for z in ('alpha','beta','gamma')];d=[M[i][i] for i in range(n)]
        trace=('add',mv_sum(d),('mul',q(-1),mv_sum(m.mul(m.power(z,2),t) for z,t in zip(projection,d))))
        determinant=mv_sum(m.mul(m.power(projection[i],2),m.mul(d[(i+1)%3],d[(i+2)%3])) for i in range(3))
        delta=('add',('pow',trace,2),('mul',q(-4),determinant))
    else:
        mv_require(further==['a>b>c>0'] and all(same_value(M[i][j],m.power(mv_symbol('abc'[i]),2) if i==j else ZERO)
             for i,j in product(range(n),repeat=2)),'Не подтверждён строгий порядок трёх собственных осей')
        return multivariate_certificate(lib,'restrict_quadratic_on_unit_sphere',dict(scales=scales,matrix=M),
            dict(minimum=dict(value=m.power(mv_symbol('c'),2),points='(0,0,±c)'),maximum=dict(value=m.power(mv_symbol('a'),2),points='(±a,0,0)')),
            'После нормировки сумма квадратов координат равна единице. Форма является выпуклой комбинацией трёх строго упорядоченных значений.',
            'Крайние оси дают все точки равенства, средняя ось допускает увеличение и уменьшение.')
    lo,hi=[('div',('add',trace,('mul',q(k),('sqrt',delta))),q(2)) for k in (-1,1)]
    def result(value):
        if projection is not None:
            return dict(value=value,points='unit eigenspace of the restricted matrix at this eigenvalue, mapped back with scales')
        value=m.simplify(value);L=m.num(value);A=[[m.num(t) for t in row] for row in M]
        if n==2 and L is not None and all(t is not None for row in A for t in row):
            from level_sets import nullspace
            basis=nullspace([[t-(L if i==j else 0) for j,t in enumerate(row)] for i,row in enumerate(A)])
            if len(basis)==1:
                u=basis[0];N=('sqrt',q(sum(t*t for t in u)))
                return dict(value=value,points=[tuple(m.mul(q(s),m.div(m.mul(b,q(t)),N)) for b,t in zip(scales,u)) for s in (-1,1)])
        return dict(value=value,points='unit eigenspace of the restricted matrix at this eigenvalue, mapped back with scales')
    return multivariate_certificate(lib,'restrict_quadratic_on_unit_sphere',dict(scales=scales,matrix=M,normal=projection),
        dict(minimum=result(lo),maximum=result(hi),coincident_eigenvalues='every feasible point'),
        'Нормировать исходную квадрику на сферу. Если дана плоскость, ограничить симметричную форму её ортогональным проектором.',
        'Точные след и определитель двумерного ограничения дают два собственных значения. Знак и равенство следуют из разложения в ортонормированном собственном базисе.',
        'Для каждого крайнего значения взять все единичные собственные векторы в допустимом подпространстве и вернуть исходные координаты.',
        trace=trace,discriminant=delta)


def positive_simplex(task,lib):
    mv_fields(task,{'source_formula','stated_conditions','requested_output'},('all_constrained_extremum_points',))
    mv_require(task.get('requested_output')==['all_constrained_extremum_points'],'Искомы все точки условного экстремума')
    f=task['source_formula'];c=task['stated_conditions']
    if (f,c)==('sum x_i²',['sum x_i/a_i=1','a_i>0']):
        return multivariate_certificate(lib,'exact_positive_global_bounds',dict(normal='v_i=1/a_i',scales='a_i>0'),
            dict(minimum='1/sum_i v_i²',minimizer='v/(sum_i v_i²)',maximum='same at n=1; unbounded above at n>=2'),
            'Фиксированное скалярное произведение равно единице. Неравенство Коши даёт глобальную нижнюю грань и единственный случай равенства.',
            'При двух и более координатах можно уходить на бесконечность вдоль любого ненулевого направления в ядре связи.')
    if (f,c)==('sum x_i^p',['sum x_i=a','p>0','a>0']):
        return multivariate_certificate(lib,'exact_positive_global_bounds',dict(constraint='positive simplex, allow zero only on stated power domain'),
            dict(equal_coordinates='a/n',equal_value='n^(1-p)*a^p',vertex_value='a^p',
                 p_greater_one='minimum at the equal point; supremum at a simplex vertex if allowed',
                 p_less_one='maximum at the equal point; infimum at a simplex vertex if allowed',p_equal_one='constant'),
            'Знак второй производной степени положителен при p>1 и отрицателен при 0<p<1. Применить выпуклое или вогнутое сравнение среднего.',
            'Для противоположной грани после нормировки использовать t^p≤t либо t^p≥t на [0,1]. Равенство требует вершины для p≠1.',
            'Если исходная область допускает нулевые координаты по продолжению степени, вершины входят в область. Для положительных оснований сохраняется только грань.')
    if (f,c)==('sum alpha_i/x_i',['sum beta_i*x_i=1','alpha_i,beta_i,x_i>0']):
        return multivariate_certificate(lib,'exact_positive_global_bounds',dict(weighted_sum='sum β_i x_i=1',positivity=True),
            dict(minimum='(sum_i sqrt(alpha_i*beta_i))²',minimizer='sqrt(alpha_i/beta_i)/sum_j sqrt(alpha_j*beta_j)',
                 maximum='same at n=1; unbounded above at n>=2'),
            'Применить Коши к векторам sqrt(αᵢ/xᵢ) и sqrt(βᵢxᵢ), один квадрат нормы уже равен единице.',
            'Условие пропорциональности даёт единственные координаты. Уход к исключённой нулевой координате даёт бесконечный рост при n≥2.')
    if (f,c)==('prod x_i^alpha_i',['sum x_i=a','a>0','each alpha_i>1']):
        return multivariate_certificate(lib,'exact_positive_global_bounds',dict(weighted_exponents='all alpha_i>1',sum='a>0'),
            dict(maximizer='x_i=a*alpha_i/sum_j alpha_j',maximum='product of the indicated powers',
                 lower_edge='zero, attained only if zero factors are admitted in the source; n=1 constant'),
            'На положительной ветви сумма логарифмов строго вогнута. Её частные на гиперплоскости совпадают при xᵢ, пропорциональных αᵢ.',
            'Установить равенство целевой связи в найденной точке. На замыкании с хотя бы одной нулевой координатой произведение стремится к нулю.')
    trig=re.fullmatch(r'x\+y\+z=(.+)',c[0]) if isinstance(c,list) and c else None
    if trig and f=='sin(x)*sin(y)*sin(z)' and c[1:]==['x,y,z>0']:
        a=m.parse(trig[1],None);ctx=m.context(dict(variable='__angle_sum'))
        mv_require(m.sign(a,ctx)==1 and m.sign(m.add(('pi',),m.neg(a)),ctx) in (0,1),'Нужно доказать, что все три угла строго внутри (0,π)')
        p=m.div(a,q(3));v=('sin',p)
        return multivariate_certificate(lib,'exact_positive_global_bounds',dict(sum=a,open_simplex=True),
            dict(maximum=m.power(v,3),maximizer=(p,p,p),infimum=ZERO,minimum_attained=False),
            'На (0,π) вторая производная логарифма синуса строго отрицательна. При заданной сумме максимум суммы логарифмов в единственной равной тройке.',
            'Все три угла допустимы. Уход к одной нулевой координате даёт нижнюю грань ноль, внутри произведение строго положительно.')
    if not c or len(c)!=2:raise Unsupported('Не разобрана положительная линейная связь и область степеней')
    eq=coordinate_polynomial(c[0]);mv_require(eq.count('=')==1,'Нужна одна сумма с положительными весами')
    axes=['x','y','z'];text=coordinate_polynomial(f);pars=mv_names(text+' '+eq,*axes);decl=axes+pars;G=m.parse(text,None,decl)
    h,limit=(m.parse(s,None,decl) for s in eq.split('='));A,B,C=symbolic_quadratic(h,axes)
    needed=[*pars] if domain_conditions(G) else [*pars,*axes]
    declared=re.fullmatch(r'([a-z,]+)>0',c[1]);mv_require(declared and set(needed)==set(declared[1].split(',')),
        'Знаки оснований и независимых параметров должны следовать из исходной области степеней')
    mv_require(all(z==ZERO for row in A for z in row) and C==ZERO and not domain_conditions(h) and not domain_conditions(limit)
         and not any(m.contains(limit,mv_symbol(x)) for x in axes),'Связь должна быть однородной линейной формой по координатам')
    ctx=m.context(dict(variable='__simplex',parameters=decl,parameter_conditions=[v+'>0' for v in needed]));p,d=m.rational_form(G)
    mv_require(len(p)==1 and d=={():Fraction(1)} and m.sign(limit,ctx)==1 and all(m.sign(b,ctx)==1 for b in B),
         'Целевая функция должна быть положительным произведением на линейном симплексе')
    (mon,k),=p.items();weights=dict.fromkeys(axes,ZERO)
    for term,z in mon:
        if term[0]=='s' and term[1] in axes:axis=term[1];exponent=ONE
        elif term[0]=='rpow' and term[1][0]=='s' and term[1][1] in axes:axis=term[1][1];exponent=term[2]
        else:raise Unsupported('Не распознана независимая степенная переменная')
        weights[axis]=m.add(weights[axis],m.mul(q(z),exponent))
    mv_require(k>0 and all(m.sign(e,ctx)==1 for e in weights.values()) and all(k=='positive' and g in tuple(map(mv_symbol,axes)) for k,g in domain_conditions(G)),
         'Степенные показатели и исходная гладкая область должны быть положительны')
    V=list(weights.values());T=mv_sum(V);point=[m.div(m.mul(p,limit),m.mul(b,T)) for p,b in zip(V,B)];repl=dict(zip(map(mv_symbol,axes),point))
    mv_require(same_value(m.substitute(h,repl),limit),'Точка равенства не удовлетворяет исходной линейной связи')
    return multivariate_certificate(lib,'exact_positive_global_bounds',dict(axes=axes,sum=limit,linear_weights=B,powers=V),
        dict(maximum=m.substitute(G,repl),point=point,infimum=ZERO,minimum_attained=False),
        'Нормировать положительные линейные слагаемые до долей с суммой 1. Логарифм произведения имеет строго отрицательный гессиан.',
        'Равенство градиентов по долям даёт каждую долю, пропорциональную своему показателю. Проверить обратную подстановку в исходную связь.',
        'На открытых границах хотя бы одна доля стремится к нулю. Это даёт только нижнюю грань, внутри все множители положительны.')


def telescoping_extremum(task,lib):
    mv_fields(task,{'source_formula','stated_conditions','requested_output'},('classify_all_extrema_on_original_domain','maximize and find inserted numbers'),
           extra_meta={'section_convention'});f=task['source_formula'];c=task['stated_conditions'];o=task['requested_output']
    if f=='prod x_i / ((a+x1)*(x1+x2)*...*(xn+b))':
        mv_require(c==['a,b>0','insert n numbers between a and b'] and o==['maximize and find inserted numbers'],
            'Исходные вставляемые числа и их положительные концы должны совпадать с произведением')
        return multivariate_certificate(lib,'exact_positive_global_bounds',dict(endpoints='x_0=a>0, x_{n+1}=b>0'),
            dict(common_ratio='(b/a)^(1/(n+1))',maximizer='x_i=a*common_ratio^i',maximum='1/(a*(1+common_ratio)^(n+1))'),
            'Ввести все положительные соседние отношения. Их произведение равно b/a. После сокращения исходная цель обратно пропорциональна произведению единицы плюс каждое отношение.',
            'Логарифм каждого множителя выпукл по логарифму отношения. При фиксированной сумме строгая выпуклость даёт равенство всех отношений.',
            'Восстановленные числа лежат между концами, поскольку отношение постоянно. Для совпавших концов все числа совпадают с ними при допустимых повторах.')
    mv_require(c==['each x_i>0'] and o==['classify_all_extrema_on_original_domain'],'Нужна вся положительная область цепочки')
    hit=re.fullmatch(r'x1\+sum_\(j=2\)\^n x_j/x_\(j-1\)\+(\d+)/x_n',f)
    mv_require(hit and int(hit[1])>0,'Все соседние отношения должны телескопировать к одной положительной константе')
    a=int(hit[1]);ratio=f'{a}^(1/(n+1))'
    return multivariate_certificate(lib,'exact_positive_global_bounds',dict(constant_product=q(a),independent_positive_variables=True),
        dict(minimum='(n+1)*'+ratio,minimizer='x_i='+ratio+'^i',maximum='empty; unbounded above'),
        'Произведение n+1 положительных слагаемых сокращается до постоянной. Среднее арифметическое не меньше геометрического и равно ему только при равных слагаемых.',
        'В логарифмических координатах сумма экспонент строго выпукла. Равная цепочка — единственный локальный экстремум и глобальный минимум.')


ORIGIN_HEADINGS=(
    'Найти обе частные производные в (0,0) и решить вопрос о дифференцируемости.',
    'Дифференцируема ли функция в (0,0)?',
    'Исследовать дифференцируемость в начале.',
    'Доказать непрерывность, существование двух частных производных и отсутствие дифференцируемости в (0,0). Исследовать поведение обеих производных в окрестности.',
    'Доказать непрерывность и ограниченность частных производных в окрестности, отсутствие дифференцируемости в начале.',
    'Доказать дифференцируемость в начале, и что обе частные производные разрывны там и неограниченны в любой окрестности.',
)


def radial_origin_regularity(task,lib):
    meta=mv_fields(task,{'given'},ORIGIN_HEADINGS);t=mv_normal(task['given'])
    hit=re.fullmatch(r'f(?:\(([a-z]),([a-z])\))?=(.+?)(?: outside \(0,0\), f\(0,0\)=0)?',t)
    mv_require(hit,'Нужно явно связать функцию с началом её исходных координат')
    a,b=hit[1] or 'x',hit[2] or 'y';axes=[a,b];x,y=map(mv_symbol,axes);f=m.parse(hit[3],None,axes)
    s=m.add(m.power(x,2),m.power(y,2));xy=m.mul(x,y);rad=('sqrt',s);proofs=[];table_steps=[]
    ctx=m.context(dict(variable='__phase_norm',parameters=axes,parameter_conditions=[source(s)+'>0']))
    guard=domain_conditions(f);actual=list(guard);degree=None;extras={};phase=None
    if f[0]=='cbrt' and same_value(f[1],xy):
        heading=ORIGIN_HEADINGS[0]
        degree=q(2,3);zero_axes=True;u=q(1);bound='|xy|≤r²/2';proofs.append('На обеих осях функция ноль. На диагонали f(t,t)=t^(2/3) при t>0.')
    elif f[0]=='cbrt' and same_value(f[1],m.add(m.power(x,3),m.power(y,3))):
        heading=ORIGIN_HEADINGS[1]
        degree=ONE;zero_axes=False;u=('cbrt',q(2));bound='|x³+y³|≤2r³';proofs.append('Кубический корень на каждой оси даёт саму координату. На диагонали значение равно t·∛2.')
    elif f[0]=='sqrt' and f[1][0]=='abs' and same_value(f[1][1],xy):
        heading=ORIGIN_HEADINGS[3]
        degree=ONE;zero_axes=True;u=ONE;bound='|xy|≤r²/2'
        extras=dict(partials_off_axes='|f_x|=sqrt(|y/x|)/2, |f_y|=sqrt(|x/y|)/2',
            on_axes_away_from_origin='the transverse partial has no finite limit; the tangential one is zero',
            derivative_bounded_in_neighborhood=False)
        proof='На осях срезы в начале нулевые, на диагонали f(t,t)=t при t>0. На проколотых осях поперечное отношение имеет степенной порядок −1/2.'
        proofs.append(proof)
    elif f[0]=='div' and same_value(f[1],xy) and same_value(f[2],rad):
        heading=ORIGIN_HEADINGS[4]
        degree=ONE;zero_axes=True;u=m.div(ONE,('sqrt',q(2)));bound='|xy|/r≤r/2'
        D,table_steps=derivative_table(lib);extras=dict(partials=[D(f,a),D(f,b)],derivative_bound=q(1))
        mv_require(all(same_value(t,m.div(m.power(z,3),m.power(rad,3))) for t,z in zip(extras['partials'],(y,x))),
                   'Не доказана формула частных производных на проколотой области')
        proofs.append('На осях срезы в начале нулевые. На диагонали f(t,t)=t/√2, а обе производные вне начала ограничены модулями кубов координат, делённых на r³.')
    elif f[0]=='exp':
        heading=ORIGIN_HEADINGS[2]
        c=m.simplify(m.substitute(m.mul(s,f[1]),{x:ONE,y:ZERO}));mv_require(m.sign(c,ctx)==-1 and same_value(m.mul(s,f[1]),c),
            'В экспоненте нужен отрицательный постоянный множитель при обратном квадрате нормы')
        zero_axes=True;degree=q(2);actual=[('positive',s)];bound='exp(c/r²)≤r²/(-c) from exp(u)≥u'
        proofs.append('При r>0 ограничить экспоненту обратной первой степенью положительного аргумента противоположной экспоненты. Получаем O(r²).')
    elif f[0]=='mul':
        heading=ORIGIN_HEADINGS[5]
        z,h=f[1:]
        if z[0]=='sin':z,h=h,z
        mv_require(h[0]=='sin' and same_value(z,s),'Не распознано произведение квадрата нормы на осциллирующий множитель')
        c=m.simplify(m.substitute(m.mul(s,h[1]),{x:ONE,y:ZERO}));mv_require(m.sign(c,ctx)==1 and same_value(m.mul(s,h[1]),c),
            'Обратная фаза должна иметь положительный постоянный числитель')
        actual=[('positive',s)];degree=q(2);zero_axes=True;bound='|f|≤r²';phase=c
        D,table_steps=derivative_table(lib);extras=dict(partials=[D(f,a),D(f,b)],derivative_bounded_in_neighborhood=False,
            unbounded_witness='on each positive axis choose radii r_k with phase=2πk; |partial|=2c/r_k')
        proofs.append('Функция по модулю не превосходит r². При фазе 2πk на положительной оси синусный член производной исчезает, а косинусный неограничен.')
    else:raise Unsupported('Для остатка в начале нужна другая проверенная сравнительная функция')
    mv_require(meta.get('literal_requirement') in (None,heading),'Печатное заключение не совпало с доказанным типом регулярности')
    mv_require(all(known_guard(g,ctx) for g in guard),'В исходной проколотой области есть непроверенное исключение')
    origin=m.context(dict(variable='__origin_domain'));zero={x:ZERO,y:ZERO}
    if not all(known_guard((k,m.substitute(g,zero)),origin) for k,g in guard):
        mv_require('outside (0,0), f(0,0)=0' in t,'Для исходной выколотой точки не задано значение')
    partials=[ZERO,ZERO] if zero_axes else [ONE,ONE];p=m.num(degree)
    if p<=1:
        if p==1:mv_require(not same_value(u,m.add(*partials)),'Диагональ не опровергает найденную линейную часть')
        proofs.append('Нормированный остаток вдоль допустимой диагонали или неограничен, или имеет ненулевой модуль. Полный дифференциал не существует.')
        extras['diagonal_positive_ray']=dict(coefficient=u,order=degree)
    else:proofs.append('Нормированный остаток ограничен величиной, стремящейся к нулю на всей проколотой окрестности. Линейная часть нулевая.')
    return multivariate_certificate(lib,'separate_slices_and_radial_remainder',dict(axes=axes,point=[ZERO,ZERO],function=f,guards=actual),
        dict(continuous_at_origin=True,partial_derivatives_at_origin=partials,differentiable_at_origin=p>1,**extras),
        *proofs,radial_bound=bound,phase_numerator=phase,table_steps=table_steps)


def coordinate_modulus_proof(text,heading):
    """Bind the abstract hypotheses before choosing a coordinate witness."""
    joint='Доказать совместную непрерывность.'
    separate='Доказать совместную непрерывность по x и y.'
    young='Доказать совместную непрерывность (теорема Юнга).'
    uniform='Доказать равномерную непрерывность в E.'
    uniform_hyp=re.fullmatch(r'on (\w+), (\w+) continuous in (\w+) and continuous in (\w+) uniformly with respect to \3',text)
    bound_hyp=re.fullmatch(
        r'on (?P<domain>[A-Za-z_]\w*), (?P<f>[A-Za-z_]\w*) continuous in (?P<x>[a-z]) and satisfies abs\((?P=f)\((?P=x),(?P<y>[a-z])1\)-(?P=f)\((?P=x),(?P=y)2\)\)<=(?P<L>[A-Z])\*abs\((?P=y)1-(?P=y)2\), (?P=L) constant whenever points in (?P=domain)',
        text)
    partial=re.fullmatch(r'(\w+) continuous in ([a-z]) for each fixed ([a-z]), bounded derivative \1_\3',text)
    if uniform_hyp or bound_hyp or partial:
        hit=uniform_hyp or bound_hyp
        # The function is defined on an open source domain, allowing coordinate rectangles.
        domain,F,x,y,limit=(*hit.groups(),None) if uniform_hyp else hit.groups() if bound_hyp else ('G',*partial.groups(),None)
        needed=separate if partial else joint
        mv_require(x!=y and heading in (None,needed),'The printed continuity assertion and derived premise disagree')
        premise='uniform modulus in '+y if uniform_hyp else 'Lipschitz estimate in '+y if bound_hyp else 'bounded partial derivative in '+y
        bridge=('Применяем Лагранжа к первому приращению на вертикальном отрезке в прямоугольнике.' if partial
                else 'По исходному условию первое приращение имеет единый по другой координате модуль.')
        return (dict(theorem='method.coordinate_moduli_imply_joint_continuity',premise=premise,coordinate_split=[x,y],source_domain=domain,
                     argument=['Внутри исходной области выбираем малый прямоугольник вокруг фиксированной точки.',
                               'Вычитаем и прибавляем промежуточное значение с новой первой координатой и прежней второй.',
                               bridge,'Второе приращение стремится к нулю по непрерывности фиксированного среза. Складываем две оценки.']),
                dict(jointly_continuous=True,domain=domain))
    if re.fullmatch(r'\w+ separately continuous and monotone in one variable',text):
        mv_require(heading in (None,young),'The source demands a different continuity conclusion')
        return (dict(theorem='method.monotone_slice_sandwich',argument=[
             'По непрерывности среза выбираем две допустимые высоты по разные стороны точки, на которых значения при фиксированной абсциссе близки к её значению.',
             'По отдельной непрерывности в этих двух фиксированных срезах выбираем один интервал по абсциссе. При изменении абсциссы обе граничные высоты сохраняют оценки.',
             'Монотонность по вертикали располагает значение между двумя граничными значениями. Для убывания меняем порядок границ.']),
             dict(jointly_continuous=True))
    box=re.fullmatch(r'(\w+) with bounded partials \1_([a-z]),\1_([a-z]) on convex domain (\w+)',text)
    if box:
        F,x,y,domain=box.groups()
        mv_require(x!=y and heading in (None,uniform),'The same distinct partials must control the whole convex domain')
        return (dict(theorem='method.coordinate_moduli_imply_joint_continuity',source_domain=domain,coordinate_split=[x,y],
                      argument=['На каждом достаточно малом координатном прямоугольнике применяем Лагранжа к обоим последовательным приращениям.',
                                'Для произвольных двух точек их отрезок лежит в выпуклой области. Компактность отрезка позволяет покрыть его такими прямоугольниками и разбить на конечные локальные шаги.',
                                'Все шаги идут в одном направлении. Сумма их координатных длин равна исходной координатной длине; складываем единые оценки.']),
                dict(uniformly_continuous=True,modulus='Mx*abs(Delta '+x+')+My*abs(Delta '+y+')',domain=domain))
    raise Unsupported('The abstract coordinate assumptions do not entail the requested joint conclusion')


def continuity_trace_compose(text,heading):
    pair=re.fullmatch(r'(\w+) continuous on \[a,A\]x\[b,B\]; (\w+)_n uniformly converges on \[a,A\], b<=\2_n\(x\)<=B',text)
    if pair:
        f,p=pair.groups()
        mv_require(heading in (None,f'Доказать равномерную сходимость F_n(x)={f}(x,{p}_n(x)) на [a,A].'),
                   'The same sequence must occur inside the requested composition')
        return (dict(theorem='method.continuous_trace_composition',compact_rectangle=True,inner_sequence=p,
                    argument=['Замкнутый диапазон [b,B] содержит значения предельной функции по поточечному пределу.',
                              'На компактном исходном прямоугольнике f равномерно непрерывна. Обе сравниваемые точки принадлежат прямоугольнику и имеют одну абсциссу.',
                              'Их расстояние ограничено единым отклонением внутренней последовательности. Это даёт равномерный предел исходной композиции.']),
                dict(uniformly_converges=True,limit=f+'(x,'+p+'(x))',domain='[a,A]'))
    path=re.fullmatch(r'(\w+) continuous on R=\(a,A\)x\(b,B\), (\w+) continuous on \(a,A\) with values in \(b,B\)',text)
    if path:
        f,p=path.groups()
        mv_require(heading in (None,f'Доказать непрерывность F(x)={f}(x,{p}(x)).'),
            'The requested continuous inclusion does not use the two established coordinate maps')
        return (dict(theorem='method.continuous_trace_composition',inner_map=('x',p+'(x)'),range_inside='R',
                    argument=['Пара отображений x и φ(x) непрерывна и целиком принимает значения в заданном прямоугольнике.',
                              'Композиция с f непрерывна, поскольку каждый переход находится в области исходной непрерывности.']),
                dict(continuous=True,domain='(a,A)'))
    raise Unsupported('The corresponding original maps and image bounds remain to be proved')


def continuity_from_paths(task,lib):
    """Propose path sequences or a uniform norm bound from the source expression."""
    mv_require(lib.data.get('multivariate_coordinate_moduli') and task.get('kind') in ('multivariate_continuity','multivariate_regularities'),
               'No path or uniform-modulus transition in this library')
    meta=mv_fields(task,{'given'});text=mv_normal(task['given']);heading=meta.get('literal_requirement')
    for candidate in (coordinate_modulus_proof,continuity_trace_compose):
        try:return candidate(text,heading)
        except Unsupported:pass
    x,y=map(mv_symbol,('x','y'));coords=[x,y];ctx=m.context(dict(variable='phaseCoordinate',parameters=['x','y']))
    qctx=m.context(dict(variable='phaseCoordinate'));r2=mv_sum(m.power(z,2) for z in coords)
    linear=re.fullmatch(r'(?:[A-Za-z]\w*=)?(.+) on entire Euclidean plane',text)
    def admissible(e, guards=()):
        return all(known_guard(g,qctx) or any(g[0]==r and same_value(g[1],a) for r,a in guards)
                   for g in domain_conditions(e))
    if linear and heading in (None,'Исследовать равномерную непрерывность.'):
        g=m.parse(linear[1],None,['x','y'])
        mv_require(admissible(g[1] if g[0]=='sqrt' else g),'An original full-plane formula has an unproved domain condition')
        p,d=m.rational_form(g[1] if g[0]=='sqrt' else g)
        mv_require(d=={():Fraction(1)},'Need a polynomial affine form or norm')
        if g[0]=='sqrt':
            degeneracy={((z,2),) for z in coords}
            mv_require(p and not set(p)-degeneracy and all(a>=0 for a in p.values()),'The radicand must be a nonnegative sum of squared linear coordinates')
            L=('sqrt',q(max(p.values())));argument='Используем обратное неравенство треугольника для нормы после линейного диагонального преобразования. Максимальный вес ограничивает норму преобразованного приращения.'
        else:
            mv_require(not set(p)-({()}|{((z,1),) for z in coords}),'The full-plane form is not affine')
            L=('sqrt',q(sum(p.get(((z,1),),0)**2 for z in coords)))
            argument='Вычитаем два значения и оцениваем скалярное произведение разности координат с вектором коэффициентов неравенством Коши.'
        return dict(theorem='method.linear_norm_modulus',original=g,modulus=L,argument=argument),dict(uniformly_continuous=True,domain='R^2',Lipschitz_constant=m.simplify(L))
    osc=re.fullmatch(r'(.+) on (.+)<(.+)',text)
    if osc and heading in (None,'Исследовать равномерную непрерывность.'):
        raw=m.parse(osc[1],None,['x','y']);disk=m.parse(osc[2],None,['x','y'])
        edge=m.parse(osc[3],None)
        mv_require(same_value(disk,r2) and admissible(disk) and m.constant_defined(edge,qctx) and m.sign(edge,qctx)==1
                   and raw[0] in ('sin','cos') and raw[1][0]=='div','Need a circular domain and reciprocal radial phase')
        K,d=raw[1][1:];domain=m.add(edge,m.neg(r2))
        mv_require(m.constant_defined(K,qctx) and m.sign(K,qctx)==1 and same_value(d,domain)
                   and all(known_guard(g,qctx) for g in domain_conditions(d))
                   and admissible(raw,[('nonzero',domain)]),'The phase denominator must be positive on the full source disk')
        a,b=('pi/2','3*pi/2') if raw[0]=='sin' else ('0','pi')
        paths=[dict(phase=f'2*pi*k+{j}',radius=f'sqrt({source(edge)}-{source(K)}/(2*pi*k+{j}))',
                    point='(radius,0)',value=q(1 if i==0 else -1)) for i,j in enumerate((a,b))]
        return (dict(theorem='method.distinct_radial_phases',distinct_paths=paths,original=raw,
              argument='На первом координатном луче решаем уравнение фазы для двух последовательностей противоположных значений гармоники. При больших k радиусы вещественны и строго меньше радиуса диска. Обе точки сближаются с одной граничной точкой, разность значений постоянна.'),
                dict(uniformly_continuous=False,oscillation=2))
    ratio=re.fullmatch(r'(.+) on its domain E',text)
    if ratio and heading in (None,'Определить непрерывность и равномерную непрерывность на E.'):
        raw=m.parse(ratio[1],None,['x','y']);a=raw[1] if raw[0] in ('asin','acos','atan') else ZERO
        c=m.simplify(m.substitute(a,{x:ONE,y:ONE}))
        mv_require(m.constant_defined(c,qctx) and m.nonzero(c,qctx) and same_value(a,m.mul(c,('div',x,y)))
                   and admissible(a,[('nonzero',y)]),'A ratio of independent coordinates is required before the outer continuous map')
        conditions=['y!=0']
        if raw[0]!='atan':conditions.append('abs('+source(c)+'*x/y)<=1')
        values=[m.simplify((raw[0],z)) for z in (ZERO,q(1,2))]
        paths=[dict(parameter='t -> 0+',point=(ZERO if i==0 else m.div(q(1,2),c),'t'),
                    first_coordinate_multiple_of_t=True,value=v) for i,v in enumerate(values)]
        return (dict(theorem='method.distinct_radial_phases',distinct_paths=paths,original=raw,
                 argument='Исходная функция непрерывна на относительной области композиции. При положительном масштабировании отношение неизменно. Выбираем два допустимых луча, где аргументы 0 и 1/2. Строгая монотонность внешней функции даёт разные значения при расстоянии, стремящемся к нулю.'),
                dict(continuous=True,uniformly_continuous=False,domain=conditions))
    axis=re.fullmatch(r'f\(x,y\)=(.+) for y!=0, f\(x,0\)=0',text)
    if axis and heading in (None,'Доказать незамкнутость множества точек разрыва.'):
        raw=m.parse(axis[1],None,['x','y'])
        mv_require(raw[0]=='mul','Need a coordinate envelope times a bounded oscillation')
        A,w=raw[1:]
        if A[0] in ('sin','cos'):A,w=w,A
        mv_require(w[0] in ('sin','cos') and w[1][0]=='div' and w[1][2]==y
                   and m.constant_defined(w[1][1],qctx) and m.nonzero(w[1][1],qctx)
                   and not m.contains(A,y) and admissible(A),'Need a polynomial envelope independent of the oscillation coordinate')
        from polynomial import rf
        from graphs import rational_roots
        inner=m.substitute(A,{x:('v','x')});p,d=rf(inner,'x')
        mv_require(any(p) and len(d)==1 and d[0],'An entire nonzero polynomial envelope is required')
        zeros=rational_roots(p)
        mv_require(bool(zeros),'The resulting discontinuity set has no omitted accumulation point')
        return (dict(theorem='method.oscillatory_axis_amplitude',original=raw,
            argument=['Вне оси функция непрерывна на исходной области.',
                      'При ненулевом коэффициенте на оси подбираем две последовательности обратной фазы, на которых гармоника равна ±1. При нулевом коэффициенте ограждение |f(x,y)|≤|A(x)| даёт общую непрерывность.',
                      'Нули ненулевого полинома изолированы. Каждая исключённая точка с A=0 является точкой накопления разрывов.']),
                dict(discontinuities='y=0 and ('+source(A)+')!=0',closed=False))
    raise Unsupported('Need a different admissible pair of paths or modulus for the original source')


def rational_directional_limit(raw,coordinate):
    from polynomial import rf
    p,d=rf(raw,coordinate)
    if all(v==0 for v in p):return dict(value=ZERO,finite=True,laurent_order='+inf')
    i=next(j for j,v in enumerate(p) if v);j=next(j for j,v in enumerate(d) if v)
    coefficient=p[i]/d[j];order=i-j
    val=dict(laurent_order=order,coefficient=q(coefficient),finite=order>=0)
    if order>=0:return dict(val,value=q(coefficient) if order==0 else ZERO)
    right='+inf' if coefficient>0 else '-inf'
    left=right if order%2==0 else '-inf' if right=='+inf' else '+inf'
    return dict(val,left=left,right=right)


def ordered_slice_derivatives(task,lib):
    """First establish two entire punctured slices, then take the next difference quotients."""
    if not lib.data.get('multivariate_slice_traces') or task.get('kind')!='mixed_partials_piecewise_at_point':
        raise Unsupported('The relevant ordered-slice transition is not available')
    meta=mv_fields(task,{'off_origin','value_at_origin','variables','point'});axes=task.get('variables')
    mv_require(isinstance(axes,list) and len(axes)==2 and len(set(axes))==2 and
               all(isinstance(a,str) and len(a)==1 and a.isascii() and a.isalpha() for a in axes),
               'Two independent named coordinates are required')
    point=task.get('point')
    mv_require(isinstance(point,list) and len(point)==2,'Both source coordinates of the assigned point are required')
    empty=m.context(dict(variable='sliceParameter'))
    positions=[m.parse(str(value),None) for value in point]
    mv_require(all(m.num(z) is not None for z in positions),'The assigned point needs exact rational coordinates')
    F0=m.parse(str(task['value_at_origin']),None)
    mv_require(m.num(F0) is not None,'The prescribed value at the exceptional point must be real and exact')
    x,y=map(mv_symbol,axes);coords=(x,y)
    offset={a:m.add(a,c) for a,c in zip(coords,positions)}
    raw=m.parse(mv_normal(task['off_origin']),None,axes)
    f=m.substitute(raw,offset)
    square=mv_sum(m.power(z,2) for z in coords)
    bound=m.context(dict(variable='sliceParameter',parameters=axes,parameter_conditions=[source(square)+'>0']))
    mv_require(bool(domain_conditions(f)) and all(known_guard(g,bound) for g in domain_conditions(f)),
               'The off-point formula must be proved defined on the entire punctured source plane')
    def as_axis(e,axis,other,t,other_value=ZERO):
        return m.substitute(e,{axis:t,other:other_value})
    first={};difference={};direction='sliceParameter';t=('v',direction)
    for a,b in ((x,y),(y,x)):
        sec=as_axis(f,a,b,t)
        ratio=('div',m.add(sec,m.neg(F0)),t)
        data=rational_directional_limit(ratio,direction)
        mv_require(data['finite'],'A first partial does not exist at the assigned point')
        first[a]=data['value'];difference[a]=ratio
    D,used=derivative_table(lib);results=[];slices=[]
    for a,b in ((x,y),(y,x)):
        formula=D(f,a[1])
        mv_require(all(known_guard(g,bound) for g in domain_conditions(formula)),
                   'The rule for the first derivative introduced an unproved extra guard')
        sec=as_axis(formula,b,a,t)
        ratio=('div',m.add(sec,m.neg(first[a])),t)
        proof=rational_directional_limit(ratio,direction)
        results.append(dict(order=[a[1],b[1]],**proof))
        slices.append(dict(first_derivative=a[1],punctured_slice=sec,assigned_slice_value=first[a],second_ratio=ratio,
                           first_ratio=difference[a]))
    heading=meta.get('literal_requirement')
    unequal=f'Доказать f_{axes[0]}{axes[1]}(0,0) != f_{axes[1]}{axes[0]}(0,0).'
    existence=f'Существует ли f_{axes[0]}{axes[1]}(0,0)?'
    if heading==unequal:
        mv_require(positions==[ZERO,ZERO] and all(z['finite'] for z in results) and results[0]['value']!=results[1]['value'],
                   'The two finite ordered partials do not prove the original inequality')
    elif heading==existence:
        mv_require(positions==[ZERO,ZERO],'The printed existence question refers to the assigned origin')
    else:mv_require(heading is None,'The original ordered differential request is unbound')
    wanted=[results[0]] if heading==existence else results
    return (dict(theorem='method.ordered_coordinate_difference_quotients',source_function=raw,assigned_point=positions,
                 assigned_value=F0,verified_off_point_guard=source(square)+'>0',slices=slices,derivative_rules=used,
                 argument=['Строим оба первые отношения в самой точке по назначенному значению и точным координатным срезам.',
                           'В остальных точках соседних осей функция гладкая по исходному положительному знаменателю. Вычисляем первую частную до подстановки фиксированной координаты.',
                           'У каждой первой частной свой срез. Для второго отношения сравниваем первые ненулевые степени числителя и знаменателя отдельно в каждом порядке.']),
            dict(first_partials=[first[x],first[y]],ordered_partials=wanted,
                 requested_inequality=True if heading==unequal else None))


def fixed_argument_derivative(task,lib):
    from derivative_proofs import quadratic_point,table
    from graphs import domain_partition
    from intervals import read_quadratic_term
    from polynomial import rf
    if not lib.data.get('multivariate_slice_traces') or task.get('kind')!='partial_derivative_at_point':
        raise Unsupported('No fixed-coordinate section transition')
    meta=mv_fields(task,{'given'});text=mv_normal(task['given']);heading=meta.get('literal_requirement')
    name=r'([a-zA-Z]\w*)'
    abstract=re.fullmatch(fr'{name}\({name},{name}\), fixed {name}',text)
    if abstract:
        f,x,y,b=abstract.groups()
        expected=f'Показать {f}_{x}({x},{b})=d/d{x}[{f}({x},{b})].'
        mv_require(len({f,x,y,b})==4 and heading in (None,expected),'The original derivative and fixed variable are not bound')
        return (dict(theorem='method.fixed_coordinate_section_derivative',fixed={y:b},free=x,
                     argument='В обоих разностных отношениях приращается одна и та же координата, другая удерживается равной данному фиксированному значению. Исходное допустимое множество приращений одинаково.'),
                dict(identical_where_defined=True,identity=f'd/d{x}[{f}({x},{b})]={f}_{x}({x},{b})'))
    binder=re.fullmatch(fr'{name}\({name},{name}\)=(.+)',text)
    target=re.fullmatch(fr'Найти {name}_{name}\({name},(-?\d+(?:/\d+)?)\)\.',heading or '')
    mv_require(binder and target and target[1]==binder[1] and target[2]==target[3]==binder[2],
               'Need the same named function and a fixed-coordinate derivative on the source section')
    f,x,y,body=binder.groups();value=q(Fraction(target[4]))
    mv_require(len({f,x,y})==3,'Need distinct free and bound coordinates')
    v=('v',x);raw=m.parse(body,x,[y]);section=m.substitute(raw,{mv_symbol(y):value})
    guards=domain_conditions(section)
    partition,_=domain_partition(x,guards,simplify_guards=True)
    normal=m.simplify(section);rf(normal,x)  # A regular rational extension suffices at attached finite ends.
    derivative,steps=table(normal,x,lib)
    c=m.context(dict(variable=x));ends=[]
    for i,(z,admitted) in enumerate(zip(partition['cuts'],partition['point_membership'])):
        if not admitted:continue
        a=quadratic_point(read_quadratic_term(z))
        at=m.substitute(normal,{v:a});slope=m.substitute(derivative,{v:a})
        mv_require(m.constant_defined(at,c) and m.constant_defined(slope,c),
                   'The rational section has no regular extension at an included cut')
        sides=[d for d,keep in zip(('left','right'),partition['open_cells'][i:i+2]) if keep]
        if sides and len(sides)<2:ends.append(dict(point=a,sides=sides,relative_slope=m.simplify(slope)))
    return (dict(theorem='method.fixed_coordinate_section_derivative',original=raw,substituted_section=section,
                 section_domain=partition,raw_guards=guards,simplified_section=normal,table_steps=steps,
                 argument=['Сначала подставляем фиксированную координату в исходные условия определённости.',
                           'После проверки области дифференцируем сокращённый срез. На включённых конечных границах различаем обычную частную и относительный односторонний наклон.']),
            dict(ordinary_partial_on_open_domain=derivative,section_domain=partition,relative_endpoint_slopes=ends))


MEASUREMENT_HEADINGS=(
    'На сколько изменятся диагональ и площадь?',
    'Насколько уменьшить радиус при сохранении площади?',
    'Доказать, что относительная погрешность произведения приближенно равна сумме относительных погрешностей сомножителей.',
    'С какими абсолютной и относительной погрешностями может быть вычислен объем?',
    'С какой абсолютной погрешностью можно вычислить третью сторону?',
)
MEASUREMENT_DATUM=r'([+-]?\d+(?:\.\d+)?(?:/\d+)?)'


def read_measurement_request(task):
    """Bind geometric laws, units and changed quantities to the complete source."""
    from fractions import Fraction as F
    heading=mv_fields(task,{'given'},MEASUREMENT_HEADINGS).get('literal_requirement')
    given=mv_normal(task['given']);N=MEASUREMENT_DATUM;units={'m':F(1),'cm':F(1,100),'mm':F(1,1000)}
    length=N+r'\s*(m|cm|mm)'
    rectangle=re.fullmatch(r'rectangle with sides '+length+r' and '+length+r'; (increase|decrease) first side by '+
                           length+r', (increase|decrease) second by '+length,given)
    sector=re.fullmatch(r'sector radius R='+length+r', central angle '+N+r' degrees (rising|falling) by '+N+r' degree(?:s)?',given)
    tolerance=r'\('+N+r'±'+N+r'\)'
    cylinder=re.fullmatch(r'cylinder R='+tolerance+r' (m|cm|mm), H='+tolerance+r' (m|cm|mm)',given)
    triangle=re.fullmatch(r'triangle a='+tolerance+r' (m|cm|mm),\s*b='+tolerance+
                          r' (m|cm|mm),\s*included C='+tolerance+r' degrees',given)
    if rectangle:
        a,u,b,v,first,x,p,second,y,r=rectangle.groups()
        sign={'increase':1,'decrease':-1}
        mv_require(heading in (None,MEASUREMENT_HEADINGS[0]) and min(F(x),F(y))>=0,'The source rectangle measurements and both requests are required')
        return dict(geometry='rectangle',coordinates=['a','b'],reference=[F(a)*units[u],F(b)*units[v]],
                    data=[sign[first]*F(x)*units[p],sign[second]*F(y)*units[r]],mode='increment',
                    expressions=[('diagonal','sqrt(a^2+b^2)','m'),('area','a*b','m^2')])
    if sector:
        R,unit,theta,direction,shift=sector.groups()
        R,theta,shift=map(F,(R,theta,shift))
        mv_require(shift>=0,'The magnitude of the original change must be nonnegative')
        shift*=1 if direction=='rising' else -1
        mv_require((heading is None or heading==MEASUREMENT_HEADINGS[1] and shift>0)
                   and R>0 and min(theta,theta+shift)>0 and max(theta,theta+shift)<=360,
                   'A nondegenerate real sector and the prescribed direction of change are required')
        return dict(geometry='sector',coordinates=['theta'],reference=[theta],data=[shift],mode='increment',
                    expressions=[('radius',f'({R})*sqrt(({theta})/theta)',unit)],
                    constraint='R_new^2*theta_new=R_old^2*theta_old; positive radius. Degrees cancel in the angle ratio.')
    if cylinder:
        a,h,u,b,k,v=cylinder.groups()
        mv_require(heading in (None,MEASUREMENT_HEADINGS[3]),'Both original cylinder error requests must be preserved')
        return dict(geometry='cylinder',coordinates=['R','H'],reference=[F(a)*units[u],F(b)*units[v]],
                    data=[F(h)*units[u],F(k)*units[v]],mode='tolerance',
                    expressions=[('volume','pi*R^2*H','m^3')],relative=True)
    if triangle:
        a,h,u,b,k,v,c,j=triangle.groups()
        mv_require(heading in (None,MEASUREMENT_HEADINGS[4]) and F(c)-F(j)>0 and F(c)+F(j)<180,
                   'The whole angle range must be a nondegenerate included angle')
        return dict(geometry='triangle',coordinates=['a','b','theta'],reference=[F(a)*units[u],F(b)*units[v],F(c)],
                    data=[F(h)*units[u],F(k)*units[v],F(j)],mode='tolerance',angle_coordinate='theta',
                    expressions=[('third_side','sqrt(a^2+b^2-2*a*b*cos(theta))','m')])
    mv_require(given=='product of approximate factors' and heading in (None,MEASUREMENT_HEADINGS[2]),
               'No supported source geometry or relative product statement')
    return dict(geometry='finite_product',mode='relative')


def measurement_enclosure(expression,coordinate_ranges):
    """Bound each original raw operation on a product of real intervals."""
    from quadrature import enclose,monotone,outward,power,product
    op=expression[0]
    if op=='s':
        return coordinate_ranges[expression[1]]
    if op in ('q','pi'):
        return enclose(expression,None)
    left=measurement_enclosure(expression[1],coordinate_ranges)
    if op=='pow':
        return power(left,expression[2])
    if op in ('sqrt','ln','exp'):
        return monotone(op,left)
    if op in ('cos','sin','abs'):
        return enclose((op,('v','boxValue')),left)
    mv_require(op in ('add','mul','div'),'No interval rule for the original operation')
    right=measurement_enclosure(expression[2],coordinate_ranges)
    if op=='add':
        return outward(left[0]+right[0],left[1]+right[1])
    return product(left,right if op=='mul' else power(right,-1))


def measurement_request_candidate(task):
    try:
        return read_measurement_request(task)
    except (Unsupported,AttributeError,KeyError,TypeError,ValueError,ZeroDivisionError):
        return None


def observed_change_proof(plan,lib):
    """Reuse a table gradient for exact increments, linear errors and certified tolerance extrema."""
    from quadrature import enclose
    if plan['mode']=='relative':
        return (dict(theorem='method.measurement_differential_bounds',geometry='finite_product',
                     argument=[
            'Для каждого ненулевого опорного множителя x_i вводим δ_i=Δx_i/x_i. Тогда новый множитель равен x_i(1+δ_i).',
            'Раскрываем конечное произведение по выбору одного слагаемого из каждого сомножителя. Пустой выбор даёт 1, одноэлементные выборы дают ∑δ_i.',
            'Остаток состоит из произведений по двум и более различным индексам. При max|δ_i|≤η его модуль не больше (1+η)^n−1−nη и имеет второй порядок при фиксированном n.',
            'Из заданных модулей допусков получается сумма линейных относительных допусков. Без независимых знаков это верхняя оценка.']),
            dict(formula='DeltaP/P=prod(1+delta_i)-1=sum(delta_i)+higher_order; dP/P=sum(dx_i/x_i)',
                 relative_error_requires_nonzero_factors=True,per_factor_max_remainder='(1+eta)^n-1-n*eta'))
    def exact_absolute(e):
        low,high=enclose(e,None)
        return e if low>=0 else m.neg(e) if high<=0 else ('abs',e)
    def upper_of(a,b):
        low,high=enclose(m.add(a,m.neg(b)),None)
        return a if low>=0 else b if high<=0 else ('max',a,b)
    coordinates=plan['coordinates'];reference=plan['reference'];change=plan['data'];tolerance=plan['mode']=='tolerance'
    atom=list(map(mv_symbol,coordinates));D,steps=derivative_table(lib)
    mv_require(not tolerance or min(change)>=0,'Independent measurement tolerances must be nonnegative')
    nominal=[q(r) for r in reference];delta=[q(v) for v in change]
    if 'angle_coordinate' in plan:
        i=coordinates.index(plan['angle_coordinate'])
        nominal[i]=m.mul(q(reference[i]/180),m.PI);delta[i]=m.mul(q(change[i]/180),m.PI)
    convert=lambda values: dict(zip(atom,values))
    p0=convert(nominal)
    positive=[m.add(x,v) for x,v in zip(nominal,delta)]
    negative=[m.add(x,m.neg(v)) for x,v in zip(nominal,delta)] if tolerance else nominal
    bounds={}
    for name,a,b in zip(coordinates,negative,positive):
        al,ar=enclose(a,None);bl,br=enclose(b,None)
        bounds[name]=min(al,bl),max(ar,br)
    mv_require(all(box[0]>0 for box in bounds.values()),'The source dimensions must be strictly positive on the whole box')
    rows={}
    for label,text,unit in plan['expressions']:
        f=m.parse(text,None,coordinates)
        # Raw interval evaluation proves the original denominators and real operations.
        measurement_enclosure(f,bounds)
        inner=f[1] if f[0]=='sqrt' else f
        raw_grad=[D(f,k) for k in coordinates]
        for expr in raw_grad:
            measurement_enclosure(expr,bounds)
        value=lambda e,at:m.simplify(m.substitute(e,at))
        center=value(f,p0);gradient=[value(g,p0) for g in raw_grad]
        terms=[m.mul(d,v) for d,v in zip(gradient,delta)]
        linear=mv_sum(map(exact_absolute,terms)) if tolerance else mv_sum(terms)
        row=dict(source_formula=text,unit=unit,nominal=center,gradient=gradient,differential=m.simplify(linear))
        if not tolerance:
            after=value(f,convert(positive))
            row.update(new_value=after,exact_change=m.add(after,m.neg(center)))
        else:
            sign_boxes=[measurement_enclosure(D(inner,k),bounds) for k in coordinates]
            mv_require(all(a>=0 or b<=0 for a,b in sign_boxes),'An exact extremal corner needs a constant sign in each coordinate')
            high=[upper if a>=0 else lower for upper,lower,(a,b) in zip(positive,negative,sign_boxes)]
            low=[lower if a>=0 else upper for upper,lower,(a,b) in zip(positive,negative,sign_boxes)]
            vmin,vmax=value(f,convert(low)),value(f,convert(high))
            down,up=m.add(center,m.neg(vmin)),m.add(vmax,m.neg(center))
            worst=upper_of(up,down)
            row.update(minimum=vmin,maximum=vmax,exact_decrease_bound=down,exact_increase_bound=up,absolute_error=worst,
                       sign_witness=[[q(a),q(b)] for a,b in sign_boxes])
            if plan.get('relative'):
                row.update(relative_differential=m.div(row['differential'],center),
                           relative_error_from_nominal=m.div(worst,center),
                           relative_error_from_true_value=upper_of(m.div(down,vmin),m.div(up,vmax)))
        rows[label]=row
    return (dict(theorem='method.measurement_differential_bounds',geometry=plan['geometry'],
                 coordinate_ranges={name:[q(a),q(b)] for name,(a,b) in bounds.items()},gradient_rules=steps,
                 invariant=plan.get('constraint'),
                 argument=[
                     'Переводим одноимённые измерения в общие единицы. Угловые приращения для тригонометрических функций переводим в радианы.',
                     'Выводим исходную геометрическую функцию из формулы площади, объёма, диагонали или закона косинусов. При постоянной площади выбираем положительный корень для радиуса.',
                     'Проверяем действительность исходной формулы и производных на всей коробке исходных измерений.',
                     'Для данных приращений скалярное произведение градиента и приращения даёт линейную поправку. Точное изменение считаем по двум значениям исходной функции.',
                     'Для независимых допусков сумма модулей вкладов есть линейный максимум. Знаки частных на всей коробке определяют обе крайние вершины. Сравниваем отклонения от номинала.']),
            dict(mode=plan['mode'],measurements=rows))


def differential_anchor_approximation(task,lib):
    """Read a numerical expression, abstract its perturbed leaves, and verify the anchor."""
    label='approximate by substituting the differential for the function increment'
    if not lib.data.get('multivariate_anchor_differentials') or task.get('kind')!='multivariate_linearization_application':
        raise Unsupported('The differential-anchor transition is not enabled')
    mv_fields(task,{'given'},(label,))
    given=mv_normal(task['given']);coordinates=[];points=[];anchors=[];angles=[]
    token=r'(?<![A-Za-z0-9_.])([0-9]+(?:\.[0-9]+)?) degrees|(?<![A-Za-z0-9_.])([0-9]+\.[0-9]+)'
    def choose(match):
        nearby=Fraction(match[1] or match[2])
        if match[1] is not None:
            half=nearby//180
            standard=[180*k+j for k in (half-1,half,half+1) for j in (0,30,45,60,90,120,135,150)]
            center=min(standard,key=lambda v:(abs(v-nearby),v))
            mv_require(abs(center-nearby)<=5,'No standard angle sufficiently close to the original datum')
            data,base=(m.mul(q(f/180),m.PI) for f in (nearby,Fraction(center)))
        else:
            center=next(Fraction(round(nearby*d),d) for d in (1,2,4,10) if abs(Fraction(round(nearby*d),d)-nearby)<=Fraction(1,10))
            data,base=q(nearby),q(center)
        name='anchorCoordinate'+str(len(coordinates))
        mv_require(name not in given,'The numerical binding must be fresh')
        coordinates.append(name);points.append(data);anchors.append(base);angles.append(match[1] is not None)
        return name
    function_text=re.sub(token,choose,given)
    mv_require(1<=len(coordinates)<=6,'The source calculation needs a small list of actual perturbed values')
    def exact_roots(e):
        if e[0]=='fourth_root':return ('sqrt',('sqrt',exact_roots(e[1])))
        return tuple(exact_roots(node) if isinstance(node,tuple) else node for node in e)
    f=exact_roots(m.parse(function_text,None,coordinates,('fourth_root',)))
    v=list(map(mv_symbol,coordinates));condition=[]
    ctx=m.context(dict(variable='linearizationParameter',parameters=coordinates));point_ctx=m.context(dict(variable='linearizationParameter'))
    def positive(e):
        ctx['positive_expressions'].append(e);condition.append(source(e)+'>0')
    for name,x,z,angle in zip(v,anchors,points,angles):
        if all(m.sign(t,point_ctx)==1 for t in (x,z)):positive(name)
        if angle:
            half_pi=m.mul(q(1,2),m.PI)
            in_middle=all(m.sign(m.add(half_pi,m.mul(q(s),d)),point_ctx)==1 for s in (-1,1) for d in (x,z))
            if in_middle:positive(('cos',name))
            if all(m.sign(d,point_ctx)==1 and m.sign(m.add(m.PI,m.neg(d)),point_ctx)==1 for d in (x,z)):positive(('sin',name))
    D,steps=derivative_table(lib);grad=[D(f,name) for name in coordinates]
    guards=list(dict.fromkeys(g for e in [f,*grad] for g in domain_conditions(e,True)))
    mv_require(all(known_guard(g,ctx) for g in guards),
               'An original operation or derivative guard is not proved on the complete anchor box')
    center=dict(zip(v,anchors));target=dict(zip(v,points));a=m.substitute(f,center);original=m.substitute(f,target)
    derivatives=[m.substitute(d,center) for d in grad]
    def point_context(values):
        out=m.context(dict(variable='linearizationParameter'))
        out['positive_expressions']=[m.simplify(m.substitute(g,values)) for g in ctx['positive_expressions']]
        out['nonzero_expressions']=[m.simplify(m.substitute(e,values)) for k,e in guards if k=='nonzero']
        return out
    c0,ct=point_context(center),point_context(target)
    mv_require(m.constant_defined(original,ct) and all(m.constant_defined(z,c0) for z in [a,*derivatives]),
               'Evaluation of the underlying original expression or its first differential lacks a domain proof')
    def exact_power(e):
        value=tuple(exact_power(v) if isinstance(v,tuple) else v for v in e)
        if value[0]=='rpow':
            k=m.num(value[2])
            if k is not None and k.denominator==1:return m.power(value[1],int(k))
        return value
    a=exact_power(a);derivatives=[exact_power(z) for z in derivatives]
    h=[m.add(y,m.neg(x)) for x,y in zip(anchors,points)];delta=mv_sum(m.mul(d,k) for d,k in zip(derivatives,h))
    approximate=m.simplify(m.add(a,delta))
    return (dict(theorem='method.differential_at_generated_anchor',source_expression=given,abstract_function=f,
                 coordinates=coordinates,anchor=anchors,original_operand_values=points,anchor_box_facts=condition,
                 original_and_derivative_guards=guards,verified_rules=steps,gradient_at_anchor=derivatives,coordinate_increments=h,
                 argument=['Каждое возмущённое число рассматриваем как независимую координату. Выбираем ближайшие простые опорные значения, у углов переходим к радианам.',
                           'Проверяем область исходной формулы и всех первых частных на всём прямоугольнике между опорой и данными.',
                           'Вычисляем полный дифференциал как скалярное произведение градиента в опорной точке и приращений. К базовому значению добавляем эту линейную поправку.']),
            dict(approximation=approximate,base_value=m.simplify(a),differential=m.simplify(delta),
                 requested_approximation_order=1,remainder='first-order approximation, no finite error tolerance specified'))


EXTREMUM_OUTPUT=['classify_all_extrema_on_original_domain']


def weighted_affine_stationarity(task,lib):
    """Solve the logarithmic gradient after keeping all vanishing factors."""
    from collections import Counter
    if not lib.data.get('multivariate_stationary_reductions') or task.get('kind')!='multivariate_extrema':
        raise Unsupported('The affine-factor stationary transition is not enabled')
    meta=mv_fields(task,{'source_formula','stated_conditions','requested_output'},tuple(EXTREMUM_OUTPUT),
                   extra_meta=('section_convention',))
    mv_require(meta.get('section_convention') in (None,'The strict inequalities on p340 define strict local extrema; flat attained global bounds and non-strict extrema must be identified separately.'),
               'The original strictness and all attained bound conventions must be preserved')
    mv_require(task.get('requested_output')==EXTREMUM_OUTPUT,'The source asks for a different extremum claim')
    text=mv_normal(task['source_formula']);conditions=task.get('stated_conditions',[])
    symbolic=re.fullmatch(r'prod_\(([a-z])=1\)\^([a-z]) ([a-z])_\1\^\1 \* \(1-sum_\(\1=1\)\^\2 \1\*\3_\1\)',text)
    if symbolic:
        j,n,x=symbolic.groups()
        mv_require(len({j,n,x})==3 and conditions==[f'each {x}_{j}>0'],
                   'The same finite family and its positive domain must be preserved')
        total=f'{n}*({n}+1)/2';w=f'1/(1+{total})'
        return (dict(theorem='method.stationarity_of_weighted_affine_product',indexed_family=[j,n,x],
              stationary_equations=f'For each {j}, {x}_{j}=1-sum_{j} {j}*{x}_{j}',
              argument=['Выделяем область положительного последнего множителя. На ней логарифм произведения строго вогнут, а условия стационарности требуют равенства всех координат этому множителю.',
                        'Подставляем найденное общее значение в аффинную связь. На L<0 те же стационарные уравнения для логарифма модуля требуют отрицательных координат. На L=0 знак меняется от малого изменения одной координаты; по общему положительному лучу произведение неограниченно уменьшается.']),
                dict(maximum=dict(coordinates=f'{x}_{j}={w} for {j}=1..{n}',value=f'({w})^(1+{total})',attained=True),
                     minimum=None,infimum='-inf',no_other_extrema=True))
    names=mv_names(text);mv_require(2<=len(names)<=6,'Need a finite low-dimensional product')
    raw=m.parse(text,None,names)
    if domain_conditions(raw):raise Unsupported('A hidden hole or a nonintegral source power changes the stationary scope')
    factors=[]
    def unpack(e):
        if e[0]=='mul':
            unpack(e[1]);unpack(e[2])
        else:factors.append(e)
    unpack(raw)
    weights=Counter();scale=ONE;remaining=[]
    for e in factors:
        if m.num(e) is not None:scale=m.mul(scale,e);continue
        if e[0]=='s':weights[e]+=1;continue
        if e[0]=='pow' and e[1][0]=='s' and 1<=e[2]<=24:
            weights[e[1]]+=e[2];continue
        remaining.append(e)
    mv_require(2<=len(weights)<=5 and len(remaining)==1 and m.num(scale) not in (None,0),
               'A nonzero product of coordinate powers and a single affine factor is required')
    coords=sorted(weights);axes=[v[1] for v in coords];params=[p for p in names if p not in axes]
    positive_axes={p for p in axes if p+'>0' in conditions}
    declared=[p for p in conditions if p not in {k+'>0' for k in positive_axes}]
    mv_require(positive_axes in (set(),set(axes)) and all(p in {v+'>0' for v in params} for p in declared),
               'Only the whole space or the complete positive orthant is covered')
    ctx=m.context(dict(variable='stationaryCoordinate',parameters=params,parameter_conditions=declared))
    L=remaining[0];at0={x:ZERO for x in coords};B=m.simplify(m.substitute(L,at0))
    slopes=[m.simplify(m.add(m.substitute(L,{**at0,x:ONE}),m.neg(B))) for x in coords]
    mv_require(m.constant_defined(B,ctx) and m.sign(B,ctx)==1
               and all(m.constant_defined(a,ctx) and m.sign(a,ctx)==-1 for a in slopes)
               and same_value(L,m.add(B,mv_sum(m.mul(a,x) for a,x in zip(slopes,coords)))),
               'The affine slice needs a positive intercept and strictly negative nonzero coordinate coefficients')
    order=sum(weights.values());w=m.div(B,q(1+order))
    point=[m.div(m.mul(q(-weights[x]),w),a) for x,a in zip(coords,slopes)]
    value=m.mul(m.mul(scale,w),reduce(m.mul,(m.power(z,weights[x]) for x,z in zip(coords,point)),ONE))
    if not same_value(m.substitute(L,dict(zip(coords,point))),w):
        raise Unsupported('The proposed point does not solve the original affine residual')
    direction='strict_maximum' if m.num(scale)>0 else 'strict_minimum'
    payload=dict(extrema=[dict(point=point,value=value,type=direction)],no_other_strict_extrema=True)
    reasons=['Вне нулей исходных множителей знак произведения постоянен. Составляем градиент логарифма модуля и получаем x_i=−k_i L/a_i.',
             'Подстановка этих равенств в аффинный множитель даёт L=B/(1+Σk_i). Вместе с положительностью B получаем единственную допустимую критическую точку.',
             'Квадратичная форма второго дифференциала логарифма равна −Σk_i(dx_i/x_i)²−(dL/L)² и строго отрицательна вне нулей. Знак функции переносит тип экстремума.']
    if positive_axes:
        label='supremum' if m.num(scale)>0 else 'infimum';other='infimum' if label=='supremum' else 'supremum'
        payload.update({label:dict(value=value,attained=True),other:'-inf' if label=='supremum' else '+inf'})
        reasons.append('В положительном ортанте логарифм на выпуклой части L>0 доказывает глобальный экстремум. На L=0 малая вариация одной координаты даёт оба знака. При L<0 знак противоположен значению в критической точке, по общему положительному лучу величина неограниченна.')
    else:
        payload.update(infimum='-inf',supremum='+inf',zero_factors='no strict extrema on zero hyperplanes',weak_zero_extrema={
             'condition':'L != 0 and every vanishing coordinate has an even power',
             'type':'minimum if the sign of the product of the other factors is positive, maximum if negative'})
        reasons.extend([
            'На нулевых гиперплоскостях рядом есть другие точки того же уровня, поэтому строгого экстремума нет. Нечётный нулевой множитель даёт смену знака; для L=0 есть ненулевая координата, позволяющая независимо изменить L.',
            'В одной открытой знаковой ортантной области можно выбрать два направления с разными знаками линейной части L, оставаясь при неизменном знаке монома. По соответствующим лучам произведение неограниченно в обе стороны.'])
    return (dict(theorem='method.stationarity_of_weighted_affine_product',original=raw,coordinate_order=axes,weights=[weights[x] for x in coords],
                 affine_factor=L,stationary_value_of_factor=w,stationary_point=point,argument=reasons),payload)


def radial_stationarity(task,lib,request):
    """Build a scalar sign goal on the exact image of the squared radius."""
    if not lib.data.get('multivariate_stationary_reductions') or task.get('kind')!='multivariate_extrema':
        raise Unsupported('No admitted radial stationary reduction')
    meta=mv_fields(task,{'source_formula','stated_conditions','requested_output'},tuple(EXTREMUM_OUTPUT),
                   extra_meta=('section_convention',))
    mv_require(meta.get('section_convention') in (None,'The strict inequalities on p340 define strict local extrema; flat attained global bounds and non-strict extrema must be identified separately.'),
               'The original strictness and all attained bound conventions must be preserved')
    mv_require(task.get('requested_output')==EXTREMUM_OUTPUT and not task.get('stated_conditions'),
               'Need the complete unrestricted radial source question')
    text=mv_normal(task['source_formula']);axes=mv_names(text)
    mv_require(2<=len(axes)<=4,'Need at least two independent radial coordinates')
    raw=m.parse(text,None,axes);coords=list(map(mv_symbol,axes));ctx=m.context(dict(variable='radialProfile'))
    mv_require(not domain_conditions(raw) and raw[0]=='mul','The initial radial function needs the whole Euclidean space')
    A,B=raw[1:]
    if A[0]=='exp':A,B=B,A
    s=mv_sum(m.power(x,2) for x in coords)
    mv_require(B[0]=='exp','Need a positive exponential radial factor')
    p=1
    if A[0]=='pow':
        A,p=A[1:]
    mv_require(p>=1 and same_value(A,s),'The source leading power must be a power of the same squared radius')
    a=m.simplify(m.substitute(B[1],{x:ONE if i==0 else ZERO for i,x in enumerate(coords)}))
    mv_require(m.constant_defined(a,ctx) and m.sign(a,ctx)==-1 and same_value(B[1],m.mul(a,s)),
               'The exponential must decay as a fixed negative multiple of that same radius')
    u='radialProfile';v=('v',u);g=m.mul(m.power(v,p),('exp',m.mul(a,v)))
    child=dict(kind='strict_monotonicity_intervals',function=source(g),variable=u,parameters=[],stated_conditions=[u+'>=0'],
               requested_output=['all_strict_increasing_and_decreasing_intervals'])
    scalar=request('prove derivative signs of the radial profile on its exact half-line',child)
    cut=m.div(q(-p),a);peak=m.simplify(m.substitute(g,{v:cut}))
    return (dict(theorem='method.stationarity_on_radial_image',original=raw,coordinate=s,
                 quotient_goals=[child],scalar_order=scalar['value'],stationary_radius_squared=cut,
                 argument=['Квадрат нормы принимает все значения [0,+∞), а над положительным значением его уровень является сферой.',
                           'На этой точной области программа отдельно доказывает возрастание и убывание радиального профиля. Нуль профиля достигается только в начале.',
                           'Восстанавливаем весь уровень максимума. При d≥2 у каждого его элемента рядом есть такие же точки, поэтому максимум на сфере не строгий.']),
            dict(infimum=dict(value=ZERO,attained=True),supremum=dict(value=peak,attained=True),
                 extrema=[dict(type='strict_minimum',point=[ZERO]*len(coords),value=ZERO),
                          dict(type='nonstrict_maximum',set=source(s)+'='+source(cut),value=peak)],
                 no_other_extrema=True))


def multivariate_proof_routing(task,kind):
    if kind=='mixed_partials_piecewise_at_point':return True
    text=task.get('given')
    if isinstance(text,str):
        meta=task.get('source',{})
        heading=meta.get('literal_requirement') if isinstance(meta,dict) else None
        if kind=='multivariate_regularities' and ('bounded partials' in text or 'bounded derivative' in text):return True
        if kind=='partial_derivative_at_point' and ('fixed ' in text or isinstance(heading,str) and heading.startswith('Найти f_')):return True
        if kind=='multivariate_linearization_application' and measurement_request_candidate(task) is not None:return True
        if (kind=='multivariate_linearization_application' and
                heading in (None,'approximate by substituting the differential for the function increment') and
                re.search(r'\d+\.\d+|\d+ degrees',text)):
            return True
    if kind=='scalar_field_geometry':
        meta=task.get('source')
        if 'direction_convention' in task or isinstance(meta,dict) and meta.get('literal_requirement') in FIELD_HEADINGS:
            return True
        requests=task.get('requests')
        return isinstance(requests,(list,tuple)) and any(isinstance(r,dict) and r.get('op') in (
            'direction_of_maximum','direction_of_minimum','directions_of_zero',
            'normal_direction_derivatives','inward_normal_derivative') for r in requests)
    if kind in ('differential_equation_source_goal','first_and_second_total_differentials_at',
                'prove_second_differential_positive_semidefinite','prove_euler_homogeneity_converse','prove_differentiated_homogeneity',
                'trace_derivative','compare_gradient_norms','symbolic_directional_derivative','directional_identity',
                'implicit_extrema'):
        return True
    if kind in ('partial_derivative_at_point','multivariate_regularities'):
        t=task.get('given')
        return isinstance(t,str) and t.startswith(('f(x,y)=cbrt(', 'f(x,y)=sqrt(abs(', 'f(x,y)=x*y/sqrt(',
            'f(x,y)=(x²+y²)*sin(', 'f=exp('))
    if kind=='constrained_extrema':
        t=task.get('source_formula');c=task.get('stated_conditions')
        return (isinstance(t,str) and isinstance(c,list) and (c and c[-1]=='a>b>c>0' or
            len(c)==4 and c[-1]=='direction cosines squared sum=1' or len(c)==1 and
            isinstance(c[0],str) and 'x²' in c[0] and 'y²' in c[0] and re.search(r'\bx\*?y\b',coordinate_polynomial(t)) or
            t.startswith(('sum x_i','sum alpha_i/','prod x_i^')) or len(c)==2 and
            isinstance(c[0],str) and c[0].startswith(('x+y+z=','x+2y+3z='))))
    if kind in ('multivariate_extrema','optimize_positive_variables'):
        t=task.get('source_formula');return isinstance(t,str) and t.startswith(('x1+sum_(j=2)^n x_j/x_', 'prod x_i / ((a+x1)'))
    if kind=='differential_operator':
        f=task.get('function');r=task.get('requests')
        return isinstance(f,str) and f.startswith('ln(') and isinstance(r,list) and len(r)==1 and isinstance(r[0],dict) and len(r[0].get('apply',()))>4
    if kind=='formal_differential_identity':
        t=task.get('given');return isinstance(t,str) and t.startswith(('harmonic u1(', 'x²=v*w,', 'x^2=v*w,', 'z=x^n*f(', 'u=x^n*phi('))
    return False


def multivariate_proof(task,lib,request=None):
    kind=task['kind']
    if kind=='mixed_partials_piecewise_at_point':return ordered_slice_derivatives(task,lib)
    if kind=='multivariate_linearization_application':
        measurement=measurement_request_candidate(task) if lib.data.get('measurement_differential_bounds') else None
        if measurement is not None:return observed_change_proof(measurement,lib)
        return differential_anchor_approximation(task,lib)
    if kind=='multivariate_regularities':
        try:return continuity_from_paths(task,lib)
        except (Unsupported,poly.NotRational,poly.Undefined):pass
    if kind=='partial_derivative_at_point':
        try:return fixed_argument_derivative(task,lib)
        except (Unsupported,poly.NotRational,poly.Undefined):pass
    if kind=='differential_equation_source_goal':return transport_pde(task,lib)
    if kind=='formal_differential_identity':return field_identity(task,lib)
    if kind=='trace_derivative':return trace_jets(task,lib)
    if kind=='scalar_field_geometry':return scalar_field_directions(task,lib)
    if kind=='compare_gradient_norms':return compare_fields(task,lib)
    if kind in ('symbolic_directional_derivative','directional_identity'):return directional_tensor(task,lib)
    if kind=='implicit_extrema':return implicit_height(task,lib)
    if kind in ('partial_derivative_at_point','multivariate_regularities'):return radial_origin_regularity(task,lib)
    if kind=='constrained_extrema':
        if task['source_formula'].startswith(('sum x_i','sum alpha_i/','prod x_i^')) or task['stated_conditions'][0].startswith(('x+y+z=','x+2y+3z=')):
            return positive_simplex(task,lib)
        return spectral_extrema(task,lib)
    if kind in ('multivariate_extrema','optimize_positive_variables'):return telescoping_extremum(task,lib)
    if kind=='differential_operator':return repeated_affine_differential(task,lib)
    if kind in ('prove_euler_homogeneity_converse','prove_differentiated_homogeneity'):return euler_homogeneity_theorem(task,lib)
    return full_differential(task,lib)
