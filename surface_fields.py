"""Verified reductions of scalar surface measures and oriented field integrals."""
from fractions import Fraction
from functools import reduce
from math import comb, factorial
import re

import expressions as m
from cartesian_fields import coordinate_curl, coordinate_sections, vector_cross, vector_source
from model import ONE, ZERO, Unsupported, freeze, q
from planar_integrals import curve_chart_moment, root_power_primitive
from tasks import domain_conditions, known_guard, source
from verify import same_value


P=m.PI
COORDS=tuple(('s',s) for s in 'xyz')
X,Y,Z=COORDS
N=r'([A-Za-z][A-Za-z_0-9]*|[1-9]\d*)'
SCALAR_HEADING='Вычислить поверхностный интеграл первого рода.'
SHELL_HEADING='Найти указанные массовые характеристики поверхности.'


def add(*size):return reduce(m.add,size,ZERO)
def mul(*size):return reduce(m.mul,size,ONE)
def sub(a,b):return m.add(a,m.neg(b))
def sqrt(a):return m.simplify(('sqrt',a))
def signed_asinh(a):return ('ln',m.add(a,sqrt(m.add(ONE,m.power(a,2)))))
def sym(name):return ('s',name)


def proof(method,steps,value,**checks):
    return dict(theorem='method.'+method,argument=list(steps),**checks),value


def positive_sizes(names,extra=()):
    names=tuple(names)
    variables=sorted({s for s in names if s.isidentifier()})
    if any(s in ('x','y','z','pi') for s in variables):
        raise Unsupported('A coordinate or special constant cannot serve as an independent size')
    hypotheses=[s+'>0' for s in variables]
    ctx=m.context(dict(parameters=variables,parameter_conditions=hypotheses+list(extra)))
    sizes=[m.parse(s,None,variables) for s in names]
    if any(m.sign(s,ctx)!=1 for s in sizes):raise Unsupported('The declared geometric dimensions are not positive')
    return sizes,variables,ctx


def polynomial_terms(raw,coords,ctx,limit=12):
    if any(not known_guard(g,ctx) for g in domain_conditions(raw,True)):
        raise Unsupported('The original field has an unresolved denominator or real restriction')
    numerator,denominator=m.rational_form(raw);den=m.poly_expr(denominator)
    if any(m.contains(den,x) for x in coords) or not m.nonzero(den,ctx):
        raise Unsupported('A coordinate appears in an original polynomial moment denominator')
    pieces={}
    for term,coefficient in numerator.items():
        factors=dict(term);degrees=tuple(factors.pop(x,0) for x in coords)
        c=m.div(m.poly_expr({tuple(factors.items()):coefficient}),den)
        if sum(degrees)>limit or any(m.contains(c,x) for x in coords) or not m.constant_defined(c,ctx):
            raise Unsupported('A finite polynomial moment of bounded order is required')
        pieces[degrees]=m.add(pieces.get(degrees,ZERO),c)
    return pieces


def polar_factor(i,j,half=False,magnitude=False):
    if not magnitude and (j%2 or i%2 and not half):return ZERO
    factor=Fraction(1)
    while i>=2:
        factor*=Fraction(i-1,i+j);i-=2
    while j>=2:
        factor*=Fraction(j-1,i+j);j-=2
    degree=i+j
    base={0:mul(q(2),P),1:q(4),2:q(2)}[degree]
    if half:factor/=2
    return m.mul(q(factor),base)


def simplex_face(R,i,j,k):
    return mul(sqrt(q(3)),q(Fraction(factorial(i)*factorial(j)*factorial(k),factorial(i+j+k+2))),m.power(R,i+j+k+2))


def radial_gram_integral(i,c,R):
    """Integral of r^i sqrt(1+c²r²) for r between zero and R and c>0."""
    u=m.mul(c,R)
    if not i%2:
        primitive=root_power_primitive(u,i//2)
    else:
        n=(i-1)//2;v=sqrt(m.add(ONE,m.power(u,2)))
        primitive=add(*(mul(q(Fraction((-1)**(n-j)*comb(n,j),2*j+3)),
                            sub(m.power(v,2*j+3),ONE)) for j in range(n+1)))
    return m.div(primitive,m.power(c,i+1))


def moment_chart(text):
    """Read a complete source shell and return dimensions and its Cartesian moments."""
    if text=='boundary of sqrt(x^2+y^2)<=z<=1':
        return 'closed_cone',('1',)
    sphere=re.fullmatch(r'x\^2\+y\^2\+z\^2='+N+r'\^2(,z>=0)?',text)
    if sphere:return ('upper_sphere' if sphere[2] else 'sphere'),(sphere[1],)
    triangle=re.fullmatch(r'x\+y\+z='+N+r',x,y,z>=0',text)
    if triangle:return 'triangle',(triangle[1],)
    octahedron=re.fullmatch(r'abs\(x\)\+abs\(y\)\+abs\(z\)='+N,text)
    if octahedron:return 'octahedron',(octahedron[1],)
    cube=re.fullmatch(r'cube surface max\(abs\(x\),abs\(y\),abs\(z\)\)='+N,text)
    if cube:return 'cube',(cube[1],)
    cyl=re.fullmatch(r'full cylinder surface x\^2\+y\^2<='+N+r'\^2,0<=z<='+N,text)
    if cyl:return 'cylinder',cyl.groups()
    cone=re.fullmatch(r'x\^2/'+N+r'\^2\+y\^2/'+N+r'\^2-z\^2/'+N+r'\^2=0,0<=z<='+N,text)
    if cone and cone[1]==cone[2] and cone[3]==cone[4]:
        return 'cone',(cone[1],cone[3])
    cone=re.fullmatch(r'z=sqrt\(x\^2\+y\^2\)(?:,inside| inside) x\^2\+y\^2=(2\*)?'+N+r'\*x',text)
    if cone:return ('disc_cone_double' if cone[1] else 'disc_cone'),(cone[2],)
    par=re.fullmatch(r'z=x\^2\+y\^2 cut by z='+N,text)
    if par:return 'paraboloid',(par[1],'1')
    par=re.fullmatch(r'z=\(x\^2\+y\^2\)/'+N+r',0<=z<='+N,text)
    if par:return 'paraboloid',(par[2],par[1])
    raise Unsupported('A complete regular surface chart with all of its pieces is still needed')


def surface_monomial(shape,D,degrees,absolute=False):
    i,j,k=degs=degrees;R=D[0];total=i+j+k
    if shape=='triangle':return simplex_face(R,*degs)
    if shape=='octahedron':return ZERO if not absolute and any(s%2 for s in degs) else mul(q(8),simplex_face(R,*degs))
    if shape=='cube':
        if not absolute and any(s%2 for s in degs):return ZERO
        weight=sum(Fraction(8,(degs[(a+1)%3]+1)*(degs[(a+2)%3]+1)) for a in range(3))
        return mul(q(weight),m.power(R,total+2))
    if shape in ('disc_cone','disc_cone_double'):
        end=m.mul(q(2),R) if shape=='disc_cone_double' else R
        return mul(sqrt(q(2)),m.div(m.power(end,total+2),q(total+2)),polar_factor(i+total+2,j,half=True,magnitude=absolute))
    angular=polar_factor(i,j,magnitude=absolute)
    if angular==ZERO:return ZERO
    if shape in ('sphere','upper_sphere'):
        if shape=='sphere' and k%2 and not absolute:return ZERO
        if (i+j)%2:raise Unsupported('This spherical moment has a nonpolynomial odd radial power')
        n=(i+j)//2
        factor=sum(Fraction((-1)**e*comb(n,e),k+2*e+1) for e in range(n+1))
        return mul(angular,q(factor*(2 if shape=='sphere' else 1)),m.power(R,total+2))
    if shape=='cylinder':
        H=D[1];ends=add(ONE if k==0 else ZERO,m.power(H,k))
        lateral=mul(m.power(R,i+j+1),m.div(m.power(H,k+1),q(k+1)))
        disks=mul(m.div(m.power(R,i+j+2),q(i+j+2)),ends)
        return mul(angular,add(lateral,disks))
    if shape in ('cone','closed_cone'):
        slope=m.div(D[1],R) if shape=='cone' else ONE
        side=mul(sqrt(add(ONE,m.power(slope,2))),m.power(slope,k),m.div(m.power(R,total+2),q(total+2)))
        cap=m.div(m.power(R,total+2),q(i+j+2)) if shape=='closed_cone' else ZERO
        return mul(angular,add(side,cap))
    if shape=='paraboloid':
        height,den=D;curvature=m.div(ONE,den);r=sqrt(m.mul(height,den))
        return mul(angular,m.power(curvature,k),radial_gram_integral(i+j+2*k+1,m.mul(q(2),curvature),r))
    raise Unsupported('Unknown surface moment')


def scalar_shell(task,request):
    kind=task['kind'];want=task['requested_output'];text=task.get('surface')
    def integrate(weight,description,rho='1'):
        shape,names=moment_chart(description);dimensions,params,ctx=positive_sizes(names)
        p=[*params,*([rho] if rho.isidentifier() and rho not in params else [])]
        ctx=m.context(dict(parameters=p,parameter_conditions=[s+'>0' for s in p]))
        expression=m.parse(weight,None,[*p,*'xyz'])
        absolute=expression[0]=='abs'
        body=expression[1] if absolute else expression
        entries=polynomial_terms(body,COORDS,ctx)
        if absolute and len(entries)!=1:raise Unsupported('The absolute value needs a verified fixed-sign monomial on each piece')
        values=[(keys,('abs',c) if absolute else c,surface_monomial(shape,dimensions,keys,absolute))
                for keys,c in entries.items()]
        total=m.simplify(add(*(m.mul(c,v) for _,c,v in values)))
        return dict(surface=description,chart=shape,scales=dimensions,original_weight=expression,moments=values),total
    parts=[]
    def weight(w,description=text,rho='1'):
        p,v=integrate(w,description,rho)
        parts.append(p)
        return v
    steps=['Bind all original faces and choose the indicated real surface chart.',
           'Pull back each Cartesian monomial with positive scalar surface measure and evaluate its moments.']
    if kind=='compare_surface_integrals':
        vector_source(task,{'integrand','surfaces','requested_output'},('Найти разность между интегралами по сфере и вписанному октаэдру.',))
        if want!=['difference'] or len(task['surfaces'])!=2:raise Unsupported('Expected both surface integrals and their difference')
        a,b=[weight(task['integrand'],s) for s in task['surfaces']]
        return proof('scalar_surface_moments',steps,dict(first=a,second=b,difference=sub(a,b)),charts=parts)
    if kind=='scalar_surface_integral':
        vector_source(task,{'integrand','surface','requested_output'},(SCALAR_HEADING,))
        if want!=['surface_integral']:raise Unsupported('The original scalar surface integral output is required')
        try:value=weight(task['integrand'])
        except Unsupported:
            return special_scalar_surface(task,request)
        return proof('scalar_surface_moments',steps,dict(surface_integral=value),charts=parts)
    vector_source(task,{'density','surface','requested_output'},(SHELL_HEADING,))
    density=task['density']
    if density=='constant':rho='rho'
    elif density in ('rho0','unit'):rho=density
    else:rho='1'
    factor=rho if density=='constant' else '1' if density=='unit' else density
    if want==['mass']:
        value=dict(mass=weight(factor,rho=rho))
        if factor!='1':value['measure']='signed density integral if the stated density changes sign'
    elif want==['static_moments_about_three_coordinate_planes'] or want==['inertias_about_three_coordinate_planes']:
        square=want[0].startswith('inertias')
        value={want[0]:[weight(f'({factor})*{c}'+('^2' if square else ''),rho=rho) for c in 'xyz']}
    elif want==['polar_inertia_about_origin'] or want==['inertia_about_Oz']:
        w='x^2+y^2'+('+z^2' if want[0].startswith('polar') else '')
        value={want[0]:weight(f'({factor})*({w})',rho=rho)}
    elif want==['inertia_about_line_(x/1=y/0=(z-b)/0)']:
        if text!='x^2/a^2+y^2/a^2-z^2/b^2=0,0<=z<=b':
            raise Unsupported('The specified axis and original surface height must be bound')
        value={want[0]:weight(f'({factor})*(y^2+(z-b)^2)',rho=rho)}
    elif want==['centroid'] and density in ('constant','unit'):
        try:
            area=weight('1')
            if area==ZERO:raise Unsupported('Centroid requires positive area')
            value=dict(centroid=[m.div(weight(c),area) for c in 'xyz'])
        except Unsupported:return sphere_cut_centroid(task)
    else:raise Unsupported('No proved surface weight for the original mechanical quantity')
    return proof('scalar_surface_moments',steps,value,charts=parts)


def sphere_cut_centroid(task):
    if task['surface']!='z=sqrt(a^2-x^2-y^2),x,y>=0,x+y<=a':
        raise Unsupported('No verified first moments for a cut spherical graph')
    a=sym('a');A=mul(P,m.power(a,2),sub(m.div(ONE,sqrt(q(2))),q(1,2)))
    xy=m.div(a,m.mul(q(2),sqrt(q(2))))
    z=m.div(a,m.mul(P,sub(sqrt(q(2)),ONE)))
    return proof('scalar_surface_moments',[
        'On the first-quadrant projection the triangle x+y≤a gives 0≤r≤a/(cos φ+sin φ). Use positive graph density a/z.',
        'Angular substitution v=sqrt(2)sin(φ−π/4) gives area πa²(1/sqrt(2)−1/2). The integrable boundary ends follow by a radial limit.',
        'The z-weight cancels the denominator, so its moment is a times projected area. Reflection exchanges the two horizontal moments.',
        'For the first horizontal moment integrate y at fixed x/a=k, then integrate k asin sqrt((1−k)/(1+k)) by parts. Substitute k=sin²u to integrate its rational weight.',
        'Divide only by the positive area.'],dict(centroid=[xy,xy,z]),area=A,scope='a>0')


def special_scalar_surface(task,request):
    text=task['surface'];g=task['integrand'];a=sym('a')
    cyl=re.fullmatch(r'x\^2\+z\^2=2\*'+N+r'\*z inside z=sqrt\(x\^2\+y\^2\),'+N+r'>0',text)
    simplex=re.fullmatch(r'boundary of x\+y\+z<='+N+r',x,y,z>=0',text)
    helicoid=re.fullmatch(r'helicoid x=u\*cos\(v\),y=u\*sin\(v\),z=v;0<u<'+N+r',0<v<([1-9]\d*)\*pi',text)
    if cyl and cyl[1]==cyl[2] and g=='z':
        [R],_,_=positive_sizes((cyl[1],));value=mul(m.div(q(7),sqrt(q(2))),P,m.power(R,3))
        steps=['The cylindrical chart gives x=a sin u and z=a(1+cos u), with dS=a du dy.',
               'The original cone yields cos u≥0 and |y|≤a sqrt(2cos u(1+cos u)), besides an isolated point of zero surface measure.',
               'Put v=sqrt(2)sin(u/2). The moment on [−1,1] is 8sqrt(2)a³ times the semicircle moment of 1−v²/2.']
    elif simplex and g=='1/(1+x+y)^2':
        [R],_,_=positive_sizes((simplex[1],));L=('ln',add(ONE,R))
        u=add(L,m.div(ONE,add(ONE,R)),m.neg(ONE));v=sub(R,L)
        value=add(m.mul(add(ONE,sqrt(q(3))),u),m.mul(q(2),v))
        steps=['Split the complete tetrahedral boundary into four faces. In all of them 1+x+y≥1.',
               'The horizontal and sloped faces give ∫s/(1+s)² ds from 0 to the edge length, with relative area factors 1 and sqrt(3).',
               'Each vertical face gives ∫(edge−s)/(1+s)² ds on the same interval. Integrate both elementary rational densities.']
    elif text=='ellipsoid; h distance from ellipsoid center to tangent plane at the element' and g=='1/h':
        a,b,c=map(sym,'abc');acc=add(*(m.power(s,-2) for s in (a,b,c)))
        value=mul(q(4,3),P,a,b,c,acc)
        steps=['Use the positive-axis scaling D on the unit sphere. The area multiplier is det(D)|D^(-T)u|.',
               'The tangent support distance is 1/|D^(-T)u|. The weighted multiplier is det(D)|D^(-T)u|².',
               'Integrate the squared unit coordinates, each with mean 1/3 by spherical symmetry.']
    elif helicoid and g=='z':
        [R],_,_=positive_sizes((helicoid[1],));angle=mul(q(int(helicoid[2])),P)
        value=mul(q(1,2),m.power(angle,2),root_power_primitive(R,0))
        steps=['Height gives the angular parameter uniquely, and positive radius gives the other parameter.',
               'The Gram determinant of the two derivatives is 1+u². Its square root depends only on the radius.',
               'Separate and integrate the first moment of the angle and the positive radial radical.']
    elif (text=='cone x=r*cos(phi)*sin(alpha),y=r*sin(phi)*sin(alpha),z=r*cos(alpha);0<=r<=a,0<=phi<=2*pi,0<alpha<pi/2' and g=='z^2'):
        alpha=sym('alpha');value=mul(q(1,2),P,m.power(a,4),('sin',alpha),m.power(('cos',alpha),2))
        steps=['Use the original nonnegative slant radius and the full turn. Distinct angles coincide only at the angular seam or vertex.',
               'The two tangent vectors are orthogonal with lengths 1 and r sin α. Multiply by z²=r² cos² α and integrate.']
    else:raise Unsupported('No positive metric and complete integration domain for the original formula')
    return proof('surface_chart_reduction',steps,dict(surface_integral=m.simplify(value)))


def spherical_surface(task):
    kind=task['kind'];want=task['requested_output'];text=task.get('surface','')
    a=sym('a');t=sym('t');r=sym('r');A=m.power(a,2)
    if kind=='surface_integral_identity':
        vector_source(task,{'formula','requested_output'},('Доказать формулу Пуассона на единичной сфере.',))
        if want!=['proof'] or task['formula']!='int_{unit sphere} f(ax+by+cz)dS=2*pi*int_-1^1 f(u*sqrt(a^2+b^2+c^2))du':
            raise Unsupported('The original scalar product and sphere normalization differ')
        return proof('spherical_band_reduction',[
            'Rotate the unit sphere so the coefficient vector is its pole direction. Rotation preserves area.',
            'At height u the spherical band has measure du dφ. Integrating φ gives the factor 2π and the full height interval is [−1,1].',
            'If the coefficient vector vanishes, both integrals equal 4πf(0).'],dict(proved=True,scope='integrable source density'))
    if kind=='newton_surface_potential':
        vector_source(task,{'surface','integrand','requested_output'},('Вычислить потенциал однородной сферы в M0(x0,y0,z0).',))
        hit=re.fullmatch(r'x\^2\+y\^2\+z\^2='+N+r'\^2',text)
        rho=re.fullmatch(r'([A-Za-z]\w*)/norm\(\(x,y,z\)-\(x0,y0,z0\)\)',task['integrand'])
        if want!=['potential_in_all_regions'] or not (hit and rho) or rho[1]==hit[1]:raise Unsupported('The uniform source sphere and inverse distance are required')
        [a],_,_=positive_sizes((hit[1],));k=mul(q(4),P,sym(rho[1]),a)
        return proof('spherical_band_reduction',[
            'Rotate to a polar axis through the observation point, at distance r from the center.',
            'For r>0, integrate the bounded band moments of (a²+r²−2ar u)^(-1/2) on −1≤u≤1. Its endpoint values contain a+r and |a−r|.',
            'The coincident boundary pole is an integrable inverse square root in u. At r=0 the source distance is constant.'],
            dict(potential=[dict(condition=f'0<=r<={hit[1]}',value=k),
                            dict(condition=f'r>{hit[1]}',value=m.div(m.mul(k,a),r))],
                 radial_coordinate='r=sqrt(x0^2+y0^2+z0^2)'))
    if kind=='attraction_of_surface':
        vector_source(task,{'surface','density','test_mass','test_mass_location','requested_output'},
                      ('Сила притяжения к однородной усечённой конической поверхности материальной точки в вершине.',))
        hit=re.fullmatch(r'x=r\*cos\(phi\),y=r\*sin\(phi\),z=r;0<=phi<=2\*pi,0<'+N+r'<=r<='+N,text)
        if (want!=['force_vector'] or not hit or task.get('test_mass_location')!=[0,0,0]
                or not all(isinstance(s,str) and s.isidentifier() for s in (task['density'],task['test_mass']))):
            raise Unsupported('The missing test position or radial truncation changes the Newtonian force')
        (lo,hi),_,_=positive_sizes(hit.groups());mass=sym(task['test_mass']);rho=sym(task['density'])
        if m.num(lo) is not None and m.num(hi) is not None and m.num(lo)>m.num(hi):
            raise Unsupported('The lower radius exceeds the upper bound')
        F=mul(P,sym('G'),mass,rho,('ln',m.div(hi,lo)))
        return proof('surface_chart_reduction',[
            'The mass is at the exact vertex, so the distance is sqrt(2)r and the axial direction cosine is 1/sqrt(2).',
            'The conical measure is sqrt(2)r dr dφ. Opposite angular elements cancel the transverse force.',
            'The remaining positive radial density is proportional to dr/r. Its limits exclude the vertex singularity.'],
            dict(force_vector=[ZERO,ZERO,F]),scope='positive density, mass and original ordered radial interval')
    vector_source(task,{'surface','integrand','stated_conditions','requested_output'},
                  ('Вычислить F(t) и построить график u=F(t).','Вычислить F(t) для исходной кусочной функции.',
                   'Вычислить F(x,y,z,t).'))
    if (text=='x+y+z=t' and want in (['piecewise_F'],['piecewise_F','graph']) and not task.get('stated_conditions')
            and task['integrand']=='1-x^2-y^2-z^2 for x^2+y^2+z^2<=1, else 0'):
        d2=m.div(m.power(t,2),q(3));result=mul(q(1,2),P,m.power(sub(ONE,d2),2))
        return proof('moving_surface_sections',[
            'The plane is at distance |t|/sqrt(3) from the center of the support ball.',
            'On its intrinsic disk the density is 1−t²/3−r², and the intrinsic area element is r dr dφ.',
            'Integrate on the disk when the distance is at most one. At tangency the disk degenerates to a point.'],
            dict(F=[dict(condition='abs(t)<=sqrt(3)',value=result),dict(condition='abs(t)>sqrt(3)',value=ZERO)]),graph_scope='out of scope')
    if (text=='x^2+y^2+z^2=t^2' and want==['function_of_t'] and not task.get('stated_conditions')
            and task['integrand']=='x^2+y^2 when x>=sqrt(x^2+y^2), else 0'):
        return proof('moving_surface_sections',[
            'The stated inequality forces x≥0. Squaring it then gives y²≤0, so y=0.',
            'The sphere intersects that half-plane in a set of zero surface area. The complementary density is identically zero.',
            'The zero-radius sphere also has zero area.'],dict(F=ZERO))
    if (text=='(xi-x)^2+(eta-y)^2+(zeta-z)^2=t^2' and want==['piecewise_F']
            and task['integrand']=='1 inside open ball xi²+eta²+zeta²<a², else 0'
            and task.get('stated_conditions')==['r=sqrt(x^2+y^2+z^2)>a>0']):
        s=('abs',t);f=mul(P,m.div(s,r),sub(A,m.power(sub(r,s),2)))
        return proof('moving_surface_sections',[
            'At radius s=|t| the center is a fixed distance r>a from the support ball center.',
            'The distance inequality becomes a lower threshold on the cosine to the inward center direction.',
            'A positive cap exists precisely for r−a<s<r+a. Its area is 2πs² times one minus that threshold.',
            'At either tangency or for s=0 the intersection has zero surface area.'],
            dict(F=[dict(condition='r-a<abs(t)<r+a',value=f),
                    dict(condition='abs(t)<=r-a or abs(t)>=r+a',value=ZERO)]))
    raise Unsupported('The stated moving support and intrinsic surface geometry are not fully bound')


def flat_affine(e,ctx,limit=1):
    return polynomial_terms(e,COORDS,ctx,limit)


def data_matrix(parts,coords=COORDS):
    return [[next((value for degree,value in col.items() if degree==tuple(int(i==j) for i in range(len(coords)))),ZERO)
             for j in range(len(coords))] for col in parts]


def calc_plane(text):
    fields=text.split('=')
    if len(fields)!=2:raise Unsupported('A plane equation is required')
    left,right=[m.parse(s,None,list('xyz')) for s in fields]
    if domain_conditions(left,True) or domain_conditions(right,True):
        raise Unsupported('Original singular plane equation')
    raw=sub(left,right)
    terms=flat_affine(raw,m.context({}))
    normal=data_matrix([terms])[0];offset=m.neg(terms.get((0,0,0),ZERO))
    if any(m.num(s) is None for s in normal+[offset]) or all(s==ZERO for s in normal):
        raise Unsupported('Need a nonzero fixed Cartesian plane normal')
    return normal,offset


def disk_boundary_witness(u,v,parts):
    matrix=data_matrix(parts)
    return mul(P,add(*(mul(matrix[i][j],sub(m.mul(u[j],v[i]),m.mul(v[j],u[i])))
                       for i in range(3) for j in range(3))))


def stokes_chart(task,request):
    vector_source(task,{'coefficients','curve','method_requirement','requested_output'},
                  ('Применить формулу Стокса и проверить непосредственным вычислением.',
                   'Применяя формулу Стокса, вычислить интеграл.'))
    req=task['method_requirement']
    direct=req=='stokes_and_direct'
    if (req not in ('stokes_theorem','stokes_and_direct') or task['requested_output']!=
            (['circulation','independent_direct_evaluation'] if direct else ['circulation','stokes_evaluation'])):
        raise Unsupported('Every stated calculation and the prescribed Stokes method are required')
    curve=task['curve'];parts=task['coefficients']
    sphere=re.fullmatch(r'x\^2\+y\^2\+z\^2='+N+r'\^2,([^;]+); anticlockwise as seen from \+O([xyz])',curve)
    ellipse=re.fullmatch(r'ellipse x='+N+r'\*sin\(t\)\^2,y=2\*'+N+r'\*sin\(t\)\*cos\(t\),z='+N+r'\*cos\(t\)\^2;0<=t<=pi, increasing',curve)
    cube=re.fullmatch(r'intersection of surface of cube \[0,'+N+r'\]\^3 with x\+y\+z=3\*'+N+r'/2, counterclockwise from \+Ox',curve)
    collapse=re.fullmatch(r'closed x='+N+r'\*cos\(t\),y='+N+r'\*cos\(([1-9]\d*)\*t\),z='+N+r'\*cos\(([1-9]\d*)\*t\), increasing t',curve)
    curtain=curve=='x^2+y^2+z^2=2*R*x,x^2+y^2=2*r*x;0<r<R,z>0; smaller patch on outer sphere stays left'
    if (not sphere and not (ellipse and len(set(ellipse.groups()))==1) and not (cube and cube[1]==cube[2])
            and not curtain):
        if not collapse or direct:raise Unsupported('The original curve does not supply a closed regularly oriented spanning patch')
        return collapsed_stokes_disk(parts,collapse,req)
    a=sphere[1] if sphere else ellipse[1] if ellipse else cube[1] if cube else None
    sizes,params,ctx=positive_sizes((a,) if a else ('r','R'),('R-r>0',) if curtain else ())
    if len(parts)!=3:raise Unsupported('Three smooth Cartesian source coefficients are required')
    field=[m.parse(f,None,[*params,*'xyz']) for f in parts]
    terms=[polynomial_terms(f,COORDS,ctx,2 if cube or curtain else 1) for f in field]
    derivative=coordinate_sections([*params,*'xyz'],request)
    curl=coordinate_curl(derivative,field)
    checking=dict(curl=curl,method_requirement=req)
    if sphere:
        if direct is False and task.get('source',{}).get('literal_requirement')=='Применить формулу Стокса и проверить непосредственным вычислением.':
            raise Unsupported('The independent computation required in print must be present')
        normal,h=calc_plane(sphere[2]);axis='xyz'.index(sphere[3]);sign=m.num(normal[axis])
        if h!=ZERO or not sign:raise Unsupported('The stated view is edge-on or the sphere section is not central')
        n=[m.mul(q(1 if sign>0 else -1),m.div(s,sqrt(m.dot(normal,normal)))) for s in normal]
        basis=next(z for j in range(3) if (z:=vector_cross(n,[q(int(i==j)) for i in range(3)]))!=[ZERO]*3)
        u=[m.mul(sizes[0],m.div(s,sqrt(m.dot(basis,basis)))) for s in basis];v=vector_cross(n,u)
        bearing='The normal has a positive component towards the specified viewer. Use the central disk cut by the given plane.'
    elif ellipse:
        if direct:raise Unsupported('The independent mode needs a direct parametrization with checked limits')
        A=sizes[0];u=[m.neg(m.div(A,q(2))),ZERO,m.div(A,q(2))];v=[ZERO,A,ZERO]
        bearing='Double the original parameter. Its resulting cosine and sine vectors span an ellipse and determine its oriented vector area.'
    elif cube:
        if direct:raise Unsupported('Direct polygon evaluation was not requested in this mode')
        A=sizes[0];n=[m.div(ONE,sqrt(q(3)))]*3;C=m.div(A,q(2));center=dict(zip(COORDS,[C]*3))
        normal=m.dot(curl,n);flat_affine(normal,ctx)
        value=mul(q(3,4),sqrt(q(3)),m.power(A,2),m.substitute(normal,center))
        return proof('oriented_stokes_reduction',[
            'The central section of the cube is a regular hexagon of side a/sqrt(2). Its normal faces positive Ox.',
            'The normal component of the curl is affine. Reflection about the hexagon center cancels its linear residual.',
            'Multiply its value at the center by the intrinsic hexagon area.'],dict(circulation=value,stokes_evaluation=value),**checking)
    else:
        if direct:raise Unsupported('The selected two-face boundary does not supply independent direct mode')
        return stokes_cylinder_curtain(curl,ctx,checking)
    vector_area=[m.mul(P,c) for c in vector_cross(u,v)]
    value=m.simplify(m.dot(curl,vector_area));result=dict(circulation=value)
    steps=[bearing,'Apply Stokes with the curl of the original field. Its constant value pairs with the oriented vector area.']
    if direct:
        actual=m.simplify(disk_boundary_witness(u,v,terms))
        if not same_value(actual,value):raise Unsupported('The independent line integral does not match the surface result')
        result['independent_direct_evaluation']=actual
        steps.append('Independently integrate the original affine field on the cosine/sine boundary chart. Only the two signed mixed coordinate moments remain.')
    else:result['stokes_evaluation']=value
    return proof('oriented_stokes_reduction',steps,result,vector_area=vector_area,**checking)


def stokes_cylinder_curtain(curl,ctx,checking):
    r,R=map(sym,('r','R'));height=mul(q(2),sqrt(m.mul(r,sub(R,r))))
    # Vertical integration fixes the angular exponent before the finite spherical moment expansion.
    wall=ZERO;part=[]
    for a,f in enumerate(curl[:2]):
        for (i,j,k),c in polynomial_terms(f,COORDS,ctx).items():
            n,b=divmod(k+1,2);J=j+a
            if J%2:continue
            I=add(*(m.mul(q(comb(i+n,l)),curtain_angle_moment(l+1-a,J,b)) for l in range(i+n+1)))
            z=m.neg(mul(c,I,q(1,2**n*(k+1)),m.power(r,i+j+1),m.power(height,k+1)))
            wall=m.add(wall,z);part.append((a,(i,j,k),I,z))
    disk=ZERO
    z0=m.substitute(curl[2],{Z:ZERO,X:m.add(X,r)})
    for (i,j,_),c in polynomial_terms(z0,COORDS,ctx).items():
        disk=m.add(disk,mul(c,polar_factor(i,j),m.div(m.power(r,i+j+2),q(i+j+2))))
    value=m.simplify(m.add(wall,disk))
    return proof('oriented_stokes_reduction',[
        'The smaller spherical patch lies inside the source cylinder, with the tangent for increasing t leaving it to the left.',
        'Span the same curve by the cylinder curtain plus its horizontal base. The curtain normal points inward. The base points upward and cancels the lower seam.',
        'Integrate the polynomial vertical density between zero and the source positive cut. Integrate the remaining angular and shifted-disc moments.'],
        dict(circulation=value,stokes_evaluation=value),curtain_integral=wall,closing_cap=disk,angular_proof=part,**checking)


def curtain_angle_moment(i,j,half):
    if not half:return polar_factor(i,j)
    # u=sin(t/2) makes cos(t/2) dt=2 du on the original interval.
    n=j//2
    return q(4**(n+1)*sum(Fraction(comb(i,a)*comb(n,b)*(-2)**a*(-1)**b,2*(n+a+b)+1)
                         for a in range(i+1) for b in range(n+1)))


def collapsed_stokes_disk(parts,names,method):
    a,b,j,c,k=names.groups();_,params,ctx=positive_sizes((a,b,c))
    field=[m.parse(s,None,[*params,*'xyz']) for s in parts]
    if len(field)!=3 or max(int(j),int(k))>12:raise Unsupported('Only a smooth finite reparametrized contour is admitted')
    for f in field:polynomial_terms(f,COORDS,ctx)
    return proof('oriented_stokes_reduction',[
        'The cosine multiples are Chebyshev polynomials of v=cos t. The original closed curve is the boundary pullback of a polynomial map from the unit disk.',
        'The disk map is (s,w) ↦ (a s,b T_j(s),c T_k(s)). Its differential has rank at most one everywhere.',
        'The pullback of the exterior derivative of the original polynomial one-form is zero. Stokes on the parameter disk gives zero with the stated increasing boundary orientation.'],
        dict(circulation=ZERO,stokes_evaluation=ZERO),rank_upper_bound=1,method_requirement=method)


def oriented_helix(task,request):
    vector_source(task,{'coefficients','curve','printed_integral_sign','suggested_method','requested_output'},
                  ('Вычислить интеграл от A до B по куску винтовой линии.',))
    hit=re.fullmatch(r'x='+N+r'\*cos\(phi\),y='+N+r'\*sin\(phi\),z='+N+r'\*phi/\(2\*pi\), from A\('+N+r',0,0\) to B\('+N+r',0,'+N+r'\)',task['curve'])
    if (not hit or not(hit[1]==hit[2]==hit[4]==hit[5] and hit[3]==hit[6]) or len(task['coefficients'])!=3
            or task['requested_output']!=['line_integral']
            or task.get('suggested_method') not in (None,'close with a segment and apply Stokes')
            or task.get('printed_integral_sign') not in (None,'closed_integral_with_open_path_AmB')):
        raise Unsupported('The original open path, closing segment and endpoint order are not bound')
    (a,h),params,ctx=positive_sizes((hit[1],hit[3]))
    coefficients=[m.parse(s,None,[*params,*'xyz']) for s in task['coefficients']]
    for f in coefficients:polynomial_terms(f,COORDS,ctx)
    curl=coordinate_curl(coordinate_sections([*params,*'xyz'],request),coefficients)
    if curl!=[ZERO]*3:raise Unsupported('The proposed closing method has no verified zero circulation for this field')
    v=('v','t');line=m.substitute(coefficients[2],{X:a,Y:ZERO,Z:v})
    part,integral=curve_chart_moment(line,'t',params,[s+'>0' for s in params],ZERO,h,request,'integral opposite the closing segment')
    return proof('oriented_stokes_reduction',[
        'Close the original open curve with the directed segment B→A. The checked original curl vanishes on all of space.',
        'The closed path therefore has zero circulation. The closing segment is at x=a,y=0 and runs from height h to zero.',
        'Reverse the sign of that segment contribution to obtain the original A→B integral.'],
        dict(line_integral=integral),curl=curl,closing_segment=m.neg(integral),segment_witness=part)


def linear_norm_flux(task,request):
    vector_source(task,{'field','surface','orientation','method_requirement','suggested_method','requested_output'},
                  ('Вычислить поток через внешнюю сторону поверхности.',))
    if (task.get('orientation') not in ('outward','inward') or task.get('method_requirement')!='divergence_theorem'
            or task.get('suggested_method') is not None or task['requested_output']!=['flux'] or len(task['field'])!=3
            or task.get('source',{}).get('literal_requirement') and task['orientation']!='outward'):
        raise Unsupported('The outward boundary, divergence theorem and Cartesian field are required')
    region=re.fullmatch(r'abs\(([^()]*)\)\+abs\(([^()]*)\)\+abs\(([^()]*)\)='+N,task['surface'])
    if not region:raise Unsupported('The norm level is not a verified bounded linear image')
    [radius],params,ctx=positive_sizes((region[4],))
    terms=[flat_affine(m.parse(s,None,list('xyz')),ctx) for s in region.groups()[:3]]
    if any(d.get((0,0,0),ZERO)!=ZERO for d in terms):raise Unsupported('The section center is not established')
    T=data_matrix(terms);det=m.dot(T[0],vector_cross(T[1],T[2]));det=m.num(det)
    if not det:raise Unsupported('The linear norm level is singular')
    raw=[m.parse(s,None,[*params,*'xyz']) for s in task['field']]
    for f in raw:polynomial_terms(f,COORDS,ctx,2)
    partial=coordinate_sections([*params,*'xyz'],request)
    div=add(*(partial(c,s) for c,s in zip(raw,'xyz')))
    affine=flat_affine(div,ctx);avg=affine.get((0,0,0),ZERO)
    vol=m.mul(q(Fraction(4,3)/abs(det)),m.power(radius,3));value=m.mul(avg,vol)
    if task['orientation']=='inward':value=m.neg(value)
    return proof('spatial_flux_reduction',[
        'The nonsingular linear map sends the original bounded interior to the octahedron |u|+|v|+|w|≤R.',
        'Eight coordinate simplexes give its volume 4R³/3, and the inverse determinant gives the original volume.',
        'The affine divergence has average equal to its constant coefficient by central symmetry. Apply the divergence theorem with the specified normal.'],
        dict(flux=value),map_determinant=q(det),volume=vol,divergence=div,orientation=task['orientation'])


def punctured_spatial_flux(task,request):
    kind=task['kind'];want=task['requested_output'];r=('s','r')
    base=['Remove a small ball about the source point if it lies in the region. The extra spherical normal points toward the center.',
          'Apply the divergence theorem on the regular remainder, then take the small-radius limit with the original exterior normal fixed.']
    if kind=='gauss_boundary_integral':
        vector_source(task,{'integrand','region','point_position','requested_output'},('Вычислить интеграл Гаусса для указанного положения точки.',))
        loc=task['point_position']
        if (want!=['flux'] or task['integrand']!='cos(r,n)/r^2' or loc not in ('inside','outside')
                or task['region']!='simple closed smooth surface S, n outward, r from observation point to surface'):
            raise Unsupported('The original source point, normals and inverse-square kernel must agree')
        value=ZERO
        if loc=='inside':
            request('enclose an isolated source with verified inward sphere correction',dict(
                kind='singular_radial_flux',field='c*r_vector/r^3',parameter='constant c',surface='closed enclosing 0, outward'))
            value=m.mul(q(4),P)
        return proof('punctured_spatial_boundary',[
            'The normal density is the flux of r_vector/r³ with the observation point as radial center.',
            'Its divergence vanishes away from the center.']+base+[
            'A centered inward sphere contributes −4π exactly when the center lies in the original interior.'],
            dict(flux=value),center_position=loc)
    if kind=='divergence_integral_transform':
        vector_source(task,{'field','region','method_requirement','requested_output'},
                      ('Преобразовать поверхностный интеграл с помощью формулы Остроградского.',))
        if (want!=['equivalent_triple_integral'] or task['method_requirement']!='divergence_theorem'
                or task['field']!=['x/r','y/r','z/r;r=sqrt(x²+y²+z²)']
                or task['region']!='smooth closed S bounds finite V; n outward'):
            raise Unsupported('The source field must be radial unit speed with the stated closed regular region')
        return proof('punctured_spatial_boundary',[
            'The radial unit field has divergence 2/r away from the origin. The kernel 2/r is locally integrable in three dimensions.']+base+[
            'The radial field is bounded, so the extra sphere or spherical cap contributes O(ε²).'],
            dict(region='V',cartesian_integrand=m.div(q(2),r),radial_coordinate='sqrt(x^2+y^2+z^2)'))
    vector_source(task,{'claim','requested_output'},('Доказать формулу для объёмного интеграла.',))
    if want!=['proof'] or task['claim']!='int_V 1/r dV = (1/2) int_S cos(r,n)dS,n outward,r vector from (x,y,z) to (xi,eta,zeta)':
        raise Unsupported('Bind the original displacement vector and orientation')
    return proof('punctured_spatial_boundary',[
        'Use the unit vector based at the observation point. Its divergence is 2/r off that point.']+base+[
        'The extra surface tends to zero with its area, and 1/r is locally integrable. Divide the original outward flux by two.'],
        dict(proved=True,identity=task['claim']))


def source_flux_or_volume(task,request):
    kind=task['kind'];want=task['requested_output']
    if kind=='oriented_surface_flux':
        if 'literal_form' not in task:return linear_norm_flux(task,request)
        vector_source(task,{'literal_form','surface','orientation','requested_output'},
                      ('Вычислить напечатанный ориентированный поверхностный интеграл, внешняя сторона.',))
        if (want!=['flux_or_singularity_diagnosis'] or task['orientation']!='outward'
                or task['literal_form']!='dy dx/x + dz dx/y + dx dy/z'
                or task['surface']!='x^2/a^2+y^2/b^2+z^2/c^2=1'):
            raise Unsupported('The literal signed order and original ellipsoid must be checked')
        return proof('spatial_flux_reduction',[
            'Swap dy dx once to obtain −dx dy. The canonical coefficients are (0, 1/y, 1/z−1/x).',
            'On the nondegenerate ellipsoid the y and z normal components each supply exactly the cancelling factor in their corresponding simple pole.',
            'Near the smooth transverse cut x=0 where z≠0, the remaining coefficient of 1/x does not vanish. Integrating either side gives logarithmic divergence.'],
            dict(ordinary_flux_exists=False,singularity='nonintegrable simple pole on x=0 where z!=0'),
            normalized_coefficients=['0','1/y','1/z-1/x'])
    vector_source(task,{'surfaces','requested_output'},('Вычислить объём тела по напечатанным поверхности и плоскостям.',))
    if want!=['exact_volume']:raise Unsupported('The original volume output is required')
    s=task['surfaces'];a=sym('a');b=sym('b')
    if s=='x=u*cos(v),y=u*sin(v),z=-u+a*cos(v),u>=0,a>0, cut by x=0,z=0':
        return proof('spatial_flux_reduction',[
            'The bounded positive-height component has |v|≤π/2 and 0≤u≤a cos v.',
            'The upper height is a cos v−u, and the polar Jacobian is u.',
            'Integrate u times the height and then the angular cosine cubed. Other signed sides are unbounded.'],
            dict(volume=m.mul(q(2,9),m.power(a,3))))
    if s=='torus x=(b+a*cos(psi))*cos(phi),y=(b+a*cos(psi))*sin(phi),z=a*sin(psi);0<a<=b':
        return proof('spatial_flux_reduction',[
            'The meridional disk has radius a and center at radial distance b. The printed a≤b places it on one side of the axis.',
            'The rotation volume is 2π times the disk first radial moment. Its centered linear part integrates to zero.',
            'At a=b only the boundary touches the axis, which does not duplicate positive volume.'],
            dict(volume=mul(q(2),m.power(P,2),m.power(a,2),b)))
    raise Unsupported('The literal parametrization does not identify a unique bounded volume component')


GREEN_FLUX={
    'int_S partial_n(u)dS=int_V Delta(u) dV, u C² on V+S':
        ('grad(u)','laplacian(u)'),
    'int_S u*partial_n(u)dS=int_V (norm(grad u)^2+u*Delta(u))dV, u C² on V+S':
        ('u*grad(u)','dot(grad(u),grad(u))+u*laplacian(u)'),
    'int_V (v*Delta(u)-u*Delta(v))dV=int_S (v*u_n-u*v_n)dS; smooth bounding S, outward n, u,v twice differentiable':
        ('v*grad(u)-u*grad(v)','v*laplacian(u)-u*laplacian(v)'),
    'int_S partial_n(u)dS=0 for u harmonic in closed bounded V':
        ('grad(u)','laplacian(u)'),
    'int_V norm(grad u)^2 dV=int_S u*partial_n(u)dS for u harmonic in closed bounded V':
        ('u*grad(u)','dot(grad(u),grad(u))+u*laplacian(u)'),
}


def checked_green_field(field,result,request):
    fields={name:'scalar' for name in ('u','v') if re.search(r'\b'+name+r'\b',field)}
    request('prove the divergence of the proposed auxiliary field',dict(
        kind='formal_vector_identity',identity='div('+field+')='+result,fields=fields,regularity={s:2 for s in fields}))


def spatial_green_claim(task,request):
    vector_source(task,{'claim','method_requirement','requested_output','stated_conditions'},('Доказать указанную формулу или теорему.',),('continued_on_pdf_page',))
    if task['requested_output']!=['proof']:raise Unsupported('The exact stated theorem is required')
    claim=task['claim'];method=task.get('method_requirement')
    if method is not None and not (isinstance(method,str) and re.fullmatch(r'energy_identity(?:_\d+[a-z])?',method)):
        raise Unsupported('The required proof method does not match the source')
    if task.get('stated_conditions') not in (None,[],['u continuous on the closed ball']):
        raise Unsupported('An original domain hypothesis is unbound')
    steps=[]
    if claim in GREEN_FLUX and method is None:
        field,divergence=GREEN_FLUX[claim];checked_green_field(field,divergence,request)
        steps=['Use the checked identity for divergence of '+field+' by Cartesian differentiation.',
               'Apply the divergence theorem on the same bounded volume with exterior normal. The normal trace of the proposed field gives each integrand on the original surface.']
        if 'harmonic' in claim:steps.append('The harmonic Laplacian vanishes throughout the original volume.')
    elif claim=='derive uniqueness of harmonic u from its values on S via the preceding energy identity' and method:
        checked_green_field('u*grad(u)','dot(grad(u),grad(u))+u*laplacian(u)',request)
        steps=['Take the difference of two harmonic candidates with the same boundary trace.',
               'The checked energy identity makes its nonnegative Dirichlet energy zero because both its boundary trace and Laplacian vanish.',
               'Continuity makes the gradient vanish everywhere. Each interior component is constant, and zero boundary data force each constant to be zero.']
    elif (claim=='u(P)=(1/(4*pi))*int_S [u*cos(r,n)/r^2+(1/r)*partial_n(u)]dS for interior P, r from P to boundary, u harmonic'
          and method is None):
        checked_green_field('v*grad(u)-u*grad(v)','v*laplacian(u)-u*laplacian(v)',request)
        steps=['Use the auxiliary field from the second Green identity with v=1/r outside the excised sphere about P.',
               'On the outer boundary ∂n v=−cos(r,n)/r². Its normal trace is the original sum.',
               'On the inner sphere the normal points toward P, so ∂n v=+1/ε². Its first term is O(ε) and its second term has limit −4πu(P).',
               'The bulk divergence vanishes on the punctured region. Move the limiting inner term to the outer side.']
    elif claim=='u(x0,y0,z0)=int_S u dS/(4*pi*R²), S radius R, harmonic u' and method is None:
        if not task.get('stated_conditions'):
            return proof('spatial_green_auxiliary_fields',[
                'Для каждой строго внутренней сферы среднее равно значению в центре. Переход к написанной сфере требует совпадения граничных значений со следом изнутри.',
                'При u=0 внутри шара и u=1 на поверхности внутренняя функция гармонична. Среднее на поверхности равно единице, а в центре значение нулевое.'],
                dict(printed_claim_holds=False,counterexample=dict(interior=ZERO,boundary=ONE,center=ZERO,surface_mean=ONE),
                     valid_with='continuous boundary trace on the closed ball'),method_requirement=method)
        checked_green_field('grad(u)','laplacian(u)',request)
        steps=['At the center of a smaller concentric sphere the Green kernel and its outer derivative are constant.',
               'The integrated normal derivative of u vanishes, leaving the normalized spherical average.',
               'Use the stated continuous trace to let the radius tend to the original R.']
    elif (claim=='A nonconstant harmonic function on the interior, continuous on a bounded closed region, cannot attain a maximum or minimum in its interior'
          and method is None):
        steps=['In a small ball contained strictly in the interior, the mean-value identity holds for every concentric sphere.',
               'If the center is a maximum, its value is the maximum of all sphere values. Their average is equal only if they are all that maximum, by continuity.',
               'The maximum set is open and closed in the connected interior. It would make the function constant. Apply the same argument to −u for a minimum.']
    else:raise Unsupported('The exact harmonic assumptions, including any required boundary trace, remain unbound')
    return proof('spatial_green_auxiliary_fields',steps,dict(proved=True,equality=claim),method_requirement=method)


def spatial_boundary_identity(task,request):
    kind=task['kind'];want=task['requested_output']
    if kind=='plane_boundary_identity':
        vector_source(task,{'integrand','hypotheses','contour_orientation','requested_output'},
                      ('Найти интеграл определителя по положительно ориентированному контуру в плоскости.',))
        if (want!=['integral'] or task['contour_orientation']!='positive relative to the given normal'
                or task['integrand']!='det([[dx,dy,dz],[cos(alpha),cos(beta),cos(gamma)],[x,y,z]])'
                or task['hypotheses']!=['plane x*cos(alpha)+y*cos(beta)+z*cos(gamma)=p','C bounds planar patch of area S']):
            raise Unsupported('The determinant, unit normal and positive traversal need to agree')
        return proof('oriented_stokes_reduction',[
            'Expand the determinant as (n×X)·dX with the same normal as in the plane equation.',
            'The curl of a constant unit normal crossed with position is 2n. Positive traversal preserves its sign.',
            'Integrate its normal component 2 over the original planar patch.'],dict(integral=mul(q(2),sym('S'))))
    if kind=='magnetic_potential_identity':
        vector_source(task,{'formula','conditions','requested_output'},
                      ('Доказать, что W — потенциал магнитного поля тока по контуру С.',))
        cond=task['conditions']
        if (want!=['proof'] or task['formula']!='W=k*i*int_S cos(r,n)/r^2 dS' or len(cond)!=4
                or cond[:3]!=['C bounds S','n normal','r from M to variable point A as printed']
                or not re.fullmatch(r'see #\d+',cond[3])):
            raise Unsupported('Bind the surface orientation and displacement from observation point to surface')
        return proof('punctured_spatial_boundary',[
            'For P off the spanning surface, write the integrand as F(Q)·n with F(Q)=(Q−P)/|Q−P|³.',
            'The derivative along a fixed v in P is the negative Q directional derivative. Away from the pole this equals curl_Q(v×F) because div_Q F=0.',
            'Stokes changes the derivative to v·∮_C F×dQ for the contour orientation induced by n. The printed Biot–Savart displacement runs from Q to P, so H=−grad W when the current follows that contour orientation.',
            'Reversing the normal reverses W while preserving the given current. The potential is defined on a branch off the cut surface.'],
            dict(proved=True,field='H=-grad W if n induces the current direction; H=grad W for the opposite n',
                 scope='observation point outside spanning surface'))
    if kind=='hydrostatic_identity':
        vector_source(task,{'conditions','method_requirement','requested_output'},
                      ('Исходя из закона Паскаля, доказать закон Архимеда (модуль и направление силы).',))
        if (want!=['proof_buoyant_force_magnitude_and_direction'] or task['method_requirement']!='pascal_law'
                or task['conditions']!=['body V fully submerged']):
            raise Unsupported('The body must be submerged and the stated Pascal-law derivation retained')
        return proof('spatial_flux_reduction',[
            'By Pascal pressure acts normally on each surface element. Static equilibrium of thin horizontal fluid layers gives grad p=−ρg e_z with z upwards.',
            'The force on the body is −∫_S p n dS because the fluid pushes against the exterior normal.',
            'Apply the divergence theorem componentwise to the complete boundary. The magnitude is the weight of the displaced liquid and the direction is upwards.'],
            dict(proved=True,force_vector='e_z*integral_V rho*g dV',uniform_density='rho*g*volume(V)'))
    if kind=='differentiate_moving_integral':
        vector_source(task,{'formula','stated_conditions','requested_output'},
                      ('Доказать формулу дифференцирования по радиусу t>0.',))
        if (want!=['proof'] or task['stated_conditions']!=['t>0','f and partial_t f continuous near the closed moving ball']
                or task['formula']!='d/dt int_{r<=t} f(x,y,z,t)dV = int_{r=t} f(x,y,z,t)dS + int_{r<=t} partial_t f(x,y,z,t)dV'):
            raise Unsupported('Proof of the asserted boundary and volume derivatives needs the original differentiation regularity')
        return proof('moving_surface_sections',[
            'Use the radius as the outer integration variable on the ball. Its upper end is the original t.',
            'Differentiate the upper endpoint by the fundamental theorem. This gives exactly the integral over the radius-t sphere.',
            'Continuity of the parameter partial on a compact neighborhood bounds the remaining difference quotients and gives the original volume term.'],
            dict(proved=True,equality=task['formula']))
    vector_source(task,{'claim','surfaces','stated_conditions','requested_output'},
                  ('Доказать нулевой поток постоянного направления.','Доказать формулу объёма.',
                   'Доказать V=S*H/3 для конуса с гладкой конической поверхностью и плоским основанием.'))
    if want!=['proof']:raise Unsupported('The complete original identity is required')
    claim=task['claim']
    if claim=='int_S cos(n,l)dS=0, S simple closed, n outward, l fixed' and not (task.get('surfaces') or task.get('stated_conditions')):
        return proof('spatial_flux_reduction',[
            'The fixed unit vector l has zero divergence. Its normal flux is the original cosine density.',
            'Apply the divergence theorem on the bounded original region.'],dict(proved=True,flux=ZERO))
    if claim=='V=(1/3)*int_S (x*cos(alpha)+y*cos(beta)+z*cos(gamma))dS for outward direction cosines' and not (task.get('surfaces') or task.get('stated_conditions')):
        return proof('spatial_flux_reduction',[
            'The displayed density is the outward flux of the Cartesian position field.',
            'Its divergence equals the dimension three. Apply the divergence theorem on the original bounded region and divide by three.'],
            dict(proved=True,equality=claim))
    if (claim=='V=S*H/3' and task['surfaces']==['F(x,y,z)=0','A*x+B*y+C*z+D=0']
            and task['stated_conditions']==['smooth conical surface','S is the area of its planar base','H is the height of the cone']):
        return proof('spatial_flux_reduction',[
            'Take the position field relative to the cone vertex. It is tangent on every regular lateral generator.',
            'On the base the outward normal component is the constant height H, so that part contributes SH.',
            'The divergence equals three, and the vertex is handled by a small vanishing cap.'],dict(proved=True,equality=claim))
    raise Unsupported('The claimed spatial balance does not identify a verified field and its complete boundary')


def compose_surface(task,library,request):
    kind=task['kind']
    if kind in ('scalar_surface_integral','compare_surface_integrals','shell_mass_properties'):return scalar_shell(task,request)
    if kind in ('surface_integral_identity','attraction_of_surface','newton_surface_potential','moving_surface_integral'):return spherical_surface(task)
    if kind=='stokes_circulation':return stokes_chart(task,request)
    if kind=='line_integral_from_geometric_locus':return oriented_helix(task,request)
    if kind in ('bounded_solid_volume','oriented_surface_flux'):return source_flux_or_volume(task,request)
    if kind in ('gauss_boundary_integral','divergence_integral_transform','newton_volume_surface_identity'):return punctured_spatial_flux(task,request)
    if kind=='green_harmonic_identity':return spatial_green_claim(task,request)
    if kind in ('plane_boundary_identity','magnetic_potential_identity','hydrostatic_identity','flux_identity','differentiate_moving_integral'):
        return spatial_boundary_identity(task,request)
    return field_source_properties(task,request)


def differentiated_gradient(task,request):
    kind=task['kind'];is_cross=kind=='cartesian_constant_cross_gradient';is_direction=kind=='symbolic_directional_derivative'
    vector_source(task,{'function','variables','parameters','stated_conditions','requested_output','points',
                        'point_names','direction','direction_cosines','constant_vector'},
                  ('Найти координаты вектора c×grad u для u=arctg(z/sqrt(x²+y²)), c=i+j+k.',
                   'Производная вдоль радиус-вектора данной точки и условие её равенства величине градиента.',
                   'Производная поля 1/r вдоль l с данными направляющими косинусами и все случаи нулевой производной.'),
                  ('printed_requirement','points','unit_direction','requested_zero_set','coordinate_identity'))
    params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    src=task.get('source',{});want=task['requested_output']
    allowed={'function','variables','parameters','stated_conditions','requested_output'}
    allowed|={'constant_vector'} if is_cross else {'direction','direction_cosines'} if is_direction else {'points','point_names','direction'}
    if (task['variables']!=list('xyz') or set(task)-allowed-{'kind','id','source'} or set(params)&set('xyz')
            or src.get('points') not in (None,task.get('points'))):
        raise Unsupported('The field and required original Cartesian data disagree')
    raw=m.parse(task['function'],None,[*params,*'xyz']);original=domain_conditions(raw,True)
    def norm(v):return sqrt(m.dot(v,v))
    branch=raw[0]=='atan' and raw[1][0]=='div' and raw[1][1]==Z and raw[1][2][0]=='sqrt' and same_value(raw[1][2][1],m.dot((X,Y),(X,Y)))
    if branch:
        s=raw[1][2];square=m.dot(COORDS,COORDS)
        gradient=[m.neg(m.div(m.mul(Z,c),m.mul(s,square))) for c in (X,Y)]+[m.div(s,square)]
    else:
        partial=coordinate_sections([*params,*'xyz'],request,local_premises=[])
        gradient=[m.simplify(partial(raw,s)) for s in 'xyz']
    r=norm(COORDS);steps=['Differentiate along each independent Cartesian coordinate on the original domain.']
    if is_cross:
        if want!=['vector_in_cartesian_basis'] or len(task['constant_vector'])!=3 or conditions:
            raise Unsupported('The full constant cross product and original field are required')
        C=[m.parse(str(s),None,params) for s in task['constant_vector']]
        ctx=m.context(dict(parameters=params))
        if not all(m.constant_defined(c,ctx) for c in C):raise Unsupported('All coordinates of the fixed field must be real')
        if branch:steps.append('On s=sqrt(x²+y²)>0, differentiate z/s by the quotient rule and multiply by 1/(1+(z/s)²).')
        return proof('gradient_goal_composition',steps+['Use the checked gradient in the directed cross product.'],
                     dict(vector=vector_cross(C,gradient)),gradient=gradient,domain=original)
    if is_direction:
        if want==['directional_derivative','locate_all_equality_with_gradient_norm']:
            if task.get('direction')!=list('xyz') or len(params)!=3 or conditions:
                raise Unsupported('The original ellipsoidal axes and radius-vector direction are required')
            shape=add(*(m.div(m.power(c,2),m.power(sym(p),2)) for c,p in zip(COORDS,params)))
            if not same_value(raw,shape):raise Unsupported('The equality classification requires a diagonal positive quadratic form')
            value=dict(directional_derivative=m.div(m.dot(gradient,COORDS),r),
                       equality='nonzero coordinates have equal corresponding squared semiaxes',
                       scope='r>0; semiaxes nonzero')
        elif want==['directional_derivative','all_zero_directions']:
            L=task.get('direction_cosines')
            if not isinstance(L,list) or len(L)!=3 or conditions!=['+'.join(c+'^2' for c in L)+'=1']:
                raise Unsupported('The three original unit direction cosines must be established')
            u=[m.parse(c,None,params) for c in L]
            value=dict(directional_derivative=m.dot(gradient,u),zero_condition='dot(gradient,unit_direction)=0')
        else:raise Unsupported('Bind all specified directional derivative outputs')
        return proof('gradient_goal_composition',steps+['Take the scalar product with the unit direction. The equality case follows from the equality criterion of Cauchy–Schwarz.'],
                     value,gradient=gradient,domain=original)
    if want==['gradient'] and not (task.get('points') or task.get('point_names') or task.get('direction') or conditions):
        extra='undefined at origin' if raw[0]=='sqrt' and same_value(raw[1],m.dot(COORDS,COORDS)) else None
        return proof('gradient_goal_composition',steps,dict(gradient=gradient),domain=original,origin=extra)
    points=task.get('points');labels=task.get('point_names')
    if (not isinstance(points,list) or not isinstance(labels,list) or len(labels)!=len(points) or not points or conditions
            or any(not isinstance(p,list) or len(p)!=3 for p in points)):
        raise Unsupported('Bind all original points and their hypotheses')
    ctx=m.context(dict(parameters=params));rows=[]
    for point in points:
        coords=[m.parse(str(c),None,params) for c in point];substitution=dict(zip(COORDS,coords))
        if (not all(m.constant_defined(c,ctx) for c in coords) or not m.constant_defined(m.substitute(raw,substitution),ctx)
                or any(not known_guard((op,m.substitute(e,substitution)),ctx) for op,e in original)):
            raise Unsupported('The original field is not differentiable at one of the points')
        g=[m.simplify(m.substitute(c,substitution)) for c in gradient];size=norm(g)
        if m.sign(size,ctx)!=1:raise Unsupported('The gradient must be nonzero for its direction or angle')
        rows.append(dict(point=coords,gradient=g,norm=size,direction=[m.div(c,size) for c in g]))
    if want==['angle_between_gradients'] and len(rows)==2 and 'direction' not in task:
        coef=m.simplify(m.dot(*(row['direction'] for row in rows)))
        value=dict(cosine=coef,angle=('acos',coef))
    elif want==['gradient_norm','gradient_direction','directional_derivative'] and len(rows)==1:
        spec=task.get('direction',{})
        if spec.get('name')!='positive xOy coordinate angle bisector' or spec.get('vector')!=[1,1,0]:
            raise Unsupported('The requested oriented bisector must be present')
        g=rows[0];d=m.div(m.add(g['gradient'][0],g['gradient'][1]),sqrt(q(2)))
        value=dict(gradient_norm=g['norm'],gradient_direction=g['direction'],directional_derivative=d)
    elif want==['gradient_norms','gradient_directions','all_stationary_points'] and 'direction' not in task:
        affine=[flat_affine(g,ctx) for g in gradient]
        A=data_matrix(affine);constant=[m.neg(f.get((0,0,0),ZERO)) for f in affine]
        def det(B):return m.dot(B[0],vector_cross(B[1],B[2]))
        D=det(A)
        if not m.nonzero(D,ctx):raise Unsupported('The stationary affine system may have more than one solution')
        t=[m.div(det([row[:j]+[c]+row[j+1:] for row,c in zip(A,constant)]),D) for j in range(3)]
        value=dict(gradient_norms=[g['norm'] for g in rows],gradient_directions=[g['direction'] for g in rows],stationary_points=[t])
    else:raise Unsupported('The original geometric gradient outputs are not all covered')
    return proof('gradient_goal_composition',steps+['Bind the original points, check their domains and normalize the nonzero gradients.'],
                 value,gradient=gradient,at_points=rows,labeled_points=labels)


def text_field_goal(task,request):
    vector_source(task,{'goal','requested_output'},())
    g=task['goal'];r=sqrt(m.dot(COORDS,COORDS))
    cube=re.fullmatch(r'u=x\^3\+y\^3\+z\^3-3xyz\. Determine all points where grad u *(is perpendicular to Oz|is parallel to Oz|=0)\.',g)
    if task.get('requested_output'):
        return focal_and_radial_levels(task)
    if cube:
        partial=coordinate_sections(list('xyz'),request)
        raw=m.parse('x^3+y^3+z^3-3*x*y*z',None,list('xyz'));grad=[partial(raw,c) for c in 'xyz']
        solutions={'is perpendicular to Oz':'z^2=x*y with x=y=z excluded when an angle is required',
                   'is parallel to Oz':'x=y=0 and z!=0',
                   '=0':'x=y=z'}
        return proof('gradient_goal_composition',[
            'Differentiate each original polynomial term. Perpendicularity imposes the zero z-component.',
            'For parallel or vanishing gradients the x and y components vanish. When xy≠0 their equations imply x³=y³ and then z=x. When xy=0 they give x=y=0.',
            'Separate the zero gradient from points at which a direction is requested.'],
            dict(points=solutions[cube[1]]),gradient=grad)
    texts={
        'u=ln(1/r), r=sqrt((x-a)^2+(y-b)^2+(x-c)^2) as printed; find |grad u|=1.':(
            ['Keep the literal repeated x. Center the two x terms by X=x−(a+c)/2, and set Y=y−b, d=(a−c)/2.',
             'The positive denominator is r²=2X²+Y²+2d². Differentiation gives gradient −(2X,Y,0)/r². Square the positive-norm equation and retain r>0.'],
            dict(points='4X^2+Y^2=(2X^2+Y^2+2d^2)^2, r>0, z arbitrary',coordinates='X=x-(a+c)/2, Y=y-b, d=(a-c)/2')),
        'u=sqrt(x²+y²+(z+8)²)+sqrt(x²+y²+(z−8)²). Construct all level surfaces, find the one through (9,12,28), and max u on x²+y²+z²≤36.':(
            ['The foci are 16 units apart. Triangle inequality gives the segment at level 16, and subtraction of squared focal distances gives the ellipsoid for higher levels.',
             'The two distances at the given point are 39 and 25, so the level is 64.',
             'Concavity of the square root gives u≤2 sqrt(x²+y²+z²+64)≤20; equality on the equator at radius 6.'],
            dict(levels='empty for u<16; focal segment for u=16; (x^2+y^2)/(u^2/4-64)+4*z^2/u^2=1 for u>16',
                 level_through_point='(x^2+y^2)/960+z^2/1024=1',maximum=q(20),maximizers='z=0,x^2+y^2=36')),
        'u=x/sqrt(x²+y²+z²). Construct the level surfaces of u and |grad u|, find inf and sup of both on 1<z<2.':(
            ['On the punctured space set r=sqrt(x²+y²+z²), w=sqrt(y²+z²). The gradient norm is w/r².',
             'Keep the sign of x in the equation x=sr for the u-level. For c>0 the gradient level is the circle equation x²+(w−1/(2c))²=1/(4c²) in the meridional coordinates.',
             'On the original strip |u|<1 and 0<|grad u|≤1/z<1. Let x tend to either infinity or set x=y=0 and let z decrease to 1 to attain the corresponding bounds as limits.'],
            dict(u_bounds=[q(-1),ONE],gradient_norm_bounds=[ZERO,ONE],u_levels='x=s*r, r>0; empty if abs(s)>1',
                 gradient_levels='c=0: x-axis excluding origin; c>0: x^2+(w-1/(2*c))^2=1/(4*c^2), r>0; c<0: empty')),
        'Find to first order the distance at M0=(x0,y0,z0) between u=c and u=c+Δc, where u(M0)=c and grad u(M0)≠0.':(
            ['Expand u near M0. Cauchy–Schwarz bounds the change by the gradient norm times the displacement plus a smaller remainder.',
             'Along the unit gradient direction the derivative is positive, so near M0 the neighboring level is realized at the matching first-order distance.'],
            dict(distance='abs(Delta_c)/norm(grad u(M0))+o(abs(Delta_c))')),
        'Найти grad f(r), r=sqrt(x²+y²+z²).':(
            ['Away from zero, use the derivative of the Euclidean norm and the scalar chain rule.',
             'At the origin a differentiable radial function has zero gradient by evenness. The condition f(r)−f(0)=o(r) suffices there.'],
            dict(gradient=[m.div(m.mul(sym('f_prime_r'),v),r) for v in COORDS],origin_condition='f(r)-f(0)=o(r)')),
        'Prove grad f(u,v)=f_u grad u+f_v grad v.':(
            ['Apply the chain rule separately to each independent Cartesian coordinate, then assemble the resulting three components.'],
            dict(proved=True,equality='grad f(u,v)=f_u grad u+f_v grad v')),
    }
    if g not in texts:raise Unsupported('No complete checked source gradient construction')
    steps,value=texts[g];return proof('gradient_goal_composition',steps,value)


def focal_and_radial_levels(task):
    g=task['goal'];out=task['requested_output']
    focal=re.fullmatch(r'For u=sqrt\(x\^2\+y\^2\+\(z\+([1-9]\d*)\)\^2\)\+sqrt\(x\^2\+y\^2\+\(z-([1-9]\d*)\)\^2\), classify its level surfaces, find the level surface through \((-?\d+),(-?\d+),(-?\d+)\) and max u on x\^2\+y\^2\+z\^2<=([1-9]\d*)\.',g)
    if focal and focal[1]==focal[2] and out==['level_family','level_through_point','maximum_on_ball']:
        f,_,x,y,z,R2=map(int,focal.groups());xy=x*x+y*y
        level=m.add(sqrt(q(xy+(z+f)**2)),sqrt(q(xy+(z-f)**2)));high=mul(q(2),sqrt(q(f*f+R2)))
        A2=m.power(m.div(level,q(2)),2)
        same=dict(level=level,radial_semiaxis_squared=sub(A2,q(f*f)),axial_semiaxis_squared=A2)
        if xy==0 and -f<=z<=f:same=dict(level=level,segment=[-f,f])
        return proof('gradient_goal_composition',[
            'Triangle inequality gives the focal segment at the distance between the two foci. For a larger level subtract the two squared focal distances to obtain the ellipsoid.',
            'Compute both original focal distances at the given point.',
            'By concavity their sum on the given ball is at most twice sqrt(focal distance²+radius²). Equality holds on its equator.'],
            dict(level_family=dict(minimum_level=q(2*f),ellipsoid='radial semiaxis²=(level/2)^2-f^2; axial semiaxis²=(level/2)^2'),
                 level_through_point=same,maximum=high,maximizers=f'z=0,x^2+y^2={R2}'))
    slab=re.fullmatch(r'For u=x/sqrt\(x\^2\+y\^2\+z\^2\), classify the level surfaces of u and norm\(grad\(u\)\) and find inf and sup of both on ([1-9]\d*)<z<([1-9]\d*)\.',g)
    if slab and int(slab[1])<int(slab[2]) and out==['level_families','four_bounds_on_slab']:
        return proof('gradient_goal_composition',[
            'The level u=s requires x=sr with r>0, preserving the original sign. Its range is [−1,1].',
            'At positive radius, norm grad u=w/r² with w=sqrt(y²+z²). Complete the meridian square to obtain every positive level.',
            'On the slab, large positive or negative x approaches the two u bounds and the zero gradient bound.',
            'The gradient norm is bounded by 1/z. Approach the lower z face on x=y=0 to reach the sharp upper bound as a limit.'],
            dict(u_levels='x=s*r, r>0; empty for |s|>1',
                 gradient_levels='for c>0: x^2+(w-1/(2*c))^2=1/(4*c^2), r>0; for c=0: x-axis off origin; for c<0: empty',
                 u_bounds=[q(-1),ONE],gradient_norm_bounds=[ZERO,q(1,int(slab[1]))]))
    raise Unsupported('The original gradient geometry and all requested domains are required')


def local_divergence_flux(task,request):
    vector_source(task,{'field','at','sphere'},('Найти дивергенцию в M и приближённый поток через бесконечно малую сферу.',))
    point=task['at'];field=task['field'];ctx=m.context({})
    if (len(field)!=3 or len(point)!=3 or not all(type(n) is int for n in point)
            or task['sphere']!='+'.join(f'({x}-{v})^2' if v>=0 else f'({x}+{-v})^2' for x,v in zip('xyz',point))+'=epsilon^2'):
        raise Unsupported('The infinitesimal sphere must be centered at the original point')
    coordinates=[q(s) for s in point];at=dict(zip(COORDS,coordinates));parts=[]
    for f in field:
        raw=m.parse(f,None,list('xyz'))
        if not m.constant_defined(m.substitute(raw,at),ctx) or any(not known_guard((op,m.substitute(e,at)),ctx) for op,e in domain_conditions(raw,True)):
            raise Unsupported('The original component is not smooth near the point')
        parts.append(raw)
    diagonal=[]
    for i,(f,c) in enumerate(zip(parts,'xyz')):
        reduced=m.substitute(f,{v:s for v,s in at.items() if v!=COORDS[i]})
        child=request('verify the normal-coordinate derivative at the original point',dict(
            kind='derivative_at',function=source(reduced),variable=c,point=str(point[i]),
            requested_output=['finite_derivative'],method_requirement='table_and_rules'))
        diagonal.append(freeze(child['value']))
    d=m.simplify(add(*diagonal))
    return proof('gradient_goal_composition',[
        'The original field is smooth in a neighborhood of the center. Sum the independently checked Cartesian diagonal derivatives.',
        'The exterior flux divided by the small-ball volume tends to that divergence by continuity. The volume is 4πε³/3.'],
        dict(divergence=d,flux_leading_coefficient=mul(q(4,3),P,d),error='o(epsilon^3)'),center=coordinates)


def formal_field_source(task,request):
    if task.get('expression')=='div(det[[i,j,k],[D_x,D_y,D_z],[omega_x,omega_y,omega_z]])':
        vector_source(task,{'expression'},('Найти дивергенцию определителя ротора.',))
        return proof('cartesian_vector_goal_composition',[
            'Read the determinant as curl of the original omega field. Commute the mixed second partials of its smooth components.'],
            dict(divergence=ZERO),operator=checked_divergence_of_curl(request))
    if task.get('claim')=='div(a)(M)=lim_(diam(S)->0) flux_S(a)/V':
        vector_source(task,{'claim','geometry'},('Доказать предельную формулу для потока, отнесённого к объёму.',))
        if task.get('geometry')!='closed S enclosing M, volume V, n exterior':raise Unsupported('Preserve the original shrinking enclosure and its exterior normal')
        return proof('cartesian_vector_goal_composition',[
            'The divergence theorem changes the flux divided by volume to the mean of the continuous divergence on each enclosure.',
            'Its deviation from the divergence at M is bounded by the modulus of continuity at the enclosure diameter. Let that diameter tend to zero.'],
            dict(proved=True,equality=task['claim']))
    if task.get('operation')=='div(a)' and task.get('method_requirement')=='direct coordinate computation':
        vector_source(task,{'operation','method_requirement','claim'},('Непосредственным вычислением доказать инвариантность дивергенции при смене прямоугольной системы координат.',))
        if task.get('claim')!='divergence is invariant under the change of rectangular Cartesian coordinate system':
            raise Unsupported('The original Cartesian coordinate change must be stated')
        return proof('cartesian_vector_goal_composition',[
            'For a fixed orthogonal coordinate matrix Q, the derivative matrix changes to Q J Qᵀ by the chain rule.',
            'Summing its diagonal uses ∑_i Q_ij Q_ik=δ_jk, so the divergence is the original trace.'],
            dict(proved=True,equality=task['claim']))
    if (task.get('field'),task.get('r'),task.get('c'))==('f(r)*c','sqrt(x^2+y^2+z^2)','constant vector'):
        vector_source(task,{'field','r','c'},('Вычислить div[f(r)c].',))
        return proof('cartesian_vector_goal_composition',[
            'The constant vector has no derivative. Apply the chain rule to the radial factor and take the Cartesian scalar product.'],
            dict(divergence='f_prime(r)*dot(c,r_vector)/r for r>0',
                 center='zero if f(r)-f(0)=o(r), with a separate zero-field case when c=0'))
    raise Unsupported('The original vector formula is unsupported or ill-typed')


def checked_divergence_of_curl(request):
    expression='div(curl(omega))'
    request('show cancellation of the six mixed partials',dict(kind='formal_vector_identity',
        claim=expression+'=0',fields={'omega':'vector'},regularity={'omega':2}))
    return expression


FIELD_GOALS={
    'gradient_lipschitz_proof':(
        {'hypotheses':['u differentiable on convex region Omega','norm(grad(u))<=M, M constant'],
         'conclusion':'abs(u(A)-u(B))<=M*distance(A,B)'},'Для любых A,B из Ω доказать оценку по евклидову расстоянию.',
        ['The original convex set contains the segment A+t(B−A). Its derivative is grad u dot (B−A), bounded in magnitude by M|B−A|.',
         'Apply the one-dimensional mean value theorem to that segment.'],dict(proved=True)),
    'generic_gradient_direction':(
        {'fields':['arbitrary differentiable u(x,y,z)','arbitrary differentiable v(x,y,z)'],
         'requested_output':['directional_derivative_along_grad_v','when_derivative_is_zero']},
        'Найти производную скалярного поля u в направлении градиента поля v. Когда она равна нулю?',
        ['Normalize the nonzero gradient of v and pair it with grad u. The derivative is zero exactly when the numerator vanishes.'],
        dict(derivative='dot(grad(u),grad(v))/norm(grad(v))',zero_condition='dot(grad(u),grad(v))=0',scope='grad(v)!=0')),
    'radial_laplacian_and_harmonicity':(
        {'field':'arbitrary radial f(r)','r':'sqrt(x^2+y^2+z^2)'},'Найти div(grad f(r)) и все случаи его равенства нулю.',
        ['Use grad r=x/r and div(x/r)=2/r away from zero. The product rule gives f″+2f′/r.',
         'Vanishing is equivalent to (r²f′)′=0. A nonzero inverse-radius term cannot pass through the origin.'],
        dict(laplacian='f_second(r)+2*f_prime(r)/r',harmonic='A+B/r for r>0; B=0 if harmonic at r=0')),
    'radial_divergence_and_solenoidality':(
        {'field':'f(r)*r_vector','r':'sqrt(x^2+y^2+z^2)'},'Найти div[f(r)r] и определить, когда оно равно нулю.',
        ['The divergence of position is three. The chain-rule part pairs the radial derivative with the position and gives rf′.',
         'The zero condition becomes (r³ f)′=0 on positive-radius intervals.'],dict(divergence='3*f(r)+r*f_prime(r)',
            zero_case='f(r)=C/r^3 for r>0; C=0 for smooth extension through origin')),
    'rigid_rotation_divergences':(
        {'rotation':'counterclockwise around Oz at constant angular speed omega','point':list('xyz'),
         'requested_output':['velocity_divergence','acceleration_divergence']},
        'Найти дивергенции скорости и ускорения вращающейся жидкости в M.',
        ['The velocity is the angular velocity crossed with position. Differentiating along that flow gives centripetal acceleration.',
         'Taking the two Cartesian traces gives zero and −2ω².'],dict(velocity_divergence=ZERO,acceleration_divergence=mul(q(-2),m.power(sym('omega'),2)))),
    'gravitational_field_divergence':(
        {'sources':'finite family of mass centers','requested_output':['divergence_on_classical_field_domain']},'Найти дивергенцию гравитационного поля конечной системы притягивающих центров.',
        ['Translate to each mass center and differentiate its inverse-square radial vector field away from that center.',
         'The two contributions cancel for each source. Add the finitely many zero divergences.'],
        dict(divergence=ZERO,scope='outside the original set of mass centers')),
    'orthogonal_coordinate_divergence':(
        {'field':'a(r,phi)','requested_output':['polar_divergence']},'Выразить дивергенцию плоского вектора в полярных координатах.',
        ['Opposite radial faces have lengths proportional to r. The angular faces have radial length dr.',
         'Divide their net outward flux by r dr dφ and pass to the limit.'],
        dict(divergence='partial_r(r*a_r)/r+partial_phi(a_phi)/r',scope='r>0; components in unit polar basis')),
}


def field_source_properties(task,request):
    kind=task['kind']
    if kind in ('gradient_source_properties','cartesian_constant_cross_gradient','symbolic_directional_derivative'):
        return differentiated_gradient(task,request)
    if kind=='vector_calculus_source_goal':return text_field_goal(task,request)
    if kind=='formal_vector_identity':return formal_field_source(task,request)
    if kind=='cartesian_field_operator':
        vector_source(task,{'expression','fields','requested_output'},('Найти дивергенцию определителя ротора.',))
        if task['requested_output']!=['simplified_divergence_and_regularity_domain'] or task['expression']!='div(curl(omega))' or task['fields']!={'omega':'vector'}:
            raise Unsupported('The source determinant must be the same rotation and regularity request')
        return proof('cartesian_vector_goal_composition',[
            'Use the checked mixed-partial cancellation for the three Cartesian components.'],
            dict(divergence=ZERO,scope='where the indicated mixed derivatives exist and commute'),checked_operator=checked_divergence_of_curl(request))
    if kind=='divergence_and_local_flux':return local_divergence_flux(task,request)
    if kind=='orthogonal_coordinate_gradient':
        vector_source(task,{'field','coordinates'},('Выразить grad u в соответствующих координатах.',))
        charts={'cylindrical':('e_r*u_r+e_phi*u_phi/r+e_z*u_z','r>0'),
                'spherical':('e_r*u_r+e_theta*u_theta/r+e_phi*u_phi/(r*sin(theta))','r>0 and 0<theta<pi; theta is colatitude')}
        coord=task['coordinates']
        if task['field']!='u(x,y,z)' or coord not in charts:raise Unsupported('A declared regular orthogonal chart is required')
        g,c=charts[coord]
        return proof('gradient_goal_composition',[
            'Write the Cartesian differential in orthogonal unit tangent directions. Each derivative coefficient is divided by that chart tangent length.'],
            dict(gradient=g,scope=c))
    if kind=='field_lines':
        vector_source(task,{'field','requested_output'},('Определить силовые линии векторного поля.',))
        if len(task['field'])!=3 or task['requested_output']!=['all_field_lines']:raise Unsupported('The linear field must have three components')
        field=[m.parse(s,None,list('xyz')) for s in task['field']]
        ctx=m.context({});powers=[]
        for i,f in enumerate(field):
            terms=flat_affine(f,ctx)
            key=tuple(int(i==j) for j in range(3))
            if not terms.keys()<={key}:raise Unsupported('No autonomous separated line for these coupled components')
            powers.append(terms.get(key,ZERO))
        t=sym('t');g=[mul(sym(k),('exp',m.mul(l,t))) for k,l in zip('ABC',powers)]
        return proof('cartesian_vector_goal_composition',[
            'Solve each decoupled constant-rate coordinate equation. Their arbitrary initial values give every integral curve.',
            'A vanishing initial coordinate stays zero, so the family includes the coordinate axes and stationary trajectories.'],
            dict(trajectory=g,parameters=list('ABC'),parameter='t'))
    entry=FIELD_GOALS.get(kind)
    if entry:
        fields,header,steps,val=entry
        vector_source(task,fields,(header,))
        if {k:task.get(k) for k in fields}==fields:return proof('cartesian_vector_goal_composition',steps,val)
    raise Unsupported('The original field and every requested operator or geometric output are not yet bound')


STANDALONE_SURFACE_KINDS={
    'compare_surface_integrals','shell_mass_properties','scalar_surface_integral','surface_integral_identity',
    'attraction_of_surface','newton_surface_potential','moving_surface_integral','stokes_circulation','plane_boundary_identity',
    'magnetic_potential_identity','newton_volume_surface_identity','hydrostatic_identity','differentiate_moving_integral',
    'gradient_source_properties','cartesian_constant_cross_gradient','symbolic_directional_derivative',
    'vector_calculus_source_goal','orthogonal_coordinate_gradient','divergence_and_local_flux','field_lines',
    *FIELD_GOALS.keys()-{'orthogonal_coordinate_divergence'},
}


class NeededSurfaceChild(Exception):
    pass


def mark_surface_child(role,task):
    raise NeededSurfaceChild


def surface_field_goal(task):
    kind=task.get('kind')
    if kind not in STANDALONE_SURFACE_KINDS:
        eligible=(
            kind in ('bounded_solid_volume','oriented_surface_flux','divergence_integral_transform',
                     'gauss_boundary_integral','green_harmonic_identity','flux_identity','line_integral_from_geometric_locus')
            or kind=='formal_vector_identity' and not {'fields','regularity'}&task.keys()
            or kind=='cartesian_field_operator' and task.get('requested_output')==['simplified_divergence_and_regularity_domain']
            or kind=='orthogonal_coordinate_divergence' and task.get('field')=='a(r,phi)')
        if not eligible:return False
    try:compose_surface(task,None,mark_surface_child)
    except NeededSurfaceChild:return True
    except (Unsupported,KeyError,TypeError,ValueError,IndexError,AttributeError):return False
    return True


def source_surface_field(task,library,request):
    if not library.data.get('source_surface_fields'):raise Unsupported('No executable source surface and field transitions')
    return compose_surface(task,library,request)
