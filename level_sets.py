"""Real level sets from quadratic normal forms or exact weighted dilations of rational branches."""
from fractions import Fraction as F
from functools import reduce
from itertools import combinations
from math import comb

import expressions as m
from graphs import rational_roots
from model import Unsupported,q
from tasks import domain_conditions,known_guard


def dot(a,b):return sum(x*y for x,y in zip(a,b,strict=True))


def nullspace(A):
    M=[list(row) for row in A];n=len(M);piv=[]
    for j in range(n):
        i=next((i for i in range(len(piv),n) if M[i][j]),None)
        if i is None:continue
        k=len(piv);M[k],M[i]=M[i],M[k];v=M[k][j];M[k]=[x/v for x in M[k]]
        for i,row in enumerate(M):
            if i!=k:M[i]=[x-row[j]*y for x,y in zip(row,M[k])]
        piv.append(j)
    basis=[]
    for j in range(n):
        if j in piv:continue
        v=[F(i==j) for i in range(n)]
        for i,p in enumerate(piv):v[p]=-M[i][j]
        for u in basis:
            factor=dot(u,v)/dot(u,u);v=[x-factor*y for x,y in zip(v,u)]
        basis.append(v)
    return basis


def quadratic_coefficients(expr,variables):
    """Extract exact coefficients of a real quadratic polynomial."""
    symbols=[('s',v) for v in variables];P,D=m.rational_form(expr);n=len(symbols)
    if D!={():F(1)} or any(set(dict(mon))-set(symbols) or sum(k for _,k in mon)>2 for mon in P):
        raise Unsupported('A polynomial of total degree at most two is required')
    def coefficient(indices):
        mon=tuple(sorted((s,indices.count(s)) for s in set(indices)))
        return P.get(mon,F(0))
    l=[coefficient([s]) for s in symbols];k=coefficient([]);A=[[coefficient([s,t])/(1 if s==t else 2) for t in symbols] for s in symbols]
    return A,l,k


def quadratic(expr,variables):
    """Certify a Euclidean principal-axis representation, including nullspace directions."""
    symbols=[('s',v) for v in variables];n=len(symbols)
    A,l,k=quadratic_coefficients(expr,variables)
    tr=sum(A[i][i] for i in range(n));minor=sum(A[i][i]*A[j][j]-A[i][j]**2 for i,j in combinations(range(n),2))
    poly=(-tr,F(1)) if n==1 else (minor,-tr,F(1))
    if n==3:
        det=sum(A[0][i]*(A[1][(i+1)%3]*A[2][(i+2)%3]-A[1][(i+2)%3]*A[2][(i+1)%3]) for i in range(3))
        poly=(-det,minor,-tr,F(1))
    roots=rational_roots(poly);axes=[];linear=q(0);terms=[]
    for lam in sorted({r.a for r in roots if not r.b}):
        for v in nullspace([[a-(lam if i==j else 0) for j,a in enumerate(row)] for i,row in enumerate(A)]):
            norm=dot(v,v);lv=dot(l,v);u=m.dot(map(q,v),symbols)
            if lam:
                u=m.add(u,q(lv/(2*lam)));k-=lv**2/(4*lam*norm)
                terms.append(m.mul(q(lam/norm),m.power(u,2)))
            else:linear=m.add(linear,m.mul(q(lv/norm),u))
            axes.append(dict(eigenvalue=q(lam),direction=tuple(map(q,v)),squared_norm=q(norm),coordinate=u))
    directions=[tuple(map(m.num,a['direction'])) for a in axes]
    checks=all(dot(u,v)==0 for u,v in combinations(directions,2))
    checks=checks and all(dot(v,v)>0 and all(dot(row,v)==m.num(a['eigenvalue'])*vj for row,vj in zip(A,v)) for a,v in zip(axes,directions))
    reconstructed=reduce(m.add,terms,m.add(q(k),linear))
    if len(axes)!=n or not checks or m.rational_form(m.add(expr,m.neg(reconstructed)))[0]:
        raise Unsupported('A complete exact diagonalization has not been verified')
    return A,l,{'offset':q(k),'orthogonal_axes':axes,'linear_residual':linear}


def exact_rational(value):
    if type(value) not in (F, int):
        raise ValueError('Expected an exact rational coefficient')
    return F(value)


def solve_linear(matrix, rhs):
    rows = [list(row) + [value] for row, value in zip(matrix, rhs, strict=True)]
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j]), None)
        if pivot is None:
            return None
        rows[j], rows[pivot] = rows[pivot], rows[j]
        divisor = rows[j][j]
        rows[j] = [value / divisor for value in rows[j]]
        for i, row in enumerate(rows):
            if i != j and row[j]:
                rows[i] = [a - row[j] * b for a, b in zip(row, rows[j], strict=True)]
    return tuple(row[-1] for row in rows)


def psd_form(matrix):
    """Return exact square weights and coordinate rows of a PSD form."""
    work = [list(row) for row in matrix]
    squares = []
    for i, row in enumerate(work):
        pivot = row[i]
        if pivot < 0 or pivot == 0 and any(row[i+1:]):
            raise ValueError('The quadratic objective is not convex')
        if pivot:
            vector = tuple(x / pivot for x in row)
            squares.append((pivot, vector))
            for j in range(i, len(work)):
                work[j] = [a - pivot * vector[j] * b for a, b in zip(work[j], vector, strict=True)]
    return tuple(squares)


def quadratic_hull(matrix, linear, offset, vertices):
    """Search supports for a rational KKT witness and check it in all directions."""
    linear = tuple(map(exact_rational, linear))
    dim = len(linear)
    matrix = tuple(tuple(map(exact_rational, row)) for row in matrix)
    vertices = tuple(dict.fromkeys(tuple(map(exact_rational, point)) for point in vertices))
    offset = exact_rational(offset)
    if (not 1 <= dim <= 4 or not 1 <= len(vertices) <= 16
            or len(matrix) != dim or any(len(row) != dim for row in (*matrix, *vertices))
            or any(matrix[i][j] != matrix[j][i] for i in range(dim) for j in range(i))):
        raise ValueError('Bounded rational coordinates and a symmetric quadratic form are required')
    squares = psd_form(matrix)

    def transform(point):
        return tuple(dot(row, point) for row in matrix)

    def value(point):
        return dot(point, transform(point)) + dot(linear, point) + offset

    slopes = [dot(v, linear) for v in vertices]
    transformed = [transform(v) for v in vertices]
    values = [value(v) for v in vertices]
    top = max(range(len(vertices)), key=values.__getitem__)
    for size in range(1, min(len(vertices), dim+1) + 1):
        for support in combinations(range(len(vertices)), size):
            stationarity = [tuple(2*dot(vertices[i], transformed[j]) for j in support)+(F(1),) for i in support]
            weights = solve_linear(stationarity+[(F(1),)*size+(F(0),)], [-slopes[i] for i in support]+[F(1)])
            if weights is None or min(weights[:-1]) <= 0:
                continue
            barycentric = weights[:-1]
            point = tuple(dot(barycentric, column) for column in zip(*(vertices[i] for i in support), strict=True))
            gradient = tuple(2*a + b for a, b in zip(transform(point), linear, strict=True))
            base = dot(gradient, point)
            margins = tuple(dot(gradient, v) - base for v in vertices)
            if min(margins) >= 0:
                plan = dict(convexity=squares, support=support, weights=barycentric,
                            first_order_margins=margins, vertex_values=values)
                answer = dict(infimum=value(point), minimum_point=point, supremum=values[top], maximum_point=vertices[top])
                verify_hull(matrix, linear, offset, vertices, plan, answer)
                return plan, answer
    raise ValueError('No stationary feasible witness was found')


def diagonal_ball(weights, radius_squared, offset=0, closed=True):
    """Compare quadratic diagonal coefficients with attained or limiting radii."""
    weights = tuple(map(exact_rational, weights))
    radius_squared, offset = exact_rational(radius_squared), exact_rational(offset)
    if not weights or radius_squared <= 0 or type(closed) is not bool:
        raise ValueError('A positive-radius real ball is required')
    branches = []
    for compare in (min, max):
        i = compare(range(len(weights)), key=weights.__getitem__)
        edge = compare(F(0), weights[i])
        differences = tuple(w - edge for w in weights)
        branches.append(dict(bound=offset+edge*radius_squared, attained=closed or edge == 0,
                             witness_axis=None if edge == 0 else i, radial_coefficient=edge,
                             residual_diagonal=differences))
    return dict(infimum=branches[0], supremum=branches[1])


def verify_hull(matrix, linear, offset, vertices, plan, answer):
    """Check global bounds by the supplied witnesses, without solving another system."""
    point, maximum = answer['minimum_point'], answer['maximum_point']
    dim = len(linear)
    squares, support, weights = (plan[key] for key in ('convexity', 'support', 'weights'))
    if any(scale <= 0 or len(axis) != dim for scale, axis in squares) or any(
        matrix[i][j] != sum(scale * axis[i] * axis[j] for scale, axis in squares)
        for i in range(dim) for j in range(dim)
    ):
        raise ValueError('The supplied squares do not prove convexity')
    if (len(support) != len(weights) or not support or any(not 0 <= j < len(vertices) for j in support)
            or len(set(support)) != len(support) or sum(weights) != 1 or any(w <= 0 for w in weights)
            or tuple(dot(weights, col) for col in zip(*(vertices[i] for i in support), strict=True)) != point):
        raise ValueError('The minimum witness does not belong to the original convex hull')

    gradient = tuple(2*dot(row, point)+b for row, b in zip(matrix, linear, strict=True))
    margins = tuple(dot(gradient, v) - dot(gradient, point) for v in vertices)
    def value(where):
        return sum(x * dot(row, where) for x, row in zip(where, matrix, strict=True)) + dot(linear, where) + offset
    values = [value(vertex) for vertex in vertices]
    if (margins != plan['first_order_margins'] or min(margins) < 0 or values != plan['vertex_values']
            or value(point) != answer['infimum'] or maximum not in vertices
            or value(maximum) != answer['supremum'] or max(values) != answer['supremum']):
        raise ValueError('A witness misses a claimed global bound')



BOX_SECTIONS=(
    'У невырожденного вписанного параллелепипеда все вершины на границе. Если все восемь лежат на квадрике, равенство в вершинах требует, чтобы рёбра давали диагональный базис квадратичной части, а линейные коэффициенты в этом базисе исчезли.',
    'Смешанная разность по трём рёбрам от квадратичного уравнения равна нулю. Если на плоской крышке только одна вершина, остальные семь снова влекут равенство на квадрике и для восьмой. Поэтому на крышке есть хотя бы ребро: вершины максимальной высоты образуют опорную грань параллелепипеда.',
    'Берём горизонтальное ребро длины 2L. Из двух вертикальных прямоугольных граней, перпендикулярных ему, одна отстоит от оси по этой координате не меньше L. Сечение там ограничено плоской крышкой и симметричным выпуклым профилем g.',
)
CONE_VERTEX_CENTER='У конуса исчезновение линейных коэффициентов влечёт, что центр параллелепипеда совпал с вершиной конуса. Это невозможно для положительного объёма по одну сторону от вершины.'
TRIANGLE_UNIT_HEXAGON=((1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1))


def triangle_box_determinant_bound():
    return max(abs(a*d-b*c) for a,b in TRIANGLE_UNIT_HEXAGON for c,d in TRIANGLE_UNIT_HEXAGON)


def quadratic_cap_box_volume(text,want,conditions,method):
    # A vertex-inscribed box in one quadric and a cap has a horizontal edge.
    import re
    if want!='dimensions maximizing volume' or method is not None:
        return None
    name=r'([A-Za-z][A-Za-z_0-9]*)'
    cone=re.fullmatch(fr'rectangular box inscribed in right circular cone(?: of base radius {name} and height {name})?',text)
    ellipse=re.fullmatch(fr'rectangular box (?:inscribed )?in elliptic paraboloid segment z/{name}=x²/{name}²\+y²/{name}² and z=\1',
                         text.replace('^2','²'))
    reversed_ellipse=re.fullmatch(fr'rectangular box (?:inscribed )?in elliptic paraboloid segment z/{name}=y²/{name}²\+x²/{name}² and z=\1',
                                  text.replace('^2','²'))
    if cone is None and ellipse is None and reversed_ellipse is None:return None
    params=list(cone.groups() if cone else ellipse.groups() if ellipse else reversed_ellipse.groups())
    if cone is None and ellipse is None:params[1:]=reversed(params[1:])
    if cone and params==[None,None]:params=['R','H']
    if len(set(params+['x','y','z']))!=len(params)+3 or conditions not in (
            [],[','.join(params)+'>0'],[name+'>0' for name in params]):
        raise Unsupported('The two or three independent positive dimensions must bind to the original inscribed box')
    point=lambda n:('s',n)
    determinant_bound=triangle_box_determinant_bound()
    if determinant_bound!=1:raise Unsupported('The determinant comparison on the triangle failed')
    argument=[
        *BOX_SECTIONS,
        'У лучшего горизонтального прямоугольника полуширины X выполняется H−g(X)=Xg′(X). Касательные к g в ±X дают содержащий профиль треугольник. Этот прямоугольник занимает ровно половину площади треугольника.',
        'Любой вписанный в треугольник параллелограмм имеет площадь не больше половины. После аффинного переноса берём полные векторы его сторон. Их суммы модулей барицентрических координат вместе не больше 2. Для вектора с нулевой суммой координат эта сумма равна удвоенному максимуму модуля.',
        'Единичный шар этой нормы — шестиугольник. Все определители пар его вершин по модулю не больше 1, значит, то же верно для любых двух векторов из него. Произведение норм двух сторон не больше 1/4. Сравниваем с площадью эталонного треугольника 1/2.'
    ]
    from graphs import optimize_geometric_profile
    powers=(1,2) if cone else (F(1,2),F(3,2))
    profile,derivative_sign,profile_proof,vertices=optimize_geometric_profile(('unit_product',*powers),('v','t'),None)
    fraction=vertices[0]['point']
    complement=m.add(m.ONE,m.neg(fraction))
    if cone:
        R,H=map(point,params)
        h=m.mul(fraction,H);top=m.mul(complement,R);width=m.mul(('sqrt',q(2)),top)
        volume=m.mul(q(2),m.mul(h,m.power(top,2)))
        result=dict(dimensions=dict(horizontal_sides=[width,width],height=h),maximum_volume=volume,
                    scope='nondegenerate vertex-inscribed boxes, base radius and height positive')
        argument.insert(1,CONE_VERTEX_CENTER)
        argument.extend([
            'Для конуса профиль вертикальной грани есть g(u)=√(u²+L²)/κ, где κ=R/H. Отражение даёт допустимый горизонтальный прямоугольник одновременно на обеих сторонах ±L. Значит, поворот коробки не увеличивает максимум.',
            'У горизонтальной коробки высоты h верхняя грань вписана в круг радиуса R(1−h/H). При фиксированной диагонали максимальная площадь у квадрата. Профиль объёма пропорционален t(1−t)², где t=h/H, и достигает максимума при t=1/3.'
        ])
        case='circular_cone'
    else:
        C,A,B=map(point,params)
        x_width=m.mul(q(2),m.mul(A,('sqrt',m.div(complement,q(3)))))
        y_width=m.mul(q(2),m.mul(B,('sqrt',fraction)))
        height=m.mul(m.mul(q(2,3),complement),C)
        result=dict(dimensions=dict(horizontal_sides=[x_width,y_width],height=height),
                    maximum_volume=m.mul(height,m.mul(x_width,y_width)),
                    scope='nondegenerate vertex-inscribed boxes, positive semiaxes and cap height')
        argument.insert(1,'У параболоида квадратичная часть не имеет компоненты вдоль оси z. Диагональный базис обязательно содержит это направление, а в нём линейный коэффициент ненулевой.')
        argument.extend([
            'В вертикальной грани дополняем квадрат в горизонтальной координате. Если перед её квадратом коэффициент A₀, то после сдвига минимума коэффициент поперечного квадрата D₀ удовлетворяет A₀D₀=1/(a²b²), независимо от поворота.',
            'При поперечной половине L площадь максимального прямоугольника в сечении равна 4c(1−D₀L²)^(3/2)/(3√(3A₀)). Это следует из профиля ширины 2X и высоты 1−X² в единичной шкале.',
            'После умножения на 2L получаем профиль t^(1/2)(1−t)^(3/2), где t=D₀L². Он максимален при t=1/4. Оценка не зависит от поворота благодаря определителю A₀D₀.',
            'Берём рёбра вдоль полуосей. Нижняя грань на половине высоты имеет четыре вершины на параболоиде. Верхние четыре лежат на плоской крышке, так что найденная граница достигается.'
        ])
        case='elliptic_paraboloid_segment'
    return dict(theorem='method.support_triangle_box_extrema',proof='\n'.join(argument),profile_branch=case,
                triangle_unit_hexagon=list(TRIANGLE_UNIT_HEXAGON),determinant_bound=q(determinant_bound),
                critical_fraction=fraction,normalized_profile=profile,derivative_sign=derivative_sign,profile_proof=profile_proof),result


def radical_stationary_system(definitions, coordinates, parameters, library):
    """Compile stationarity of P+Q√K into a rational straight-line system."""
    import re
    from derivative_proofs import table
    from tasks import source

    bindings=[];known=set(coordinates)
    for label,text in definitions.items():
        expr=m.parse(text,None,known|set(parameters))
        parents=sorted(set(re.findall(r'[A-Za-z_]\w*',text))&known)
        partials={p:table(m.substitute(expr,{('s',p):('v',p)}),p,library)[0] for p in parents}
        partials={p:m.substitute(d,{('v',p):('s',p)}) for p,d in partials.items()}
        bindings.append((label,text))
        for axis in coordinates:
            derivative=m.ZERO
            for p,d in partials.items():
                if p in coordinates:
                    if p==axis:derivative=m.add(derivative,d)
                else:
                    derivative=m.add(derivative,m.mul(d,('s',f'd_{p}_{axis}')))
            bindings.append((f'd_{label}_{axis}',source(derivative)))
        known.add(label)
    return dict(assignments=bindings,
                equations=['w^2=K','A=P+Q*w',*(
                    f'2*w*d_P_{axis}+2*K*d_Q_{axis}+Q*d_K_{axis}=0' for axis in coordinates)],
                positive_radical='w>0',value='A')


def tilted_cone_area(R,H,horizontal,domain,library):
    determinant=triangle_box_determinant_bound()
    # For y=√2 H/R≥19/6 these coefficients prove horizontal dominance
    # of the crude diameter bound on collapsed rectangles.
    polynomial=(F(-32),F(64),F(-33),F(2),F(1))
    start=F(19,6)
    shifted=tuple(sum(polynomial[i]*comb(i,j)*start**(i-j)
                      for i in range(j,5)) for j in range(5))
    if determinant!=1 or min(shifted)<=0 or 2*F(9,4)**2<=start**2:
        raise Unsupported('The comparison with degenerate configurations did not verify')
    definitions={
        'U':'2*sigma*(s+1/s)*t/(sigma^2+s^2+2)',
        'V':'2*sigma*(s+1/s)*(1-t)/(sigma^2+1/s^2+2)',
        'Y':'sigma-s*U-V/s',
        'L2':'(sigma-s)*(sigma-1/s)*(Y+(sigma+s)*U/2)*(Y+(sigma+1/s)*V/2)/sigma^4',
        'P':'(1+s^2)*U*V/(2*s)',
        'Q':'U+V/s',
        'K':'(1+s^2)*L2',
    }
    system=radical_stationary_system(definitions,('s','t'),('sigma',),library)
    system.update(parameters={'sigma':m.div(H,R)},bounds=['1/sigma<s<sigma','0<t<1'],
                  dimensions_in_units_of_radius=['2*w/sqrt(1+s^2)','U*sqrt(1+s^2)','V*sqrt(1+1/s^2)'])
    proof=[
        BOX_SECTIONS[0],CONE_VERTEX_CENTER,*BOX_SECTIONS[1:],
        'Если на основании две вершины, остальные шесть лежат на конусе. У двух поперечных граней совпадают вертикальные координаты соответствующих вершин, поэтому квадраты их горизонтальных смещений равны. Грани находятся на смещениях ±L.',
        'В единицах радиуса сечение задаётся Y²=σ²(X²+L²), крышка Y=σ. От противоположной крышке вершины рёбра имеют горизонтальные проекции U и −V, вертикальные sU и V/s. Вычитание двух уравнений конуса даёт sY−σ²X=(σ²−s²)U/2 и Y/s+σ²X=(σ²−1/s²)V/2.',
        'Прибавляем уравнения и используем Y+sU+V/s=σ. Получаем (σ²+s²+2)U+(σ²+1/s²+2)V=2σ(s+1/s). Поэтому положительные U,V задаёт t от 0 до 1. Две разности Y±σX дают L² в системе. При 1/σ<s<σ обе положительны, поскольку Y=((σ²−s²)U+(σ²−1/s²)V)/(2(s+1/s)). Вершина крышки допустима по выпуклости профиля: её абсцисса и абсцисса противоположной вершины делят промежуток между двух боковых вершин с той же суммой координат.',
        'Компактное замыкание параметров даёт все предельные конфигурации. На краях s=σ или s=1/σ выходит L=0, а площадь прямоугольника в осевом треугольнике не больше половины площади треугольника. Нормированная поверхность S/(4R²) тогда не больше σ/4, строго меньше горизонтального максимума.',
        'На краях t=0,1 одна сторона исчезает. Для оставшегося отрезка вертикального сечения L≤1 и |X|≤√(1−L²). Произведение L на длину отрезка не больше √(1+σ²/16): горизонтальная проекция после умножения на L ограничена 1, а вертикальная — σL(1−L)≤σ/4.',
        'Для σ≤9/4 уточняем границу. Если нижняя по числовой высоте Y точка имеет радиус r, умноженная на L горизонтальная проекция не больше (1+r²)/2 из 2L|X|≤r² и 2L√(1−L²)≤1. Вертикальная проекция не больше σr(1−r). Сумма квадратов не больше 1, так как r²(1−r)≤4/27, а (1+r)(3+r²)≥3. При √3<σ≤9/4 горизонтальный максимум строго больше 1.',
        'Для σ≥9/4 возведённое в квадрат сравнение горизонтального максимума с грубой границей сводится к y⁴+2y³−33y²+64y−32>0 при y=√2σ>19/6. Все коэффициенты сдвинутого многочлена проверены строго положительными.',
        'Поэтому для σ>√3 всякий наклонный максимум, способный улучшить горизонтальный, лежит внутри. Нормированная поверхность там P+Q√K. Проверяем обе производные с положительным корнем w. Множество критических значений конечно: критическое множество полуалгебраично, состоит из конечного числа кусочно-гладко связных компонент, и вдоль каждой компоненты производная поверхности равна нулю.',
        'Берём наибольшее действительное значение из конечной системы и горизонтального кандидата. Все отвечающие этому значению размеры восстанавливаются указанными формулами, горизонтальный случай включается при равенстве.',
    ]
    answer=dict(condition=domain,attained=True,scale=m.mul(q(4),m.power(R,2)),length_scale=R,
                horizontal_candidate=horizontal,tilted_critical_system=system,
                selection='largest normalized value A among the admissible real solutions and the horizontal candidate')
    return answer,proof,tuple(map(q,shifted))


def cone_box_surface(text,want,conditions,method,library):
    """Optimize total area when the supporting triangle has a longest base."""
    import re
    from tasks import source

    if want not in ('dimensions maximizing total surface area','dimensions maximizing TOTAL AREA (not volume)') or method is not None:
        return None
    name=r'([A-Za-z][A-Za-z_0-9]*)'
    start=r'rectangular box (?:inscribed )?in right circular cone of '
    size=re.fullmatch(start+f'base radius {name} and height {name}',text)
    slope=re.fullmatch(start+f'slant length {name} and angle {name} to base',text)
    if not (size or slope):return None
    a,b=(size or slope).groups()
    if len({a,b,'pi','e'})!=4 or {a,b}&(m.FUNCTIONS|set(m.ALIASES)):return None
    conditions={c.replace(' ','').replace('≤','<=') for c in conditions}
    A,B=('s',a),('s',b)
    bound=f'{b}^2<=3*{a}^2' if size else f'{b}<=pi/3'
    tall=bound.replace('<=','>')
    full=library.data.get('tilted_cone_critical_values')
    allowed={bound,f'{a}>0',f'{b}>0'}|({tall} if full else set())
    if (conditions-allowed or {bound,tall}<=conditions or
            bound not in conditions and not full):
        raise Unsupported('Total area needs comparison with tilted rectangles. The current longest-base bound requires H^2<=3*R^2.')
    R,H=(A,B) if size else (m.mul(A,('cos',B)),m.mul(A,('sin',B)))
    lam=m.div(m.mul(('sqrt',q(2)),H),R);ell=source(lam)
    t=m.div(m.add(lam,q(-2)),m.mul(q(2),m.add(lam,q(-1))))
    width=m.mul(m.mul(('sqrt',q(2)),R),m.add(m.ONE,m.neg(t)))
    radius_squared=m.power(R,2)
    maximum=m.div(m.mul(radius_squared,m.power(lam,2)),m.add(lam,q(-1)))
    determinant=triangle_box_determinant_bound()
    if determinant!=1:raise Unsupported('The area comparison on the supporting triangle failed')
    branches=[
        dict(condition=f'{ell}<=2',attained=False,supremum=m.mul(q(4),radius_squared)),
        dict(condition=f'{ell}>2',attained=True,maximum=maximum,
             dimensions=dict(horizontal_sides=(width,width),height=m.mul(H,t)))]
    argument=[
        BOX_SECTIONS[0],CONE_VERTEX_CENTER,*BOX_SECTIONS[1:],
        'Зафиксировать L. При горизонтальном сечении полуширины X берём высоту h=H−g(X). На участке допустимых X максимизируем 2Xh+2L(2X+h). Касательные в ±X в точке максимума образуют содержащий профиль треугольник, у которого тот же горизонтальный максимум: производная совпадает, а треугольный профиль является вогнутым квадратным трёхчленом. Это верно и при нулевой предельной высоте.',
        'У касательной наклон не больше H/R≤√3, поэтому основание B треугольника является его диаметром. Для повёрнутого прямоугольника полные длины u,v удовлетворяют u/U+v/V≤1 из барицентрических координат. Для полуразмеров U/2,V/2 сравнение определителей в единичном шестиугольнике даёт UV≤Bh, где h теперь высота треугольника.',
        'Пусть U≥V. Диаметр даёт U≤B. Из UV≤Bh следует U+V≤B+h: при U≤h это сразу, а при h≤U≤B выпуклая функция U+Bh/U ограничена указанной величиной на концах. Максимизатор при u=tU,v=(1−t)V можно искать при t≥1/2. Произведение uv и линейная комбинация u+v тогда не превосходят значений при U=B,V=h. Получена граница для всех поворотов.',
        'При фиксированной высоте tH у горизонтальной коробки диагональ верхней грани не больше 2R(1−t). Квадрат максимизирует и произведение, и сумму сторон. Полная поверхность после деления на 4R² равна 1+(λ−2)t+(1−λ)t². Производная даёт внутренний максимум при λ>2, а при λ≤2 максимум достигается лишь на вырожденной границе.'
    ]
    cert={}
    theorem='method.longest_base_box_surface'
    if bound not in conditions:
        horizontal=branches[1]
        candidate=dict(normalized_value=m.div(maximum,m.mul(q(4),radius_squared)),dimensions=horizontal['dimensions'])
        tilted,proof,coefficients=tilted_cone_area(R,H,candidate,tall,library)
        theorem='method.tilted_cone_critical_values'
        cert['boundary_polynomial_positive_coefficients']=coefficients
        if tall in conditions:
            argument=proof
            branches=[tilted]
        else:
            for branch in branches:branch['condition']=bound+' and '+branch['condition']
            branches.append(tilted)
            argument.extend(proof)
    return dict(theorem=theorem,proof='\n'.join(argument),radius=R,height=H,
                determinant_bound=q(determinant),normalized_quadratic=(m.ONE,m.add(lam,q(-2)),m.add(m.ONE,m.neg(lam))),
                source_conditions=sorted(conditions),**cert),dict(branches=branches,scope='vertex-inscribed boxes with positive dimensions')


def source_global_extrema(task, library):
    """Read compact bound statements before applying their mathematical reductions."""
    import re
    from verify import same_value

    meta = task.get('source', {})
    provenance = {'exercise', 'printed_subpart', 'pdf_page', 'printed_page', 'pdf_sha256', 'literal_requirement'}
    want = task.get('requested_output')
    raw_text = task.get('source_formula')
    if (not library.data.get('source_global_extrema') or not isinstance(meta, dict) or set(meta) - provenance
            or not isinstance(want, list) or len(want) != 1 or not isinstance(raw_text, str)
            or meta.get('literal_requirement', want[0]) != want[0]
            or set(task) - {'id', 'kind', 'source', 'source_formula', 'stated_conditions', 'requested_output', 'suggested_method'}):
        raise Unsupported('The complete source extremum and its conditions have to be bound')
    conditions = task.get('stated_conditions', [])
    if not isinstance(conditions, list) or not all(isinstance(condition, str) for condition in conditions):
        raise Unsupported('Unknown source domain')
    kind = task['kind']
    if kind == 'optimization_application':
        if library.data.get('longest_base_box_surface'):
            surface=cone_box_surface(raw_text,want[0],conditions,task.get('suggested_method'),library)
            if surface is not None:return surface
        if library.data.get('support_triangle_box_extrema'):
            cap=quadratic_cap_box_volume(raw_text,want[0],conditions,task.get('suggested_method'))
            if cap is not None:return cap
        return optimization_source(raw_text, want[0], conditions, task.get('suggested_method'))
    if kind in ('prove_inequality', 'constrained_extrema', 'multivariate_extrema_proof'):
        return analytical_extremum_source(kind, raw_text, want[0], conditions, task.get('suggested_method'))
    if want != ['infimum_and_supremum'] or not conditions or task.get('suggested_method'):
        raise Unsupported('Exact upper and lower bounds on a stated region are required')
    normalize = lambda s: s.replace('²', '^2').replace('³', '^3').replace('≤', '<=').replace(' ', '')
    text = normalize(raw_text)
    conditions = list(map(normalize, conditions))
    names = lambda s: sorted(set(re.findall(r'[A-Za-z_]\w*', s)) - m.FUNCTIONS - set(m.ALIASES) - {'pi', 'e'})
    coords = sorted(set(names(','.join(conditions))))
    if not 1 <= len(coords) <= 4 or not set(names(text)) <= set(coords):
        raise Unsupported('The bound region must bind each free real variable')
    f = m.parse(text, None, coords)
    variables = [('s', name) for name in coords]
    if domain_conditions(f):
        raise Unsupported('The original expression has additional real-domain restrictions')

    def complete(method, proof, plan, value):
        def encode(v):
            if type(v) is F:return q(v)
            if isinstance(v, dict):return {k: encode(w) for k, w in v.items()}
            if isinstance(v, (tuple, list)):return tuple(map(encode, v))
            return v
        return encode(dict(theorem='method.' + method, proof=proof, coordinates=coords, source_expression=f,
                           source_conditions=conditions, **plan)), encode(value)

    if conditions == [','.join(coords) + '>0']:
        if f[0] != 'mul':raise Unsupported('The positive-domain objective does not have a bounded exponential profile')
        profiles = [(a, b[1]) for a, b in (f[1:], f[:0:-1]) if b[0]=='exp']
        if len(profiles) != 1:raise Unsupported('A single exponential scale is required')
        linear, exponent = profiles[0]
        A, c, offset = quadratic_coefficients(linear, coords)
        B, w, decay_offset = quadratic_coefficients(exponent, coords)
        if any(any(row) for row in A+B) or offset or decay_offset or min(c) < 0 or not any(c) or max(w) >= 0:
            raise Unsupported('A nonnegative linear height and strictly positive attenuation are required')
        lamb = min(-wj/cj for wj, cj in zip(w, c) if cj)
        axis = next(i for i, (cj, wj) in enumerate(zip(c, w)) if cj and -wj == lamb*cj)
        attained = all(-wj == lamb*cj for wj, cj in zip(w, c))
        value = m.div(m.simplify(('exp', q(-1))), q(lamb))
        limit_point = tuple(q(1/(lamb*cj)) if j == axis else m.ZERO for j, cj in enumerate(c))
        point = tuple(q(1/(lamb*sum(c))) for _ in c) if attained else limit_point
        return complete('positive_orthant_exponential_bound',
            'Обозначаем линейный множитель через s. Отношения коэффициентов дают затухание как минимум λs. '
            'Сравниваем с s·exp(−λs), затем проверяем достижимость или подход вдоль оптимальной оси.',
            dict(linear_coefficients=c, attenuation=tuple(-x for x in w), optimal_scale=lamb, axis=axis),
            dict(infimum=m.ZERO, supremum=value, minimum_attained=False, maximum_attained=attained,
                 minimum_limit_point=tuple(m.ZERO for _ in c),
                 **{('maximum_point' if attained else 'maximum_limit_point'):point}))

    A, linear, offset = quadratic_coefficients(f, coords)
    zero = tuple(F(0) for _ in coords)
    axes = tuple(tuple(F(i == j) for i in range(len(coords))) for j in range(len(coords)))
    squared = m.dot(variables, variables)
    ball_match = re.fullmatch(r'([^<>=]+)(<=|<)(\d+(?:/\d+)?)', conditions[0]) if len(conditions) == 1 else None
    if ball_match:
        shape, op, radius = ball_match.groups()
        radius = F(radius)
        if radius <= 0:raise Unsupported('A positive bound radius is required')
        region = m.parse(shape, None, coords)
        if domain_conditions(region):raise Unsupported('An unverified restriction remains in the region')
        if same_value(region, squared):
            if any(A[i][j] for i in range(len(coords)) for j in range(i)):
                raise Unsupported('The ball proof needs a diagonal or translated isotropic objective')
            diag = [row[i] for i, row in enumerate(A)]
            if not any(linear):
                extrema = diagonal_ball(diag, radius, offset, closed=op == '<=')
                return complete('diagonal_ball_bounds',
                    'Сравниваем коэффициенты квадратов с крайними коэффициентами и нулём. '
                    'Точные грани получаются в центре или по соответствующим осям шара.',
                    dict(diagonal=diag, radius_squared=radius, comparisons=extrema), {
                        **{k: v['bound'] for k, v in extrema.items()},
                        'minimum_attained':extrema['infimum']['attained'], 'maximum_attained':extrema['supremum']['attained']})
            if diag[0] == 0 or len(set(diag)) != 1:
                raise Unsupported('Complete a common isotropic square before using the distance bounds')
            scale = diag[0]
            p = tuple(-coeff/(2*scale) for coeff in linear)
            p2 = dot(p, p)
            R = m.simplify(('sqrt', q(radius)))
            rho = m.simplify(('sqrt', q(p2)))
            direction = tuple(m.div(q(t), rho) for t in p) if p2 else tuple(map(q, axes[0]))
            boundary = tuple(m.mul(R, t) for t in direction)
            near = tuple(map(q, p)) if p2 <= radius else boundary
            far = tuple(m.neg(t) for t in boundary)
            c = q(offset-scale*p2)
            values = [m.add(c, m.mul(q(scale), m.power(d, 2))) for d in
                      (m.add(rho, m.neg(R)) if p2 > radius else m.ZERO, m.add(rho, R))]
            points = [near, far]
            attained = [op=='<=' or p2 < radius, op=='<=']
            if scale < 0:
                values.reverse()
                points.reverse()
                attained.reverse()
            return complete('translated_ball_distance',
                'Выделяем квадрат расстояния до центра целевой формы. '
                'Неравенство треугольника даёт обе оценки, а точные направления и центр устанавливают достижимость.',
                dict(translation=p, scale=scale, completed_offset=c, radius_squared=radius),
                dict(infimum=values[0],supremum=values[1],minimum_attained=attained[0],maximum_attained=attained[1],
                     **{('minimum_point' if attained[0] else 'minimum_limit_point'):points[0],
                        ('maximum_point' if attained[1] else 'maximum_limit_point'):points[1]}))

        abs_sum = reduce(m.add, [('abs', x) for x in variables])
        if op == '<=' and same_value(region, abs_sum):
            vertices = [tuple(s*radius*t for t in row) for row in axes for s in (1, -1)]
            plan, values = quadratic_hull(A, linear, offset, vertices)
            return complete('convex_quadratic_hull',
                'Ограничение на сумму модулей задаёт выпуклую оболочку осевых вершин. '
                'Квадратичные остатки неотрицательны. Максимум ищем по вершинам, минимум подтверждаем '
                'допустимой комбинацией и неотрицательностью производных по всем вершинам.',
                dict(vertices=vertices, **plan), dict(values, minimum_attained=True, maximum_attained=True))

    positive_simplex = re.fullmatch(r'0<=(.+?)<=(\d+(?:/\d+)?)', conditions[-1])
    if len(conditions) == 2 and positive_simplex:
        maximum = F(positive_simplex[2])
        coordinate_bounds = re.fullmatch(r'0<=(.+?)<=(\d+(?:/\d+)?)', conditions[0])
        total = m.parse(positive_simplex[1], None, coords)
        if (maximum > 0 and coordinate_bounds and coordinate_bounds[1].split(',') == coords
                and F(coordinate_bounds[2]) >= maximum and not domain_conditions(total)
                and same_value(total,reduce(m.add,variables))):
            vertices = [zero, *[tuple(maximum*t for t in row) for row in axes]]
            plan, values = quadratic_hull(A, linear, offset, vertices)
            return complete('convex_quadratic_hull',
                'Деление координат на верхнюю грань суммы даёт веса выпуклой комбинации вершин. '
                'Максимум выпуклой формы достигается на вершине. Для минимума проверяем знак приращений по всем вершинам.',
                dict(vertices=vertices, **plan), dict(values, minimum_attained=True, maximum_attained=True))

    cap = re.fullmatch(r'(.+?)<=(\w+)<=(\d+(?:/\d+)?)',conditions[0]) if len(conditions)==1 else None
    if cap and cap[2] in coords and F(cap[3]) > 0 and not any(any(row) for row in A):
        from ray_proofs import compare_scalar
        height = coords.index(cap[2])
        other = [x for j,x in enumerate(variables) if j!=height]
        raw_cap = m.parse(cap[1],None,coords)
        if domain_conditions(raw_cap) or not other or not same_value(raw_cap,m.dot(other,other)):
            raise Unsupported('The cap does not bound the Euclidean radius as required')
        limit = q(F(cap[3]))
        coefficients = [a for j,a in enumerate(linear) if j!=height]
        length = m.simplify(('sqrt', q(dot(coefficients,coefficients))))
        R = m.simplify(('sqrt',limit))
        values = []
        for sign in (-1,1):
            bottom = sign*linear[height] <= 0
            use_radius = [m.ZERO,R]
            if bottom and linear[height]:
                critical=m.div(m.mul(q(-sign),length),q(2*linear[height]))
                if compare_scalar(critical,m.ZERO)>0 and compare_scalar(critical,R)<0:
                    use_radius.append(critical)
            candidates=[]
            for radius in use_radius:
                h=m.power(radius,2) if bottom else limit
                value=m.add(q(offset),m.add(m.mul(q(linear[height]),h),m.mul(q(sign),m.mul(length,radius))))
                xy=[m.div(m.mul(q(sign*a),radius),length) for a in coefficients] if length!=m.ZERO else [radius,*[m.ZERO]*(len(other)-1)]
                xy.insert(height,h)
                candidates.append((value,xy))
            best=candidates[0]
            for pair in candidates[1:]:
                if compare_scalar(pair[0],best[0])==sign:best=pair
            values.append(best)
        return complete('affine_height_cap_bounds',
            'Фиксируем горизонтальный радиус. Неравенство Коши определяет крайние направления, '
            'знак вертикального коэффициента выбирает высоту. Остаются концы и стационарная точка скалярного профиля.',
            dict(height=cap[2],upper_height=limit,radial_linear_norm=length),
            dict(infimum=values[0][0],supremum=values[1][0],minimum_point=values[0][1],maximum_point=values[1][1],
                 minimum_attained=True,maximum_attained=True))
    raise Unsupported('The original region needs another global bound or feasibility reduction')


def analytical_extremum_source(kind, text, output, conditions, suggestion):
    """Select exact structural theorems, with source hypotheses and equality cases."""
    import re
    from operations import expression_positions
    from verify import same_value

    def proof(method, argument, **value):
        return dict(theorem='method.'+method,proof=argument,source_conditions=conditions,suggestion=suggestion),value
    if kind=='constrained_extrema':
        if (text!='sum_(i,j=1)^n a_ij*x_i*x_j' or output!='all_constrained_extremum_points'
                or conditions!=['a_ij=a_ji','sum x_i²=1'] or suggestion):
            raise Unsupported('The original form must be symmetric on the full unit sphere')
        return proof('orthogonal_quadratic_extrema',
            'В ортонормированном собственном базисе форма равна сумме λ_i t_i². На сфере это выпуклая комбинация '
            'собственных чисел. Крайние собственные подпространства дают точные случаи равенства.',
            infimum='λ_min(A)',supremum='λ_max(A)',minimizers='the unit vectors of ker(A−λ_min I)',
            maximizers='the unit vectors of ker(A−λ_max I)',other_eigenvalues='saddles on the sphere')
    if kind=='prove_inequality' and output=='proof':
        if (text=='(x^n+y^n)/2>=((x+y)/2)^n' and conditions==['n>=1','x,y>=0']
                and suggestion in (None,'minimize (x^n+y^n)/2 subject to x+y=s')):
            return proof('convex_power_fixed_sum',
                'Фиксируем сумму. Функция t↦tⁿ выпукла на положительной полуоси и непрерывна в нуле при n≥1. '
                'Среднее двух значений не меньше значения при среднем аргументе.',
                inequality=True,equality='x=y or n=1')
        if (text=='sum a_i*x_i<=(sum a_i^k)^(1/k)*(sum x_i^kprime)^(1/kprime)'
                and conditions==['a_i,x_i>=0','k>1','1/k+1/kprime=1']
                and suggestion in (None,'minimize product of the norms with sum a_i*x_i fixed')):
            return proof('holder_normalized_conjugate_powers',
                'При положительных нормах нормируем обе последовательности. По выпуклости степенной функции '
                'произведение каждой пары не превышает uᵏ/k+vᵏ′/k′. После суммирования правая часть равна 1. '
                'Нулевая норма зануляет исходную линейную форму.',
                inequality=True,equality='zero norm or proportional a_i^k and x_i^kprime',
                constrained_minimum='at fixed positive linear form the necessary norm is achieved by x_i proportional to a_i^(k−1)')
        if (text=='det(A)^2<=prod_i sum_j a_ij²' and conditions==['square real A of order n']
                and suggestion in (None,'consider extreme determinant on sets with all squared row norms fixed')):
            return proof('hadamard_orthogonal_rows',
                'Последовательно вычитаем ортогональные проекции предыдущих строк. Определитель сохраняется, '
                'длины строк убывают, а для ортогональных строк квадрат определителя равен произведению квадратов длин. '
                'При заданных нормах верхняя грань достигается на ортогональных строках. Нулевая строка зануляет обе части.',
                inequality=True,equality='a zero row or pairwise orthogonal rows')
    if kind=='multivariate_extrema_proof' and not conditions and not suggestion:
        text=text.replace('²','^2')
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES))
        if len(names)!=2:raise Unsupported('The source proof must involve two real coordinates')
        raw=m.parse(text,None,names);x,y=[('s',v) for v in names]
        if domain_conditions(raw):raise Unsupported('The original field and paths must be defined')
        if output=='prove infinitely many maxima and no minima':
            waves={e for _,e in expression_positions(raw) if e[0] in ('cos','exp')}
            c=next((e for e in waves if e[0]=='cos'),None);w=next((e for e in waves if e[0]=='exp'),None)
            if len(waves)!=2 or c is None or w is None:
                raise Unsupported('One cosine and one exponential along independent axes are required')
            C,cx,cd=quadratic_coefficients(c[1],names);W,wy,wd=quadratic_coefficients(w[1],names)
            if any(any(row) for row in C+W) or cx[1] or wy[0] or cd or wd or cx[0]<=0 or wy[1]<=0:
                raise Unsupported('The cosine and exponential must have positive independent coordinate slopes')
            u,v=('s','__cosine'),('s','__exponential')
            transformed=m.substitute(raw,{c:u,w:v})
            samples=[m.simplify(m.substitute(transformed,{u:q(i),v:q(j),y:q(k)}))
                     for i,j,k in ((1,0,0),(1,1,0),(0,1,0),(0,1,1))]
            s=[m.num(t) for t in samples]
            if any(t is None for t in s):raise Unsupported('The periodic profile coefficients must be exact rational numbers')
            a,d=s[0],-s[2];b=s[1]-a+d;g=-s[3]-d
            rebuilt=m.add(m.mul(m.add(q(a),m.mul(q(b),v)),u),m.neg(m.mul(m.add(m.mul(q(g),y),q(d)),v)))
            if min(a,b,g)<=0 or not same_value(transformed,rebuilt):
                raise Unsupported('The periodic profile does not have the required positive factors')
            return proof('separated_periodic_extrema',
                'Сначала зануляем синус по первой координате. По второй остаётся линейное уравнение. '
                'В этих точках гессиан диагонален. Чётные индексы дают две отрицательные кривизны, нечётные — разные знаки.',
                maxima={names[0]:'2πk/'+str(cx[0]),names[1]:q((b-d)/g-1/wy[1])},minima='empty',
                saddles={names[0]:'(2k+1)π/'+str(cx[0]),names[1]:q((-b-d)/g-1/wy[1])},index='all integers')
        if output=='does a minimum along every line imply a minimum in the plane; examine given counterexample' and raw[0]=='mul':
            ratios=[];linear_scales=[]
            for factor in raw[1:]:
                matrix,l,offset=quadratic_coefficients(factor,names)
                if offset or l[0]<=0 or l[1] or matrix[0][0] or matrix[0][1] or matrix[1][1]>=0:
                    raise Unsupported('Each factor must vanish on a positive parabolic branch')
                ratios.append(-matrix[1][1]/l[0]);linear_scales.append(l[0])
            if ratios[0]==ratios[1]:raise Unsupported('Coincident branches do not enclose a negative region')
            mid=sum(ratios)/2
            coefficient=(mid-ratios[0])*(mid-ratios[1])*linear_scales[0]*linear_scales[1]
            return proof('directional_minimum_between_parabolic_curves',
                'На прямой с ненулевым изменением первой координаты ведущий член положителен и имеет порядок 2. '
                'На оси второй координаты произведение положительно и имеет порядок 4. '
                'Парабола с коэффициентом между двумя корнями даёт отрицательные значения сколь угодно близко к началу.',
                implication_holds=False,curve=names[0]+'='+str(mid)+'*'+names[1]+'^2',negative_quartic_coefficient=q(coefficient))
    raise Unsupported('The printed extremum argument needs another structural theorem')


def affine_section_geometry(text, output):
    import re
    from cartesian_fields import mv_sum, symbolic_quadratic
    from model import ONE, ZERO
    from tasks import entailed_domain_guards, guard_source, source
    axes=list('xyz')
    prefix,sep,plane=text.partition(' cut by plane ')
    if not sep:return None
    body,_,equation=prefix.partition(' ')
    cylinder=prefix.startswith('elliptical cylinder ')
    if cylinder:
        equation=prefix.removeprefix('elliptical cylinder ')
        if output!='area of resulting ellipse':return None
        lhs,eq,rhs=plane.partition('=')
        if not eq:return None
        pieces=[lhs,rhs]
    elif body=='ellipsoid' and output=='central section area':
        given=re.fullmatch(r'normal to ([A-Za-z_]\w*)=\(([^()]+(?:\([^()]*\)[^()]*)*)\),\s*\|\|\1\|\|=1',plane)
        if not given:return None
        pieces=given[2].split(',')
        if len(pieces)!=3:return None
    else:return None
    left,eq,right=equation.partition('=')
    if not eq:return None
    formulas=[re.sub(r'\b(sin|cos)\s+([A-Za-z_]\w*)',r'\1(\2)',v.replace('²','^2'))
              for v in (left,right,*pieces)]
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',' '.join(formulas)))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi',*axes})
    a,b,*orientation=[m.parse(f,None,axes+names) for f in formulas]
    guards=domain_conditions(a)+domain_conditions(b)
    if any(domain_conditions(e) for e in orientation) or any(
            m.contains(u,('s',x)) for _,u in guards for x in axes):
        return None
    domain=[guard_source(g) for g in entailed_domain_guards(guards)]
    ctx=m.context(dict(variable='__section',parameters=names,parameter_conditions=domain))
    if not all(known_guard(g,ctx) for g in guards):return None
    A,linear,c=symbolic_quadratic(m.add(a,m.neg(b)),axes)
    r=m.neg(c)
    diagonal=[A[i][i] for i in range(3)]
    if (any(t!=ZERO for t in linear) or any(A[i][j]!=ZERO for i in range(3) for j in range(3) if i!=j)
            or m.sign(r,ctx)!=1 or cylinder and diagonal[-1]!=ZERO):return None
    diagonal=diagonal[:2] if cylinder else diagonal
    if any(m.sign(v,ctx)!=1 for v in diagonal):return None
    if cylinder:
        quad,normal,offset=symbolic_quadratic(m.add(orientation[0],m.neg(orientation[1])),axes)
        if any(v!=ZERO for row in quad for v in row) or offset!=ZERO or all(v==ZERO for v in normal):return None
    else:
        normal=orientation
        if any(not m.constant_defined(v,ctx) for v in normal):return None
    components=[m.div(r,v) for v in diagonal]
    mul=lambda values:reduce(m.mul,values,ONE)
    squared_norm=mv_sum(m.power(z,2) for z in normal)
    if cylinder:
        C=normal[-1]
        if C==ZERO:return None
        planar=m.div(m.mul(mul(components),squared_norm),m.power(C,2))
        value=dict(defined_when=source(C)+'!=0',
                   degenerate='When the vertical coefficient vanishes, a nonzero normal gives two generators.')
        proof='Проектируем плоский эллипс на основание цилиндра. Обратный масштаб площади равен отношению нормы нормали к модулю её вертикальной компоненты.'
    else:
        planar=m.div(mul(components),mv_sum(m.mul(v,m.power(z,2)) for v,z in zip(components,normal)))
        value={}
        proof='Нормируем оси эллипсоида. Сечение шара плоскостью через центр даёт единичный круг. Площадь умножается на определитель масштаба, делённый на длину преобразованной единичной нормали.'
    value['area']=m.mul(m.PI,('sqrt',planar))
    return dict(theorem='method.affine_section_metric',proof=proof,source_model=text,
                axis_scales_squared=components,normal=normal,section_area_scale_squared=planar,
                original_domain=domain),value


def optimization_source(text, output, conditions, suggestion):
    """Use coordinate-free inequalities or a verified scalar profile after modeling."""
    import re
    from graphs import optimize_geometric_profile
    from verify import same_value

    if conditions or suggestion:raise Unsupported('The additional source constraints need to be included in the model')
    name=r'([A-Za-z]\w*)'
    def proof(method, statement, **value):
        return dict(theorem='method.'+method,proof=statement,source_model=text),value
    def scalar_profile(params, profile, statement, dimensions, sense, **fields):
        variable=next(v for v in ('t','u','v','w') if v not in params)
        def parse(s):return m.parse(s.replace('@',variable),variable,params)
        curve, signs, reason, branches=optimize_geometric_profile(profile,('v',variable),parse)
        point,=branches
        if not point['attained']:raise Unsupported('The selected physical shape is degenerate')
        at=lambda s:m.simplify(m.substitute(parse(s),{('v',variable):point['point']}))
        plan,result=proof('explicit_optimization_profiles',statement+' '+reason,
            optimizing_configuration={k:at(v) for k,v in dimensions.items()},extremum=sense,attained=True)
        plan.update(profile=curve,derivative_sign=signs,normalized_variable=variable,optimal_parameter=point['point'],**fields)
        return plan,result

    if hit:=re.fullmatch(r'positive '+name+r' as (product of n positive factors|sum of n summands)',text):
        a,meaning=hit.groups()
        if meaning.startswith('sum') and output=='minimize sum of squares':
            return proof('equalization_convex_cost',
                'Вычитаем общее среднее из каждого слагаемого. Сумма попарных приращений равна нулю, '
                'и остаток после вычитания n квадратов среднего равен сумме квадратов отклонений.',
                minimum=a+'^2/n',minimizers='all summands equal '+a+'/n')
        if meaning.startswith('product') and output=='minimize sum of reciprocals':
            return proof('equalization_convex_cost',
                'Произведение обратных множителей фиксировано. Их арифметическое среднее не меньше '
                'геометрического; равенство требует одинаковых множителей.',
                minimum='n/'+a+'^(1/n)',minimizers='all factors equal '+a+'^(1/n)')
        if meaning.startswith('product') and output=='minimize sum of specified positive powers':
            return proof('equalization_convex_cost',
                'Переходим к логарифмам положительных множителей. Их сумма фиксирована, а сумма e в степенях p_i t_i строго выпукла. '
                'Формула обеспечивает общую производную λ; сумма линейных частей при допустимых отклонениях равна нулю.',
                condition='all powers p_i>0',lambda_equation='prod_i (λ/p_i)^(1/p_i)='+a,
                minimizers='x_i=(λ/p_i)^(1/p_i)',minimum='λ sum_i 1/p_i')
    if text=='n given planar points with masses m_i' and output=='location P minimizing moment of inertia':
        return proof('centering_quadratic_cost',
            'Центр масс зануляет взвешенную сумму отклонений. После переноса начала координат '
            'момент равен моменту в центре масс плюс полная масса, умноженная на квадрат расстояния до него.',
            minimizer='P=Σ_i m_i P_i / Σ_i m_i for positive total mass',zero_mass='every point')
    if text=='unit sphere with given points M_i' and output=='point minimizing sum of squared distances':
        return proof('centering_quadratic_cost',
            'Квадрат нормы точки сферы фиксирован. После раскрытия квадратов минимизация равносильна '
            'максимизации скалярного произведения с суммой данных радиус-векторов.',
            minimizer='Σ_i M_i/||Σ_i M_i|| when the sum is nonzero',zero_sum='every point on the unit sphere')
    if (hit:=re.fullmatch('open rectangular bath of volume '+name,text)) and output=='dimensions minimizing material area':
        V=hit[1];s='cbrt('+V+')'
        return scalar_profile([V],('opposite_powers',1,2,4,1,False),
            'При заданных объёме и площади дна квадрат уменьшает периметр. '
            'Сторона равна кубическому корню из объёма, умноженному на t. Площадь сводится к t²+4/t.',
            {'base_side':s+'*@','height':s+'/@^2'},'minimum',parameter_conditions=[V+'>0'])
    if (hit:=re.fullmatch('open cylindrical trough with semicircular cross-section, total surface '+name,text)) and output=='dimensions maximizing volume':
        S=hit[1];r='sqrt('+S+'/pi)*@'
        return scalar_profile([S],('rational','@*(1-@^2)',(F(0),F(1)),'maximum'),
            'Бок и два полукруглых торца дают площадь πrL+πr². После исключения длины объём пропорционален t(1−t²).',
            {'radius':r,'length':'sqrt('+S+'/pi)*(1-@^2)/@'},'maximum',parameter_conditions=[S+'>0'])
    shell_bound = ('Для любого k≥0 по неравенству Коши √(r²+k²)−(2/3)k≥√5·r/3. '
                   'Равенство требует k=2r/√5, и в этом положении оставшаяся высота тела положительна.')
    if (hit:=re.fullmatch('right circular cylinder topped by right circular cone with total outside area '+name,text)) and output=='dimensions maximizing volume':
        S=hit[1];r='sqrt('+S+'/(pi*(3+sqrt(5))))'
        return scalar_profile([S],('rational','3*@-@^3',(F(0),None),'maximum'),
            'Из площади исключаем высоту цилиндра. При фиксированном радиусе максимизируем k/3−ℓ/2. '
            +shell_bound+' Нормируем радиус на '+r+'. Верхняя оценка объёма сводится к 3t−t³ и достигается.',
            {'base_radius':r+'*@','cone_height':'2*'+r+'*@/sqrt(5)',
             'cylinder_height':r+'*@*(1+1/sqrt(5))'},'maximum',parameter_conditions=[S+'>0'])
    if (hit:=re.fullmatch('rectangular prism with equal regular square pyramids on both bases; volume '+name,text)) and output=='face-to-base inclination minimizing outside area':
        V=hit[1];s='cbrt(3*'+V+'/sqrt(5))'
        return scalar_profile([V],('opposite_powers',1,2,2,1,False),
            'Из объёма исключаем высоту призмы. При стороне s и высоте пирамиды k остаётся '
            '4V/s+4s(ℓ−2k/3), где ℓ²=k²+(s/2)². '+shell_bound+
            ' Берём в этой оценке r=s/2. После нормировки стороны остаётся t²+2/t.',
            {'square_base_side':s+'*@','pyramid_height':s+'*@/sqrt(5)','prism_height':s+'*@/sqrt(5)',
             'tangent_of_inclination':'2/sqrt(5)'},'minimum',parameter_conditions=[V+'>0'])
    if (hit:=re.fullmatch('rectangle of perimeter 2'+name+' rotated about one side',text)) and output=='maximize volume of resulting solid':
        p=hit[1]
        return scalar_profile([p],('unit_product',1,2),
            'Сторона оси вращения и радиус цилиндра имеют фиксированную сумму. Нормируем первую сторону на полупериметр.',
            {'axis_side':p+'*@','radius_side':p+'*(1-@)'},'maximum',parameter_conditions=[p+'>0'])
    if (hit:=re.fullmatch('triangle of perimeter 2'+name+' rotated about one side',text)) and output=='maximize volume of resulting solid':
        p=hit[1]
        return scalar_profile([p],('unit_product',1,1),
            'Объём вращения равен πb h²/3, где b — выбранная сторона и h — высота. Для заданных b и суммы '
            'двух других сторон выпуклость расстояния даёт наибольшую высоту при равных сторонах. Тогда h²=p(p−b).',
            {'axis_side':p+'*@','equal_sides':p+'*(1-@/2)','height':p+'*sqrt(1-@)'},'maximum',parameter_conditions=[p+'>0'])
    if (hit:=re.fullmatch('rectangular box in a hemisphere of radius '+name,text)) and output=='dimensions maximizing volume':
        R=hit[1]
        return scalar_profile([R],('unit_product',F(1,2),1),
            'Пусть m — наименьшее полуребро. Норма центра не меньше m по условию высоты всех вершин. '
            'Наибольший квадрат расстояния до вершины содержит сумму квадратов полурёбер, квадрат нормы центра и '
            'дважды сумму модулей проекций центра, умноженных на полурёбра. Последняя сумма не меньше m². '
            'Значит два других полуребра ограничены кругом радиуса √(R²−4m²). Квадрат на горизонтальном основании достигает оценки.',
            {'height':R+'*sqrt(@)','square_base_side':R+'*sqrt(2*(1-@))'},'maximum',parameter_conditions=[R+'>0'])
    if output=='dimensions maximizing volume' and text=='rectangular parallelepiped in x²/a²+y²/b²+z²/c²=1':
        return proof('orthogonal_quadratic_extrema',
            'Усредняем квадратичное ограничение по всем вершинам. Среднее не меньше суммы квадратов полурёбер '
            'с весами, заданными диагональю матрицы формы в рёберном базисе. Средние и неравенство Адамара '
            'ограничивают произведение полурёбер, а выбор собственных направлений даёт равенство.',
            optimum_dimensions='2|a|/√3, 2|b|/√3, 2|c|/√3',maximum_volume='8|abc|/(3√3)')
    if text=='point M0=(x0,y0,z0), plane A*x+B*y+C*z+D=0' and output=='shortest distance':
        return proof('affine_orthogonal_projection',
            'Разность точки и её ортогональной проекции направлена по нормали. Любой другой отрезок до плоскости '
            'имеет ту же нормальную компоненту и добавляет неотрицательный квадрат касательной компоненты.',
            condition='A²+B²+C²>0',distance='|A*x0+B*y0+C*z0+D|/sqrt(A²+B²+C²)')
    if text=='two spatial lines through P_i=(xi,yi,zi) in directions d_i=(mi,ni,pi)' and output=='shortest distance':
        return proof('affine_orthogonal_projection',
            'Разности точек двух прямых образуют аффинную плоскость, если направления независимы, '
            'и аффинную прямую, если направления параллельны. Ближайший к нулю вектор получается ортогональным проектированием.',
            non_parallel='|(P2−P1)·(d1×d2)|/||d1×d2||',
            parallel='||(P2−P1)×d1||/||d1||',condition='both line directions are nonzero')
    if (hit:=re.fullmatch(r'parabola y=(.+), straight line (.+)=0',text)) and output=='shortest distance':
        x,y=('s','x'),('s','y');trace=m.parse(hit[1].replace('²','^2'),None,['x'])
        plane=m.parse(hit[2],None,['x','y'])
        matrix,c,offset=quadratic_coefficients(plane,['x','y'])
        if domain_conditions(trace) or domain_conditions(plane) or any(any(r) for r in matrix) or not any(c):
            raise Unsupported('An actual parabola and straight line are required')
        restricted=m.substitute(plane,{y:trace})
        A,B,C=quadratic_coefficients(restricted,['x']);a=A[0][0];b=B[0]
        if a==0:raise Unsupported('The line projection needs a quadratic sign certificate')
        center=-b/(2*a);minimum=C-b*b/(4*a)
        if a*minimum<=0:raise Unsupported('The line intersects or touches the parabola; isolate the zero positions')
        return proof('affine_orthogonal_projection',
            'Подставляем уравнение параболы в формулу расстояния до прямой и выделяем полный квадрат. '
            'Знак подстановки постоянен, поэтому ближайшая точка соответствует вершине этого квадрата.',
            distance=m.div(q(abs(minimum)),m.simplify(('sqrt',q(dot(c,c))))),
            closest_parabola_point=(q(center),m.simplify(m.substitute(trace,{x:q(center)}))))
    if text in ('central conic A*x²+2*B*x*y+C*y²=1',
                 'central quadric A*x²+B*y²+C*z²+2*D*x*y+2*E*y*z+2*F*x*z=1') and output=='semiaxes':
        matrix='[[A,B],[B,C]]' if text.startswith('central conic') else '[[A,D,F],[D,B,E],[F,E,C]]'
        return proof('orthogonal_quadratic_extrema',
            'Ортогональный базис собственных векторов диагонализует исходную форму. '
            'Для ненулевого собственного числа положительный масштаб координаты равен обратному корню из его модуля. '
            'Знак определяет тип соответствующей оси. Нулевое собственное число оставляет свободное направление.',
            matrix=matrix,semiaxis='1/√|λ_i| for λ_i≠0 along the corresponding eigenvector',
            feasibility='at least one λ_i>0 is necessary and sufficient for a nonempty real level')
    if output in ('area of resulting ellipse','central section area'):
        if (section:=affine_section_geometry(text,output)) is not None:return section
    if text=='Fermat least-time ray, two uniform media separated by plane, speeds v1 and v2' and output=='derive refraction law':
        return proof('weighted_distance_variation',
            'Пересечение луча с границей выбираем минимумом суммы расстояний до концов с весами 1/v₁ и 1/v₂. '
            'Производная вдоль границы даёт равенство касательных компонент. При строго положительных расстояниях '
            'концов до границы функция строго выпукла и растёт к бесконечности.',
            snell_law='sin(i)/v1=sin(r)/v2',condition='v1,v2>0 and endpoints in the interiors of opposite half-spaces')
    if text=='prism of apex angle alpha and refractive index n' and output=='incidence angle of least deviation and minimum deviation':
        return proof('symmetric_refraction_angles',
            'Внутренние углы дают сумму α. Для g(t)=arcsin(n sin t) производная чётна. '
            'При n>1 она растёт с |t|, при 0<n<1 убывает. Поэтому g(t)+g(α−t) имеет крайнее значение в середине. '
            'Знак суммы минус α совпадает со знаком n−1, поскольку g′−1 имеет этот знак внутри допустимой ветви. '
            'С учётом модуля отклонения симметричный луч даёт минимум.',
            incidence='arcsin(n sin(α/2))',minimal_deviation='|2 arcsin(n sin(α/2))−α|',
            admissibility='n>0, 0<α<π and n sin(α/2)≤1; equality is the grazing limit',
            identical_media='n=1 gives zero deviation at every admissible angle',
            outside='n sin(α/2)>1 precludes transmission on this branch')
    if text=='y=a*x+b, n equally precise measurements (x_i,y_i)' and output=='least-squares estimates for a and b':
        return proof('centering_quadratic_cost',
            'После выделения квадрата среднего остатка оптимальная прямая проходит через центр выборки. '
            'Остаток по наклону — квадрат с коэффициентом суммы центрированных квадратов абсцисс. '
            'При её занулении весь остаток не зависит от наклона.',
            slope='a=Σ(x_i−x̄)(y_i−ȳ)/Σ(x_i−x̄)² if the denominator is positive',
            intercept='b=ȳ−a*x̄',degenerate='a arbitrary if all x_i=x̄')
    if text=='given planar points; straight line x*cos(alpha)+y*sin(alpha)-p=0' and output=='line minimizing sum of squared perpendicular deviations':
        return proof('centering_quadratic_cost',
            'Сначала выделяем квадрат смещения вдоль единичной нормали и получаем прямую через центр выборки. '
            'После центрирования остаётся симметричная квадратичная форма на единичных нормалях.',
            minimizing_lines='through the centroid, unit normal in the smallest eigenspace of the centered scatter matrix',
            smallest_residual='smallest eigenvalue of the scatter matrix')
    if (hit:=re.fullmatch(r'best line a\*x\+b to (.+) on ([^<]+)<=x<=([^<]+)',text)) and output=='minimize uniform absolute deviation':
        x=m.parse('x',None,['x']);curve=m.parse(hit[1].replace('²','^2'),None,['x'])
        interval=[m.parse(hit[i],None) for i in (2,3)];ctx=m.context({})
        if domain_conditions(curve) or not all(m.constant_defined(e,ctx) for e in interval):
            raise Unsupported('The entire approximation interval and its objective must be defined')
        lo,hi=map(m.num,map(m.simplify,interval))
        if lo is None or hi is None or lo>=hi:raise Unsupported('A nondegenerate rational interval is required')
        matrix,l,k=quadratic_coefficients(curve,['x']);a=matrix[0][0]
        slope=a*(lo+hi)+l[0];intercept=k-a*lo*hi-a*(hi-lo)**2/8
        bound=abs(a)*(hi-lo)**2/8
        if not same_value(m.add(curve,m.neg(m.add(m.mul(q(slope),x),q(intercept)))),
                          m.add(m.mul(q(a),m.power(m.add(x,q(-(lo+hi)/2)),2)),q(-a*(hi-lo)**2/8))):
            raise Unsupported('The full residual of the candidate line did not match')
        return proof('three_point_affine_alternation',
            'Для любой прямой вторая разность остатка по концам и середине не зависит от коэффициентов прямой. '
            'Это даёт нижнюю оценку максимального модуля. Сдвиг секущей на половину отклонения в середине '
            'выравнивает три значения, а точный квадрат подтверждает оценку на всём отрезке.',
            slope=q(slope),intercept=q(intercept),minimal_sup_error=q(bound))
    raise Unsupported('The source optimization needs another feasible geometric or algebraic model')


def source_global_extrema_report(result,pretty):
    from model import freeze
    def show(value):
        if isinstance(value,(list,tuple)):
            if value and isinstance(value[0],str) and value[0] in m.FUNCTIONS|{'q','s','v','pi','pow','rpow','add','mul','div'}:
                return pretty(freeze(value),'x')
            return '('+', '.join(map(show,value))+')'
        if isinstance(value,dict):return ', '.join(str(k)+' = '+show(v) for k,v in value.items())
        return str(value)
    names={'infimum':'нижняя грань','supremum':'верхняя грань','minimum_point':'точка минимума','maximum_point':'точка максимума',
           'minimum_attained':'нижняя грань достигается','maximum_attained':'верхняя грань достигается'}
    def local(value):return ('да' if value else 'нет') if type(value) is bool else show(value)
    values='\n'.join(names.get(k,k)+' = '+local(v) for k,v in result['value'].items())
    return result['compilation']['proof']+'\n'+values


def constrained_projection(f,g,variables,params,guards):
    """Classify an isotropic quadratic on a hyperplane, or its restriction to a sphere."""
    from tasks import guard_source
    from verify import same_value
    ss=[('s',v) for v in variables];zeros=dict.fromkeys(ss,m.ZERO)
    if any(any(m.contains(e,v) for v in ss) for _,e in guards):raise Unsupported('В исходном множестве есть дополнительные исключения')
    ctx=m.context(dict(variable='__basepoint',parameters=params,parameter_conditions=[guard_source(r) for r in guards]))
    def isotropic(e):
        c=m.simplify(m.substitute(e,zeros));lines=[];squares=[]
        for x in ss:
            a,b=(m.simplify(m.substitute(e,{**zeros,x:m.q(k)})) for k in (-1,1))
            lines.append(m.div(m.add(b,m.neg(a)),m.q(2)));squares.append(m.add(m.div(m.add(a,b),m.q(2)),m.neg(c)))
        q=squares[0]
        if not same_value(e,m.add(c,m.add(m.dot(lines,ss),m.mul(q,m.dot(ss,ss))))):
            raise Unsupported('Нужна классификация анизотропной формы или смешанных членов')
        return q,lines,c
    Q,L,C=isotropic(f);A,B,D=isotropic(g);two=m.q(2)
    def positive_norm(vec):
        return any(m.nonzero(x,ctx) for x in vec)
    if A==m.ZERO and positive_norm(B) and m.sign(Q,ctx) in (-1,1):
        center=[m.div(m.neg(t),m.mul(two,Q)) for t in L];norm=m.dot(B,B)
        dist=m.div(m.add(m.dot(B,center),D),norm)
        foot=[m.add(c,m.neg(m.mul(dist,b))) for c,b in zip(center,B)]
        if not same_value(m.substitute(g,dict(zip(ss,foot))),m.ZERO):raise Unsupported('Проекция не удовлетворяет связи')
        center_value=m.substitute(f,dict(zip(ss,center)))
        value=m.add(center_value,m.mul(Q,m.div(m.power(m.add(m.dot(B,center),D),2),norm)))
        extrem=[dict(kind='minimum' if m.sign(Q,ctx)==1 else 'maximum',value=value,strict=True,global_bound=True,point=foot,free_directions=[])]
        displacement=[m.add(x,m.neg(v)) for x,v in zip(ss,foot)]
        squared_displacement=m.dot(displacement,displacement)
        multiple=m.mul(m.q(-2),m.mul(Q,dist))
        if not same_value(m.add(f,m.neg(value)),m.add(m.mul(Q,squared_displacement),m.mul(multiple,g))):
            raise Unsupported('Не подтверждено изменение значения на всей гиперплоскости')
        plan=dict(projection_source=center,normal=B,squared_normal=norm,constraint_multiplier=multiple)
    elif m.nonzero(A,ctx):
        center=[m.div(m.neg(b),m.mul(two,A)) for b in B];r2=m.add(m.dot(center,center),m.neg(m.div(D,A)))
        if m.sign(r2,ctx)!=1:raise Unsupported('Не установлен положительный радиус сферы')
        ratio=m.div(Q,A);line=[m.add(l,m.neg(m.mul(ratio,b))) for l,b in zip(L,B)]
        norm=m.dot(line,line);r=('sqrt',r2);length=('sqrt',norm)
        base=m.add(m.add(C,m.neg(m.mul(ratio,D))),m.dot(line,center))
        extrem=[]
        if positive_norm(line):
            for sign,label in ((-1,'minimum'),(1,'maximum')):
                d=m.mul(m.q(sign),r)
                pt=[m.add(c,m.div(m.mul(d,a),length)) for c,a in zip(center,line)]
                extrem.append(dict(kind=label,value=m.add(base,m.mul(d,length)),strict=True,global_bound=True,point=pt,free_directions=[]))
        else:
            if not same_value(m.add(f,m.neg(base)),m.mul(ratio,g)):
                raise Unsupported('Постоянство целевой функции на исходной сфере не доказано')
            point=[m.add(center[0],r),*center[1:]]
            if not same_value(m.substitute(g,dict(zip(ss,point))),m.ZERO):
                raise Unsupported('Нет проверенной точки исходной сферы')
            extrem=[dict(kind=label,value=base,strict=False,global_bound=True,point=point,free_directions=[],
                         attaining_set={'equation_zero':g,'variables':variables}) for label in ('minimum','maximum')]
        position=[m.add(x,m.neg(c)) for x,c in zip(ss,center)]
        if not same_value(g,m.mul(A,m.add(m.dot(position,position),m.neg(r2)))) or not same_value(f,m.add(m.mul(ratio,g),m.add(base,m.dot(line,position)))):
            raise Unsupported('Центрирование не восстановило исходную поверхность и целевую функцию')
        plan=dict(center=center,squared_radius=r2,linear_direction=line,squared_direction=norm)
        if extrem[0].get('attaining_set'):
            plan.update(constant_value=base,constraint_multiplier=ratio,feasible_point=point)
    else:raise Unsupported('Не построен центр квадрики или нормаль к гиперплоскости')
    plan.update(variables=variables,parameter_guards=guards,objective_coefficients=[Q,L,C],constraint_coefficients=[A,B,D])
    return plan,dict(extrema=extrem,scope='all points of the original constraint')


def planar_stationary_locus(equations,symbols):
    """Eliminate a fiber coordinate by a linear relation, checking the vanishing leading coefficient separately."""
    from plane_domains import yterm
    from verify import same_value
    def coefficients(e,axis):
        p,d=m.rational_form(e)
        if d!={():F(1)} or any(k not in symbols for mon in p for k,_ in mon):raise Unsupported('Polynomial elimination requires a polynomial system')
        rows={}
        for mon,c in p.items():
            rest=dict(mon);j=rest.pop(axis,0);rows.setdefault(j,{})[tuple(rest.items())]=c
        return [m.poly_expr(rows.get(j,{})) for j in range(max(rows,default=0)+1)]
    def roots(e,axis):
        c=coefficients(e,axis)
        if c==[m.ZERO] or any(m.num(t) is None for t in c):raise Unsupported('An identically zero or nonrational fiber needs a separate argument')
        return sorted(set(yterm(t) for t in rational_roots(tuple(m.num(t) for t in c))),key=str)
    def at(e,points):return m.simplify(m.substitute(e,points))
    for x,y in (symbols,symbols[::-1]):
        try:
            rows=[coefficients(e,y) for e in equations];a,b=sorted(rows,key=len)
            if len(a)==3 and len(b)==3:a=[m.add(m.mul(b[2],a[i]),m.neg(m.mul(a[2],b[i]))) for i in range(2)]
            if len(a)>2 or not any(z!=m.ZERO for z in a):continue
            points=[];fibers=[]
            def add_point(X,Y):
                at_point={x:X,y:Y}
                if all(same_value(at(e,at_point),m.ZERO) for e in equations):points.append([at_point[z] for z in symbols])
                elif not any(m.sign(at(e,at_point),{}) in (-1,1) for e in equations):
                    raise Unsupported('An algebraic point could not be decided exactly')
            def fiber(X):
                specialized=[at(e,{x:X}) for e in equations]
                nonzero=next((z for z in specialized if z!=m.ZERO),None)
                if nonzero is None:raise Unsupported('A positive-dimensional critical fiber remains')
                ys=roots(nonzero,y);fibers.append((X,ys))
                for Y in ys:add_point(X,Y)
            if len(a)==1 or a[1]==m.ZERO:
                projected=a[0];axis_roots=roots(projected,x)
                for X in axis_roots:fiber(X)
            else:
                offset,slope=a;Y=m.div(m.neg(offset),slope)
                eliminants=[m.poly_expr(m.rational_form(m.substitute(e,{y:Y}))[0]) for e in equations]
                projected=next((z for z in eliminants if z!=m.ZERO),None)
                if projected is None:raise Unsupported('A whole critical branch remains')
                axis_roots=roots(projected,x)
                for X in axis_roots:
                    s=at(slope,{x:X})
                    if same_value(s,m.ZERO):continue
                    if m.sign(s,{}) not in (-1,1):raise Unsupported('The substitution denominator is unresolved')
                    add_point(X,at(Y,{x:X}))
                for X in roots(slope,x):
                    residual=at(offset,{x:X})
                    if same_value(residual,m.ZERO):fiber(X)
                    elif m.sign(residual,{}) not in (-1,1):raise Unsupported('A singular projected fiber is unresolved')
            return dict(eliminated=y,linear_relation=a,projection=projected,axis_roots=axis_roots,singular_or_vertical_fibers=fibers),points
        except Unsupported:continue
    raise Unsupported('Could not certify every real point of the stationary system')


def isolated_stationary_points(raw,coords,conditions,request):
    from cartesian_fields import coordinate_sections
    from integrals import learned_nodes
    from verify import same_value
    symbols=[('s',v) for v in coords];ctx=m.context(dict(variable='t',parameters=coords))
    allowed={'s','q','pi','add','mul','div','pow','exp','ln','atan','sin','cos'}
    if any(node[0] not in allowed for node in learned_nodes(raw) if isinstance(node,tuple)):
        raise Unsupported('A nonsmooth or closed-domain component needs its own boundary investigation')
    raw_guards=domain_conditions(raw)+[('positive',('s',s[:-2])) for s in conditions]
    partial=coordinate_sections(coords,request)
    # For f=exp(P)H, the positive common factor can be removed from the gradient.
    factor=m.ONE;H=raw
    if raw[0]=='mul' and any(t[0]=='exp' for t in raw[1:]):
        pos=1 if raw[1][0]=='exp' else 2;factor=raw[pos];H=raw[3-pos]
    gradient=[partial(H,v) for v in coords]
    if factor!=m.ONE:gradient=[m.add(z,m.mul(H,partial(factor[1],v))) for v,z in zip(coords,gradient)]
    polys=[];denoms=[]
    for z in gradient:
        p,d=m.rational_form(z)
        if any(k not in symbols for part in (p,d) for mon in part for k,_ in mon):raise Unsupported('The gradient does not yet have algebraic zero sets')
        polys.append(m.poly_expr(p));denoms.append(m.poly_expr(d))
    locus,points=planar_stationary_locus(polys,symbols);checked=[];extrema=[]
    for point in points:
        subs=dict(zip(symbols,point))
        def val(e):return m.simplify(m.substitute(e,subs))
        signs=[];outside=False
        for op,e in raw_guards:
            z=val(e);sg=m.sign(z,ctx)
            if sg not in (-1,0,1):raise Unsupported('An original domain condition remains unresolved')
            signs.append((op,z,sg))
            if sg==0 and op in ('positive','nonzero') or sg<0 and op in ('positive','nonnegative'):outside=True;break
        if outside:
            checked.append(dict(point=point,source_guards=signs,classification='outside_domain'));continue
        if any(not m.nonzero(val(d),ctx) for d in denoms):raise Unsupported('No identity between gradient zeros and polynomial zeros at a source point')
        # At a zero of P_i, the derivative of P_i/D_i is (∂P_i)/D_i.
        def dp(i,axis):
            terms,_=m.rational_form(polys[i]);out={}
            for mon,c in terms.items():
                rest=dict(mon);n=rest.get(axis,0)
                if n:rest[axis]-=1;out[tuple((k,j) for k,j in rest.items() if j)]=n*c
            return m.div(val(m.poly_expr(out)),val(denoms[i]))
        A,B=dp(0,symbols[0]),dp(0,symbols[1]);C,D=dp(1,symbols[0]),dp(1,symbols[1])
        if not same_value(B,C):raise Unsupported('Mixed partials are inconsistent')
        determinant=m.add(m.mul(A,D),m.neg(m.power(B,2)));sg=m.sign(determinant,ctx);a=m.sign(A,ctx)
        directions=[]
        if sg==-1:kind='saddle'
        elif sg==1 and a in (1,-1):kind='minimum' if a==1 else 'maximum'
        elif sg==0:
            import polynomial as poly
            t=('v','t');value=val(raw)
            for dx,dy in ((1,0),(0,1),(1,1),(1,-1),(-1,0),(0,-1),(-1,1),(-1,-1)):
                along={v:m.add(c,m.mul(q(d),t)) for v,c,d in zip(symbols,point,(dx,dy))}
                try:p,d=poly.rf(m.add(m.substitute(raw,along),m.neg(value)),'t')
                except poly.NotRational:continue
                cp=next((c for c in p if c),0);cd=next((c for c in d if c),0)
                if cp*cd:
                    sign=1 if cp*cd>0 else -1
                    if not any(row['sign']==sign for row in directions):
                        directions.append(dict(direction=[dx,dy],sign=sign,first_coefficients=[q(cp),q(cd)]))
                if len(directions)==2:break
            if len(directions)!=2:raise Unsupported('No two higher-order signed directions have been proved for the degenerate critical point')
            kind='saddle'
        else:raise Unsupported('The sign of the second derivative test is unresolved')
        checked.append(dict(point=point,source_guards=signs,reduced_hessian=[A,B,D],determinant=determinant,classification=kind,directions=directions))
        if kind!='saddle':extrema.append(dict(kind=kind,point=point,strict=True,value=val(raw),free_directions=[],scope='local'))
    return (dict(variables=coords,gradient_after_positive_factor=gradient,positive_factor=factor,gradient_denominators=denoms,
                 stationary_polynomials=polys,elimination=locus,critical_points=checked,source_domain=raw_guards),
            dict(extrema=extrema,scope='all local extrema on the original open domain'))


def quadratic_extrema(task,library,request=None):
    try:return extrema_normal_form(task,library,None)
    except Unsupported:
        if library.data.get('multivariate_stationary_reductions'):
            from cartesian_fields import radial_stationarity,weighted_affine_stationarity
            from polynomial import NotRational,Undefined
            try:return weighted_affine_stationarity(task,library)
            except (Unsupported,NotRational,Undefined):pass
            if request:
                used=False
                def checked_request(*args):
                    nonlocal used
                    used=True
                    return request(*args)
                try:return radial_stationarity(task,library,checked_request)
                except (Unsupported,NotRational,Undefined):
                    if used:raise
        if not request or not library.data.get('isolated_stationary_points'):raise
    return extrema_normal_form(task,library,request)


def extrema_normal_form(task,library,stationary_request):
    import re
    from verify import same_value
    if not library.data.get('multivariate_extrema_normal_forms'):
        raise Unsupported('Правило классификации экстремумов по нормальной форме отсутствует')
    allowed={'id','kind','source','source_formula','stated_conditions','requested_output'}
    constrained=task['kind']=='constrained_extrema'
    goal='all_constrained_extremum_points' if constrained else 'classify_all_extrema_on_original_domain'
    origin=task.get('source',{})
    if (set(task)-allowed or task.get('requested_output')!=[goal] or not isinstance(origin,dict)
            or set(origin)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement','section_convention'}
            or origin.get('literal_requirement',goal)!=goal or 'section_convention' in origin and origin['section_convention']!=
            'The strict inequalities on p340 define strict local extrema; flat attained global bounds and non-strict extrema must be identified separately.'):
        raise Unsupported('Не установлены все требования к строгим и нестрогим экстремумам')
    conditions=task.get('stated_conditions',[])
    if not isinstance(conditions,list) or not all(isinstance(s,str) for s in conditions):raise Unsupported('Неверная запись области')
    def notation(s):return s.replace('²','^2').replace('³','^3').replace('⁴','^4')
    text=notation(task['source_formula']);ss=lambda x:('s',x)
    all_text=text+' '+notation(' '.join(conditions))
    coords=[v for v in 'xyz' if re.search(r'\b'+v+r'\b',all_text)]
    if len(coords) not in (2,3):raise Unsupported('Нужны исходные две или три независимые координаты')
    names=set(re.findall(r'\b[A-Za-z][A-Za-z0-9]*\b',all_text))
    params=sorted(names-set(coords)-m.FUNCTIONS-set(m.ALIASES)-{'e','pi'})
    raw=m.parse(text,None,coords+params);ambient={ss(x):ss(x) for x in coords};variables=list(coords)
    if stationary_request:
        if constrained or params or len(coords)!=2 or any(c not in {v+'>0' for v in coords} for c in conditions):
            raise Unsupported('A smooth open planar domain with known coordinate restrictions is required')
        return isolated_stationary_points(raw,coords,conditions,stationary_request)
    if conditions or constrained:
        if not constrained or len(conditions)!=1 or conditions[0].count('=')!=1:raise Unsupported('Не рассмотрены все границы или ограничения множества')
        lhs,rhs=[m.parse(notation(s),None,coords+params) for s in conditions[0].split('=')]
        g=m.add(lhs,m.neg(rhs))
        guards=list(dict.fromkeys(k for e in (raw,lhs,rhs) for k in domain_conditions(e)))
        try:return constrained_projection(raw,g,coords,params,guards)
        except Unsupported:pass
        if any(not known_guard(guard,{'parameters':coords,'assumptions':[]}) for expr in (lhs,rhs) for guard in domain_conditions(expr)):
            raise Unsupported('Остались условия определённости связи')
        zeros={ss(v):m.ZERO for v in coords};offset=m.simplify(m.substitute(g,zeros))
        weights=[m.add(m.substitute(g,{**zeros,ss(v):m.ONE}),m.neg(offset)) for v in coords]
        if not all(w[0]=='q' for w in weights) or not same_value(g,m.add(offset,m.dot(weights,map(ss,coords)))):
            raise Unsupported('Для нелинейной связи нужна отдельная проверка всего допустимого множества')
        axis=next((v for v,w in zip(coords,weights) if w!=m.ZERO),None)
        if axis is None:raise Unsupported('Ранг связи не равен единице')
        variables.remove(axis);ambient[ss(axis)]=m.div(m.neg(m.substitute(g,{ss(axis):m.ZERO})),weights[coords.index(axis)])
        if not same_value(m.substitute(g,ambient),m.ZERO):raise Unsupported('Параметризация не восстанавливает исходную связь')
    raw=m.substitute(raw,ambient);s=ss('__level')
    def nodes(e):
        yield e
        for child in e[1:]:
            if isinstance(child,tuple):yield from nodes(child)
    for inner in dict.fromkeys(nodes(raw)):
        if not all(m.contains(inner,ss(v)) for v in variables):continue
        outer=m.substitute(raw,{inner:s})
        if any(m.contains(outer,ss(v)) for v in variables):continue
        guard_ctx={'parameters':variables,'assumptions':[]}
        if not all(known_guard(g,guard_ctx) for g in domain_conditions(inner)):continue
        try:
            _,_,normal=quadratic(inner,variables)
        except Unsupported:continue
        axes=normal['orthogonal_axes'];eigen=[m.num(a['eigenvalue']) for a in axes]
        minimum=all(w>=0 for w in eigen);maximum=all(w<=0 for w in eigen);offset=normal['offset']
        tilted=normal['linear_residual']!=m.ZERO
        zeros={ss(v):m.ZERO for v in variables};center=[m.ZERO for _ in variables];free=[]
        for row in axes:
            v=row['direction']
            if row['eigenvalue']==m.ZERO:free.append(v);continue
            move=m.div(m.substitute(row['coordinate'],zeros),row['squared_norm'])
            center=[m.add(k,m.neg(m.mul(move,w))) for k,w in zip(center,v)]
        points=dict(zip(map(ss,variables),center))
        # All original restrictions must hold over this chart. In particular, a punctured quadratic
        # may have a different attained bound even though its simplified polynomial agrees.
        mapping=None
        for core in (s,('sqrt',s),('exp',s),('ln',s)):
            atom=ss('__outer');poly,den=m.rational_form(m.substitute(outer,{core:atom}))
            if den!={():F(1)} or set(poly)-{(),((atom,1),)} or not poly.get(((atom,1),)):continue
            coeff=m.q(poly[((atom,1),)])
            if core[0] in ('sqrt','ln') and (tilted or not minimum or m.num(offset)<0 or core[0]=='ln' and offset==m.ZERO):continue
            allowed={'sqrt':('nonnegative',s),'ln':('positive',s)}.get(core[0])
            if any(g!=allowed and not known_guard(g,guard_ctx) for g in domain_conditions(outer)):continue
            mapping=('identity' if core==s else core[0],coeff);break
        if mapping is None:continue
        extrem=[];location=[m.simplify(m.substitute(ambient[ss(v)],points)) for v in coords]
        directions=[[m.add(m.substitute(ambient[ss(x)],dict(zip(map(ss,variables),[m.add(a,b) for a,b in zip(center,d)]))),m.neg(l))
                     for x,l in zip(coords,location)] for d in free]
        if not tilted:
            bound=m.simplify(m.substitute(outer,{s:offset}))
            for kind,holds in (('minimum',minimum),('maximum',maximum)):
                if holds:
                    classification=kind if m.num(mapping[1])>0 else ('maximum' if kind=='minimum' else 'minimum')
                    extrem.append(dict(kind=classification,value=bound,strict=not free,global_bound=True,
                                       point=location,free_directions=directions))
        plan=dict(variables=coords,independent=variables,source_chart=[ambient[ss(v)] for v in coords],inner=inner,
                  normal_form=normal,outer=outer,monotone_map=mapping,nonzero_axis_signs=[int(a>0)-int(a<0) for a in eigen])
        if not tilted:
            plan['critical_affine_set']=dict(point=location,free_directions=directions,
                differentiable=not(mapping[0]=='sqrt' and offset==m.ZERO and any(eigen)),
                saddle=not minimum and not maximum)
        return plan,dict(extrema=extrem,scope='all points of the original domain')
    raise Unsupported('Не построена полная классификация на исходной области')


def geometry(eigen,tilted,side):
    n=len(eigen);p=sum(v>0 for v in eigen);mneg=sum(v<0 for v in eigen);r=p+mneg
    if tilted:
        if not r:return 'line' if n==2 else 'plane'
        if n==2:return 'parabola'
        if r==1:return 'parabolic_cylinder'
        return 'hyperbolic_paraboloid' if p and mneg else 'elliptic_paraboloid'
    if not r:return 'entire_space' if not side else 'empty'
    if not side:
        if p and mneg:return 'two_intersecting_lines' if n==2 else 'two_intersecting_planes' if r==2 else 'double_cone'
        return ('point','line','plane')[n-r]
    pos,neg=(p,mneg) if side>0 else (mneg,p)
    if not pos:return 'empty'
    if not neg:
        if r==1:return 'two_parallel_lines' if n==2 else 'two_parallel_planes'
        equal=len({abs(v) for v in eigen if v})==1
        if r<n:return 'circular_cylinder' if equal else 'elliptic_cylinder'
        return ('circle' if equal else 'ellipse') if n==2 else ('sphere' if equal else 'ellipsoid')
    if r==2:return 'hyperbola' if n==2 else 'hyperbolic_cylinder'
    return 'two_sheet_hyperboloid' if pos==1 else 'one_sheet_hyperboloid'


def check_request(t,lib):
    fields={'id','schema','source','kind','function','variables','parameters','stated_conditions','level_parameter','requested_output'}
    v=t['variables'];c=t['level_parameter'];d=len(v);out=t.get('requested_output',())
    if (not lib.data.get('quadratic_level_families') or set(t)-fields or t.get('kind')!='level_sets' or t.get('parameters') or t.get('stated_conditions') or
        not isinstance(v,(list,tuple)) or d not in (2,3) or len(set([*v,c]))!=d+1 or
        set(out)!=({'all_level_sets','level_curve_drawing'} if d==2 else {'all_level_sets'})):
        raise Unsupported('Different dimension, source constraints or additional level-family requests')
    for name in [*v,c]:m.context({'variable':name})


def classify(t,raw):
    v=t['variables'];c=t['level_parameter'];d=len(v)
    ctx=m.context({'variable':c})
    def extra_domain(e):return any(not known_guard(g,ctx) for g in domain_conditions(e))
    cc=('s',c);inner=raw;level=cc;mapping='identity';guard=[]
    if raw[0]=='sqrt':inner=raw[1];level=m.power(cc,2);guard=[('nonnegative',cc)];mapping='sqrt'
    elif raw[0]=='div' and m.constant_defined(raw[1],m.context({'variable':c})) and m.num(m.simplify(raw[1])) not in (None,0):
        inner=raw[2];level=m.div(raw[1],cc);guard=[('nonzero',cc)];mapping='reciprocal'
    elif raw[0]=='div' and d==2:
        N,D=raw[1:]
        if extra_domain(N) or extra_domain(D):raise Unsupported('The affine pencil has additional original exclusions')
        An,ln,n0=quadratic(N,v);Ad,ld,d0=quadratic(D,v)
        if any(any(row) for row in An+Ad) or ln[0]*ld[1]==ln[1]*ld[0]:raise Unsupported('Unresolved singular level of the pencil')
        eq=m.add(N,m.neg(m.mul(cc,D)))
        det=ln[0]*ld[1]-ln[1]*ld[0];a,b=m.num(n0['offset']),m.num(d0['offset'])
        return dict(method='affine_pencil',equation=(eq,q(0)),source_domain=domain_conditions(raw),admissible_levels=[],
                    puncture=(q((ln[1]*b-a*ld[1])/det),q((a*ld[0]-ln[0]*b)/det)),
                    families=[dict(relation='all',geometry='punctured_line')]),[(q(i),m.substitute(eq,{cc:q(i)})) for i in (-1,0,1)]
    if extra_domain(inner):raise Unsupported('The quadratic inner expression has extra raw restrictions')
    A,l,normal=quadratic(inner,v);k=m.num(normal['offset']);axes=normal['orthogonal_axes']
    eigen=[m.num(s['eigenvalue']) for s in axes];tilted=normal['linear_residual']!=q(0)
    # When a quadratic projection has real critical abscissas, this step gives rational representatives.
    if d==2 and A[1][1]:step=abs(A[0][0]-A[0][1]**2/A[1][1]) or F(1)
    else:step=abs(A[0][0]) or F(1)
    examples=[];spares=[];rows=[]
    def valid(z):return (mapping!='sqrt' or z>=0) and (mapping!='reciprocal' or z!=0)
    def outside(z):return m.simplify(('sqrt',q(z))) if mapping=='sqrt' else m.div(raw[1],q(z)) if mapping=='reciprocal' else q(z)
    for side in (-1,0,1):
        geom=geometry(eigen,tilted,side);typ=('<','==','>')[side+1]
        allowed=(side!=0 or valid(k)) and (mapping!='sqrt' or side>=0 or k>0)
        if not allowed:continue
        row=dict(relation=typ,geometry=geom)
        if not tilted and side and geom!='empty':
            gap=m.add(level,q(-k))
            row['principal_lengths']=[m.simplify(('sqrt',m.div(m.mul(q(side),gap),q(abs(a))))) for a in eigen if a]
        rows.append(row)
        if d!=2 or geom=='empty':continue
        candidates=[k] if not side else [k+side*step*z*z for z in (F(1),F(2),1+abs(k)/step,F(1,2)/(1+step+abs(k)))]
        choices=[a for a in dict.fromkeys(candidates) if valid(a)]
        if not choices:raise Unsupported('No admissible representative for a nonempty regime')
        examples.append((outside(choices[0]),m.add(inner,q(-choices[0]))))
        spares.extend((outside(z),m.add(inner,q(-z))) for z in choices[1:])
    if len(examples)==1 and spares:examples.append(spares[0])
    if tilted:rows=[dict(relation='all',geometry=geometry(eigen,True,0))]
    return dict(method='principal_axes',mapping=mapping,equation=(inner,level),source_domain=domain_conditions(raw),admissible_levels=guard,
                outside_admissible='empty',normal_form=normal,families=rows),examples


def rational_branches(e):
    """Expand abs/min/max, retaining both operands' original domains, including unselected operands."""
    from intervals import MAX_BRANCHES
    from polynomial import ResourceBound
    op=e[0]
    if op in ('q','s'):return [(e,())]
    if op not in ('add','mul','div','pow','abs','min','max'):raise Unsupported('Unimplemented piecewise rational operation')
    left=rational_branches(e[1]);out=[]
    def record(value,guards):
        row=(value,tuple(dict.fromkeys(guards)))
        if row not in out:out.append(row)
        if len(out)>MAX_BRANCHES:raise ResourceBound('Cartesian branch bound exceeded')
    if op in ('abs','pow'):
        for a,g in left:
            if op=='abs':
                record(a,(*g,('nonnegative',a)));record(m.neg(a),(*g,('nonnegative',m.neg(a))))
            elif e[2]>0 or m.rational_form(a)[0]:
                record(m.power(a,e[2]),g if e[2]>0 else (*g,('nonzero',a)))
        return out
    right=rational_branches(e[2])
    if len(left)*len(right)>MAX_BRANCHES:raise ResourceBound('Cartesian branch bound exceeded')
    for a,g in left:
        for b,h in right:
            both=g+h
            if op in ('min','max'):
                d=m.add(a,m.neg(b)) if op=='max' else m.add(b,m.neg(a))
                record(a,(*both,('nonnegative',d)));record(b,(*both,('nonnegative',m.neg(d))))
            elif op=='div':
                if m.rational_form(b)[0]:record(m.div(a,b),(*both,('nonzero',b)))
            else:record((m.add if op=='add' else m.mul)(a,b),both)
    return out


def dilation_degrees(branches,variables):
    """Each polynomial needs one weighted degree; all nonzero outputs need the same net degree."""
    from math import gcd
    x,y=(('s',v) for v in variables);constraints=set();degree=None
    def subtract(a,b):return a[0]-b[0],a[1]-b[1]
    def grade(poly):
        first=None
        for mon in poly:
            powers=dict(mon)
            if set(powers)-{x,y}:raise Unsupported('A branch coefficient is not rational')
            pair=powers.get(x,0),powers.get(y,0)
            if first is None:first=pair
            else:constraints.add(subtract(pair,first))
        return first
    for e,g in branches:
        for _,predicate in g:
            for p in m.rational_form(predicate):grade(p)
        numerator,denominator=map(grade,m.rational_form(e))
        if numerator is None:continue
        delta=subtract(numerator,denominator)
        if degree is None:degree=delta
        else:constraints.add(subtract(delta,degree))
    constraints.discard((0,0));w=(1,1)
    if constraints:
        a,b=next(iter(constraints));norm=gcd(a,b)
        w=(abs(b)//norm,abs(a)//norm)
        if min(w)<=0 or any(dot(row,w) for row in constraints):raise Unsupported('No common positive coordinate dilation')
    d=dot(degree,w) if degree else 0
    if not d:raise Unsupported('No common nonzero output degree')
    return w,d


def dilation_family(t,raw):
    """All nonzero signed levels are exact dilations of the corresponding unit level."""
    from plane_domains import decomposition
    v=t['variables'];c=('s',t['level_parameter']);outer=raw[0]=='exp'
    e=raw[1] if outer else raw;level=('ln',c) if outer else c
    branches=rational_branches(e);w,d=dilation_degrees(branches,v);panels=[];rows=[]
    for side in (-1,0,1):
        rep=m.simplify(('exp',q(side))) if outer else q(side)
        cases=[(*g,('zero',m.add(a,q(-side)))) for a,g in branches]
        region,proj=decomposition((),v,cases)
        dim=max([2 if any(s['cells']) else 1 if any(s['points']) else -1 for s in region['slabs']]+
                [1 if any(s['cells']) else 0 if any(s['points']) else -1 for s in region['sections']])
        panels.append(dict(level=rep,exact_region=region,projection=proj))
        base=m.mul(q(side),level)
        scales=[q(1) if not side else m.simplify(('rpow',base,q(F(j,d)))) for j in w]
        rows.append(dict(relation=('<','==','>')[side+1],geometry='empty' if dim<0 else 'coordinate_dilation',
                         dimension=dim,reference_level=rep,coordinate_scales=scales))
    return dict(method='weighted_dilation',equation=(e,level),source_domain=domain_conditions(raw),
                admissible_levels=[('positive',c)] if outer else [],outside_admissible='empty',
                coordinate_weights=w,degree=d,families=rows),panels



def level_sets(t,lib,request):
    from plane_domains import decomposition,draw_region
    from graphs import svg_canvas,svg_element,svg_text,svg_payload
    from xml.etree import ElementTree as ET
    check_request(t,lib);v=t['variables'];raw=m.parse(t['function'],None,v,extra_functions=('min','max'))
    try:family,examples=classify(t,raw)
    except Unsupported:
        if len(v)!=2 or not lib.data.get('weighted_level_dilation'):raise
        family,panels=dilation_family(t,raw)
    else:
        panels=[]
        if len(v)==3:return {'drawn_levels':[]},{'family':family}
        for c,eq in examples or [(q(0),q(1))]:
            region,proj=decomposition((*domain_conditions(raw),('zero',eq)),v)
            panels.append(dict(level=c,exact_region=region,projection=proj))
    values={'family':family}
    def render(panel,window=None):
        return ET.fromstring(draw_region(panel['exact_region'],t['level_parameter']+' = '+m.render(panel['level']),window)['drawing_svg'])
    roots=[render(p) for p in panels]
    windows=[tuple(F(r.get('data-'+name)) for name in ('xmin','xmax','ymin','ymax')) for r in roots]
    x0=min(w[0] for w in windows);x1=max(w[1] for w in windows);y0=min(w[2] for w in windows);y1=max(w[3] for w in windows)
    size=max(x1-x0,y1-y0);cx=(x0+x1)/2;cy=(y0+y1)/2;common=(cx-size/2,cx+size/2,cy-size/2,cy+size/2)
    svg=svg_canvas(535*len(roots),520);svg_element(svg,'rect',width='100%',height='100%',fill='white')
    for i,(r,p,w) in enumerate(zip(roots,panels,windows)):
        if w!=common:r=render(p,common)
        layer=svg_element(svg,'g',transform=f'translate({i*535} 0)',data_level=m.render(p['level']))
        for node in r.iter():
            node.tag=node.tag.rsplit('}',1)[-1]
            if node.get('id')=='plot':node.set('id','plot'+str(i))
            if node.get('clip-path')=='url(#plot)':node.set('clip-path','url(#plot'+str(i)+')')
        for child in list(r)[1:]:layer.append(child)
    values.update(svg_payload(svg_text(svg)));return {'drawn_levels':panels},values


def family_report(r):
    from model import freeze
    from tasks import guard_source
    t=r['task'];lines=['Семейство уровней '+t['function'],r['status']]
    if r.get('value') is None:return '\n'.join(lines+[r.get('reason','')])+'\n'
    f=r['value']['family'];show=lambda x:m.render(freeze(x));name=t['level_parameter']
    n={'line':'прямая','plane':'плоскость','point':'точка','circle':'окружность','sphere':'сфера','ellipse':'эллипс',
       'ellipsoid':'эллипсоид','empty':'пустое множество','entire_space':'всё пространство','hyperbola':'гипербола',
       'double_cone':'двойной конус','two_intersecting_lines':'две пересекающиеся прямые','two_intersecting_planes':'две пересекающиеся плоскости',
       'two_parallel_lines':'две параллельные прямые','two_parallel_planes':'две параллельные плоскости','elliptic_cylinder':'эллиптический цилиндр',
       'circular_cylinder':'круговой цилиндр','hyperbolic_cylinder':'гиперболический цилиндр','two_sheet_hyperboloid':'двуполостный гиперболоид',
       'one_sheet_hyperboloid':'однополостный гиперболоид','punctured_line':'прямая с выколотой точкой','parabola':'парабола',
       'elliptic_paraboloid':'эллиптический параболоид','hyperbolic_paraboloid':'гиперболический параболоид','parabolic_cylinder':'параболический цилиндр'}
    if f['source_domain']:lines.append('Область исходной функции  '+', '.join(guard_source(freeze(g)) for g in f['source_domain']))
    if f['admissible_levels']:lines.append('Условия на '+name+'  '+', '.join(guard_source(freeze(g)) for g in f['admissible_levels'])+'. При нарушении уровень пуст.')
    lines.append('Уравнение  '+show(f['equation'][0])+' = '+show(f['equation'][1]))
    if f['method']=='weighted_dilation':
        from plane_domains import region_description
        lines.append('Веса координат '+str(f['coordinate_weights'])+', степень '+str(f['degree']))
        for case,panel in zip(f['families'],r['compilation']['drawn_levels']):
            text=show(f['equation'][1])+' '+case['relation']+' 0'
            if case['dimension']<0:lines.append(text+'   пустое множество');continue
            lines.append(text+'   опорный уровень '+show(case['reference_level'])+', множители координат ('+', '.join(map(show,case['coordinate_scales']))+')')
            lines.extend(region_description(panel['exact_region']))
        return '\n'.join(lines)+'\n'
    if 'puncture' in f:lines.append('Исключена точка ('+', '.join(map(show,f['puncture']))+')')
    if 'normal_form' in f:
        for axis in f['normal_form']['orthogonal_axes']:
            lines.append('Направление ('+', '.join(map(show,axis['direction']))+'), собственное значение '+show(axis['eigenvalue']))
    for case in f['families']:
        rel=case['relation'];condition='Все допустимые '+name if rel=='all' else show(f['equation'][1])+' '+rel+' '+show(f['normal_form']['offset'])
        lines.append(condition+'   '+n[case['geometry']]+('. Длины главных полуосей '+', '.join(map(show,case['principal_lengths'])) if case.get('principal_lengths') else ''))
    return '\n'.join(lines)+'\n'


def set_order_identity(task):
    """Build bounds of set images from independent witnesses approaching each endpoint."""
    import ast
    import re
    goal=task['goal'];claim=goal['proposition'];assumptions=task.get('assumptions',[])
    facts={};zero_infinite=False
    for line in assumptions:
        if line=='0*infinity=0 for nonnegative extended products':
            zero_infinite=True;continue
        wording=re.fullmatch(r'([A-Z](?:,[A-Z])*) (?:is|are) (.+)',line)
        if not wording:raise Unsupported('The set assumptions have not been established')
        sets=wording[1].split(',');scope=wording[2]
        allowed={'nonempty; bounds may be extended real','a nonempty set of real numbers','nonempty real sets',
                 'nonempty subsets of[0,+inf)','nonempty nonnegative real sets','nonempty positive real sets',
                 'bounded above','bounded below'}
        if scope not in allowed:raise Unsupported('Unresolved set domain or a possibly empty factor')
        for s in sets:facts.setdefault(s,set()).add(scope)
    declared=goal.get('sets',{})
    if not isinstance(declared,dict) or any(s not in facts or desc!='nonempty subset of[0,+inf)' or
            not facts[s]&{'nonempty subsets of[0,+inf)','nonempty nonnegative real sets'} for s,desc in declared.items()):
        raise Unsupported('The additional set declarations are unresolved')
    if claim=='Every nonempty real set bounded below/above has infimum/supremum':
        if not facts or any(not any('nonempty' in s for s in options) for options in facts.values()):
            raise Unsupported('A nonempty family of real cuts is required')
        steps=['Представляем вещественные числа нижними дедекиндовыми сечениями рациональных.',
               'Объединение непустого семейства сечений снова непусто, замкнуто вниз и не имеет наибольшего элемента. Верхняя граница содержит всё объединение, так что оно собственное.',
               'Каждое сечение семейства содержится в объединении. Любая общая верхняя граница содержит объединение. Значит, оно задаёт точную верхнюю грань.',
               'Для ограниченного снизу множества применяем эту конструкцию к противоположным числам. Изменение знака меняет порядок, поэтому минус полученная верхняя грань есть нижняя грань.']
        return dict(theorem='method.order_bounds_of_images',construction='union_of_lower_cuts',steps=steps),dict(proposition=claim,proved=True)
    def parse(s):
        s=re.sub(r'\b([A-Z])([A-Z])\b',r'\1*\2',s)
        try:return ast.parse(s.strip(),mode='eval').body
        except (SyntaxError,ValueError):raise Unsupported('The set operation is not a mathematical expression')
    def combine(op,a,b):
        terms=[]
        for x in (a,b):terms.extend(x[1:] if x[0]==op else [x])
        return (op,*sorted(terms,key=repr))
    def neg(a):
        if a[0]=='neg':return a[1]
        if a[0]=='sum':return ('sum',*sorted((neg(x) for x in a[1:]),key=repr))
        return ('neg',a)
    def scalar(n):
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return neg(scalar(n.operand))
        if isinstance(n,ast.BinOp) and isinstance(n.op,(ast.Add,ast.Sub,ast.Mult)):
            a,b=scalar(n.left),scalar(n.right)
            return combine('product' if isinstance(n.op,ast.Mult) else 'sum',a,neg(b) if isinstance(n.op,ast.Sub) else b)
        if (isinstance(n,ast.Call) and not n.keywords and isinstance(n.func,ast.Name) and n.func.id in ('inf','sup') and
                len(n.args)==1 and isinstance(n.args[0],ast.Name) and n.args[0].id in facts):return (n.func.id,n.args[0].id)
        raise Unsupported('The claimed expression contains another endpoint or operation')
    steps=[];vertices=[];used=set();undefined_products=[]
    def image(n,side):
        if isinstance(n,ast.Name) and n.id in facts:
            scope=facts[n.id];used.add(n.id)
            if not any('nonempty' in s for s in scope):raise Unsupported('Nonemptiness of each set is required')
            nonneg=bool(scope&{'nonempty subsets of[0,+inf)','nonempty nonnegative real sets','nonempty positive real sets'})
            return (side,n.id),nonneg,'bounded above' in scope,'nonempty positive real sets' in scope
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
            opposite='inf' if side=='sup' else 'sup';end,_,_,_=image(n.operand,opposite)
            text='Отражение меняет направление всех неравенств. Элементы, приближающие противоположную грань, после отражения приближают искомую, в том числе при неограниченности.'
            steps.append(text);vertices.append(('reflection',side,opposite));return neg(end),False,False,False
        if not isinstance(n,ast.BinOp) or not isinstance(n.op,(ast.Add,ast.Mult)):raise Unsupported('No endpoint preservation theorem applies to the set operation')
        a,na,ba,pa=image(n.left,side);b,nb,bb,pb=image(n.right,side)
        if isinstance(n.op,ast.Add):
            steps.append('Складываем покомпонентные границы. Для любой ε>0 независимо выбираем по элементу на расстоянии меньше ε/2 от каждой конечной грани. При бесконечной грани фиксируем элемент второго множества и уводим первый сколь угодно далеко.')
            vertices.append(('sum',side,a,b));return combine('sum',a,b),na and nb,ba and bb,(pa and nb) or (pb and na)
        if not (na and nb):raise Unsupported('Multiplication requires a sign domain for both independent factors')
        if side=='sup' and not ((ba or pb) and (bb or pa)) and not zero_infinite:
            if a[0]!='sup' or b[0]!='sup' or not isinstance(lhs.args[0],ast.BinOp) or n is not lhs.args[0]:
                raise Unsupported('A nested undefined product needs its own scope proof')
            unbounded,zero=(a[1],b[1]) if not ba and not pb else (b[1],a[1])
            undefined_products.append(dict(sets={unbounded:'[0,+inf)',zero:'{0}'},
                                           image_supremum=m.ZERO,printed_right_side='undefined 0 times +infinity'))
            steps.append('При нулевой грани одного множества и бесконечной грани другого левая часть равна нулю. Обычное произведение расширенных границ здесь не определено.')
        steps.append('На неотрицательной полуоси умножение сохраняет порядок. Для конечных граней A,B выбираем приближения с ошибкой меньше min(1, ε/(1+A+B)). Ошибка произведения ограничена суммой двух линейных ошибок и их произведения.')
        if side=='sup':
            steps.append('Если одна верхняя грань бесконечна, фиксируем строго положительный элемент другого множества и берём неограниченную последовательность первого. Если второй множитель состоит из нуля, всё произведение состоит из нуля.')
        vertices.append(('product',side,a,b));return combine('product',a,b),True,ba and bb,pa and pb
    if claim.count('=')!=1:raise Unsupported('A single equality of set bounds is required')
    lhs,rhs=map(parse,claim.split('='))
    if not (isinstance(lhs,ast.Call) and isinstance(lhs.func,ast.Name) and lhs.func.id in ('inf','sup') and not lhs.keywords and len(lhs.args)==1):
        raise Unsupported('No upper or lower image bound was requested')
    end,*_=image(lhs.args[0],lhs.func.id)
    if not vertices or end!=scalar(rhs) or used!=set(facts):raise Unsupported('The derived endpoint differs from the requested identity or a set is unbound')
    result=dict(proposition=claim,proved=not undefined_products)
    if undefined_products:
        result.update(printed_claim_holds=False,counterexample=undefined_products[0])
    return dict(theorem='method.order_bounds_of_images',construction='endpoint_witnesses',steps=steps,
                set_operations=vertices,derived_bound=end),result


def rational_cut_identity(claim):
    """Construct rational witnesses inside a lower cut or on either side of a polynomial cut."""
    import re
    from fractions import Fraction
    from math import isqrt
    def cert(construction,steps,**data):
        return dict(theorem='method.rational_cut_witnesses',construction=construction,steps=steps,**data),dict(proposition=claim,proved=True)
    cut=re.fullmatch(r'([A-Z])=\{(\w+) in Q:\2\^(\d+)<(-?\d+)\}, ([A-Z])=Q\\+\1; \1 has no maximum and \5 has no minimum',claim)
    if cut:
        if cut[1]==cut[5]:raise Unsupported('The two cut classes must be distinct')
        k=int(cut[3]);magnitude=abs(int(cut[4]))
        if k<1 or not k%2:raise Unsupported('The power must preserve the order of all rationals')
        lo,hi=0,magnitude+1
        while hi-lo>1:
            middle=(lo+hi)//2
            if middle**k<=magnitude:lo=middle
            else:hi=middle
        if lo**k==magnitude:raise Unsupported('The upper rational class contains its least element')
        return cert('rational_perturbation',['Целая нечётная степень строго возрастает. Рациональный корень целого числа при несократимой записи обязан быть целым. Последовательные целые степени по модулю охватывают данную константу строго.',
                'Для любого рационального t положим δ=min(1, |M−t^k|/(2k(|t|+1)^(k−1))). Это положительное рациональное число.',
                'По формуле разности степеней изменение (t±δ)^k не превосходит k(|t|+1)^(k−1)δ. Поэтому t+δ всё ещё в нижнем классе, если t в нижнем, а t−δ в верхнем, если t в верхнем.'],
                power=k,constant=int(cut[4]),consecutive_integer_powers=[lo**k,hi**k])
    ratio=r'(\d+(?:/\d+)?)';mt=re.fullmatch(r'sqrt\('+ratio+r'\)([+*])sqrt\('+ratio+r'\)=sqrt\('+ratio+r'\), by corresponding cuts',claim)
    if not mt:raise Unsupported('The source needs a different cut construction')
    try:a,b,c=(Fraction(mt[i]) for i in (1,3,4))
    except ZeroDivisionError as e:raise Unsupported('A radicand has zero denominator') from e
    if min(a,b,c)<=0:raise Unsupported('Positive rational radicands are required')
    steps=['Представляем положительный корень при помощи нижнего сечения: все отрицательные рациональные и те неотрицательные t, для которых t² меньше подкоренного числа.']
    if mt[2]=='*':
        if a*b!=c:raise Unsupported('The product of the radicands differs from the target')
        steps+=['Произведение двух положительных представителей лежит в целевом сечении: квадрат произведения меньше произведения подкоренных чисел.',
                'Для любого положительного q с q²<ab выбираем рациональное s>0 с q²/b<s²<a. Такое s находится делением пополам рационального отрезка, содержащего положительный корень a: ширина отрезка стремится к нулю, как и разность квадратов его концов. Тогда (q/s)²<b и q=s·(q/s) принадлежит произведению сечений. Нуль и отрицательные числа входят в нижний класс.']
        return cert('positive_cut_product',steps,radicands=[str(a),str(b),str(c)])
    scale=b/a;p,d=isqrt(scale.numerator),isqrt(scale.denominator);t=Fraction(p,d)
    if t*t!=scale or (1+t)**2*a!=c:raise Unsupported('No rational dilation identifies these square-root cuts')
    steps+=['Положительный рациональный множитель '+str(t)+' переводит первое сечение во второе, что проверяется сравнением квадратов в обе стороны.',
            'Сумма сечения и его положительного рационального кратного равна сечению, растянутому в 1+'+str(t)+' раз. Для включения слева делим сумму на 1+'+str(t)+' и получаем взвешенное среднее двух элементов нижнего класса. Обратно, любой его элемент u даёт сумму u+'+str(t)+'u.',
            'Квадрат масштаба, умноженный на первый радиканд, равен целевому радиканду. Поэтому нижние сечения совпадают.']
    return cert('positive_cut_dilation',steps,radicands=[str(a),str(b),str(c)],rational_scale=str(t))
