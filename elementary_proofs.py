"""Checked elementary reductions on real functions, measurements and discrete tails."""
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from math import ceil, factorial, isqrt, lcm, prod
import re

import expressions as m
import polynomial as poly
from model import ONE, ZERO, Unsupported, q


NATURAL = 'n is a positive integer'
METADATA = {'kind', 'task_type', 'id', 'source', 'source_number', 'source_exercise_number',
            'source_edition', 'source_subpart', 'source_pdf_page', 'source_pdf_pages', 'source_statement',
            'program_status', 'transcription_notes', 'main_pass_status', 'deferred_reason', 'index_domain'}
NAME = r'[A-Za-z_]\w*'


def need(ok, text):
    if not ok:
        raise Unsupported(text)


def packet(task, *keys, exact=True):
    goal = task.get('goal')
    given = task.get('assumptions', task.get('source_assumptions', []))
    need(not set(task) - METADATA - {'goal', 'assumptions', 'source_assumptions'} and
         not ('assumptions' in task and 'source_assumptions' in task) and
         isinstance(goal, dict) and set(goal) <= set(keys) and (not exact or set(goal) == set(keys)) and
         isinstance(given, list) and all(isinstance(c, str) for c in given),
         'Unbound source fields, hypotheses or output')
    need(task.get('index_domain') in (None, 'positive_integers', 'nonnegative_integers'),
         'The source index domain is not bound')
    return goal, given


def cert(library, method, value, *argument, **details):
    need(method in library.data.get('elementary_proof_transitions', ()), 'Transition absent from the active library')
    return dict(theorem='method.' + method, argument=argument, **details), value


def names(text, variable, extra=()):
    return sorted(set(re.findall(NAME, text)) - m.FUNCTIONS - set(m.ALIASES) - {variable, 'pi', 'e', *extra})


def same(a, b):
    return m.simplify(m.add(a, m.neg(b))) == ZERO


def rational(text):
    value = m.parse(str(text), None)
    need(m.constant_defined(value, m.context({'variable': 'x'})), 'Undefined rational datum')
    ans = m.num(m.simplify(value))
    need(ans is not None, 'Expected an exact rational datum')
    return ans


def power_ceiling(target, base):
    """Least nonnegative exponent with base**exponent >= target, by exact comparisons."""
    need(base > 1 and target > 0, 'The increasing power used for comparison must have base > 1')
    left, right = -1, 1
    while base ** right < target:
        left, right = right, 2 * right
        need(right <= 262_144, 'The requested exact table threshold exceeds the supported size')
    while right - left > 1:
        mid = (left + right) // 2
        if base ** mid < target:
            left = mid
        else:
            right = mid
    return right


def log_power(numerator, denominator):
    """Try the exact integer ratio ln(numerator)/ln(denominator), with bounded powers."""
    a, b = m.num(numerator), m.num(denominator)
    if a is None or b is None or a <= 0 or b <= 0 or b == 1:
        return None
    if a == 1:
        return ZERO
    if b < 1:
        b, a = 1/b, 1/a
    sign = 1 if a > 1 else -1
    k = power_ceiling(max(a, 1/a), b)
    return q(sign*k) if b**k == max(a, 1/a) else None


def reduce_value(expr):
    if expr[0] in ('q', 's', 'v', 'pi'):
        return expr
    args = tuple(reduce_value(t) if isinstance(t, tuple) else t for t in expr[1:])
    if expr[0] == 'floor' and m.num(args[0]) is not None:
        return q(m.num(args[0]).__floor__())
    if expr[0]=='rpow':
        degree=m.num(args[1])
        if degree is not None and degree.denominator==1 and abs(degree)<=m.MAX_INTEGER_POWER:
            return m.power(args[0],int(degree))
        base=m.num(args[0])
        if degree is not None and base is not None and base>0 and degree.denominator<=32 and abs(degree.numerator)<=m.MAX_INTEGER_POWER:
            a=m.perfect_root(base.numerator,degree.denominator);b=m.perfect_root(base.denominator,degree.denominator)
            if a is not None and b is not None:return q(Fraction(a,b)**degree.numerator)
    if expr[0] == 'div' and all(t[0] == 'ln' for t in args):
        exact = log_power(args[0][1], args[1][1])
        if exact is not None:
            return exact
    return m.simplify((expr[0], *args))


def value_at(raw, v, value):
    expr = m.substitute(raw, {v: value})
    ctx=m.context({'variable': v[1]})
    def bind_floor(node):
        if isinstance(node,tuple):
            op,*items=node
            args=tuple(map(bind_floor,items))
            if op=='floor' and m.constant_defined(args[0],ctx):
                integer=m.num(m.simplify(args[0]))
                if integer is not None:return q(integer.__floor__())
            return (op,*args)
        return node
    expr=bind_floor(expr)
    need(m.constant_defined(expr,ctx), 'The original function is undefined at a requested argument')
    return reduce_value(expr)


def piece_value(text, variable, value):
    true = []
    for entry in text.removeprefix('piecewise(')[:-1].split(';'):
        expr, cond = entry.split(' if ')
        match = re.fullmatch(re.escape(variable) + r'(<=|>=|=|<|>)(.+)', cond.strip())
        need(match, 'Unsupported piecewise point condition')
        x, cut = m.num(value), rational(match[2])
        need(x is not None, 'An ordered exact argument is required')
        if {'<': x < cut, '<=': x <= cut, '=': x == cut, '>=': x >= cut, '>': x > cut}[match[1]]:
            true.append(m.parse(expr.strip(), variable, (), ('floor',)))
    need(len(true) == 1, 'The requested point must lie in exactly one branch')
    return true[0]


def apply_function(node, variable, fn):
    """Replace a declared function by its definition without simplifying any domain guard."""
    if not isinstance(node, tuple):
        return node
    if node[0] == 'f':
        return m.substitute(fn, {('v', variable): apply_function(node[1], variable, fn)})
    return (node[0], *(apply_function(t, variable, fn) for t in node[1:]))


def interpolation(task, library):
    kind = task.get('kind', task.get('task_type'))
    g, given = packet(task, 'family', 'conditions', 'requests', 'goal', exact=False)
    need(not given and {'family', 'conditions'} <= set(g) and
         (g.get('requests') is not None or g.get('goal') in
          ('unique polynomial in this family', 'determine the real exponential function')),
         'The interpolation targets or restrictions are not bound')
    rows = []
    for loc, val in g['conditions']:
        match = re.fullmatch(r'f\((.+)\)', loc)
        need(match, 'A point-value interpolation datum is required')
        rows.append((rational(match[1]), rational(val)))
    need(len(rows) > 1 and len({a for a, _ in rows}) == len(rows), 'The interpolation nodes must be distinct')
    x = ('v', 'x')
    params = names(g['family'], 'x')
    template = m.parse(g['family'], 'x', params)
    exponential = kind == 'exponential_family_interpolation'
    if exponential:
        need(len(rows) == len(params) == 3 and g.get('requests') is None, 'Three equally spaced nodes must determine the exponential')
        need(any(same(template,m.add(p,m.mul(b,('rpow',c,x)))) for p,b,c in
                 permutations(('s',n) for n in params)), 'Unsupported exponential interpolation family')
        (x0,y0),(x1,y1),(x2,y2) = sorted(rows)
        h = x1-x0
        need(x2-x1 == h and y1 != y0, 'Equal spacing and a nonzero first increment are required')
        ratio = (y2-y1)/(y1-y0)
        need(ratio > 0 and ratio != 1, 'The positive exponential base and nonconstant model need positive ratio different from 1')
        base = reduce_value(('rpow',q(ratio),q(1/h)))
        coefficient = m.div(q((y1-y0)/(ratio-1)), reduce_value(('rpow',base,q(x0))))
        intercept = q(y0-(y1-y0)/(ratio-1))
        fn = m.add(intercept,m.mul(coefficient,('rpow',base,x)))
        return cert(library, 'interpolate_equal_step_exponential', dict(function=fn,base=base),
                    'Вычитаем значения в соседних равноотстоящих узлах. Отношение разностей равно положительной степени основания.',
                    'Определяем основание, затем масштаб и сдвиг. Ненулевая первая разность обеспечивает единственность обеих операций.',
                    data=[tuple(map(q,row)) for row in rows],step=q(h),increment_ratio=q(ratio))
    need(len(rows)==len(params)<=8 and not (set(g) == {'family','conditions'}), 'Full polynomial interpolation is required')
    n, d = m.rational_form(template)
    need(d == {(): Fraction(1)} and len(n) == len(params), 'The expected family must span all polynomials of the required degree')
    degrees = set(); used = set()
    for monomial, factor in n.items():
        factors = dict(monomial); degree = factors.pop(x,0)
        need(len(factors)==1 and factor!=0, 'Each coefficient must be an independent parameter')
        (symbol, degree_coefficient), = factors.items()
        need(symbol[0]=='s' and symbol[1] in params and degree_coefficient==1 and symbol not in used,
             'Polynomial coefficient occurrence is not independent')
        degrees.add(degree); used.add(symbol)
    need(degrees==set(range(len(rows))), 'The polynomial family fails to include all required degrees')
    terms = []
    for a, y in rows:
        term = q(y)
        for b, _ in rows:
            if b != a:
                term = m.mul(term,m.mul(q(1/(a-b)),m.add(x,q(-b))))
        terms.append(term)
    fn=ZERO
    for term in terms:fn=m.add(fn,term)
    need(all(value_at(fn,x,q(a))==q(y) for a,y in rows), 'Interpolation failed its exact point checks')
    output = dict(function=fn)
    if 'requests' in g:
        requested={}
        for loc in g['requests']:
            arg = re.fullmatch(r'f\((.+)\)',loc)
            need(arg, 'Unsupported additional interpolation question')
            requested[loc] = fn if arg[1]=='x' else value_at(fn,x,q(rational(arg[1])))
        output['requested_values']=requested
    return cert(library, 'interpolate_and_check_polynomial_nodes', output,
                'Строим базис Лагранжа из различий узлов. Каждый множитель имеет единицу в своём узле и ноль в остальных.',
                'Проверяем все исходные значения. Разность двух полиномов допустимой степени с таким числом разных нулей тождественно равна нулю.',
                data=[tuple(map(q,row)) for row in rows],terms=terms)


def function_sheet(task, library):
    from tasks import domain_conditions
    kind=task.get('kind',task.get('task_type'))
    if kind=='exact_function_evaluation':
        g,given=packet(task,'variable','expression','arguments','goal')
        need(not given and g['goal']=='all listed exact values' and g['arguments'],
             'The original point queries or assumptions are unresolved')
        variable=g['variable'];x=('v',variable);text=g['expression'];rows=[]
        piece=text.startswith('piecewise(') and text.endswith(')')
        for argument in g['arguments']:
            z=q(rational(argument))
            raw=piece_value(text,variable,z) if piece else m.parse(text,variable,(),('floor',))
            rows.append((z,value_at(raw,x,z)))
        return cert(library,'evaluate_on_original_branches',dict(values=rows),
                    'Для каждой точки определяем её исходную ветвь, проверяем подставленную область и вычисляем точное значение.',
                    original_expression=text)
    formal=kind=='function_expression_substitution'
    if formal:
        g,given=packet(task,'variable','definition','requests','goals')
        need(not given and g['goals']==['derive each expression','retain the domain of each original expression'],
             'The original domain and all substitutions must be covered')
        texts=g['requests'];definition=g['definition']
    elif kind=='polynomial_finite_difference_identity':
        g,given=packet(task,'variable','parameters','definition','proposition')
        need(not given and g['proposition'].count('=')==1, 'A finite difference identity is required')
        texts=list(g['proposition'].split('='));definition=g['definition']
    else:
        g,given=packet(task,'variable','parameters','expression','goal')
        need(given==['h!=0'] and 'h' in g['parameters'] and
             g['goal']=='simplify the finite difference quotient, retaining its original domain','The nonzero step and original difference quotient must be retained')
        texts=[f'(f({g["variable"]}+h)-f({g["variable"]}))/h']
        definition='f('+g['variable']+')='+g['expression']
    variable=g['variable'];x=('v',variable);symbol='f('+variable+')='
    need(definition.startswith(symbol), 'A declared one-variable function is required')
    params=g.get('parameters',[]);raw=m.parse(definition[len(symbol):],variable,params)
    rows=[]
    for text in texts:
        original=apply_function(m.parse(text,variable,params,('f',)),variable,raw)
        guards=domain_conditions(original,smooth=False)
        if not m.contains(original,x) and not params:
            computed=value_at(original,x,ZERO)
        else:
            computed=m.simplify(original)
            if kind=='difference_quotient_simplification' and raw[0]=='rpow' and raw[2]==x and not m.contains(raw[1],x):
                base=raw[1];h=('s','h')
                computed=m.div(m.mul(raw,m.add(('rpow',base,h),q(-1))),h)
        rows.append(dict(expression=text,original=original,value=computed,original_guards=tuple(dict.fromkeys(guards))))
    if kind=='polynomial_finite_difference_identity':
        need(not any(row['original_guards'] for row in rows) and same(*(row['value'] for row in rows)),
             'The substituted polynomial identity does not hold on the entire original domain')
    return cert(library,'substitute_defined_function_then_normalize',dict(results=rows),
                'Подставляем определение в каждое исходное выражение и сохраняем ограничения до преобразований.',
                'Нормализуем многочлены и дроби. При положительном основании выносим степень по правилу сложения показателей.',
                definition=raw)


def measurement(task, library):
    kind=task.get('kind',task.get('task_type'))
    if kind=='measurement_tolerance':
        g,given=packet(task,'operation','true_side_range','unit','desired_absolute_area_error','question',
                       'side_upper_bound','side_unit','same_absolute_error_for_both',exact=False)
        t=rational(g['desired_absolute_area_error'])
        need(not given and t>0,'A positive error tolerance with no unresolved hypotheses is required')
        if g['operation']=='square':
            side=g['true_side_range'];maximum=rational(side['right'])
            need(g['question']=='sufficient absolute measurement tolerance' and 0<=rational(side['left'])<maximum,
                 'A bounded positive original side interval is required')
        else:
            need(g['operation']=='product' and g.get('same_absolute_error_for_both') is True and
                 g['question']=='sufficient common absolute measurement tolerance','A common error bound on a rectangle is needed')
            maximum=rational(g['side_upper_bound'])
            need(maximum>0,'The printed side bound must be positive')
        delta=m.add(('sqrt',q(maximum**2+t)),q(-maximum))
        return cert(library,'invert_product_error_majorant',dict(maximal_uniform_tolerance=delta),
                    'Раскрываем произведение возмущённых положительных величин и оцениваем два линейных и смешанный член.',
                    'Верхняя граница 2Mδ+δ² возрастает при δ≥0. Решаем квадратное неравенство с нужным знаком.',
                    size_bound=q(maximum),desired=q(t),operation=g['operation'])
    if kind=='compare_measurement_errors':
        g,given=packet(task,'measurements','question')
        need(not given and g['question']=='compare relative precision' and len(g['measurements'])>=2,
             'A relative precision comparison with fixed units is required')
        units={'mm':Fraction(1,1000),'cm':Fraction(1,100),'m':Fraction(1),'km':Fraction(1000)}
        rows=[]
        for row in g['measurements']:
            a=rational(row['nominal'])*units[row['unit']]
            error=rational(row['absolute_error'])*units[row['error_unit']]
            need(0<=error<a,'The original true length interval must be strictly positive')
            rows.append(error/(a-error))
        return cert(library,'compare_relative_errors_in_common_units',
                    dict(relative_bounds=list(map(q,rows)),minimum_measurements=[i+1 for i,r in enumerate(rows) if r==min(rows)]),
                    'Сначала переводим каждую длину и её абсолютную ошибку в общие единицы.',
                    'Относительная ошибка максимальна при наименьшем допустимом истинном знаменателе.')
    if kind in ('correct_significant_digits','relative_error_bound_from_digits'):
        g,given=packet(task,'nominal','relative_error','correct_significant_digits','question',exact=False)
        a=rational(g['nominal']);magnitude=abs(a)
        need(not given and magnitude>0,'A nonzero nominal value is required for significant digits')
        decade=Fraction(1)
        while magnitude<decade:
            decade/=10
        while magnitude>=10*decade:
            decade*=10
        if kind=='correct_significant_digits':
            error=rational(g['relative_error'])
            need(g['question']=='guaranteed correct significant digits' and 0<error<1,
                 'Relative error must be positive and less than one')
            delta=magnitude*error/(1-error)
            digits=0;unit=decade
            while delta<=unit/2:
                digits+=1;unit/=10
            value=dict(significant_digits=digits,maximum_absolute_error=q(delta),
                       true_interval=tuple(sorted((q(a/(1+error)),q(a/(1-error))),key=m.num)))
        else:
            digits=g['correct_significant_digits']
            need(type(digits) is int and digits>=1 and g['question']=='relative error bound','A valid significant-place count must be stated')
            delta=decade/2/10**(digits-1)
            value=dict(maximum_relative_error=q(delta/(magnitude-delta)),maximum_absolute_error=q(delta))
        return cert(library,'convert_true_relative_error_and_significant_places',value,
                    'Используем знаменатель истинного значения. Половина единицы соответствующего разряда связывает абсолютную ошибку с числом верных знаков.',
                    nominal=q(a),leading_decade=q(decade))
    if kind=='relative_area_error_estimator':
        g,given=packet(task,'radius','pi_approximation','question')
        row=g['radius'];a=rational(row['nominal']);e=rational(row['absolute_error']);ap=rational(g['pi_approximation'])
        need(not given and g['question']=='minimal relative area error' and 0<=e<a and ap>0,
             'A positive radius interval and positive numerical pi approximation are required')
        nominal=q(ap*a*a);lo,hi=(m.mul(m.PI,q(r*r)) for r in (a-e,a+e))
        traces=tuple(m.div(('abs',m.add(v,m.neg(nominal))),v) for v in (lo,hi))
        return cert(library,'propagate_error_over_positive_interval',dict(range=(lo,hi),nominal=nominal,
                    sharp_relative_bound=('maximum',*traces)),
                    'Площадь возрастает по положительному радиусу. На каждой стороне номинальной площади относительная ошибка монотонна, проверяем оба конца.')
    g,given=packet(task,'operation','quantities','questions')
    need(not given and g['questions']==['range','nominal result','absolute error bound','relative error bound'],
         'The full interval and both errors must be evaluated')
    intervals=[]
    for row in g['quantities']:
        a=rational(row['nominal']);e=rational(row['absolute_error'])
        need(0<=e<a,'Every genuine factor and denominator must stay positive')
        intervals.append((a-e,a,a+e))
    if g['operation']=='product' and intervals:
        lo,nominal,hi=(prod(v) for v in zip(*intervals))
    else:
        need(g['operation']=='quotient' and len(intervals)==2,'Only the ordered positive product or quotient is supported')
        p,v=intervals
        lo,nominal,hi=p[0]/v[2],p[1]/v[1],p[2]/v[0]
    return cert(library,'propagate_error_over_positive_interval',
                dict(range=(q(lo),q(hi)),nominal=q(nominal),maximum_absolute_error=q(max(nominal-lo,hi-nominal)),
                     maximum_relative_error=q(max((nominal-lo)/lo,(hi-nominal)/hi))),
                'Монотонность каждого положительного фактора или делителя даёт точные достижимые края диапазона.',
                'Обе ошибки достигают максимума на одном из краёв. Для относительной ошибки знаменатель берём на том же краю.',
                operation=g['operation'],factor_intervals=[tuple(map(q,row)) for row in intervals])


def polynomial(expr, n):
    try:
        p,d=poly.rf(expr,n[1])
    except (poly.NotRational,poly.Undefined):
        return None
    return tuple(c/d[0] for c in p) if len(d)==1 and d[0] else None


def at(coeff, n):
    return sum(c*n**i for i,c in enumerate(coeff))


def integral_polynomial(e,n):
    p=polynomial(e,n)
    return p if p is not None and all(at(p,i).denominator==1 for i in range(len(p))) else None


def periodic_branches(raw, n):
    """Find an integer residue modulus from exact polynomial phases and rational turns."""
    periods={}
    def scan(e):
        if not isinstance(e,tuple):
            return
        if e[0]=='rpow' and m.simplify(e[1])==q(-1):
            p=integral_polynomial(e[2],n)
            if p is not None:
                lattice_domain(e[2],n,[],whole=True)
                periods[e]=(2*lcm(*(c.denominator for c in p)),p)
                return
        if e[0] in ('sin','cos'):
            p=polynomial(m.simplify(('div',e[1],m.PI)),n)
            if p is not None and len(p)<=2 and len(p)==2:
                lattice_domain(e[1],n,[],whole=True)
                a=p[1]/2
                periods[e]=(a.denominator,None)
                return
        for arg in e[1:]:
            scan(arg)
    scan(raw)
    period=lcm(*(p for p,_ in periods.values()))
    need(period<=48,'The common exact residue period is too large')
    rows=[]
    for j in range(1,period+1):
        replacements={e:q(-1 if at(p,j)%2 else 1) if p is not None else
                      reduce_value(m.substitute(e,{n:q(j)})) for e,(_,p) in periods.items()}
        rows.append((j,m.substitute(raw,replacements)))
    return period,rows


def positive_constant(e, given, n):
    a=m.num(e)
    if a is not None:
        return a>0
    if e[0]=='ln':
        return larger_than_one(e[1],given)
    return any(e==('s',s.split('>')[0]) and s.split('>')[1] in ('0','1') for s in given if '>' in s and s.count('>')==1)


def larger_than_one(e, given):
    a=m.num(e)
    return a>1 if a is not None else e[0]=='s' and e[1]+'>1' in given


def factors(e, power=1):
    if e[0] in ('mul','div'):
        yield from factors(e[1],power)
        yield from factors(e[2],power if e[0]=='mul' else -power)
    elif e[0]=='pow':
        yield from factors(e[1],power*e[2])
    else:
        yield e,power


def tail_sign(e,n,given,whole=False):
    e=m.simplify(e)
    try:
        p,d=poly.rf(e,n[1])
        if any(d):
            if whole:
                from finite_sums import integer_sign_runs
                signs={s for _,s in integer_sign_runs(poly.pm(p,d),1)}
                return signs.pop() if len(signs)==1 else None
            a=p[-1]/d[-1]
            return (a>0)-(a<0)
    except (poly.NotRational,poly.Undefined):
        pass
    if positive_constant(e,given,n) or e in (('factorial',n),m.PI) or e[0] in ('exp','cosh'):
        return 1
    if e[0]=='ln':
        return tail_sign(m.add(e[1],q(-1)),n,given,whole)
    if e[0] in ('sqrt','cbrt','abs'):
        s=tail_sign(e[1],n,given,whole)
        return abs(s) if e[0]=='abs' and s is not None else s
    if e[0] in ('pow','rpow'):
        s=tail_sign(e[1],n,given,whole)
        if s in (0,1):return s
        k=e[2] if e[0]=='pow' else m.num(e[2])
        if k is not None and int(k)==k and s is not None:return abs(s) if k%2==0 else s
    if e[0] in ('add','mul','div'):
        a,b=(tail_sign(z,n,given,whole) for z in e[1:])
        if a is not None and b is not None:
            if e[0]=='mul' or e[0]=='div' and b:return a*b
            if e[0]=='add' and a*b>=0:return a or b
        if e[0]=='add' and not whole:
            try:
                _,trace=dominant_exponential_quotient(('div',e,e),n)
                _,coef=max(trace['numerator_scales'],key=lambda v:abs(m.num(v[0])))
                return 1 if m.num(coef)>0 else -1
            except Unsupported:
                pass
    return None


def lattice_domain(raw,n,given,whole=False):
    """Bind all original guards before any cancellation or phase substitution."""
    from tasks import domain_conditions
    powers=set()
    def visit(e):
        if not isinstance(e,tuple):return
        if e[0]=='rpow':
            p=integral_polynomial(e[2],n)
            if p is not None and p[-1]>0 and (not whole or tail_sign(e[2],n,given,True)==1):
                powers.add(e[2])
        if e[0]=='factorial':
            p=integral_polynomial(e[1],n)
            need(p is not None and p[-1]>=0,'An eventual nonnegative integer factorial argument is required')
        for child in e[1:]:visit(child)
    visit(raw)
    guards=domain_conditions(raw,positive_integer_exponents=tuple(powers))
    for relation,g in guards:
        sign=tail_sign(g,n,given,whole)
        permitted={-1,1} if relation=='nonzero' else {1} if relation=='positive' else {0,1}
        need(sign in permitted,'An original domain condition is unproved on the full tail: '+relation+' '+m.render(g))
    return guards


def zero_power_rate(expr, n, given):
    """Test the lexicographic growth of a monomial on the original positive lattice."""
    coefficient=Fraction(1);degree=Fraction(0);logs=0;factorials=0;rate=Fraction(1)
    symbolic_degree=False;directions=[]
    for factor,power in factors(expr):
        c=m.num(factor)
        if c is not None and c!=0:
            coefficient*=abs(c)**power
        elif factor==n:
            degree+=power
        elif factor==('ln',n):
            logs+=power
        elif factor==('factorial',n):
            factorials+=power
        elif factor[0]=='cbrt' or factor[0]=='sqrt':
            p=m.rational_form(factor[1])
            need(p[1]=={():Fraction(1)} and len(p[0])==1,'A pure positive integer scale is required inside the root')
            (mon,c),=p[0].items()
            need(c>0 and len(mon)==1 and mon[0][0]==n,'The positive root factor needs its original lattice sign')
            degree+=Fraction(power*mon[0][1],3 if factor[0]=='cbrt' else 2)
        elif factor[0]=='rpow' and factor[1]==n and not m.contains(factor[2],n):
            k=m.num(factor[2])
            if k is None:symbolic_degree=True
            else:degree+=power*k
        elif factor[0]=='rpow' and not m.contains(factor[1],n):
            p=polynomial(factor[2],n);a=m.num(factor[1])
            need(p is not None and len(p)==2 and p[1].denominator==1 and p[0].denominator==1,
                 'A real fixed base and integer affine exponent are required')
            exponent=power*int(p[1])
            if a is not None and a:
                rate*=abs(a)**exponent
            elif a==0 and power>0 and p[1]>0:
                return dict(zero_base_tail=True)
            elif factor[1][0]=='s':
                base=factor[1][1]
                if larger_than_one(factor[1],given):
                    directions.append(1 if exponent>0 else -1)
                elif power>0 and p[1]>0 and f'abs({base})<1' in given:
                    directions.append(-1)
                elif power>0 and p[1]>0 and (base+' is a fixed real number' in given or base+'>0' in given):
                    directions.append(0)
                else:raise Unsupported('The rate or original real domain of a fixed base needs a hypothesis')
            else:raise Unsupported('A constant nonzero rate or a positive power of a zero base is required')
        elif not m.contains(factor,n) and positive_constant(factor,given,n):
            continue
        else:
            p=polynomial(factor,n)
            need(p is not None and any(p),'No multiplicative growth estimate for a factor')
            degree+=power*(len(p)-1)
    direction=(rate>1)-(rate<1)
    decay=(factorials<0 or factorials==0 and
           (all(d<=0 for d in (direction,*directions)) and any(d<0 for d in (direction,*directions)) and 0 not in directions
            or not directions and direction==0 and not symbolic_degree and (degree<0 or degree==0 and logs<0)))
    need(decay,'The derived scale does not give strict decay')
    return dict(factorial_power=factorials,known_geometric_rate=q(rate),fixed_rate_signs=directions,
                integer_scale_power='fixed real' if symbolic_degree else q(degree),logarithm_power=logs)


def terms(e):
    return (*terms(e[1]),*terms(e[2])) if e[0]=='add' else (e,)


def dominant_exponential_quotient(e,n):
    need(e[0]=='div','A quotient of finite exponential sums is required')
    def maximum(side):
        rows={}
        for row in terms(side):
            c=Fraction(1);power=None
            for f,k in factors(row):
                if m.num(f) is not None:
                    c*=m.num(f)**k
                else:
                    need(power is None and k==1 and f[0]=='rpow','An exponential summand needs one affine integer exponent')
                    power=f
            need(power is not None,'Each represented summand needs a nonzero fixed exponential scale')
            b=m.num(power[1]);p=polynomial(power[2],n)
            need(b is not None and b and p is not None and len(p)==2 and all(j.denominator==1 for j in p),
                 'Each scale and real integer exponent must be known')
            base=b**int(p[1]);rows[base]=rows.get(base,Fraction(0))+c*b**int(p[0])
        rows={b:c for b,c in rows.items() if c}
        need(rows,'The original sum needs a nonzero leading factor')
        high=max(rows,key=abs);need(high>0 and -high not in rows,'Dominant competing phases require more residue branches')
        return high,rows[high],tuple((q(b),q(c)) for b,c in rows.items())
    a,c,num=maximum(e[1]);b,d,den=maximum(e[2])
    value=q(c/d) if a==b else ZERO if a<b else '+inf' if c/d>0 else '-inf'
    return value,dict(numerator_scales=num,denominator_scales=den,dominant_quotient_rate=q(a/b))


def tail(expr,n,given):
    e=reduce_value(expr)
    if not m.contains(e,n):
        ctx=m.context(dict(variable=n[1],parameters=sorted(names(m.render(e),n[1]))))
        need(m.constant_defined(e,ctx),'The constant branch needs a defined real value')
        return e,dict(step='constant on this residue')
    try:
        p,d=poly.rf(e,n[1])
        need(any(d),'The original denominator is identically zero')
        if not any(p) or len(p)<len(d):value=ZERO
        elif len(p)==len(d):value=q(p[-1]/d[-1])
        else:value='+inf' if p[-1]/d[-1]>0 else '-inf'
        return value,dict(step='rational leading terms',numerator=tuple(map(q,p)),denominator=tuple(map(q,d)))
    except (poly.NotRational,poly.Undefined):
        pass
    inv=m.div(ONE,n);factorial=('factorial',n)
    if same(e,m.div(ONE,('rpow',factorial,inv))):
        return ZERO,dict(step='at least half the factorial factors exceed n/2')
    if same(e,m.div(n,('rpow',factorial,inv))):
        return ('exp',ONE),dict(step='introduce z_n=n ln n−ln n!, difference n ln(1+1/n)→1, then exponential')
    def root_scale(z):
        if z[0]=='rpow' and same(z[2],inv):
            b=z[1]
            if b==n or not m.contains(b,n) and positive_constant(b,given,n):
                return ONE,dict(step='log of positive nth root tends to zero',base=b)
            for piece in terms(b):
                if piece[0]=='rpow' and same(b,m.add(ONE,piece)):
                    c=m.num(piece[1]);p=polynomial(piece[2],n)
                    if c is not None and c>0 and p is not None and len(p)==2:
                        base=reduce_value(('rpow',q(c),q(p[1])))
                        rate=(c>1)-(c<1)
                        if rate*p[1]<=0:base=ONE
                        return base,dict(step='factor the dominant positive term before taking the nth root',base=b)
        return None
    root=root_scale(e)
    if root is not None:return root
    if e[0]=='rpow' and same(e[2],n):
        b=e[1];z=m.simplify(m.mul(n,m.add(b,q(-1))))
        if not m.contains(z,n):
            return ('exp',z),dict(step='logarithm of (1+z/n)^n',scale=z)
        c=m.num(b)
        if c is not None and -1<c<=1:
            return (ONE if c==1 else ZERO),dict(step='fixed geometric tail',base=b)
    # First-order increment of any fixed positive real nth-root base.
    if e[0] in ('add','mul'):
        for row in terms(e):
            for z,k in factors(row):
                if (k==1 and z[0]=='rpow' and same(z[2],inv) and positive_constant(z[1],given,n)
                        and same(e,m.mul(n,m.add(z,q(-1))))):
                    return m.simplify(('ln',z[1])),dict(step='exponential first-order increment at zero',positive_base=z[1])
    if e[0]=='add':
        a,d1=tail(e[1],n,given);b,d2=tail(e[2],n,given)
        need(not (isinstance(a,str) and isinstance(b,str) and a!=b),'Competing infinite terms need a finer scale')
        return (a if isinstance(a,str) else b if isinstance(b,str) else m.add(a,b)),dict(step='add admissible limits',children=(d1,d2))
    try:
        return ZERO,zero_power_rate(e,n,given)
    except Unsupported:
        pass
    try:
        return dominant_exponential_quotient(e,n)
    except Unsupported:
        pass
    bounded=[(f,k) for f,k in factors(e) if k>0 and f[0] in ('sin','cos')]
    if bounded:
        z=e
        for f,k in bounded:z=m.substitute(z,{f:ONE})
        scale=zero_power_rate(m.simplify(z),n,given)
        return ZERO,dict(step='squeeze by absolute value of scale',bounded_factors=[f for f,k in bounded],scale=scale)
    # Multiplication by a nonzero fixed scalar preserves an already established limit.
    if e[0]=='mul' and (m.num(e[1]) is not None or m.num(e[2]) is not None):
        a,b=e[1:];a,b=(b,a) if m.num(a) is None else (a,b)
        z,k=tail(b,n,given);c=m.num(a)
        if isinstance(z,str):
            need(c!=0,'A vanishing constant with an infinite limit is ambiguous')
            z=z if c>0 else ('-inf' if z=='+inf' else '+inf')
        else:z=m.mul(a,z)
        return z,dict(step='fixed scalar multiplication',scalar=a,child=k)
    raise Unsupported('No checked scale and limit on an original residue branch')


SEQUENCE_LIMIT={'compute_sequence_limit','compute_discrete_power_limit','prove_sequence_limit_identity',
                'prove_discrete_factorial_limit','prove_discrete_geometric_limit','prove_discrete_factorial_root_limit',
                'factorial_root_limit','eventual_comparison'}
CLUSTERS={'sequence_cluster_set','unbounded_but_not_magnitude_infinity'}


def parse_sequence(text,n):
    patches={}
    def large(match):
        value=int(match[1])
        if value<=m.MAX_INTEGER_POWER:return match[0]
        symbol='proofExponent'+str(len(patches))
        need(symbol not in text,'An exponent placeholder must be fresh')
        patches[('s',symbol)]=q(value)
        return '^'+symbol
    text=re.sub(r'\^(\d+)(?![\d.])',large,text)
    params=names(text,n[1],('factorial','floor','log10'))
    return m.substitute(m.parse(re.sub(r'\blog10\(', 'lg(',text),n[1],params,('factorial','floor')),patches)


def tail_packet(task,library):
    g,given=packet(task,'expression','variable','approach','target_limit','source_claim','left','right','comparison',exact=False)
    n=('v',g.get('variable','n'))
    natural=n[1]+' is a positive integer'
    need(task.get('index_domain')=='positive_integers' or natural in given,'The natural lattice is required')
    need(g.get('approach','positive_integer_index_to_infinity')=='positive_integer_index_to_infinity' and
         all(c==natural or re.fullmatch(NAME+r' is a fixed real number|'+NAME+r'>[01]|abs\('+NAME+r'\)<1',c) for c in given),
         'The original approach or fixed parameters are not resolved')
    if 'comparison' in g:
        need(set(g)=={'left','right','comparison'} and g['comparison']=='eventually greater','An original direction of comparison is needed')
        a,b=(parse_sequence(g[z],n) for z in ('left','right'))
        guards=[lattice_domain(z,n,given) for z in (a,b)];e=m.add(b,m.neg(a))
        try:
            v,proof=tail(e,n,given);need(v in ('+inf','-inf') or (m.num(v) is not None and m.num(v)!=0),'A nonzero comparison limit is needed')
            side='right' if v=='+inf' or m.num(v) is not None and m.num(v)>0 else 'left'
        except Unsupported:
            try:positive=zero_power_rate(m.div(a,b),n,given);side='right'
            except Unsupported:positive=zero_power_rate(m.div(b,a),n,given);side='left'
            # Rate compares positive sources; otherwise signs would have to be separated beforehand.
            need(all(tail_sign(e,n,given)==1 for e in (a,b)),'Comparison of signed growth needs explicit sign proof')
            proof=positive
        return cert(library,'compare_eventual_growth',dict(eventually_greater=side),
                    'Выводим строгий знак разности на хвосте либо показываем, что отношение двух положительных величин стремится к нулю.',
                    source_operands=(a,b),original_guards=guards,comparison_evidence=proof)
    need('expression' in g and not (set(g)&{'left','right'}),'A single original sequence is required')
    e=parse_sequence(g['expression'],n);guards=lattice_domain(e,n,given);value,proof=tail(e,n,given)
    claim=g.get('source_claim') if g.get('source_claim') is not None else g.get('target_limit')
    if claim is not None:
        target=parse_sequence(claim,n)
        need(isinstance(value,tuple) and same(value,target),'The computed limit disagrees with the original claimed value')
    return cert(library,'derive_lattice_limit_by_scale',value,
                'Проверяем исходную натуральную область на хвосте. Выделяем определяющий масштаб: соседнее отношение, логарифм, старший член или ограниченную фазу.',
                'Из строгой оценки масштаба или точного предела на хвосте следует результат для исходного выражения.',
                original=e,source_index=n,conditions=given,original_guards=guards,scale=proof)


def choose_edges(values):
    from functools import cmp_to_key
    def compare(a,b):
        if a==b:return 0
        if a=='-inf' or b=='+inf':return -1
        if b=='-inf' or a=='+inf':return 1
        delta=m.add(a,m.neg(b));sign=m.sign(delta,m.context({'variable':'n'}))
        if sign is None:
            lo,hi=constant_enclosure(delta)
            sign=1 if lo>0 else -1 if hi<0 else 0 if lo==hi==0 else None
        need(sign in (-1,0,1),'The exact edge values could not be ordered')
        return sign
    z=sorted(values,key=cmp_to_key(compare))
    return z[0],z[-1]


def constant_enclosure(e):
    c=m.num(e)
    if c is not None:return c,c
    if e==('exp',ONE):
        n=16;total=sum(Fraction(1,factorial(k)) for k in range(n+1))
        return total,total+Fraction(1,n*factorial(n))
    if e[0]=='sqrt' and m.num(e[1]) is not None and m.num(e[1])>=0:
        z=m.num(e[1]);scale=10**12
        a=Fraction(isqrt(z.numerator*scale**2//z.denominator),scale)
        return a,a+Fraction(1,scale)
    if e[0]=='add':
        (a,b),(c,d)=map(constant_enclosure,e[1:]);return a+c,b+d
    if e[0]=='mul':
        (a,b),(c,d)=map(constant_enclosure,e[1:]);values=(a*c,a*d,b*c,b*d)
        return min(values),max(values)
    raise Unsupported('A rational enclosure for this exact constant remains to be proved')


def cluster_packet(task,library):
    kind=task.get('kind',task.get('task_type'))
    g,given=packet(task,'sequence','goals','goal','sequence_by_blocks',exact=False)
    need(task.get('index_domain')=='positive_integers' or NATURAL in given,'The residue analysis needs positive integer indices')
    need(all(c==NATURAL or re.fullmatch(NAME+r','+NAME+r' are fixed real numbers',c) for c in given),
         'Additional lattice restrictions must be preserved')
    need('sequence' in g and 'sequence_by_blocks' not in g,'The original array needs a separate block coverage calculation')
    n=('v','n');raw=parse_sequence(g['sequence'],n);period,rows=periodic_branches(raw,n)
    need(period>1,'A finite exact residue partition is needed')
    guards=[lattice_domain(e,n,given,whole=True) for _,e in rows]
    results=[(r,reduce_value(e),*tail(e,n,given)) for r,e in rows]
    vs=[v for _,_,v,_ in results]
    if kind=='sequence_cluster_set':
        need(g.get('goal')=='all subsequential limits','The complete cluster set is requested')
        value=dict(cluster_values=sorted(set(vs),key=str))
    elif kind=='unbounded_but_not_magnitude_infinity':
        need(g.get('goals')==['unbounded','not unsigned_infinity_in_magnitude']
             and any(isinstance(v,str) for v in vs) and any(isinstance(v,tuple) for v in vs),
             'This residue calculation has no required pair of bounded and unbounded witnesses')
        value=dict(unbounded=True,magnitude_infinity=False)
    else:
        lo,hi=choose_edges(vs);value=dict(liminf=lo,limsup=hi)
        if kind=='sequence_range_and_envelopes':
            need(g.get('goals')==['infimum over all positive integer indices','supremum over all positive integer indices','liminf','limsup'],
                 'The four original extremal outputs must all be checked')
            bounds=[]
            for r,e,z,_ in results:
                if not m.contains(e,n):bounds.append((z,z));continue
                p,d=m.rational_form(e)
                need(len(p)==len(d)==1,'Whole-lattice residue range needs a monotonicity bound')
                (num,c),=p.items();(den,k),=d.items()
                need(c*k>0 and all(f==n for f,j in (*num,*den)),'A positive pure power is required for the whole residue range')
                start=m.simplify(m.substitute(e,{n:q(r)}))
                bounds.append(choose_edges((start,z)))
            value.update(infimum=choose_edges([a for a,b in bounds])[0],supremum=choose_edges([b for a,b in bounds])[1])
        else:need(g.get('goals')==['liminf','limsup'],'Both original limiting envelopes must be supplied')
    return cert(library,'split_by_exact_integer_phase',value,
                'Вычисляем общий период всех периодических фаз. Подставляем каждый остаток только в периодические части, оставляя индекс свободным в масштабе.',
                'Классы исчерпывают все индексы. Конечное число доказанных ветвей даёт все частичные пределы, а при запросе глобальных граней проверяем всю каждую ветвь.',
                period=period,original=raw,residue_proofs=results,conditions=given,original_guards=guards)


def epsilon_bound(expr,n):
    e=m.simplify(expr)
    try:
        p,d=poly.rf(e,n[1])
        if len(d)>len(p) and all(c*d[-1]>=0 for c in d):
            c=sum(map(abs,p))/abs(d[-1])
            return ('power',q(c),len(d)-len(p))
    except (poly.NotRational,poly.Undefined):
        pass
    scalar=Fraction(1);scale=[]
    for f,k in factors(e):
        c=m.num(f)
        if c is not None:scalar*=abs(c)**k
        else:scale.append((f,k))
    need(len(scale)==1,'No common positive majorant for this exact residue')
    (f,k),=scale
    if f==('factorial',n) and k==-1:
        return ('geometric',q(2*scalar),q(Fraction(1,2)))
    if f[0]=='rpow' and k==1 and f[2]==n:
        a=m.num(f[1]);need(a is not None and 0<abs(a)<1,'A strict positive geometric rate in modulus is needed')
        return ('geometric',q(scalar),q(abs(a)))
    raise Unsupported('The exact majorant cannot be inverted for this sequence')


def integer_root_ceiling(z,k):
    lo,hi=0,1
    while hi**k<z:hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k<z:lo=mid
        else:hi=mid
    return hi


def lower_magnitude(expr,n):
    e=m.simplify(expr)
    p=polynomial(e,n)
    if p is not None and len(p)>1 and p[-1] and not any(p[:-1]):
        return ('power',q(abs(p[-1])),len(p)-1)
    if e[0]=='rpow' and e[2]==('sqrt',n) and larger_than_one(e[1],[]):
        return ('exponential_root',e[1])
    if e[0]=='div' and e[1][0]=='ln' and e[2][0]=='ln' and larger_than_one(e[2][1],[]):
        if same(e[1][1],m.div(('ln',n),e[2])):
            return ('double_logarithm',e[2][1])
    raise Unsupported('The source magnitude has no exact increasing lower scale')


def witness_threshold(bound,threshold,mode):
    name,c,*rest=bound
    if mode=='epsilon':
        coef=m.num(c)
        return q(max(1,integer_root_ceiling(coef/threshold,rest[0]) if name=='power'
                     else power_ceiling(coef/threshold,1/m.num(rest[0]))))
    if name=='power':return q(max(1,integer_root_ceiling(threshold/m.num(c),rest[0])))
    if name=='exponential_root':return q(max(1,power_ceiling(threshold,m.num(c))**2))
    return ('integer_above',('rpow',c,('rpow',c,q(threshold))))


def quantified_tails(task,library):
    kind=task.get('kind',task.get('task_type'))
    if kind in ('quantifier_formulation','negate_Cauchy_quantifiers'):
        if kind=='quantifier_formulation':
            g,given=packet(task,'source_statement','required_output')
            match=re.fullmatch(r'lim\(n→∞\)x\[n\]=(unsigned infinity|[+-]infinity)',g['source_statement'])
            need(given==[NATURAL] and g['required_output']=='quantified inequalities' and match,
                 'The signed or unsigned source direction is missing')
            target=match[1]
            inequality={'unsigned infinity':'abs(x[n])>E','+infinity':'x[n]>E','-infinity':'x[n]<-E'}[target]
            result=dict(quantifiers=['for every E>0','there exists N in positive integers','for every integer n>N'],predicate=inequality)
        else:
            g,given=packet(task,'goal')
            need(given==[NATURAL] and g['goal']=='write the quantified negation of the Cauchy criterion for a real sequence',
                 'The original Cauchy quantifier goal is missing')
            result=dict(quantifiers=['there exists epsilon>0','for every N in positive integers','there exist integers m,n>N'],
                        predicate='abs(x[m]-x[n])>=epsilon')
        return cert(library,'expand_discrete_limit_quantifiers',result,
                    'Разворачиваем определение с его областью индексов. При отрицании меняем каждый квантор и строгость конечного сравнения.')
    epsilon=kind=='epsilon_sequence_limit'
    if epsilon:
        g,given=packet(task,'sequence','target_limit','epsilon_condition','tail_goal','table_epsilons',exact=False)
        need(g.get('epsilon_condition','epsilon>0')=='epsilon>0' and g.get('tail_goal') in
             ('abs(x[n])<epsilon for n>N','abs(x[n]-1)<epsilon for every integer n>N(epsilon)'),
             'The original epsilon target and strict tail need to be represented')
        target=q(rational(g['target_limit']))
        need(target==(ONE if 'x[n]-1' in g['tail_goal'] else ZERO),'Target does not agree with the stated tail')
    else:
        g,given=packet(task,'sequence','target','tail_goal','table_E')
        need(g['target']=='unsigned_infinity_in_magnitude' and g['tail_goal']=='abs(x[n])>E for every n>N(E)',
             'The original unsigned approach needs a magnitude witness')
    need(given in ([NATURAL],[NATURAL,'n>=2']),'The original witness lattice restrictions are unresolved')
    n=('v','n');raw=parse_sequence(g['sequence'],n);period,rows=periodic_branches(raw,n)
    guards=[lattice_domain(e,n,given) for _,e in rows]
    bounds=[epsilon_bound(('add',e,m.neg(target)),n) if epsilon else lower_magnitude(e,n) for _,e in rows]
    mode='epsilon' if epsilon else 'magnitude'
    records=[]
    for s in g['table_epsilons' if epsilon else 'table_E']:
        t=rational(s);need(t>0,'Every requested threshold must be strictly positive')
        values=[witness_threshold(b,t,mode) for b in bounds]
        z=values[0] if len(set(values))==1 else max(values,key=m.num)
        records.append((q(t),z))
    return cert(library,'construct_integer_tail_witness',dict(table=records,mode=mode,strict=True,
                formula=dict(action='maximum of the checked inverse majorants',branches=bounds)),
                'Находим одну точную степенную или геометрическую оценку для каждого остатка. Для растущей функции обращаем её монотонный масштаб.',
                'Берём целую границу не меньше каждого обратного порога. Строгое условие n>N даёт все нужные неравенства.',
                original=raw,residue_period=period,original_guards=guards)


TAIL_THEOREMS={
    'bounded_variation_convergence_and_counterexample':(
        {'hypothesis':'exists C, every n>=2 has sum(k,1,n-1,abs(x[k+1]-x[k]))<C',
         'goals':['bounded variation implies finite convergence','construct convergent sequence with unbounded total variation']},
        {'converges':True,'converse_counterexample':'(-1)^n/n'},
        ('Частичные суммы модулей приращений возрастают и ограничены. Поэтому их хвосты стремятся к нулю.',
         'Телескопирование и неравенство треугольника мажорируют |x_m−x_n| хвостом вариации. По Коши x_n сходится.',
         'Для обратного примера (−1)^n/n сходится к нулю, но модуль его приращения равен 1/n+1/(n+1).')),
    'subsequence_limit_inheritance':(
        {'hypothesis':'x[n]->a finite and p[n] strictly increasing positive integers','conclusion':'x[p[n]]->a'},
        {'limit':'a','intermediate':'p[n]>=n'},
        ('Строго возрастающие натуральные индексы удовлетворяют p_n≥n. Поэтому определение исходного предела непосредственно переносится на весь хвост подпоследовательности.',)),
    'monotone_subsequence_convergence':(
        {'hypothesis':'x[n] monotone and x[p[n]]->a finite','conclusion':'x[n]->a'},
        {'limit':'a','both_monotonicity_directions':True},
        ('При неубывании для каждого n можно взять p_j≥n. Тогда x_n≤x_{p_j}≤a.',
         'Позднее p_J даёт x_n≥x_{p_J}>a−ε при n≥p_J. Невозрастающий случай следует применением к −x_n.')),
    'absolute_value_limit':(
        {'hypothesis':'x[n]->a finite','conclusion':'abs(x[n])->abs(a)'},
        {'limit':'abs(a)','bound':'abs(abs(x[n])-abs(a))<=abs(x[n]-a)'},
        ('Обратное неравенство треугольника ограничивает разность модулей исходной разностью, стремящейся к нулю.',)),
    'conditional_successive_ratio_limit':(
        {'hypothesis':'x[n]->a finite','question':'existence and possible values of the successive ratio limit'},
        {'if_a_nonzero':'ratio tends to 1 and is defined eventually',
         'if_a_zero':'no guaranteed existence; any finite limit in [-1,1]',
         'examples':['1/n! for 0','r^n for 0<|r|<1','1/n for 1','(-1)^n/n for -1',
                     '2^(-n)*(2+(-1)^n) for two ratio phases']},
        ('При a≠0 знаменатель ненулевой на хвосте и действует предел частного.',
         'При a=0 предел модуля отношения больше единицы заставил бы модули членов расти геометрически. Включая существование самого отношения, остальные варианты дают перечисленные примеры.')),
    'convergent_sequence_bounded':(
        {'hypothesis':'x[n]->a finite','conclusion':'exists M finite, all abs(x[n])<=M'},
        {'bound':'max(abs(a)+1, max_{1<=k<=N}abs(x[k]))'},
        ('Для ε=1 хвост ограничен |a|+1. Максимум этой величины и модулей конечного префикса ограничивает всю последовательность.',)),
    'attained_extrema_and_examples':(
        {'hypothesis':'x[n] converges to a finite real limit',
         'goals':['sup or inf is attained','construct examples of each of the three attainment types']},
        {'attains_at_least_one':True,'only_sup':'1/n','only_inf':'-1/n','both':'(-1)^n/n'},
        ('Если одно значение ниже предела, после некоторого индекса все значения больше него. Минимум находится в конечном префиксе.',
         'Значение выше предела аналогично даёт достижение максимума. Если все значения равны пределу, достигаются обе грани.',
         'Для ±1/n одна граница достигается в первом члене, противоположная равна нулю и недостижима. У знакопеременного примера достигаются обе.')),
    'positive_infinity_attained_minimum':(
        {'hypothesis':'x[n]->+infinity signed','conclusion':'there exists an attained global minimum'},
        {'minimum':'minimum of finite prefix before all terms exceed x[1]'},
        ('Определение +∞ даёт хвост, где все значения больше первого. Минимум конечного префикса одновременно глобальный и достигнутый.',)),
    'Bolzano_Weierstrass_proof':(
        {'hypothesis':'x[n] is bounded','conclusion':'there is a finitely convergent subsequence'},
        {'subsequence':'select increasing index in the j-th retained half interval','interval_length':'initial_length/2^j'},
        ('Делим ограничивающий отрезок пополам. В одной половине остаётся бесконечно много индексов, её сохраняем.',
         'Повторяем для вложенных отрезков. Их длины стремятся к нулю, поэтому есть единственная общая точка.',
         'В каждом следующем отрезке берём индекс больше уже найденного. Его значение отстоит от общей точки не больше длины этого отрезка.')),
    'unbounded_subsequence_extraction':(
        {'hypothesis':'x[n] is unbounded in magnitude','conclusion':'there is a subsequence with unsigned magnitude infinity'},
        {'witness':'p[j]>p[j-1] and abs(x[p[j]])>j'},
        ('Удаление конечного числа членов сохраняет неограниченность по модулю. Последовательно выбираем более поздний индекс с модулем больше j.',)),
    'connected_cluster_set':(
        {'hypotheses':['bounded x[n]','x[n+1]-x[n]->0'],'conclusion':'cluster set is the closed interval[liminf(x),limsup(x)]'},
        {'cluster_set':['liminf(x)','limsup(x)'],'auxiliary_witness':'first consecutive crossing of each fixed interior target'},
        ('Края уже являются частичными пределами. Вне замкнутого промежутка между ними частичных пределов нет.',
         'Для внутреннего c сколь угодно поздно встречаются x_n<c и x_n>c. На каждом переходе берём первую точку с другой стороны c, строго позже предыдущей.',
         'Расстояние её значения до c не больше модуля одного соседнего приращения, стремящегося к нулю.')),
    'nonnegative_subadditive_ratio_limit':(
        {'hypothesis':'0<=x[m+n]<=x[m]+x[n] for positive integers m,n','conclusion':'x[n]/n has a finite limit'},
        {'limit':'inf_{k>=1} x[k]/k','decomposition':'n=q*k+r, 0<=r<k'},
        ('Из субаддитивности при n=qk+r следует x_n≤q x_k+C_k с конечным C_k=max(0,x₁,…,x_{k−1}). При r=0 слагаемое x_r не вводится.',
         'При фиксированном k после деления limsup не больше x_k/k. Снизу все отношения не меньше общей нижней грани, которая конечна и неотрицательна.')),
    'Cesaro_convergence_and_counterexample':(
        {'hypothesis':'x[n]->a finite','mean':'sum(k,1,n,x[k])/n','goals':['mean tends to a','counterexample to converse']},
        {'limit':'a','converse_counterexample':'(-1)^n'},
        ('Вычитаем a из каждого слагаемого. Конечная начальная сумма после деления на n исчезает, модуль среднего хвоста ограничен ε.',
         'Частичные суммы (−1)^n ограничены, поэтому их средние стремятся к нулю, а сама последовательность расходится.')),
    'Cesaro_positive_infinity':(
        {'hypothesis':'x[n]->+infinity signed','conclusion':'sum(k,1,n,x[k])/n ->+infinity'},
        {'limit':'+inf'},
        ('Для любой границы M в исходном хвосте все значения больше 2|M|+1. Вес хвоста стремится к единице, конечная начальная сумма/n к нулю. Среднее на всём достаточно позднем хвосте больше M.',)),
    'geometric_mean_limit':(
        {'hypotheses':['x[n]>0','x[n]->a finite'],'geometric_mean':'product(k,1,n,x[k])^(1/n)','conclusion':'geometric mean ->a'},
        {'limit':'a','cases':['a>0','a=0']},
        ('При a>0 логарифмы сходятся к ln a. Логарифм среднего геометрического есть их среднее арифметическое.',
         'При a=0 фиксируем ε>0 и x_k<ε на хвосте. После извлечения корня постоянный префикс стремится к единице, а верхняя граница хвоста к ε.')),
    'positive_root_ratio_limit':(
        {'hypotheses':['x[n]>0','ratio limit exists'],'conclusion':'nth-root limit equals successive-ratio limit'},
        {'limit':'successive ratio limit','intermediate':'x[n]=x[1]*product(k,1,n-1,x[k+1]/x[k])'},
        ('Телескопическое произведение положительных отношений равно x_n/x₁. Среднее геометрическое этих отношений имеет их предел, включая нуль.',
         'Первый постоянный фактор и переход от корня степени n−1 к n предела не меняют. При бесконечном отношении используем произвольно большую нижнюю геометрическую оценку хвоста.')),
    'Stolz_theorem':(
        {'hypotheses':['y[n+1]>y[n]','y[n]->+infinity signed','increment-ratio limit exists'],'conclusion':'ratio limit equals increment-ratio limit'},
        {'limit':'increment-ratio limit','intermediate':'positive telescoping increments of denominator'},
        ('Ограничиваем отношение соседних приращений между L−ε и L+ε на хвосте. Умножаем на положительное Δy_k, затем складываем.',
         'Суммы приращений телескопируются. После деления на y_n>0 постоянные начальные величины исчезают. Для бесконечных L берём только нужную сторону сравнения.')),
    'positive_sequence_convergence_criterion':(
        {'hypothesis':'limsup(x)*limsup(1/x)=1','conclusion':'x[n] converges finitely'},
        {'converges':True,'intermediate':'limsup(1/x)=1/liminf(x)'},
        ('На положительной оси обратное преобразование меняет порядок. Поэтому верхний предел 1/x равен обратной величине нижнего предела x.',
         'Произведение ровно 1 возможно только при положительных конечных обеих гранях. Оно превращается в их отношение, откуда обе грани равны.')),
    'limsup_sum_with_convergent_factor':(
        {'hypothesis':'limit x[n] exists','proposition':'limsup(x+y)=limit(x)+limsup(y)'},
        {'limit_superior':'limit(x)+limsup(y)'},
        ('При конечном a=lim x_n сдвинутая последовательность зажата между y_n+a−ε и y_n+a+ε. Верхний предел сохраняет порядок, а затем ε→0.',)),
    'construct_finite_cluster_set':(
        {'given':'finite real list a[1]..a[p]','goal':'construct a sequence with these subsequential limits'},
        {'construction':'periodic repetition of the given nonempty list','cluster_set':'set of the given values'},
        ('Повторяем конечный список по периодам. Каждое данное значение встречается бесконечно часто, а внешняя точка имеет положительное расстояние от этого конечного множества.',)),
    'construct_countable_cluster_set':(
        {'given':'arbitrary real sequence a[j]','goals':['construct a sequence with each a[j] as a cluster value','identify necessarily forced additional cluster values']},
        {'construction':'concatenate initial blocks of growing length','all_finite_clusters':'closure of the given values','forced':'closure of the given values'},
        ('Каждое данное значение повторяется во всех достаточно длинных блоках.',
         'Если оно приближается к другой точке через значения списка, для каждого уровня точности берём новое достаточно позднее повторение. Замыкание списка поэтому обязательно.',
         'Предложенная последовательность не выходит за список, следовательно других конечных частичных пределов у неё нет.')),
}


def abstract_tail(task,library):
    kind=task.get('kind',task.get('task_type'));expected,value,argument=TAIL_THEOREMS[kind]
    g,given=packet(task,*expected)
    need(g==expected,'A hypothesis or quantified conclusion differs from the admitted general theorem')
    allowed={
        'construct_finite_cluster_set':['p is a positive integer','a[j] are real'],
        'positive_sequence_convergence_criterion':['x[n]>0'],
    }
    need([c for c in given if c!=NATURAL]==allowed.get(kind,[]) and
         (NATURAL in given or task.get('index_domain')=='positive_integers'),
         'The original index type and required mathematical assumptions must match')
    return cert(library,'derive_quantified_sequence_theorem',value,*argument,
                semantic_transition=kind,hypotheses=given,original_goal=g)


def arithmetic_tails(task,library):
    kind=task.get('kind',task.get('task_type'))
    n=('v','n')
    if kind=='moving_harmonic_block_limit':
        g,given=packet(task,'expression','goal')
        match=re.fullmatch(r'sum\(k,n\+1,(\d+)\*n,1/k\)',g['expression'])
        need(not given and g['goal']=='compute limit' and match and int(match[1])>1 and task.get('index_domain')=='positive_integers',
             'The range of the harmonic block must be a fixed multiple of the same index')
        scale=q(int(match[1]))
        return cert(library,'bound_harmonic_block_by_neighboring_integrals',('ln',scale),
                    'Убывание 1/t для положительного t зажимает сумму между интегралами на соседних границах.',
                    'Обе разности логарифмов после деления аргументов на n стремятся к ln от исходного множителя.',
                    lower_end=n,upper_end=m.mul(scale,n),integrand='1/k')
    if kind=='Cauchy_divergence_proof':
        g,given=packet(task,'sequence','required_method')
        match=re.fullmatch(r'sum\(k,1,n,(\d+)/k\)',g['sequence'])
        need(given==[NATURAL] and g['required_method']=='negated Cauchy criterion' and match,
             'A positive harmonic prefix and the original Cauchy method are required')
        c=q(int(match[1] or '1'));need(m.num(c)>0,'The harmonic profile must be strictly positive')
        return cert(library,'exhibit_large_block_in_cauchy_test',dict(diverges=True,block=('n+1','2*n'),threshold=m.div(c,q(2))),
                    'Слагаемые от n+1 по 2n не меньше c/(2n). Блок из n членов даёт разность не меньше c/2 на сколь угодно поздних парах.',
                    coefficient=c,cauchy_quantifiers='for every N choose n>N and m=2n')
    if kind=='harmonic_logarithm_convergence':
        g,given=packet(task,'sequence','goals','source_given_decimal')
        need(not given and g['sequence']=='sum(k,1,n,1/k)-ln(n)' and g['goals']==[
             'finite convergence','derive H[n]=C+ln(n)+epsilon[n], epsilon[n]->0'] and
             task.get('index_domain')=='positive_integers','The original harmonic normalization or asymptotic output differs')
        return cert(library,'monotone_harmonic_logarithm_difference',
                    dict(converges=True,constant='lim_{n→∞}(H[n]-ln(n))',expansion='H[n]=C+ln(n)+o(1)'),
                    'Разность соседних членов равна 1/(n+1)−ln(1+1/n), строго отрицательна по интегральной оценке логарифма.',
                    'Сумма H_n≥∫_1^{n+1}dt/t, поэтому разность H_n−ln n положительна. Монотонность и ограниченность дают предел и обосновывают исчезающий остаток.')
    if kind=='logarithm_two_sided_bound':
        g,given=packet(task,'proposition')
        need(given==[NATURAL] and g['proposition']=='1/(n+1)<ln(1+1/n)<1/n','A strictly positive reciprocal scale is needed')
        return cert(library,'logarithmic_integral_between_endpoint_rectangles',dict(holds=True),
                    'Логарифм приращения равен интегралу 1/(1+t) от нуля до 1/n. Строгая монотонность подынтегральной функции даёт обе оценки исходными прямоугольниками.')
    if kind=='exponential_tangent_inequality':
        g,given=packet(task,'proposition')
        p=re.fullmatch(r'1\+('+NAME+r')<exp\(\1\)',g['proposition'])
        need(p and [c for c in given if c!=NATURAL]==[p[1]+' is real',p[1]+'!=0'],
             'The strict tangent inequality needs the original nonzero real argument')
        return cert(library,'strict_convex_exponential_tangent',dict(holds=True,equality_only_at_zero=True),
                    'Производная exp(t)−1−t равна exp(t)−1, отрицательна слева от нуля и положительна справа. Строгий минимум равен нулю.')
    g,given=packet(task,'expression','target_limit')
    match=re.fullmatch(r'sum\(k,1,n,(k|\((\d+)\*k([+-]\d+)\))\^p\)/n\^(?:\(p\+1\)|p-n/\(p\+1\))',g['expression'])
    need(given==['p is a fixed positive integer'] and task.get('index_domain')=='positive_integers' and match,
         'A fixed positive integer power and a bound polynomial arithmetic lattice are required')
    a=int(match[2] or 1);b=int(match[3] or 0)
    refined=g['expression'].endswith('/n^p-n/(p+1)')
    p=('s','p');parameter=m.add(p,ONE)
    need(a>0 and (not refined or (a,b)==(1,0)), 'Second-order subtraction must match the exact original leading coefficient')
    scale=ONE if a==1 else reduce_value(('rpow',q(a),p))
    value=q(1,2) if refined else m.div(scale,parameter)
    need(same(value,m.parse(g['target_limit'],None,['p'])),'The verified leading coefficient disagrees with the claimed value')
    argument=['Суммируем биномиальные разности (k+1)^(p+1)−k^(p+1). Главный вклад равен (p+1)Σ k^p, младшие степени дают меньший порядок.']
    if refined:argument.append('Оставляем второй биномиальный коэффициент и используем ведущую формулу для p−1. Следующий коэффициент равен 1/2. При p=1 то же равенство получается точно.')
    elif (a,b)!=(1,0):argument.append('Ограниченный сдвиг в каждом слагаемом арифметической решётки меняет только младшие порядки.')
    return cert(library,'derive_symbolic_power_sum_by_adjacent_binomial_differences',value,*argument,
                lattice_slope=a,lattice_shift=b,second_order=refined,parameter=p)


ARITHMETIC_TAIL={'moving_harmonic_block_limit','Cauchy_divergence_proof','harmonic_logarithm_convergence',
                 'logarithm_two_sided_bound','exponential_tangent_inequality','symbolic_power_sum_limit'}


def convergent_prefix(task,library):
    kind=task.get('kind',task.get('task_type'))
    g,given=packet(task,'sequence','required_method')
    if kind=='cauchy_sequence_convergence':
        match=re.fullmatch(r'('+NAME+r')\[0\]\+sum\(k,1,n,\1\[k\]\*('+NAME+r')\^k\)',g['sequence'])
        need(match,'A finite power series with bounded coefficient sequence is required')
        a,q0=match.groups();M='M'
        need(g['required_method']=='Cauchy criterion' and given==[NATURAL,f'{a}[k] are real',
              f'{M}>0',f'for every k>=0,abs({a}[k])<{M}',f'{q0} is real',f'abs({q0})<1'],
              'The original coefficient bounds and Cauchy method must be supplied')
        return cert(library,'compare_cauchy_prefix_with_geometric_tail',dict(converges=True),
                    'В разности двух частичных сумм остаётся только конечный хвост.',
                    'Его модуль не больше M|q|^(n+1)/(1−|q|), независимо от правого конца. При |q|<1 граница стремится к нулю, включая q=0.',
                    bounded_sequence=a,contraction=q0,majorant=M)
    need(g['required_method']=='monotone and bounded sequence theorem','The required bounded monotone argument must be reproduced')
    digit=re.fullmatch(r'('+NAME+r')\[0\]\+sum\(k,1,n,\1\[k\]/(\d+)\^k\)',g['sequence'])
    if digit:
        name,B=digit[1],int(digit[2])
        need(B>=2 and given==[NATURAL,f'{name}[0] is a nonnegative integer',
             f'for every k>=1,{name}[k] is an integer in[0,{B-1}]'],'Exact radix and coefficient bounds are needed')
        return cert(library,'bound_monotone_digit_prefix',dict(converges=True,upper_bound=name+'[0]+1'),
                    'Каждое новое слагаемое неотрицательно. Все дробные разряды вместе ограничены геометрическим рядом с суммой единица.',
                    radix=B,coefficient_bound=B-1)
    product=re.fullmatch(r'product\(k,1,n,(.+)\)',g['sequence'])
    need(product and given==[NATURAL],'The original product and its natural binding must be identifiable')
    k=('v','k');raw=parse_sequence(product[1],k);f=reduce_value(raw)
    geom=re.fullmatch(r'1([+-])(\d+(?:/\d+)?/)?(\d+)\^k',product[1])
    if geom:
        base=int(geom[3]);c=rational(geom[2][:-1]) if geom[2] else Fraction(1)
        need(base>1 and c>0 and (geom[1]=='+' or c<base),
             'All factors must be positive and the absolute increments geometrically summable')
        values=dict(converges=True,monotone='increasing' if geom[1]=='+' else 'decreasing',
                    lower_bound=ZERO,upper_bound=('exp',q(c/(base-1))) if geom[1]=='+' else ONE)
        return cert(library,'log_bound_monotone_geometric_product',values,
                    'Проверяем знак и монотонность частичных произведений по положительным множителям.',
                    'Если они растут, логарифмы ограничены суммой положительных геометрических приращений. Если убывают, общая нижняя граница равна нулю.',
                    factor=raw,ratio=q(Fraction(1,base)),absolute_increment_scale=q(c))
    p,d=poly.rf(f,'k')
    need(len(p)==len(d)==2 and p[1]>0 and d[1]>0 and at(p,1)>0 and at(d,1)>0 and p[1]<d[1],
         'A positive affine ratio strictly below one eventually is required')
    cut=max(1,ceil((p[0]-d[0])/(d[1]-p[1])))
    return cert(library,'find_monotone_tail_from_positive_factors',dict(converges=True,lower_bound=ZERO,
                decreasing_from_factor=cut),'Находим первый гарантированный хвост, где исходный положительный множитель не больше единицы.',
                'Частичные произведения на хвосте не возрастают и остаются неотрицательными.',
                original_factor=raw,polynomial_coefficients=tuple(tuple(map(q,z)) for z in (p,d)))


def monotone_recursion(task,library):
    kind=task.get('kind',task.get('task_type'))
    if kind=='recursive_monotone_bounded_convergence':
        g,given=packet(task,'initial','recurrence','required_method')
        p=re.fullmatch(r'x\[n\+1\]=sqrt\((.+)\+x\[n\]\)',g['recurrence'])
        need(p and given==[NATURAL] and g['required_method']=='monotone and bounded sequence theorem'
             and g['initial']==f'x[1]=sqrt({p[1]})','The nesting, initial seed or the requested method is not preserved')
        c=rational(p[1]);need(c>0,'A positive main radical is required')
        R=m.div(m.add(ONE,('sqrt',q(1+4*c))),q(2))
        return cert(library,'invariant_interval_for_increasing_iterates',dict(converges=True,limit=R,invariant=(ZERO,R)),
                    'Находим положительную неподвижную точку, решая R²−R−c=0. Возрастающая карта sqrt(c+x) переводит [0,R] в себя.',
                    'Первый шаг растёт, и возрастание сохраняется. Предел существует и по непрерывности совпадает с единственной неотрицательной неподвижной точкой.',
                    map_constant=q(c),initial=('sqrt',q(c)))
    if kind=='positive_Newton_recurrence_limit':
        g,given=packet(task,'initial','recurrence','target_limit')
        p=re.fullmatch(r'x\[n\+1\]=\(x\[n\]\+(.+)/x\[n\]\)/2 for n>=0',g['recurrence'])
        need(p and not given and g['initial']=='x[0]>0' and task.get('index_domain')=='nonnegative_integers',
             'The original positive seed and real iteration must be preserved')
        c=rational(p[1]);root=m.simplify(('sqrt',q(c)))
        need(c>0 and same(root,m.parse(g['target_limit'],None)),'The fixed point must be the claimed positive radical')
        return cert(library,'derive_root_iteration_by_invariant_and_monotonicity',root,
                    'Вычитание положительного корня даёт точный квадрат ошибки, делённый на 2x. Все члены после первого шага не меньше корня.',
                    'На этом хвосте разность соседних членов неположительна. Подставляем положительный предел в исходную итерацию и получаем его квадрат.',
                    radicand=q(c),first_invariant_index=1)
    g,given=packet(task,'initial','recurrence','goal')
    rc=re.fullmatch(r'x\[n\]=(.+) for n>=3',g['recurrence'])
    need(rc and set(g['initial'])=={'x[1]','x[2]'} and g['goal']=='compute limit'
         and task.get('index_domain')=='positive_integers','A two-step recurrence starting at n=3 and both seeds are required')
    a,b=(g['initial'][k] for k in ('x[1]','x[2]'))
    need(a!=b and re.fullmatch(NAME,a) and re.fullmatch(NAME,b) and given==[f'{a},{b} are fixed real numbers'],
         'The original initial data are not two independent fixed real values')
    left,right=('s','older'),('s','last')
    text=rc[1].replace('x[n-1]','last').replace('x[n-2]','older')
    expr=m.parse(text,None,['older','last']);num,den=m.rational_form(expr)
    need(den=={():Fraction(1)} and set(num)=={((left,1),),((right,1),)},
         'The original iteration must be a linear combination with two independent previous values')
    h,j=num[((left,1),)],num[((right,1),)]
    need(h+j==1 and 0<h<1,'Only a strict convex two-step average gives the required contraction')
    limit=m.mul(q(1/(1+h)),m.add(('s',b),m.mul(q(h),('s',a))))
    return cert(library,'derive_two_step_average_invariant',limit,
                'Вычитаем предыдущий член: соседняя разность умножается на отрицательный коэффициент при старшем из двух прошлых членов.',
                'Геометрическая сумма разностей сходится. Линейное выражение x_n+h x_{n−1} проверяется подстановкой как инвариант, оно определяет единственный предел.',
                weights=(q(j),q(h)),difference_ratio=q(-h),invariant=m.add(('s',b),m.mul(q(h),('s',a))))


PREFIX={'monotone_bounded_convergence','eventually_monotone_bounded_convergence','cauchy_sequence_convergence'}
RECURSIONS={'recursive_monotone_bounded_convergence','positive_Newton_recurrence_limit','linear_recurrence_limit'}


def exponential_bracket(task,library):
    kind=task.get('kind',task.get('task_type'))
    if kind=='arbitrary_sequence_composition_limit':
        g,given=packet(task,'index_sequences','targets')
        need(given==[NATURAL,'p[n],q[n] are real','p[n],q[n] not in[-1,0]'] and
             g['index_sequences']=={'p':'p[n]->+inf','q':'q[n]->-inf'} and
             g['targets']==['(1+1/p[n])^p[n] ->e','(1+1/q[n])^q[n] ->e'],
             'Both directed source tails and the real bases must be specified')
        return cert(library,'transport_reciprocal_exponential_limit_to_sequences',dict(positive_end=('exp',ONE),negative_end=('exp',ONE)),
                    'Для t вне [−1,0] основание положительно. Логарифм исходной степени равен ln(1+u)/u при u=1/t.',
                    'Оба исходных направления переходят в разные стороны нуля. С каждой стороны логарифмическое отношение стремится к единице.')
    if kind=='monotone_bounded_common_limit':
        g,given=packet(task,'sequences','goals')
        need(given==[NATURAL] and g['sequences']=={'x':'(1+1/n)^n','y':'(1+1/n)^(n+1)'} and
             g['goals']==['x strictly increasing','x bounded above','y strictly decreasing','y bounded below','common limit e'],
             'Both complete source sequences and all their bound goals must be present')
        return cert(library,'bracket_exponential_with_monotone_approximations',
                    dict(lower_increases=True,upper_decreases=True,common_limit=('exp',ONE)),
                    'По Бернулли (1+1/(n+1))(1−1/(n+1)^2)^n>1. Это отношение соседних членов нижней последовательности.',
                    'Для верхней последовательности обратное отношение равно ((n+1)^2/(n(n+2)))^(n+1)·(n+1)/(n+2)>1 снова по Бернулли.',
                    'Обе ограничены друг другом, а разность x_n/n≤y_1/n исчезает. Их общий предел задаёт e.',
                    gap_bound='upper_first_term/n')
    if kind=='factorial_two_sided_bound':
        g,given=packet(task,'proposition')
        need(given==[NATURAL] and g['proposition']=='(n/e)^n<factorial(n)<e*(n/2)^n',
             'Both original strict estimates for the full factorial are required')
        return cert(library,'bound_factorial_by_log_integral_and_arithmetic_mean',dict(holds=True),
                    'При n>1 сумма логарифмов строго больше интеграла ln t от 1 до n. Случай n=1 проверяется непосредственно.',
                    'По неравенству средних произведение не больше ((n+1)/2)^n. После отделения (n/2)^n второй множитель строго меньше e.')
    g,given=packet(task,'sequence','target','bound','desired_absolute_error','question')
    need(given==[NATURAL] and g['sequence']=='(1+1/n)^n' and g['target']=='e' and g['bound']=='0<e-x[n]<3/n'
         and g['question']=='integer index range guaranteeing desired error','The source Euler bound or requested integer range is unbound')
    epsilon=rational(g['desired_absolute_error']);need(epsilon>0,'The error tolerance is positive')
    hi=max(1,ceil(3/epsilon));lo=0
    need(hi<=20_000,'The exact integer threshold needs a larger comparison backend')
    def below(k):
        value=Fraction((k+1)**k,k**k)
        for j in (12,20,32):
            low,high=factorial_bracket(j)
            if high-value<epsilon:return True
            if low-value>=epsilon:return False
        raise Unsupported('The rational e enclosure cannot distinguish the threshold')
    while hi-lo>1:
        k=(hi+lo)//2
        if below(k):hi=k
        else:lo=k
    need(below(hi) and (not lo or not below(lo)),'The consecutive exact index bounds must both be verified')
    return cert(library,'find_sharp_integer_threshold_in_monotone_error',
                dict(strict_uniform_bound='0<e-x[n]<3/n',least_integer_n=hi,index_predicate=('n>=',hi)),
                'Верхняя экспоненциальная скобка даёт 0<e−x_n<x_n/n<3/n.',
                'Ошибка убывает. Рациональными факториальными границами e проверяем два соседних индекса и получаем точный порог.',
                tolerance=q(epsilon),threshold_checks=(lo,hi))


def factorial_bracket(n):
    s=sum(Fraction(1,factorial(k)) for k in range(n+1))
    return s,s+Fraction(1,n*factorial(n))


def exponential_factorial_tail(task,library):
    kind=task.get('kind',task.get('task_type'))
    if kind=='irrationality_proof':
        g,given=packet(task,'proposition')
        need(given==[NATURAL] and g['proposition']=='e is irrational','The rational contradiction concerns the admitted factorial series')
        return cert(library,'multiply_factorial_series_by_denominator',dict(irrational=True),
                    'Предполагаем e=p/q и берём n≥q. Тогда n!e целое, как и конечная часть его факториального ряда после умножения.',
                    'Разность этих целых строго положительна, а строгое ограничение факториального хвоста даёт величину меньше 1/n≤1.')
    g,given=packet(task,'initial_fact','goals')
    need(given==[NATURAL] and g['initial_fact']=='Euler sequence limit is e' and len(g['goals'])==3 and
         g['goals'][:2]==['factorial partial sums tend to e','strict remainder0<R[n]<1/(n!*n)'],
         'The factorial limit, exact remainder and approximation must all be covered')
    precision=re.fullmatch(r'compute e with absolute error below(.+)',g['goals'][2])
    need(precision,'The desired approximation accuracy is missing')
    epsilon=rational(precision[1]);need(epsilon>0,'A positive precision is required')
    for n in range(1,100):
        low,high=factorial_bracket(n)
        if high-low<epsilon:break
    else:raise Unsupported('The desired precision needs more factorial terms')
    return cert(library,'derive_factorial_series_and_bound_exact_tail',
                dict(limit=('exp',ONE),remainder='0<R[n]<1/(n!*n)',approximation=q(low),
                     enclosure=(q(low),q(high)),finite_order=n),
                'В биноме (1+1/n)^n при фиксированном k коэффициент стремится к 1/k!. Каждый коэффициент не больше 1/k!, и факториальный мажорирующий хвост мал.',
                'Берём сначала конечную часть в пределе, затем уменьшаем хвост. После порядка n факториальный остаток строго меньше положительного геометрического хвоста 1/(n! n).',
                precision=q(epsilon))


def finite_cut_or_atom(task,library):
    kind=task.get('kind',task.get('task_type'))
    if kind=='mathematical_question':
        goal=task['goal']
        if goal.get('function')=='sgn':
            g,given=packet(task,'function','pieces','goals')
            need(not given and g['pieces']==[['x<0',-1],['x=0',0],['x>0',1]]
                 and g['goals']==['prove abs(x)=x*sgn(x) for all real x'],'The original sign branches must cover the identity')
            return cert(library,'verify_sign_identity_by_exhaustive_real_branches',dict(holds=True,branches=g['pieces']),
                        'На отрицательной, нулевой и положительной ветви исходное произведение равно соответственно −x, 0 и x. Это определение модуля.')
        g,given=packet(task,'variable','variable_space','distributed_mass','atoms','interval','goals')
        var=g['variable'];x=('v',var)
        need(not given and g['variable_space']=='real_numbers' and g['interval']=='(-infinity,'+var+')'
             and g['goals']==['exact mass function'],'The original strict upper endpoint and mathematical mass output must be retained')
        mass=g['distributed_mass'];support=re.fullmatch(r'\[(.+),(.+)\]',mass['support'])
        need(set(mass)=={'support','total_grams','uniform'} and support and mass['uniform'] is True,
             'The continuous mass must be uniform on a finite connected interval')
        a,b=map(rational,support.groups());u=rational(mass['total_grams'])
        need(b>a and u>=0,'A positive-length interval and nonnegative mass are required')
        continuous=m.mul(q(u/(b-a)),('max',ZERO,m.add(('min',x,q(b)),q(-a))))
        atoms=[]
        for row in g['atoms']:
            location,weight=(rational(row[k]) for k in ('position','mass_grams'))
            need(weight>=0 and set(row)=={'position','mass_grams'},'Unbound atom data')
            atoms.append(dict(position=q(location),weight=q(weight),condition=('less',q(location),x)))
        return cert(library,'integrate_uniform_density_and_strict_atoms',dict(continuous=continuous,atoms=atoms,addition=True),
                    'Пересечение исходного полуинтервала с отрезком плотности даёт длину, умноженную на постоянную плотность.',
                    'Атом включается только если его координата строго меньше верхней границы. Суммируем независимо все вклады.',
                    original_interval=g['interval'])
    if kind=='set_extrema_and_bounds':
        g,given=packet(task,'set','goals')
        need(not given and g['set']=='{m/n:m,n positive integers,0<m<n}' and g['goals']==[
             'no minimum','no maximum','infimum','supremum'],'The original proper fraction domain and four outputs must be explicit')
        return cert(library,'approximate_both_open_ends_on_rational_grid',
                    dict(infimum=ZERO,supremum=ONE,minimum_attained=False,maximum_attained=False),
                    'На каждом знаменателе n≥2 первый и последний допустимые кратные равны 1/n и 1−1/n. Эти значения приближают оба исключённых конца.')
    g,given=packet(task,'set','goals');match=re.fullmatch(r'\{r in Q:r\^2<(.+)\}',g['set'])
    need(not given and match and g['goals']==['infimum','supremum'],'A bounded rational quadratic set with both requested edges is needed')
    c=rational(match[1]);need(c>0,'The open quadratic interval must be nonempty')
    right=m.simplify(('sqrt',q(c)))
    return cert(library,'density_attains_open_rational_bounds_as_limits',
                dict(infimum=m.neg(right),supremum=right,attained=False),
                'Строгое квадратное неравенство даёт открытый симметричный интервал. Плотность рациональных обеспечивает произвольную близость к обоим концам изнутри.',
                interval=(m.neg(right),right))


def review_printed_scope(task,library):
    kind=task.get('kind',task.get('task_type'))
    if kind=='prove_cut_nonattainment':
        g,given=packet(task,'sets','proposition')
        need(given==['c is a positive real number','c is not the square of an integer'] and
             g['sets']=={'B':'{b in Q:b>0 and b^2>c}','A':'Q\\B'} and g['proposition']=='A has no maximum and B has no minimum',
             'The given class must retain the literal exclusion of integer squares only')
        return cert(library,'disprove_nonattainment_by_exact_rational_square',
                    dict(printed_claim_holds=False,counterexample=dict(c=q(1,4),maximum_A=q(1,2),minimum_B_exists=False)),
                    'Положительное c=1/4 не является квадратом целого. Положительные рациональные с квадратом больше c — ровно числа больше 1/2.',
                    'Значит 1/2 принадлежит A и превосходит или равняется каждому элементу A, опровергая отсутствие максимума.')
    if kind=='limsup_product_with_convergent_factor':
        g,given=packet(task,'hypothesis','proposition')
        need(task.get('index_domain')=='positive_integers' and given==['x[n]>=0'] and g=={
             'hypothesis':'limit x[n] exists','proposition':'limsup(x*y)=limit(x)*limsup(y)'},
             'The printed unrestricted second factor and vanishing first factor must be admissible')
        return cert(library,'disprove_unrestricted_envelope_product_by_equal_input_limits',
                    dict(printed_claim_holds=False,counterexample=dict(y='n',first_sequences=['1/n','1/n^2'],
                         both_factor_limits=ZERO,both_y_envelopes='+inf',product_envelopes=[ONE,ZERO])),
                    'Оба положительных первых множителя 1/n и 1/n² стремятся к нулю. Второй множитель n имеет верхний предел +∞.',
                    'В первом случае произведение равно 1, во втором стремится к 0. Одна величина, определённая только через 0 и +∞, не может равняться обоим результатам.')
    g,given=packet(task,'initial','recurrences','goal')
    need(task.get('index_domain')=='positive_integers' and given==['a,b are real'] and g['initial']=={'x[1]':'a','y[1]':'b'}
         and g['recurrences']==['x[n+1]=sqrt(x[n]*y[n])','y[n+1]=(x[n]+y[n])/2'] and g['goal']=='common finite limit',
         'The source two-variable iteration and unrestricted real seeds must be preserved')
    return cert(library,'disprove_unrestricted_iteration_by_early_domain_failure',
                dict(printed_claim_holds=False,counterexample=dict(a=q(-1),b=q(-1),x2=ONE,y2=q(-1),
                     first_undefined='x[3]',radicand=q(-1))),
                'При обоих начальных значениях −1 первая пара обновлений даёт x₂=1, y₂=−1. Следующий квадратный корень имеет отрицательный аргумент.',
                'Таким образом, исходные вещественные последовательности могут не продолжиться до третьего члена.')


EXP_BRACKETS={'monotone_bounded_common_limit','error_bound_and_integer_threshold','arbitrary_sequence_composition_limit',
              'factorial_two_sided_bound'}
EXP_FACTORIAL={'series_limit_remainder_and_evaluation','irrationality_proof'}
CUTS={'set_extrema_and_bounds','set_bounds'}
REFUTATIONS={'prove_cut_nonattainment','limsup_product_with_convergent_factor','coupled_AGM_recurrence'}


WITNESS_GOALS={'triangular_array_cluster_set','construct_sequence_example','convergence_case_analysis',
               'counterexample_to_limit_inference'}


def finite_ladder_argument(task,library,kind):
    if kind=='induction_with_corollary':
        g,given=packet(task,'definition','proposition','further_goal')
        declaration=re.fullmatch(r'([A-Za-z_]\w*)\(a,h,n\)=product\(j,0,n-1,a-j\*h\); \1\(a,h,0\)=1',
                                 g['definition'])
        need(given==['n is a nonnegative integer','a,b,h are fixed real numbers'] and declaration,
             'Bind the original real ladder step and nonnegative degree')
        f=declaration[1];method='pascal_convolution_of_falling_ladders'
        need(g['proposition']==f'{f}(a+b,h,n)=sum(m,0,n,binom(n,m)*{f}(a,h,n-m)*{f}(b,h,m))'
             and g['further_goal']=='derive Newton binomial formula',
             'The original convolution and its Newton specialization are required')
        a,b,h,n,k=(('s',v) for v in ('a','b','h','n','m'))
        total=m.add(m.add(a,b),m.neg(m.mul(n,h)))
        shift_a=m.add(a,m.neg(m.mul(m.add(n,m.neg(k)),h)))
        shift_b=m.add(b,m.neg(m.mul(k,h)))
        need(same(total,m.add(shift_a,shift_b)),'The carrying factor must split at each summand')
        return cert(library,method,dict(proved=True,corollary='(a+b)^n = sum(m,0,n,binom(n,m)*a^(n-m)*b^m)'),
                    'При n=0 обе стороны равны 1 по пустому произведению.',
                    'Умножаем равенство для n на a+b−nh и внутри m-го слагаемого разбиваем этот множитель на a−(n−m)h и b−mh. Это удлиняет ровно одну из двух лестниц.',
                    'Переиндексируем вторую сумму и складываем коэффициенты по формуле Паскаля, включая оба крайних члена. Получаем равенство для n+1.',
                    'При h=0 каждая лестница становится обычной степенью. Получаем биномиальную формулу Ньютона.',
                    shift_factors=[total,shift_a,shift_b],required_method='induction')
    g,given=packet(task,'expression','target_limit')
    rhs=re.fullmatch(r'product\(([A-Za-z])\s*,\s*1\s*,\s*n\s*,\s*(.+)\)',g['expression'])
    need(given==[NATURAL] and rhs and g['target_limit']=='0','The original positive-index product and limit are required')
    j=('s',rhs[1]);factor=m.parse(rhs[2],None,[rhs[1]])
    need(factor[0]=='div','The original ratio must admit a direct bound on both affine terms')
    from tasks import domain_conditions
    p,den1=m.rational_form(factor[1]);d,den2=m.rational_form(factor[2]);linear=((j,1),)
    need(den1==den2=={():Fraction(1)} and not any(domain_conditions(t,True) for t in factor[1:]),
         'The affine terms must have no hidden domain restrictions')
    slope=p.get(linear,0);offset=p.get((),0)
    need(slope>0 and d.get(linear)==slope and set(p)|set(d)<={(),linear}
         and d.get((),0)-offset==slope/2 and offset+slope>0,
         'The numerator and positive denominator must be neighboring terms on a half-step lattice')
    a=m.add(m.mul(q(slope),j),q(offset));h=q(slope/2);c=m.add(a,h);b=m.add(c,h)
    need(same(m.add(m.power(c,2),m.neg(m.mul(a,b))),m.power(h,2)),'The product comparison failed')
    return cert(library,'positive_product_by_squared_telescoping',dict(limit=ZERO),
                'Обозначаем числитель через A, знаменатель через A+h, а следующий числитель через A+2h. Все три положительны.',
                'Из (A+h)²−A(A+2h)=h² следует (A/(A+h))²≤A/(A+2h). Перемножаем эти оценки и сокращаем соседние положительные множители.',
                'Квадрат искомого произведения зажат между нулём и первым числителем, делённым на следующий за последним. Эта дробь стремится к нулю.',
                factor=factor,initial_numerator=q(offset+slope),comparison_denominator_at_successor=b)


def scale_cluster_set(task,library,request):
    g,given=packet(task,'sequences','goal')
    rows=g['sequences']
    need(isinstance(rows,dict) and set(rows)=={'x','y'} and rows['x']=='arbitrary real x[n]'
         and g['goal']=='same finite and infinite cluster limits' and not given
         and task.get('index_domain')=='positive_integers','Bind the two real sequences on the original positive lattice')
    hit=re.fullmatch(r'x\[n\]\*n\^\(([^()/]+)/n\)',rows['y'])
    need(hit,'The original scaling factor is not a checked positive power of the index')
    coefficient=rational(hit[1]);query=dict(kind='limit',variable='n',variable_domain='positive_integers',
           expression=f'({coefficient})*ln(n)/n',approach={'point':'+inf','side':'positive_infinity'})
    from model import freeze
    need(freeze(request('logarithm of the positive scaling factor',query)['value'])==ZERO,
         'The original positive factor must tend to one')
    return cert(library,'cluster_set_under_unit_scaling',dict(same_finite_and_infinite_limits=True),
                'Индекс положителен, поэтому множитель положителен. Его логарифм стремится к нулю, а сам множитель и обратный ему стремятся к единице.',
                'Вдоль любой сходящейся подпоследовательности умножение на положительный множитель с пределом 1 сохраняет конечный или бесконечный предел. Обратный множитель даёт включение в другую сторону.',
                scale_numerator=q(coefficient))


def alternating_product_witness(task,library):
    from finite_sums import periodic_phases
    from tasks import domain_conditions,known_guard
    g,given=packet(task,'hypothesis','question','source_examples')
    need(task.get('index_domain')=='positive_integers' and not given and g['hypothesis']=='x[n]*y[n]->0'
         and g['question']=='must x[n]->0 or y[n]->0?','The source proposes an inference from a zero product limit')
    a,b=(m.parse(t,'n') for t in g['source_examples']);ctx=m.context(dict(variable='n'))
    profiles=[]
    for e in (a,b):
        phases=periodic_phases(e,'n')
        need(all(atom[0]=='rpow' and period in (1,2) for atom,(_,_,period) in phases.items()),
             'Only exact alternating integer phases are admitted')
        values=[]
        for residue in (0,1):
            mapping={atom:q((-1)**int((offset+slope*residue)%2)) for atom,(offset,slope,_) in phases.items()}
            branch=m.substitute(e,mapping)
            need(all(known_guard(g,ctx) for g in domain_conditions(branch,True)),'A residue branch retains an undefined expression')
            value=m.num(m.simplify(branch));need(value is not None,'A parity branch is not exactly constant')
            values.append(q(value))
        profiles.append(values)
    x,y=profiles
    need(x[0]!=x[1] and y[0]!=y[1] and all(m.mul(u,v)==ZERO for u,v in zip(x,y)),
         'The source examples must both diverge while their product is identically zero')
    return dict(theorem='method.search_verified_rational_sequence_profiles',argument=[
        'Подставляем чётный и нечётный индекс в исходные выражения. На двух классах получаются две различные константы у каждого множителя.',
        'На каждом классе произведение равно нулю. Следовательно, ни один из расходящихся множителей не обязан стремиться к нулю.']),dict(
        inference_holds=False,residue_values=profiles,product_limit=ZERO)


PROGRESSION_MAPS={'arithmetic_progression_under_affine_map','geometric_progression_under_exponential_map'}


def transport_progression(task,library,kind):
    from integrals import affine
    from tasks import domain_conditions,known_guard
    g,given=packet(task,'definition','hypothesis','conclusion')
    defn=re.fullmatch(r'f\(x\)=(.+)',g['definition'])
    need(defn and g['hypothesis']=='x[n+1]-x[n]=d is constant','Bind the constant step of the original progression')
    params=names(defn[1],'x');need('d' not in params,'The symbol d already denotes the progression step')
    raw=m.parse(defn[1],'x',params);ctx=m.context(dict(variable='x',parameters=params,parameter_conditions=given))
    step=('s','d')
    if kind=='arithmetic_progression_under_affine_map':
        need(not given and g['conclusion']=='y[n+1]-y[n] is constant','The original affine conclusion is about differences')
        slope,offset=affine(raw,'x')
        need(all(known_guard(c,ctx) for c in domain_conditions(raw,True)),'The source affine function has a hole')
        term=('s','__value');x=('v','x')
        difference=m.add(m.substitute(raw,{x:m.add(term,step)}),m.neg(m.substitute(raw,{x:term})))
        result=m.mul(slope,step)
        need(same(difference,result),'The original difference does not reduce to the slope times the step')
        return cert(library,'transport_fixed_steps_through_elementary_maps',dict(common_difference=result),
                    'Подставляем соседние аргументы u+d и u. Свободный член сокращается, и разность равна произведению наклона на постоянный шаг.',
                    slope=slope,offset=offset)
    need(raw[0]=='rpow' and raw[2]==('v','x') and g['conclusion']=='y[n+1]/y[n] is constant',
         'The source conclusion must use the quotient of a fixed-base exponential')
    base=raw[1];need(m.constant_defined(base,ctx) and m.sign(base,ctx)==1,'The real exponential has a strictly positive base')
    return cert(library,'transport_fixed_steps_through_elementary_maps',dict(common_ratio=('rpow',base,step)),
                'Положительное основание даёт ненулевые значения обеих степеней. В их отношении показатели вычитаются, поэтому отношение равно степени с постоянным показателем d.',
                original_base=base)


def affine_interval_data(task):
    from integrals import affine
    from tasks import domain_conditions,known_guard
    g,given=packet(task,'variable','expression','given_domain','goal');var=g['variable']
    params=names(g['expression'],var)
    hit=re.fullmatch(r'([\[(])([^,]+),([^,]+)([\])])',g['given_domain'])
    need(params and not given and hit and g['goal']=='exact image','Need an affine map of a given finite interval')
    a,b=map(rational,hit.groups()[1:3]);raw=m.parse(g['expression'],var,params)
    ctx=m.context(dict(variable=var,parameters=params));slope,offset=affine(raw,var)
    need(a<b and all(known_guard(c,ctx) for c in domain_conditions(raw,True)),
         'The original finite interval must be ordered and free of holes')
    return slope,offset,q(a),q(b),hit[1]=='[',hit[4]==']'


def affine_interval_image(task,library):
    slope,offset,a,b,lclosed,rclosed=affine_interval_data(task)
    left,right=[m.simplify(m.add(m.mul(slope,t),offset)) for t in (a,b)]
    return cert(library,'affine_interval_image_with_unknown_slope',dict(slope=slope,
         when_positive=(left,right,lclosed,rclosed),when_negative=(right,left,rclosed,lclosed),when_zero=(offset,)),
         'Подставляем оба исходных края. При положительном наклоне порядок и принадлежность концов сохраняются, при отрицательном меняются местами.',
         'При ненулевом наклоне решение аффинного уравнения даёт прообраз каждой внутренней точки. При нулевом наклоне весь непустой интервал отображается в одну точку.')


def inscribed_scaled_power(task,library,request):
    from model import freeze
    g,given=packet(task,'figure','curve','boundaries','required_method','goals')
    match=re.fullmatch(r'y=([A-Za-z]+)\*\(x/([A-Za-z]+)\)\^([1-9]\d*)',g['curve'])
    need(match and g['boundaries']==['Ox','x='+match[2]] and
         g['required_method']==f'limit of inscribed rectangles of width {match[2]}/n' and
         g['goals']==['construct the inscribed area sums','take their limit','justify that it is the required area'],
         'The original positive-length region and inscribed method must be retained')
    amplitude,length,degree=match.groups();degree=int(degree)
    stated_dimensions=set(given)=={amplitude+'>0',length+'>0'}
    source_dimensions=(not given and g['figure'].startswith('source figure') and
                       'площадь криволинейного треугольника' in task.get('source_statement',''))
    need(len({amplitude,length,'x','n'})==4 and degree<=16 and (stated_dimensions or source_dimensions),
         'Bind distinct positive scales and supported power')
    result=request('power sum limit on the unit interval',dict(kind='riemann_integral_by_definition',variable='u',
        function=f'u^{degree}',interval=['0','1'],requested_output=['partition','riemann_sum','limit_and_integral']))
    value=freeze(result['value']['integral']);scale=m.mul(('s',length),('s',amplitude))
    return cert(library,'inscribed_samples_from_monotone_scaled_power',dict(area=m.mul(scale,value),
                inscribed_sum=dict(scale=scale,degree=degree,index='j=0..n-1',normalization=f'n^(-{degree+1})')),
                'Исходные длина основания и высота положительны. Нормированная степень непрерывна и возрастает, поэтому вписанные прямоугольники используют левые концы.',
                'У правой суммы и левой суммы все внутренние слагаемые одинаковы. Разность равна произведению двух масштабов, делённому на n, и стремится к нулю.',
                'Переносим отдельно доказанный предел правой суммы на левую. График непрерывной высоты лежит между обеими ступенчатыми фигурами.')


def rational_power_cut(task,library):
    g,given=packet(task,'object','construction')
    hit=re.fullmatch(r'([^()^]+)\^sqrt\(([^()]+)\)',g['object'])
    need(not given and hit and g['construction']=='Dedekind cut of rational numbers',
         'The requested cut must bind the positive rational base and square root')
    b,d=map(rational,hit.groups())
    need(b>1 and d>0,'Monotone real exponentiation requires base greater than one and a positive radicand')
    above=1+isqrt(d.numerator//d.denominator)
    return cert(library,'rational_comparisons_for_power_cut',dict(base=q(b),radicand=q(d),
                lower_class=dict(nonpositive_rationals=True,positive_rationals_test='exists integers p,q>0: p^2<d*q^2 and r^q<b^p'),
                upper_class='the complement in the rationals',upper_witness=('pow',q(b),above)),
                'В нижний класс помещаем все неположительные рациональные. При r>0 проверяем существование положительных целых p,q с p²<dq² и r^q<b^p.',
                'Класс замкнут вниз и собственный: для целого m>√d число b^m не проходит тест. У каждого положительного элемента есть больший рациональный элемент между ним и корнем степени q из b^p. Для неположительного элемента можно взять 1.',
                'Рациональные p/q при p²<dq² плотны снизу у √d. Возрастание и непрерывность показательной функции доказывают, что граница сечения равна b^√d.')


def symmetric_power_addition(task,library):
    from integrals import affine
    g,given=packet(task,'definition','proposition')
    prefix=re.fullmatch(r'f\(x\)=(.+)',g['definition'])
    need(prefix and g['proposition']=='f(x+y)+f(x-y)=2*f(x)*f(y)' and 'x,y real' in given,
         'Bind the original addition identity and its two real arguments')
    params=names(prefix[1],'x');raw=m.parse(prefix[1],'x',params);ctx=m.context(dict(variable='x',parameters=params,
                                                                        parameter_conditions=[c for c in given if c!='x,y real']))
    net,den=m.rational_form(raw)
    terms=[(mon,c/den[()]) for mon,c in net.items()] if set(den)=={()} else []
    need(len(terms)==2 and all(len(mon)==1 and mon[0][1]==1 and mon[0][0][0]=='rpow' and c==Fraction(1,2)
                               for mon,c in terms),'The function needs two equally weighted real exponential terms')
    u,v=[mon[0][0] for mon,_ in terms]
    need(same(u[1],v[1]) and m.constant_defined(u[1],ctx) and m.sign(u[1],ctx)==1 and same(u[2],m.neg(v[2])),
         'The powers must use one positive base and opposite exponents')
    from tasks import domain_conditions,known_guard
    need(all(known_guard(c,ctx) for c in domain_conditions(raw,True)),
         'No hidden restriction may be removed while collecting the original powers')
    slope,shift=affine(u[2],'x')
    need(shift==ZERO and m.constant_defined(slope,ctx),'An additive real exponent is required')
    P,Q=('s','P'),('s','Q')
    def sym(a):return m.mul(q(1,2),m.add(a,m.div(ONE,a)))
    left=m.add(sym(m.mul(P,Q)),sym(m.div(P,Q)));right=m.mul(q(2),m.mul(sym(P),sym(Q)))
    need(same(left,right),'The original addition law did not give the same Laurent expressions')
    return cert(library,'symmetric_addition_by_multiplicative_coordinates',dict(proved=True),
                'Выбираем положительные координаты P и Q как значения одной показательной функции в двух аргументах. Сумме и разности аргументов соответствуют PQ и P/Q.',
                'Раскрываем два проверенных выражения. Совпадают коэффициенты при PQ, P/Q, Q/P и 1/(PQ). Делители ненулевые по положительности исходной степени.',
                base=u[1],exponent_slope=slope,transformed_left=left,transformed_right=right)


def planar_metric_model(task,library,request):
    g,given=packet(task,'model','data','variable','goals');data=g['data'];var=g['variable'];x=('s',var)
    model=g['model'];want=g['goals']
    need(isinstance(var,str) and var.isidentifier() and isinstance(data,dict),'The model must bind one variable and its geometric data')
    from geometric_domains import plus,times,diff,root,triangle_section_width
    if model=='triangle_parallel_section':
        need(set(data)=={'base','altitude','altitude_foot_on_base'} and data['altitude_foot_on_base'] is True
             and want==['perimeter','area'],'An inscribed rectangle needs its parallel section and a foot on the base')
        b,h=[data[k] for k in ('base','altitude')]
        need(all(isinstance(v,str) and v.isidentifier() for v in (b,h)) and len({b,h,var})==3
             and set(given)=={b+'>0',h+'>0'},'The original base and altitude must be positive and fixed')
        B,H=('s',b),('s',h);width=triangle_section_width(B,H,x)
        return cert(library,'affine_sections_by_similarity',dict(domain=f'0<{var}<{h}',width=width,
                    perimeter=times(q(2),plus(width,x)),area=times(width,x),endpoints='degenerate limiting rectangles'),
                    'На высоте x подобный верхний треугольник имеет высоту h−x. Гомотетия с центром в вершине даёт ширину сечения b(1−x/h).',
                    'Проекция сечения остаётся на основании. С этой шириной и заданной высотой вычисляются периметр и площадь.')
    if model=='isosceles_trapezoid_upper_side_cut':
        need(set(data)=={'lower_base','upper_base','altitude'} and want==['left_cut_area'],
             'A vertical cut through the upper side fixes the left part of a symmetric trapezoid')
        a,b,h=[data[k] for k in ('lower_base','upper_base','altitude')]
        need(all(isinstance(v,str) and v.isidentifier() for v in (a,b,h)) and len({a,b,h,var})==4
             and set(given)=={a+'>'+b,b+'>0',h+'>0'},'Bind both positive bases and the positive altitude')
        A,B,H=('s',a),('s',b),('s',h);overhang=times(q(1,2),diff(A,B))
        return cert(library,'affine_sections_by_similarity',dict(cut_domain=(overhang,plus(overhang,B),True,True),
                    area=times(H,diff(x,times(q(1,2),overhang)))),
                    'Два равных выступа нижнего основания имеют длину половины разности оснований. Вертикаль через верхнюю сторону находится между проекциями её концов.',
                    'Слева от вертикали складываем площадь бокового треугольника и площадь прямоугольника над отрезком от левой проекции до вертикали.')
    if model=='triangle_included_angle':
        need(set(data)=={'adjacent_sides','length_unit'} and not given and want==['opposite_side','area'],
             'Need the two sides and their included angle with a common length unit')
        l,r=map(rational,data['adjacent_sides']);unit=data['length_unit']
        need(l>0 and r>0 and isinstance(unit,str) and unit,'The two adjacent lengths are positive')
        w=plus(q(l*l+r*r),times(q(-2*l*r),('cos',x)))
        return cert(library,'triangle_metrics_from_included_angle',dict(angle_domain=(ZERO,m.PI,False,False),
                    opposite_side=root(w),area=times(q(l*r/2),('sin',x)),length_unit=unit,area_unit=unit+'²'),
                    'Применяем теорему косинусов к двум сторонам с данным углом. Берём положительный корень для длины.',
                    'Высота относительно одной стороны равна другой стороне, умноженной на синус угла. В невырожденном треугольнике угол строго между 0 и π.')
    if model=='uniform_motion_1d':
        need(set(data)=={'positions','velocities','units','time_domain'} and not given and
             data['time_domain']=='nonnegative' and want==['motion_equations','meeting_time_and_coordinate'],
             'The two signed velocities and the original future time domain are required')
        a,b=map(rational,data['positions']);u,v=map(rational,data['velocities']);units=data['units']
        need(units=={'position':'m','time':'s','velocity':'m/s'},'The coordinate, time and velocity units must agree')
        equations=[plus(q(pos),times(q(vel),x)) for pos,vel in ((a,u),(b,v))]
        meeting='none'
        if u==v:
            if a==b:meeting='all nonnegative times'
        else:
            t=(b-a)/(u-v)
            if t>=0:meeting=dict(time=q(t),position=q(a+u*t))
        return cert(library,'affine_relative_motion_meeting',dict(equations=equations,meeting=meeting,units=units),
                    'К начальной координате прибавляем произведение знаковой скорости на время. Приравниваем полученные координаты и оставляем только время в исходной области.',
                    'При одинаковых скоростях совпадение зависит только от начальных координат. При разных скоростях относительная координата имеет не более одного нуля.')
    need(model=='projectile_same_level' and set(data)=={'speed','angle_degrees','gravity','no_drag'} and
         data['no_drag'] is True and not given and want==['maximum_height','horizontal_range'],
         'Need the no-drag model, launch and gravity data, and return to launch level')
    v,angle,gravity=[rational(data[k]) for k in ('speed','angle_degrees','gravity')]
    need(v>0 and gravity>0 and 0<angle<180,'The projectile must initially rise in positive constant gravity')
    child=dict(kind='motion_under_constant_gravity',initial_speed=str(v),launch_angle=f'({angle}/180)*pi',
        plane='vertical Oxy',gravity=True,no_drag=True,
        requested_output=['motion','velocity','acceleration','trajectory','maximum rise','range'])
    from model import freeze
    branches=request('motion chart for constant vertical gravity',child)['value']
    substitution={('s','g'):q(gravity)};rise=branches['upward_launch']
    peak,flight=[m.simplify(m.substitute(freeze(rise[k]),substitution)) for k in ('maximum_rise','flight_time')]
    u=freeze(branches['velocity'][0]);reach=times(u if angle<90 else m.neg(u) if angle>90 else ZERO,flight)
    return cert(library,'project_projectile_extrema_from_kinematic_chart',dict(maximum_height=peak,horizontal_range=reach,
                units='m with supplied gravity in m/s²'),
                'Угол лежит строго между 0 и 180 градусами, так что начальная вертикальная скорость положительна. Берём ветвь подъёма проверенной модели и подставляем исходное ускорение.',
                'Направление горизонтальной скорости следует из знака косинуса угла. Дальность равна модулю этой скорости, умноженному на проверенное время полёта.')


def sequence_witness(task,library,kind):
    """Search a bounded set of rational residue-class profiles, or construct a verified block grid."""
    need(library.data.get('rational_sequence_witnesses'),'No executable sequence witnesses')
    n=('v','n')
    if kind=='sequence_cluster_set' and 'sequence_by_blocks' in task['goal']:
        g,given=packet(task,'sequence_by_blocks','goal')
        hit=re.fullmatch(r'for ([a-z])=1,2,\.\.\. append\[([^,]+)\^\(-\1\),([^,]+)-\2\^\(-\1\)\]',
                         g['sequence_by_blocks'])
        need(hit and given==[NATURAL] and g['goal']=='all subsequential limits',
             'Bind both original geometric block branches and the positive index')
        ratio,center=map(rational,hit.groups()[1:])
        need(ratio>1,'A growing positive base is required for the two limits')
        return dict(theorem='method.subsequence_from_an_indexed_grid',argument=[
            'Разделяем последовательность на первые и вторые места каждого блока. Обратная геометрическая степень стремится к нулю, поэтому две части имеют указанные пределы.',
            'Любая бесконечная подпоследовательность содержит бесконечную часть одного из двух типов. Если она сходится, её предел совпадает с пределом этой части.'],
            block_formula=g['sequence_by_blocks']),dict(cluster_set=sorted({ZERO,q(center)},key=m.num))
    if kind=='triangular_array_cluster_set':
        g,given=packet(task,'sequence_by_blocks','goal')
        text=g['sequence_by_blocks']
        fractions=re.fullmatch(r'for ([a-z])=2,3,\.\.\. append\[(?:([1-9]\d*)\*)?([a-z])/\1 for \3=1\.\.\1-1\]',text)
        reciprocal=re.fullmatch(r'for ([a-z])=1,2,\.\.\. append\[1/\1\] then\[1/([a-z])\+1/\1 for \2=1\.\.\1-1\]',text)
        need(given==[NATURAL] and g['goal']=='all subsequential limits' and (fractions or reciprocal),
             'The exact source block enumeration is required')
        binder,j=(fractions[1],fractions[3]) if fractions else reciprocal.groups()
        scale=int(fractions[2] or '1') if fractions else 1
        need(binder!=j,'The two bound indices must be independent')
        if task.get('source_statement'):
            if fractions:
                blocks=[','.join(f'{scale*j0}/{k0}' for j0 in range(1,k0)) for k0 in range(2,6)]
                printed='Найти частичные пределы:'+';'.join(blocks)+';...'
            else:
                blocks=['1']+[','.join([f'1/{k0}']+[('1' if j0==1 else f'1/{j0}')+f'+1/{k0}' for j0 in range(1,k0)])
                              for k0 in range(2,4)]
                printed=('Найти частичные пределы последовательности блоков:'+';'.join(blocks)+
                         f';...;1/{binder},1+1/{binder},...,1/({binder}-1)+1/{binder};...')
            need(task['source_statement']==printed,'The displayed block contains a different start or order')
        if fractions:
            value=dict(cluster_interval=(ZERO,q(scale)))
            steps=['Вне первых конечных блоков знаменатели растут. Все точки лежат между нулём и максимальным масштабом.',
                   'Для любой точки этого отрезка в каждом достаточно позднем блоке выбираем ближайшую разрешённую дробь. Погрешность не больше масштаба, делённого на k.']
        else:
            value=dict(cluster_set='0 and reciprocals of positive integers')
            steps=['У каждой подпоследовательности из всё более поздних блоков добавок 1/k стремится к нулю.',
                   'Если вторые индексы уходят в бесконечность, остаётся ноль. Если некоторый конечный индекс повторяется бесконечно, получаем его обратную величину. Каждый такой предел достигается.']
        return dict(theorem='method.subsequence_from_an_indexed_grid',argument=steps,block_formula=text),value

    wanted=None
    if kind=='construct_sequence_example':
        g,given=packet(task,'required_property')
        properties={'не имеющей конечных частичных пределов':'no_finite_cluster',
                    'имеющей единственный конечный частичный предел, но не сходящейся':'one_finite_cluster_and_divergence',
                    'имеющей бесконечное множество частичных пределов':'infinitely_many_clusters',
                    'имеющей частичным пределом каждое вещественное число':'all_real_clusters'}
        property_text=g['required_property']
        if isinstance(property_text,dict) and set(property_text)=={'only_finite_cluster','diverges'} and property_text['diverges'] is True:
            wanted=q(rational(property_text['only_finite_cluster']))
            target='one_finite_cluster_and_divergence'
            need(not given and 'source_statement' not in task,'A formal specified cluster value needs exact source binding')
        else:
            target=properties.get(property_text) if isinstance(property_text,str) else None
            need(not given and target and task.get('source_statement') in (
                None,'Построить пример последовательности, '+property_text+'.'),
                'The requested original construction or its lattice has changed')
        if target in ('infinitely_many_clusters','all_real_clusters'):
            full=target=='all_real_clusters'
            interval='all real numbers' if full else '[0,1]'
            lo,hi=('-k^2','k^2') if full else ('0','k')
            return dict(theorem='method.subsequence_from_an_indexed_grid',
                        argument=['Строим конечные решётки j/k с уменьшающимся шагом.',
                                  'Для каждой заданной точки берём в каждом достаточно позднем блоке ближайшую дробь. Погрешность ≤1/k.'],
                        block_index='positive integer k',bound_index=('j',lo,hi)),dict(
                        formula='append j/k for every integer '+lo+' <= j <= '+hi+' in block k',cluster_set=interval)
    else:
        g,given=packet(task,'hypotheses','expression','question',exact=False)
        target=None
        f,d='x[n] converges finitely','x[n] does not converge finitely'
        y='y[n] does not converge finitely'
        operators={'x[n]+y[n]':'add','x[n]*y[n]':'mul'}
        mul=g.get('expression')=='x[n]*y[n]'
        if (kind=='convergence_case_analysis' and set(g)=={'hypotheses','expression'} and g['hypotheses']==[f,y]
                and g['expression'] in operators):
            target='maybe_product' if mul else 'divergent_sum'
            display='x_n сходится, y_n расходится. Что можно утверждать о сходимости '+('x_n*y_n' if mul else 'x_n+y_n')+'? Привести примеры.'
        elif (kind=='counterexample_to_limit_inference' and set(g)=={'hypotheses','expression','question'} and
                g['hypotheses']==[d,y] and g['expression'] in operators and g['question']=='must this diverge?'):
            target='finite_product' if mul else 'finite_sum'
            display='x_n и y_n расходятся. Можно ли утверждать, что '+g['expression']+' тоже расходится?'
        elif (kind=='counterexample_to_limit_inference' and g==dict(hypotheses=['x[n]->0','y[n] arbitrary real sequence'],
                                                                  question='must product tend to0?')):
            target='nonzero_product';display='x_n→0, y_n — произвольная последовательность. Можно ли утверждать x_n*y_n→0? Привести примеры.'
        else:raise Unsupported('The two original sequence hypotheses or requested operation remain unbound')
        need(not given and task.get('source_statement') in (None,display),'The displayed sequence hypotheses or conclusion differ')

    @lru_cache(maxsize=256)
    def limit(e):
        num,den=m.rational_form(e)
        if not num:return ZERO
        def lead(p):
            return max((mon[0][1] if mon else 0,c) for mon,c in p.items())
        (p,a),(r,b)=lead(num),lead(den)
        return ZERO if p<r else q(a/b) if p==r else '+inf' if a*b>0 else '-inf'

    def finite(values):return values[0]==values[1] and isinstance(values[0],tuple)

    base=tuple(dict.fromkeys((ZERO,ONE,q(-1),n,('div',ONE,n),m.neg(n))+((wanted,) if wanted is not None else ())))
    profiles=[(t,t) for t in base]+list(permutations(base,2))

    def witness(x,y=None,operation=None):
        xlim=tuple(map(limit,x));result=dict(x=x,x_limits=xlim,domain='positive integers n; even and odd residues')
        if y is not None:
            ylim=tuple(map(limit,y));z=tuple((operation,a,b) for a,b in zip(x,y));zlim=tuple(map(limit,z))
            result.update(y=y,y_limits=ylim,expression=z,expression_limits=zlim)
        return result

    if target in ('no_finite_cluster','one_finite_cluster_and_divergence'):
        desired=int(target=='one_finite_cluster_and_divergence')
        for x in profiles:
            z=witness(x);bounded={a for a in z['x_limits'] if isinstance(a,tuple)}
            if len(bounded)==desired and not finite(z['x_limits']) and (wanted is None or bounded=={wanted}):break
        else:raise Unsupported('No expression in the checked residue profile has the target')
        return dict(theorem='method.search_verified_rational_sequence_profiles',
                    argument=['Перебираем пары рациональных формул для чётных и нечётных индексов.',
                              'Для каждой части сравниваем первые степени числителя и знаменателя. Любая бесконечная подпоследовательность содержит бесконечную часть одной чётности.'],
                    search_profile='signed rational monomials on residues 0 and 1'),z

    operation='add' if target in ('divergent_sum','finite_sum') else 'mul'
    witnesses={}
    for x,y in product(profiles,repeat=2):
        z=witness(x,y,operation);a,b,c=(z[key] for key in ('x_limits','y_limits','expression_limits'))
        if target=='nonzero_product':
            if a==(ZERO,ZERO):
                verdict='diverges' if not finite(c) else 'zero_limit' if c[0]==ZERO else 'nonzero_limit'
                witnesses.setdefault(verdict,z)
                if len(witnesses)==3:break
        elif not finite(b) and finite(a)==(target in ('divergent_sum','maybe_product')):
            if target=='maybe_product' and a!=(ZERO,ZERO):continue
            if target in ('finite_sum','finite_product') and finite(c):
                witnesses['converges']=z;break
            if target in ('divergent_sum','maybe_product'):
                witnesses.setdefault('converges' if finite(c) else 'diverges',z)
                if target=='divergent_sum' and 'diverges' in witnesses or target=='maybe_product' and len(witnesses)==2:break
    need(witnesses and (target!='maybe_product' or len(witnesses)==2)
         and (target!='nonzero_product' or 'nonzero_limit' in witnesses),'No verified witness meets the source hypotheses')
    argument=['Программа пробует точные рациональные формулы на двух классах индексов. Сравниваем их предельные степени и проверяем все исходные требования.']
    if target=='divergent_sum':
        argument.append('Если сумма сходится, вычитание сходящейся последовательности даёт конечный предел для второй последовательности. Это противоречит условию.')
        conclusion='always fails finite convergence'
    elif target=='maybe_product':
        argument.append('При ненулевом пределе первого множителя конечный предел произведения дал бы конечный предел второго делением. При нулевом первом пределе проверены оба исхода.')
        conclusion='always divergent for a nonzero limit of x, both behaviors possible when x tends to zero'
    else:conclusion='the stated conclusion is not forced'
    return dict(theorem='method.search_verified_rational_sequence_profiles',argument=argument,
                search_profile='signed rational monomials on residues 0 and 1'),dict(conclusion=conclusion,witnesses=witnesses)


def reversible_addition(task,library):
    """Solve an addition law by applying an inverse only on a proved image."""
    from integrals import affine
    from tasks import domain_conditions,source
    need(library.data.get('inverse_addition_laws'),'No executable inverse addition transitions')
    g,given=packet(task,'equation','definition','goal')
    f=g['definition']
    need(not given and g['equation'] in ('f(x)+f(y)=f(z)','f(y)+f(x)=f(z)') and
         g['goal']=='all admissible real z, including parameter degeneracies' and
         task.get('source_statement') in (None,f'Пусть {g["equation"]}. Определить z, если f(x)={f}.'),
         'The original inverse equation or scope differs')
    x,y=('s','x'),('s','y');total=m.add(x,y);p=m.mul(x,y)
    if f=='1/x':
        value=dict(original_domain=['x!=0','y!=0'],cases=[dict(condition='x+y=0',solutions='none'),
                   dict(condition='x+y!=0',solution=m.div(p,total))])
        steps=['Области исходных сопряжённых дробей требуют ненулевых x и y.',
               'Складываем дроби. Если сумма ноль, ни один ненулевой z не подходит. Иначе обращаем ненулевой результат, поэтому найденная точка допустима.']
    elif f=='arctan(x), abs(x)<1':
        v=m.div(total,m.add(ONE,m.neg(p)))
        value=dict(original_domain=['abs(x)<1','abs(y)<1'],candidate=v,
                   cases=[dict(condition='abs(candidate)<1',solution=v),dict(condition='abs(candidate)>=1',solutions='none')])
        steps=['Две главные угловые величины лежат между −π/4 и π/4. Их сумма остаётся внутри главной ветви тангенса.',
               'Проверяем 1−xy>0 и применяем формулу сложения. Образ ограниченной исходной области требует ещё |z|<1.']
    elif f in ('log((1+x)/(1-x))','ln((1+x)/(1-x))'):
        denominator=m.add(ONE,p);v=m.div(total,denominator)
        value=dict(original_domain=['abs(x)<1','abs(y)<1'],solution=v)
        steps=['Положительность исходного отношения равносильна |u|<1. Сумма логарифмов превращается в логарифм положительного произведения.',
               'Обращаем линейно-дробную функцию. Знаменатель 1+xy положителен, а (1+xy)²−(x+y)²=(1−x²)(1−y²)>0 доказывает |z|<1.']
    else:
        params=names(f,'x')
        need(not set(params)&{'y','z'},'A fixed coefficient captures an original argument')
        raw=m.parse(f,'x',params)
        need(not domain_conditions(raw),'An affine source may not acquire hidden holes')
        a,b=affine(raw,'x');ctx=m.context(dict(variable='x',parameters=params))
        need(all(m.constant_defined(v,ctx) for v in (a,b)),'The source coefficients must be fixed real values')
        guard=source(a);offset=source(b)
        nonzero=[dict(condition=guard+'!=0',solution=m.add(total,m.div(b,a)))] if a!=ZERO else []
        branches=[] if m.nonzero(a,ctx) else [dict(condition=guard+'=0 and '+offset+'=0',solutions='all reals'),
                                             dict(condition=guard+'=0 and '+offset+'!=0',solutions='none')]
        value=dict(slope=a,offset=b,cases=nonzero+branches)
        steps=['Отделяем ненулевой наклон, когда исходное аффинное равенство можно обратить.',
               'При нулевом наклоне проверяем равенство 2b=b, которое определяет, допустимы ли все z или ни одного.']
    return dict(theorem='method.invert_addition_inside_source_image',argument=steps,original_function=f),value


def centered_form(task,library):
    """Construct centered algebraic and trigonometric representations with their original domain."""
    from integrals import affine
    from tasks import domain_conditions,known_guard
    need(library.data.get('exact_centered_forms'),'No executable centered form transitions')
    if task['goal']['required_form']=='y0+a*(x-x0)^2':
        return quadratic_center(task,library)
    g,given=packet(task,'general','required_form','example','goals')
    required=g['required_form'];text=g['general'];ex=g['example'];origin=task.get('source_statement')
    x=('v','x');params=names(text,'x')
    need(isinstance(ex,str) and isinstance(g['goals'],list) and len(g['goals'])==2 and g['goals'][1]=='obtain the prescribed form for every given example',
         'Every printed example is required')
    if required=='A*sin(x-x0)':
        need(not given and g['goals'][0]=='derive amplitude and phase with degeneracies' and origin in (
             None,f'Построить y={text}, приведя к y={required}. Рассмотреть y={ex}.'),'The original amplitude request differs')
        def phase(formula,parameters):
            raw=m.parse(formula,'x',parameters);ctx=m.context(dict(variable='x',parameters=parameters))
            need(raw[0]=='add' and not domain_conditions(raw),'Expected exactly two originally defined trigonometric terms')
            weights={}
            for term in raw[1:]:
                if term in (('sin',x),('cos',x)):scale,phase=ONE,term
                else:
                    need(term[0]=='mul','No fixed coefficient on the original phase')
                    candidates=[v for v in term[1:] if v in (('cos',x),('sin',x))]
                    need(len(candidates)==1,'Unproved amplitude phase')
                    phase=candidates[0];scale=term[1] if term[2]==phase else term[2]
                need(phase[0] not in weights and m.constant_defined(scale,ctx),'Duplicate phase or undefined coefficient')
                weights[phase[0]]=scale
            a,b=weights['cos'],weights['sin'];length=m.simplify(('sqrt',m.add(m.power(a,2),m.power(b,2))))
            if length==ZERO:return dict(amplitude=ZERO,phase='any real')
            return dict(amplitude=length,nonzero_case=dict(cos_phase=m.div(b,length),sin_phase=m.neg(m.div(a,length))),
                        zero_case='when both coefficients vanish any phase represents zero')
        return dict(theorem='method.centered_trigonometric_form_from_a_unit_vector',
                    argument=['Берём модуль вектора двух исходных коэффициентов.',
                              'При ненулевом модуле нормируем вектор и подбираем синус и косинус фазы. Тождество синуса разности восстанавливает исходную функцию.',
                              'При нулевом векторе амплитуда нулевая и фаза свободна.']),dict(general=phase(text,params),example=phase(ex,[]))

    simple=required=='y0+m/(x-x0)'
    need(simple or required=='k*x+m+n/(x-x0)','No checked normalized rational form')
    if simple:
        need(g['goals'][0]=='derive general centered form' and origin in (
            None,f'Построить график y={text}, ad-bc!=0,c!=0, приведя к y={required}. Рассмотреть y={ex}.'),
            'The original division and determinant conditions differ')
        need(not origin or given==['a*d-b*c!=0','c!=0'],'The explicit source exclusions were not retained')
    else:
        need(g['goals'][0]=='derive long-division coefficients' and origin in (
            None,f'Построить эскиз y={text}, a1!=0, приведя к y={required}. Рассмотреть y={ex}.'),
            'The original long division requirement differs')
        need(not origin or given==['a1!=0'],'The explicit affine divisor guard was omitted')
    def divide(formula,parameters,conditions):
        raw=m.parse(formula,'x',parameters);ctx=m.context(dict(variable='x',parameters=parameters,parameter_conditions=conditions))
        need(raw[0]=='div' and not any(domain_conditions(e) for e in raw[1:]),'The numerator or divisor has additional holes')
        v,w=affine(raw[2],'x');need(known_guard(('nonzero',v),ctx),'An affine divisor must have nonzero slope')
        coefficients=[ZERO,ZERO,ZERO]
        p,d=m.rational_form(raw[1]);need(d=={():1},'The original numerator must be polynomial')
        for mon,c in p.items():
            degree=dict(mon).get(x,0)
            need(degree<=2 and all(a==x or a[0]=='s' for a,j in mon),'An unbound operation remains in the numerator')
            term=m.poly_expr({tuple((a,n) for a,n in mon if a!=x):c})
            coefficients[degree]=m.add(coefficients[degree],term)
        c,b,a=coefficients
        need(not simple or a==ZERO,'The requested constant plus pole cannot absorb a linear term')
        k=m.div(a,v);y0=m.div(m.add(b,m.neg(m.mul(k,w))),v);m0=m.div(m.add(c,m.neg(m.mul(y0,w))),v)
        x0=m.neg(m.div(w,v))
        return dict(center=x0,affine_part=(k,y0),residue=m0,original_excluded_point=x0)
    return dict(theorem='method.centered_rational_form_with_original_pole',argument=[
                   'Проверяем ненулевой коэффициент исходного линейного делителя и находим его ноль.',
                   'Приравниваем коэффициенты числителя после умножения на делитель. Остаток делим на его ведущий коэффициент.',
                   'Исходная исключённая точка остаётся исключённой даже при нулевом остатке.']),dict(
                   conditions=given,general=divide(text,params,given),example=divide(ex,[],[]))


def quadratic_center(task,library):
    from tasks import domain_conditions,known_guard
    g,given=packet(task,'general_family','required_form','examples','goals')
    need(not given and g['goals']==['derive the general completed-square form',
         'obtain the prescribed form for every given example'] and isinstance(g['examples'],list) and g['examples'],
         'Every named polynomial and the full requested form are required')
    x=('v','x')

    def center(text):
        params=names(text,'x');raw=m.parse(text,'x',params);num,den=m.rational_form(raw)
        ctx=m.context(dict(variable='x',parameters=params))
        need(den=={():1} and all(known_guard(c,ctx) for c in domain_conditions(raw,True)),
             'Only originally defined real polynomials are admitted')
        p=[{} for _ in range(3)]
        for mon,c in num.items():
            degree=dict(mon).get(x,0);rest=tuple((a,k) for a,k in mon if a!=x)
            need(degree<=2 and all(a[0]=='s' for a,_ in rest),'Original function is not a quadratic polynomial')
            p[degree][rest]=c
        c,b,a=map(m.poly_expr,p)
        if a==ZERO:
            return dict(degree_zero=b==ZERO,constant=c,center=ZERO if b==ZERO else None)
        h=ZERO if b==ZERO else m.simplify(m.neg(m.div(b,m.mul(q(2),a))))
        v=m.simplify(m.add(c,m.neg(m.mul(a,m.power(h,2)))))
        need(same(raw,m.add(v,m.mul(a,m.power(m.add(x,m.neg(h)),2)))),'The centered expression fails expansion')
        return dict(leading=a,center=h,value=v,
                    zero_leading=dict(constant=c,required_zero_linear=b,center='arbitrary if constant'))

    return cert(library,'quadratic_center_by_coefficient_matching',
                dict(general=center(g['general_family']),examples=[center(f) for f in g['examples']]),
                'Сопоставляем коэффициенты при x², x и единице. При ненулевом ведущем коэффициенте находим центр из коэффициента при x и проверяем полное раскрытие квадрата.',
                'При нулевом ведущем коэффициенте отдельно оставляем постоянное выражение либо фиксируем, что ненулевая линейная часть препятствует указанной форме.')


def reciprocal_phase_signs(task,library):
    from tasks import source
    need(library.data.get('exact_reciprocal_phase_signs'),'No executable reciprocal phase sign profiles')
    g,given=packet(task,'variable','expression','goals');var=g['variable'];x=('v',var);raw=m.parse(g['expression'],var)
    need(not given and g['goals']==['zero set','strict positive set','strict negative set'] and
         task.get('source_statement') in (None,f"Для f({var})={g['expression']} найти {var}, для которых1)f({var})=0;2)f({var})>0;3)f({var})<0.") and
         raw[0]=='sin' and raw[1][0]=='div' and raw[1][2]==x,'The original signs or common reciprocal phase differ')
    ctx=m.context(dict(variable=var));coefficient=raw[1][1];scale=m.simplify(m.div(coefficient,m.PI))
    need(m.constant_defined(coefficient,ctx) and m.num(scale) is not None and scale!=ZERO,
         'The reciprocal phase needs a nonzero rational multiple of π')
    t=m.div(scale,x);shown=source(t)
    return dict(theorem='method.sign_sets_by_reciprocal_phase_preimages',argument=[
        'Вводим фазовую координату u как аргумент синуса, делённый на π. Она пробегает ненулевые вещественные числа.',
        'Переносим точные целые нули и соседние открытые интервалы знакопостоянства на исходную область. Исключаем нулевую фазу, недостижимую при конечном исходном аргументе.'],
        original_phase=raw,phase_coordinate=t),dict(
        original_domain=[var+'!=0'],zero_set=source(scale)+'/k for nonzero integers k',
        positive_set='2k<'+shown+'<2k+1 for integer k',negative_set='2k+1<'+shown+'<2k+2 for integer k')


def composed_real_image(task,library):
    from integrals import affine
    from tasks import domain_conditions,known_guard,source
    need(library.data.get('monotone_component_images'),'No executable monotone-image transitions')
    g,given=packet(task,'variable','variable_space','expression','goals');var=g['variable']
    text=g['expression']
    need(not given and g['variable_space']=='real_numbers' and g['goals']==['maximal real domain','exact image of that domain']
         and task.get('source_statement') in (None,f'Определить область существования и множество значений y={text}.'),
         'The actual complete domain and image are required')
    lens=re.fullmatch(r'(lg|ln)\((.+)\)',text)
    outer=re.fullmatch(r'(?:asin|arcsin)\((lg|ln)\((.+)\)\)',text)
    if re.match(r'\(-\s*\d',text):
        raw=m.parse(text,var)
        need(raw[0]=='rpow' and not domain_conditions(raw[1]) and not domain_conditions(raw[2]),
             'The fixed negative base or its original power argument is unresolved')
        base=m.num(m.simplify(raw[1]));a,b=affine(raw[2],var)
        need(base is not None and base<0 and m.num(a) not in (None,0) and m.num(b) is not None,
             'A constant negative base and nonconstant affine exponent are required')
        exponent=source(raw[2])
        allowed=dict(exponent=exponent,form='p/q in reduced form, p integer and q positive odd')
        if base==-1:image=dict(values=[q(-1),ONE],attained_at_exponents=[ONE,ZERO])
        else:image=dict(magnitude_base=q(-base),value='(-1)^p * magnitude_base^(p/q)',exponent_domain=allowed)
        return (dict(theorem='method.real_negative_base_rational_exponents',
                    argument=['Для несократимого показателя p/q вещественный корень отрицательного основания существует тогда, когда q нечётно.',
                              'Знак значения определяется чётностью p. Аффинный показатель ненулевого наклона принимает все вещественные значения и потому даёт весь указанный образ.']),
                    dict(domain=allowed,image=image,real_power_convention='real roots of reduced rational powers'))
    if lens:
        kind,inside=lens.groups();raw=m.parse(inside,var)
        need(not domain_conditions(raw),'The original cosine expression has additional restrictions')
        p,d=m.rational_form(raw)
        nonconstant=[(mon,c) for mon,c in p.items() if mon]
        need(d=={():1} and len(nonconstant)==1 and len(nonconstant[0][0])==1 and nonconstant[0][0][0][1]==1,
             'Expected one nonconstant, linearly weighted cosine')
        ((atom,_),),b=nonconstant[0];need(atom[0]=='cos','The interior image must be periodic cosine')
        a,c=affine(atom[1],var)
        need(m.num(a) is not None and m.num(a)!=0 and m.constant_defined(c,m.context(dict(variable=var))),
             'The phase does not cover the real line')
        offset=p.get((),0);low,high=offset-abs(b),offset+abs(b)
        def log(value):return m.simplify(('ln',q(value))) if kind=='ln' else m.div(('ln',q(value)),('ln',q(10)))
        intervals=[] if high<=0 else [('-inf' if low<=0 else log(low),log(high),low>0,True)]
        value=dict(domain='empty' if high<=0 else source(raw)+'>0',image_intervals=intervals)
        steps=['Аффинная фаза с ненулевым наклоном принимает все вещественные значения, и косинус достигает обеих границ.',
               'Пересекаем точный интервал внутренней функции с положительной областью логарифма. Строгая монотонность переносит достижимость каждой оставшейся границы.']
    elif outer:
        kind,inside=outer.groups();raw=m.parse(inside,var)
        need(all(known_guard(g,m.context(dict(variable=var))) for g in domain_conditions(raw)),
             'The original affine argument contains an additional hole')
        a,b=affine(raw,var);coefficient=m.num(a)
        need(coefficient is not None and coefficient!=0 and m.num(b) is not None,'The inner affine image needs a nonzero real slope')
        lo,hi=(q(1,10),q(10)) if kind=='lg' else (('exp',q(-1)),('exp',ONE))
        endpoints=[m.div(m.add(v,m.neg(b)),a) for v in (lo,hi)]
        if coefficient<0:endpoints.reverse()
        value=dict(domain_interval=(*endpoints,True,True),image_intervals=[(m.mul(q(-1,2),m.PI),
                    m.mul(q(1,2),m.PI),True,True)])
        steps=['Из главной ветви арксинуса выводим условие −1≤log(u)≤1.',
               'Обращаем монотонный логарифм и линейную функцию с проверенным знаком наклона. Все точки допустимого интервала, включая его концы, дают полный главный образ арксинуса.']
    else:raise Unsupported('No checked monotone component composition for the full domain and image')
    return dict(theorem='method.image_by_inverting_the_outer_domain',argument=steps,original_expression=text),value


def relative_product_error(task,library):
    need(library.data.get('signed_error_product_expansion'),'No executable relative-error expansion')
    g,given=packet(task,'proposition','factor_bounds',exact=False)
    need(g.get('proposition')=='delta(product)<=delta(x)+delta(y)+delta(x)*delta(y)' and
         given==['true values a,b are nonzero; relative error is defined with the true denominator'] and
         task.get('source_statement') in (None,'Пусть delta(x),delta(y) — относительные погрешности x,y, а delta(xy) — относительная погрешность произведения. Доказать delta(xy)<=delta(x)+delta(y)+delta(x)*delta(y).'),
         'The true nonzero denominators and the original error estimate are required')
    value=dict(proved=True,relative_bound='abs(u)+abs(v)+abs(u)*abs(v)')
    if 'factor_bounds' in g:
        need('source_statement' not in task and isinstance(g['factor_bounds'],list) and len(g['factor_bounds'])==2,
             'Expected both stated factor-error bounds')
        a,b=map(rational,g['factor_bounds'])
        need(a>=0 and b>=0,'Absolute error bounds cannot be negative')
        value['evaluated_upper_bound']=q(a+b+a*b)
    return dict(theorem='method.relative_error_from_multiplicative_increment',
                argument=['Делим знаковую ошибку каждого множителя на его истинное ненулевое значение.',
                          'Правильное отношение измеренного произведения к истинному равно (1+u)(1+v).',
                          'Вычитаем единицу и применяем треугольное неравенство к u+v+uv.']),value


QUANTIFIERS={'epsilon_sequence_limit','magnitude_infinity_witness','quantifier_formulation','negate_Cauchy_quantifiers'}


MEASUREMENT={'compare_measurement_errors','correct_significant_digits','relative_error_bound_from_digits',
             'interval_measurement_error','relative_area_error_estimator','measurement_tolerance'}
INTERPOLATION={'linear_interpolation_and_evaluation','quadratic_interpolation_and_evaluation','cubic_interpolation',
               'exponential_family_interpolation'}
FUNCTION={'exact_function_evaluation','function_expression_substitution','difference_quotient_simplification',
          'polynomial_finite_difference_identity'}


ENVELOPE_GOALS={'limsup_liminf_inequality','limsup_liminf_product_inequality'}


def tail_operation_bounds(task,library):
    """Use order-preserving operations on tails and construct strict periodic witnesses."""
    goal,given=packet(task,'proposition','extra_goal')
    need(task.get('index_domain')=='positive_integers' and goal['extra_goal']=='strict examples',
         'The stated integer domain and both strict witnesses are required')
    proposition=goal['proposition']
    names=sorted(set(re.findall(NAME,proposition))-{'liminf','limsup'})
    clauses=proposition.replace('≤','<=').split('<=')
    need(len(names)==2 and len(clauses)==3,'One three-part envelope inequality in two sequences is required')
    tags=('liminf','limsup')
    raw=[m.parse(e,None,names,tags) for e in clauses]
    kind=task.get('kind',task.get('task_type'))
    mode='mul' if kind=='limsup_liminf_product_inequality' else 'add'
    need(raw[1][0] in tags and raw[1][1][0]==mode and set(raw[1][1][1:])=={('s',n) for n in names},
         'The middle envelope must combine both original sequences')
    need(sorted(given)==sorted([n+'[n]>=0' for n in names] if mode=='mul' else []),
         'Multiplication is order preserving only in the bound original nonnegative regime')
    statement=task.get('source_statement','')
    middle=raw[1][0]
    def atom(tag,name):return (tag,('s',name))
    def expected(t,u):return m.simplify((mode,atom(t,names[0]),atom(u,names[1])))
    both_low=expected('liminf','liminf');both_high=expected('limsup','limsup')
    mixed={expected('liminf','limsup'),expected('limsup','liminf')}
    permitted=(m.simplify(raw[0])==both_low and m.simplify(raw[2]) in mixed if middle=='liminf'
               else m.simplify(raw[0]) in mixed and m.simplify(raw[2])==both_high)
    need(permitted,'The requested outer estimates do not follow from the stated envelope directions')
    if statement:
        need('построить' in statement and 'строг' in statement,'The verbatim request must include the strictness examples')
        stated=statement.split('Доказать ',1)[-1].split(' и построить',1)[0].split(';',1)[0]
        original=stated.replace('≤','<=').split('<=')
        if len(original)==3:
            stated_raw=[m.parse(e,None,names,tags) for e in original]
            need(all(m.simplify(e)==m.simplify(v) or (i==1 and e[0]==v[0] and
                     m.simplify(e[1])==m.simplify(v[1])) for i,(e,v) in enumerate(zip(stated_raw,raw))),
                 'The displayed source inequality differs from the typed conclusion')
        else:raise Unsupported('The printed comparison was not recovered')

    def apply(a,b):return a+b if mode=='add' else a*b
    def samples(e,choices):
        if e[0]=='s':return choices[e[1]]
        return tuple(apply(a,b) for a,b in zip(samples(e[1],choices),samples(e[2],choices),strict=True))
    def evaluate(e,choices):
        if e[0] in tags:return (min if e[0]=='liminf' else max)(samples(e[1],choices))
        return apply(evaluate(e[1],choices),evaluate(e[2],choices))

    witnesses=[]
    for i in (0,1):
        for data in product((0,1,2),repeat=4):
            choices=dict(zip(names,(data[:2],data[2:])))
            values=[evaluate(e,choices) for e in raw]
            if values[0]<=values[1]<=values[2] and values[i]<values[i+1]:
                witnesses.append(dict(strict_index=i,periodic_samples=choices,envelopes=values))
                break
    need(len(witnesses)==2,'Both strict inequalities need exact periodic examples')
    return cert(library,'tail_envelope_monotone_operations',
                dict(proved=True,strict_witnesses=witnesses,scope='all stated sequences whenever the extended displayed operations are defined'),
        'На каждом целом хвосте операция сохраняет порядок в обоих аргументах. Две одинаковые грани дают нижнюю оценку inf или верхнюю sup.',
        'Для смешанной оценки выбираем на том же хвосте член, сколь угодно близкий к нужной грани одного множителя. Второй ограничиваем его противоположной гранью.',
        'Переходим к монотонным пределам хвостовых граней там, где исходная расширенная операция определена. Для каждого строгого знака перебираем двухчленные периоды и точно пересчитываем три величины.',
        operation=mode,source_envelope=raw[1],source_conditions=given)



def routing(task,kind):
    g=task.get('goal')
    if kind in ENVELOPE_GOALS:return isinstance(g,dict)
    if kind=='mathematical_question':
        return isinstance(g,dict) and ('distributed_mass' in g or g.get('function')=='sgn' and 'pieces' in g
                                      or g.get('required_form')=='y0+a*(x-x0)^2' and {'general_family','examples','goals'}<=g.keys()
                                      or g.get('required_form') in ('y0+m/(x-x0)','k*x+m+n/(x-x0)','A*sin(x-x0)')
                                      and {'general','example','goals'}<=g.keys())
    if kind=='functional_addition_equation':return isinstance(g,dict)
    if isinstance(g,dict):
        if kind=='restricted_function_image':
            try:affine_interval_data(task)
            except (Unsupported,ValueError,TypeError,KeyError):pass
            else:return True
        expr=g.get('expression','');var=g.get('variable','x')
        if kind=='proof' and g.get('proposition')=='delta(product)<=delta(x)+delta(y)+delta(x)*delta(y)':return True
        if isinstance(expr,str) and isinstance(var,str):
            if (kind=='function_sign_sets' and set(g)=={'variable','expression','goals'}
                    and re.fullmatch(r'sin\((?:-?\d+\*)?pi/'+re.escape(var)+r'\)',expr)):return True
            if kind=='real_function_domain_and_range' and set(g)=={'variable','variable_space','expression','goals'}:
                phase=re.escape(var)
                scale=r'(?:\d+\*)?'+phase+r'(?:/\d+)?'
                if re.match(r'\(-\s*\d',expr) or re.fullmatch(r'(?:lg|ln)\(\d+[+-]\d+\*cos\('+scale+r'\)\)',expr) or re.fullmatch(
                    r'(?:asin|arcsin)\((?:lg|ln)\('+scale+r'(?:[+-]\d+)?\)\)',expr):return True
    if kind=='compute_sequence_limit' and isinstance(g,dict) and not set(g)&{'left','right','comparison'}:
        # The lattice scale table is one of several limit routes; leave other expressions to the shared limit graph.
        try:
            given=task.get('assumptions',task.get('source_assumptions',[]));n=('v',g.get('variable','n'))
            e=parse_sequence(g['expression'],n);lattice_domain(e,n,given);tail(e,n,given)
        except (Unsupported,ValueError,TypeError,KeyError,poly.NotRational,poly.Undefined):return False
    return (kind in MEASUREMENT | INTERPOLATION | FUNCTION | SEQUENCE_LIMIT | CLUSTERS | QUANTIFIERS | ARITHMETIC_TAIL | WITNESS_GOALS
            | PROGRESSION_MAPS | {'induction_with_corollary','prove_finite_product_limit','cluster_set_invariance',
                                  'counterexample_to_factor_limit_inference','area_via_inscribed_sum_limit',
                                  'construct_dedekind_cut','exponential_identity','planar_metric_model'}
            | TAIL_THEOREMS.keys() | PREFIX | RECURSIONS | EXP_BRACKETS | EXP_FACTORIAL | CUTS | REFUTATIONS and isinstance(g,dict)
            and (kind!='cauchy_sequence_convergence' or task['goal'].get('required_method')=='Cauchy criterion'
                 and isinstance(task['goal'].get('sequence'),str) and '[0]+sum(' in task['goal']['sequence'])
            and (kind!='compute_sequence_limit' or NATURAL in task.get('assumptions',())
                 or task.get('index_domain')=='positive_integers'))


def elementary_proof(task,library,request):
    kind=task.get('kind',task.get('task_type'))
    if kind in ENVELOPE_GOALS:return tail_operation_bounds(task,library)
    if kind in ('induction_with_corollary','prove_finite_product_limit'):return finite_ladder_argument(task,library,kind)
    if kind=='cluster_set_invariance':return scale_cluster_set(task,library,request)
    if kind=='counterexample_to_factor_limit_inference':return alternating_product_witness(task,library)
    if kind in PROGRESSION_MAPS:return transport_progression(task,library,kind)
    if kind=='restricted_function_image':return affine_interval_image(task,library)
    if kind=='area_via_inscribed_sum_limit':return inscribed_scaled_power(task,library,request)
    if kind=='construct_dedekind_cut':return rational_power_cut(task,library)
    if kind=='exponential_identity':return symmetric_power_addition(task,library)
    if kind=='planar_metric_model':return planar_metric_model(task,library,request)
    if kind in WITNESS_GOALS or kind=='sequence_cluster_set' and 'sequence_by_blocks' in task['goal']:
        return sequence_witness(task,library,kind)
    if kind=='functional_addition_equation':return reversible_addition(task,library)
    if kind=='mathematical_question' and 'required_form' in task['goal']:return centered_form(task,library)
    if kind=='function_sign_sets':return reciprocal_phase_signs(task,library)
    if kind=='real_function_domain_and_range':return composed_real_image(task,library)
    if kind=='proof' and task['goal']['proposition'].startswith('delta('):return relative_product_error(task,library)
    if kind in SEQUENCE_LIMIT:return tail_packet(task,library)
    if kind in CLUSTERS:return cluster_packet(task,library)
    if kind in QUANTIFIERS:return quantified_tails(task,library)
    if kind in TAIL_THEOREMS:return abstract_tail(task,library)
    if kind in ARITHMETIC_TAIL:return arithmetic_tails(task,library)
    if kind in PREFIX:return convergent_prefix(task,library)
    if kind in RECURSIONS:return monotone_recursion(task,library)
    if kind in EXP_BRACKETS:return exponential_bracket(task,library)
    if kind in EXP_FACTORIAL:return exponential_factorial_tail(task,library)
    if kind in CUTS or kind=='mathematical_question':return finite_cut_or_atom(task,library)
    if kind in REFUTATIONS:return review_printed_scope(task,library)
    handler=measurement if kind in MEASUREMENT else interpolation if kind in INTERPOLATION else function_sheet
    return handler(task,library)
