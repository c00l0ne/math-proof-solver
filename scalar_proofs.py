"""Exact scalar property certificates, with reflection and the original domain."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt, lcm
import re

import expressions as m
import intervals as line
import polynomial as poly
from model import ONE, ZERO, Unsupported, freeze, q
from tasks import domain_conditions, known_guard, source
from verify import same_value


KINDS = {
    'function_parity', 'even_odd_decomposition_proof', 'graph_symmetry_classification',
    'periodicity_and_fundamental_period', 'dirichlet_function_period_proof',
    'commensurate_period_arithmetic_proof', 'antiperiod_implies_period_proof',
    'scaled_period_factorization', 'reflection_period_proof',
    'limit_definition_and_examples', 'infinity_limit_definition_and_examples',
    'infinite_point_limit_definition_and_examples', 'infinite_tail_definition_and_examples',
    'directed_value_limit_definition_and_examples', 'epsilon_delta_proof_and_table',
    'E_delta_infinite_limit_proof_and_table',
    'oscillation_at_point', 'geometric_infinitesimal_order',
    'prove_asymptotic_relation', 'Landau_or_equivalence_example_proof',
    'Landau_symbol_algebra_proof', 'Landau_power_algebra_proof',
    'asymptotic_equivalence_relation_proof', 'prove_eventual_inequality',
    'parameter_monotonicity_classification', 'inequality_logarithm_conditions',
    'ordered_composition_sandwich', 'finite_but_locally_unbounded_proof',
    'local_global_boundedness_with_examples', 'boundedness_proof',
    'unbounded_not_magnitude_infinite_proof', 'boundedness_analysis',
    'infimum_supremum_proof', 'monotone_bounds_question', 'bounds_sum_proof_with_examples',
    'derivative_limit_counterexample',
}
EXTENSION = ['even extension to negative x', 'odd extension to negative x']
META = {'schema', 'id', 'kind', 'task_type', 'source', 'source_number', 'source_exercise_number',
        'source_subpart', 'source_pdf_page', 'source_pdf_pages', 'source_edition',
        'program_status', 'main_pass_status', 'pending_obligations', 'deferred_reason', 'transcription_notes'}
EPSILON_GOALS = ['quantified inequality definition', 'corresponding example']


def routing(kind, goal):
    if kind in KINDS:
        return True
    if not isinstance(goal, dict):
        return False
    return (kind == 'mathematical_question' and goal.get('goals') == EXTENSION
            or kind == 'proof' and goal.get('domain') == 'R' and goal.get('goal') in
            ('prove periodicity','prove that f is a sum of linear and periodic functions and that f is periodic when y0=y1'))


def fresh(name, occupied):
    while name in occupied:
        name += '_'
    return name


def term_names(text, var='x'):
    return sorted(set(re.findall(r'[a-zA-Z_][\w]*', text))-m.FUNCTIONS-set(m.ALIASES)-{var,'pi','e'})


def parsed(text, assumptions=(), var='x'):
    names = term_names(text, var)
    facts = []
    for item in assumptions:
        if re.fullmatch(r'0<[A-Za-z_]\w*<[A-Za-z_]\w*',item):
            _, a, b = item.split('<')
            facts.extend([a+'>0','('+b+'-'+a+')>0'])
        else:
            facts.append(item)
    context = m.context(dict(variable=var, parameters=names, parameter_conditions=facts))
    return m.parse(text, var, names), context


def statement(task, expected):
    if task.get('source_statement', expected) != expected:
        raise Unsupported('The requested assertion disagrees with the printed source')


def packet(task, fields, expected, assumptions=()):
    if set(task)-META-{'goal','source_statement','assumptions','source_assumptions'} or set(task.get('goal',{}))!=fields:
        raise Unsupported('An unproved source obligation remains')
    if task.get('assumptions', task.get('source_assumptions', [])) != list(assumptions):
        raise Unsupported('An additional source assumption remains')
    statement(task, expected)
    return task['goal']


def proof(rule, answer, argument, **evidence):
    return dict(theorem='method.'+rule, argument=argument, **evidence), answer


def shifted(e, x, replacement):
    return m.substitute(e, {x: replacement})


def global_guard(g, var, ctx):
    relation, e = g
    atom = ('s',var)
    fixed = {**ctx, 'parameters':[*ctx['parameters'],var]}
    raw = shifted(e, ('v',var), atom)
    if known_guard((relation,raw),fixed):
        return True
    if relation=='positive' and raw[0]=='add' and raw[2][0]=='sqrt':
        a,b=raw[1],raw[2][1]
        return (m.constant_defined(a,fixed) and m.constant_defined(b,fixed)
                and known_guard(('positive',m.add(b,m.neg(m.power(a,2)))),fixed))
    return False


def analytic_support(raw, var, ctx):
    from graphs import domain_partition
    guards = domain_conditions(raw)
    unresolved = [g for g in guards if not global_guard(g,var,ctx)]
    if not unresolved:
        return guards, None
    if ctx['parameters']:
        raise Unsupported('The original parameterized domain has not been partitioned')
    try:
        _, intervals = domain_partition(var, unresolved)
    except (poly.NotRational, poly.Undefined) as exc:
        raise Unsupported('The domain of the reflected expression is unresolved') from exc
    if not intervals[1]:
        raise Unsupported('The function has no real point on its source domain')
    return guards, intervals[1]


def even_odd(task, kind):
    g=task['goal'];x=('v','x')
    if kind=='even_odd_decomposition_proof':
        expected='Доказать, что всякую функцию f, определённую на симметричном интервале(-l,l), можно представить суммой чётной и нечётной функций.'
        packet(task,{'domain','hypothesis','goal'},expected)
        if g!=dict(domain='(-l,l)',hypothesis='f is defined on that symmetric interval',goal='construct even and odd summands giving f'):
            raise Unsupported('Unexpected reflection or decomposition obligation')
        return proof('scalar_reflection',dict(even='(f(x)+f(-x))/2',odd='(f(x)-f(-x))/2',domain=g['domain']),
                     'Симметрия интервала допускает подстановку −x. Среднее сохраняет знак при отражении, полуразность меняет знак. Их сумма равна f(x).')
    if kind=='mathematical_question':
        text=g['original_expression']
        packet(task,{'original_expression','original_domain','goals'},
               f'Функцию f(x)={text} при x>0 продолжить на x<0 как1)чётную;2)нечётную. Построить оба графика.')
        if g['original_domain']!='x>0' or g['goals']!=EXTENSION:
            raise Unsupported('The retained extension and source half-line must agree')
        raw,ctx=parsed(text)
        if ctx['parameters']:
            raise Unsupported('No additional parameter has been declared')
        # Prove that f is defined for every positive x before reflecting it.
        u=('s','x');whole=m.context(dict(variable='__extension',parameters=['x'],parameter_conditions=['x>0']))
        if not all(known_guard((rel,shifted(e,x,u)),whole) for rel,e in domain_conditions(raw)):
            raise Unsupported('The positive half-line is not contained in the original domain')
        reflected=shifted(raw,x,m.neg(x))
        return proof('scalar_reflection',dict(on_positive=raw,on_negative_even=reflected,
                          on_negative_odd=m.neg(reflected),domain='x!=0'),
                     'При x<0 число −x принадлежит исходной положительной полуоси. У чётного продолжения берём f(−x), у нечётного −f(−x). Эти назначения вынуждены соответствующим тождеством.')
    text=g['expression'];assumptions=task.get('assumptions',[])
    packet(task,{'expression','goal'},f'Определить чётность или нечётность f(x)={text}.',assumptions)
    if g['goal']!='classify parity on its symmetric real domain':
        raise Unsupported('Unknown source parity condition')
    raw,ctx=parsed(text,assumptions)
    guards,intervals=analytic_support(raw,'x',ctx)
    if intervals is not None:
        reflect=lambda p: '+inf' if p=='-inf' else '-inf' if p=='+inf' else line.endpoint_term(line.read_endpoint(p).neg())
        reversed_domain=[(reflect(b),reflect(a),rc,lc) for a,b,lc,rc in reversed(intervals)]
        if list(map(freeze,reversed_domain))!=list(map(freeze,intervals)):
            raise Unsupported('The original domain is not invariant under reflection')
    other=shifted(raw,x,m.neg(x))
    even=same_value(other,raw)
    odd=same_value(other,m.neg(raw))
    reciprocal=raw[0]=='ln' and same_value(m.mul(raw[1],other[1]),ONE)
    odd=odd or reciprocal
    if not even and not odd:
        raise Unsupported('No reflection identity is established')
    return proof('scalar_reflection',dict(parity='even_and_odd' if even and odd else 'even' if even else 'odd',
                     support=intervals if intervals is not None else 'R'),
                 'Область сохраняется при отражении. Аргументы двух логарифмов положительны и взаимно обратны.' if reciprocal else
                 'После подстановки −x проверяется тождество чётности или нечётности на симметричной области.',
                 original_guards=guards,original=raw,reflected=other,assumptions=assumptions)


def polynomial_coefficients(raw, x, maximum):
    numerator,denominator=m.rational_form(raw)
    if not denominator or any(m.contains(a,x) for mon in denominator for a,_ in mon):
        raise Unsupported('A polynomial in the coordinate is required')
    rows=[{} for _ in range(maximum+1)]
    for mon,c in numerator.items():
        power=dict(mon).get(x,0)
        rest=tuple((a,k) for a,k in mon if a!=x)
        if power>maximum or any(m.contains(a,x) for a,k in rest):
            raise Unsupported('Unexpected coordinate dependence')
        rows[power][rest]=c
    return [m.div(m.poly_expr(row),m.poly_expr(denominator)) for row in rows]


def symmetry(task):
    g=task['goal'];text=g['expression'];x=('v','x')
    mode={'all vertical symmetry axes including parameter cases':'axis',
          'all centers of graph symmetry, retaining domain':'center'}.get(g['goal'])
    if mode is None:
        raise Unsupported('Unknown reflection to classify')
    prefix='Определить вертикальные оси симметрии графика y=' if mode=='axis' else 'Определить центры симметрии графика y='
    assumptions=task.get('assumptions',[])
    packet(task,{'expression','goal'},prefix+text+'.',assumptions)
    raw,ctx=parsed(text,assumptions);guards=domain_conditions(raw)
    def answer(cases, argument, **evidence):
        return proof('scalar_reflection',dict(kind=mode,cases=cases),argument,original=raw,guards=guards,**evidence)
    def row(conditions, point, ordinate=None):
        return dict(conditions=conditions,abscissa=point,ordinate=ordinate)
    test=lambda e,op: source(e)+op+'0'
    if all(global_guard(g,'x',ctx) for g in guards):
        try:
            d,c,b,a=polynomial_coefficients(raw,x,3)
        except Unsupported:
            pass
        else:
            rows=[]
            if mode=='axis':
                if a!=ZERO:rows.append(row([test(a,'!=')],'none'))
                if b!=ZERO:rows.append(row(([test(a,'=')] if a!=ZERO else [])+[test(b,'!=')],m.div(m.neg(c),m.mul(q(2),b))))
                tail=[test(e,'=') for e in (a,b) if e!=ZERO]
                if c!=ZERO:rows.append(row(tail+[test(c,'!=')],'none'))
                rows.append(row(tail+([test(c,'=')] if c!=ZERO else []),'all real'))
            else:
                if a!=ZERO:
                    h=m.div(m.neg(b),m.mul(q(3),a))
                    rows.append(row([test(a,'!=')],h,m.simplify(shifted(raw,x,h))))
                if b!=ZERO:rows.append(row(([test(a,'=')] if a!=ZERO else [])+[test(b,'!=')],'none'))
                rows.append(row([test(e,'=') for e in (a,b) if e!=ZERO],'all real','on graph'))
            return answer(rows,'Сравниваем коэффициенты степеней u в выражениях f(h+u) и f(h−u). Для оси должны исчезнуть нечётные коэффициенты, для центра чётные коэффициенты положительной степени. Проверяем вырождения старших коэффициентов.',
                          coefficients=[d,c,b,a])
    if raw[0]=='div' and mode=='center' and guards==[('nonzero',raw[2])]:
        try:
            b,a=polynomial_coefficients(raw[1],x,1)
            d,c=polynomial_coefficients(raw[2],x,1)
        except Unsupported:
            pass
        else:
            if all(m.constant_defined(e,ctx) for e in (a,b,c,d)):
                cases=[]
                if c!=ZERO:cases.append(row([test(c,'!=')],m.div(m.neg(d),c),m.div(a,c)))
                tail=[test(c,'=')] if c!=ZERO else []
                if d!=ZERO:cases.append(row(tail+[test(d,'!=')],'all real','on graph'))
                cases.append(row(tail+([test(d,'=')] if d!=ZERO else []),'no real domain'))
                return answer(cases,'При ненулевом коэффициенте x в знаменателе единственная исключённая точка должна быть центром отражения области. После вычитания отношения старших коэффициентов получается кратное 1/(x−h). Проверяем также линейный случай и пустую область.',
                              numerator=[b,a],denominator=[d,c])
    if mode=='axis' and raw[0]=='add' and all(u[0]=='sqrt' for u in raw[1:]):
        a,p=polynomial_coefficients(raw[1][1],x,1);b,r=polynomial_coefficients(raw[2][1],x,1)
        positive_width=(m.sign(m.add(a,b),ctx)==1 or
                        m.sign(a,ctx)==m.sign(m.add(b,m.neg(a)),ctx)==1)
        if p==ONE and r==q(-1) and positive_width:
            h=m.mul(q(1,2),m.add(b,m.neg(a)))
            return answer([row([],h)],'Отражение ограниченной области обязано сохранять её два конца. В её середине отражение меняет местами подкоренные выражения.',
                          domain=[m.neg(a),b],axis=h)
    if mode=='axis' and not guards:
        from integrals import affine
        numerator,denominator=m.rational_form(raw)
        waves=[(mon[0][0],c) for mon,c in numerator.items() if len(mon)==1 and mon[0][1]==1 and mon[0][0][0]=='cos']
        cosines={w for w,_ in waves}
        if len(waves)!=1:
            # A parameter multiplying a cosine is a separate atom in the monomial.
            cosines={a for mon in numerator for a,k in mon if a[0]=='cos' and k==1 and m.contains(a,x)}
        if len(cosines)==1:
            wave,=cosines;at=('s',fresh('__cos',ctx['parameters']))
            try:b1,b0=affine(wave[1],'x');c,amp=polynomial_coefficients(shifted(raw,wave,at),at,1)
            except Unsupported:pass
            else:
                if (not m.variable_in(c) and not m.variable_in(amp) and m.num(b1) not in (None,0)
                        and all(m.constant_defined(e,ctx) for e in (c,amp,b0))):
                    k=('s',fresh('k',ctx['parameters']))
                    h=m.div(m.add(m.mul(m.PI,k),m.neg(b0)),b1)
                    return answer([row([test(amp,'!=')],h),row([test(amp,'=')],'all real')],
                        'Разность отражённых косинусов пропорциональна sin(ωh+β). При ненулевой амплитуде оси получаются из всех целых кратных π в фазе, а при нулевой амплитуде все вертикальные прямые являются осями.',
                        index=k,frequency=b1,phase=b0)
    if mode=='center' and raw[0]=='add':
        cube=next((e for e in raw[1:] if e[0]=='cbrt'),None)
        if cube is not None:
            from integrals import affine
            constant=raw[2] if raw[1]==cube else raw[1]
            speed,shift=affine(cube[1],'x')
            if m.constant_defined(constant,ctx) and not m.variable_in(constant) and m.nonzero(speed,ctx):
                h=m.div(m.neg(shift),speed)
                return answer([row([],h,constant)],'Единственная точка с негладкой кубической ветвью фиксирует абсциссу центра. Кубический корень от линейного приращения нечётен.',
                              singular_abscissa=h)
    if not ctx['parameters']:
        try:poly.rf(raw,'x')
        except (poly.NotRational,poly.Undefined):raise Unsupported('The finite-pole reflection requires rational values')
        _,intervals=analytic_support(raw,'x',ctx)
        if intervals and all(not a[3] and not b[2] and a[1]==b[0] and a[1] not in ('+inf','-inf')
                             for a,b in zip(intervals,intervals[1:])) and len(intervals)>1 and intervals[0][0]=='-inf' and intervals[-1][1]=='+inf':
            holes=[line.read_endpoint(r[1]) for r in intervals[:-1]]
            if any(h.b for h in holes):
                raise Unsupported('The finite complement requires irrational comparisons')
            h=(holes[0].a+holes[-1].a)/2
            if any(a.a+b.a!=2*h for a,b in zip(holes,reversed(holes))):
                return answer([row([],'none')],'Требуемое отражение не сохраняет конечное множество выколотых точек.')
            lo,hi=[shifted(raw,x,m.add(q(h),u)) for u in (x,m.neg(x))]
            if mode=='axis':
                point=q(h) if same_value(lo,hi) else 'none'
                return answer([row([],point)],'Конечное множество исключённых точек допускает только отражение вокруг середины крайних точек. Проверяем тождество на этой оси.',shifted_values=[lo,hi])
            average=m.mul(q(1,2),m.add(lo,hi))
            if not m.variable_in(average) and m.constant_defined(average,ctx):
                return answer([row([],q(h),average)],'Выколотые точки фиксируют возможную абсциссу центра. Полусумма отражённых значений постоянна на исходной области.',shifted_values=[lo,hi])
    raise Unsupported('The complete reflection locus has not been established')


def rational_gcd(values):
    den=lcm(*(x.denominator for x in values))
    return F(gcd(*(int(x*den) for x in values)), den)


def simple_phase_sum(raw, name):
    numerator,denominator=m.rational_form(raw)
    if denominator!={():F(1)}:
        raise Unsupported('The phase sum has a nonconstant denominator')
    waves=[]
    for mon,c in numerator.items():
        if not mon:
            continue
        if len(mon)!=1 or mon[0][1]!=1 or mon[0][0][0]!=name:
            raise Unsupported('Not a simple sum of independent trigonometric modes')
        waves.append((mon[0][0][1],c))
    if not waves:
        raise Unsupported('No trigonometric wave found')
    return waves


def fundamental_period(task):
    from integrals import affine, harmonic_modes
    g=task['goal'];text=g['expression'];x=('v','x')
    packet(task,{'expression','goals'},f'Выяснить периодичность f(x)={text} и определить наименьший период, если он есть.')
    if g['goals']!=['determine periodicity on original real domain','find least positive period if it exists']:
        raise Unsupported('Unknown source period requirement')
    raw,ctx=parsed(text);conditions=domain_conditions(raw)
    restrictions=[g for g in conditions if not global_guard(g,'x',ctx)]
    def answer(period, argument, **evidence):
        return proof('scalar_period_lattice',dict(periodic=period is not False,
                     least_positive_period=None if period is False else period),argument,original=raw,
                     source_guards=conditions,**evidence)
    def symbol_period(coefficient):
        return m.mul(q(2/coefficient),m.PI)
    if raw[0]=='tan' and raw[1][0]=='sqrt' and raw[1][1]==x:
        return answer(False,'Точка 0 принадлежит области, а сдвиг на любой отрицательный T выводит её из области квадратного корня.')
    if (raw[0]=='sqrt' and raw[1][0]=='tan'
            and set(restrictions)<= {('nonzero',('cos',raw[1][1])),('nonnegative',raw[1])}):
        a,b=affine(raw[1][1],'x');a=m.num(a);b=m.pi_multiple(b)
        if a not in (None,0) and b is not None:
            return answer(m.div(m.PI,q(abs(a))),'Нули исходной функции образуют одну решётку с шагом π/|ω|, поэтому меньший сдвиг невозможен. Этот шаг сохраняет тангенс и его неотрицательную область.',
                          frequency=q(a),phase_in_pi=q(b))
    if raw[0]=='sin' and not ctx['parameters'] and not restrictions:
        try:c,b,a=polynomial_coefficients(raw[1],x,2)
        except Unsupported:pass
        else:
            if m.num(a) not in (None,0) and b==c==ZERO:
                return answer(False,'В точке 0 функция и её производная равны нулю. В любой другой точке, где синус квадратичной фазы обращается в нуль, производная отлична от нуля. Период сохранял бы оба значения.')
    if restrictions:
        modes=simple_phase_sum(raw,'tan');rows=[]
        if set(restrictions)!={('nonzero',('cos',phase)) for phase,_ in modes}:
            raise Unsupported('The raw domain contains additional restrictions beyond the active pole lattices')
        for phase,c in modes:
            a,b=affine(phase,'x');a,b=m.num(a),m.pi_multiple(b)
            if a in (None,0) or b is None:
                raise Unsupported('Unproved rational phase lattice or overlap')
            rows.append((abs(1/a),(F(1,2)-b)/a,-c/a))
        for (u,a,k),(v,b,l) in combinations(rows,2):
            if k==l or ((a-b)/rational_gcd([u,v])).denominator==1:
                raise Unsupported('The pole lattices do not have distinct principal parts')
        common=F(lcm(*(row[0].numerator for row in rows)),gcd(*(row[0].denominator for row in rows)))
        return answer(m.mul(q(common),m.PI),
            'Сдвиг сохраняет полюса и коэффициенты при обратном расстоянии до них. Непересекающиеся решётки с разными коэффициентами сохраняются каждая отдельно. Пересечение групп их периодов даёт наименьший положительный период.',
            pole_lattices=[dict(step=q(a),offset=q(b),residue=q(c)) for a,b,c in rows])
    modes,_,steps=harmonic_modes(dict(kind='integrate',integrand=text,variable='x',parameters=ctx['parameters']))
    if any(a!=ZERO or len(p)!=1 for (a,b),p in modes.items()):
        raise Unsupported('The collected modes are not a finite Fourier sum')
    rows={b:p[0] for (a,b),p in modes.items() if b!=ZERO and p[0]!=(ZERO,ZERO)}
    if not rows:
        return answer('does_not_exist_for_constant','У постоянной функции каждый положительный сдвиг является периодом.')
    unit=next(iter(rows));ratios={w:m.num(m.div(w,unit)) for w in rows}
    if None in ratios.values():
        if ctx['parameters'] or any(not any(m.nonzero(z,ctx) for z in c) for c in rows.values()):
            raise Unsupported('The active incommensurable frequencies are not proved')
        def irrational(w,v):
            square=m.num(m.simplify(m.power(m.div(w,v),2)))
            return (square is not None and square>0 and
                    (isqrt(square.numerator)**2!=square.numerator or isqrt(square.denominator)**2!=square.denominator))
        if not any(irrational(u,v) for u,v in combinations(rows,2)):
            raise Unsupported('No exact independence over integer multiples of the frequencies')
        return answer(False,'Линейная независимость комплексных экспонент с разными частотами вынуждает каждую ненулевую моду сохранять фазу. Для пары с иррациональным отношением частот общего положительного сдвига нет.',
                      modes=list(rows.items()))
    factors={r for r in ratios.values() if r>0}
    admissible=[c for w,c in rows.items() if ratios[w]>0]
    if not factors or len(admissible)!=len(factors):
        raise Unsupported('The independent frequency pairs are unresolved')
    common=rational_gcd(factors)
    least=m.div(symbol_period(common),m.simplify(('abs',unit)))
    if m.nonzero(unit,ctx) and all(any(m.nonzero(e,ctx) for e in c) for c in admissible):
        return answer(least,'Линейная независимость экспонент требует, чтобы сдвиг сохранял фазу каждой активной частоты. Общий шаг вычисляется по рациональному НОД частот.',
                      modes=list(rows.items()),frequency_gcd=q(common),basis=unit,steps=steps)
    if len(admissible)==1:
        real,imag=admissible[0]
        condition=source(unit)+'!=0 and ('+source(real)+'!=0 or '+source(imag)+'!=0)'
        return proof('scalar_period_lattice',dict(periodic=True,cases=[
            dict(condition=condition,least_positive_period=least),
            dict(condition='otherwise',least_positive_period='does_not_exist_for_constant')]),
            'Для одной активной пары частот наименьший положительный сдвиг равен 2π, делённым на модуль частоты. При нулевой частоте или нулевой амплитуде функция постоянна, так что наименьшего положительного периода нет.',
            original=raw,modes=list(rows.items()),basis=unit,original_guards=conditions)
    raise Unsupported('More than one undetermined active Fourier pair remains')


def abstract_period(task, kind):
    g=task['goal']
    if kind=='dirichlet_function_period_proof':
        literal='Для функции Дирихле chi(x)=1 при рациональном x,0 при иррациональном x доказать, что периодом является любое рациональное число.'
        packet(task,{'definition','goal'},literal)
        if g!=dict(definition='chi(x)=1 iff x rational, else0',
                   goal='prove every positive rational is a period; rational shift identity for all rational shifts'):
            raise Unsupported('The rational indicator and requested shifts must agree')
        return proof('scalar_period_lattice',dict(translations='Q',positive_periods='Q∩(0,+inf)',least=None),
            'Для рационального T условие x+T∈Q равносильно x∈Q по сложению и вычитанию. Иррациональный T меняет значение в нуле, поэтому других сдвигов нет. Рациональные положительные периоды можно уменьшать делением на два.')
    if kind=='commensurate_period_arithmetic_proof':
        packet(task,{'hypotheses','goals'},'Доказать, что сумма и произведение двух периодических функций на общем множестве E с соизмеримыми периодами также периодичны.')
        if g!=dict(hypotheses=['f,g share domain E','periods T1,T2>0 are commensurate'],
                   goals=['periodicity of f+g','periodicity of f*g']):
            raise Unsupported('The same invariant domain and commensurate periods are required')
        return proof('scalar_period_lattice',dict(common_period='q*T1=p*T2 when T1/T2=p/q',
            preserves=['f+g','f*g'],domain='E'),
            'Положительные целые кратные периодов сохраняют область и значения по последовательным сдвигам в обе стороны. При соизмеримости два таких кратных совпадают. Сумма и произведение сохраняются тем же сдвигом.')
    if kind=='antiperiod_implies_period_proof':
        packet(task,{'hypothesis','conclusion'},'Если f(x+T)=-f(x), T>0 (антипериодичность), доказать, что f периодична с периодом2*T.')
        if g!=dict(hypothesis='f(x+T)=-f(x), T>0',conclusion='f(x+2*T)=f(x)'):
            raise Unsupported('A global antiperiodic identity is required')
        return proof('scalar_period_lattice',dict(period='2*T',
            domain='R, or a source domain invariant under both shifts by T',
            caveat='forward invariance alone gives only the forward shift identity'),
            'Применяем антипериодичность второй раз к x+T и получаем f(x+2T)=−f(x+T)=f(x). На всей прямой подстановка x−2T даёт обратный сдвиг. На неполной области нужно также сохранить её обратным сдвигом, чтобы назвать 2T периодом в принятом определении.')
    if kind=='scaled_period_factorization':
        packet(task,{'domain','hypothesis','parameters','goal'},
               'Если f на R удовлетворяет f(x+T)=k*f(x), где k,T положительны, доказать f(x)=a^x*phi(x), где a постоянна, phi периодична с периодомT.',
               ['k>0','T>0'])
        if g!=dict(domain='R',hypothesis='f(x+T)=k*f(x)',parameters=['k','T'],
                   goal='construct constant a and T-periodic phi with f(x)=a^x*phi(x)'):
            raise Unsupported('The multiplicative translation data do not match')
        return proof('scalar_period_lattice',dict(base='exp(ln(k)/T)',periodic_factor='f(x)/a^x',factor_period='T'),
            'Положительные k и T дают положительное основание a с равенством a^T=k. Деление сдвинутой функции на a^(x+T) сокращает общий множитель k. Исходная прямая сохраняется обоими сдвигами.')
    packet(task,{'domain','hypotheses','goal'},task.get('source_statement'))
    if g['domain']!='R':
        raise Unsupported('The two reflections must act on the entire domain')
    variants=[
        (['f(2*a-x)=f(x)','f(2*b-x)=f(x)','b>a'],'prove periodicity',
         'Доказать: график f на R, симметричный относительно вертикальных осей x=a,x=b, b>a, задаёт периодическую функцию.',
         dict(period='2*(b-a)'), 'Композиция отражений x↦2a−x и x↦2b−x переносит абсциссу на 2(b−a) и сохраняет ординату. Это положительный период.'),
        (['central symmetry about(a,y0) and(b,y1)','b>a'],
         'prove that f is a sum of linear and periodic functions and that f is periodic when y0=y1',
         'Доказать: если график f на R симметричен относительно A(a,y0),B(b,y1), b>a, то f есть сумма линейной и периодической функций; при y0=y1 функция периодична.',
         dict(slope='(y1-y0)/(b-a)',periodic_part='f(x)-slope*x',period='2*(b-a)',equal_ordinates_case='slope=0'),
         'Две центральные симметрии сдвигают график на вектор (2(b−a),2(y1−y0)). Вычитание линейной функции с отношением этих сдвигов оставляет чистый горизонтальный перенос. При равных ординатах наклон равен нулю.'),
        (['central symmetry about(a,y0)','vertical symmetry about x=b','b!=a'],'prove periodicity',
         'Доказать: график f на R, симметричный относительно точки A(a,y0) и прямой x=b, b!=a, задаёт периодическую функцию.',
         dict(period='4*abs(b-a)'), 'Композиция центрального отражения и отражения в прямой сдвигает аргумент и заменяет f на 2y₀−f. Двойное применение восстанавливает ординату и даёт ненулевой сдвиг. Его модуль является периодом.'),
    ]
    for assumptions,goal,literal,value,argument in variants:
        if g['hypotheses']==assumptions and g['goal']==goal:
            statement(task,literal)
            return proof('scalar_period_lattice',value,argument,hypotheses=assumptions)
    raise Unsupported('The original reflection hypotheses require a different composition')


def limit_language(task, kind):
    g=task['goal']
    finite_modes=('both','left','right')
    tails=('magnitude_infinity','negative_infinity','positive_infinity')
    if kind=='limit_definition_and_examples':
        a,mode,target=g['point'],g['side'],g['target']
        keys={'point','side','target','goals'}
        expected=f'Сформулировать через неравенства lim_{{x->{a} {mode}}}f(x)={target}. Привести пример.'
        goals=EPSILON_GOALS
    elif kind=='infinity_limit_definition_and_examples':
        a,mode,target=None,g['input_approach'],g['target']
        keys={'input_approach','target','goals'}
        expected=f'Сформулировать через неравенства lim_{{x->{mode}}}f(x)={target} и привести пример.'
        goals=EPSILON_GOALS
    elif kind=='infinite_point_limit_definition_and_examples':
        a,mode,target=g['input_point'],g['input_side'],g['target']
        keys={'input_point','input_side','target','goals'}
        expected=f'Сформулировать неравенствами предел при x->{a} {mode} со значением {target} и привести пример.'
        goals=['E-delta definition','corresponding example']
    elif kind=='infinite_tail_definition_and_examples':
        a,mode,target=None,g['input_approach'],g['target']
        keys={'input_approach','target','goals'}
        expected=f'Сформулировать неравенствами предел при x->{mode} со значением {target} и привести пример.'
        goals=['E-M definition','corresponding example']
    else:
        a,mode=g['input_point'],g['input_approach']
        target,direction=g['output_approach'].split(' from ')
        keys={'input_point','input_approach','output_approach','goals'}
        expected=f'Сформулировать через неравенства y=f(x)->{target} {direction} при x->{mode}; привести пример.'
        goals=['quantified strict one-sided value approach','corresponding example']
    packet(task,keys,expected)
    if g['goals']!=goals or mode not in (*finite_modes,*tails) or (mode in finite_modes)!=(a is not None):
        raise Unsupported('The original directions and example obligations disagree')
    if a is not None and (not isinstance(a,str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',a) or a=='x'):
        raise Unsupported('Need a generic finite reference point')
    large=kind in ('infinite_point_limit_definition_and_examples','infinite_tail_definition_and_examples')
    directed=kind=='directed_value_limit_definition_and_examples'
    if large and target not in tails or not large and (not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',target)
                                                       or target in (a,'x')):
        raise Unsupported('The value is not of the original finite or infinite type')
    delta,distance='δ',f'|x−{a}|'
    input_condition=(
        (f'0<{distance}<δ' if mode=='both' else f'0<{a}−x<δ' if mode=='left' else f'0<x−{a}<δ')
        if a is not None else ('|x|>M' if mode==tails[0] else 'x<−M' if mode==tails[1] else 'x>M'))
    if a is None:delta,distance='M','|x|'
    quantifier=('E' if large else 'ε')+'>0'
    sign=1
    if large:
        magnitude=target==tails[0]
        if target==tails[1]:sign=-1
        output_condition='|f(x)|>E' if magnitude else 'f(x)<−E' if sign<0 else 'f(x)>E'
        if a is not None:
            witness=f'{"−" if sign<0 else ""}1/(x−{a})²'
            threshold='1/√E'
        else:
            witness='−x²' if sign<0 else 'x²'
            threshold='√E'
        warrant=f'Модуль примера равен {"обратному квадрату" if a is not None else "квадрату"} расстояния {distance}; выбранный порог обеспечивает требуемое строгое неравенство.'
    else:
        if directed and direction not in ('above','below'):
            raise Unsupported('The output direction is not specified')
        sign=-1 if directed and direction=='below' else 1
        output_condition=f'0<f(x)−{target}<ε' if directed and sign==1 else f'0<{target}−f(x)<ε' if directed else f'|f(x)−{target}|<ε'
        if a is not None:
            witness=target+('−' if sign<0 else '+')+distance
            threshold='ε'
        else:
            witness=target+('−' if sign<0 else '+')+'1/x²'
            threshold='1/√ε'
        warrant=f'Модуль разности с {target} равен {distance if a is not None else "1/x²"} и меньше ε при выбранном пороге.'
        if directed:warrant+=' Эта разность имеет требуемый ненулевой знак во всей проверяемой области.'
    return proof('quantified_limits',dict(definition=dict(for_all=quantifier,exists=delta+'>0',
        for_all_inputs='x in the original domain satisfying '+input_condition,implies=output_condition,
        approach_nonvacuity='the original domain has points arbitrarily far in the required tail or arbitrarily close on each required side'),
        example=dict(expression=witness,threshold=threshold,domain='R outside the displayed denominator zeros')),
        'Сначала задаём произвольную точность или высоту, затем выбираем порог по аргументу. '+warrant,
        original_directions=[mode,target,direction if directed else None])


def limit_table(task, kind):
    g=task['goal'];x=('v','x')
    text=g['expression'];a=g['approach']['point']
    if g['approach']!=dict(point=a,side='both'):
        raise Unsupported('The source requires both punctured sides')
    raw_point=m.parse(a,None)
    point=m.num(m.simplify(raw_point))
    if point is None or not m.constant_defined(raw_point,m.context({})):
        raise Unsupported('An exact rational approach point is required')
    finite=kind=='epsilon_delta_proof_and_table'
    labels='table_epsilons' if finite else 'table_E'
    thresholds=list(map(F,g[labels]))
    if not thresholds or min(thresholds)<=0:
        raise Unsupported('All specified thresholds must be positive')
    raw,ctx=parsed(text)
    if ctx['parameters']:
        raise Unsupported('No additional parameter is declared by the table')
    if finite:
        literal=task.get('source_statement')
        label=literal.split('epsilon=')[-1].rstrip('.') if isinstance(literal,str) else ','.join(map(str,thresholds))
        if list(map(F,label.split(',')))!=thresholds:
            raise Unsupported('The numeric table differs from the source')
        packet(task,{'expression','approach','target','method_requirement',labels,'goals'},
               f'С помощью epsilon-delta рассуждений доказать lim_{{x->{a}}}{text}={g["target"]}. Заполнить таблицу epsilon={label}.')
        if g['method_requirement']!='epsilon-delta proof' or g['goals']!=['universal delta(epsilon) proof','all exact table entries']:
            raise Unsupported('The source prescribes a quantified proof and its table')
        if domain_conditions(raw):
            raise Unsupported('A guard on the entire approach neighborhood is unproved')
        p,d=poly.rf(raw,'x')
        if len(d)!=1 or not d[0]:
            raise Unsupported('A polynomial difference estimate is required')
        from graphs import peval
        target=m.parse(g['target'],None)
        if m.num(target)!=peval(p,point)/d[0]:
            raise Unsupported('The stated target differs from the polynomial value')
        B=abs(point)+1
        C=max(F(1),sum(i*abs(c/d[0])*B**(i-1) for i,c in enumerate(p) if i))
        result=dict(delta='min(1,epsilon/C)',constant=q(C),table=[(q(e),q(min(F(1),e/C))) for e in thresholds])
        return proof('quantified_limits',result,
            'Разность степеней делится на x−a. Если |x−a|<1, каждый частный коэффициент ограничен суммой произведений степеней с модулем не больше |a|+1. Точная оценка C умножается на |x−a|, и выбранная δ даёт строгое неравенство.',
            original=raw,point=q(point),comparison_radius=ONE,absolute_base_bound=q(B),target=target)
    packet(task,{'expression','approach','target','method_requirement',labels},
          f'На языке E-delta доказать lim_{{x->{a}}}{text}=+infinity. Заполнить E='+','.join(g[labels])+'.')
    if g['target']!='positive_infinity' or g['method_requirement']!='E-delta proof':
        raise Unsupported('The infinite target or stated proof differs')
    if raw[0]!='div' or raw[2][0]!='pow' or raw[2][2]<=0 or raw[2][2]%2 or domain_conditions(raw)!=[('nonzero',raw[2])]:
        raise Unsupported('A positive reciprocal of an even power is required')
    C=m.num(m.simplify(raw[1]));n=raw[2][2]
    if C is None or C<=0 or not (same_value(raw[2][1],m.add(x,q(-point))) or same_value(raw[2][1],m.add(q(point),m.neg(x)))):
        raise Unsupported('The pole must have the given center and an even positive exponent')
    def threshold(e):
        return m.simplify(('sqrt',q(C/e))) if n==2 else ('rpow',q(C/e),q(1,n))
    return proof('quantified_limits',dict(delta='(C/E)^(1/n)',constant=q(C),degree=n,
                 table=[(q(e),threshold(e)) for e in thresholds]),
                 'Из 0<|x−a|<δ следует 0<|x−a|^n<C/E для данного чётного n. Обращение положительных величин даёт C/|x−a|^n>E.',
                 original=raw,point=q(point))


def monotonicity(task, kind):
    g=task['goal'];x=('v','x')
    if kind=='inequality_logarithm_conditions':
        packet(task,{'goal'},'Можно ли почленно логарифмировать неравенство?')
        if g['goal']!='state exact real-domain and base conditions for applying a logarithm to an inequality':
            raise Unsupported('Unknown logarithmic order question')
        return proof('scalar_order_bounds',dict(real_domain='both sides > 0; base a>0 and a!=1',
             keeps_relation='a>1',reverses_relation='0<a<1',equal_arguments_stay_equal=True),
             'Логарифм — обратная функция к a^x. Для a>1 степенная показательная функция строго возрастает, для 0<a<1 строго убывает. Обратная сохраняет соответствующее направление монотонности.')
    if kind=='ordered_composition_sandwich':
        packet(task,{'hypotheses','conclusion'},'Пусть phi,psi,f монотонно возрастают. Доказать: если phi(x)<=f(x)<=psi(x), то phi(phi(x))<=f(f(x))<=psi(psi(x)).')
        if g!=dict(hypotheses=['phi,f,psi are increasing','phi(t)<=f(t)<=psi(t) on the common relevant domain'],
                   conclusion='phi(phi(x))<=f(f(x))<=psi(psi(x))'):
            raise Unsupported('Need a pointwise order on the entire common domain of composition')
        chain=['phi(phi(x))','phi(f(x))','f(f(x))','psi(f(x))','psi(psi(x))']
        return proof('scalar_order_bounds',dict(chain=chain,condition='all inner values belong to the relevant common domain'),
                     'Крайние переходы следуют из монотонности крайних функций. Два средних сравнения — исходный порядок функций в общей точке f(x).')
    text=g['expression'];assumptions=task.get('assumptions',[])
    suffix=' ('+', '.join(assumptions)+')' if assumptions else ''
    packet(task,{'expression','goal'},f'Исследовать на монотонность f(x)={text}{suffix}.',assumptions)
    if g['goal']!='classify all parameter and domain cases':
        raise Unsupported('The requested collection of monotonicity cases is unresolved')
    raw,ctx=parsed(text,assumptions)
    def result(cases,arg,**data):
        return proof('scalar_order_bounds',dict(cases=cases),arg,original=raw,source_guards=domain_conditions(raw),**data)
    def compare(e,form,domain='R',extra=()):
        v=m.sign(e,ctx);rows=[]
        for sign,op,label in ((1,'>','increasing'),(-1,'<','decreasing'),(0,'=','constant')):
            if v not in (None,sign):continue
            labels=[*extra]+([source(e)+op+'0'] if v is None else [])
            direction=form.get(label,label)
            rows.append(dict(conditions=labels,domain=domain,monotonicity=direction))
        return rows
    if raw[0]=='rpow' and raw[2]==x and not m.variable_in(raw[1]) and m.sign(raw[1],ctx)==1:
        return result(compare(m.add(raw[1],q(-1)),{}),
            'При x₂>x₁ отношение значений равно a^(x₂−x₁). Для положительного a оно больше, меньше или равно единице вместе с a.')
    if raw[0]=='div' and domain_conditions(raw)==[('nonzero',raw[2])]:
        b,a=polynomial_coefficients(raw[1],x,1);d,c=polynomial_coefficients(raw[2],x,1)
        determinant=m.add(m.mul(a,d),m.neg(m.mul(b,c)))
        cs,ds=m.sign(c,ctx),m.sign(d,ctx);cases=[]
        if cs!=0:
            pole=m.div(m.neg(d),c)
            cases.extend(compare(determinant,{'increasing':'increasing on each component only',
                                  'decreasing':'decreasing on each component only'},
                                  dict(real_except=pole),[source(c)+'!=0'] if cs is None else []))
        if cs in (None,0):
            zeros=[source(c)+'=0'] if cs is None else []
            if ds!=0:
                extra=zeros+([source(d)+'!=0'] if ds is None else [])
                cases.extend(compare(m.mul(a,d),{},extra=extra))
            if ds in (None,0):
                cases.append(dict(conditions=zeros+([source(d)+'=0'] if ds is None else []),domain='empty'))
        return result(cases,'Разность значений равна (ad−bc)(x₂−x₁)/[(cx₁+d)(cx₂+d)]. На одной компоненте произведение знаменателей положительно, а по разные стороны полюса отрицательно. При c=0 остаются линейная функция либо пустая область.',
                      determinant=determinant,denominator=[d,c])
    if not all(global_guard(g,'x',ctx) for g in domain_conditions(raw)):
        raise Unsupported('The original monotonicity domain remains unresolved')
    c,b,a,u=polynomial_coefficients(raw,x,3)
    if u!=ZERO and a==b==ZERO:
        return result(compare(u,{}),'Куб сохраняет строгий порядок на всей прямой. Знак множителя задаёт направление, нулевой множитель даёт постоянную функцию.',
                      coefficients=[c,b,a,u])
    if u!=ZERO:
        raise Unsupported('A general cubic needs separate critical-point isolation')
    rows=[]
    if a!=ZERO:
        h=m.div(m.neg(b),m.mul(q(2),a));sgn=m.sign(a,ctx)
        for s,op,label in ((1,'>',['decreasing','increasing']),(-1,'<',['increasing','decreasing'])):
            if sgn not in (None,s):continue
            rows.append(dict(conditions=[source(a)+op+'0'] if sgn is None else [],vertex=h,
                intervals=['left through vertex','right from vertex'],monotonicity=label))
        if sgn is None:rows.extend(compare(b,{},extra=[source(a)+'=0']))
    else:rows.extend(compare(b,{}))
    return result(rows,'При ненулевом квадратном коэффициенте выделяем квадрат около вершины. Квадрат убывает слева от вершины и возрастает справа. При нулевом квадратном коэффициенте достаточно знака наклона прямой.',
                  coefficients=[c,b,a])


def boundedness(task, kind, request):
    g=task['goal']
    if kind=='finite_but_locally_unbounded_proof':
        packet(task,{'definition','goals'},'Показать: f(x)=n, если x=m/n в несократимом виде,n>0; f(x)=0 для иррационального x. Функция конечна, но не ограничена ни в какой окрестности любой точки.')
        if g!=dict(definition='rational reduced m/n -> n; irrational ->0',
                   goals=['finite at every real point','unbounded on every neighborhood of every real point']):
            raise Unsupported('The unique reduced-denominator rule is required')
        return proof('scalar_order_bounds',dict(finite_everywhere=True,bounded_on_any_neighborhood=False),
            'Несократимая дробь с положительным знаменателем единственна, и её знаменатель конечен. В любом ограниченном открытом интервале лишь конечное число рациональных чисел имеют знаменатель ≤N, потому что каждый из N знаменателей допускает конечное число числителей. Плотность рациональных чисел даёт в том же интервале значение со знаменателем >N.')
    if kind=='local_global_boundedness_with_examples':
        domain=g['domain']
        packet(task,{'domain','hypothesis','goals'},f'Если f определена и локально ограничена в каждой точке {domain}, обязательно ли она ограничена на всём множестве? Привести примеры.')
        if g['hypothesis']!='f defined and locally bounded at each domain point' or g['goals']!=['decide global boundedness','give corresponding examples']:
            raise Unsupported('The local boundedness hypothesis or example requirements differ')
        if domain=='open interval(a,b)':
            return proof('scalar_order_bounds',dict(necessarily_bounded=False,unbounded_example='1/(x-a)',
                    bounded_example='f(x)=0',domain='a<x<b'),
                'Для каждого x внутри интервала можно взять радиус меньше половины x−a, и на такой окрестности знаменатель отделён от нуля. При приближении справа к a значения неограниченно растут. Нулевая функция показывает, что ограниченность также возможна.')
        if domain=='closed segment[a,b]':
            return proof('scalar_order_bounds',dict(necessarily_bounded=True,example='f(x)=x on [a,b]'),
                'Относительные окрестности локальной ограниченности покрывают компактный сегмент. Берём конечное подпокрытие и максимум конечного набора локальных оценок. Для примера f(x)=x подходит оценка max(|a|,|b|).')
        raise Unsupported('The original interval compactness is unproved')
    if kind=='monotone_bounds_question':
        packet(task,{'domain','hypothesis','goal'},'f определена и монотонно возрастает на[a,b]. Чему равны нижняя и верхняя грани?')
        if g!=dict(domain='[a,b]',hypothesis='f is increasing',goal='determine infimum and supremum'):
            raise Unsupported('The monotone order or attainment hypothesis differs')
        return proof('scalar_order_bounds',dict(infimum='f(a)',supremum='f(b)',attained=True),
                     'Для каждой точки x сегмента монотонность даёт f(a)≤f(x)≤f(b). Обе границы сами являются значениями исходной функции.')
    if kind=='bounds_sum_proof_with_examples':
        packet(task,{'domain','goals'},'Для нижней m и верхней M граней на(a,b) доказать m[f1+f2]>=m[f1]+m[f2], M[f1+f2]<=M[f1]+M[f2]. Построить примеры1)равенств;2)строгих неравенств.', ['a<b'])
        if g!=dict(domain='(a,b)',goals=['prove both bound inequalities','construct equality examples','construct strict examples']):
            raise Unsupported('Both inequalities and the two kinds of examples are required')
        return proof('scalar_order_bounds',dict(lower='inf(f+g)>=inf(f)+inf(g)',upper='sup(f+g)<=sup(f)+sup(g)',
            equality_example=['x','x'],strict_example=['x','-x']),
            'Суммируем поточечные нижние и верхние оценки. При одинаковых функциях x оба предельных края совпадают. Для x и −x сумма нулевая, а суммы нижних и верхних граней равны a−b<0 и b−a>0.')
    text=g['expression'];x=('v','x')
    if kind=='boundedness_proof':
        packet(task,{'expression','domain','goal'},f'Показать, что f(x)={text} ограничена на R.')
        if g['domain']!='R' or g['goal']!='prove a finite global bound':
            raise Unsupported('A different bound or domain is requested')
        raw,ctx=parsed(text)
        if ctx['parameters'] or not all(global_guard(g,'x',ctx) for g in domain_conditions(raw)):
            raise Unsupported('No whole-real-domain rational bound')
        p,d=poly.rf(raw,'x')
        if d[-1]<0:p,d=tuple(-c for c in p),tuple(-c for c in d)
        if len(p)>len(d) or not d[0] or any(c<0 or i%2 and c for i,c in enumerate(d)):
            raise Unsupported('Asymptotic denominator domination on the entire line has not been proved')
        bound=sum(map(abs,p))/min(d[0],d[-1])
        return proof('scalar_order_bounds',dict(absolute_bound=q(bound)),
            'Если |x|≤1, модуль числителя не превосходит суммы модулей коэффициентов, а знаменатель не меньше свободного члена. Вне этого интервала сравниваем обе части со старшей чётной степенью. Это даёт одну конечную оценку на всей прямой.',
            numerator=list(map(q,p)),denominator=list(map(q,d)))
    if kind=='infimum_supremum_proof':
        lower,upper=[re.fullmatch(r'prove '+v+r'(.+)',p)[1] for v,p in zip(('infimum','supremum'),g['goals'],strict=True)]
        packet(task,{'expression','domain','goals'},f'Показать, что f(x)={text} на0<=x<infinity имеет нижнюю грань{lower} и верхнюю грань{upper}.')
        if g['domain']!='[0,infinity)':
            raise Unsupported('The asserted interval differs from the available proof')
        child=request('Точные грани образа на полуоси',dict(kind='function_bounds',function=text,variable='x',
            given_domain='[0,+infinity)',requested_output=['infimum','supremum']))['value']
        if not all(same_value(m.parse(t,None),freeze(child[k]['value'])) for t,k in
                   zip((lower,upper),('infimum','supremum'))):
            raise Unsupported('The printed claim differs from the computed bounds')
        return proof('scalar_order_bounds',child,'Вычисляем точный образ функции на исходной полуоси и сохраняем достижимость каждой границы.')
    raw,ctx=parsed(text)
    if ctx['parameters']:
        raise Unsupported('An extra phase parameter remains')
    if kind=='unbounded_not_magnitude_infinite_proof':
        packet(task,{'expression','domain','goals'},f'Показать: f(x)={text} не ограничена в любой окрестности0, но не бесконечно большая при x->0.')
        if g['domain']!='R \\ {0}' or g['goals']!=['unbounded in every punctured neighborhood of0','not abs(f(x))->infinity at0']:
            raise Unsupported('The two punctured neighborhood requirements differ')
        if raw[0]!='div' or raw[2]!=x or raw[1][0] not in ('cos','sin'):
            raise Unsupported('A reciprocal-phase wave divided by x is required')
        wave,phase=raw[1];constant=reciprocal_constant(phase,x)
        a,b=('2πn','2πn+π/2') if wave=='cos' else ('2πn+π/2','2πn')
        return proof('scalar_order_bounds',dict(unbounded_on_neighborhoods=True,magnitude_infinite_limit=False),
            'Два семейства точек подставляют в исходную фазу значения с модулем волны 1 и 0. В первой серии модуль функции уходит в бесконечность, во второй он тождественно нулевой.',
            growth_sequence=source(constant)+'/('+a+')',zero_sequence=source(constant)+'/('+b+')')
    packet(task,{'expression','domain','goal'},f'Исследовать на ограниченность f(x)={text} в интервале0<x<epsilon.',['epsilon>0'])
    if g['domain']!='(0,epsilon)' or g['goal']!='determine boundedness above and below' or raw[0]!='mul':
        raise Unsupported('The interval and signed amplitude requirements differ')
    logarithm=('ln',x)
    if logarithm not in raw[1:]:
        raise Unsupported('No logarithmic amplitude')
    other=raw[2] if raw[1]==logarithm else raw[1]
    if other[0]!='pow' or other[2]<=0 or other[2]%2 or other[1][0] not in ('cos','sin'):
        raise Unsupported('No nonnegative periodic factor bounded by one')
    wave,phase=other[1];constant=reciprocal_constant(phase,x)
    denominator='2πn' if wave=='cos' else '2πn+π/2'
    return proof('scalar_order_bounds',dict(bounded_above=True,upper_bound='max(0,ln(epsilon))',bounded_below=False),
        'На всём интервале множитель лежит между нулём и единицей, а логарифм не больше ln ε. На положительной последовательности ниже ε множитель равен единице, и логарифм уходит вниз.',
        full_amplitude_sequence=source(m.simplify(('abs',constant)))+'/('+denominator+')')


def reciprocal_constant(phase,x):
    if phase[0]!='div' or phase[2]!=x or m.variable_in(phase[1]):
        raise Unsupported('An exact single reciprocal phase is required')
    ctx=m.context(dict(variable=x[1]))
    c=m.simplify(phase[1])
    if not m.constant_defined(phase[1],ctx) or not m.nonzero(c,ctx):
        raise Unsupported('The reciprocal phase numerator is not real nonzero')
    return c


def oscillation(task, request):
    from graphs import rational_roots
    from operations import expression_positions
    from ray_proofs import compare_scalar
    g=task['goal'];text=g['expression'];x=('v','x')
    packet(task,{'expression','point','goal','domain'},
           f'Используя omega0=lim_{{h->0}}omega_h[f] наabs(x)<=h, определить колебание в0 для {text}.')
    if (g['point']!='0' or g['goal']!='oscillation limit of neighborhood supremum minus infimum'
            or g['domain']!='original domain intersected with the neighborhood'):
        raise Unsupported('The source oscillation definition or reference point differs')
    raw,ctx=parsed(text)
    if ctx['parameters']:
        raise Unsupported('A parameterized range needs additional branch proofs')
    def answer(lower, upper, explanation, **data):
        width='+inf' if upper=='+inf' or lower=='-inf' else m.simplify(m.add(upper,m.neg(lower)))
        return proof('scalar_point_oscillation',dict(liminf=lower,limsup=upper,oscillation=width),explanation,
                     original_guards=domain_conditions(raw),original=raw,**data)
    waves=set()
    for _,e in expression_positions(raw):
        if e[0] not in ('sin','cos'):continue
        try:c=reciprocal_constant(e[1],x)
        except Unsupported:continue
        waves.add((e,c))
    if waves:
        if len(waves)!=1 or any(r!='nonzero' or not same_value(e,x) and not same_value(e,m.power(x,2))
                                for r,e in domain_conditions(raw)):
            raise Unsupported('The wave range is not independent of the full punctured domain')
        wave,frequency=waves.pop();y=('v','__phase')
        num,den=m.rational_form(shifted(raw,wave,y))
        denominator=poly.univariate_coefficients(den,x)
        if not denominator or not any(denominator):
            raise Unsupported('The phase polynomial has a variable denominator')
        by_power={}
        for mon,c in num.items():
            if any(atom not in (x,y) or k<0 for atom,k in mon):
                raise Unsupported('The phase range is mixed with a nonpolynomial term')
            power=dict(mon).get(y,0)
            by_power.setdefault(power,{})[tuple((a,k) for a,k in mon if a!=y)]=c
        den_degree=next(i for i,c in enumerate(denominator) if c)
        leads={};order={}
        for power,terms in sorted(by_power.items()):
            series=poly.univariate_coefficients(terms,x)
            degree=next(i for i,c in enumerate(series) if c)
            order[power]=degree-den_degree
            leads[power]=series[degree]/denominator[den_degree]
        if any(k<0 for k in order.values()):
            if len(order)!=1:
                raise Unsupported('Mixed unbounded amplitudes need separate comparisons')
            power,n=next(iter(order.items()))
            if power<=0 or power%2 or n%2 or leads[power]<=0:
                raise Unsupported('The growing envelope is not nonnegative on both sides')
            return answer(ZERO,'+inf',
                'Чётная степень волны неотрицательна, а ведущий коэффициент амплитуды положителен на обеих сторонах. Волна принимает нулевые и единичные значения вдоль сколь угодно малых точек, а при единичных значениях амплитуда растёт без границы.',
                growth_order=n,phase=wave,frequency=frequency,coefficient=q(leads[power]))
        p=tuple(leads[i] if order.get(i)==0 else F(0) for i in range(1+max(order,default=0)))
        p=poly.trim(p);derivative=tuple(i*a for i,a in enumerate(p) if i)
        extrema=[line.Quadratic(-1),line.Quadratic(1)]
        if derivative:
            extrema.extend(p for p in rational_roots(derivative) if line.compare(p,line.Quadratic(-1))>0 and line.compare(p,line.Quadratic(1))<0)
        values=[line.peval(p,z) for z in extrema]
        lower=upper=values[0]
        for v in values[1:]:
            if line.compare(v,lower)<0:lower=v
            if line.compare(v,upper)>0:upper=v
        def expression(v):
            return q(v.a) if not v.b else m.add(q(v.a),m.mul(q(v.b),('sqrt',q(v.d))))
        return answer(expression(lower),expression(upper),
            'Коэффициенты многочлена по волне имеют конечные пределы, и сходимость равномерна при её значениях в [−1,1]. Каждое значение из этого отрезка реализуется на фиксированной фазе с добавлением 2πn. Грани предельного многочлена вычисляются по концам и стационарным точкам.',
            phase=wave,frequency=frequency,coefficient_limits=list(map(q,p)),
            critical_phase_values=list(map(expression,extrema)))
    def side(which):
        return freeze(request('Проверить одностороннюю грань '+which,dict(kind='compute_limit',
            goal=dict(variable='x',expression=text,approach=dict(point='0',side=which))))['value'])
    bounds=[side(which) for which in ('left','right')]
    at_point=shifted(raw,x,ZERO)
    if m.constant_defined(at_point,ctx):
        at_point=m.simplify(at_point)
    elif any(m.constant_defined(e,ctx) and
             (m.sign(e,ctx)==-1 and r!='nonzero' or m.sign(e,ctx)==0 and r!='nonnegative')
             for r,e in domain_conditions(at_point)):
        at_point=None
    else:
        raise Unsupported('Membership of the center in the original domain is unproved')
    from functools import cmp_to_key
    candidates=sorted(bounds+([] if at_point is None else [at_point]),key=cmp_to_key(compare_scalar))
    return answer(candidates[0],candidates[-1],'Оба односторонних предела получены на исходной области. Если центральная точка входит в область, её значение тоже участвует в сравнении. Минимум и максимум этих величин дают пределы граней стягивающихся окрестностей.',
                  directional_limits=bounds,source_value_at_center=at_point)


def geometric_order(task, request):
    g=task['goal'];obj=g['quantity']
    packet(task,{'figure','given','quantity','goal'},
           'Считая центральный угол AOB=x бесконечно малой1-го порядка(рис4), определить порядок '+obj+'.')
    if (g['figure']!='source figure4' or g['given']!='positive central angle x is first order'
            or g['goal']!='derive its infinitesimal order from the geometry'):
        raise Unsupported('The positive-angle geometry binding differs')
    plans={
        'chord AB':('2*R*sin(x/2)','Перпендикуляр из центра пополам делит хорду. Её половина равна R sin(x/2).'),
        'sagitta CD':('R*(1-cos(x/2))','Стрелка равна разности радиуса и удаления хорды от центра.'),
        'sector AOB area':('R^2*x/2','Площадь сектора пропорциональна центральному углу в радианах.'),
        'triangle ABC area':('R^2*sin(x/2)*(1-cos(x/2))','Половина произведения хорды на стрелку даёт площадь треугольника.'),
        'trapezoid ABB1A1 area':('R^2*(sin(x/2)+tan(x/2))*(1-cos(x/2))','На касательной основание равно 2R tan(x/2), на хорде 2R sin(x/2). Умножаем их полусумму на стрелку.'),
        'circular segment ABC area':('R^2*(x-sin(x))/2','Из площади сектора вычитаем площадь осевого треугольника с двумя сторонами R и углом x.'),
    }
    expression,construction=plans[obj]
    unit_expression=expression.replace('R','1')
    child=request('Вычислить первый ненулевой член нормированной геометрической величины',
                  dict(kind='leading_asymptotic_term',variable='x',expression=unit_expression,
                       approach=dict(point='0',side='right')))['value']
    if len(child)!=3 or child[0]!='leading_monomial':
        raise Unsupported('A positive leading power must be found')
    order,coefficient=freeze(child[1]),freeze(child[2]);r=('s','R')
    if m.num(order) is None or m.num(order)<=0 or m.sign(coefficient,m.context({}))!=1:
        raise Unsupported('The leading coefficient or infinitesimal order is unresolved')
    exponent=1 if obj in ('chord AB','sagitta CD') else 2
    return proof('geometric_leading_order',dict(order=order,coefficient=m.mul(m.power(r,exponent),coefficient),
                 expression=expression,source_radius='R>0',source_approach='x→0+'),
                 construction+' Делим длину на R или площадь на R² и находим первый ненулевой член при x→0 справа.')


def landau_algebra(task,kind):
    g=task['goal'];identity=g.get('identity')
    if kind=='asymptotic_equivalence_relation_proof':
        property=g['property'];claim=g['proposition']
        packet(task,{'property','proposition','goal'},f'Показать {property} свойства отношения~: {claim}.')
        rows={
            'reflexive':('phi~phi','Нулевая малая поправка даёт φ=(1+0)φ и сохраняет совпадающие нули.'),
            'symmetric':('phi~psi implies psi~phi','Пишем φ=(1+α)ψ, α→0. Множитель 1+α на проколотой окрестности отличен от нуля. Обращение даёт ψ=(1−α/(1+α))φ с новой малой поправкой.'),
            'transitive':('phi~psi and psi~chi imply phi~chi','Перемножение коэффициентов (1+α)(1+β) даёт эквивалентность φ и χ, поскольку α+β+αβ→0.'),
        }
        if property not in rows or rows[property][0]!=claim or g['goal']!='proof for arbitrary functions on a common punctured domain':
            raise Unsupported('The original equivalence statement differs')
        return proof('landau_factorization',dict(property=property,proved=True),rows[property][1])
    if kind=='Landau_symbol_algebra_proof':
        wording=('Пусть при x→a функция o(f(x)) произвольная функция более низкого порядка роста, '
                 'а O(f(x)) — произвольная функция того же порядка роста, f(x)>0. Показать '+identity+'.')
        packet(task,{'assumption','identity','goal','source_notation'},wording,['f(x)>0'])
        notation=dict(approach='x->a',exercise_o='arbitrary function of lower growth order than f',
            exercise_O='arbitrary function of the same growth order as f',
            section_O='eventual absolute upper bound by a fixed multiple',
            section_O_star='finite nonzero limit of the quotient on a punctured neighborhood where the denominator is nonzero')
        if (g['assumption']!='f(x)>0 near the common point' or g['source_notation']!=notation
                or g['goal']!='prove the full Landau rewrite interpretation'):
            raise Unsupported('The two notations and lower growth condition must agree with the source')
        rows={
            'o(o(f(x)))=o(f(x))':'Вложенная малая величина умножает f на произведение двух малых множителей. Обратно, при g=fη выбираем промежуточный член f√|η|. Отношение g к этому члену задаётся множителем sgn(η)√|η|, в том числе при η=0.',
            'O(o(f(x)))=o(f(x))':'Ограниченный множитель, умноженный на малый, остаётся малым. Общее обратное включение получается выбором промежуточного члена g и множителя 1.',
            'o(O(f(x)))=o(f(x))':'Малый множитель, умноженный на ограниченный, остаётся малым. Обратно, берём промежуточным членом саму f.',
            'O(O(f(x)))=O(f(x))':'Произведение двух ограниченных множителей ограничено. Для экземпляров одного порядка произведение множителей также отделено от нуля. Обратно, промежуточным членом берём f, а единичный множитель сохраняет её порядок.',
            'O(f(x))+o(f(x))=O(f(x))':'Сумма ограниченного и малого множителей ограничена. Если первый отделён от нуля, достаточно сузить окрестность, чтобы модуль второго был меньше половины нижней границы первого. Обратное включение получается добавлением нуля.',
        }
        argument=rows.get(identity)
        if argument is None:
            raise Unsupported('The typed composition of comparison classes is unavailable')
        return proof('landau_factorization',dict(identity=identity,proved=True,
            readings=['section upper bound','same order as comparable absolute sizes'],
            quotient_caveat='If O* is restricted to eventually nonzero comparison functions, require its punctured quotient domain separately.'),
            argument+' Вложенные классы образуются объединением по промежуточным представителям. Оценки через множители учитывают общие нули без деления на исчезающую функцию.')
    at_zero=g['approach']=='x->0';approach='x->0' if at_zero else 'x->+infinity'
    assumptions=['n>0']
    scalar='C*O(x^n)=O(x^n)'
    addition='O(x^n)+O(x^m)=O(x^n)'
    product='O(x^n)*O(x^m)=O(x^(n+m))'
    if identity==scalar:assumptions+=['C constant']+(['C!=0'] if at_zero else [])
    elif identity==addition:assumptions+=['n<m' if at_zero else 'n>m']
    elif identity!=product:raise Unsupported('Unknown power algebra statement')
    packet(task,{'approach','identity','goal'},f'Пусть {approach}, n>0. Показать {identity}.',assumptions)
    if g['approach']!=approach or g['goal']!='full asymptotic class proof':
        raise Unsupported('The comparison scales or power class requirement differs')
    if identity==scalar and not at_zero:
        return proof('landau_factorization',dict(printed_claim_holds=False,counterexample=dict(C=ZERO,n=ONE,missing_function='x',
                     reading='literal separate exercise; the preceding nonzero-constant condition is not repeated'),
            corrected_condition='C!=0'),
            'При напечатанных условиях можно взять C=0 и n=1. Тогда левый класс содержит только нуль, а правый содержит функцию x. При C≠0 умножение ограниченного коэффициента на C обратимо.')
    explanations={
        scalar:'Умножение или деление ограниченного множителя на фиксированное ненулевое C сохраняет ограниченность, что даёт оба включения.',
        addition:'Из напечатанного порядка показателей следует, что отношение второй шкалы к первой стремится к нулю. Сумма двух оценок имеет порядок не выше первой шкалы. Обратное включение получается нулём во втором слагаемом.',
        product:'В произведении перемножаются ограниченные коэффициенты и складываются показатели. Для обратного включения произвольный ограниченный коэффициент при x^(n+m) относим к первому множителю, а во втором используем коэффициент 1.',
    }
    return proof('landau_factorization',dict(identity=identity,proved=True,approach=approach,
                original_real_domain='each punctured side on which the comparison powers are real'),
                explanations[identity]+' Все сравнения делаются на общей действительной проколотой области степеней.')


def approach_conditions(raw,var,point,side,ctx):
    """Prove the original raw guards on an actual punctured interval or tail."""
    x=('v',var);fixed=('s',var)
    additional=[dict(symbol=var,relation='negative' if side=='left' else 'positive')]
    shell={**ctx,'parameters':[*ctx['parameters'],var],
           'assumptions':[*ctx['assumptions'],*additional]}
    guards=domain_conditions(raw)
    for rel,e in guards:
        if known_guard((rel,shifted(e,x,fixed)),shell) or global_guard((rel,e),var,ctx):
            continue
        try:p,d=poly.rf(e,var)
        except (poly.NotRational,poly.Undefined) as exc:
            raise Unsupported('A guard has not been proved on the approach domain') from exc
        def lead(p):
            indices=[i for i,u in enumerate(p) if u]
            if not indices:return 0,F(0)
            j=indices[-1] if point=='+inf' else indices[0]
            return j,p[j]
        i,a=lead(p);j,b=lead(d)
        if b==0:
            raise Unsupported('A raw domain guard has an identically zero denominator')
        sign=a*b*(-1 if side=='left' and (i-j)%2 else 1)
        if not (sign>0 or sign<0 and rel=='nonzero' or sign==0 and rel=='nonnegative'):
            raise Unsupported('A raw guard fails on the specified side')
    return guards


def bounded_ratio(raw,var,point,side,ctx):
    """Prove boundedness using exact Laurent orders and bounded wave factors."""
    from operations import expression_positions
    guards=approach_conditions(raw,var,point,side,ctx)
    x=('v',var)
    raw=shifted(raw,('abs',x),m.neg(x) if side=='left' else x)
    waves={e for _,e in expression_positions(raw) if e[0] in ('sin','cos','atan') and m.contains(e,x)}
    symbols={e:('s',f'__bounded_{i}') for i,e in enumerate(sorted(waves))}
    n,d=m.rational_form(m.substitute(raw,symbols))
    d=poly.univariate_coefficients(d,x)
    if not d or not any(d):
        raise Unsupported('An unbounded denominator wave or unproved parameter case remains')
    relevant=lambda seq:max(seq) if point=='+inf' else min(seq)
    j=relevant([i for i,c in enumerate(d) if c])
    for mon,c in n.items():
        if any(atom not in [x,*symbols.values()] or k<0 for atom,k in mon):
            raise Unsupported('A numerator factor has no bound witness')
        degree=dict(mon).get(x,0)
        if relevant([degree,j])!=j:
            raise Unsupported('The numerator order exceeds the denominator order')
    return dict(guards=guards,denominator_order=j,wave_bounds=[(e,m.div(m.PI,q(2)) if e[0]=='atan' else ONE)
                  for e in sorted(waves)],normalized_numerator=[(mon,q(c)) for mon,c in n.items()])


def monomial_order(term,x):
    if term==x:return F(1)
    tag=term[0]
    if tag in ('sqrt','cbrt'):return monomial_order(term[1],x)/(2 if tag=='sqrt' else 3)
    if tag=='pow':return monomial_order(term[1],x)*term[2]
    if tag=='rpow':
        degree=m.num(m.simplify(term[2]))
        if degree is not None and not domain_conditions(term[2]):
            return degree*monomial_order(term[1],x)
        if term[2][0]=='div' and all(m.num(t) not in (None,0) for t in term[2][1:]):
            return m.num(term[2][1])*monomial_order(term[1],x)/m.num(term[2][2])
    raise Unsupported('A single power of the positive coordinate is required')


def relation_proof(task,kind,request):
    x=('v','x')
    if kind=='Landau_or_equivalence_example_proof':
        g=task['goal'];relation=g['claim'];conditions=task.get('source_assumptions',[])
        packet(task,{'claim','original_domain','goal'},f'При x->0 доказать {relation}.',conditions)
        if g['goal']!='prove the complete O/o/equivalence assertion':
            raise Unsupported('The required asymptotic assertion was not read')
        point='0';domain=g['original_domain']
        if domain not in ('both-sided punctured0','positive original domain','x->0+','positive near1 base, x->0'):
            raise Unsupported('Unknown source approach')
        sides=['right'] if domain in ('positive original domain','x->0+') else ['left','right']
        if conditions:
            if conditions!=['epsilon>0'] or not relation.endswith(', epsilon>0'):
                raise Unsupported('The printed parameter inequality differs')
            relation=relation.removesuffix(', epsilon>0')
        params=set(term_names(relation.replace('root8','').replace('O(','(').replace('o(','(')))
    else:
        fields={'variable','original_domain_policy','approach','parameters','given_relation','requested_output'}
        if kind=='prove_eventual_inequality':
            fields={'variable','original_domain_policy','stated_conditions','claim','quantifiers','requested_output'}
        if (set(task)-META-fields or task['original_domain_policy']!='Original real natural domain; preserve each printed approach and all side/parameter restrictions.'
                or task['variable']!=dict(symbol='x',domain='real')):
            raise Unsupported('An extra original relation, domain or variable requirement remains')
        point='+inf';sides=['positive_infinity'];conditions=[];params=set()
        if kind=='prove_eventual_inequality':
            if (task['stated_conditions']!=['x>0'] or task['requested_output']!=['eventual_inequality_proof']
                    or task['quantifiers']!='There exists X>0 such that for all x>X the printed strict inequality holds.'):
                raise Unsupported('The printed eventual strict comparison differs')
            relation=task['claim']
        else:
            if task['approach']!=dict(point='+inf',direction='positive_infinity') or task['requested_output'] not in (
                    ['proof','Landau_or_equivalence_conditions'],['proof','eventual_real_domain_and_Landau_remainder']):
                raise Unsupported('Different source comparison direction')
            relation=task['given_relation']
            for param in task['parameters']:
                name=param['symbol']
                if param['domain']!='real' or name in params:
                    raise Unsupported('Each scale parameter is fixed and real')
                if set(param)=={'symbol','domain','condition'} and param['condition']==name+'>0':
                    conditions.append(param['condition'])
                elif not (set(param)=={'symbol','domain','fixed','source_restrictions'}
                          and param['fixed'] is True and param['source_restrictions']==[]):
                    raise Unsupported('An original parameter restriction remains')
                params.add(name)
    ctx=m.context(dict(variable='x',parameters=sorted(params),parameter_conditions=conditions))
    if kind=='prove_eventual_inequality':
        logarithmic=re.fullmatch(r'ln\(x\)\^(\d+) < sqrt\(x\)',relation)
        if logarithmic:
            n=int(logarithmic[1])
            if not 1<=n<=1000000:
                raise Unsupported('Formula is outside the supported positive integer power range')
            return proof('scalar_growth_comparison',dict(proved=True,power=n,threshold=f'exp(2^{n+1}*{n+1}!)'),
                 'При t=ln x>0 положительный член ряда exp(t/2) порядка n+1 больше t^n, как только t>2^(n+1)(n+1)!. Это даёт строгое неравенство для всех больших x.',
                 compared_expression=relation)
        if relation.count('<')!=1:
            raise Unsupported('Expected one strict inequality')
        lh,rh=[m.parse(z.strip(),'x',sorted(params)) for z in relation.split('<')]
        approach_conditions(rh,'x',point,sides[0],ctx)
        if rh[0]!='exp' and not (rh[0]=='mul' and m.num(rh[1]) is not None and m.num(rh[1])>0
                                 and rh[2][0]=='pow' and rh[2][1]==x and rh[2][2]>0):
            raise Unsupported('The positive denominator of the strict comparison is unproved')
        ratio=('div',lh,rh);tag='strict'
    else:
        main=re.fullmatch(r'(.+?)\s*=?~\s*(.+)',relation)
        mark=re.fullmatch(r'(.+?)\s*=\s*(.*?)([Oo])\((.+)\)',relation)
        if main:
            lh,scale=main.groups();offset='0';tag='~'
        elif mark:
            lh,offset,tag,scale=mark.groups()
            if offset:
                if not offset.rstrip().endswith('+'):
                    raise Unsupported('The printed leading term is not separated from the remainder')
                offset=offset.rstrip()[:-1].strip()
            else:offset='0'
        else:raise Unsupported('Could not bind the complete asymptotic relation')
        parse=lambda z:m.parse(re.sub(r'\broot8\(x\)',r'(x^(1/8))',z.strip()),'x',sorted(params))
        left,left_scale,leading=map(parse,(lh,scale,offset))
        ratio=('div',left if leading==ZERO else ('add',left,('mul',q(-1),leading)),left_scale)
        if (task.get('requested_output')==['proof','eventual_real_domain_and_Landau_remainder'] and (tag!='O' or leading==ZERO)):
            raise Unsupported('A leading part with an explicit bounded remainder is required')
        if tag=='o' and left[0]=='rpow' and left[2]==('s','n') and not domain_conditions(left[1]) and same_value(left[1],m.add(x,ONE)):
            expected=m.add(ONE,m.mul(('s','n'),x))
            if left_scale==x and same_value(leading,expected) and point=='0' and set(params)=={'n'} and not conditions:
                return proof('scalar_growth_comparison',dict(relation=relation,proved=True),
                    'Основание 1+x положительно в двусторонней окрестности нуля. Производная функции t^n в t=1 равна n для любого фиксированного действительного n. Определение производной даёт остаток o(x) после вычитания 1+nx.',
                    original=left,leading=leading)
        if (tag=='O' and left[0]=='sqrt' and point=='+inf' and not domain_conditions(left[1])
                and not domain_conditions(leading) and left_scale==('div',ONE,x)):
            difference=m.add(left[1],m.neg(m.power(leading,2)))
            a,b=polynomial_coefficients(leading,x,1)
            if b==ONE and not m.variable_in(difference) and all(m.constant_defined(t,ctx) for t in (a,difference)):
                normalized=m.div(difference,q(2))
                return proof('scalar_growth_comparison',dict(relation=relation,proved=True,normalized_remainder_limit=normalized),
                    'Рационализуем разность квадратного корня и линейного члена. Разность их квадратов постоянна. После деления нового знаменателя на x он стремится к 2, при этом подкоренное выражение положительно на хвосте.',
                    squared_difference=difference,leading=leading)
        if tag=='O' and point=='0' and sides==['right'] and leading==ZERO and left[0]=='mul':
            wave=next((e for e in left[1:] if e[0]=='sin'),None)
            if wave is not None:
                factor=left[2] if left[1]==wave else left[1]
                try:degree=monomial_order(factor,x)+monomial_order(wave[1],x)-monomial_order(left_scale,x)
                except Unsupported:pass
                else:
                    if degree>=0:
                        guards=approach_conditions(ratio,'x',point,'right',ctx)
                        return proof('scalar_growth_comparison',dict(relation=relation,proved=True,ratio_bound=ONE),
                            'Положительная шкала допускает деление. По |sin u|≤|u| нормированное отношение по модулю не больше неотрицательной степени x, а значит не больше единицы при 0<x<1.',
                            comparison_order=q(degree),original_guards=guards)
    witnesses=[]
    if tag=='O':
        try:
            bounds=[bounded_ratio(ratio,'x',point,side,ctx) for side in sides]
        except (Unsupported,poly.NotRational,poly.Undefined):
            pass
        else:
            return proof('scalar_growth_comparison',dict(relation=relation,proved=True),
                'Проверяем исходную область перед делением на шкалу. В нормированном отношении волны равномерно ограничены, и каждый оставшийся степенной порядок не превосходит порядка знаменателя.',
                normalized_ratio=ratio,directional_bounds=bounds)
    for side in sides:
        target=dict(expression=source(ratio),variable='x',parameters=sorted(params),approach=dict(point=point,side=side))
        child=request('Проверить отношение на стороне '+side,dict(kind='compute_limit',goal=target,source_assumptions=conditions))
        value=freeze(child['value'])
        if tag=='strict':
            if not isinstance(value,tuple) or m.sign(m.add(ONE,m.neg(value)),ctx)!=1:
                raise Unsupported('A limit strictly below one has not been certified')
        elif tag=='O':
            if not isinstance(value,tuple) or not m.constant_defined(value,ctx):
                raise Unsupported('The normalized ratio has no proved finite limit')
        elif not same_value(value,ONE if tag=='~' else ZERO):
            raise Unsupported('The claimed equivalence or small-order limit differs')
        witnesses.append((side,value))
    return proof('scalar_growth_comparison',dict(relation=relation,proved=True,normalized_limits=witnesses),
                 'На каждой исходной стороне проверяем делитель и вычисляем предел требуемого отношения. Конечный предел даёт ограниченность, нулевой — малый порядок, единичный — эквивалентность. Для строгого сравнения предел ниже единицы даёт нужный хвост.',
                 normalized_ratio=ratio)


def phase_envelope_limit(e,point,side):
    """A power comparison with bounded sine and cosine factors."""
    x=('v','x');ctx=m.context(dict(variable='x'))
    guards=approach_conditions(e,'x',point,side,ctx)
    def terms(polynomial):
        for mon,c in polynomial.items():
            power=F(0);bounded=False
            for a,k in mon:
                if a[0] in ('sin','cos'):
                    bounded=True
                    continue
                power+=k*monomial_order(a,x)
            yield power,c,bounded
    n,d=m.rational_form(e)
    left,right=list(terms(n)),list(terms(d))
    if not right or any(w for _,_,w in right):
        raise Unsupported('An oscillating or zero denominator prevents the envelope limit')
    dominant=max if point=='+inf' else min
    degree=dominant(j for j,_,_ in right)
    scale=sum(c for j,c,_ in right if j==degree)
    if not scale:
        raise Unsupported('The denominator leading coefficient cancels')
    if not left:
        return ZERO,guards
    lead=dominant(j for j,_,_ in left)
    if lead!=degree and dominant(lead,degree)==degree:
        return ZERO,guards
    if any(w for j,_,w in left if j==lead):
        raise Unsupported('The leading term has an unresolved oscillating coefficient')
    constant=sum(c for j,c,_ in left if j==lead)/scale
    if not constant:
        raise Unsupported('The numerator leading coefficient cancels')
    return (q(constant) if lead==degree else '+inf' if constant>0 else '-inf'),guards


def unequal_phase_limits(e,point,side,*,absolute=False):
    from operations import expression_positions
    x=('v','x')
    waves={z for _,z in expression_positions(e) if z[0] in ('sin','cos') and m.contains(z,x)}
    for phase in sorted({z[1] for z in waves}):
        if phase==('ln',x) and point=='+inf':
            inverse=lambda u:('exp',u)
        else:
            try:n,d=poly.rf(phase,'x')
            except (poly.NotRational,poly.Undefined):continue
            top=[(i,c) for i,c in enumerate(n) if c]
            bot=[(i,c) for i,c in enumerate(d) if c]
            if len(top)!=1 or len(bot)!=1:continue
            (i,a),(j,b)=top[0],bot[0]
            speed=a/b
            if speed<=0 or i==j or (i>j)!=(point=='+inf'):continue
            inverse=lambda u:('rpow',m.div(u,q(speed)),q(1,i-j))
        first=None
        for theta in (ZERO,m.div(m.PI,q(2)),m.PI,m.mul(q(3,2),m.PI)):
            specialized=m.substitute(e,{z:m.simplify((z[0],theta)) for z in waves if same_value(z[1],phase)})
            try:value,guards=phase_envelope_limit(specialized,point,side)
            except Unsupported:continue
            if absolute:value='+inf' if value in ('-inf','+inf') else m.simplify(('abs',value))
            seq=inverse(m.add(theta,m.mul(m.mul(q(2),m.PI),('s','n'))))
            hit=dict(phase=theta,sequence=seq,value=value,remaining_guards=guards)
            if first is None:first=hit
            elif value!=first['value']:return [first,hit]
    raise Unsupported('Two admissible subsequences with distinct limits have not been constructed')


def derivative_limit_example(task,library,request):
    from cartesian_fields import vector_source
    if not library.data.get('derivative_phase_limit_examples'):
        raise Unsupported('The differential phase and envelope method is not enabled')
    headings=(
        'Следует ли напечатанный вывод из расходимости f в конце ограниченного интервала? Рассмотреть заданный пример.',
        'Обязателен ли бесконечный предел f, если предел f′ бесконечен? Разобрать пример.',
        'Пусть f дифференцируема на (x0,+∞) и существует предел f′(x) при x→+∞. Следует ли отсюда, что существует предел f′(x) при x→+∞? Рассмотреть указанный пример.',
        'Для ограниченной функции с пределом f′ на бесконечности следует ли существование конечного или бесконечного предела f? Рассмотреть пример.',
    )
    vector_source(task,{'given','test','example'},headings)
    givens=(
        'f differentiable on bounded (a,b), lim_(x→a+) f(x)=infinity',
        'f differentiable on bounded (a,b), lim_(x→a+)f′=infinity',
        'f differentiable on (x0,+infinity) and limit of f′(x) at +infinity exists',
        'bounded differentiable f on (x0,+infinity); limit of f′ exists',
    )
    given=task['given'];example=task['example'];test=task.get('test')
    heading=task.get('source',{}).get('literal_requirement')
    if given not in givens or heading is not None and heading!=headings[givens.index(given)]:
        raise Unsupported('The implication or its full printed hypothesis is not bound')
    kind=givens.index(given)
    targets=(('lim f′(x)=infinity','lim abs(f′(x))=+infinity'),(None,),
             ('does limit of f′(x) at +infinity exist?',),(None,))
    if test not in targets[kind]:
        raise Unsupported('The requested conclusion differs from the implication')
    if kind<2:
        if not example.endswith(', x→0+'):
            raise Unsupported('The example must use the right side of the finite endpoint')
        example=example.removesuffix(', x→0+').removeprefix('f(x)=')
    point,side=('0','right') if kind<2 else ('+inf','positive_infinity')
    example=re.sub(r'\bln\s+x\b','ln(x)',example)
    raw=m.parse(example,'x')
    child=request('differentiate the given function on its original open interval',dict(
        kind='ordinary_derivative_order',function=example,variable='x',orders=[1],requested_output=['derivatives']))
    derivative=freeze(child['value']['derivatives'][0])
    ctx=m.context(dict(variable='x'))
    guards=approach_conditions(raw,'x',point,side,ctx)
    for relation,e in child['value']['smooth_domain']:
        probe={'nonzero':('div',ONE,e),'positive':('ln',e),'nonnegative':('sqrt',e)}[relation]
        approach_conditions(probe,'x',point,side,ctx)
    evidence=dict(original_guards=guards,source_function=raw,source_derivative=derivative)
    if kind==2:
        f_limit,_=phase_envelope_limit(raw,point,side)
        hits=unequal_phase_limits(derivative,point,side)
        evidence.update(function_limit=f_limit,derivative_subsequences=hits)
        return proof('derivative_phase_examples',dict(implication_holds=True,example_satisfies_hypothesis=False,
                     example_derivative_limit_exists=False,example_function_limit=f_limit),
            'В буквальном условии существование предела f′ уже принято. Указанный пример не удовлетворяет этой предпосылке: две последовательности фиксируют разные фазы производной. При чтении первого f′ как f предел самой функции подтверждает предполагаемый контрпример.',
            **evidence)
    required=phase_envelope_limit(derivative if kind in (1,3) else raw,point,side)[0]
    if (kind<2 and required!='+inf') or (kind==3 and not isinstance(required,tuple)):
        raise Unsupported('The example has not been shown to satisfy the printed limit hypothesis')
    if kind==3:
        bounded_ratio(raw,'x',point,side,m.context(dict(variable='x')))
    if kind==1:
        limit=phase_envelope_limit(raw,point,side)[0]
        if limit in ('-inf','+inf'):
            raise Unsupported('The example is not a counterexample to an infinite function limit')
        evidence['function_limit']=limit
    else:
        evidence['conflicting_subsequences']=unequal_phase_limits(raw if kind==3 else derivative,point,side,
                                                                 absolute=test=='lim abs(f′(x))=+infinity')
    return proof('derivative_phase_examples',dict(implication_holds=False,hypothesis_limit=required,
                 original_open_side=side,example_analysis=evidence),
        'Проверяем исходную область и вычисляем производную. В предпосылке старший степенной порядок отделяется от ограниченных тригонометрических множителей. Для вывода вычисляем конечный предел либо строим две последовательности, на которых фазы дают разные пределы.',
        **evidence)


def scalar_proof(task, library, request):
    kind=task.get('kind',task.get('task_type'))
    if kind=='derivative_limit_counterexample':return derivative_limit_example(task,library,request)
    metadata=task.get('source',{})
    if (not library.data.get('source_scalar_proofs') or not isinstance(metadata,dict) or
            set(metadata)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256'}):
        raise Unsupported('The scalar proof or all its source requirements are not admitted')
    if kind in ('function_parity','even_odd_decomposition_proof','mathematical_question'):
        return even_odd(task,kind)
    if kind=='graph_symmetry_classification':
        return symmetry(task)
    if kind=='periodicity_and_fundamental_period':
        return fundamental_period(task)
    if kind in ('dirichlet_function_period_proof','commensurate_period_arithmetic_proof',
                'antiperiod_implies_period_proof','scaled_period_factorization','proof'):
        return abstract_period(task,kind)
    if kind.endswith('_definition_and_examples'):
        return limit_language(task,kind)
    if kind in ('epsilon_delta_proof_and_table','E_delta_infinite_limit_proof_and_table'):
        return limit_table(task,kind)
    if kind in ('parameter_monotonicity_classification','inequality_logarithm_conditions','ordered_composition_sandwich'):
        return monotonicity(task,kind)
    if kind in ('finite_but_locally_unbounded_proof','local_global_boundedness_with_examples','boundedness_proof',
                'unbounded_not_magnitude_infinite_proof','boundedness_analysis','infimum_supremum_proof',
                'monotone_bounds_question','bounds_sum_proof_with_examples'):
        return boundedness(task,kind,request)
    if kind=='oscillation_at_point':
        return oscillation(task,request)
    if kind=='geometric_infinitesimal_order':
        return geometric_order(task,request)
    if kind in ('Landau_symbol_algebra_proof','Landau_power_algebra_proof','asymptotic_equivalence_relation_proof'):
        return landau_algebra(task,kind)
    if kind in ('prove_asymptotic_relation','Landau_or_equivalence_example_proof','prove_eventual_inequality'):
        return relation_proof(task,kind,request)
    raise Unsupported('The complete scalar proof remains open')
