"""Certificates for ordinary series on their original integer lattices."""
from collections import defaultdict
from fractions import Fraction
import re

import expressions as m
from expressions import PI
from model import ONE, ZERO, Unsupported, q


OUTPUTS = {'convergence_classification','justification','asymptotic_order','absolute_convergence','conditional_convergence'}
GENERAL = (None, 'general_convergence_tests', 'comparison_or_ratio_or_root')
ORDINARY_FIELDS = {'kind','term','index','start_index','index_domain','parameters','stated_conditions','method_requirement',
                   'requested_output','schema','id','source','transcription','hint','tolerance','block_terms','block_index'}
NATIVE = {'rearranged_series_sum','construct_series_rearrangement','sum_of_series'}


def routing(task, kind):
    if boundary_series_head(task,kind):return True
    if kind=='complex_power_series_disk':
        try:normalized_complex_geometric_disk(task)
        except Unsupported:return False
        return True
    if kind == 'series_convergence':
        method=task.get('method_requirement')
        if method=='comparison_or_ratio_or_root':
            if 'sqrt(' in str(task.get('sequence_definitions','')):return True
            index=re.escape(str(task.get('index','')))
            return bool(index and re.search(r'\^\s*(?:\([^)]*\b)?'+index+r'\b',str(task.get('term',''))))
        return method!='cauchy_tail_criterion'
    if kind == 'sequence_convergence':
        return task.get('method_requirement') == 'series_of_consecutive_differences'
    if kind == 'functional_series_convergence_set':
        return len(task.get('variables') or ()) == 2 or 'term' in task and len(task.get('variables') or ())>1
    if kind in ('series_grouping_proof','laurent_series'):return True
    return kind in NATIVE or (kind in ('series_theorem','series_proposition')
                              and 'statement' in task and not isinstance(task.get('functional_statement'),dict))


def add(a, b):
    return m.simplify(m.add(a,b))


def mul(a, b):
    return m.simplify(m.mul(a,b))


def power(a, b):
    if a==ONE:return ONE
    k=m.num(b)
    return m.simplify(m.power(a,int(k)) if k is not None and k.denominator==1 and 0<=k<=64 else ('rpow',a,b))


def result(theorem, value, *reason, **evidence):
    return dict(theorem='method.'+theorem, argument=list(reason), **evidence), value


def verdict(absolute=False, conditional=False):
    return dict(classification='convergent' if absolute or conditional else 'divergent',
                absolute_convergence=absolute, conditional_convergence=conditional)


def branches(cases):
    return dict(classification='parameter_dependent', branches=[dict(condition=c,**v) for c,v in cases])


def power_classes(d, absolute, ordinary, ctx):
    from finite_sums import progression_classes
    return {k:v for k,v in progression_classes(d,absolute,ordinary,ctx).items() if k!='criterion'}


def index_context(index, params, conditions):
    if not (isinstance(params,list) and all(isinstance(p,str) for p in params) and isinstance(conditions,list)):
        raise Unsupported('Parameters and original assumptions must be explicit')
    return m.context(dict(variable=index,parameters=params,parameter_conditions=conditions))


def no_real_holes(expr,index,start,ctx):
    from tasks import domain_conditions,known_guard
    n=('v',index);fresh='seriesRay'
    while fresh in [index,*ctx['parameters']]:fresh+='_'
    extra={**ctx,'parameters':[*ctx['parameters'],fresh],
           'assumptions':[*ctx['assumptions'],dict(symbol=fresh,relation='positive')]}
    return all(known_guard((sign,m.substitute(e,{n:point})),c)
               for sign,e in domain_conditions(expr,True)
               for point,c in ((q(start),ctx),(m.add(q(start),('s',fresh)),extra)))


def logarithmic_monomial(expr,n,ctx):
    """Collect exact powers of the index and its successive logarithms."""
    def atom(e):
        if e==n:return 0
        if e[0]=='ln':return 1+atom(e[1])
        raise Unsupported('Expected an iterated logarithm of the original index')
    coeff=ONE;rates={};bases={}
    def visit(e, orientation):
        nonlocal coeff
        op=e[0]
        if op in ('mul','div'):
            visit(e[1],orientation);visit(e[2],orientation if op=='mul' else -orientation);return
        if m.constant_defined(e,ctx):
            if orientation<0 and m.sign(e,ctx) not in (-1,1):raise Unsupported('A fixed coefficient might vanish in the denominator')
            coeff=mul(coeff,e if orientation>0 else m.div(ONE,e));return
        base,d=(e[1],q(1,2)) if op=='sqrt' else (e[1],q(e[2])) if op=='pow' else (e[1],e[2]) if op=='rpow' else (e,ONE)
        if not m.constant_defined(d,ctx):raise Unsupported('A depth exponent must be independently fixed')
        k=atom(base)
        rates[k]=add(rates.get(k,ZERO),mul(q(orientation),d));bases[k]=base
    visit(expr,1)
    return coeff,[rates.get(k,ZERO) for k in range(max(rates,default=0)+1)],bases


def logarithmic_classification(rates,ctx):
    from tasks import source
    unknown=[];cases=[]
    for d in rates:
        s=m.sign(add(d,ONE),ctx);shown=source(d)
        join=lambda text:' and '.join([*unknown,text])
        if s is None:
            cases.extend([(join(f'({shown})<-1'),verdict(True)),(join(f'({shown})>-1'),verdict())])
            unknown.append(f'({shown})=-1')
        elif s:
            if not unknown:return verdict(s<0)
            cases.append((' and '.join(unknown),verdict(s<0)))
            return branches(cases)
    if not unknown:return verdict()
    return branches([*cases,(' and '.join(unknown),verdict())])


def logarithmic_series(term,index,start,ctx,method,outputs):
    n=('v',index)
    coefficient,rates,bases=logarithmic_monomial(term,n,ctx)
    for node in bases.values():
        if node==n:continue
        # Iterated logarithms are strictly increasing wherever the inner ones are positive.
        if constant_sign(m.substitute(node,{n:q(start)}),ctx)!=1:
            raise Unsupported('A logarithmic base is not proved positive at the original first index')
    s=m.sign(coefficient,ctx)
    if s not in (-1,0,1):raise Unsupported('The coefficient needs a zero/nonzero case distinction')
    answer=verdict(True) if s==0 else logarithmic_classification(rates,ctx)
    if 'asymptotic_order' in outputs:
        if s==0:raise Unsupported('An identically zero term has no nonzero equivalent coefficient')
        answer.update(asymptotic_order=dict(index_power=m.neg(rates[0]),log_powers=list(map(m.neg,rates[1:])),equivalent_coefficient=coefficient))
    if method=='cauchy_integral_test':
        if s!=1 or len(rates)<2 or rates[0]!=q(-1):raise Unsupported('Positive density of the required integral comparison has not been established')
        theorem='iterated_logarithm_integral_test'
        reasons=('Все основы положительны от исходного индекса. В логарифмической производной множитель степени x определяет отрицательный знак на хвосте.',
                 'К каждому первому показателю −1 применяем подстановку t=ln x, dt=dx/x. Первый отличный от −1 показатель определяет сравнение с интегралом степени.')
    else:
        theorem='logarithmic_power_scale'
        reasons=('Собираем степени n, ln n и следующих логарифмов в исходном члене.',
                 'Мелкие логарифмические множители лежат между любыми фиксированными положительной и отрицательной степенями предыдущего масштаба. Применяем сравнение с граничными рядами.')
    return result(theorem,answer,*reasons,coefficient=coefficient,rates=rates,first_index=start)


def finite_blocks(task):
    from finite_sums import progression_weight
    from tasks import source
    if (task.get('term')!='concatenate_blocks' or set(task)-ORDINARY_FIELDS or task.get('method_requirement') not in GENERAL
            or set(task.get('requested_output',()))-{'convergence_classification','justification','absolute_convergence','conditional_convergence'}):
        raise Unsupported('No specified fixed-length series blocks')
    i=task['block_index'];start=task['start_index'];params=task['parameters'];terms=task['block_terms']
    if type(start) is not int or start<0 or not 2<=len(terms)<=16:raise Unsupported('Invalid first block or block length')
    ctx=index_context(i,params,task.get('stated_conditions',[]));ctx.update(variable=i,sum_start=start)
    groups=defaultdict(list);checks=[]
    for term in terms:
        c,phase,slope,offset,first,d=progression_weight(m.parse(term,i,params),ctx)
        if phase or c==ZERO:raise Unsupported('The block requires nonzero fixed signs and power progressions')
        checks.append((c,slope,offset,first,d));groups[d].append((c,slope))
    if len(groups)>2:raise Unsupported('Need a larger parameter-order decomposition')

    def coefficient(exponent, data):
        by_slope=defaultdict(Fraction)
        for c,a in data:by_slope[a]+=m.num(c)
        nonzero={a:c for a,c in by_slope.items() if c}
        if not nonzero:return ZERO
        value=ZERO
        for a,c in nonzero.items():value=add(value,mul(q(c),power(a,m.neg(exponent))))
        return value

    def grouped(members):
        ds=[d for d,_ in members];names=list(map(source,ds));coeffs=[coefficient(d,v) for d,v in members];co=list(map(source,coeffs))
        positives=' and '.join(f'({d})>0' for d in names)
        absolute=' and '.join(f'({d})>1' for d in names)
        summable=' and '.join(f'(({d})>1 or ({c})=0)' for d,c,z in zip(names,co,coeffs) if z!=ZERO) or 'true'
        return dict(absolute_if=absolute,conditional_if=f'({positives}) and ({summable}) and not ({absolute})',
                    divergent_if=f'not (({positives}) and ({summable}))',leading_coefficients=list(zip(ds,coeffs)))

    items=list(groups.items())
    if len(items)==1:answer=grouped(items)
    else:
        (a,aa),(b,bb)=items;s=m.sign(add(a,m.neg(b)),ctx)
        if s==0:answer=grouped([(a,aa+bb)])
        elif s in (-1,1):answer=grouped(items)
        else:
            A,B=map(source,(a,b))
            answer=dict(exponent_cases=[dict(condition=f'({A})=({B})',**grouped([(a,aa+bb)])),
                                        dict(condition=f'({A})!=({B})',**grouped(items))])
    return result('leading_terms_of_series_blocks',dict(classification='parameter_dependent',**answer),
                  'Сначала проверяем тест общего члена на каждой позиции блока. Положительность всех первоначальных оснований сохраняется.',
                  'Для каждого показателя складываем коэффициенты соответствующего порядка. Остаток блока имеет на одну степень быстрее убывание.',
                  'При положительных показателях все внутриблочные хвосты стремятся к нулю. Абсолютная сходимость требует суммируемости каждой позиции отдельно.',
                  checked_progressions=checks,first_block=start)


def phase_polynomial(phase,index):
    from integrals import affine
    from polynomial import NotRational, rf
    try:
        p,d=rf(phase,index)
        if len(d)==1 and len(p)<=7:return tuple(q(x/d[0]) for x in p)
    except NotRational:pass
    slope,offset=affine(phase,index)
    return offset,slope


def nonresonant(step, even=True):
    step=m.simplify(step);exact=m.num(step)
    if exact is not None:return exact!=0
    multiple=m.pi_multiple(step)
    if multiple is not None:return (multiple/(2 if even else 1)).denominator!=1
    marker=('v','phasePi')
    try:p=phase_polynomial(m.substitute(step,{PI:marker}),marker[1])
    except Unsupported:return False
    return len(p)==2 and all(m.num(x) is not None for x in p) and p[0]!=ZERO


def fourier_terms(waves,index):
    """Apply product-to-sum, then combine equal polynomial phases."""
    n=('v',index);terms=[(Fraction(1),'cos',ZERO)]
    for op,b in waves:
        next_terms=[]
        for c,kind,a in terms:
            if a==ZERO and kind=='cos':next_terms.append((c,op,b));continue
            if kind=='cos' and op=='sin':a,before=b,a
            else:before=b
            same=kind==op;tag='cos' if same else 'sin'
            next_terms.extend(((c/2 if kind!=op or op=='cos' else -c/2,tag,add(a,before)),
                               (c/2,tag,add(a,m.neg(before)))))
        terms=next_terms
    out=defaultdict(Fraction)
    for c,kind,angle in terms:
        poly=phase_polynomial(angle,index)
        if all(m.num(x) is not None for x in poly):
            leading=next((m.num(x) for x in reversed(poly) if x!=ZERO),0)
            if leading<0:
                poly=tuple(m.neg(x) for x in poly)
                if kind=='sin':c=-c
        if kind=='sin' and all(x==ZERO for x in poly):continue
        out[kind,poly]+=c
    return {k:c for k,c in out.items() if c}


def bounded_phase_terms(terms,index):
    from verify import same_value
    n=('v',index);pending=dict(terms);checks=[]
    while pending:
        (kind,a),weight=pending.popitem()
        if len(a)==2 and nonresonant(a[1]):
            checks.append(dict(phase=a,argument='bounded geometric partial sums'));continue
        if len(a)<3 or any(m.num(x) is None for x in a):raise Unsupported('A nonoscillating or unsupported phase remained')
        expr=ZERO
        for c in reversed(a):expr=add(mul(n,expr),c)
        matched=False
        for (other,b),c in tuple(pending.items()):
            if other!=kind or len(b)!=len(a) or c!=-weight or b[-1]!=a[-1] or any(m.num(x) is None for x in b):continue
            shift=m.num(add(b[-2],m.neg(a[-2])))/((len(a)-1)*m.num(a[-1]))
            if not shift or shift.denominator!=1 or abs(shift)>64:continue
            changed=m.substitute(expr,{n:m.add(n,q(shift))})
            got=phase_polynomial(changed,index)
            if len(got)==len(b) and all(same_value(x,y) for x,y in zip(got,b)):
                pending.pop((other,b));checks.append(dict(phase=a,shift=int(shift),shifted_phase=b,argument='telescoping bounded sequence'));matched=True;break
        if not matched:raise Unsupported('The polynomial phases do not provide a bounded sum by a shared integer shift')
    return checks


def split_waves(term,n):
    """Separate bounded signed factors from a positive amplitude without canceling any raw guard."""
    waves=[]
    def visit(e):
        tag=e[0]
        if tag=='mul':
            a,b=visit(e[1]),visit(e[2]);return a if b==ONE else b if a==ONE else ('mul',a,b)
        if tag=='div':return ('div',visit(e[1]),e[2])
        if tag in ('cos','sin'):
            waves.append(e);return ONE
        if tag=='pow' and type(e[2]) is int and 1<=e[2]<=4 and e[1][0] in ('cos','sin'):
            waves.extend([e[1]]*e[2]);return ONE
        if tag=='rpow' and e[1]==q(-1):
            coefficients=phase_polynomial(e[2],n[1])
            if any(m.num(c) is None or m.num(c).denominator!=1 for c in coefficients):
                raise Unsupported('Parity exponent has not been proved an integer')
            waves.append(('cos',mul(PI,e[2])));return ONE
        return e
    return visit(term),waves


def monomial_weight(expr,index,start,ctx):
    n=('v',index);coefficient,rates,bases=logarithmic_monomial(expr,n,ctx)
    if m.sign(coefficient,ctx)!=1 or any(constant_sign(m.substitute(a,{n:q(start)}),ctx)!=1 for a in bases.values() if a!=n):
        raise Unsupported('The positive weight has an unproved source domain')
    signs=[m.sign(d,ctx) for d in rates]
    if None in signs:raise Unsupported('The weight needs parameter-dependent monotonicity')
    decay=next((k for k in signs if k),0)<0
    classification=logarithmic_classification(rates,ctx)
    return decay,classification['absolute_convergence'],rates


def polynomial_phase_series(raw,index,start,ctx,outputs):
    n=('v',index)
    if ctx['parameters'] or 'asymptotic_order' in outputs:raise Unsupported('Fixed coefficients and pure convergence question required')
    if raw[0] in ('sin','cos'):
        if not no_real_holes(raw,index,start,ctx):raise Unsupported('An original phase has a domain guard')
        poly=phase_polynomial(raw[1],index);d=len(poly)-1
        from math import factorial
        if d<1 or not nonresonant(mul(q(factorial(d)),poly[-1]),False):raise Unsupported('No nontrivial highest phase difference')
        return result('polynomial_phase_fails_null_test',verdict(),
                      'Если терм стремится к нулю, удвоенная комплексная фаза стремится к постоянной единичного модуля.',
                      'На каждом следующем мультипликативном разностном шаге предел отношения равен единице. Последняя разность многочлена даёт постоянный угол, для которого это неверно.',
                      polynomial=poly,order=d)
    amplitude,waves=split_waves(raw,n)
    if not waves or len(waves)>4:raise Unsupported('No supported finite phase decomposition')
    if any(not no_real_holes(wave,index,start,ctx) for wave in waves) or not no_real_holes(amplitude,index,start,ctx):
        raise Unsupported('An original wave or weight has a domain guard')
    decay,absolute,rates=monomial_weight(amplitude,index,start,ctx)
    if not decay:raise Unsupported('The extracted weight does not decrease to zero')
    terms=fourier_terms(waves,index);checks=bounded_phase_terms(terms,index)
    answer=verdict(True) if absolute else dict(classification='convergent')
    if not absolute and len(waves)==1:
        p=phase_polynomial(waves[0][1],index)
        if len(p)==2 and nonresonant(p[1],False):answer=verdict(False,True)
    if not absolute and len(waves)==3:
        for j in range(3):
            phase=waves[j];pair=waves[:j]+waves[j+1:]
            if phase[0]!='cos' or pair[0]!=pair[1]:continue
            ordinary=phase_polynomial(pair[0][1],index);parity=phase_polynomial(phase[1],index)
            if len(ordinary)==len(parity)==2 and nonresonant(ordinary[1],False) and m.pi_multiple(parity[1]) in (Fraction(1),Fraction(-1)) and parity[0]==ZERO:
                answer=verdict(False,True);break
    if not absolute and set(outputs)&{'absolute_convergence','conditional_convergence'} and 'absolute_convergence' not in answer:
        raise Unsupported('The modulus requires an independent lower bound')
    return result('bounded_phase_dirichlet',answer,
                  'Выделяем положительную амплитуду, которая убывает к нулю на хвосте.',
                  'Раскрываем произведения по формулам сложения. Для линейных фаз применяем конечную геометрическую сумму, для сдвинутых фаз остаётся конечное число граничных членов.',
                  'Ограниченные частичные суммы и монотонный вес дают сходимость по Дирихле. Если модуль исследован, используем положительную среднюю массу квадрата или суммируемую мажоранту.',
                  rate=rates,checked_phases=checks,first_index=start)


def floor_blocks(text,index,start,ctx,outputs):
    name=re.escape(index)
    p=re.fullmatch(r'\(-1\)\^floor\((sqrt|ln)\('+name+r'\)\)/(.+)',text.replace(' ',''))
    if not p or 'asymptotic_order' in outputs:raise Unsupported('No proved floor block structure')
    n=('v',index);den=m.parse(p[2],index,ctx['parameters'])
    d=ONE if den==n else (q(den[2]) if den[0]=='pow' else den[2]) if den[0] in ('rpow','pow') and den[1]==n else None
    if d is None or not m.constant_defined(d,ctx):raise Unsupported('No fixed power weight in the floor blocks')
    if p[1]=='ln':
        if d!=ONE:raise Unsupported('Need separate exponential block estimates for a nonharmonic weight')
        return result('exponential_lattice_blocks',verdict(),
                      'Между соседними целыми значениями ln n знак постоянен. Масса такого блока гармонического веса стремится к единице по интегральному сравнению, поэтому нарушен критерий Коши.',
                      block='ceil(exp(j)) <= n < ceil(exp(j+1))',first_index=start)
    return result('square_lattice_blocks',power_classes(d,ONE,q(1,2),ctx),
                  'На блоке j² ≤ n < (j+1)² имеется 2j+1 членов одинакового знака.',
                  'Равномерная оценка веса даёт сумму модуля блока 2j^(1−2p)+O(j^(−2p)). При p>1/2 главная часть сходится по Лейбницу, ошибка суммируема и неполный блок стремится к нулю.',
                  'При p≤1/2 массы блоков не стремятся к нулю. Абсолютная сходимость по исходным отдельным членам требует p>1.',
                  exponent=d,first_index=start)


def periodic_sign_series(text,index,start,ctx,outputs):
    if 'asymptotic_order' in outputs:raise Unsupported('A signed periodic term has no constant leading coefficient')
    iv=re.escape(index)
    shape=re.fullmatch(r'periodic_sign\(('+iv+r'(?:[+-]\d+)?),\[([+-]?\d+(?:,[+-]?\d+)*)\]\)/(.+)',text.replace(' ',''))
    if not shape:raise Unsupported('No explicit finite sign cycle')
    cycle=[int(x) for x in shape[2].split(',')];offset=int(shape[1][len(index):] or 0)
    if not 1<=len(cycle)<=64:raise Unsupported('Sign cycle too large')
    amp=m.div(ONE,m.parse(shape[3],index,ctx['parameters']))
    decay,absolute,rates=monomial_weight(amp,index,start,ctx)
    zero=not any(cycle);null_mean=not sum(cycle)
    return result('periodic_mean_and_tail',verdict(zero or absolute,not absolute and not zero and null_mean and decay),
                  'На каждом полном периоде обычный вклад определяется средним значением знаков. Часть с нулевым средним имеет ограниченные частичные суммы.',
                  'Для абсолютной сходимости применяем тот же разбор к неотрицательному периоду модулей, среднее которого строго положительно, если цикл не нулевой.',
                  period=cycle,offset=offset,rate=rates,first_index=start)


def positive_cutoff(task,outputs):
    from integrals import affine
    from math import ceil, factorial, prod
    if outputs!=['number_of_terms_for_requested_tolerance','verified_tail_bound'] or task.get('parameters') or task.get('stated_conditions'):
        raise Unsupported('The requested tail precision is not yet supported')
    index=task['index'];n=('v',index);start=task['start_index']
    tol_raw=m.parse(task['tolerance'],None);tol=m.num(m.simplify(tol_raw))
    if not m.constant_defined(tol_raw,dict(parameters=[],assumptions=[])) or tol is None or tol<=0:
        raise Unsupported('The original precision is not a positive rational number')
    e=m.parse(task['term'],index,(),('factorial',))
    if e[0]!='div':raise Unsupported('The remainder majorant needs a positive reciprocal kernel')
    top,bottom=e[1:];c=m.num(top)
    if bottom[0]=='pow' and bottom[1]==n and bottom[2]>1 and c is not None and c>0:
        p=bottom[2];q0=Fraction(c,p-1)/tol
        # A binary search on the exact comparison avoids enumerating large finite partial sums.
        lo=start-1;hi=max(start,ceil(q0))
        while lo<hi-1:
            mid=(lo+hi)//2
            if mid**(p-1)>=q0:hi=mid
            else:lo=mid
        bound=Fraction(c,(p-1)*hi**(p-1))
        return result('monotone_power_integral_remainder',dict(sufficient_terms=hi-start+1,last_index=hi,upper_error=q(bound)),
                      'Интеграл от последнего оставленного индекса до бесконечности строго больше положительного остатка убывающего степенного ряда.',
                      exponent=p,tolerance=q(tol),cutoff=hi)
    if bottom[0]!='factorial':raise Unsupported('No affine factorial in the tail ratio')
    a,b=map(m.num,affine(bottom[1],index))
    if any(v is None or v.denominator!=1 for v in (a,b)) or not 1<=a<=16 or not 0<=a*start+b<=256:
        raise Unsupported('The initial factorial or every integer shift is not admissible')
    a,b=int(a),int(b)
    if c is not None and c>0:r=Fraction(1)
    elif top[0]=='rpow' and top[2]==n and m.num(top[1]) is not None and m.num(top[1])>0:r=m.num(top[1]);c=r**start
    else:raise Unsupported('The numerator lacks a fixed positive geometric ratio')
    def ratio(k):return r/prod(a*k+b+j for j in range(1,a+1))
    value=c/factorial(a*start+b)
    for hi in range(start,start+512):
        value*=ratio(hi);upper_ratio=ratio(hi+1)
        if upper_ratio<1 and (bound:=value/(1-upper_ratio))<=tol:
            return result('affine_factorial_geometric_remainder',dict(sufficient_terms=hi-start+1,last_index=hi,upper_error=q(bound)),
                          'Отношение двух соседних членов выражается через возрастающие положительные целые множители. Первое отношение после отсечения ограничивает все последующие.',
                          'Первый пропущенный член и полученное отношение дают геометрическую мажоранту хвоста.',
                          first_omitted=q(value),tail_ratio=q(upper_ratio),factorial_step=a,factorial_offset=b,cutoff=hi,tolerance=q(tol))
    raise Unsupported('A sufficient tail cutoff is not established within the exact ratio calculation')


def partial_sum_error(task,request):
    from tasks import source
    from verify import same_value
    if set(task)-{'kind','expression','index','start_index','method_requirement','requested_output','id','source'} or task.get('requested_output')!=['convergence_decision','equivalent_series_proof']:
        raise Unsupported('Both convergence and a consecutive-difference proof are required')
    index=task['index'];n=('v',index);start=task['start_index']
    if type(start) is not int or start<1:raise Unsupported('Need a positive original index')
    expr=re.fullmatch(r'sum\((.+),([A-Za-z_]\w*)=(\d+)\.\.'+re.escape(index)+r'\)\s*-\s*(.+)',task['expression'])
    if not expr or not 1<=int(expr[3])<=start:raise Unsupported('No admissible finite prefix and antiderivative difference')
    f=m.substitute(m.parse(expr[1],expr[2]),{('v',expr[2]):n});primitive=m.parse(expr[4],index)
    ctx=index_context(index,[],[])
    if not no_real_holes(f,index,int(expr[3]),ctx) or not no_real_holes(primitive,index,start,ctx):
        raise Unsupported('The prefix density or primitive is undefined at an original index')
    _,rates,_=logarithmic_monomial(f,n,ctx)
    if next((m.sign(d,ctx) for d in rates if d!=ZERO),0)!=-1:
        raise Unsupported('The checked weight does not decrease to zero on a tail')
    child=dict(kind='differentiate',function=source(primitive),variable=index,requested_output=['derivative_formula'])
    proof=request('производная непрерывного приближения к частичной сумме',child,('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'))
    compilation=proof.get('plan',{}).get('compilation',proof.get('compilation',{}))
    if proof['status']=='FORMULA_ON_SUFFICIENT_DOMAIN':
        guards=compilation['sufficient_formula_domain']
        if not all(guard_on_ray((g,m.freeze(e)),index,start,ctx) for g,e in guards):
            raise Unsupported('A derivative boundary obligation falls on the original ray')
    derivative=m.freeze(proof.get('formula',proof['value']));symbol=compilation.get('formula_scope',{}).get('quantified_symbol')
    if symbol:derivative=m.substitute(derivative,{('s',symbol):n})
    if not same_value(derivative,f):raise Unsupported('The continuous part is not a primitive of the sequence kernel')
    return result('integral_and_sum_discretization_error',dict(convergent=True,equivalent_series='absolute convergence of consecutive differences'),
                  'Разность соседних членов равна f(n+1) минус интеграл f на [n,n+1]. Производную непрерывной части проверили отдельно.',
                  'На хвосте f монотонна и стремится к нулю. Модуль разности ограничен |f(n+1)−f(n)|, а эти границы телескопируются.',
                  'Значит, ряд последовательных разностей сходится абсолютно, что даёт сходимость исходной последовательности.',
                  term=f,primitive=primitive,rate=rates,first_index=start)


def fixed_cycle(phase,index,start):
    from finite_sums import integer_sign_period
    n=('v',index)
    if phase[0]=='rpow' and phase[1]==q(-1):
        ordered=integer_sign_period(phase,index,start)
        cycle=tuple(q(ordered[(start+j)%len(ordered)]) for j in range(len(ordered)))
    elif phase[0] in ('sin','cos'):
        line=phase_polynomial(phase[1],index)
        if len(line)!=2:raise Unsupported('Only a finite affine phase has a fixed cycle')
        step=m.pi_multiple(line[1]);offset=m.pi_multiple(line[0])
        if step is None or offset is None:raise Unsupported('Phase is not a rational multiple of π from the source')
        count=(step/2).denominator
        if count>64:raise Unsupported('The exact phase period is too large')
        cycle=tuple(m.simplify(m.substitute(phase,{n:q(start+j)})) for j in range(count))
    else:raise Unsupported('No original signed periodic factor')
    if not cycle or add_many(cycle)!=ZERO or not any(x!=ZERO for x in cycle):
        raise Unsupported('The phase has no proved nonzero, centered period')
    return cycle


def add_many(terms):
    value=ZERO
    for x in terms:value=add(value,x)
    return value


def index_power(e,n):
    if e==n:return ONE
    if e[0]=='sqrt' and e[1]==n:return q(1,2)
    if e[0]=='pow' and e[1]==n:return q(e[2])
    if e[0]=='rpow' and e[1]==n:return e[2]
    raise Unsupported('Expected a single index power')


def centered_perturbations(raw,index,start,ctx,outputs):
    """Check the signed leading term and the drift created by the same perturbation."""
    from tasks import source
    from verify import same_value
    if 'asymptotic_order' in outputs:raise Unsupported('The signed term requires several leading coefficients')
    n=('v',index)
    if raw[0]=='ln' and raw[1][0]=='add' and raw[1][1]==ONE and raw[1][2][0]=='div':
        phase,den=raw[1][2][1:];d=index_power(den,n)
        cycle=fixed_cycle(phase,index,start)
        if set(cycle)!={ONE,q(-1)} or start<2 or not m.constant_defined(d,ctx):
            raise Unsupported('The logarithmic branch must be defined from its original index')
        if not ctx['parameters']:
            if m.sign(d,ctx) in (-1,0):return result('centered_logarithmic_drift',dict(classification='undefined',offending_residue=cycle.index(q(-1))),
                                                       'При неположительной степени аргумент логарифма на отрицательной фазе неположителен.',first_index=start,period=cycle)
            val=power_classes(d,ONE,q(1,2),ctx)
        else:
            val=power_classes(d,ONE,q(1,2),ctx);val.update(undefined_if=source(d)+'<=0',divergence=source(d)+' > 0 and '+source(d)+' <= 1/2')
        return result('centered_logarithmic_drift',val,
                      'При положительном показателе логарифм определён во всех исходных индексах. Неположительный показатель нарушает это на отрицательной фазе.',
                      'В log(1+s n⁻ᵖ) ведущий знакопеременный член сходится по Дирихле. Второй член равен −s² n⁻²ᵖ/2, а остаток меньше по порядку.',
                      'При 2p≤1 постоянный отрицательный вклад даёт расходимость, при 2p>1 он и остаток суммируемы. Модуль главной части требует p>1.',
                      exponent=d,period=cycle,first_index=start)
    if raw[0]!='div':raise Unsupported('No centered perturbation of an inverse power')
    phase,den=raw[1:];cycle=fixed_cycle(phase,index,start)
    if any(m.sign(add(ONE,m.neg(power(v,q(2)))),ctx) not in (0,1) for v in cycle):raise Unsupported('Phase bound |s|≤1 was not proved')
    data=(den[1],q(den[2])) if den[0]=='pow' else (den[1],den[2]) if den[0]=='rpow' else (den,ONE)
    base,p=data
    if base[0]!='add' or not same_value(base[2],phase):raise Unsupported('The phase in the source denominator differs from its numerator')
    a=m.simplify(index_power(base[1],n))
    if not all(m.constant_defined(e,ctx) for e in (a,p)):raise Unsupported('The original exponents are not fixed independently of n')
    aval=m.num(a)
    if aval is not None and aval>0:
        if start==1 and m.sign(add(ONE,cycle[0]),ctx)!=1:raise Unsupported('First original denominator vanishes')
        value=power_classes(p,q(1/aval),q(max(0,1/aval-1)),ctx)
        return result('centered_inverse_power_drift',value,
                      'Исходный знаменатель положителен, поскольку растущая степень индекса больше модуля фазы. Первый индекс проверяется отдельно.',
                      'Разложение даёт s n⁻ᵅᵖ − p s² n⁻ᵅ⁽ᵖ⁺¹⁾. При p>0 первая часть сходится по Дирихле, вторая при α(p+1)≤1 определяет знак расходящегося хвоста.',
                      'При p≤0 общий член не стремится к нулю. Для абсолютной сходимости нужна αp>1, так как ненулевые фазы повторяются.',
                      inner_power=a,outer_power=p,period=cycle,first_index=start)
    if p!=ONE or not ctx['parameters']:raise Unsupported('The inner scale needs parameter branches')
    if start==1 and m.sign(add(ONE,cycle[0]),ctx)!=1:raise Unsupported('First original denominator vanishes for every parameter')
    name=source(a);value=power_classes(a,ONE,q(1,2),ctx)
    value.update(undefined_when=dict(condition=name+'<=0',original_denominator='exists n >= start with n^exponent + phase(n) = 0'),
                 divergence_requires_original_domain=True)
    return result('centered_inverse_power_drift',value,
                  'При положительном показателе знаменатель строго положителен на исходной области. При неположительном показателе отдельно исключаем точные нули исходного знаменателя.',
                  'Положительный показатель даёт ведущий знакопеременный вклад s n⁻ᵖ и дрейф −s² n⁻²ᵖ. Среднее квадрата по периоду положительно, поэтому его суммируемость требует p>1/2.',
                  'На неположительном показателе и при определённых членах ненулевая положительная фаза повторяется, поэтому главный тест нарушается.',
                  inner_power=a,outer_power=p,period=cycle,first_index=start)


def affine_weighted_parity(raw,index,start,ctx,outputs):
    from integrals import affine
    if 'asymptotic_order' in outputs:raise Unsupported('No scalar asymptotic coefficient for an alternating term')
    n=('v',index);rest,waves=split_waves(raw,n)
    if len(waves)!=1 or waves[0][0]!='cos':raise Unsupported('No single alternating factor')
    poly=phase_polynomial(waves[0][1],index)
    if len(poly)!=2 or m.pi_multiple(poly[0]) not in (Fraction(0),Fraction(1),Fraction(-1)) or m.pi_multiple(poly[1]) not in (Fraction(-1),Fraction(1)):
        raise Unsupported('Only strict alternating signs are proved here')
    if ctx['parameters'] and rest[0]=='div' and rest[1]==ONE:
        a,b=affine(rest[2],index)
        if m.num(a) is not None and m.num(a)>0 and m.constant_defined(b,ctx):
            return result('shifted_harmonic_integer_poles',dict(classification='parameter_dependent',conditional_when='no excluded original index',
                                                                excluded_if=dict(affine_slope=a,affine_offset=b,index_at_least=start)),
                          'Исходный член недопустим ровно там, где его аффинный знаменатель обращается в ноль на целочисленном луче.',
                          'На хвосте амплитуда положительна, убывает к нулю и эквивалентна константе, делённой на индекс. Ряд сходится условно.',
                          first_index=start,slope=a,offset=b)
    factors=[];coefficient=ONE
    def visit(e,sign):
        nonlocal coefficient
        op=e[0]
        if op in ('mul','div'):
            visit(e[1],sign);visit(e[2],sign if op=='mul' else -sign);return
        if m.constant_defined(e,ctx):
            if m.sign(e,ctx) not in (-1,1):raise Unsupported('A possibly vanishing constant needs separate treatment')
            coefficient=mul(coefficient,e if sign>0 else m.div(ONE,e));return
        atom,p=(e[1],q(1,2)) if op=='sqrt' else (e[1],q(e[2])) if op=='pow' else (e[1],e[2]) if op=='rpow' else (e,ONE)
        a,b=map(m.num,affine(atom,index));exponent=mul(q(sign),p)
        if a is None or b is None or a<=0 or not m.constant_defined(exponent,ctx):raise Unsupported('Unknown affine scale or exponent')
        at=a*start+b
        if at<0 or at==0 and (sign<0 or m.sign(p,ctx)!=1):raise Unsupported('Affine denominator or fractional power is singular at the first index')
        factors.append((q(a),q(b),exponent))
    visit(rest,1)
    d=m.neg(add_many(z[2] for z in factors));sign=m.sign(d,ctx)
    if sign==0 and not factors:raise Unsupported('No nonconstant amplitude')
    return result('affine_power_logarithmic_derivative',power_classes(d,ONE,ZERO,ctx),
                  'После проверки всех исходных оснований амплитуда похожа на постоянную степень n. Логарифмическая производная имеет главный коэффициент суммы показателей при 1/n.',
                  'При убывании к нулю применяем Лейбница, а модуль проверяем степенным сравнением. При неположительном порядке общий член не стремится к нулю.',
                  first_index=start,affine_factors=factors,coefficient=coefficient,decay=d)


def fractional_phase_weight(raw,index,start,ctx,outputs):
    from quadrature import enclose
    from verify import same_value
    if ctx['parameters'] or 'asymptotic_order' in outputs or raw[0]!='div' or raw[1][0] not in ('sin','cos'):
        raise Unsupported('No weighted phase correction of fixed coefficients')
    wave,den=raw[1:];angle=wave[1];n=('v',index)
    if angle[0]=='add':
        left,offset=angle[1:];l=phase_polynomial(left,index)
        if len(l)!=2 or not nonresonant(l[1],False) or offset[0]!='div' or m.num(offset[1]) is None or offset[2]!=n:
            raise Unsupported('Need an affine phase and an exact inverse-index increment')
        tail=max(3,start)
        for i in range(start,tail):
            lo,hi=enclose(m.substitute(den,{n:q(i)}),None)
            if not (lo>0 or hi<0):raise Unsupported('An original early weight may be singular')
        decay,absolute,rates=monomial_weight(m.div(ONE,den),index,tail,ctx)
        if not decay:raise Unsupported('The phase amplitude must decrease on a tail')
        return result('affine_phase_with_summable_quadratic_error',verdict(absolute,not absolute),
                      'В синусе или косинусе выделяем аффинную фазу и поправку c/n. Разложение угла даёт исходную гармонику, гармонику с дополнительным весом 1/n и ошибку O(n⁻²).',
                      'Две гармоники сходятся по суммированию по частям, остаток абсолютно суммируем. В несуммируемом весе квадрат возмущённой гармоники сохраняет положительную среднюю массу.',
                      affine_phase=l,correction=offset,amplitude_rates=rates,first_index=start,verified_tail=tail)
    if den[0]!='add' or den[1]!=n or den[2][0]!='mul' or m.num(den[2][1]) is None or not same_value(den[2][2],wave):
        raise Unsupported('No matching bounded oscillation in an affine denominator')
    amp=abs(m.num(den[2][1]));poly=phase_polynomial(angle,index)
    if len(poly)!=2 or not nonresonant(poly[1],False):raise Unsupported('No oscillating affine phase')
    tail=max(start,int(amp)+1)
    if tail-start>16:raise Unsupported('Early interval too large for exact domain check')
    for i in range(start,tail):
        lo,hi=enclose(m.substitute(den,{n:q(i)}),None)
        if not (lo>0 or hi<0):
            # At n=|coefficient|, equality would force a rational-affine angle to be an odd half-multiple of π.
            angle_at=m.simplify(m.substitute(angle,{n:q(i)}))
            if i!=amp or m.num(angle_at) is None:raise Unsupported('An original early denominator may vanish')
    return result('bounded_phase_denominator_remainder',verdict(False,True),
                  'Из знаменателя выделяем n и тот же ограниченный множитель, что в числителе. На хвосте разность с исходной гармоникой, делённой на n, ограничена C/n².',
                  'Гармоника с весом 1/n сходится по Дирихле. Её модуль не суммируем по положительной средней массе квадрата. Суммируемая поправка сохраняет оба вывода.',
                  phase=poly,denominator_amplitude=q(amp),first_index=start,verified_tail=tail)


def oscillatory_function_sets(task):
    allowed={'kind','terms','index','start_index','variables','stated_conditions','requested_output','id','source'}
    request=task.get('requested_output');names=task.get('variables');index=task.get('index');start=task.get('start_index')
    if (set(task)-allowed or not isinstance(names,list) or len(names)!=2 or type(start) is not int or start<1
            or request not in (['absolute_convergence_set','proof'],['conditional_convergence_set','proof'])):
        raise Unsupported('Need the full variable set for the requested trigonometric convergence question')
    p,x=names;n=('v',index);phase=mul(n,('s',x));power_index=('rpow',n,('s',p))
    if task.get('stated_conditions')!=['0<'+x+'<pi'] or not isinstance(task.get('terms'),list) or not task['terms']:
        raise Unsupported('The angle restriction must exclude both resonant endpoints')
    ctx=index_context(index,names,[])
    atoms=[]
    for s in task['terms']:
        e=m.parse(s,index,names)
        if e[0]!='div' or e[2]!=power_index or e[1][0] not in ('cos','sin') or m.simplify(e[1][1])!=phase:
            raise Unsupported('The terms must have the checked common power amplitude and angle')
        atoms.append(e[1][0])
    return result('nonresonant_trigonometric_parameter_sets',dict({request[0]:f'{p}>1' if request[0]=='absolute_convergence_set' else f'0<{p}<=1'},angle_condition=f'0<{x}<pi'),
                  'Для 0<x<π геометрические суммы гармоник x и 2x ограничены. Первая частота даёт сходимость по Дирихле при p>0.',
                  'Квадрат гармоники имеет постоянную часть 1/2 и сходящуюся взвешенную часть при p>0. Для 0<p≤1 это даёт расходимость ряда модулей.',
                  'При p≤0 сам член не стремится к нулю, поскольку средний квадрат гармоники равен 1/2. При p>1 модуль сравнивается со сходящимся степенным рядом.',
                  components=atoms,index=index,first_index=start)


def harmonic_rearrangement(task):
    from verify import same_value
    fields={'kind','source','id','statement','original_term','given_sum','order'}
    ordering=task.get('order')
    if (set(task)-fields or not isinstance(ordering,dict) or set(ordering)!={'positive_terms_then_negative_terms','within_each_sign'}
            or ordering['within_each_sign']!='original order' or not isinstance(task.get('statement'),str)
            or not task['statement'].startswith('Зная сумму знакопеременного гармонического ряда ') or 'найти сумму переставленного ряда' not in task['statement']):
        raise Unsupported('Need a prefix-preserving block permutation and a known alternating harmonic sum')
    counts=ordering['positive_terms_then_negative_terms']
    if not isinstance(counts,list) or len(counts)!=2 or any(type(c) is not int or c<1 for c in counts):raise Unsupported('Every sign must occur in each block')
    term=m.parse(task['original_term'],'n');given=m.parse(task['given_sum'],None)
    if not same_value(given,('ln',q(2))) or term!=m.parse('(-1)^(n+1)/n','n'):
        raise Unsupported('The sign or harmonic normalization differs')
    p,q0=counts;answer=add(given,mul(q(1,2),('ln',q(p,q0))))
    return result('harmonic_rearrangement_from_prefix_counts',dict(sum=answer),
                  'После B блоков использованы первые pB положительных и первые qB отрицательных членов. Каждое исходное место появляется ровно один раз.',
                  'Их сумму выражаем через H_(2pB)−H_(pB)/2−H_(qB)/2. В разности сокращаются log B и постоянная Эйлера; внутри блока остаток стремится к нулю.',
                  positive_count=p,negative_count=q0,first_index=1)


def summability_statement(task):
    """Read a closed quantified series statement, preserving all its premises."""
    if set(task)-{'kind','source','id','statement','requested_output'} or task.get('requested_output',['proof'])!=['proof']:
        raise Unsupported('Unbound additional conclusion in the series statement')
    text=task['statement'];origin=task.get('source',{});label=origin.get('literal_requirement',origin.get('printed_instruction',text))
    equivalent_label=isinstance(label,str) and label.replace('Q_q(x) != 0','Q_q(x)>0')==text
    if not isinstance(text,str) or label!=text and not equivalent_label or set(origin)-SOURCE_META:
        raise Unsupported('The source theorem and printed question disagree')
    if re.fullmatch(r'Доказать, что члены условно сходящегося ряда можно, сохраняя порядок, сгруппировать в абсолютно сходящийся ряд\.',text):
        return result('absolute_grouping_from_cauchy_cutoffs',dict(proved=True,positive_block_lengths=True),
                      'По критерию Коши выбираем возрастающие границы N_j так, чтобы любая сумма хвоста за N_j имела модуль ≤2⁻ʲ.',
                      'Из суммы от N_j+1 до N_(j+1) получается очередной блок. Абсолютные величины блоков имеют суммируемую геометрическую мажоранту. Порядок членов сохраняется.',
                      block_majorant='2^(-j)')
    motion=re.fullmatch(r'Доказать сохранение суммы сходящегося ряда при перестановке, передвигающей каждый член максимум на заранее фиксированные (\w+) мест\.',text)
    if motion:
        return result('bounded_permutation_preserves_prefix_limit',dict(proved=True,sum_preserved=True),
                      'Префикс после перестановки может отличаться от исходного только в окне ширины 2m около его конца.',
                      'Модуль разности ограничен длиной окна, умноженной на супремум модуля общего члена в хвосте. По сходимости этот супремум стремится к нулю.',
                      fixed_displacement=motion[1],tail_error='2*m*sup_{j>N-m}|a_j|')
    if re.fullmatch(r'Доказать сходимость sum a_n, если a_n→0, sum A_n сходится, A_n=sum\(a_i,i=p_n\.\.p_\(n\+1\)-1\), 1=p_1<p_2<…, а длины блоков ограничены\.',text):
        return result('bounded_block_remainders',dict(proved=True,original_series_converges=True),
                      'Граничные частичные суммы сходятся как суммы блоков. Любая исходная частичная сумма отличается от ближайшей граничной не более чем на M умноженное на максимальный модуль члена в хвосте.',
                      'Из a_n→0 и фиксированности предельной длины блока M следует сходимость всех исходных частичных сумм.',
                      partial_block_error='M*sup_{j>=p_n}|a_j|')
    ratio=re.fullmatch(r'Доказать сходимость знакопеременного ряда sum\(\(-1\)\^\(n-1\)\*([a-z])_n\), \1_n>0, если \1_n/\1_\(n\+1\)=1\+([a-z])/n\+o\(1/n\), \2>0\. Ссылка на №\d+\.',text)
    if ratio:
        return result('ratio_drift_implies_alternating_null_amplitude',dict(proved=True,converges=True),
                      'Положительное отношение соседних амплитуд на хвосте не меньше 1+p/(2n), поэтому амплитуда убывает.',
                      'Сумма логарифмов этих отношений уходит к +∞ по гармоническому сравнению. Следовательно, амплитуда стремится к нулю и применяется признак Лейбница.',
                      amplitude=ratio[1],positive_ratio_coefficient=ratio[2])
    phase=re.fullmatch(r'Доказать, что ряд sum\((sin|cos)\(n\*([a-z])\)/n,n=1\.\.inf\) не сходится абсолютно для каждого \2 из \(0,pi\)\.',text)
    if phase:
        return result('harmonic_lower_bound_from_squared_phase',dict(proved=True,absolute_convergence=False),
                      'Модуль гармоники не меньше её квадрата. Квадрат равен 1/2 плюс гармоника удвоенной частоты с коэффициентом ±1/2.',
                      'В интервале 0<x<π удвоенная частота нерезонансна, поэтому её ряд с весом 1/n сходится. Остаётся расходящаяся половина гармонического ряда.',
                      component=phase[1],angle=phase[2])
    if re.fullmatch(r'Для R\(x\)=P_p\(x\)/Q_q\(x\) с ненулевыми старшими коэффициентами и Q_q\(x\)>0 при всех вещественных x>=n0 исследовать абсолютную и условную сходимость sum\(\(-1\)\^n\*R\(n\),n=n0\.\.inf\)\.',text):
        return result('rational_amplitude_degree_gap',dict(absolute_if='q-p>1',conditional_if='0<q-p<=1',divergent_if='q-p<=0'),
                      'Положительность знаменателя на исходном луче исключает все полюсы. Знак ведущего коэффициента фиксирует знак рациональной амплитуды на хвосте.',
                      'Если q−p>0, модуль амплитуды сравним с n^(p−q), а его производная в ведущем порядке отрицательна. Применяем Лейбница и степенное сравнение. При q−p≤0 общий член не стремится к нулю.',
                      degree_gap='q-p')
    raise Unsupported('No bound quantified grouping, convergence, or permutation theorem')


def diverging_rearrangement(task):
    if set(task)-{'kind','id','source','statement'}:raise Unsupported('A single rearrangement goal is required')
    text=task['statement'];origin=task.get('source',{})
    s=re.fullmatch(r'Построить перестановку членов sum\((.+),([A-Za-z_]\w*)=1\.\.inf\), делающую ряд расходящимся\.',text)
    if not s or origin.get('literal_requirement',text)!=text:raise Unsupported('The original permutation question differs')
    index=s[2];n=('v',index);ctx=index_context(index,[],[]);e=m.parse(s[1],index)
    if e[0]!='div' or fixed_cycle(e[1],index,1)!=(ONE,q(-1)):
        raise Unsupported('Need positive odd and negative even original terms')
    p=index_power(e[2],n);d=m.num(p)
    if d is None or not 0<d<=1:raise Unsupported('Both signed subseries must have unbounded magnitudes and null terms')
    return result('rearrangement_crossing_increasing_targets',dict(proved=True,construction='at stage j add the next negative term and at least one next positive term, then positives until the sum exceeds j',diverges_to='+inf'),
                  'Положительная подпоследовательность имеет расходящуюся сумму, поэтому каждый этап заканчивается за конечное число шагов. Берём по одному следующему отрицательному и хотя бы одному положительному члену на каждом этапе.',
                  'Используются все исходные места ровно один раз. Граничные суммы превышают номер этапа. Внутри следующего этапа падение ограничено одним отрицательным членом, который стремится к нулю.',
                  decay=p,positive_sign_at_first_index=True)


def logarithmic_variable_exponents(raw,index,start,ctx,task,outputs,library):
    from tasks import source
    n=('v',index);logn=('ln',n);p=raw;orientation=1
    if p[0]=='div' and p[1]==ONE and p[2][0]=='rpow':
        p=p[2];orientation=-1
    if p[0]=='rpow' and p[1]==n:
        exponent=p[2];fixed=ZERO;correction=exponent
        if exponent[0]=='add':fixed,correction=exponent[1:]
        fixed=mul(q(orientation),fixed)
        if not m.constant_defined(fixed,ctx):raise Unsupported('Expected an independently fixed leading exponent')
        small=correction[2] if correction[0]=='mul' and correction[1]==q(-1) else correction
        sign=-orientation if small!=correction else orientation
        if small[0]=='div' and m.constant_defined(small[1],ctx):
            k,den=small[1:]
            if den==logn:
                coefficient=('exp',mul(q(sign),k));bad=[1] if start==1 else []
            else:
                d=index_power(den,n)
                if m.sign(d,ctx)!=1:raise Unsupported('Variable exponent must be a vanishing positive power')
                coefficient=ONE;bad=[]
        else:raise Unsupported('No checked logarithmic or power correction to the exponent')
        answer=power_classes(m.neg(fixed),ONE,ONE,ctx)
        if 'asymptotic_order' in outputs:answer['asymptotic_order']=dict(index_power=m.neg(fixed),equivalent_coefficient=coefficient)
        if bad:answer=dict(classification='undefined',undefined_indices=bad,tail_classification=answer)
        return result('normalize_variable_index_exponent',answer,
                      'Переписываем переменную степень как экспоненту показателя, умноженного на ln n. Логарифмическая добавка даёт точную постоянную, а добавка обратной степени стремится к нулю.',
                      'Проверяем исходный первый индекс, если в показателе появился делитель ln n. На хвосте применяем степенное сравнение.',
                      leading_exponent=fixed,correction=correction,first_index=start)
    if (raw[0]=='add' and raw[1][0]=='rpow' and raw[1][1]==n and m.simplify(raw[2])==q(-1)
            and 'asymptotic_order' not in outputs):
        h=raw[1][2]
        if not no_real_holes(h,index,start,ctx):raise Unsupported('The exponent has an unresolved original hole')
        try:d=m.neg(index_power(h,n));c=ONE
        except Unsupported:
            if ctx['parameters']:raise Unsupported('Need a checked fixed-parameter class for the inner growth')
            profile,_=germ_profiles(h,index,[],[],ctx,library)
            if not profile:raise Unsupported('No first nonzero exponent')
            d,c=profile[0]
        if m.sign(c,ctx) not in (-1,1):raise Unsupported('The coefficient of the exponent may vanish')
        return result('exponential_increment_with_logarithmic_scale',power_classes(d,ONE,ONE,ctx),
                      'Вычитаем единицу из exp(h(n) ln n). Когда h убывает как ненулевая степень n⁻ᵈ при d>0, разность эквивалентна h(n) ln n.',
                      'Порог сходимости остаётся d>1, включая расходимость на d=1. При d≤0 аргумент экспоненты не стремится к нулю.',
                      exponent=h,leading_decay=d,leading_coefficient=c,first_index=start)
    raise Unsupported('No normalizable variable exponent in the source')


def alternating_exponent_correction(raw,index,start,ctx,outputs):
    if 'asymptotic_order' in outputs:raise Unsupported('The alternating term has no signed scalar equivalent')
    from tasks import source
    n=('v',index);amplitude,waves=split_waves(raw,n)
    if len(waves)!=1 or waves[0][0]!='cos':raise Unsupported('A single alternating phase is required')
    ph=phase_polynomial(waves[0][1],index)
    if len(ph)!=2 or m.pi_multiple(ph[0]) not in (Fraction(0),Fraction(1),Fraction(-1)) or m.pi_multiple(ph[1]) not in (Fraction(1),Fraction(-1)):
        raise Unsupported('A strictly alternating integer phase is required')
    weight=ONE;special=amplitude;sign=1
    if amplitude[0]=='div':
        if amplitude[1]==ONE:special=amplitude[2];sign=-1
        else:special,weight=amplitude[1],m.div(ONE,amplitude[2])
    if special[0]!='rpow' or special[1]!=n:raise Unsupported('No variable exponent correction to the index')
    exponent=special[2];fixed=ZERO;correction=exponent
    if exponent[0]=='add':fixed,correction=exponent[1:]
    if not m.constant_defined(fixed,ctx) or correction[0]!='div' or not m.constant_defined(correction[1],ctx):
        raise Unsupported('No independent main exponent and an explicit inverse-power correction')
    d=index_power(correction[2],n);main=mul(q(-sign),fixed)
    if m.sign(d,ctx)!=1:raise Unsupported('The correction does not tend to zero rapidly enough')
    if weight==ONE:answer=power_classes(main,ONE,ZERO,ctx)
    else:
        if main!=ZERO:raise Unsupported('Need a separate mixed power and log boundary')
        decay,absolute,rates=monomial_weight(weight,index,start,ctx)
        if not decay:raise Unsupported('The retained amplitude does not decrease eventually')
        answer=verdict(absolute,not absolute)
    return result('alternating_variable_exponent_amplitude',answer,
                  'Записываем поправку к степени как exp(c ln(n)/n^d); она стремится к 1. Амплитуда сравнима с исходной главной степенью или логарифмическим весом.',
                  'При строгом убывании ведущего степенного или логарифмического веса его логарифмическая производная господствует над производной поправки. Это даёт нужную монотонность для Лейбница.',
                  'Модуль проверяем по исходному главному весу. При нулевом либо растущем степенном порядке общий член не стремится к нулю.',
                  decay_power=main,correction_order=d,first_index=start)


def fixed_geometric_profile(raw,index,start,ctx,outputs):
    """Separate an explicit integer geometric coordinate and its positive power weight."""
    from integrals import affine
    from tasks import source
    if 'asymptotic_order' in outputs:raise Unsupported('A geometric scale needs a different explicit asymptotic output')
    n=('v',index);amplitude,waves=split_waves(raw,n);bases=[];variable_base=False
    if waves:
        ph=phase_polynomial(waves[0][1],index)
        if (len(waves)!=1 or waves[0][0]!='cos' or len(ph)!=2 or m.pi_multiple(ph[0]) not in (Fraction(0),Fraction(1),Fraction(-1))
                or m.pi_multiple(ph[1]) not in (Fraction(-1),Fraction(1))):
            raise Unsupported('Expected an unsigned series or pure alternating signs')
    def collect(e):
        nonlocal variable_base
        tag=e[0]
        if tag=='mul':return ('mul',collect(e[1]),collect(e[2]))
        if tag=='div':return ('div',collect(e[1]),e[2])
        if tag=='rpow':
            try:a,b=map(m.num,affine(e[2],index))
            except Unsupported:return e
            if a is not None and a.denominator==1 and a>0 and b==0:
                if m.constant_defined(e[1],ctx):bases.append(m.power(e[1],int(a)));return ONE
                if a==1 and no_real_holes(e[1],index,start,ctx):
                    pp=phase_polynomial(e[1],index) if e[1][0]!='div' else ()
                    if pp:raise Unsupported('A polynomial geometric base is unbounded')
                    from finite_sums import rational_on_tail
                    p,d=rational_on_tail(e[1],index,start)
                    if len(p)>len(d):raise Unsupported('The root factor needs a finite limit')
                    root=abs(p[-1]/d[-1]) if len(p)==len(d) else 0
                    variable_base=True;bases.append(q(root));return ONE
        return e
    weight=collect(amplitude)
    if not bases:raise Unsupported('No multiplicative integer geometric scale')
    scale=mul(ONE,bases[0])
    for base in bases[1:]:scale=mul(scale,base)
    coeff,rates,atoms=logarithmic_monomial(weight,n,ctx)
    if m.sign(coeff,ctx)!=1 or any(constant_sign(m.substitute(a,{n:q(start)}),ctx)!=1 for a in atoms.values()):
        raise Unsupported('The nonoscillating amplitude or an original base is not defined and positive')
    if any(m.num(d) is None for d in rates):raise Unsupported('A fixed polynomial or logarithmic weight is required')
    rate=m.simplify(('abs',scale));diff=m.sign(add(rate,q(-1)),ctx)
    if diff in (-1,1):answer=verdict(diff<0)
    else:
        if variable_base:raise Unsupported('A varying geometric base on the unit boundary needs a next-order estimate')
        abs_boundary=logarithmic_classification(rates,ctx)['absolute_convergence'];decays=next((m.sign(d,ctx) for d in rates if d!=ZERO),0)==-1
        nonnegative=all(m.known_nonnegative(f,ctx) for f in bases)
        conditional=bool(not abs_boundary and decays and waves and nonnegative)
        if not abs_boundary and decays and not nonnegative:
            raise Unsupported('Both signs of the original geometric boundary need their own phase rule')
        boundary=verdict(abs_boundary,conditional)
        answer=boundary if diff==0 else branches([(source(rate)+'<1',verdict(True)),(source(rate)+'=1',boundary),(source(rate)+'>1',verdict())])
    return result('geometric_scale_and_weight_boundary',answer,
                  'Из n-го корня модуля получаем предел геометрического множителя. Строго внутри единичного круга получаем абсолютную сходимость, снаружи общий член не стремится к нулю.',
                  'В возможной граничной ветви геометрический множитель оставляет только постоянный знак либо проверенное чередование. Тогда применяем степенное сравнение или Лейбница к оставшемуся весу.',
                  geometric_scale=scale,amplitude_rates=rates,first_index=start)


def discrete_growth_series(text,index,start,ctx,outputs):
    from tasks import source
    if 'asymptotic_order' in outputs:raise Unsupported('A distinct leading asymptotic constant is not requested here')
    n=('v',index);iv=re.escape(index)
    prefix=re.fullmatch(r'sum\((.+),([A-Za-z_]\w*)=(\d+)\.\.'+iv+r'\)/(.+)',text.replace(' ',''))
    if prefix:
        body,k,lo,den=prefix.groups();lo=int(lo)
        if not 1<=lo<=start:raise Unsupported('The source summation starts outside its range')
        term=m.parse(body,k,(),('factorial',));bottom=m.parse(den,index,ctx['parameters'],('factorial',))
        z=('v',k)
        if term==('factorial',z) and bottom[0]=='factorial' and not ctx['parameters']:
            from integrals import affine
            a,b=map(m.num,affine(bottom[1],index))
            if a is not None and b is not None and a.denominator==b.denominator==1 and a>=2 and a*start+b>=0:
                return result('finite_monotone_factorial_sum_majorant',verdict(True),
                              'Конечная сумма возрастающих факториалов не превосходит n·n!. На хвосте в факториале знаменателя остаётся линейно много множителей больше n, дающих геометрическую мажоранту.',
                              factorial_slope=q(a),factorial_offset=q(b),first_index=start)
        rates=logarithmic_monomial(term,z,index_context(k,[],[]))[1]
        if len(rates)!=2 or rates[0]!=ZERO or m.sign(rates[1],ctx)!=1 or m.num(rates[1]) is None:
            raise Unsupported('No growing fixed logarithmic density in the finite sum')
        if lo==1 and m.num(rates[1])<1:raise Unsupported('An endpoint log power may require a separate zero branch')
        p=index_power(bottom,n)
        if not m.constant_defined(p,ctx):raise Unsupported('The denominator power must be fixed')
        d=add(p,q(-1));answer=power_classes(d,ONE,ONE,ctx)
        return result('monotone_prefix_mass_comparison',answer,
                      'Сверху оцениваем конечную сумму последним весом, умноженным на число слагаемых. Снизу берём последнюю половину слагаемых.',
                      'Это две положительные кратные n, умноженного на нужную степень ln n. Граничный вес с индексной степенью −1 расходится.',
                      logarithmic_power=rates[1],denominator_power=p,first_index=start)
    e=m.parse(text,index,ctx['parameters'],('factorial','decimal_digit_count'))
    lnf=('ln',('factorial',n));digits=('decimal_digit_count',n)
    if e[0]=='div' and ((e[1] in (lnf,digits)) or e[2]==lnf and e[1]==ONE):
        if e[2]==lnf:
            if start<2:raise Unsupported('The first logarithm of a factorial is zero')
            proxy=m.div(ONE,m.mul(n,('ln',n)))
        else:
            proxy=m.div(m.mul(n,('ln',n)) if e[1]==lnf else ('ln',n),e[2])
        _,rates,bases=logarithmic_monomial(proxy,n,ctx)
        # The parsed non-special factor is independently defined at every retained index.
        if e[2]!=lnf and any(a!=n for a in bases.values() if a!=('ln',n)):
            raise Unsupported('A higher logarithmic denominator needs independent domain checks')
        if e[2]!=lnf and (not no_real_holes(e[2],index,start,ctx) or not guard_on_ray(('nonzero',e[2]),index,start,ctx)):
            raise Unsupported('An original denominator guard remains')
        return result('logarithmic_size_of_factorials_and_digits',logarithmic_classification(rates,ctx),
                      'Число цифр составляет фиксированную кратную ln n с ограниченной ошибкой. Логарифм n! есть сумма ln k и сравним с n ln n по последней половине слагаемых.',
                      'Степенные и логарифмические множители сравниваем с пограничными рядами. Ранние нули логарифма проверяются в исходной формуле.',
                      comparison=m.simplify(proxy),rates=rates,first_index=start)
    if e[0]=='div' and e[1]==('factorial',n) and e[2][0]=='rpow' and e[2][1]==n:
        d=index_power(e[2][2],n)
        if m.num(d) is not None and m.num(d)<1:
            return result('factorial_dominates_sublinear_exponent',verdict(),
                          'Логарифм факториала ограничен снизу суммой последних n/2 логарифмов. Она имеет порядок n ln n и господствует над n^d ln n при d<1, поэтому общий член растёт.',
                          denominator_exponent=d,first_index=start)
    raise Unsupported('No supported factorial, digit count, or monotone prefix comparison')


def integral_mass_series(text,index,start,ctx,outputs,library):
    from tasks import domain_conditions
    from quadrature import enclose
    if ctx['parameters'] or 'asymptotic_order' in outputs:raise Unsupported('Only a fixed integral-valued kernel is admitted')
    shape=re.fullmatch(r'(1/)?integral\((.+),([A-Za-z_]\w*)=(.+)\.\.(.+)\)',text.replace(' ',''))
    if not shape:raise Unsupported('No integral-valued summand')
    inverse,body,x,lo,hi=shape.groups();e=m.parse(body,x);a=m.parse(lo,index);b=m.parse(hi,index)
    n=('v',index);z=('v',x);local=index_context(x,[],[])
    if inverse is None and a==n and b==('add',n,ONE) and e[0]=='exp' and e[1][0]=='mul' and e[1][1]==q(-1):
        d=index_power(e[1][2],z)
        if m.num(d) is not None and m.num(d)>0:
            return result('adjacent_integrals_and_rapid_decay',verdict(True),
                          'Соседние интервалы складываются в один исходный несобственный интеграл. При положительном d плотность exp(−x^d) на хвосте меньше x⁻².',
                          decay_exponent=d,first_index=start)
    if a!=ZERO:raise Unsupported('The original integral does not start at zero')
    if inverse is None and b[0]=='div' and b[2]==n and m.constant_defined(b[1],ctx) and m.sign(b[1],ctx)==1:
        cap=enclose(m.div(b[1],q(start)),None)[1]
        for g,v in domain_conditions(e):
            low,high=enclose(v,(Fraction(0),cap))
            if not (low>=0 if g=='nonnegative' else low>0 if g=='positive' else low>0 or high<0):
                raise Unsupported('The initial compact integral may have an unproved singularity')
        from limit_proofs import local_coefficients
        jet,_,_=local_coefficients(e,x,'0','right',4,library)
        if not jet[1]:raise Unsupported('No nonzero first density coefficient')
        d,c=jet[1][0];decay=add(d,ONE)
        if m.sign(c,local) not in (-1,1) or m.sign(decay,local)!=1:raise Unsupported('A nonintegrable density or vanishing coefficient needs another route')
        return result('shrinking_integral_comparison',power_classes(decay,ONE,ONE,ctx),
                      'На уменьшающемся интервале остаток относительно ведущего члена плотности равномерно мал. Интегрирование степени прибавляет единицу к показателю затухания.',
                      'Проверяем область от нуля до самой большой исходной границы. Затем сравниваем полученный порядок с порогом степенного ряда.',
                      density_power=d,coefficient=c,upper_scale=b[1],first_index=start)
    if inverse and b==n and e[0] in ('sqrt','rpow'):
        p=q(1,2) if e[0]=='sqrt' else m.simplify(e[2]);co=polynomial_coefficients(e[1],z,local)
        if m.num(p) is None or m.num(p)<=0 or not co or m.sign(co.get(0,ZERO),local)!=1 or any(m.sign(v,local) not in (0,1) for v in co.values()):
            raise Unsupported('The growing density must be positive on the entire original ray')
        decay=add(ONE,mul(q(max(co)),p))
        return result('reciprocal_accumulated_integral_comparison',power_classes(decay,ONE,ONE,ctx),
                      'Положительность многочлена гарантирует существование и ненулевость исходного накопленного интеграла при всех индексах.',
                      'Его ядро сравнимо со степенью при бесконечности. Интегрируем двусторонние оценки на хвосте и применяем степенное сравнение к обратной величине.',
                      polynomial=sorted(co.items()),power=p,reciprocal_decay=decay,first_index=start)
    raise Unsupported('No sufficient comparison mass on the original integration range')


SOURCE_META={'pdf_sha256','pdf_page','pdf_pages','printed_page','exercise','printed_subpart','page_png_sha256','heading_page','parameter_notation',
             'printed_instruction','literal_requirement','printed_requirement','printed_group_heading','printed_term','lower_index_origin',
             'order_interpretation','method_requirement','explicit_required_method','explicit_imposed_method'}


def validate_source(task,outputs,method):
    origin=task.get('source',{})
    if not isinstance(origin,dict) or set(origin)-SOURCE_META:
        raise Unsupported('Additional printed claims must be represented in the proof')
    for label in ('literal_requirement','printed_instruction','printed_requirement','printed_group_heading'):
        if label not in origin:continue
        text=origin[label]
        if not isinstance(text,str):raise Unsupported('Nontextual printed requirement')
        if text.startswith('Определив порядок убывания общего члена') and 'asymptotic_order' in outputs:continue
        if text.startswith('Пользуясь интегральным признаком Коши, исследовать сходимость') and method=='cauchy_integral_test':continue
        if text.startswith('Сколько примерно надо взять членов ряда, чтобы получить его сумму с точностью до ') and 'verified_tail_bound' in outputs:
            printed=text.split('с точностью до ',1)[1].removesuffix('?');tol=task.get('tolerance')
            if tol and m.simplify(m.parse(printed,None))==m.simplify(m.parse(tol,None)):continue
        if text.rstrip('.') in ('Исследовать сходимость ряда','Исследовать сходимость следующих рядов','Исследовать сходимость ряда в напечатанном порядке, включая неполные блоки'):
            if 'convergence_classification' in outputs:continue
        if text=='Исследовать сходимость, где ν(n) — число цифр числа n.' and 'decimal_digit_count(' in task.get('term','') and 'convergence_classification' in outputs:continue
        if text.rstrip('.')=='Исследовать абсолютную и условную сходимость' and {'absolute_convergence','conditional_convergence'}<=set(outputs):continue
        if re.fullmatch(r'По заголовку для №\d+ исключена проверка абсолютной сходимости\. Исследовать сходимость\.',text) and set(outputs)=={'convergence_classification','justification'}:continue
        raise Unsupported('The requested mathematical method does not establish the printed requirement')
    if 'printed_term' in origin and origin['printed_term'].replace(' ','')!=str(task.get('term')).replace(' ',''):
        raise Unsupported('Source summand differs from its printed form')


def constant_sign(e,ctx):
    from quadrature import enclose
    s=m.sign(e,ctx)
    if s is not None or m.variable_in(e) or any(m.contains(e,('s',p)) for p in ctx['parameters']):return s
    try:lo,hi=enclose(e,None)
    except (Unsupported,ArithmeticError):return None
    return 1 if lo>0 else -1 if hi<0 else 0 if lo==hi==0 else None


def guard_on_ray(guard,index,start,ctx):
    from polynomial import NotRational, rf
    from tasks import known_guard
    g,e=guard;n=('v',index);r=('v','seriesOffset')
    if known_guard(guard,ctx) and not m.variable_in(e):return True
    if no_real_guard(g,e,index,start,ctx):return True
    if e[0]=='div' and g in ('positive','nonzero'):
        return all(guard_on_ray((g,a),index,start,ctx) for a in e[1:])
    if e[0]=='sec' and g in ('positive','nonzero'):
        return guard_on_ray((g,('cos',e[1])),index,start,ctx)
    if e[0]=='ln' and e[1][0]=='sec' and g in ('positive','nonnegative','nonzero'):
        return all(guard_on_ray(('positive',(wave,e[1][1])),index,start,ctx) for wave in ('sin','cos'))
    if e[0] in ('cosh','exp'):return True  # Original argument domains are all checked separately.
    if e[0]=='add' and e[1][0]=='sqrt' and e[2][0]=='mul' and e[2][1]==q(-1) and e[2][2][0]=='sqrt':
        return guard_on_ray((g,add(e[1][1],m.neg(e[2][2][1]))),index,start,ctx)
    if g=='positive' and e[0]=='add' and e[1]==('exp',ONE) and e[2][0]=='mul' and e[2][1]==q(-1):
        x=e[2][2]
        if x[0]=='rpow' and x[1]==('add',ONE,('div',ONE,n)) and x[2]==n:return True
    if e[0] not in ('sin','cos'):return False
    phase=m.simplify(m.div(e[1],PI));shifted=m.substitute(phase,{n:m.add(q(start),r)})
    try:p,d=rf(shifted,r[1])
    except (NotRational,ArithmeticError):return False
    if d[0]<0:p,d=tuple(-x for x in p),tuple(-x for x in d)
    if d[0]<=0 or any(x<0 for x in d):return False
    bands={'sin':(0,1),'cos':(Fraction(-1,2),Fraction(1,2))};lo,hi=bands[e[0]]
    p,d=tuple(p)+(0,)*max(0,len(d)-len(p)),tuple(d)+(0,)*max(0,len(p)-len(d))
    below=[x-lo*y for x,y in zip(p,d)];above=[hi*y-x for x,y in zip(p,d)]
    return all(v>=0 for v in (*below,*above)) and (g=='nonnegative' or below[0]>0 and above[0]>0)


def polynomial_coefficients(e,n,ctx):
    p,d=m.rational_form(e)
    den=m.poly_expr(d)
    if m.variable_in(den) or m.sign(den,ctx) not in (-1,1):raise Unsupported('No fixed nonzero polynomial denominator')
    coefficients=defaultdict(dict)
    for monomial,value in p.items():
        degree=0;fixed=[]
        for atom,k in monomial:
            if atom==n:degree=k
            elif m.variable_in(atom):raise Unsupported('A nonpolynomial source atom remains')
            else:fixed.append((atom,k))
        coefficients[degree][tuple(fixed)]=value
    return {degree:m.simplify(m.div(m.poly_expr(c),den)) for degree,c in coefficients.items()}


def original_series_domain(raw):
    from tasks import domain_conditions
    positive_fractional=set()
    def walk(e):
        if e[0]=='rpow':
            x=m.simplify(e[2]);p=m.num(x)
            if p is not None and p>0 and p.denominator%2==0 and m.constant_defined(e[2],dict(parameters=[],assumptions=[])):
                positive_fractional.add(e[1])
        for v in e[1:]:
            if isinstance(v,tuple):walk(v)
    walk(raw)
    if not positive_fractional:return domain_conditions(raw)
    def relax(e):
        out=[]
        for v in e[1:]:
            if isinstance(v,tuple):out.extend(relax(v))
        children={t for v in e[1:] if isinstance(v,tuple) for t in domain_conditions(v)}
        for g,x in domain_conditions(e):
            if (g,x) not in children:
                out.append(('nonnegative' if g=='positive' and e[0]=='rpow' and x==e[1] and x in positive_fractional else g,x))
        return out
    return list(dict.fromkeys(relax(raw)))


def no_real_guard(rel,e,index,start,ctx):
    from tasks import known_guard
    n=('v',index);fresh='seriesRay'
    while fresh in [index,*ctx['parameters']]:fresh+='_'
    extra={**ctx,'parameters':[*ctx['parameters'],fresh],
           'assumptions':[*ctx['assumptions'],dict(symbol=fresh,relation='positive')]}
    return all(known_guard((rel,m.substitute(e,{n:point})),c)
               for point,c in ((q(start),ctx),(m.add(q(start),('s',fresh)),extra)))


def germ_profiles(raw,index,params,conditions,ctx,library):
    """Discover leading inverse-index powers using the existing checked elementary jets."""
    from limit_proofs import local_coefficients
    n=('v',index);t=('v','seriesSmall')
    if t[1] in [index,*params]:raise Unsupported('No free variable for the reciprocal germ')
    def split_root(e):
        sign=ONE
        if e[0]=='mul' and m.num(e[1]) is not None:sign,e=e[1:]
        if e[0]=='sqrt' or e[0]=='rpow' and m.num(m.simplify(e[2])) is not None:
            exponent=q(1,2) if e[0]=='sqrt' else m.simplify(e[2])
            try:co=polynomial_coefficients(e[1],n,ctx)
            except Unsupported:pass
            else:
                d=max(co,default=0)
                if d and m.sign(co[d],ctx)==1:
                    regular=add_many(mul(v,m.power(t,d-k)) for k,v in co.items())
                    return mul(q(-d),exponent),mul(sign,power(regular,exponent))
        return None
    def reciprocal(e):
        if e==n:return m.div(ONE,t)
        if e[0]=='sec':return ('div',ONE,('cos',reciprocal(e[1])))
        return (e[0],*(reciprocal(c) if isinstance(c,tuple) else c for c in e[1:]))
    def collect(e):
        if m.constant_defined(e,ctx):return [(ZERO,m.simplify(e))],None
        op=e[0]
        if op in ('mul','div'):
            a,ar=collect(e[1]);b,br=collect(e[2])
            if op=='div' and (not b or m.sign(b[0][1],ctx) not in (-1,1)):
                raise Unsupported('The reciprocal germ has an unproved nonzero coefficient')
            if a and b and m.sign(a[0][1],ctx) in (-1,1) and m.sign(b[0][1],ctx) in (-1,1):
                (d,c),(f,k)=a[0],b[0]
                return ([(add(d,f),mul(c,k))] if op=='mul' else [(add(d,m.neg(f)),m.simplify(m.div(c,k)))]),None
        if op=='rpow' and m.constant_defined(e[2],ctx):
            b,br=collect(e[1]);p=m.simplify(e[2])
            if not b or m.sign(b[0][1],ctx)!=1:raise Unsupported('The positive real branch of a variable power is unproved')
            d,c=b[0]
            return [(mul(d,p),power(c,p))],None
        order_shift=ZERO;transformed=reciprocal(e)
        if op=='add':
            a,b=(split_root(x) for x in e[1:])
            if a and b and a[0]==b[0]:order_shift=a[0];transformed=m.add(a[1],b[1])
        jet,_,_=local_coefficients(transformed,t[1],'0','right',4,library,params,conditions)
        return [(add(order_shift,d),c) for d,c in jet[1]],add(order_shift,jet[2])
    return collect(raw)


def reciprocal_germ_series(raw,index,start,ctx,task,outputs,library):
    from tasks import domain_conditions,source
    if any(tag in task['term'] for tag in ('(-1)^','floor(','factorial','product(','sum(','integral(')):
        raise Unsupported('Discrete operators require their own shift or product certificate')
    original=original_series_domain(raw);guards=[];conditional=[];bad_indices=[];tail=start;n=('v',index)
    for g,e in original:
        if guard_on_ray((g,e),index,start,ctx):continue
        if not any(m.contains(e,('s',p)) for p in ctx['parameters']) and g in ('positive','nonzero','nonnegative'):
            for shift in range(1,4):
                if not guard_on_ray((g,e),index,start+shift,ctx):continue
                broken=[]
                for i in range(start,start+shift):
                    at=m.substitute(e,{n:q(i)});s=constant_sign(at,ctx)
                    def contradicts(rel,value):
                        return value in (-1,0) if rel=='positive' else value==0 if rel=='nonzero' else value==-1
                    if contradicts(g,s) or any(contradicts(rel,constant_sign(expr,ctx)) for rel,expr in domain_conditions(at)):
                        broken.append(i)
                    elif s is None or not m.constant_defined(at,ctx):break
                else:
                    bad_indices.extend(broken);tail=max(tail,start+shift);break
            else:raise Unsupported('Unproved original series guard: '+source(e))
            continue
        if g in ('positive','nonnegative'):
            try:cs=polynomial_coefficients(e,n,ctx)
            except Unsupported:pass
            else:
                if any(k>0 and m.sign(c,ctx)==1 for k,c in cs.items()) and all(k==0 or m.sign(c,ctx) in (0,1) for k,c in cs.items()):
                    conditional.append(source(m.simplify(m.substitute(e,{n:q(start)})))+('>0' if g=='positive' else '>=0'));continue
        guards.append((g,e))
    if guards:raise Unsupported('Parameter-domain cases required for '+', '.join(source(e) for _,e in guards))
    ps=ctx['parameters'];conditions=task.get('stated_conditions',[])
    profile,remainder=germ_profiles(raw,index,ps,conditions,ctx,library)
    if not profile:raise Unsupported('Need a nonzero leading coefficient or a proved zero identity')
    deg,coefficient=profile[0];s=m.sign(coefficient,ctx)
    if s==0:raise Unsupported('The proposed leading coefficient vanishes identically')
    if m.num(deg) is not None and m.num(deg)>1:answer=verdict(True)
    elif s in (-1,1) or not ps:answer=power_classes(deg,ONE,ONE,ctx)
    elif remainder is not None and m.num(deg) is not None and all(m.num(d)>1 for d,_ in profile[1:]) and m.num(remainder)>1:
        answer=branches([(source(coefficient)+'=0',verdict(True)),(source(coefficient)+'!=0',verdict())])
    elif m.num(deg) is None and (m.sign(coefficient,ctx)==1 or coefficient[0]=='rpow' and m.sign(coefficient[1],ctx)==1):
        answer=power_classes(deg,ONE,ONE,ctx)
    else:raise Unsupported('Need to resolve the zero-leading-coefficient cases')
    if 'asymptotic_order' in outputs:
        if s not in (-1,1) and not (coefficient[0]=='rpow' and m.sign(coefficient[1],ctx)==1):
            raise Unsupported('Asymptotic order requires a proved nonzero leading coefficient in every reported regime')
        answer.update(asymptotic_order=dict(index_power=deg,equivalent_coefficient=coefficient))
    if bad_indices:answer=dict(classification='undefined',undefined_indices=sorted(set(bad_indices)),tail_classification=answer)
    if conditional:answer=dict(classification='parameter_dependent',original_domain=conditional,when_defined=answer,otherwise='undefined at the first index')
    return result('reciprocal_jet_series_comparison',answer,
                  'Подставляем t=1/n и строим разложение в точке t=0 справа. Сопоставляем первую ненулевую степень с порогом степенного ряда.',
                  'Коэффициент фиксирован при каждом значении параметров. Проверяем его знак или нулевую ветвь и отдельно область всех исходных членов.',
                  first_index=start,verified_tail=tail,source_domain=original,leading_powers=profile,remainder_order=remainder)


def convergence_heading(task,*headings):
    src=task.get('source',{});method=task.get('method_requirement')
    for key in ('literal_requirement','printed_instruction','printed_requirement','printed_group_heading'):
        if src.get(key) not in (None,*headings):raise Unsupported('An additional printed series requirement remains')
    for key in ('method_requirement','explicit_required_method','explicit_imposed_method'):
        if src.get(key) not in (None,method):raise Unsupported('The printed method differs from the original mathematical input')
    if 'printed_term' in src and src['printed_term'].replace(' ','')!=task['term'].replace(' ',''):
        raise Unsupported('The original summand differs from the printed expression')


def affine_product_profile(task, library):
    from finite_sums import product_series_ratio
    from integrals import affine
    from tasks import domain_conditions, source
    from verify import same_value

    kind=task['kind'];start=task.get('start_index');index=task.get('index')
    text=task.get('term');outputs=task.get('requested_output',[])
    fields={'kind','id','source','term','index','start_index','index_domain','parameters','variables','variable',
            'requested_output','stated_conditions','method_requirement','original_qualifications','definition'}
    if (not library.data.get('affine_series_coefficients') or set(task)-fields
            or set(task.get('source',{}))-SOURCE_META or not isinstance(text,str)
            or type(start) is not int or start<0 or task.get('index_domain','integers')!='integers'
            or not isinstance(index,str) or not index.isidentifier()
            or task.get('stated_conditions',[])!=[] or task.get('method_requirement') not in GENERAL
            or not re.search(r'\b(product|prod|falling_factorial|rising_factorial)\s*\(',text)):
        raise Unsupported('Need a bound affine product on the original integer lattice')
    functional=kind=='functional_series_convergence_set';power_series=kind=='power_series_convergence_set'
    if kind=='series_convergence' and outputs and set(outputs)<=OUTPUTS-{'asymptotic_order'}:validate_source(task,outputs,task.get('method_requirement'))
    elif functional and outputs in (['absolute_convergence_set','proof'],['conditional_convergence_set','proof'],
                                    ['absolute_convergence_set','conditional_convergence_set','proof']):pass
    elif power_series and outputs in (['radius','open_interval','both_endpoint_classifications'],['complete_convergence_set']):pass
    else:raise Unsupported('The original requested comparison is not an affine-product classification')
    qualification=task.get('original_qualifications')
    if qualification not in (None,'start=0, general hypergeometric series; no parameter exclusions printed'):
        raise Unsupported('An unbound condition changes the domain of the series')
    names=list(task.get('parameters',task.get('variables',[])))
    if not names:
        names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)
                     -{index,'product','prod','falling_factorial','rising_factorial','factorial','e','pi'})
    if functional:convergence_heading(task,'Определить указанную область по ('+','.join(names)+').',
                                      'Определить области абсолютной и условной сходимости исходного функционального ряда.')
    if power_series:convergence_heading(task,'Определить радиус, интервал сходимости и исследовать обе граничные точки.',
                                        'Определить область сходимости гипергеометрического ряда.')
    coordinate=task.get('variable') if power_series else None
    if functional and 'falling_factorial' in text and len(names)==2:
        coordinate=next((p for p in names if re.search(r'\^\s*'+re.escape(index)+r'\b',text)
                         and re.search(r'(?:\*|\()\s*'+re.escape(p)+r'\s*\)\s*\^',text)),None)
    params=[v for v in names if v!=coordinate]
    if power_series and not isinstance(coordinate,str):raise Unsupported('A power coordinate must be specified')
    x=('s',coordinate) if coordinate else None;n=('v',index);ctx=index_context(index,params,[])
    products={};parity=False;coordinate_count=0
    raw=text.replace(' ','')
    dummy='seriesProductIndex'
    while dummy in raw or dummy in names:dummy+='_'
    def store(expression,k,lo):
        if start<lo-1 or k in [index,*params,coordinate]:raise Unsupported('An original product binder conflicts or its lower bound exceeds the first range')
        atom='seriesProduct'+str(len(products))
        while atom in raw or atom in names:atom+='_'
        products[atom]=(expression,k,lo)
        return atom
    def prefix(match):
        expression,k,lo,upper=match.groups()
        if upper!=index:raise Unsupported('The product bound differs from the series index')
        return store(expression,k,int(lo))
    raw=re.sub(r'product\(([^,]+),([A-Za-z_]\w*),(-?\d+),([A-Za-z_]\w*)\)',prefix,raw)
    raw=re.sub(r'prod\(([^,]+),([A-Za-z_]\w*)=(-?\d+)\.\.([A-Za-z_]\w*)\)',prefix,raw)
    raw=re.sub(r'\b'+re.escape(index)+r'!',lambda _:f'factorial({index})',raw)
    definition=task.get('definition')
    if definition not in (None,'falling_factorial(x,n)=product(x-j,j,0,n-1)'):
        raise Unsupported('The product definition is not the falling factorial')
    def factorial_power(match):
        tag,a,bound=match.groups()
        if bound!=index or a not in params:raise Unsupported('The factorial coefficient does not bind its original parameter and index')
        changing=dummy+'+'+a+'-1' if tag=='rising' else dummy+'-'+a+'-1'
        product=store(changing,dummy,1)
        return product if tag=='rising' else f'((-1)^{index}*{product})'
    raw=re.sub(r'(falling|rising)_factorial\(([A-Za-z_]\w*),([A-Za-z_]\w*)\)',factorial_power,raw)
    if not products or start==0 and not power_series:
        raise Unsupported('No positive-index product of fixed affine factors')
    term=m.parse(raw,index,[*params,*products,*([coordinate] if coordinate else [])],('factorial',))
    def rewrite(e,orientation=1):
        nonlocal parity,coordinate_count
        op=e[0]
        if op in ('mul','div'):
            return (op,rewrite(e[1],orientation),rewrite(e[2],orientation if op=='mul' else -orientation))
        if op=='rpow' and e[1]==q(-1):
            if domain_conditions(e[2]):raise Unsupported('The original integer sign exponent has a hole')
            a,b=map(m.num,affine(e[2],index))
            if a is None or b is None or a.denominator!=1 or b.denominator!=1:
                raise Unsupported('The sign phase requires an integer affine index')
            parity^=bool(a%2)
            return ONE
        if x is not None and m.contains(e,x):
            if orientation!=1 or e[0]!='rpow' or e[2]!=n:raise Unsupported('Variable power needs a numerator occurrence with the original index')
            if domain_conditions(e[1]):raise Unsupported('The original variable base has a hole')
            if not same_value(e[1],x):
                scale=m.simplify(m.substitute(e[1],{x:ONE}))
                if not m.constant_defined(scale,ctx) or m.sign(scale,ctx)!=1 or not same_value(e[1],m.mul(scale,x)):
                    raise Unsupported('The power coordinate has no proved positive scale')
                if scale!=('exp',ONE) and scale!=('e',):raise Unsupported('The logarithm of the fixed power scale must be verified')
                residual=('exp',n)
            else:residual=ONE
            coordinate_count+=1
            return residual
        if op=='s' and e[1] in products:
            body,k,lo=products[e[1]]
            expression=m.parse(body,k,params)
            if domain_conditions(expression) and expression[0]!='div':
                raise Unsupported('The original product factor has an unverified domain')
            if expression[0] not in ('mul','div'):
                slope,_=affine(expression,k)
                if m.sign(slope,ctx)==-1:
                    products[e[1]]=(source(m.neg(expression)),k,lo)
                    parity^=True  # The number of factors is n−lo+1.
        return e
    reduced=rewrite(term)
    if bool(coordinate)!=bool(coordinate_count) or coordinate_count>1:
        raise Unsupported('The series requires a single verified common power coordinate')
    text=source(reduced)
    for atom,(expression,k,lo) in products.items():
        text=re.sub(r'\b'+re.escape(atom)+r'\b',lambda _:f'prod({expression},{k}={lo}..{index})',text)
    text=re.sub(r'\bn!\b',f'factorial({index})',text) if index=='n' else text
    cert=product_series_ratio(dict(term=text,index=index,parameters=params,start_index=start),signed_denominator_products=True)
    if cert['leading_ratio']!=ONE or cert['half_order']!=ZERO:
        raise Unsupported('Need separate handling of the geometric or sub-exponential factor')
    h=cert['log_coefficient']
    terminated=[dict(integer_at_least=z['integer_at_least'],root=source(z['root'])) for z in cert['terminating_if']]
    verdict_right=power_classes(m.neg(h),q(1),ZERO if parity else q(1),ctx)
    if coordinate is not None:
        verdict_left=power_classes(m.neg(h),q(1),q(1) if parity else ZERO,ctx)
        value=dict(variable=coordinate,radius=ONE,open_interval=['-1','1'],at_left=verdict_left,at_right=verdict_right)
        if functional:
            value=dict(absolute_convergence_set={'interior':'abs('+coordinate+')<1','left':verdict_left['absolute_convergence'],
                                                 'right':verdict_right['absolute_convergence']},
                       conditional_convergence_set={'left':verdict_left['conditional_convergence'],'right':verdict_right['conditional_convergence']})
    elif functional:
        value={key:verdict_right[key.removesuffix('_set')] for key in outputs if key.endswith('_set')}
    else:value=verdict_right
    if terminated:value.update(terminating_numerator=terminated,terminating_branch='finite sum and absolute convergence wherever all original denominator factors are nonzero')
    if cert['undefined_if']:value.update(undefined_denominator=cert['undefined_if'])
    return result('affine_product_coefficient_ratio',value,
                  'Выделяем целую фазу и общий степенной множитель. Точное отношение модулей соседних координатных коэффициентов собирается из последних множителей конечных произведений.',
                  'Положительное отношение имеет вид 1+H/n+O(n⁻²). После логарифмирования остаток суммируется, поэтому модуль коэффициента эквивалентен C n^H. При H<0 отношение доказывает убывание на хвосте.',
                  'На границе общего степенного множителя отдельно проверяем знак и пороги H=−1, H=0. Нулевые множители обнуляют весь хвост, а исходный ненулевой начальный префикс сохраняется.',
                  first_index=start,coefficient_ratio=cert,phase=parity,zero_branches=terminated,scope=outputs)


def compare_growth_levels(task, lib):
    from integrals import affine
    from tasks import source

    fields={'kind','id','source','term','index','start_index','variables','variable','stated_conditions',
            'original_qualifications','requested_output'}
    kind=task['kind'];start=task.get('start_index');index=task.get('index')
    if (not lib.data.get('geometric_growth_levels') or set(task)-fields or set(task.get('source',{}))-SOURCE_META
            or not isinstance(index,str) or not isinstance(task.get('term'),str) or type(start) is not int or start<1):
        raise Unsupported('Every source exponential needs a bound positive integer lattice')
    outputs=task.get('requested_output')
    power_series=kind=='power_series_convergence_set'
    if power_series:
        if outputs!=['radius','open_interval','both_endpoint_classifications']:
            raise Unsupported('The original radius and two endpoint requirements must be explicit')
        convergence_heading(task,'Определить радиус, интервал сходимости и исследовать обе граничные точки.')
        x=task['variable'];given=task.get('original_qualifications','')
        conditions=given.split(',') if given else []
        if any(part.count('>')!=1 or not part.split('>')[0].isidentifier() or part.split('>')[1]!='0' for part in conditions):
            raise Unsupported('Fixed positive coefficients require proved source qualifications')
        names=[part.split('>')[0] for part in conditions]
    elif kind=='functional_series_convergence_set' and outputs==['absolute_convergence_set','conditional_convergence_set','proof']:
        if task.get('original_qualifications'):raise Unsupported('Unbound restrictions remain')
        convergence_heading(task,'Определить области абсолютной и условной сходимости исходного функционального ряда.')
        x=None;names=task['variables'];conditions=task.get('stated_conditions',[])
    else:raise Unsupported('The input is not a complete geometric parameter classification')
    nonnegative={part[:-3] for part in conditions if part.endswith('>=0') and part[:-3] in names}
    strict=[part for part in conditions if part not in {name+'>=0' for name in nonnegative}]
    ctx=index_context(index,names,strict)
    n=('v',index);v=('s',x)
    raw=m.parse(task['term'],index,[*names,*([x] if x else [])])
    phase=[];geometric_factors=0;coordinate_count=0
    def node(e,denominator=False):
        nonlocal geometric_factors,coordinate_count
        tag=e[0]
        if tag in ('add','mul','div'):
            a,positive_a,signed_a=node(e[1],denominator)
            b,positive_b,signed_b=node(e[2],denominator or tag=='div')
            if tag=='add' and (signed_a or signed_b) or tag=='div' and (signed_b or not positive_b):
                raise Unsupported('A sum can cancel or a divisor can vanish on the original domain')
            rule={'add':'lexicographic_max','mul':'multiply','div':'divide'}[tag]
            return [rule,a,b],(positive_a or positive_b) if tag=='add' else positive_a and positive_b,signed_a^signed_b
        if tag=='ln' and e[1][0]=='add' and ONE in e[1][1:]:
            tail=e[1][2] if e[1][1]==ONE else e[1][1]
            f,positive,signed=node(tail)
            if signed or f[:1]!=['geometric']:
                raise Unsupported('The original logarithm needs a nonnegative pure geometric increment')
            return ['logarithmic_increment',f],positive,False
        if tag in ('pow','rpow'):
            base,exp=e[1:]
            if tag=='pow':exp=q(exp)
            if base==n and m.constant_defined(exp,ctx):
                return ['index_power',source(exp)],True,False
            if tag=='rpow':
                a,b=map(m.num,affine(exp,index))
                if a is not None and a.denominator==1 and a>0 and b==0:
                    if x and base==v:
                        if denominator or a!=1:raise Unsupported('The power coordinate belongs once in the numerator')
                        coordinate_count+=1
                        return ['unit'],True,False
                    if not m.constant_defined(base,ctx):raise Unsupported('The base is not a fixed defined real expression')
                    geometric_factors+=1
                    even=a%2==0;positive=m.sign(base,ctx) in (1,-1) or m.nonzero(base,ctx)
                    signed=not even and not (m.known_nonnegative(base,ctx) or base[0]=='s' and base[1] in nonnegative)
                    if signed:phase.append(source(base))
                    return ['geometric',source(base),int(a)],positive,signed
        if e==n:return ['index_power','1'],True,False
        if m.constant_defined(e,ctx) and m.sign(e,ctx)==1:return ['unit'],True,False
        raise Unsupported('The original summand exceeds finite noncancelling geometric algebra')
    profile,positive,signed=node(raw)
    if not geometric_factors or x and coordinate_count!=1:
        raise Unsupported('There is no mixed geometric scale after extracting the common coordinate')
    def show(tree):
        op,*children=tree
        if op=='unit':return '1','0'
        if op=='geometric':
            base,power=children;r=base if base in nonnegative or base+'>0' in strict else f'abs({base})'
            return (r if power==1 else f'{r}^{power}'),'0'
        if op=='index_power':return '1',children[0]
        if op=='logarithmic_increment':
            growth,_=show(children[0])
            return f'min({growth},1)',f'1 if {growth}>1, else 0'
        a,d=show(children[0]);b,e=show(children[1])
        if op=='lexicographic_max':
            return f'max({a},{b})',d if d==e else f'{d} if {a}>{b}, {e} if {a}<{b}, max({d},{e}) if equal'
        if op=='multiply':
            return (b if a=='1' else a if b=='1' else f'({a})*({b})'),(e if d=='0' else d if e=='0' else f'({d})+({e})')
        return (a if b=='1' else f'({a})/({b})'),(d if e=='0' else f'-({e})' if d=='0' else f'({d})-({e})')
    rate,order=show(profile)
    if signed and not phase or not signed and phase:
        raise Unsupported('Separate signed factors may need an explicit parity comparison')
    if x:
        if signed or not positive:raise Unsupported('Coefficient function must be positive on the entire printed parameter domain')
        value=dict(variable=x,rate=rate,order=order,radius='1/rate',
                   open_interval=['-1/rate','1/rate'],
                   at_left={'absolute':'order<-1','conditional':'-1<=order<0','divergent':'order>=0'},
                   at_right={'absolute':'order<-1','conditional':'never','divergent':'order>=-1'})
    else:
        alternating='*'.join('sign('+z+')' for z in phase)+'=-1' if signed else 'never'
        value=dict(rate=rate,order=order,absolute_convergence_set='rate<1 or (rate=1 and order<-1)',
                   conditional_convergence_set=('rate=1 and -1<=order<0 and '+alternating) if signed else 'empty',
                   divergence='other admitted parameters',source_conditions=conditions)
    return result('finite_geometric_growth_levels',value,
                  'Положительные суммы сравниваем сначала по экспоненциальному темпу, затем по степени n. В произведении и частном темпы умножаются и делятся, а порядки складываются и вычитаются.',
                  'Логарифм 1+u эквивалентен u при u→0, стремится к ln 2 при u=1 и к n ln ρ в относительном смысле при u=ρ^n, ρ>1.',
                  'На границе ρ=1 ненулевая амплитуда эквивалентна C n^d. У конечных геометрических сумм и частных при d<0 отношение соседних амплитуд равно 1+d/n+o(1/n), поэтому применим Лейбниц при проверенном чередовании.',
                  'Нулевой геометрический множитель учитывается отдельно. Каждый знаменатель подтверждён как строго положительный у всех исходных индексов.',
                  index=index,original_first_index=start,positive_coefficient=positive,orientation_factors=phase,positive_domain=conditions,growth_profile=profile)


def logarithmic_growth_levels(task,lib):
    from tasks import domain_conditions, known_guard, source
    if (not lib.data.get('logarithmic_series_growth') or task.get('kind')!='series_convergence'
            or set(task)-ORDINARY_FIELDS-{'printed_index_condition'}
            or task.get('method_requirement') not in GENERAL or task.get('index_domain','integers')!='integers'):
        raise Unsupported('No compatible logarithmic series goal')
    index=task['index'];start=task['start_index'];outputs=task.get('requested_output',[])
    if type(start) is not int or start<1 or task.get('printed_index_condition',f'{index}>{start-1}')!=f'{index}>{start-1}':
        raise Unsupported('The lower lattice bound does not match the mathematical input')
    if set(outputs)-{'convergence_classification','justification','definedness_at_each_printed_index'} or 'convergence_classification' not in outputs:
        raise Unsupported('Logarithmic growth does not recover the requested separate asymptotic equivalent')
    validate_source(task,outputs,task.get('method_requirement'))
    params=task.get('parameters',[]);ctx=index_context(index,params,task.get('stated_conditions',[]))
    n=('v',index);L=('ln',n)
    raw=m.parse(task['term'],index,params)
    reciprocal=raw[0]=='div' and raw[1]==ONE
    core=raw[2] if reciprocal else raw
    if core[0]=='rpow' and not params and core[1][0]=='ln' and (core[2]==n or core[2][0]=='ln'):
        def depth(e):
            if e==n:return 0
            if e[0]=='ln':return 1+depth(e[1])
            raise Unsupported('This variable power needs two iterated logarithm factors')
        level=depth(core[1]);weight=depth(core[2])
        if level:
            bad=[];tail=None
            guards=[(relation,g) for relation,g in domain_conditions(raw) if g!=core]
            for k in range(start,start+24):
                signs=[constant_sign(m.substitute(g,{n:q(k)}),ctx) for _,g in guards]
                if any(s==0 or s==-1 and relation=='positive' for (relation,_),s in zip(guards,signs)):
                    bad.append(k);continue
                if any(s is None for s in signs):raise Unsupported('An original logarithm sign remains open')
                tail=k;break
            if tail is None:raise Unsupported('No positive iterated-log ray found from the given source')
            # Every iterated log is increasing once its defining subtree is positive.
            answer=verdict(reciprocal and weight<=1)
            if bad:answer=dict(classification='undefined',undefined_indices=bad,tail_classification=answer)
            return result('iterated_logarithm_power_comparison',answer,
                          'Проверяем начальные индексы исходного выражения. После первого положительного значения все необходимые вложенные логарифмы определены и возрастают.',
                          'Логарифм модуля члена равен ± произведению двух итераций ln. Делим на ln n. Для обратной степени с показателем порядка не меньше ln n отношение стремится к −∞; при более глубокой итерации отношение стремится к нулю. Для прямой степени член растёт.',
                          original_term=raw,first_index=start,verified_tail_start=tail,log_base_depth=level,log_exponent_depth=weight)
    if core[0]=='exp':
        top,bottom=core[1][1:] if core[1][0]=='div' else (core[1],ONE)
    elif core[0]=='rpow' and m.constant_defined(core[1],ctx) and m.sign(core[1],ctx)==1:
        top,bottom=('mul',('ln',core[1]),core[2]),ONE
    else:raise Unsupported('No exponential with a proved fixed positive base')
    if reciprocal:top=('mul',q(-1),top)
    for e in (top,bottom):
        if any(g!=n and not known_guard((relation,g),ctx) for relation,g in domain_conditions(e)):
            raise Unsupported('An inner exponent factor has a source hole besides the separately analyzed quotient')
    variable='logarithmicCoordinate'
    while variable in (index,*params):variable+='_'
    t=('v',variable)
    p=polynomial_coefficients(m.substitute(top,{L:t}),t,ctx)
    d=polynomial_coefficients(m.substitute(bottom,{L:t}),t,ctx)
    if not p or not d or max(p)>3 or max(d)>1:
        raise Unsupported('Only a positive-index polynomial divided by an affine logarithm is covered')
    def polynomial_parts(rows):
        equal=[]
        for degree,coefficient in sorted(rows.items(),reverse=True):
            if m.sign(coefficient,ctx)==0:continue
            if m.sign(coefficient,ctx) in (1,-1):
                yield equal,degree,coefficient;return
            yield [*equal,source(coefficient)+'!=0'],degree,coefficient
            equal=[*equal,source(coefficient)+'=0']
        yield equal,None,ZERO
    regimes=[]
    for cond,deg,lead in polynomial_parts(d):
        if deg is None:
            regimes.append(dict(conditions=cond,classification='undefined',domain='all denominators zero'));continue
        holes=None if deg==0 else dict(index='exp(-('+source(d.get(0,ZERO))+')/('+source(lead)+'))',
                                    applies_if='integer at least '+str(start),classification='undefined at that index')
        for pre,order,co in polynomial_parts(p):
            offset=None if order is None else order-deg
            criterion='never' if offset is None or offset<=0 else '('+source(co)+')/('+source(lead)+')<'+('-1' if offset==1 else '0')
            regimes.append(dict(conditions=[*cond,*pre],absolute_convergence_if=criterion,
                                otherwise='divergent when defined',conditional_convergence=False,original_hole=holes))
    return result('exponential_of_logarithmic_rational_scale',dict(classification='by_parameter',regimes=regimes),
                  'Полагаем t=ln n. Сравниваем старшие ненулевые коэффициенты. Если частное ограничено, член не стремится к нулю. При линейном росте показателя получается степенное сравнение, включая гармоническую границу.',
                  'При более высоком росте отрицательный показатель даёт убывание быстрее любой степени, положительный — рост. Корень исходного аффинного знаменателя переносим обратно, до всех сокращений.',
                  original_term=raw,polynomial_in_log=p,denominator_in_log=d,first_index=start)


def ordinary_goal(task,library,request):
    from tasks import series_outputs
    if not library.data.get('ordinary_series_transitions'):raise Unsupported('Ordinary series transitions unavailable in this library')
    if task['kind']=='series_convergence' and task.get('term')=='concatenate_blocks':
        outputs=series_outputs(task)
        validate_source(task,outputs,task.get('method_requirement'))
        return finite_blocks(task)
    for transition in (logarithmic_growth_levels,affine_product_profile,compare_growth_levels,original_series_profiles,ordinary_transport_goal,residual_series_scales,remaining_series_claim):
        try:return transition(task,library)
        except Unsupported:pass
    kind=task['kind']
    if kind=='sequence_convergence':return partial_sum_error(task,request)
    if kind=='functional_series_convergence_set':return oscillatory_function_sets(task)
    if kind=='rearranged_series_sum':return harmonic_rearrangement(task)
    if kind=='construct_series_rearrangement':return diverging_rearrangement(task)
    if kind in ('series_theorem','series_proposition'):return summability_statement(task)
    if kind!='series_convergence':raise Unsupported('The statement requires a structured quantified-series representation')
    outputs=series_outputs(task);method=task.get('method_requirement')
    if set(task)-ORDINARY_FIELDS or method not in (*GENERAL,'cauchy_integral_test'):
        raise Unsupported('The additional source fields or method are not admitted by these transitions')
    validate_source(task,outputs,method)
    index=task['index'];text=task['term'];start=task['start_index']
    if not isinstance(text,str) or type(start) is not int or start<1 or task.get('index_domain','integers')!='integers':
        raise Unsupported('The original integer lattice must start at a positive literal index')
    if 'verified_tail_bound' in outputs:return positive_cutoff(task,outputs)
    if not outputs or set(outputs)-OUTPUTS:raise Unsupported('The mathematical question is not a convergence or asymptotic-order goal')
    params=task.get('parameters',[]);ctx=index_context(index,params,task.get('stated_conditions',[]))
    if 'floor(' in text:return floor_blocks(text,index,start,ctx,outputs)
    if 'periodic_sign(' in text:return periodic_sign_series(text,index,start,ctx,outputs)
    if method in GENERAL and 'integral(' in text:return integral_mass_series(text,index,start,ctx,outputs,library)
    if method in GENERAL and any(op+'(' in text for op in ('factorial','sum','decimal_digit_count')):
        return discrete_growth_series(text,index,start,ctx,outputs)
    raw=m.parse(text,index,params)
    if method=='cauchy_integral_test':return logarithmic_series(raw,index,start,ctx,method,outputs)
    try:return logarithmic_variable_exponents(raw,index,start,ctx,task,outputs,library)
    except Unsupported:pass
    reasons=[]
    signed=(centered_perturbations,polynomial_phase_series,affine_weighted_parity,fractional_phase_weight,alternating_exponent_correction)
    for operate in (() if method=='comparison_or_ratio_or_root' else signed):
        try:return operate(raw,index,start,ctx,outputs)
        except Unsupported as exc:reasons.append(str(exc))
    if method in GENERAL:
        try:return fixed_geometric_profile(raw,index,start,ctx,outputs)
        except Unsupported as exc:reasons.append(str(exc))
    try:return logarithmic_series(raw,index,start,ctx,method,outputs)
    except Unsupported as exc:reasons.append(str(exc))
    try:return reciprocal_germ_series(raw,index,start,ctx,task,outputs,library)
    except Unsupported as exc:raise Unsupported(str(exc)+'; '+'; '.join(reasons)) from None


def series_domain_answer(absolute, conditional='empty', domain=None, **facts):
    return dict(absolute_convergence_set=absolute, conditional_convergence_set=conditional,
                **(dict(original_domain=domain,sets_relative_to_original_domain=True) if domain is not None else {}), **facts)


def eliminate_unit(op,a,b):
    """Keep source factors intact while removing a neutral factor introduced by separation."""
    if b==ONE:return a
    if op=='mul' and a==ONE:return b
    return op,a,b


def coefficient_lattice_split(expression, index, coordinate, ctx):
    """Extract one affine power coordinate without deleting source guards."""
    from integrals import affine
    from tasks import domain_conditions
    from verify import same_value
    n=('v',index);x=('s',coordinate);bases=[]

    def separate(e, orientation):
        if not m.contains(e,x):return e
        if e[0] in ('mul','div'):
            a=separate(e[1],orientation);b=separate(e[2],orientation if e[0]=='mul' else -orientation)
            return eliminate_unit(e[0],a,b)
        if e[0]!='rpow' or e[2]!=n or orientation!=1 or domain_conditions(e[1]):
            raise Unsupported('Need a hole-free affine numerator coordinate to the original integer power')
        v=('v',coordinate);a,b=affine(m.substitute(e[1],{x:v}),coordinate)
        if m.num(a) is None or not m.num(a) or m.num(b) is None or not same_value(e[1],m.add(m.mul(a,x),b)):
            raise Unsupported('The extracted coordinate is not a verified nonconstant affine map')
        bases.append((a,b))
        return ONE

    coefficient=separate(expression,1)
    if len(bases)!=1:raise Unsupported('Expected a single independently verified affine coordinate')
    a,b=bases[0]
    return coefficient,a,m.div(m.neg(b),a)


def periodic_coefficient_root(e,index):
    """Find an exact even period from the syntactic integer phase before evaluation."""
    from math import gcd, lcm
    from tasks import domain_conditions, known_guard
    n=('v',index)
    if not m.contains(e,n):
        if domain_conditions(e) or m.sign(e,m.context(dict(variable=index))) is None:
            raise Unsupported('A periodic coefficient constant lacks a real defined sign')
        return 2
    if e[0] in ('add','mul'):
        return lcm(periodic_coefficient_root(e[1],index),periodic_coefficient_root(e[2],index))
    if e==('rpow',q(-1),n):return 2
    if e[0] in ('sin','cos') and all(known_guard(g,index_context(index,[],[])) for g in domain_conditions(e[1])):
        phase=phase_polynomial(e[1],index)
        if len(phase)==2 and (slope:=m.pi_multiple(phase[1])) is not None:
            return lcm(2,2*slope.denominator//gcd(abs(slope.numerator),2*slope.denominator))
    raise Unsupported('No exact finite period for the original coefficient base')


def periodic_radius_and_endpoints(raw,index,start,coordinate,ctx):
    """Compare integer residue classes, then check the two signed boundary series."""
    from tasks import source
    from verify import same_value
    coef,scale,center=coefficient_lattice_split(raw,index,coordinate,ctx);n=('v',index);bases=[]

    def extract(e, orientation=1):
        if e[0] in ('mul','div'):
            a=extract(e[1],orientation);b=extract(e[2],orientation if e[0]=='mul' else -orientation)
            return eliminate_unit(e[0],a,b)
        if e[0]=='rpow' and e[2]==n:
            if orientation<0:raise Unsupported('A denominator geometric base has separate integer poles')
            bases.append(e[1]);return ONE
        return e

    weight=extract(coef)
    if not bases:raise Unsupported('Need a coefficient base with a verified periodic dependence')
    base=ONE
    for e in bases:base=eliminate_unit('mul',base,e)
    period=periodic_coefficient_root(base,index)
    if period>64:raise Unsupported('Too many residue classes for exact phase evaluation')
    c,rates,logs=logarithmic_monomial(weight,n,ctx)
    if m.sign(c,ctx)!=1 or any(m.num(d) is None for d in rates) or any(
            constant_sign(m.substitute(l,{n:q(start)}),ctx)!=1 for l in logs.values()):
        raise Unsupported('The original weight is not a positive fixed logarithmic scale')
    if not no_real_holes(weight,index,start,ctx):
        raise Unsupported('A weight denominator could vanish at an original index')
    values=[m.simplify(m.substitute(base,{n:q(j),('rpow',q(-1),n):q((-1)**j)})) for j in range(period)]
    magnitudes=[m.simplify(('abs',z)) for z in values];maximum=ZERO
    for z in magnitudes:
        s=constant_sign(m.add(z,m.neg(maximum)),ctx)
        if s is None:raise Unsupported('Residue amplitudes cannot yet be ordered exactly')
        if s>0:maximum=z
    if maximum==ZERO:raise Unsupported('The identically zero coefficient needs a separate entire-series result')
    comparisons=[0 if same_value(z,maximum) else constant_sign(m.add(z,m.neg(maximum)),ctx) for z in magnitudes]
    if any(s not in (-1,0) for s in comparisons):
        raise Unsupported('The maximal classes must be completely identified')
    active=[j for j,s in enumerate(comparisons) if s==0]
    radius=m.div(ONE,m.mul(m.simplify(('abs',scale)),maximum))
    summable=logarithmic_classification(rates,ctx)['absolute_convergence']
    decays=next((m.sign(a,ctx) for a in rates if a!=ZERO),0)==-1
    ends=[]
    for side in (-1,1):
        signs=[(constant_sign(values[j],ctx)*m.sign(scale,ctx)*side)**j for j in active]
        ends.append(dict(point=add(center,m.mul(q(side),radius)),
                         classification='absolute' if summable else 'conditional' if decays and not sum(signs) else 'divergent',
                         dominant_class_signs=signs))
    return result('periodic_coefficient_dominant_classes',
                  dict(center=center,radius=radius,open_interval=[ends[0]['point'],ends[1]['point']],endpoints=ends),
                  'Вычисляем модуль экспоненциального основания на каждом классе индексов. Его максимум задаёт радиус по коренному признаку.',
                  'На каждой границе меньшие классы абсолютно суммируемы. Классы максимума оставляют периодический знак и один общий положительный вес.',
                  'При несуммируемом убывающем весе проверяем среднее знаков. Нулевое среднее даёт ограниченные частичные суммы и сходимость по Дирихле. Ненулевое среднее сохраняет расходящуюся часть.',
                  first_index=start,period=period,residue_bases=values,active_classes=active,weight_rates=rates)


def nonperiodic_power_profile(term,index,start,coordinate,qualification):
    """Use bounded or unbounded coefficient envelopes before testing boundary terms."""
    from tasks import domain_conditions
    n=('v',index);ctx=index_context(index,[coordinate],[]);marker='prefixMassCoefficient'
    while marker in term or marker in (index,coordinate):marker+='_'
    hit=re.search(r'sum_\{(\w+)=(\d+)\.\.'+re.escape(index)+r'\}\(([^()]+)\)',term)
    if hit:
        j,lo,body=hit.groups();lo=int(lo)
        if j in (index,coordinate) or not 1<=lo<=start:raise Unsupported('A finite coefficient sum has an invalid binder or empty first range')
        z=m.parse(body,j)
        try:p=index_power(z,('v',j))
        except Unsupported:
            if z[0]!='div' or z[1]!=ONE:raise
            p=m.neg(index_power(z[2],('v',j)))
        if not m.constant_defined(p,index_context(j,[],[])) or qualification:
            raise Unsupported('The prefix density needs an all-index positive fixed power')
        raw=m.parse(term[:hit.start()]+marker+term[hit.end():],index,[coordinate,marker])
        coef,scale,center=coefficient_lattice_split(raw,index,coordinate,ctx)
        if coef!=('s',marker):raise Unsupported('Additional coefficient weights need their own bounds')
        explanation='На конечной сумме степеней нижнюю границу даёт первый положительный член, верхнюю — число слагаемых, умноженное на наибольшую степень. Корни обеих границ стремятся к единице.'
        evidence=dict(prefix_first=lo,prefix_power=p)
    else:
        raw=m.parse(term,index,[coordinate],('digits10','floor'))
        try:coef,scale,center=coefficient_lattice_split(raw,index,coordinate,ctx)
        except Unsupported:
            x=('s',coordinate)
            if qualification or raw!=('rpow',('div',x,('sin',n)),n):
                raise
            return result('irrational_rotation_coefficient_poles',
                    dict(center=ZERO,radius=ZERO,open_interval=[],convergence_set=[ZERO],
                         endpoints=[dict(point=ZERO,classification='absolute')]),
                    'Для каждого положительного целого индекса sin n отличен от нуля по иррациональности π.',
                    'Плотность иррационального вращения даёт сколь угодно большие индексы, где |sin n|<|x|/2 при любом фиксированном x≠0. Члены не стремятся к нулю. В нуле они равны нулю.',
                    first_index=start,rotation='n modulo pi')
        if coef==('div',('rpow',q(10),('digits10',n)),n) and qualification==f'digits10({index}) is number of decimal digits of {index}':
            explanation='Проверяем определение числа десятичных цифр. Неравенства 10^(d−1)≤n<10^d дают коэффициент между 1 и 10, значит его корень стремится к единице.'
            evidence=dict(coefficient_lower=ONE,coefficient_upper=q(10))
        elif coef==('div',('rpow',q(-1),('floor',('sqrt',n))),n) and qualification in (None,'Pringsheim series'):
            radius=m.div(ONE,m.simplify(('abs',scale)));ends=[add(center,m.neg(radius)),add(center,radius)]
            return result('square_lattice_boundary_blocks',
                    dict(center=center,radius=radius,open_interval=ends,
                         endpoints=[dict(point=t,classification='conditional') for t in ends]),
                    'При модуле степенной координаты меньше единицы геометрическое сравнение даёт абсолютную сходимость. При модуле больше единицы члены не стремятся к нулю.',
                    'При координате +1 группируем индексы между соседними квадратами. Амплитуда группы равна 2/k+O(k⁻²), поэтому чередующиеся группы сходятся. Остаток незавершённой группы стремится к нулю.',
                    'При координате −1 внутри каждой группы знаки чередуются. Любая начальная часть группы ограничена её первым членом O(k⁻²). На обеих границах ряд модулей гармонический.',
                    first_index=start,reused_theorem='method.square_lattice_blocks',boundary_coordinates=[q(-1),ONE])
        else:
            if qualification not in (None,'start='+str(start)) or (not domain_conditions(coef) and m.constant_defined(coef,ctx)):
                raise Unsupported('No recognized bound for the entire coefficient sequence')
            return periodic_radius_and_endpoints(raw,index,start,coordinate,ctx)
    radius=m.div(ONE,m.simplify(('abs',scale)));ends=[add(center,m.neg(radius)),add(center,radius)]
    return result('power_coefficient_two_sided_bounds',
                  dict(center=center,radius=radius,open_interval=ends,
                       endpoints=[dict(point=t,classification='divergent') for t in ends]),
                  explanation,'В каждой граничной точке модуль члена не стремится к нулю.',
                  first_index=start,**evidence)


def two_tail_series_profile(task,index,raw,start):
    """Separate both integer tails, and inspect the finite junction in the raw formula."""
    from tasks import source
    n=('v',index);name=task['variable'];x=('s',name);output=task['requested_output']
    if task.get('end_index') not in ('+inf','+infinity') or start not in ('-inf','-infinity'):
        raise Unsupported('Both tails of the original integer lattice must be specified')
    ctx=index_context(index,[name],[])
    if (task['kind']=='generalized_series_convergence_set' and output==['complete_convergence_set','definedness_at_each_printed_index']
            and raw[0]=='div' and m.constant_defined(m.substitute(raw[2],{n:ZERO}),ctx)
            and m.simplify(m.substitute(raw[2],{n:ZERO}))==ZERO
            and task.get('original_qualifications')==f'{index} from -infinity to +infinity'):
        return result('bilateral_series_finite_junction_domain',series_domain_answer('empty',domain='empty',undefined_indices=[0]),
                      'Проверяем исходный нулевой индекс до исследования двух хвостов. Нулевой знаменатель исключает определённость всего ряда при любом значении параметра.',
                      zero_index_denominator=ZERO,first_index=start,last_index=task['end_index'])
    if (task['kind']!='laurent_series' or output!=['convergence_set','sum'] or raw[0]!='div'
            or raw[1] not in (('mul',n,('rpow',x,n)),('mul',('rpow',x,n),n)) or raw[2][0]!='rpow'
            or raw[2][2]!=('abs',n) or m.num(raw[2][1]) is None or m.num(raw[2][1])<=1):
        raise Unsupported('No supported pair of geometric moment tails')
    b=raw[2][1];t=m.div(x,b);u=m.div(ONE,m.mul(b,x))
    moment=lambda z:m.div(z,m.power(m.add(ONE,m.neg(z)),2))
    return result('bilateral_geometric_moment_tails',
                  series_domain_answer(source(m.div(ONE,b))+'<abs('+name+')<'+source(b),domain=name+'!=0',
                                       sum=m.add(moment(t),m.neg(moment(u)))),
                  'На исходной области x≠0 нулевой член равен нулю. Меняем знак индекса в отрицательном хвосте и получаем два ряда первых моментов геометрической последовательности.',
                  'Оба геометрических основания должны иметь модуль меньше единицы. На каждой границе один хвост не удовлетворяет необходимому признаку.',
                  'Сумму каждого хвоста получаем дифференцированием геометрического ряда внутри его круга сходимости.',
                  positive_coordinate=t,negative_coordinate=u,central_term=ZERO)


def convergence_grouping(task):
    fields={'kind','source','id','group','assumptions','requested_output'}
    info=task.get('source',{});group=task.get('group');requirements=task.get('requested_output')
    if set(task)-fields or set(info)-SOURCE_META-{'printed_instruction'}:
        raise Unsupported('The finite grouping leaves an unrecognized source requirement')
    if (requirements==['proof','converse_counterexample'] and group=='A_n=sum(a_i,i=p_n,...,p_(n+1)-1)'
            and task.get('assumptions')==['p_1=1','p_n strictly increasing integers','original order preserved']
            and info.get('printed_instruction') in (None,'Если Σ a_n сходится, доказать сходимость сгруппированного ряда к той же сумме. Привести пример неверности обратного.')):
        return result('partial_sums_at_group_ends',dict(grouped_sum_equals_original=True,
                           converse_counterexample=dict(terms=[ONE,q(-1)],block_size=2,grouped_sum=ZERO,
                                                        original_partial_sum_values=[ONE,ZERO])),
                      'Первые N групп покрывают без пропусков исходные индексы до p_(N+1)−1. Поэтому их частичные суммы образуют подпоследовательность исходных.',
                      'В переменном ряду 1,−1,1,−1,… сумма каждой пары ноль. Исходные частичные суммы принимают два различных значения и не сходятся.')
    if (requirements==['proof'] and group=='successive finite blocks in original order'
            and task.get('assumptions')==['a_n>0 for n>=1','sum of grouped terms converges']
            and info.get('printed_instruction') in (None,'Доказать, что при положительных членах сходимость ряда, полученного группировкой членов, влечёт сходимость исходного ряда.')):
        return result('partial_sums_at_group_ends',dict(original_sum_equals_grouped=True),
                      'Из положительности членов следует монотонность исходных частичных сумм. Каждая из них лежит между суммами на концах двух соседних групп.',
                      'Обе ограничивающие последовательности стремятся к сумме сгруппированного ряда. По сжатию исходные частичные суммы имеют тот же предел.')
    raise Unsupported('The source assumptions do not specify a recognized grouping implication')


def wave_index_weight(raw,index,ctx):
    n=('v',index)
    if raw[0] in ('sin','cos'):
        wave=raw;weight=ONE
    elif raw[0]=='div' and raw[1][0]=='mul':
        a,b=raw[1][1:]
        wave,amp=(a,b) if a[0] in ('sin','cos') else (b,a)
        weight=('div',amp,raw[2])
        if wave[0] not in ('sin','cos'):raise Unsupported('Need a sinusoidal sequence')
    else:raise Unsupported('Need a sinusoidal sequence')
    angle=m.simplify(m.substitute(wave[1],{n:ONE}))
    from tasks import domain_conditions, known_guard
    from verify import same_value
    if any(not known_guard(g,ctx) for g in domain_conditions(wave[1])) or not same_value(wave[1],m.mul(n,angle)):
        raise Unsupported('The original phase is not linear and defined at all indices')
    return wave[0],angle,weight


def oscillatory_series_domain(raw,index,start,names,conditions,ctx):
    from tasks import source
    n=('v',index);wave,angle,weight=wave_index_weight(raw,index,ctx)
    if angle[0]!='s' or angle[1] not in names:
        raise Unsupported('The phase is not a free real parameter')
    s=angle[1]
    if weight==ONE and names==[s] and not conditions:
        resonance=source(angle)+' in pi*Z'
        zero=wave=='sin'
        return result('neighboring_phase_lower_bound',
                      branches([(resonance,verdict(zero)),('not ('+resonance+')',verdict())]),
                      'Из формулы разности углов следует, что сумма модулей двух соседних значений гармоники не меньше |sin x|. При ненулевой правой части члены не стремятся к нулю.',
                      'При x∈πℤ синус тождественно равен нулю. Для косинуса в этой ветви модуль каждого члена равен единице.',
                      wave=wave,phase=angle,first_index=start)
    if weight[0]!='div':raise Unsupported('Need two powers to compare the wave envelope')
    amp,den=weight[1:]
    if (amp[0]!='rpow' or amp[1]!=n or den[0]!='add' or den[1]!=ONE or den[2][0]!='rpow'
            or den[2][1]!=n or amp[2][0]!='s' or den[2][2][0]!='s'):
        raise Unsupported('No positive weight with a known asymptotic ratio to a pure power')
    p,r=amp[2][1],den[2][2][1]
    if set(names)!={s,p,r} or len(names)!=3 or set(conditions)!={r+'>0','0<'+s+'<pi'}:
        raise Unsupported('The original nonresonance and subdominant constant must be supported by the source')
    return result('neighboring_phase_lower_bound',
                  series_domain_answer(p+'<'+r+'-1',r+'-1<='+p+'<'+r,conditions),
                  'Положительная амплитуда эквивалентна n^(p−q). При p<q её производная на хвосте отрицательна, что следует из знака p+(p−q)n^q.',
                  'Частичные суммы гармоники ограничены геометрической формулой, поскольку угол не кратен 2π. При убывании к нулю применяем признак Дирихле.',
                  'Два соседних модуля гармоники в сумме не меньше sin x>0, а их веса сравнимы. Это даёт необходимую степенную границу для абсолютной сходимости и исключает стремление общего члена к нулю при p≥q.',
                  phase=angle,weight_rate=add(amp[2],m.neg(den[2][2])),first_index=start)


def maximum_positive_bases(raw,index,start,names,conditions):
    from tasks import domain_conditions,source
    n=('v',index)
    if raw[0]!='rpow' or raw[2]!=('div',ONE,n) or conditions:
        raise Unsupported('Need a positive lattice root of a finite sum of powers')

    def atoms(e):
        if e[0]=='add':return [*atoms(e[1]),*atoms(e[2])]
        return [e]

    terms=atoms(raw[1]);bases=[]
    if len(terms)<2:raise Unsupported('No competing power rates')
    for e in terms:
        if (e[0]!='rpow' or e[1][0]!='abs' or not m.constant_defined(e[1],index_context(index,names,[]))
                or domain_conditions(e[1]) or e[2][0]!='pow' or e[2][1]!=n or e[2][2]<2):
            raise Unsupported('Each competing base must be independently defined and nonnegative')
        if e[2]!=terms[0][2]:raise Unsupported('Different exponent scales need a separate analysis')
        bases.append(e[1])
    bound='max('+','.join(map(source,bases))+')'
    return result('maximal_nonnegative_base_rate',series_domain_answer(bound+'<1'),
                  'Положим r равным максимальному из неотрицательных оснований. Сумма лежит между наибольшим слагаемым и этим слагаемым, умноженным на число членов.',
                  'После извлечения корня сравниваем с r в положительной степени индекса. При r<1 получаем геометрическую мажоранту. При r≥1 общий член не стремится к нулю.',
                  first_index=start,bases=bases,numerator_exponent=terms[0][2])


def functional_geometric_domain(raw,index,start,names,conditions,ctx):
    from integrals import affine
    from tasks import domain_conditions, known_guard, source
    from verify import same_value
    n=('v',index)
    if conditions:raise Unsupported('No extra functional restriction is covered by this geometric rule')
    if raw[0]=='div' and raw[1][0]=='rpow' and raw[1][2]==n:
        base=raw[1][1]
        if (not m.contains(base,n) and m.constant_defined(base,ctx)
                and same_value(raw[2],m.add(ONE,m.neg(raw[1])))
                and all(g[1]==n or known_guard(g,ctx) for g in domain_conditions(raw[2],positive_integer_exponents=(n,)))):
            b=source(base)
            return result('integer_geometric_denominator',series_domain_answer('abs('+b+')<1',domain='abs('+b+')!=1'),
                          'При модуле основания меньше единицы знаменатель отделён от нуля величиной 1−|основание|. Применяем геометрическую мажоранту.',
                          'При модуле больше единицы деление на исходную геометрическую степень даёт предел члена −1. Модуль, равный единице, даёт нулевой знаменатель на чётном индексе.',
                          first_index=start,geometric_base=base)
    if raw[0]=='rpow' and raw[2]==n:
        base=raw[1]
        if base[0]=='tan':
            a,b=affine(m.simplify(m.substitute(base[1],{n:('div',ONE,n)})),index)
            if (m.constant_defined(a,ctx) and m.constant_defined(b,ctx) and
                    all(g[1]==n or known_guard(g,ctx) for g in domain_conditions(base[1])) and
                    same_value(base[1],m.add(b,m.div(a,n)))):
                t=source(b);domain=f'for all integer {index}>={start}, cos({source(base[1])})!=0'
                return result('first_order_geometric_endpoint',series_domain_answer('abs(tan('+t+'))<1',domain=domain),
                              'На каждой допустимой непрерывной ветви корень модуля стремится к |tan исходного предельного угла|.',
                              'При модуле, равном единице, логарифм модуля имеет производную 2·sign(tan угла). Умножение приращения на индекс даёт конечный предел, а исходный модуль стремится к положительному числу.',
                              'В полюсе предельного тангенса модули корней неограниченны. Полюса исходных членов исключаем до применения любого признака.',
                              first_index=start,limiting_angle=b,reciprocal_shift=a,source_guard=('nonzero',('cos',base[1])))
        if m.contains(base,n) and all(g[1]==n or known_guard(g,ctx) for g in domain_conditions(base)):
            b,a=affine(m.simplify(m.substitute(base,{n:('div',ONE,n)})),index)
            if m.constant_defined(a,ctx) and m.constant_defined(b,ctx) and same_value(base,m.add(a,m.div(b,n))) and m.contains(base,n):
                return result('first_order_geometric_endpoint',series_domain_answer('abs('+source(a)+')<1'),
                              'Корень модуля равен |A+B/n| и стремится к |A|.',
                              'В граничных случаях A=±1 логарифм n ln|A+B/n| стремится к B/A. Член имеет положительный предельный модуль, поэтому ряд расходится.',
                              first_index=start,limiting_base=a,reciprocal_correction=b)
    raise Unsupported('The original geometric profile and its boundaries require another estimate')


def reciprocal_geometric_wave(raw,index,start,name):
    from tasks import source
    n=('v',index);x=('s',name)
    if (raw[0]!='div' or raw[2]!=('rpow',x,n) or raw[1][0]!='sin' or raw[1][1][0]!='div'):
        raise Unsupported('Need a decaying wave over a geometric coordinate')
    c,b=raw[1][1][1:];ctx=index_context(index,[],[])
    if (b[0]!='rpow' or b[2]!=n or m.num(b[1]) is None or m.num(b[1])<=1 or
            not m.constant_defined(c,ctx) or m.sign(c,ctx) not in (-1,1)):
        raise Unsupported('The scalar sine argument must have a nonzero decaying geometric coefficient')
    rate=m.div(ONE,b[1])
    return result('inverse_coordinate_geometric_equivalent',series_domain_answer('abs('+name+')>'+source(rate),domain=name+'!=0'),
                  'В исходном ряде x≠0. Аргумент синуса убывает геометрически, синус эквивалентен своему аргументу.',
                  'Проверяем коренной признак на обеих сторонах. При равенстве модулей исходный член имеет ненулевой предельный модуль.',
                  first_index=start,coefficient=c,inverse_base=rate)


def shifted_power_and_factorial_bounds(raw,index,start,names,conditions,ctx):
    from tasks import source,domain_conditions
    n=('v',index)
    if conditions:raise Unsupported('An additional parameter constraint needs its own power proof')
    if (raw[:2]==('div',('rpow',q(-1),n)) and raw[2][0]=='rpow'
            and raw[2][1][0]=='add' and n in raw[2][1][1:] and raw[2][2][0]=='s'):
        base=raw[2][1];p=raw[2][2];shift=base[2] if base[1]==n else base[1]
        if shift[0]!='s' or set(names)!={p[1],shift[1]} or len(names)!=2:
            raise Unsupported('The shifted power needs a free real shift and exponent')
        domain=f'for all integer {index}>={start}, ({source(base)})^({p[1]}) is real and nonzero'
        return result('shifted_alternating_power_tail',
                      series_domain_answer(p[1]+'>1','0<'+p[1]+'<=1',domain),
                      'При фиксированном сдвиге на хвосте основания положительны и их отношение к n стремится к единице. Определённость всей суммы требует проверки каждого раннего основания.',
                      'Модуль хвоста эквивалентен n^(−p). При p>0 он убывает, при p≤0 не стремится к нулю. Сравнение и признак Лейбница дают обе границы.',
                      first_index=start,original_power=raw[2])
    if raw[:2]!=('div',ONE) or raw[2][0]!='mul':
        raise Unsupported('Need a reciprocal product of a factorial root and a nonnegative correction')
    a,b=raw[2][1:]
    if a==('rpow',('factorial',n),('div',ONE,n)):root,g=a,b
    elif b==('rpow',('factorial',n),('div',ONE,n)):root,g=b,a
    else:raise Unsupported('The positive factorial root is missing')
    if g[0]!='add' or g[1]!=ONE or g[2][0]!='mul':
        raise Unsupported('Need one plus a nonnegative geometric term')
    A,X=g[2][1:]
    if A[0]!='rpow':A,X=X,A
    if (A[0]!='rpow' or A[2][0]!='mul' or A[2][2]!=n or m.num(A[2][1]) is None
            or m.num(A[2][1])<=0 or m.num(A[2][1])%2 or X[0]!='pow' or X[2]<2 or X[2]%2
            or not all(m.constant_defined(e,ctx) and not domain_conditions(e) for e in (A[1],X[1]))):
        raise Unsupported('The geometric term and its weight are not nonnegative on the original lattice')
    u,v=map(source,(A[1],X[1]))
    return result('factorial_root_with_geometric_gain',
                  series_domain_answer(f'abs({u})>1 and ({v})!=0'),
                  'По интегральной оценке логарифма факториала получаем n/e≤(n!)^(1/n)≤n.',
                  'Ветвь строго растущего геометрического основания и ненулевого веса даёт геометрическую мажоранту. В остальных ветвях второй знаменатель ограничен сверху и остаётся расходящаяся гармоническая миноранта.',
                  first_index=start,factorial_root=root,modulus_base=A[1],nonnegative_weight=X)


def functional_product_bound(term,index,start,names):
    from tasks import source
    n=('v',index)
    match=re.fullmatch(r'(.+)/product\((.+),(\w+),(\d+),'+re.escape(index)+r'\)',term.replace(' ',''))
    if not match:raise Unsupported('Need a full finite product in the original denominator')
    prefix,body,j,lo=match.groups();lo=int(lo)
    if j in [index,*names] or not 1<=lo<=start:raise Unsupported('The finite product binder is captured or its initial range is empty')
    ctx=index_context(index,names,[]);u=m.parse(prefix,index,names);f=m.parse(body,j,names)
    if (u[0]!='rpow' or u[2]!=n or not m.constant_defined(u[1],ctx)
            or f!=('add',ONE,('rpow',u[1],('v',j)))):
        raise Unsupported('The original product factors need the same fixed geometric base')
    t=source(u[1])
    return result('geometric_factors_product_lower_bound',
                  series_domain_answer(f'({t})!=-1',domain=f'({t})!=-1'),
                  'При модуле основания меньше единицы логарифмы положительных множителей мажорируются геометрическим рядом на хвосте. Конечный префикс положителен, поэтому произведение отделено от нуля.',
                  'При модуле больше единицы выносим из каждого множителя его геометрическую степень. Оставшееся произведение с обратным основанием снова отделено от нуля. Сумма вынесенных показателей растёт квадратично.',
                  'Основание +1 даёт знаменатель 2 в каждом множителе. Основание −1 даёт нулевой множитель на нечётном индексе и исключается в исходной задаче.',
                  first_index=start,product_first=lo,bound_index=j,geometric_base=u[1])


def fixed_factors_times_varying_limit(raw,index,start,names,conditions):
    from tasks import source
    n=('v',index);ctx=index_context(index,names,conditions)
    if len(names)!=1 or conditions!=[names[0]+'>0']:
        raise Unsupported('The reciprocal exponent base must be proved positive')
    x=('s',names[0]);target=('rpow',x,('div',ONE,n))

    def factors(expr):
        if expr[0]=='mul':return [*factors(expr[1]),*factors(expr[2])]
        return [expr]

    a=factors(raw);varying=[e for e in a if m.contains(e,n)]
    if len(a)<2 or len(varying)!=1 or varying[0][0]!='add':
        raise Unsupported('Need one varying factor and the original finite product of constants')
    A,B=varying[0][1:]
    if (not m.constant_defined(A,ctx) or B[0]!='mul' or B[2]!=target or
            not m.constant_defined(B[1],ctx) or m.sign(m.add(A,B[1]),ctx) not in (-1,1)):
        raise Unsupported('A nonzero limit of the varying factor is not yet proved')
    fixed=[e for e in a if e!=varying[0]]
    if not all(m.constant_defined(e,ctx) for e in fixed):
        raise Unsupported('A constant-factor source hole remains')
    constant=ONE
    for e in fixed:constant=m.mul(constant,e)
    return result('fixed_zero_factors_before_term_test',
                  series_domain_answer('('+source(constant)+')=0',domain=conditions),
                  'Степень фиксированного положительного основания с показателем 1/n стремится к единице. У переменного множителя предел конечен и отличен от нуля.',
                  'Если любой из исходных постоянных множителей равен нулю, весь ряд нулевой. В остальных точках общий член имеет ненулевой предел.',
                  first_index=start,fixed_factors=fixed,varying_factor=varying[0])


def rational_index_parts(e,n,ctx):
    p,d=m.rational_form(e)
    return tuple(polynomial_coefficients(m.poly_expr(a),n,ctx) for a in (p,d))


def rational_log_profile(raw,index,start,ctx,outputs,functional=False):
    """Collect log-magnitudes on a positive tail while checking every original power."""
    from tasks import domain_conditions,source
    n=('v',index);powers=[];exponents=[]
    if not any(e[0]=='rpow' for e in series_factors(raw)):
        raise Unsupported('Need coupled variable powers for a logarithmic growth comparison')

    def collect(e,s=1):
        if e[0] in ('mul','div'):
            collect(e[1],s);collect(e[2],s if e[0]=='mul' else -s);return
        if e==ONE:return
        base,exponent=(e[1],e[2]) if e[0]=='rpow' else (e[1],q(e[2])) if e[0]=='pow' else (e,ONE)
        ep,ed=rational_index_parts(exponent,n,ctx)
        if len(ed)!=1 or not ep:raise Unsupported('The exponent is not an exact Laurent polynomial in the original index')
        j,den=next(iter(ed.items()))
        powers.append((base,{i-j:mul(q(s),m.div(v,den)) for i,v in ep.items()}))
        if e[0]=='rpow' and j==0 and den==ONE and all(
                m.num(v) is not None and m.num(v).denominator==1 for v in ep.values()):
            if guard_on_ray(('positive',exponent),index,start,ctx):exponents.append(exponent)

    collect(raw)
    if not powers:raise Unsupported('No nontrivial power factor')
    if any(not guard_on_ray(g,index,start,ctx) for g in domain_conditions(raw,positive_integer_exponents=exponents)):
        raise Unsupported('An original variable-power domain is not established at all indices')
    rates={}

    def put(order,logarithmic,coefficient):
        if order>=0:
            k=(order,logarithmic);rates[k]=add(rates.get(k,ZERO),coefficient)

    profiles=[]
    for base,ep in powers:
        if max(ep)>2:raise Unsupported('The available logarithmic expansion bounds the exponent through degree two')
        p,d=rational_index_parts(base,n,ctx)
        if not p or not d:raise Unsupported('An identically zero power base needs separate proof')

        def side(poly):
            k=max(poly);a=poly[k]
            if m.sign(a,ctx)!=1:raise Unsupported('A positive eventual polynomial leader is required')
            b=m.simplify(m.div(poly.get(k-1,ZERO),a))
            c=add(m.div(poly.get(k-2,ZERO),a),m.neg(m.mul(q(1,2),m.power(b,2))))
            return k,('ln',a),b,c

        pp,dp=side(p),side(d);jet=[add(a,m.neg(b)) for a,b in zip(pp[1:],dp[1:])];degree=pp[0]-dp[0]
        for j,v in ep.items():
            put(j,True,mul(v,q(degree)))
            for k,c in enumerate(jet):put(j-k,False,mul(v,c))
        profiles.append(dict(base=base,exponent=ep,log_index_coefficient=degree,inverse_index_coefficients=jet))
    for (order,logarithmic),co in sorted(rates.items(),reverse=True):
        if order<=0 or co==ZERO:continue
        s=m.sign(co,ctx)
        if s not in (-1,1) or 'asymptotic_order' in outputs:
            raise Unsupported('The dominant exponential change needs an additional parameter branch')
        answer=verdict(s<0)
        break
    else:
        d=rates.get((0,True),ZERO)
        answer=series_domain_answer(source(d)+'<-1') if functional else logarithmic_classification([d],ctx)
        if 'asymptotic_order' in outputs:
            answer['asymptotic_order']=dict(index_power=m.neg(d),equivalent_coefficient=('exp',rates.get((0,False),ZERO)))
    if functional and 'absolute_convergence_set' not in answer:
        answer=series_domain_answer('all parameters' if answer['absolute_convergence'] else 'empty')
    return result('logarithm_of_index_power_products',answer,
                  'Проверяем определённость каждого исходного основания и показателя. На хвосте рациональные основания положительны по знакам старших коэффициентов.',
                  'Логарифм каждого основания записываем как степень ln n, фиксированную часть и два порядковых члена при 1/n. Умножаем на исходный показатель и складываем с нужными знаками.',
                  'Первый ненулевой положительный порядок индекса в логарифме даёт сравнение с любой фиксированной степенью. Если эти порядки сократились, сравниваем оставшуюся степень с порогом −1.',
                  factors=profiles,logarithmic_scales=[dict(power=k[0],logarithmic=k[1],coefficient=c) for k,c in sorted(rates.items(),reverse=True)],
                  first_index=start)


def series_factors(e):
    if e[0] in ('mul','div'):
        for child in e[1:]:yield from series_factors(child)
    else:yield e


def boundary_variable_powers(raw,index,start,ctx):
    """At root one, evaluate small logarithmic corrections and retain the first-index check."""
    from tasks import domain_conditions, known_guard
    n=('v',index);factors=list(series_factors(raw))
    if raw[0]=='div' and raw[1]==ONE and raw[2][0]=='rpow':
        base,exponent=raw[2][1:]
        if base==('ln',n) and exponent==('div',ONE,n):
            answer=verdict()
            if start==1:answer=dict(classification='undefined',undefined_indices=[1],tail_classification=answer)
            return result('small_exponent_logarithmic_boundary',answer,
                          'Проверяем ln n в исходном знаменателе. Он обнуляется при n=1, строго положителен при каждом n≥2.',
                          'Логарифм модуля члена на хвосте равен −ln ln n/n и стремится к нулю. Член стремится к единице.',
                          first_index=start,verified_tail=max(2,start))
    if raw[0]=='rpow' and raw[1][0]=='cos' and raw[2]==('pow',n,3):
        phase=raw[1][1]
        if (phase[0]=='div' and phase[2]==n and m.constant_defined(phase[1],ctx)
                and all(e==n or known_guard((g,e),ctx) for g,e in domain_conditions(phase))):
            a=phase[1]
            from tasks import source
            text=source(a);s=m.sign(a,ctx)
            answer=verdict(s in (-1,1)) if s is not None else branches([(text+'=0',verdict()),(text+'!=0',verdict(True))])
            return result('cosine_exponential_root_bound',answer,
                          'Исходная степень n³ целая и положительная. На хвосте косинус положителен, независимо от знаков ранних оснований.',
                          'При ненулевом коэффициенте корень степени n стремится к exp(−a²/2)<1 по разложению ln cos. Нулевой коэффициент даёт тождественно единичные члены.',
                          phase_coefficient=a,root_limit=('exp',m.mul(q(-1,2),m.power(a,2))),first_index=start)
    if raw[0]=='div' and all(a[0]=='rpow' and a[2]==n and m.constant_defined(a[1],ctx) and m.sign(a[1],ctx)==1
                             for a in factors if a[0]=='rpow') and raw[2][0]=='add':
        bases=raw[2][1:]
        if all(e[0]=='rpow' and e[2]==n and m.num(e[1]) is not None and m.num(e[1])>0 for e in bases):
            from tasks import domain_conditions
            c,rates,_=logarithmic_monomial(raw[1],n,ctx)
            if domain_conditions(raw[1]) or m.sign(c,ctx) not in (-1,1):
                raise Unsupported('The numerator weight has an original guard or vanishes')
            b=max(m.num(e[1]) for e in bases)
            if b==1:raise Unsupported('A unit geometric denominator requires a separate boundary weight')
            return result('positive_geometric_denominator_rate',verdict(b>1),
                          'Знаменатель положителен и сравним с наибольшей из положительных геометрических степеней. Корни фиксированного индексного веса стремятся к единице.',
                          'Коренной признак сравнивает обратное наибольшее основание с единицей.',
                          geometric_base=q(b),weight_rates=rates,first_index=start)
    raise Unsupported('A different first nonzero logarithmic correction is needed')


def original_series_profiles(task,library):
    """Admit only complete convergence questions and dispatch plausible profile proofs."""
    from polynomial import NotRational, Undefined
    if not library.data.get('series_original_domain_profiles'):
        raise Unsupported('No original-domain series profiles in this library')
    kind=task['kind'];given=task.get('source',{})
    if kind=='series_grouping_proof':return convergence_grouping(task)
    if not isinstance(given,dict) or set(given)-SOURCE_META:
        raise Unsupported('An original series qualification remains')
    index=task.get('index');start=task.get('start_index');term=task.get('term');outputs=task.get('requested_output')
    if not isinstance(index,str) or not index.isidentifier() or not isinstance(term,str):
        raise Unsupported('Need the bound index and complete source term')
    domain_fields={'kind','id','source','term','index','start_index','end_index','variable','variables',
                   'requested_output','stated_conditions','original_qualifications','transcription_note'}
    if kind in ('laurent_series','generalized_series_convergence_set') and start in ('-inf','-infinity'):
        if set(task)-domain_fields or task.get('stated_conditions') or not isinstance(task.get('variable'),str):
            raise Unsupported('An extra bilateral series requirement remains')
        convergence_heading(task,'Найти область сходимости и сумму двустороннего ряда Лорана.',
                            'Найти область сходимости обобщённого степенного ряда.')
        return two_tail_series_profile(task,index,m.parse(term,index,[task['variable']]),start)
    if type(start) is not int or start<1:
        raise Unsupported('Need a positive initial index for this scale')
    if task.get('end_index','+infinity') not in ('+inf','+infinity'):
        raise Unsupported('The original series must have an infinite upper range')
    if kind=='power_series_convergence_set':
        if (set(task)-domain_fields or task.get('stated_conditions') or not isinstance(task.get('variable'),str)
                or outputs!=['radius','open_interval','both_endpoint_classifications']):
            raise Unsupported('Need the entire original real power-series question')
        convergence_heading(task,'Определить радиус, интервал сходимости и исследовать обе граничные точки.')
        return nonperiodic_power_profile(term,index,start,task['variable'],task.get('original_qualifications'))
    if kind=='generalized_series_convergence_set':
        if (set(task)-domain_fields or task.get('stated_conditions') or task.get('original_qualifications')
                or outputs!=['complete_convergence_set'] or not isinstance(task.get('variable'),str)):
            raise Unsupported('Need the original generalized convergence set')
        convergence_heading(task,'Найти область сходимости обобщённого степенного ряда.')
        return reciprocal_geometric_wave(m.parse(term,index,[task['variable']]),index,start,task['variable'])
    if kind=='functional_series_convergence_set':
        names=task.get('variables');conditions=task.get('stated_conditions',[])
        if (set(task)-domain_fields or task.get('original_qualifications')
                or not isinstance(names,list) or index in names or outputs not in (
                ['absolute_convergence_set','conditional_convergence_set','proof'],
                ['absolute_convergence_set','conditional_convergence_set','proof','definedness_at_each_printed_index'])):
            raise Unsupported('Need both original convergence sets and their source conditions')
        convergence_heading(task,'Определить области абсолютной и условной сходимости исходного функционального ряда.')
        if 'product(' in term:
            if conditions:raise Unsupported('The extra restriction has no finite-product closure')
            return functional_product_bound(term,index,start,names)
        ctx=index_context(index,names,[]);raw=m.parse(term,index,names,('factorial',))
        for attempt in (lambda:oscillatory_series_domain(raw,index,start,names,conditions,ctx),
                        lambda:maximum_positive_bases(raw,index,start,names,conditions),
                        lambda:functional_geometric_domain(raw,index,start,names,conditions,ctx),
                        lambda:shifted_power_and_factorial_bounds(raw,index,start,names,conditions,ctx),
                        lambda:fixed_factors_times_varying_limit(raw,index,start,names,conditions),
                        lambda:rational_log_profile(raw,index,start,index_context(index,names,conditions),outputs,True)):
            try:return attempt()
            except (Unsupported,NotRational,Undefined):pass
        raise Unsupported('No exact geometric or oscillatory estimate yet')
    if kind=='series_convergence' and set(task)<=ORDINARY_FIELDS and task.get('method_requirement') in GENERAL:
        names=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
        if not outputs or set(outputs)-OUTPUTS or task.get('index_domain','integers')!='integers':
            raise Unsupported('An additional original convergence output is not covered by the profile tests')
        permitted_hint='Исследовать сходимость ряда. Указание. Показать, что при x≠kπ (k — целое) невозможно, чтобы sin(nx)→0 при n→∞.'
        hinted=given.get('printed_instruction')==permitted_hint
        comparison_heading='Пользуясь признаком сравнения, Даламбера или Коши, исследовать сходимость рядов'
        comparison=(task.get('method_requirement')=='comparison_or_ratio_or_root' and given.get('printed_instruction')==comparison_heading)
        checked={**task,'source':{**given,'printed_instruction':'Исследовать сходимость ряда.'}} if hinted or comparison else task
        if any(given.get(k) not in (None,task.get('method_requirement')) for k in
               ('method_requirement','explicit_required_method','explicit_imposed_method')):
            raise Unsupported('The original required method differs from the admitted comparison')
        validate_source(checked,outputs,task.get('method_requirement'))
        ctx=index_context(index,names,conditions)
        raw=m.parse(term,index,names)
        if hinted:
            if raw!=('sin',('mul',('v',index),('s','x'))) or names!=['x'] or conditions or 'asymptotic_order' in outputs:
                raise Unsupported('The optional original hint concerns a different phase')
            return oscillatory_series_domain(raw,index,start,names,conditions,ctx)
        if 'asymptotic_order' not in outputs:
            for attempt in (lambda:oscillatory_series_domain(raw,index,start,names,conditions,ctx),
                            lambda:boundary_variable_powers(raw,index,start,ctx)):
                try:return attempt()
                except (Unsupported,NotRational,Undefined):pass
        return rational_log_profile(raw,index,start,ctx,outputs)
    raise Unsupported('No original-domain profile for this kind of series')


def geometric_monomials(raw,index):
    """Factor finite sums into weights c*r^n*n^d, preserving integer powers and source poles."""
    from integrals import affine
    from tasks import domain_conditions,known_guard
    n=('v',index);ctx=index_context(index,[],[])
    if raw==n:return {(Fraction(1),1):Fraction(1)}
    op=raw[0]
    if op in ('add','mul','div'):
        a,b=(geometric_monomials(e,index) for e in raw[1:]);out=defaultdict(Fraction)
        if op=='add':
            for f in (a,b):
                for k,c in f.items():out[k]+=c
        elif op=='mul':
            for (u,i),c in a.items():
                for (v,j),d in b.items():out[(u*v,i+j)]+=c*d
        else:
            if len(b)!=1:raise Unsupported('A denominator is not one nonzero positive-index monomial')
            ((v,j),d),=b.items()
            if not d or not v:raise Unsupported('A zero formal denominator is present')
            for (u,i),c in a.items():out[(u/v,i-j)]+=c/d
        return {k:v for k,v in out.items() if v}
    if op=='pow' and raw[1]==n:return {(Fraction(1),raw[2]):Fraction(1)}
    if op=='rpow' and all(known_guard(g,ctx) for g in domain_conditions(raw[1])) and not domain_conditions(raw[2]):
        a=m.num(m.simplify(raw[1]));s,t=map(m.num,affine(raw[2],index))
        if a and s is not None and t is not None and s.denominator==t.denominator==1 and max(abs(s),abs(t))<=64:
            return {(a**int(s),0):a**int(t)}
    if m.constant_defined(raw,ctx) and (a:=m.num(m.simplify(raw))) is not None:
        return {(Fraction(1),0):a} if a else {}
    raise Unsupported('No source geometric-monomial decomposition')


def ordinary_transport_goal(task,lib):
    from polynomial import rf
    from tasks import source
    if not lib.data.get('coefficient_and_limit_transport'):raise Unsupported('The coefficient transport rules are absent')
    k=task['kind'];meta=task.get('source',{});source_text=task.get('statement')
    if k=='series_convergence' and isinstance((text:=task.get('term')),str) and text.startswith('lambda('):
        n=task.get('index','');hit=re.fullmatch(r'lambda\('+re.escape(n)+r'\)\^\(-([\d]+(?:/[1-9]\d*)?)\)',text) if isinstance(n,str) else None
        if (set(task)-ORDINARY_FIELDS or not hit or task.get('start_index')!=1 or task.get('parameters')!=[]
                or task.get('index_domain')!='integers' or task.get('method_requirement')!='general_convergence_tests'
                or task.get('stated_conditions')!=[f'lambda({n}) is the nth positive root of tan(x)=x']
                or task.get('requested_output')!=['convergence_classification','justification']):
            raise Unsupported('The ordered root lattice must follow from the original problem')
        validate_source(task,task['requested_output'],task['method_requirement'])
        p=Fraction(hit[1])
        if p<=0:raise Unsupported('Need a positive reciprocal power')
        return result('root_lattice_bounds_for_numeric_series',verdict(p>1),
                      'На (nπ,nπ+π/2) функция tan x−x строго возрастает, слева отрицательна, справа неограниченна. Это ровно один положительный корень на каждой такой ветви.',
                      'На отрицательных ветвях тангенса положительный корень невозможен. На первой ветви от нуля разность строго растёт из нуля, поэтому новых положительных корней там нет.',
                      'Полученные линейные верхняя и нижняя оценки корня дают сравнение ряда модулей со степенным рядом.',
                      root_interval=['n*pi','(n+1/2)*pi'],decay_power=q(p))
    if (k not in ('series_theorem','series_proposition','sum_of_series') or set(task)-{'kind','id','source','statement','requested_output'} or
            not isinstance(source_text,str) or not isinstance(meta,dict) or set(meta)-SOURCE_META or any(
                meta.get(field) not in (None,source_text) for field in ('literal_requirement','printed_instruction','printed_requirement','printed_group_heading'))
            or any(meta.get(field) for field in ('method_requirement','explicit_required_method','explicit_imposed_method'))):
        raise Unsupported('Need a whole original ordinary-series statement')
    h=re.fullmatch(r'Доказать признак Лобачевского: если a_n положительны и монотонно стремятся к нулю, Σa_n сходится одновременно с Σ_\{m=0\}\^∞ p_m (\d+)\^\(−m\), где p_m — наибольший номер с a_n≥\1\^\(−m\) \(n=1,\.\.\.,p_m\)\.',source_text)
    if k=='series_theorem' and h and task.get('requested_output')==['proof']:
        b=int(h[1])
        if b<=1:raise Unsupported('Threshold levels must decrease geometrically')
        return result('counting_positive_terms_by_geometric_levels',dict(equivalent_convergence=True),
                     'Монотонность и предел ноль означают, что p_m считает ровно все члены выше очередного порога. Разложить это число в сумму индикаторов.',
                     'Переставить неотрицательное двойное суммирование. Для каждого члена сумма порогов, лежащих под ним, является геометрическим хвостом.',
                     'После конечного префикса этот хвост заключён между двумя положительными кратными исходного члена. Сравнение доказывает равносильность.',
                     threshold_base=q(b),lower_multiplier=q(1,b-1),upper_multiplier=q(b,b-1))
    h=re.fullmatch(r'Достаточны ли b_n>0 и b_n→0 для сходимости sum\(\(-1\)\^n\*b_n\)\? Исследовать пример sum\((.+)\)\.',source_text)
    if k=='series_proposition' and h and not task.get('requested_output'):
        layers=geometric_monomials(m.parse(h[1],'n'),'n')
        c=layers.get((Fraction(-1),-1),0);d=layers.get((Fraction(1),-1),0)
        if len(layers)!=2 or not c>abs(d)>0:raise Unsupported('The positive amplitude and noncancelled harmonic drift must both be verified')
        return result('nonalternating_component_after_parity_multiplication',
                     dict(sufficient_conditions=False,example_diverges=True,divergence_direction='+inf' if d>0 else '-inf'),
                     'Умножение на знак чётности переставляет две геометрические составляющие. Обратный перенос подтверждает положительную исходную амплитуду и её предел ноль.',
                     'У исходного примера одна гармоническая часть строго чередуется, а вторая имеет постоянный ненулевой знак. Первая сходится, вторая расходится.',
                     alternating_weight=q(c),nonalternating_weight=q(d))
    if k=='sum_of_series' and not task.get('requested_output'):
        h=re.fullmatch(r'Найти сумму двух рядов sum\((.+),(\w+)=1\.\.inf\)\+sum\((.+),\2=1\.\.inf\)\.',source_text)
        if not h:raise Unsupported('Need two series with the same original first and running indices')
        a,j,b=h.groups();coeff=defaultdict(Fraction)
        for body in (a,b):
            layers=geometric_monomials(m.parse(body,j),j)
            if any(abs(r)>1 or abs(r)==1 and d>=-1 for r,d in layers):
                raise Unsupported('Absolute convergence is not verified for both original sums')
            for t,w in layers.items():coeff[t]+=w
        if any(c and (abs(r)>=1 or d) for (r,d),c in coeff.items()):
            raise Unsupported('After cancellation additional nongeometric terms remain')
        total=sum(c*r/(1-r) for (r,_),c in coeff.items() if c)
        return result('aligned_cancellation_before_geometric_summation',dict(sum=q(total)),
                     'Сначала подтвердить сходимость обеих исходных сумм. После совмещения индексов одинаковые весовые составляющие с противоположными знаками сокращаются.',
                     'Оставшиеся геометрические составляющие суммируются от исходного первого индекса.',
                     remaining_geometric_terms=[(q(r),q(c)) for (r,_),c in coeff.items() if c])
    if k=='series_proposition' and not task.get('requested_output'):
        h=re.fullmatch(r'Проверить абсолютную сходимость произведения Коши расходящихся рядов 1([+−])sum\((.+),(\w+)=1\.\.inf\) и 1([+−])sum\((.+),\3=1\.\.inf\)\.',source_text)
        if not h:raise Unsupported('Need the two original geometric streams of the formal Cauchy product')
        s,a,n,t,b=h.groups();name='cauchyCoordinate'
        if name==n:name+='_'
        z=('v',name);factors=[]
        for sign,body in ((s,a),(t,b)):
            layers=geometric_monomials(m.parse(body,n),n)
            modes=sorted((abs(r),r,c) for (r,d),c in layers.items() if d==0)
            if len(modes)!=len(layers) or not modes or modes[-1][0]<=1 or len(modes)>1 and modes[-2][0]==modes[-1][0]:
                raise Unsupported('The stated divergence of a source factor is not verified')
            f=ONE
            for _,r,c in modes:
                zr=m.mul(q(r),z);f=m.add(f,m.mul(q(c if sign=='+' else -c),m.div(zr,m.add(ONE,m.neg(zr)))))
            factors.append(f)
        padded=m.mul(*factors);p,d=rf(padded,name)
        if len(p)!=1 or len(d)!=2 or not d[0]:raise Unsupported('The combined germ does not reduce to one geometric denominator')
        r=-d[1]/d[0];c=p[0]/d[0]
        return result('cauchy_product_after_formal_pole_cancellation',dict(**verdict(abs(r)<1),product_sum=q(c/(1-r)) if abs(r)<1 else None),
                     'Ввести степенную координату. В достаточно малом круге обе исходные производящие функции сходятся, хотя при единице их члены не стремятся к нулю.',
                     'Перемножить рациональные функции в окрестности нуля. Тождество коэффициентов определяет исходное произведение Коши.',
                     'После сокращения полюсов коэффициенты образуют одну геометрическую последовательность. Проверить её абсолютную сходимость при исходной единице.',
                     generating_factors=factors,product_ratio=q(r),formal_product=source(padded))
    raise Unsupported('No ordinary-series transport binds the whole statement')


def series_scale_heading(task):
    outputs=task.get('requested_output');method=task.get('method_requirement');origin=task.get('source',{})
    if outputs not in (['convergence_classification','justification'],['convergence_classification','justification','asymptotic_order']):
        raise Unsupported('The requested asymptotic or convergence conclusion must be bound')
    comparison='Пользуясь признаком сравнения, Даламбера или Коши, исследовать сходимость рядов'
    if method=='comparison_or_ratio_or_root' and origin.get('printed_instruction')==comparison:
        origin=dict(origin,printed_instruction='Исследовать сходимость ряда.')
    hint=origin.get('printed_hint')
    if hint=='Использовать формулу √2 = 2 cos(π/4).' and 'sequence_definitions' in task:
        origin={k:v for k,v in origin.items() if k!='printed_hint'}
    validate_source(dict(task,source=origin),outputs,method)


def radical_recurrence_series(task,index,start,ctx):
    from verify import same_value
    defs=task['sequence_definitions'];word=r'([A-Za-z_]\w*)';I=re.escape(index)
    rec=re.fullmatch(word+r'\(1\)=(.+); '+word+r'\(1\)=(.+); \3\('+I+r'\+1\)=sqrt\(2\+\3\('+I+r'\)\); \1\('+I+r'\+1\)=sqrt\(2-\3\('+I+r'\)\)',defs)
    if not rec or len({index,rec[1],rec[3]})!=3 or start!=1 or task['term']!=f'{rec[1]}({index})':
        raise Unsupported('The radical seeds and two original recurrences must be bound')
    a,c=m.parse(rec[2],None),m.parse(rec[4],None)
    if not all(m.constant_defined(e,ctx) for e in (a,c)) or constant_sign(a,ctx)!=1 or constant_sign(c,ctx)!=1 or not same_value(m.add(m.power(a,2),m.power(c,2)),q(4)):
        raise Unsupported('The two positive seeds do not determine one first-quadrant angle')
    if task.get('source',{}).get('printed_hint') and not same_value(c,('sqrt',q(2))):
        raise Unsupported('The optional cosine identity must match the original radical seed')
    angle=('acos',m.div(c,q(2)))
    return result('half_angle_majorant_for_nested_radical_series',verdict(True),
                 'Построить угол по положительным начальным значениям. Предпосылка о сумме квадратов даёт согласованные синус и косинус одного угла.',
                 'Две формулы половинного угла подтверждают обе рекурсии с положительными корнями. Углы уменьшаются вдвое, а синус не превосходит аргумент.',
                 'Полученная геометрическая мажоранта доказывает абсолютную сходимость на исходных индексах.',
                 angle=angle,verified_initial_pair=[a,c],majorant='2*theta/2^(n-1)')


def formal_monic_degree_ratio(task,index,text):
    H=task.get('stated_conditions');N=re.escape(index)
    rg=re.fullmatch(r'\((.+)\)/\((.+)\)',text)
    if not rg:raise Unsupported('Need both monic polynomials as given')

    def degree(body):
        form=re.fullmatch(N+r'\^([A-Za-z_]\w*)\+([A-Za-z_])1\*'+N+r'\^\(\1-1\)\+\.\.\.\+\2\1',body)
        if not form:raise Unsupported('The symbolic polynomial degree is not bound')
        return form[1]

    p,r=map(degree,rg.groups())
    if len({p,r,index})!=3 or task.get('parameters')!=[p,r] or H!=[
            'denominator > 0 at every initial integer index',f'monic polynomials of degrees {p} and {r}']:
        raise Unsupported('The denominator sign and both degree hypotheses are required')
    return result('leading_degrees_of_symbolic_monic_ratio',dict(
                  **branches([(f'{r}>{p}+1',verdict(True)),(f'{r}<={p}+1',verdict())]),
                  asymptotic_order=dict(index_power=('add',('s',r),('mul',q(-1),('s',p))),equivalent_coefficient=ONE)),
                  'Вынести старшие степени обоих многочленов. Их остаточные скобки стремятся к единице по моничности.',
                  'По исходной положительности знаменатель не обнуляется у начальных индексов. Положительный хвост сравнить со степенным рядом и учесть равенство граничного показателя.',
                  numerator_degree=p,denominator_degree=r)


def shifted_log_product_series(task,index,start):
    text=task['term'];N=re.escape(index)
    hit=re.fullmatch(r'prod\(ln\((\w+)\)/ln\(\1\+(\w+)\),\1=(\d+)\.\.'+N+r'(?:\+(\d+))?\)',text)
    if (not hit or int(hit[3])<2 or start+int(hit[4] or 0)<int(hit[3]) or len({hit[1],hit[2],index})!=3 or
            task.get('parameters')!=[hit[2]] or task.get('stated_conditions')!=[hit[2]+'>0']):
        raise Unsupported('The shifted log product must use positive logs on the whole source lattice')
    return result('logarithmic_minorant_for_shifted_factor_products',verdict(),
                  'Логарифм обратного множителя есть приращение ln ln t. По убыванию производной оно не превосходит длину сдвига, делённую на k ln k.',
                  'Суммирование и интегральная оценка дают верхнюю границу p ln ln n плюс константа для логарифма обратного произведения.',
                  'Исходный член ограничен снизу положительной кратной 1/(ln n)^p. Этот ряд расходится, поскольку любая фиксированная степень логарифма растёт медленнее n.',
                  bound_index=hit[1],first_factor=int(hit[3]),factor_shift=hit[2])


def growing_factorial_product_ratio(task,index,start):
    from integrals import affine
    from tasks import domain_conditions
    N=re.escape(index);hit=re.fullmatch(r'factorial\((.+)\)\^'+N+r'/product\(factorial\((.+)\),(\w+),(\d+),'+N+r'\)',task['term'])
    if not hit or start<1 or hit[3]==index or not 1<=int(hit[4])<=start:raise Unsupported('Need exact consecutive factorial product')
    binder=hit[3];x=m.parse(hit[1],index);y=m.parse(hit[2],binder)
    a,b=map(m.num,affine(x,index));d,e=map(m.num,affine(y,binder))
    if (domain_conditions(x) or domain_conditions(y) or a!=1 or d!=2 or e!=0 or b is None or b<0 or b.denominator!=1 or
            task.get('parameters') or task.get('stated_conditions')):
        raise Unsupported('The factorial arguments must be valid integer shifts on every source index')
    return result('factorial_ratio_with_positive_density_of_small_factors',verdict(True),
                  'Составить отношение соседних членов. В знаменателе появляется ровно один новый факториал, а у числителя увеличиваются аргумент и показатель.',
                  'Сократить общие факториалы. Остаётся многочленный множитель и произведение отношений с числителем n+a+1 и возрастающими знаменателями до 2n+2.',
                  'Для достаточно больших n все отношения не больше единицы, а не менее линейного числа отношений отделены от единицы. Их произведение подавляет многочленный множитель. Отношение членов стремится к нулю.',
                  numerator_shift=q(b),first_product_index=int(hit[4]),factorial_stride=2)


def logarithmic_germ_and_phase_scales(raw,index,start,ctx,conditions,outputs):
    from tasks import domain_conditions
    from polynomial import pdiv,rf
    n=('v',index)
    if (raw[0]=='div' and raw[1][0]=='ln' and raw[1][1][0]=='add' and raw[1][1][1]==ONE and
            raw[2][0]=='ln' and raw[2][1][0]=='rpow' and raw[2][1][2]==n):
        b=raw[2][1][1];u=raw[1][1][2]
        if (b[0]=='s' and u[0]=='div' and u[2]==n and u[1][0]=='rpow' and u[1][2]==('div',ONE,n) and
                u[1][1][0]=='s' and set(conditions)=={u[1][1][1]+'>0',b[1]+'>0'} and len(ctx['parameters'])==2):
            good=dict(**verdict(True),asymptotic_order=dict(index_power=q(2),equivalent_coefficient=m.div(ONE,('ln',b))))
            return result('normalize_fixed_base_logarithmic_series',
                         branches([(b[1]+'!=1',good),(b[1]+'=1',dict(classification='undefined'))]),
                         'Отдельно проверить ненулевость ln b. Для положительного b≠1 знаменатель равен n ln b и не обращается в ноль.',
                         'Числитель эквивалентен 1/n, поскольку степень фиксированного положительного основания с показателем 1/n стремится к единице. Полученный точный эквивалент суммируем.',
                         first_index=start,original_log_base=b)
    if 'asymptotic_order' in outputs:raise Unsupported('A precise source equivalent is not established')
    if (raw[:2]==('div',ONE) and raw[2][0]=='pow' and raw[2][2]>0 and raw[2][2]%2==0 and
            raw[2][1][0]=='ln' and raw[2][1][1][0]=='sin'):
        t=raw[2][1][1][1]
        if t[0]=='div' and rpow_index_degree(t[2],n)>0 and (c:=m.num(t[1])) is not None and 0<c<=1 and not conditions:
            return result('reciprocal_logarithm_of_small_sine',verdict(),
                          'Исходный синус строго положителен и меньше единицы на всей решётке, поэтому логарифм определён и ненулевой.',
                          'Малый синус эквивалентен аргументу, логарифм имеет главный порядок −r ln n. Любая положительная обратная логарифмическая степень даёт расходящийся ряд.',
                          logarithmic_power=raw[2][2],small_argument=t)
    if raw[0]=='add' and raw[1][0]=='ln' and raw[2][:2]==('mul',q(-1)) and raw[2][2][0]=='ln' and raw[2][2][1][0]=='sin':
        t=raw[1][1]
        if (not conditions and t[:2]==('div',ONE) and t[2][:2]==('rpow',n) and t[2][2][0]=='s' and
                t==raw[2][2][1][1] and ctx['parameters']==[t[2][2][1]]):
            a=t[2][2][1]
            return result('difference_of_logs_normalized_by_small_sine',
                         branches([(a+'>1/2',verdict(True)),('0<='+a+'<=1/2',verdict()),
                                   (a+'<0',dict(classification='divergent where every source sine is positive, undefined otherwise'))]),
                         'Для положительного показателя аргумент 1/n^a находится в (0,1]. Переписать разность логарифмов как минус логарифм нормированного синуса. Его главный порядок равен квадрату аргумента, делённому на шесть.',
                         'Нулевой показатель даёт постоянный ненулевой член. При отрицательном показателе аргумент растёт, а во всех определённых индексах логарифм синуса не больше нуля. Это исключает сходимость и сохраняет исходные запреты.',
                         source_argument=t)
    if raw[0]=='sin' and raw[1][0]=='mul' and raw[1][1]==PI and raw[1][2][0]=='sqrt':
        u=raw[1][2][1]
        if u[0]=='add' and not domain_conditions(u) and not conditions:
            early,late=u[1:]
            if not m.contains(early,n):early,late=late,early
            p,d=rf(early,index);sq=p[2] if len(p)==3 and not p[0] and not p[1] and d==(1,) else None
            from math import isqrt
            if sq is not None and sq>0 and sq.denominator==1 and isqrt(int(sq))**2==sq and late[0]=='pow' and late[2]==2 and late[1][0]=='s' and ctx['parameters']==[late[1][1]]:
                a=isqrt(int(sq));k=late[1][1]
                return result('rationalize_integer_phase_before_harmonic_comparison',
                             branches([(k+'=0',verdict(True)),(k+'!=0',verdict(False,bool(a%2)))]),
                             'Выделить целую часть фазы a n. Рационализация остатка даёт k²/(sqrt(a²n²+k²)+a n), положительную убывающую величину при k≠0.',
                             'Вынести знак целой фазы. Оставшийся малый синус убывает на хвосте и имеет гармонический порядок. Чётная фаза даёт постоянный знак, нечётная даёт Лейбница.',
                             integer_phase_stride=a,source_radicand=u)
    if not ctx['parameters'] and raw[0]=='div' and raw[1][0]=='cos' and start>=2:
        phase=raw[1][1];weight=raw[2]
        if weight[0]=='pow' and weight[1]==('ln',n) and weight[2]>0:
            if all(guard_on_ray((g,e),index,start,ctx) for g,e in domain_conditions(phase)):
                p,d=rf(m.div(phase,PI),index)
                Q,R=pdiv(p,d)
                if (len(d)==2 and d[1]>0 and d[0]+start*d[1]>0 and len(Q)==2 and all(a.denominator==1 for a in Q)
                        and len(R)==1 and not domain_conditions(weight[1][1])):
                    return result('integer_phase_division_with_summable_cosine_error',verdict(False,bool(Q[1]%2)),
                                 'Разделить многочлены фазы. Целое линейное частное даёт точный периодический знак, а остаток имеет порядок 1/n.',
                                 'Малый косинус отличается от единицы на O(1/n²). Поправка суммируема, оставшийся логарифмический вес убывает, а его ряд модулей расходится.',
                                 integer_quotient=list(map(q,Q)),reciprocal_phase_remainder=q(R[0]),first_index=start)
    raise Unsupported('No verified logarithmic or integer-phase scale for the original term')


def rpow_index_degree(e,n):
    if e==n:return 1
    if e[0]=='pow' and e[1]==n:return e[2]
    return 0


def normalized_complex_geometric_disk(task):
    origin=task.get('source',{});word=r'([A-Za-z_]\w*)';var=re.fullmatch(word+r' complex',task.get('variable',''))
    index=re.fullmatch(word+r'>=(\d+)',task.get('index',''))
    if (not var or not index or int(index[2])!=1 or var[1]==index[1] or
            set(task)-{'kind','id','source','term','variable','index','printed_assumptions'} or
            task.get('printed_assumptions') not in (None,'no exclusion for alpha printed') or origin.get('literal_requirement') not in (
            None,'Определить радиус и круг сходимости в комплексной области, z=x+iy.')):
        raise Unsupported('The original center, printed first index and possible zero normalizer are not bound')
    z,n=map(re.escape,(var[1],index[1]));text=task.get('term','')
    r=re.fullmatch(r'\('+z+r'-exp\(i\*'+word+r'\)\)\^'+n+r'/\('+n+r'\*\(1-exp\(i\*\1\)\)\^'+n+r'\)',text)
    if not r or r[1] in (var[1],index[1],'i'):raise Unsupported('A fixed complex normalization must be extracted without index capture')
    a=r[1];center=f'exp(i*{a})';radius='abs(1-'+center+')'
    return result('complex_normalization_with_resonant_boundary',dict(
                  undefined_if=center+'=1',
                  when_defined=dict(center=center,radius=radius,open_disk=f'abs({var[1]}-({center}))<{radius}',
                                    boundary_diverges_at=var[1]+'=1',remaining_boundary='conditionally convergent')),
                  'При совпадении фиксированного центра с единицей исходный знаменатель равен нулю при каждом индексе.',
                  'На допустимой ветви ввести нормированную координату w=(z−c)/(1−c). Внутри единичного круга имеется абсолютная сходимость, снаружи общий член не стремится к нулю.',
                  'При |w|=1 и w≠1 геометрические частичные суммы ограничены и применяется Дирихле. При w=1 остаётся гармонический ряд.',
                  original_center=center,first_index=1)


def residual_series_scales(task,lib):
    if not lib.data.get('residual_series_and_derivative_scales'):raise Unsupported('The additional scale proofs are absent')
    if task['kind']=='complex_power_series_disk':return normalized_complex_geometric_disk(task)
    method=task.get('method_requirement')
    if (task['kind']!='series_convergence' or set(task)-ORDINARY_FIELDS-{'sequence_definitions'} or
            set(task)&{'tolerance','block_index','block_terms','hint'} or task.get('index_domain','integers')!='integers' or
            method not in GENERAL or method=='comparison_or_ratio_or_root' and 'sequence_definitions' not in task):
        raise Unsupported('The original integer series conditions are unresolved')
    text=task.get('term');index=task.get('index');start=task.get('start_index')
    if not isinstance(text,str) or not isinstance(index,str) or not index.isidentifier() or type(start) is not int or start<1:
        raise Unsupported('Need an exact positive integer lattice')
    series_scale_heading(task)
    if 'monic polynomials' in str(task.get('stated_conditions',())):
        return formal_monic_degree_ratio(task,index,text)
    if text.startswith('prod(ln('):return shifted_log_product_series(task,index,start)
    if text.startswith('factorial(') and '/product(' in text:return growing_factorial_product_ratio(task,index,start)
    ctx=index_context(index,task.get('parameters',[]),task.get('stated_conditions',[]))
    if 'sequence_definitions' in task:return radical_recurrence_series(task,index,start,ctx)
    raw=m.parse(text,index,ctx['parameters'])
    return logarithmic_germ_and_phase_scales(raw,index,start,ctx,task.get('stated_conditions',[]),task['requested_output'])


def boundary_series_head(task,kind):
    if kind=='infinite_product_identity':
        return bool(re.fullmatch(r'1\+.+\^\(2\*\w+\)',task.get('factor_or_given',''))) and task.get('start_index')==0
    if kind=='infinite_product_convergence':
        return bool(re.fullmatch(r'cos\(\w+_\w+\)',task.get('factor_or_given','')))
    return False


def remaining_series_claim(task,lib):
    if not lib.data.get('remaining_analysis_proofs'):raise Unsupported('Additional comparison and product proofs are unavailable')
    kind=task['kind'];origin=task.get('source',{});text=task.get('statement');label=origin.get('literal_requirement')
    if set(origin)-SOURCE_META-{'transcription_note'}:raise Unsupported('Original printed qualifications are still open')
    if kind=='series_theorem' and isinstance(text,str):
        prefix='Для положительной монотонно невозрастающей f и сходящегося Σf(n) доказать строгие оценки ∫_{n+1}^∞f(x)dx < R_n < f(n+1)+∫_{n+1}^∞f(x)dx. Пользуясь этим, найти Σ 1/n^'
        normal=text.translate(str.maketrans({'²':'^2','³':'^3','⁴':'^4','⁵':'^5'}))
        hit=re.fullmatch(re.escape(prefix)+r'(\d+) с точностью до (0,\d+)\.',normal)
        if hit and set(task)<={'kind','id','source','statement','requested_output'} and task.get('requested_output')==[
                'two_strict_bounds','numerical_sum','certified_accuracy'] and origin.get('printed_instruction') in (None,text):
            p=int(hit[1]);tol=Fraction(hit[2].replace(',','.'))
            if not 2<=p<=12 or tol<=0:raise Unsupported('Need a positive tolerance and a summable integer power')
            n=1
            while Fraction(1,2*(n+1)**p)>tol and n<1000:n+=1
            if n>=1000:raise Unsupported('The exact partial sum requires a larger lattice')
            partial=sum(Fraction(1,k**p) for k in range(1,n+1))
            lo=partial+Fraction(1,(p-1)*(n+1)**(p-1));hi=lo+Fraction(1,(n+1)**p)
            return result('integral_rectangle_bounds_preserve_weak_monotonicity',
                dict(printed_claim_holds=False,counterexample=dict(function='2^(-floor(t))',equality='lower bound equals the tail'),
                     numerical_sum=q((lo+hi)/2),strict_error_bound=q((hi-lo)/2),proved_interval=(q(lo),q(hi))),
                'Для убывания в широком смысле прямоугольники дают нестрогие оценки. Положительная геометрическая ступенчатая функция, постоянная на [k,k+1), даёт точное равенство нижней границы.',
                'Для численного степенного ряда высоты строго убывают на каждом интервале. Поэтому в специальном случае обе границы строгие.',
                'Вычислить конечную сумму и два хвостовых ограничения точно. Середина интервала имеет требуемую погрешность.',
                positive_power=p,last_index=n,tolerance=q(tol))
    if kind=='infinite_product_identity' and boundary_series_head(task,kind):
        if set(task)-{'kind','id','source','factor_or_given','index','start_index'} or not isinstance(label,str):
            raise Unsupported('The literal proposed product value is required')
        symbol=task['index'];h=re.fullmatch(r'1\+(.+)\^\(2\*'+re.escape(symbol)+r'\)',task['factor_or_given'])
        base=h[1].strip('()');symbolic=base.isidentifier()
        raw=m.parse(base,None,[base] if symbolic else [])
        b=q(1,2) if symbolic else m.simplify(raw);bv=m.num(b)
        if symbolic:
            pattern=r'Доказать равенство =1/\(1-'+re.escape(base)+r'\), abs\('+re.escape(base)+r'\)<1\.'
            claim=q(2) if re.fullmatch(pattern,label) else None
        else:
            hit=re.fullmatch(r'Доказать равенство =(\d+(?:/\d+)?)\.',label)
            claim=m.simplify(m.parse(hit[1],None)) if hit else None
        if bv is None or not 0<abs(bv)<1 or not claim or m.num(claim)>2 or (not symbolic and not m.constant_defined(raw,{})):
            raise Unsupported('The proposed value is not contradicted by the first two allowed factors')
        return result('first_positive_product_prefix_refutes_lower_claim',
            dict(printed_claim_holds=False,counterexample=dict(base=b,claimed=claim,first_pair_product=q(2*(1+bv*bv)))),
            'При ненулевом основании с модулем меньше единицы первый множитель равен двум, второй строго больше единицы. Все последующие множители не меньше единицы.',
            'Сумма геометрических поправок конечна, поэтому бесконечное произведение существует и превосходит заявленное число.',
            ordinary_exponent=f'2*{symbol}')
    if kind=='infinite_product_convergence' and boundary_series_head(task,kind):
        term=task['factor_or_given'];n=task['index']
        if (set(task)-{'kind','id','source','factor_or_given','index','start_index'} or task['start_index']!=1 or not re.fullmatch(r'cos\(\w+_'+re.escape(n)+r'\)',term)
                or label!='Prove convergence if the “series” printed as product(n>=1,x_n^2) converges.' or n!='n' or term!='cos(x_n)'):
            raise Unsupported('Neither an actual series premise nor a literal product premise is bound')
        return result('product_premise_cannot_replace_square_summability',
            dict(printed_claim_holds=False,counterexample=dict(sequence='x_n=1',square_product=ONE,cosine_factors=('cos',ONE),limit=ZERO,no_zero_factor=True)),
            'При постоянной единичной последовательности произведение квадратов равно единице. Каждый косинус строго между нулём и единицей.',
            'Произведение косинусов расходится к нулю по определению источника, потому что ни один исходный множитель не равен нулю.',
            corrected_series_hypothesis='square summability gives a positive tail with summable logarithms; separately check initial zero factors')
    raise Unsupported('No complete bound or product assertion follows from the source fields')
