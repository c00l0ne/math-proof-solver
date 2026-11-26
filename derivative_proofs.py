"""Replay ordinary derivative tables on raw domains and discharge exceptional points."""
from fractions import Fraction
from functools import cmp_to_key
from math import factorial
import re

import expressions as m
import intervals as line
import polynomial as poly
from graphs import ordinate, peval, rational_roots
from model import ONE, ZERO, Unsupported, instantiate, match, q
from operations import expression_positions
from tasks import domain_conditions, entailed_domain_guards, guard_source, known_guard, source
from verify import same_value

KINDS=frozenset({
    'abstract_difference_quotient_limit','sequential_derivative_characterization','derivative_level_set',
    'indexed_real_root_derivative','differentiate_by_substitution','logarithmic_derivative',
    'logarithmic_derivative_of_product','differentiate_functional','derivative_at_finite_product',
    'prove_determinant_derivative_rule','differentiate_determinant','prove_derivative_discontinuity',
    'classify_continuity_at_point','classify_differentiability_at_point','classify_derivative_continuity_at_point',
    'classify_bounded_derivative_near_point','classify_unbounded_derivative_near_point',
    'derivative_at_from_continuous_factor','prove_derivative_nonexistence_and_one_sided_values',
    'construct_continuous_function_with_prescribed_corners','prove_differentiability_and_accumulating_corners',
    'classify_differentiability_dense_piecewise','differentiable_gluing','derivative_closure_counterexample',
    'vertical_tangent_points','derivative_at_discontinuity','differentiate_inequality_counterexample',
    'differentiate_finite_sum','derivative_symmetry_proof','derivative_periodicity_proof',
    'differentiate_floor_expression',
})
BASE={'kind','id','source','schema','transcription','variable','parameters','stated_conditions',
      'method_requirement','requested_output'}
PROVENANCE={'exercise','pdf_page','printed_page','pdf_pages','printed_subpart','pdf_sha256',
            'literal_requirement','original_page_image_sha256','shared_instruction_page','source_continues_on_pdf_page',
            'printed_instruction','source_domain_note','heading_page','source_condition_literal'}
PRINTED_TABLE='Найти производные функций'
HEADINGS={
    'differentiate':('Find the derivative by the derivative table and its rules on the original real domain.',),
    'indexed_real_root_derivative':('The same number appears twice consecutively; indices m+n and n+m give the same radical.',),
    'global_one_sided_derivatives':('Определить левую и правую производные как функции x.',),
    'differentiable_gluing':('Подобрать a,b для непрерывности и дифференцируемости в x0.',
        'Подобрать a,b для непрерывного и дифференцируемого продолжения в x0.',
        'Построить сопряжение двух полупрямых кубической параболой, определив A,c.',
        'Определить параметры параболы для гладкого сопряжения с обеими внешними ветвями.'),
    'derivative_closure_counterexample':('Определить, следует ли недифференцируемость для данной операции, и разобрать напечатанный пример, если он дан.',),
    'vertical_tangent_points':('Найти все точки вертикального касания графика.',),
    'derivative_at_discontinuity':('Может ли разрывная функция иметь в точке разрыва указанную производную? Рассмотреть sgn x.',),
    'differentiate_inequality_counterexample':('Можно ли почленно дифференцировать неравенство между функциями?',),
    'differentiate_finite_sum':('Вывести формулы для обеих конечных сумм, используя указанную сумму степеней.',
        'Вывести формулы для обеих конечных тригонометрических сумм.',
        'Вывести формулу конечной суммы гиперболических косинусов.',
        'Вывести формулу суммы, пользуясь тождеством произведения косинусов.'),
    'derivative_symmetry_proof':('Доказать чётность/нечётность производной и дать геометрическую интерпретацию.',),
    'derivative_periodicity_proof':('Доказать, что производная периодической дифференцируемой функции имеет тот же период.',),
}
OPS={'add':'sum','mul':'product','div':'quotient','pow':'power','exp':'exp','ln':'log'}
NAME=r'[A-Za-z]\w*'


def require(cond,text):
    if not cond:raise Unsupported(text)


def routing(task,kind):
    if kind=='ambiguous_elementary_derivative':return True
    if higher_routing(task,kind) or mvt_routing(task,kind) or local_geometry_routing(task,kind):return True
    branches=task.get('branches')
    if isinstance(branches,list) and len(branches)==2 and all(isinstance(b,dict) for b in branches):
        if kind=='differentiate' and (' outside [' in str(branches[1].get('condition')) or (
                str(branches[0].get('condition','')).startswith('abs(') and 'sgn(' in str(branches[1].get('function')))):
            return True
        if kind=='one_sided_derivative_functions' and '*abs(cos(' in str(branches[0].get('function')):
            return True
    return kind in KINDS or (kind=='one_sided_derivative_functions' and isinstance(task.get('function'),str)
                            and task['function'].startswith(('floor(','sqrt(sin('))) or (
        kind=='global_one_sided_derivatives' and isinstance(task.get('function'),str)
        and task['function'].startswith(('sqrt(1-exp(','abs(ln(abs(','asin(2*'))) or (
        kind in ('differentiate','investigate_differentiability') and isinstance(task.get('function'),str)
        and 'branches' not in task and task.get('method_requirement') in (None,'table_and_rules')
        and (kind=='differentiate' and (task.get('requested_output')==['finite_derivative','natural_domain_and_boundary_notes']
                 or task.get('source',{}).get('printed_instruction')==PRINTED_TABLE and 'requested_output' not in task)
             and ('abs(' not in task['function'] or task['function'].startswith(('abs(sin','acos(1/abs')))
             or kind=='investigate_differentiability' and task['function'].startswith(('asin(cos','abs(cos','abs(pi^2'))))


def contract(task,allowed,outputs=None,methods=(None,'table_and_rules'),conditions=False,params=False):
    src=task.get('source',{})
    require(not set(task)-BASE-set(allowed) and isinstance(src,dict) and not set(src)-PROVENANCE
            and task.get('method_requirement') in methods
            and src.get('printed_instruction') in (None,PRINTED_TABLE)
            and src.get('literal_requirement') in (None,*HEADINGS.get(task['kind'],()))
            and src.get('source_condition_literal') in (None,'0 <= |b| < a','The definition in984 is stated for f(x)>0.')
            and (src.get('source_condition_literal')!='0 <= |b| < a' or task.get('stated_conditions')==['a>abs(b)'])
            and src.get('source_domain_note') in (None,'The source does not print a base restriction; a>0 follows from a real exponential on all real x.')
            and (outputs is None or task.get('requested_output')==outputs)
            and (conditions or not task.get('stated_conditions')) and (params or not task.get('parameters')),
            'Сохраняем исходные условия, способ решения и все запрошенные результаты')


def certificate(lib,rule,scope,value,*steps,**data):
    require(rule in lib.data.get('derivative_proof_transitions',()),'В библиотеке нет этого перехода о производных')
    return dict(theorem='derivative_proof.'+rule,scope=scope,argument=steps,**data),value


def table(e,x,lib,abstract=()):
    """Compose the stored derivative rule results, retaining the original rule identities."""
    answers={};used={}
    v=('v',x)
    def tidy(value):
        # These are exact formulas. Large composite formulas can keep the factored table form.
        return m.simplify(value) if m.size(value)<=100 else value
    def diff(u):
        if u in answers:return answers[u]
        tag=u[0];goal=('derivative',u);env={}
        if tag in abstract:
            arg=u[1];value=m.mul(('derivative_at_unknown',tag,arg),diff(arg))
            rule='chain_on_named_differentiable_function'
        else:
            constant=not m.variable_in(u,x)
            rule='derivative.'+('constant' if constant else 'variable' if u==v else OPS.get(tag,'chain_'+tag))
            spec=lib.by_id.get(rule)
            require(spec and match(spec['head'],goal,env),'Нет табличного правила для исходного элемента '+tag)
            for step in spec['steps']:
                bind=step['bind']
                require(step.get('ask',[None])[0] in (None,'defined','positive','nonzero','derivative') and
                        step.get('op') in (None,'tidy','minus_one','constant_defined','is_constant'),
                        'Новый тип предпосылки таблицы требует явной связи с исходной областью')
                if isinstance(bind,str) and bind.startswith('?') and step.get('ask',[None])[0]=='derivative':
                    env[bind]=diff(instantiate(step['ask'][1],env))
                elif step.get('op') in ('tidy','minus_one'):
                    value=instantiate(step['args'][0],env)
                    env[bind[0]]=tidy(value) if step['op']=='tidy' else value-1
            value=tidy(instantiate(spec['result'],env))
        answers[u]=value;used[u]=rule
        return value
    value=diff(e)
    return value,tuple((u,used[u],d) for u,d in answers.items())


def scalar_context(task):
    var=task.get('variable','x');pars=task.get('parameters',[])
    require(re.fullmatch(NAME,var) and isinstance(pars,list),'Не разобраны имена переменной и постоянных')
    names=[p['symbol'] if isinstance(p,dict) else p for p in pars]
    require(len(set(names))==len(names) and var not in names and all(re.fullmatch(NAME,n) for n in names),
            'Переменная и параметры должны различаться')
    conditions=[c.replace(' ','') for c in task.get('stated_conditions',[])]
    # The context understands strict conditions. Weak inequalities remain explicit in the certificate.
    inferred=[]
    for c in conditions:
        s=re.fullmatch(rf'abs\(({NAME})\)<abs\(({NAME})\)',c)
        if s:inferred.append(f'{s[2]}^2-{s[1]}^2>0')
        s=re.fullmatch(rf'({NAME})>abs\(({NAME})\)',c)
        if s:inferred.extend((f'{s[1]}^2-{s[2]}^2>0',f'{s[1]}-{s[2]}>0',f'{s[1]}+{s[2]}>0'))
        s=re.fullmatch(rf'({NAME})-({NAME})>0',c)
        if s and f'{s[2]}>=0' in conditions:
            inferred.extend((f'{s[1]}^2-{s[2]}^2>0',f'{s[1]}+{s[2]}>0'))
    strict=[]
    for c in conditions:
        if '<=' in c or '>=' in c:continue
        if '<' in c:
            a,b=c.split('<');c=f'({b})-({a})>0'
        elif '>' in c and not c.endswith('>0'):
            a,b=c.split('>');c=f'({a})-({b})>0'
        strict.append(c)
    ctx=m.context(dict(variable=var,parameters=pars,parameter_conditions=strict+inferred))
    return var,names,conditions,ctx


def zero_points(e,x,ctx,natural):
    from graphs import rational_roots
    from scalar_proofs import global_guard
    if global_guard(('nonzero',e),x,ctx):return set()
    u=m.simplify(e)
    if u[0] in ('sqrt','cbrt','abs') or u[0]=='pow' and u[2]>0:
        return zero_points(u[1],x,ctx,natural)
    if u[0]=='mul':
        return zero_points(u[1],x,ctx,natural)|zero_points(u[2],x,ctx,natural)
    if u[0]=='div':return zero_points(u[1],x,ctx,natural)
    if u[0] in ('asin','atan','sinh','tanh'):
        return zero_points(u[1],x,ctx,natural)
    if u[0]=='acos':return zero_points(m.add(u[1],q(-1)),x,ctx,natural)
    if u[0]=='ln':return zero_points(m.add(u[1],q(-1)),x,ctx,natural)
    if u[0]=='add':
        for a,b in (u[1:],u[:0:-1]):
            if a[0]=='cbrt' and m.num(b) is not None:
                return zero_points(m.add(a[1],q(m.num(b)**3)),x,ctx,natural)
            if b==q(-1) and (a[0]=='cosh' or a[0]=='pow' and a[2]==2 and a[1][0]=='cosh'):
                return zero_points(a[1] if a[0]=='cosh' else a[1][1],x,ctx,natural)
            if b==q(-1) and a[0]=='abs':
                return zero_points(m.add(m.power(a[1],2),q(-1)),x,ctx,natural)
            if a==ONE and b[0]=='mul' and b[1]==q(-1):
                w=b[2]
                if w[0]=='pow' and w[2]>0:w=w[1]
                if w[0]=='exp':return zero_points(w[1],x,ctx,natural)
            if b==('mul',q(-1),('pow',('v',x),2)) and a[0]=='pow' and a[2]==2 and m.constant_defined(a[1],ctx):
                return {a[1],m.neg(a[1])}
        squares=[z[1] for z in u[1:] if z[0]=='pow' and z[2]==2]
        if len(squares)==2 and any(('nonzero',z) in natural or ('positive',z) in natural
                                   or ('positive',m.neg(z)) in natural for z in squares):
            return set()
    if u[0]=='add' and any(a[0]=='sqrt' and (('nonnegative',b) in natural or ('positive',b) in natural)
                          for a,b in (u[1:],u[:0:-1])):
        a=next(z for z in u[1:] if z[0]=='sqrt')
        return zero_points(a[1],x,ctx,natural)
    try:
        p,d=poly.rf(u,x)
        require(any(p),'Особый уровень тождественно нулевой')
        if len(p)==4 and not any(p[1:3]):return {m.simplify(('cbrt',q(-p[0]/p[3])))}
        return {q(z.a) if not z.b else m.add(q(z.a),m.mul(q(z.b),('sqrt',q(z.d)))) for z in rational_roots(p)}
    except (poly.NotRational,poly.Undefined) as exc:
        raise Unsupported('Не изолированы нули особого уровня '+source(e)) from exc


def endpoint_rows(raw,x,pars,conditions,ctx,natural,smooth,lib,composition=None):
    from limit_proofs import stable_germ_at
    from tasks import known_guard
    xvar=('v',x)
    consequences=set(entailed_domain_guards(natural))
    def invalid(g):
        rel,term=g;s=m.sign(term,ctx)
        return {'positive':s in (-1,0),'nonnegative':s==-1,'nonzero':s==0}[rel]
    def excluded_square_sum(e):
        e=m.simplify(e)
        if e[0]!='add' or not all(z[0]=='pow' and z[2]==2 and z[1][0] in ('s','v') for z in e[1:]):
            return False
        # A sum of squares vanishes exactly when each real summand vanishes.
        values={z[1]:ZERO for z in e[1:]}
        return any(invalid((r,m.substitute(v,values))) for r,v in natural)
    boundaries=set()
    for g in set(smooth)-set(natural):
        if g in consequences or (('nonzero',g[1]) in consequences and ('nonnegative',g[1]) in natural):continue
        if excluded_square_sum(g[1]):continue
        boundaries.update(zero_points(g[1],x,ctx,natural))
    rows=[]
    for point in sorted(boundaries,key=str):
        repl={xvar:point}
        evaluated=[(guard,m.substitute(level,repl)) for guard,level in natural]
        if any(invalid(g) for g in evaluated):
            rows.append(dict(point=point,original_value='undefined'));continue
        at=m.substitute(raw,repl)
        require(m.constant_defined(at,ctx),'Не установлено значение исходной функции в особой точке')
        if pars and any(e[0] in ('sin','cos','tan','cot') and any(t[0]=='s' for _,t in expression_positions(e))
                        for _,e in expression_positions(at)):
            raise Unsupported('Граничное разностное отношение требует разбить постоянные параметры по фазам')
        f,at_f=raw,at;multiplier=ONE
        if composition:
            inner,outer,u,dg=composition
            inner_at=m.simplify(m.substitute(inner,repl))
            outer_sub={u:inner_at}
            outer_d=m.simplify(m.substitute(dg,outer_sub))
            if (all(known_guard((r,m.substitute(e,outer_sub)),ctx) for r,e in domain_conditions(outer,True))
                    and m.sign(outer_d,ctx) in (-1,1)):
                f,at_f=inner,inner_at;multiplier=outer_d
        elementary={}
        for _,e in expression_positions(f):
            if e[0] in ('sec','csc'):
                elementary[e]=('div',ONE,('cos' if e[0]=='sec' else 'sin',e[1]))
            if e[0]=='acot':
                elementary[e]=m.add(m.mul(q(1,2),m.PI),m.neg(('atan',e[1])))
        numerator=('add',m.substitute(f,elementary),('mul',q(-1),at_f))
        quotient=('div',numerator,('add',xvar,m.neg(point)))
        traces=[]
        for side in ('left','right'):
            plan,value=stable_germ_at(quotient,x,source(point),side,lib,pars,conditions)
            if isinstance(value,tuple):value=m.mul(multiplier,value)
            if value in ('+inf','-inf') and m.sign(multiplier,ctx)==-1:value='-inf' if value=='+inf' else '+inf'
            traces.append(dict(direction=side,value=value,replay=plan,outer_slope=multiplier,
                               elementary_reciprocals=tuple(elementary.items())))
        rows.append(dict(point=point,original_value=m.simplify(at),traces=traces))
    return rows


def complete_table(task,lib):
    fn=task.get('function','');meta=task.get('source',{})
    if (lib.data.get('raw_boundary_derivative_profiles') and task['kind']=='differentiate' and isinstance(fn,str)
            and ('cbrt(' in fn or fn.startswith('(asin(') or 'source_notation' in meta)):
        try:return original_boundary_derivative(task,lib)
        except (Unsupported,poly.NotRational,poly.Undefined):pass
    if lib.data.get('remaining_analysis_proofs') and lifted_table_input(task):
        try:return complete_source_endpoint_table(task,lib)
        except (Unsupported,poly.NotRational,poly.Undefined):pass
    kind=task['kind'];investigative=kind!='differentiate'
    outputs={'differentiate':['finite_derivative','natural_domain_and_boundary_notes'],
             'investigate_differentiability':['complete_differentiability_domain','derivative_formula','boundary_and_one_sided_notes'],
             'one_sided_derivative_functions':['left_derivative_function','right_derivative_function','finite_infinite_and_domain_statuses']}
    expected=outputs.get(kind) if 'requested_output' in task or task.get('source',{}).get('printed_instruction')!=PRINTED_TABLE else None
    contract(task,{'function'},expected,params=True,conditions=True)
    x,pars,conditions,ctx=scalar_context(task);text,sep,restriction=task['function'].partition(' for ')
    raw=m.parse(text,x,pars)
    natural=domain_conditions(raw);smooth=domain_conditions(raw,True)
    if sep:
        require(restriction==x+'!=0' and (('nonzero',('v',x)) in set(entailed_domain_guards(natural))
                or ('positive',('abs',('v',x))) in natural),
                'Дополнительное ограничение стороны не проверено')
    require(all(r=='nonnegative' or m.simplify(e)!=ZERO for r,e in natural),'Исходная область пуста из-за нулевого строгого условия')
    formula,proof=table(raw,x,lib)
    scope=dict(variable=x,parameters=task.get('parameters',[]),conditions=conditions,original_guards=natural)
    phase=angular_boundaries(raw,x,lib)
    if phase is not None:
        return certificate(lib,'principal_phase_derivatives',scope,
            dict(formula=formula,smooth_domain=smooth,folds=phase) if investigative else formula,
            'Определить фазовые уровни из границ главного значения, а не из сокращённой формулы.',
            'В особых уровнях применить односторонний профиль внешней функции к первому ненулевому члену фазы.',
            table_steps=proof,source_expression=raw,smooth_domain=smooth,exceptional_points=phase)
    boundaries=endpoint_rows(raw,x,pars,conditions,ctx,natural,smooth,lib)
    return certificate(lib,'raw_domain_derivative_table',scope,
        dict(formula=formula,smooth_domain=smooth,exceptional_points=boundaries) if investigative else formula,
        'Применить таблицу к исходному дереву, сохранив ограничения каждого исходного узла.',
        'В точках, где таблице не хватает строгого ограничения, проверить исходное значение и оба относительных отношения.',
        table_steps=proof,source_expression=raw,smooth_domain=smooth,exceptional_points=boundaries)


def substitute_outer(task,lib,request):
    if lib.data.get('raw_boundary_derivative_profiles') and 'acos(' in str(task.get('function','')):
        try:return arccos_substitution_endpoint(task,lib)
        except Unsupported:pass
    from verify import same_value
    outputs=['finite_derivative','explicit_intermediate_variable_chain','natural_domain_and_boundary_notes']
    contract(task,{'function','required_substitution'},outputs,('intermediate_substitution',),True,True)
    x,pars,conditions,ctx=scalar_context(task);raw=m.parse(task['function'],x,pars);v=('v',x)
    text=task.get('required_substitution')
    if text:
        name,eq,expr=text.partition('=');require(eq and re.fullmatch(NAME,name) and name not in [x,*pars],'Не разобрана заданная подстановка')
        inner=m.parse(expr,x,pars)
    else:
        name='u'
        while name in [x,*pars]:name+='_'
        inner=None
    u=('v',name)
    # Find a repeating nonleaf expression whose replacement binds every occurrence of x.
    candidates=(inner,) if inner else tuple(dict.fromkeys(e for path,e in expression_positions(raw) if path and m.variable_in(e,x) and e!=v))
    lifting={}
    for candidate in sorted(candidates,key=m.size,reverse=True):
        replacements={candidate:u};laws={}
        if candidate[0]=='pow' and candidate[2]>0:
            for _,part in expression_positions(raw):
                if part!=candidate and part[0]=='pow' and part[1]==candidate[1] and part[2]>0 and part[2]%candidate[2]==0:
                    multiple=part[2]//candidate[2]
                    replacements[part]=('pow',u,multiple);laws[part]=multiple
        if candidate[0]=='exp' or candidate[0]=='rpow' and not m.variable_in(candidate[1],x):
            tag=candidate[0];phase=candidate[-1]
            for _,part in expression_positions(raw):
                if part==candidate or part[0]!=tag or tag=='rpow' and part[1]!=candidate[1]:continue
                multiple=m.num(m.simplify(m.div(part[-1],phase)))
                if multiple is None or multiple.denominator!=1 or not 0<abs(multiple)<=12:continue
                if same_value(part[-1],m.mul(q(multiple),phase)):
                    replacements[part]=('pow',u,int(multiple));laws[part]=int(multiple)
        outer=m.substitute(raw,replacements)
        if m.variable_in(outer,x) or not m.variable_in(outer,name):continue
        if not laws and not same_value(m.substitute(outer,{u:candidate}),raw):continue
        lifting=laws
        inner=candidate;break
    else:raise Unsupported('Повторяющееся подвыражение не охватывает все исходные появления переменной')
    df,inside=table(inner,x,lib);dg,outside=table(outer,name,lib);formula=m.mul(df,m.substitute(dg,{u:inner}))
    natural=domain_conditions(raw);smooth=domain_conditions(raw,True)
    # Substitution cannot introduce an extra restriction on the original smooth chart.
    assembled=domain_conditions(inner,True)+[(r,m.substitute(e,{u:inner})) for r,e in domain_conditions(outer,True)]
    from scalar_proofs import global_guard
    facts=[guard_source(g) for g in entailed_domain_guards(natural) if not m.variable_in(g[1],x)]
    fixed=m.context(dict(variable=x,parameters=pars,parameter_conditions=[c for c in conditions if '>=' not in c and '<=' not in c]+facts))
    admissible=set(smooth)|set(entailed_domain_guards(smooth))
    restored={('pow',inner,k):part for part,k in lifting.items()}
    assembled=[(r,m.substitute(e,restored)) for r,e in assembled]
    require(all(g in admissible or global_guard(g,x,fixed) or any(r==g[0] and same_value(e,g[1]) for r,e in admissible)
                for g in assembled),'Заменённая область отличается от исходной')
    boundaries=endpoint_rows(raw,x,pars,conditions,ctx,natural,smooth,lib,(inner,outer,u,dg))
    return certificate(lib,'find_inner_coordinate',dict(variable=x,conditions=conditions,original_domain=natural),
        dict(inner=inner,outer=outer,substitution_variable=name,formula=formula,smooth_domain=smooth,exceptional_points=boundaries),
        'Выделить внутреннюю переменную и проверить восстановление исходного дерева.',
        'Применить таблицу к внешней и внутренней функциям и проверить область подстановки.',
        inner_table=inside,outer_table=outside,exponential_power_lifting=tuple(lifting.items()))

def functional_derivative(task,lib):
    contract(task,{'functions','function'},['derivative_formula','explicit_function_hypotheses',
             'natural_domain_and_boundary_notes'],conditions=True)
    funcs=task['functions'];require(isinstance(funcs,dict) and funcs and set(funcs.values())<={
                                         'differentiable','differentiable on every used argument'},
                                     'Требуются дифференцируемые функции с объявленной областью аргументов')
    x=task.get('variable','x');expr=task['function'];names=set(funcs)
    log=re.fullmatch(r'log_base\((\w+\('+re.escape(x)+r'\)),(\w+\('+re.escape(x)+r'\))\)',expr)
    if log:expr=f'ln({log[2]})/ln({log[1]})'
    raw=m.parse(expr,x,extra_functions=names)
    given=[]
    for c in task.get('stated_conditions',[]):
        relation=re.fullmatch(r'(.+?)(!=|>)0',c);require(relation,'Не разобрано условие на значение функции')
        given.append(('nonzero' if relation[2]=='!=' else 'positive',m.parse(relation[1],x,extra_functions=names)))
    guards=domain_conditions(raw);smooth=domain_conditions(raw,True)
    derivative,tree=table(raw,x,lib,names)
    pending=set(smooth)-set(guards)
    special=None
    if pending:
        norm=raw[0]=='sqrt' and raw[1][0]=='add' and all(c[0]=='pow' and c[2]==2 and c[1][0] in names for c in raw[1][1:])
        require(norm,'Особые точки неизвестной функции требуют отдельного разностного отношения')
        args=tuple(c[1] for c in raw[1][1:])
        d=tuple(table(a,x,lib,names)[0] for a in args)
        special=dict(at=dict(zero_arguments=args),finite_derivative=ZERO,iff_zero_derivatives=d,
                     otherwise_left_and_right=('negative Euclidean norm of derivatives','positive Euclidean norm of derivatives'))
    arguments=tuple(dict(function=e[0],original_argument=e[1]) for _,e in expression_positions(raw) if e[0] in names)
    return certificate(lib,'named_function_chain',dict(functions=funcs,stated_values=given,argument_membership=arguments),
        dict(formula=derivative,natural_domain=guards,smooth_domain=smooth,common_zero_case=special),
        'Связать каждое значение внешней функции с её производной в том же аргументе.',
        'Сохранить исходные условия логарифмов, знаменателей и степеней.',
        *(( 'В общей нулевой точке норма приращения имеет ведущий член |h| умножить на норму вектора производных.',) if special else ()),
        table_steps=tree)


def derivative_algebra(task,lib):
    kind=task['kind'];x=task.get('variable','x');v=('v',x)
    if kind=='derivative_level_set':
        from graphs import rational_roots
        contract(task,{'function','level'},['derivative_formula','all_real_solutions_of_derivative_equals_level'])
        raw=m.parse(task['function'],x);level=m.parse(task['level'],None)
        from tasks import known_guard
        ctx=m.context(dict(variable=x))
        require(all(known_guard(g,ctx) for g in domain_conditions(raw)) and m.num(level) is not None,
                'Требуется полиномиальная производная и числовой уровень')
        df,tree=table(raw,x,lib);p,d=poly.rf(m.add(df,m.neg(level)),x);require(any(p),'Тождественный уровень требует отдельного ответа')
        roots=[line.quadratic_term(z) for z in rational_roots(p)]
        return certificate(lib,'differentiate_then_solve',dict(variable=x,source=raw,level=level),
            dict(derivative=df,solutions=roots),'Вычислить производную и исчерпывающе решить полиномиальное равенство.',table_steps=tree)
    if kind=='derivative_at_finite_product':
        contract(task,{'function_family','point'},['finite_derivative_at_point'])
        f=task['function_family'];a,b,k=f['lower'],f['upper'],f['index']
        require(set(f)=={'operator','lower','upper','index','factor'} and f['operator']=='product'
                and type(a) is int and type(b) is int and 0<=b-a<=1200 and re.fullmatch(NAME,k) and k!=x,
                'Требуется конечное произведение аффинных множителей по целому индексу')
        factor=m.parse(f['factor'],x,[k]);target=('add',v,('mul',q(-1),('s',k)))
        from verify import same_value
        require(not domain_conditions(factor) and same_value(factor,target),'Множитель должен обращаться в нуль ровно при x=k')
        p=m.num(m.parse(task['point'],None))
        require(p is not None and p.denominator==1 and a<=p<=b,'Нет единственного нулевого множителя в указанной точке')
        j=int(p);value=q((-1)**(b-j)*factorial(j-a)*factorial(b-j))
        return certificate(lib,'single_zero_product_factor',dict(integer_interval=(a,b),point=q(p),factor=factor),value,
            'Только член, дифференцирующий нулевой множитель, остаётся в формуле производной конечного произведения.')
    if kind.startswith('logarithmic_derivative'):
        outputs=['logarithmic_derivative','original_positive_function_domain']
        contract(task,{'function','function_family'},outputs,('logarithmic_differentiation',),True,True)
        if kind.endswith('_of_product'):
            f=task['function_family'];k=f['index'];n=f['upper'];a=re.fullmatch(r'\('+x+r'-(\w+)\['+k+r'\]\)\^(\w+)\['+k+r'\]',f['factor'])
            require(a and f==dict(operator='product',index=k,lower=1,upper=n,factor=f['factor'])
                    and task['parameters']==[dict(symbol=n,domain='positive_integer'),
                      dict(symbol=a[1],domain='indexed_real_family'),dict(symbol=a[2],domain='indexed_real_family')]
                    and not task.get('stated_conditions'),'Исходные индексы, постоянные и показатели не связаны')
            return certificate(lib,'positive_logarithmic_derivative',dict(positive_product=True,domain=f'{x}>max {a[1]}[{k}] on the standard real-power domain'),
                dict(formula=f'sum({a[2]}[{k}]/({x}-{a[1]}[{k}]), {k}=1..{n})'),
                'Применить логарифм к положительному произведению. На других действительных положительных ветвях использовать логарифмы модулей ненулевых факторов.',
                'Конечная сумма разрешает дифференцировать каждый логарифм отдельно.')
        x,pars,conditions,ctx=scalar_context(task);raw=m.parse(task['function'],x,pars);d,tree=table(raw,x,lib)
        natural=domain_conditions(raw)+[('positive',raw)];smooth=domain_conditions(raw,True)
        ends=endpoint_rows(raw,x,pars,conditions,ctx,natural,smooth,lib)
        require(all(row['original_value']=='undefined' for row in ends),'На положительной области осталась особая точка логарифма')
        return certificate(lib,'positive_logarithmic_derivative',dict(variable=x,source=raw,natural_domain=natural,conditions=conditions),
            dict(formula=m.div(d,raw),positive_domain=natural),
            'На исходной положительной области применять цепное правило к ln(y), сохраняя все ограничения источника.',
            'Проверить, что нули исходных подкоренных выражений исключены из этой положительной области.',table_steps=tree,boundaries=ends)
    if kind=='indexed_real_root_derivative':
        contract(task,{'radicand','root_index','repeated_printed_form'},['derivative_on_natural_real_domain'])
        names=re.fullmatch(r'(\w+)\+(\w+)',task['root_index']);require(names and len({x,*names.groups()})==3,'Требуется индекс как сумма двух независимых показателей')
        a,b=names.groups();r=m.parse(task['radicand'],x,[a,b])
        expected=m.parse(f'(1-{x})^{a}*(1+{x})^{b}',x,[a,b])
        require(r==expected and task.get('repeated_printed_form') in (None,f'index {b}+{a}, identical radicand'),
                'Радиканд или повторное написание индекса отличаются от связанной формулы')
        return certificate(lib,'indexed_real_radical',dict(radicand=r,index=f'{a}+{b}',index_positive_integer=True),
            dict(formula=f'y*({b}-{a}-({a}+{b})*{x})/(({a}+{b})*(1-{x}^2))',
                 smooth_domain='original power and root branches, x!=±1, radicand nonzero',
                 ordinary_integer_cases='odd index includes negative radicands; even index admits only nonnegative radicands',
                 boundary_exponents=(f'{b}/({a}+{b})',f'{a}/({a}+{b})')),
            'Из уравнения y^d=R при ненулевом корне получить y′=R′/(d y^(d−1)).',
            'Внутри каждой ненулевой действительной ветви сократить R′/R по двум факторам.',
            'В точках ±1 конечность разностного отношения определяется соответствующими порядками корня. При положительных целых показателях оба порядка строго между нулём и единицей.')
    if kind=='prove_determinant_derivative_rule':
        contract(task,{'matrix_family'},['proof','explicit_differentiability_hypotheses'],('prove_general_rule',),params=True)
        f=task['matrix_family']
        require(f==dict(size='n by n',entry=f'f[i,j]({x})',hypotheses='Every entry is differentiable on the common open interval.')
                and task['parameters']==[dict(symbol='n',domain='positive_integer')],'Не разобрана размерность или общая область определителя')
        return certificate(lib,'differentiate_determinant_rows',dict(matrix=f,hypotheses='every entry differentiable'),
            dict(identity='(det A)′ = sum_i det A with row i replaced by its derivative'),
            'Разложить определитель по перестановкам. В каждом произведении выбрать один дифференцированный множитель.',
            'Группировка по номеру строки даёт сумму определителей с одной дифференцированной строкой.')
    from itertools import permutations
    contract(task,{'matrix'},['finite_derivative','natural_domain_and_boundary_notes'])
    matrix=task['matrix'];n=len(matrix)
    require(1<=n<=4 and all(len(row)==n for row in matrix),'Для явного определителя требуется небольшая квадратная матрица')
    parsed=[[m.parse(e,x) for e in row] for row in matrix]
    require(not any(domain_conditions(e,True) for row in parsed for e in row),'Матрица содержит особые входы')
    polynomial=ZERO
    for p in permutations(range(n)):
        term=q((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))
        for i,j in enumerate(p):term=m.mul(term,parsed[i][j])
        polynomial=m.add(polynomial,term)
    d,tree=table(polynomial,x,lib)
    return certificate(lib,'differentiate_determinant_rows',dict(matrix=parsed,domain='real line'),
        dict(formula=d,determinant=polynomial),'Точно разложить определитель по перестановкам и продифференцировать конечную сумму.',table_steps=tree)


def floor_derivative(task,lib):
    x=task.get('variable','x');kind=task['kind']
    ordinary=kind=='differentiate_floor_expression'
    want=['finite_derivative','natural_domain_and_boundary_notes'] if ordinary else ['left_derivative_function','right_derivative_function','finite_infinite_and_domain_statuses']
    contract(task,{'function','required_functions'},want)
    require(task.get('required_functions',['floor'])==['floor'],'Не разобрана ступенчатая операция')
    v=('v',x);expr=m.parse(task['function'],x,extra_functions={'floor'});step=('floor',v)
    require(expr[0]=='mul' and step in expr[1:],'Ожидалось произведение целой части и непрерывного множителя')
    phase=expr[2] if expr[1]==step else expr[1]
    a,n=(phase[1],phase[2]) if phase[0]=='pow' else (phase,1)
    require(a==('sin',m.parse('pi*'+x,x)) and n>=1 and (not ordinary or n>=2),'Фазовый множитель должен исчезать во всех целых точках')
    d,tree=table(phase,x,lib);k=('s','k')
    return certificate(lib,'derivative_on_integer_cells',dict(source=expr,cell='k<x<k+1'),
        dict(on_open_cells=m.mul(k,d),integer_left=ZERO if n>1 else 'pi*(k-1)*(-1)^k',
             integer_right=ZERO if n>1 else 'pi*k*(-1)^k',both_sides_equal=n>1),
        'Внутри каждой ячейки целая часть постоянна.',
        'При целом k исходное значение нуль. Использовать \u03c0(-1)^k h как первый член синуса и разные значения целой части слева и справа.',table_steps=tree)

def quotient_principles(task,lib):
    kind=task['kind'];x=task.get('variable','x');xvar=('v',x)
    if kind=='abstract_difference_quotient_limit':
        contract(task,{'expression','assumptions','point'})
        a=task['point'];match_=re.fullmatch(rf'\(({NAME})\({x}\)-\1\({a}\)\)/\({x}-{a}\)',task['expression'])
        require(match_ and re.fullmatch(NAME,a) and a!=x and task['assumptions']==[f'{match_[1]} differentiable at {a}'],
                'Разностное отношение или его исходная дифференцируемость не совпадают')
        return certificate(lib,'derivative_definition_transport',dict(point=a,assumptions=task['assumptions']),
            dict(limit=f'{match_[1]}′({a})'),'Положить h=x−a и применить точное определение производной.')
    if kind=='sequential_derivative_characterization':
        contract(task,{'expression','sequence_index','index_domain'},['prove convergence to f-prime for differentiable f',
                                                                        'decide converse using Dirichlet function'])
        n=task['sequence_index'];s=re.fullmatch(rf'{n}\*\(({NAME})\({x}\+1/{n}\)-\1\({x}\)\)',task['expression'])
        require(s and n!=x and task['index_domain']=='natural_numbers','Не разобрана натуральная последовательность шагов')
        return certificate(lib,'derivative_definition_transport',dict(increment=f'1/{n}',sequence_domain='positive integers'),
            dict(limit=f'{s[1]}′({x})',converse=False,dirichlet_limit=ZERO),
            'Производная даёт предел вдоль каждой допустимой последовательности ненулевых шагов.',
            'В обратную сторону рациональные сдвиги оставляют класс рациональности, поэтому у функции Дирихле отношения тождественно нулевые.',
            'Иррациональные и рациональные точки плотны, а конечная производная требовала бы непрерывности.')
    if kind=='derivative_at_discontinuity':
        contract(task,{'derivative_type','example'})
        t=task['derivative_type'];require(t in ('finite','infinite') and task['example']==f'sign({x})','Нужно связать тип производной и напечатанный пример')
        steps=('Конечное разностное отношение, умноженное на h, стремится к нулю и заставляет исходную функцию быть непрерывной.',)
        if t=='infinite':steps=('У sign(x) левый и правый пределы различаются, а значение в нуле 0.',
                               'Оба отношения sign(h)/h=1/|h| стремятся к +∞.')
        return certificate(lib,'derivative_definition_transport',dict(discontinuous_at_point=True,derivative_type=t),
            dict(possible=t=='infinite',sign_example_derivative='+inf'),*steps)
    if kind=='derivative_periodicity_proof':
        contract(task,{'hypothesis'})
        s=re.fullmatch(rf'({NAME})\({x}\+({NAME})\)=\1\({x}\)',task['hypothesis']);require(s,'Ожидается периодический сдвиг')
        return certificate(lib,'derivative_definition_transport',dict(period=s[2],source_function=s[1]),
            dict(derivative_has_period=s[2]),'Сдвиг на период сохраняет оба значения в разностном отношении и потому его предел.')
    if kind=='derivative_symmetry_proof':
        contract(task,{'assumptions'})
        require(task['assumptions']=='differentiable even or odd function on symmetric domain','Не задана симметричная область с дифференцируемой функцией')
        return certificate(lib,'derivative_definition_transport',dict(symmetric_domain=True),dict(even_derivative='odd',odd_derivative='even'),
            'Дифференцировать f(−x)=±f(x), множитель −1 от отражения меняет чётность.',
            'При отражении относительно вертикальной оси наклон касательной меняет знак. При центральной симметрии наклон сохраняется.')
    side=kind=='prove_derivative_nonexistence_and_one_sided_values'
    contract(task,{'functions','function','point'},
        ['proof_of_no_ordinary_derivative','finite_one_sided_derivatives'] if side else ['finite_derivative_at_point','proof'],
        ('from_definition_with_continuity',),True,True)
    point=task['point'];fs=task['functions'];fn=next(iter(fs))
    require(len(fs)==1 and task['parameters']==[point]
            and fs[fn] in (f'continuous at {point} only',f'continuous at {point} only; differentiability is NOT assumed'),
            'Непрерывный множитель должен относиться к исходной точке')
    f=m.parse(task['function'],x,[point],extra_functions={fn});base=m.parse(f'{x}-{point}',x,[point]);expected=(('abs',base) if side else base)
    require(f==('mul',expected,(fn,xvar)) and task['stated_conditions']==([f'{fn}({point})!=0'] if side else []),
            'Не разобран нулевой множитель, его чётность или ненулевость')
    at=(fn,('s',point))
    vals=dict(left=m.neg(at),right=at,ordinary_exists=False) if side else at
    return certificate(lib,'derivative_definition_transport',dict(point=point,factor=fn,continuous=True,nonzero=side),vals,
        'Сократить разностное отношение на ненулевом шаге.',
        'По непрерывности оставшийся множитель стремится к значению в исходной точке. У модуля шаг меняет знак на другой стороне.')


def oscillatory_source(task,lib):
    kind=task['kind'];x=task.get('variable','x');v=('v',x);name=task.get('parameters',[]);method=task.get('method_requirement')
    outputs=task.get('requested_output')
    regular=['necessary_and_sufficient_parameter_conditions','proof']
    want={'prove_derivative_discontinuity':['derivative_formula','proof_of_discontinuity'],
          'prove_differentiability_and_accumulating_corners':['derivative_at_zero','proof_of_nondifferentiability_arbitrarily_near_zero'],
          'classify_differentiability_dense_piecewise':['complete_differentiability_domain','proof']}
    chosen=want.get(kind,regular+['neighborhood_scope' if 'bounded_derivative' in kind else 'real_power_domain_notes'])
    contract(task,{'branches','point'},chosen,('prove_statement','classify_parameter_conditions'),True,True)
    a,b=task['branches'];dense=kind=='classify_differentiability_dense_piecewise'
    require(set(a)==set(b)=={'condition','function'} and b['function']=='0' and
            (a['condition'],b['condition'])==((x+' rational',x+' irrational') if dense else (x+'!=0',x+'=0'))
            and task.get('point','0')=='0','Исходный кусок и присвоенное значение в нуле не совпадают')
    f=m.parse(a['function'],x,name);absx=('abs',v)
    if dense:
        require(f[0]=='pow' and f[1]==v and f[2]>=2 and not name and not task['stated_conditions'],'Ветвь должна быть ненулевой вне нуля и иметь порядок выше первого')
        return certificate(lib,'sequences_at_exceptional_point',dict(branches=task['branches']),
            dict(differentiable_only_at=ZERO,derivative_at_zero=ZERO),
            'В ненулевой точке рациональные и иррациональные аргументы дают разные пределы значений.',
            'В нуле обе ветви ограничены O(|h|²), поэтому разностное отношение стремится к нулю.')
    require(f[0]=='mul','Требуется затухающий амплитудный множитель исходной фазы')
    amp,wave=f[1:];pure=kind=='prove_derivative_discontinuity'
    if kind=='prove_differentiability_and_accumulating_corners':
        require(amp[0]=='pow' and amp[1]==v and amp[2]>1 and wave==('abs',('cos',('div',m.PI,v)))
                and not name and not task['stated_conditions'],'Не разобраны простые фазовые нули модуля косинуса')
        return certificate(lib,'sequences_at_exceptional_point',dict(branches=task['branches']),
            dict(derivative_at_zero=ZERO,corners='x=2/(2k+1), k integer'),
            'Разностное отношение в нуле ограничено степенью |h| с положительным порядком.',
            'Простые нули внутреннего косинуса дают углы, потому что амплитуда там ненулевая. Эти точки сгущаются к нулю.')
    require(wave[0]=='sin' and wave[1][0]=='div' and wave[1][1]==ONE,'Требуется обратная степенная фаза')
    phase=wave[1][2]
    if phase==v:
        if pure:
            require(amp==('pow',v,2) and not name and not task['stated_conditions'],'Не разобрана квадратичная амплитуда')
            d,tree=table(f,x,lib)
            return certificate(lib,'sequences_at_exceptional_point',dict(source=f,assigned_at_zero=ZERO),
                dict(on_punctured_domain=d,derivative_at_zero=ZERO,derivative_continuous=False,cluster_witnesses=(q(-1),ONE)),
                'Разностное отношение в нуле ограничено |h|. В производной вдали от нуля остаётся член −cos(1/x).',
                'Две последовательности с фазами 2kπ и (2k+1)π дают различные предельные значения.',table_steps=tree)
        require(len(name)==1 and amp==('rpow',v,('s',name[0])) and not task['stated_conditions'],'Показатель не связан с исходной степенью')
        thresholds={'classify_continuity_at_point':0,'classify_differentiability_at_point':1,
                    'classify_derivative_continuity_at_point':2}
        threshold=thresholds[kind]
        return certificate(lib,'sequences_at_exceptional_point',dict(source=f,power_convention='real power on every side where defined'),
            dict(iff=f'{name[0]}>{threshold}',left_side_requires_real_power=True),
            'Для нужного свойства сравнить амплитуду, разностное отношение или производную с соответствующей степенью.',
            'При положительном порядке сжатие даёт нуль. При неположительном порядке выбрать последовательности постоянных фаз.',
            'Левая сторона предъявляется отдельно только при допустимости действительной исходной степени.')
    require(len(name)==2 and amp==('rpow',absx,('s',name[0])) and phase==('rpow',absx,('s',name[1]))
            and task['stated_conditions']==[name[1]+'>0'] and kind in ('classify_bounded_derivative_near_point','classify_unbounded_derivative_near_point'),
            'Не разобраны оба вещественных показателя затухающей амплитуды и растущей фазы')
    n,p=name;bounded=kind.startswith('classify_bounded')
    return certificate(lib,'sequences_at_exceptional_point',dict(source=f,conditions=task['stated_conditions']),
        dict(iff=n+('>=' if bounded else '<')+p+'+1',scope='punctured neighborhood',finite_derivative_at_zero_iff=n+'>1'),
        'После цепного правила порядки двух слагаемых производной равны n−1 и n−m−1.',
        'При n≥m+1 оба слагаемых ограничены. Иначе выбрать постоянные косинусные фазы с исчезающим синусом.')


def vertical_tangents(task,lib):
    from verify import same_value
    contract(task,{'function'},['all_vertical_tangent_points'])
    x=task['variable'];v=('v',x);raw=m.parse(task['function'],x)
    entries=[e for e in raw[1:] if isinstance(e,tuple) and e[0]=='cbrt' and e[1][0] in ('sin','cos')]
    require(raw[0]=='add' and len(entries)==1,'Ожидается одна действительная корневая волна плюс гладкое слагаемое')
    wave,=entries;regular=next(e for e in raw[1:] if e!=wave)
    p,d=poly.rf(wave[1][1],x);require(len(p)==2 and len(d)==1 and not domain_conditions(regular,True),'Фаза должна быть аффинной, гладкое слагаемое должно иметь полную область')
    a,b=p[1]/d[0],p[0]/d[0];phase='k*pi' if wave[1][0]=='sin' else '(k+1/2)*pi'
    z=f'({phase}-({b}))/({a})';s=source(regular)
    return certificate(lib,'simple_phase_root_slopes',dict(source=raw,affine_phase=(q(a),q(b)),index_domain='all integers'),
        dict(abscissas=z,ordinates=dict(formula=s,at=z),line='vertical at each abscissa'),
        'На всех указанных уровнях тригонометрический аргумент имеет простой нуль.',
        'Кубический корень даёт по обе стороны один знак отношения и рост как |h|^(−2/3), гладкое слагаемое имеет конечный наклон.',
        'В остальных точках применяется обычная таблица.')

def glued_derivative(task,lib):
    contract(task,{'pieces','hypothesis','left','right','between','domain','outer','inner'})
    if 'pieces' in task:
        (lo,f),(hi,g)=task['pieces']
        cut=re.fullmatch(rf'({NAME})<=({NAME})',lo);require(cut and hi==f'{cut[1]}>{cut[2]}','Точки стыка и принадлежность границы должны совпадать')
        x,z=cut.groups();slope=re.fullmatch(r'([A-Za-z])\*?'+x+r'\+('+NAME+r')',g)
        require(slope and len({x,z,*slope.groups()})==4 and not set(task)&{'left','right','between','domain','outer','inner'},
                'Правая ветвь должна быть одной аффинной функцией с двумя неизвестными')
        a,b=slope.groups();u=('v',x);p=('s',z)
        if 'hypothesis' in task:
            fn=re.fullmatch(rf'({NAME})\({x}\)',f)
            require(fn and task['hypothesis']==f'{fn[1]} left-differentiable at {z}','Левая производная должна существовать в точке стыка')
            value=(fn[1],p);derivative=('left_derivative_at_unknown',fn[1],p)
        else:
            f=m.parse(f.replace('²','^2'),x)
            require(not domain_conditions(f,True),'Не установлено значение и наклон левой ветви в произвольной точке стыка')
            value=m.substitute(f,{u:p});derivative=m.substitute(table(f,x,lib)[0],{u:p})
        params={a:derivative,b:m.add(value,m.neg(m.mul(p,derivative)))}
        return certificate(lib,'match_values_and_slopes',dict(point=p,left_value=value,left_derivative=derivative),
            dict(coefficients=params),'Равенство наклонов определяет коэффициент при x. Равенство значений определяет свободный член.')
    if 'between' in task:
        require((task.get('left'),task.get('right'),task.get('between'),task.get('domain'))==
           ('k1*(x-a), x<a','k2*(x-b), x>b','A*(x-a)*(x-b)*(x-c), a<=x<=b','a<b') and not set(task)&{'outer','inner','hypothesis'},
           'Форма вставки и обе полупрямые должны быть точно связаны')
        value=dict(nonzero_slope_sum=dict(A='(k1+k2)/(b-a)^2',c='(b*k1+a*k2)/(k1+k2)'),
                   both_slopes_zero=dict(A=ZERO,c='arbitrary'),opposite_nonzero_slopes='no solution of the prescribed form')
        return certificate(lib,'match_values_and_slopes',dict(derivative_equations=('k1=A(b-a)(c-a)','k2=A(b-a)(b-c)')),value,
            'Факторизация гарантирует совпадение значений на обоих концах. Из наклонов получаем два линейных уравнения для A и Ac.',
            'При k1+k2=0 исходная параметризация не допускает деления. Ненулевой противоположный наклон потребовал бы квадратичной вставки вне заданного семейства.')
    require(task.get('outer')=='m^2/abs(x), abs(x)>c' and task.get('inner')=='a+b*x^2, abs(x)<=c'
            and not set(task)&{'left','right','domain','hypothesis'},'Не связаны обе внешние ветви и чётная вставка')
    return certificate(lib,'match_values_and_slopes',dict(conditions='c>0',equations=('a+bc²=m²/c','2bc=−m²/c²')),
        dict(positive_c=dict(a='3m²/(2c)',b='−m²/(2c³)'),zero_c='smooth iff m=a=0, b arbitrary'),
        'Сначала приравнять значение и наклон при c. Чётность даёт нужные условия при −c.')


def differentiate_glued(task,lib):
    from scalar_proofs import global_guard
    from tasks import known_guard
    from verify import same_value
    contract(task,{'branches'},['finite_derivative','natural_domain_and_boundary_notes'],params=True)
    x=task['variable'];v=('v',x);a,b=task['branches']
    require(set(a)==set(b)=={'condition','function'},'Нужны ровно две исходные ветви и их области')
    if ' outside [' in b['condition']:
        match_=re.fullmatch(r'(\w+)<=('+x+r')<=(\w+)',a['condition'])
        require(match_ and task['parameters']==[match_[1],match_[3]] and
                b['condition']==f'{x} outside [{match_[1]},{match_[3]}]' and b['function']=='0',
                'Открытая внешняя область или два конца сегмента расходятся')
        p,qname=task['parameters'];f=m.parse(a['function'],x,[p,qname])
        require(not domain_conditions(f,True),'Внутренняя ветвь должна быть гладкой в обоих концах')
        df,tree=table(f,x,lib)
        require(all(same_value(m.substitute(e,{v:('s',z)}),ZERO) for z in (p,qname) for e in (f,df)),
                'Значения и наклоны внутренней ветви в двух концах должны быть нулевые')
        return certificate(lib,'match_values_and_slopes',dict(branches=task['branches'],ordered_segment=(p,qname)),
            dict(inside=df,outside=ZERO,joints=ZERO),
            'Производная внутренней ветви существует до обоих концов. При подстановке в каждом конце её значение и значение самой функции равны нулю.',
            'Снаружи функция нулевая. Значения и оба наклона на каждом стыке совпадают.',table_steps=tree)
    cut=re.fullmatch(r'abs\('+x+r'\)<=([0-9]+(?:/[0-9]+)?)',a['condition'])
    require(cut and b['condition']==f'abs({x})>{cut[1]}' and not task['parameters'],'Не связана симметричная центральная область')
    r=Fraction(cut[1]);require(r>0,'Требуется невырожденный центральный отрезок')
    f=m.parse(a['function'],x);g=m.parse(b['function'].replace('sgn(','sign('),x,extra_functions={'sign'})
    ctx=m.context(dict(variable=x));ends=[];regular=[]
    for z in (-r,r):
        sg=q(1 if z>0 else -1);p=q(z);mapping={v:p}
        exterior=m.substitute(g,{('sign',v):sg})
        require(not any(t[0]=='sign' for _,t in expression_positions(exterior)) and
                all(known_guard((k,m.substitute(u,mapping)),ctx) for e in (f,exterior) for k,u in domain_conditions(e,True)),
                'Обе формулы должны иметь гладкие продолжения к своей граничной точке')
        in_at,out_at=(m.simplify(m.substitute(e,mapping)) for e in (f,exterior))
        in_d,out_d=(table(e,x,lib)[0] for e in (f,exterior))
        regular.append(out_d);d=m.sign(m.add(out_at,m.neg(in_at)),ctx)
        require(d in (-1,0,1),'Знак скачка между исходным значением и внешним следом не установлен')
        outward=m.simplify(m.substitute(out_d,mapping)) if d==0 else ('+inf' if d*int(m.num(sg))>0 else '-inf')
        inward=m.simplify(m.substitute(in_d,mapping))
        ends.append(dict(point=p,left=outward if z<0 else inward,right=inward if z<0 else outward,continuous=d==0))
    require(all(global_guard(g,x,ctx) for e in (f,m.substitute(g,{('sign',v):ONE}),m.substitute(g,{('sign',v):q(-1)}))
                for g in domain_conditions(e,True)),
            'Среди открытых частей есть дополнительные особые точки')
    return certificate(lib,'match_values_and_slopes',dict(branches=task['branches'],center=(q(-r),q(r))),
        dict(left=regular[0],center=in_d,right=regular[1],joints=ends),
        'На каждой внешней полуоси знак постоянен. У каждого стыка сначала сравнить фактическое центральное значение с внешним следом.',
        'При скачке разностное отношение получает бесконечный знак, а при равенстве значений сравниваются обычные производные гладких продолжений.')


def reciprocal_phase_sides(task,lib):
    want=['left_derivative_function','right_derivative_function','finite_infinite_and_domain_statuses']
    contract(task,{'branches'},want)
    x=task['variable'];v=('v',x);a,b=task['branches'];f=m.parse(a['function'],x)
    require(a['condition']==x+'!=0' and b==dict(condition=x+'=0',function='0') and f[0]=='mul' and f[1]==v
            and f[2][0]=='abs' and f[2][1][0]=='cos' and f[2][1][1][0]=='div' and f[2][1][1][2]==v,
            'Нужна обратная косинусная фаза с амплитудой x и нулём в исходной точке')
    c=f[2][1][1][1];s=m.sign(c,m.context(dict(variable=x)))
    require(s in (-1,1) and not m.variable_in(c),'Коэффициент фазы должен быть постоянным и ненулевым')
    d,tree=table(f,x,lib)
    return certificate(lib,'sequences_at_exceptional_point',dict(source=f,original_domain='real line'),
        dict(regular=d,zero_both_sides='does not exist, subsequences 0 and 1',
             corners='x=c/((k+1/2)*pi), k integer',corner_left='-abs(c)/x',corner_right='abs(c)/x'),
        'В нуле исходное разностное отношение равно модулю косинуса. На обеих сторонах имеются постоянные фазовые последовательности со значениями 0 и 1.',
        'На каждом ненулевом прообразе нечётной полупериодической фазы простота нуля даёт противоположные наклоны модуля.',table_steps=tree)


WITNESSES={
    ('sum','neither differentiable'):(('abs(h)','-abs(h)','0'),('abs(h)','abs(h)','2*abs(h)')),
    ('product','f differentiable, g nondifferentiable; example x and |x| at 0'):(('h','abs(h)','h*abs(h)'),('1','abs(h)','abs(h)')),
    ('product','neither differentiable; example |x|,|x| at 0'):(('abs(h)','abs(h)','h^2'),('1+abs(h)','1+abs(h)','(1+abs(h))^2')),
    ('composition','outer differentiable at g(x0), inner not; f=x²,g=|x|,x0=0'):(('h^2','abs(h)','h^2'),('h','abs(h)','abs(h)')),
    ('composition','outer not differentiable, inner differentiable; f=|x|,g=x²,x0=0'):(('abs(h)','h^2','h^2'),('abs(h)','h','abs(h)')),
    ('composition','neither differentiable; f=2x+|x|,g=2x/3-|x|/3,x0=0'):(('2*h+abs(h)','(2*h-abs(h))/3','h'),('abs(h)','abs(h)','abs(h)')),
}


def derivative_witness(task,lib):
    if task['kind']=='differentiate_inequality_counterexample':
        contract(task,set())
        return certificate(lib,'derivative_closure_witnesses',dict(interval='(-pi/2,pi/2)'),dict(preserved=False,example=('sin(x)','2')),
            'На всём интервале sin x<2, однако cos x>0 и производная постоянной равна нулю.')
    contract(task,{'operation','hypotheses_and_example'})
    key=task['operation'],task['hypotheses_and_example']
    if key==('sum','f differentiable, g not differentiable'):
        return certificate(lib,'derivative_closure_witnesses',dict(operation='sum',differentiable_operands=(True,False)),
            dict(necessarily_nondifferentiable=True),'Если сумма дифференцируема, вычесть дифференцируемое слагаемое. Получается противоречие.')
    examples=WITNESSES.get(key);require(examples,'Не установлен полный набор гипотез или примеров')
    # Use the exact one-sided germ builder to verify the open examples, not trial numerical points.
    from verify import same_value
    ctx=m.context(dict(variable='h'));out=[]
    for f,g,target in examples:
        exprs=[m.parse(e,'h') for e in (f,g,target)]
        def signed(e,side):
            h=('v','h')
            # Each witness has a known sign partition on the two rays near zero.
            def replace(u):
                if u[0] not in ('pow','add','mul','div','abs'):return u
                if u[0]=='abs':
                    arg=replace(u[1]);at=m.simplify(m.substitute(arg,{h:q(1 if side=='right' else -1)}))
                    return arg if m.sign(at,ctx) in (0,1) else m.neg(arg)
                return (u[0],*(replace(t) if isinstance(t,tuple) else t for t in u[1:]))
            return replace(e)
        sides=[]
        for side in ('left','right'):
            u,v,target_=(signed(a,side) for a in exprs);h=('v','h')
            if key[0]=='composition':
                v_at=m.simplify(m.substitute(v,{h:q(1 if side=='right' else -1)}))
                outer=signed(exprs[0],'right' if m.sign(v_at,ctx) in (0,1) else 'left')
                actual=m.substitute(outer,{h:v})
            else:actual=m.add(u,v) if key[0]=='sum' else m.mul(u,v)
            require(same_value(actual,target_),'Исходный пример не равен проверяемому выражению на своей стороне')
            traces=[]
            for e in (u,v,target_):
                p,d=poly.rf(e,'h');require(len(d)==1,'Требуются полиномиальные свидетели')
                traces.append(q(p[1]/d[0]) if len(p)>1 else ZERO)
            sides.append(tuple(traces))
        out.append(dict(functions=(f,g),result=target,left=sides[0],right=sides[1]))
    require(out[0]['left'][2]==out[0]['right'][2] and out[1]['left'][2]!=out[1]['right'][2],'Примеры должны дать противоположные случаи')
    return certificate(lib,'derivative_closure_witnesses',dict(operation=key[0],source_hypotheses=key[1]),
        dict(necessarily_nondifferentiable=False,witnesses=out),
        'Разбить исходные примеры по знаку приращения около рассматриваемой точки. Проверить значение операции и оба наклона на каждой стороне.')


def finite_sum_derivative(task,lib):
    contract(task,{'sum','sums','hint','given'})
    sums=task.get('sums');term=task.get('sum');hint=task.get('hint')
    require((sums is None)!=(term is None) and hint in (None,'differentiate sum sinh(kx)','differentiate x+x²+...+x^n'),
            'Не связаны обе нужные суммы и печатное указание')
    if sums==['sum_(k=1)^n k*x^(k-1)','sum_(k=1)^n k²*x^(k-1)'] and 'given' not in task:
        out=dict(P='(1-(n+1)*x^n+n*x^(n+1))/(1-x)^2',
                 Q='((1+x)-(n+1)^2*x^n+(2*n^2+2*n-1)*x^(n+1)-n^2*x^(n+2))/(1-x)^3',
                 at_one=('n(n+1)/2','n(n+1)(2n+1)/6'))
        return certificate(lib,'differentiate_generating_sum',dict(integer_bound='n>=1',generator='sum x^k'),
            out,'Найти конечную геометрическую сумму, взять её производную P, затем (xP)′.',
            'В x=1 подставить в исходные конечные суммы, чтобы не создавать прокол.')
    if (sums==['sum_(k=1)^n sin(k*x)','sum_(k=1)^n k*cos(k*x)'] or term=='sum_(k=1)^n k*cosh(k*x)') and 'given' not in task:
        periodic=sums is not None;op='sin' if periodic else 'sinh';x='x';params=['n']
        form=f'{op}(n*x/2)*{op}((n+1)*x/2)/{op}(x/2)'
        generator=m.parse(form,x,params);d,tree=table(generator,x,lib)
        boundary='x=2*pi*k' if periodic else 'x=0'
        val=dict(derivative=d,boundary=boundary,derivative_on_boundary='n(n+1)/2')
        if periodic:val.update(sum=generator,sum_on_boundary=ZERO)
        return certificate(lib,'differentiate_generating_sum',dict(integer_bound='n>=1',generator=form),val,
            'Из конечной геометрической суммы получить формулу генератора и продифференцировать почленно.',
            'На исключённых точках вычислить исходные суммы отдельно.',table_steps=tree)
    require(term=='sum_(k=1)^n tan(x/2^k)/2^k' and task.get('given')=='product_(k=1)^n cos(x/2^k)=sin(x)/(2^n*sin(x/2^n))',
            'Указанное тождество конечного произведения не связано с суммой')
    return certificate(lib,'differentiate_generating_sum',dict(integer_bound='n>=1',given=task['given']),
        dict(formula='2^(-n)*cot(x/2^n)-cot(x)',on_regular_domain='x not in pi*Z',
             removable_formula_exceptions='x in 2^n*pi*Z, original value 0',
             original_poles='all other x in pi*Z'),
        'Проделать логарифмическое дифференцирование данного произведения на области ненулевых факторов.',
        'В кратных 2^nπ все исходные тангенсы равны нулю. Остальные кратные π исключены полюсами.')


def angular_boundaries(raw,x,lib):
    """Bind all singular levels of folds of a smooth polynomial phase."""
    def chart(e):
        op=e[0]
        if op not in ('asin','acos','abs','sqrt'):return None
        u=e[1];j=1
        if u[0]=='pow' and u[2]>0:u,j=u[1:]
        if u[0] in ('sin','cos'):
            phase=u[1];name=u[0]
            if op=='sqrt' and j==1:
                return dict(phase=phase,levels='k*pi' if name=='sin' else '(k+1/2)*pi',
                            source_access=f'{name}(phase)>=0',profile=f'sqrt({name}(phase))',
                            ordinary_rule='square root of the first nonzero allowed phase term divided by h')
            if op=='abs':
                return dict(phase=phase,levels='k*pi' if name=='sin' else '(k+1/2)*pi',
                            profile='|factor * phase increment|^power',power=j,
                            ordinary_rule='zero derivative if phase slope vanishes or power>1')
            if j==1 or j==2 and op=='acos':
                return dict(phase=phase,levels='(k+1/2)*pi' if name=='sin' else 'k*pi',
                            profile='angle value plus signed local absolute phase increment',
                            abs_factor='1' if j==1 else 'sqrt(2)',
                            sign_relative_to_outer_endpoint='negative for a local maximum, positive for local minimum',
                            ordinary_rule='zero derivative exactly when phase slope vanishes')
        if op in ('asin','acos') and u[0]=='add':
            for a,b in (u[1:],u[:0:-1]):
                if a[0]=='sin' and b==('mul',q(-1),('cos',a[1])) and j==1:
                    return dict(phase=a[1],levels='k*pi/2',source_access='sin(2*phase)>=0',
                                profile='signed sqrt(2*(1-abs(sin(phase)-cos(phase))))',outer=op,
                                value_at_folds='principal inverse at sin(phase)-cos(phase)=±1',
                                ordinary_rule='each available side uses the first nonzero polynomial phase term',
                                sign='asin: −sign(u_endpoint), acos: sign(u_endpoint)')
        return None
    parts=[raw] if raw[0]!='add' else raw[1:];charts=[chart(e) for e in parts]
    if not all(charts):return None
    for row in charts:
        phase=row['phase'];p,d=poly.rf(phase,x)
        if len(p)<2 or len(d)!=1 or domain_conditions(phase):return None
        row['polynomial_phase_coefficients']=tuple(q(c/d[0]) for c in p)
        row['slope']=table(phase,x,lib)[0]
        if 'source_access' in row:
            degree=len(p)-1
            row['relative_side_rule']=('Взять первый ненулевой член c*h^r приращения фазы. Сохранить стороны, '
                                       'где условие source_access выполняется независимо от значения в точке.')
            row['derivative_magnitude']=('sqrt(abs(c))*|h|^(r/2−1)' if row['profile'].startswith('sqrt')
                                         else 'sqrt(2*abs(c))*|h|^(r/2−1)',degree)
    require(len(charts)==1 or all(row['phase']==charts[0]['phase'] for row in charts) and
            len({row['levels'] for row in charts})==len(charts) and all('source_access' not in row for row in charts),
            'Совпадающие фазовые границы требуют общего сложения односторонних следов')
    return charts



def derivative_reading_branches(task,lib,request):
    if not lib.data.get('derivative_reading_branches'):
        raise Unsupported('The verified notation-branch transition is unavailable')
    src=task.get('source',{})
    if (set(task)-{'kind','id','source','printed_denominator','variable','source_readings','requested_output'}
            or not isinstance(src,dict)
            or set(src)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement','original_page_image_sha256'}
            or task.get('requested_output')!=['differentiate_source_expression']):
        raise Unsupported('The source interpretation set and complete derivative goal are required')
    sup='¹²³⁴⁵⁶⁷⁸⁹'
    parsed=re.fullmatch(fr'(arccos|arcsin|arctg)([{sup}]+)\(([A-Za-z]\w*)\)([{sup}]+)',task['printed_denominator'])
    if not parsed or parsed[3]!=task['variable']:
        raise Unsupported('The raised powers and the original argument must be bound')
    op,alpha,x,beta=parsed.groups()
    f={'arccos':'acos','arcsin':'asin','arctg':'atan'}[op]
    decode=str.maketrans(sup,'123456789')
    power,inner=[int(row.translate(decode)) for row in (alpha,beta)]
    if power<2 or inner<2:raise Unsupported('Distinct placements of two nontrivial powers are needed')
    expected=[f'1/({f}({x}^{inner})^{power})',f'1/({f}({x})^{power*inner})']
    readings=task.get('source_readings',[])
    if len(readings)!=2 or {m.parse(v,x) for v in readings}!={m.parse(v,x) for v in expected}:
        raise Unsupported('The interpretations must match the two positions of the printed powers')
    cases=[]
    for v in expected:
        child=dict(kind='differentiate',function=v,variable=x,
                   requested_output=['finite_derivative','natural_domain_and_boundary_notes'])
        p=request('differentiate each verified reading on its own domain',child)
        if p.get('status')!='SOLVED' or p.get('verification',{}).get('complete') is not True:
            raise Unsupported('A reading still needs its full natural domain and one-sided edges')
        c=p['compilation']
        cases.append(dict(reading=v,derivative=p['value'],smooth_domain=c.get('smooth_domain'),
                          original_real_domain=c.get('real_domain',c.get('natural_domain')),
                          exceptional_points=c.get('exceptional_points',[])))
    return dict(theorem='method.derivative_reading_branches',argument=[
        'Две верхние степени допускают чтение со степенью аргумента и чтение с двумя степенями внешней функции.',
        'Проверяем обе соответствующие записи. Для каждой отдельно доказываем производную, исходную область и поведение на её включённых краях.'
    ],printed=task['printed_denominator']),dict(interpreted_derivatives=cases)


def derivative_proof(task,lib,request):
    try:
        kind=task['kind']
        if kind=='ambiguous_elementary_derivative':return derivative_reading_branches(task,lib,request)
        if higher_routing(task,kind):return higher_derivative_goal(task,lib,request)
        if mvt_routing(task,kind):return mvt_goal(task,lib)
        if local_geometry_routing(task,kind):return local_geometry_goal(task,lib,request)
        if kind=='differentiate' and 'branches' in task:return differentiate_glued(task,lib)
        if kind=='one_sided_derivative_functions' and 'branches' in task:return reciprocal_phase_sides(task,lib)
        if kind in ('differentiate','investigate_differentiability','global_one_sided_derivatives') or (
                kind=='one_sided_derivative_functions' and task['function'].startswith('sqrt(')):
            return complete_table(task,lib)
        if kind=='differentiate_by_substitution':return substitute_outer(task,lib,request)
        if kind=='differentiate_functional':return functional_derivative(task,lib)
        if kind in ('differentiate_floor_expression','one_sided_derivative_functions'):return floor_derivative(task,lib)
        if kind=='differentiable_gluing':return glued_derivative(task,lib)
        if kind in ('differentiate_inequality_counterexample','derivative_closure_counterexample'):return derivative_witness(task,lib)
        if kind=='differentiate_finite_sum':return finite_sum_derivative(task,lib)
        if kind=='vertical_tangent_points':return vertical_tangents(task,lib)
        if kind.startswith('classify_') or kind in ('prove_derivative_discontinuity','prove_differentiability_and_accumulating_corners'):
            if kind!='construct_continuous_function_with_prescribed_corners':return oscillatory_source(task,lib)
        if kind=='construct_continuous_function_with_prescribed_corners':
            contract(task,{'given_points'},['example_function','continuity_proof','nondifferentiability_at_each_given_point'],
                     ('construct_and_prove',),params=True)
            a=re.fullmatch(r'(\w+)\[1\],\.\.\.,\1\[(\w+)\]',task['given_points'])
            require(a and task['parameters']==[dict(symbol=a[2],domain='positive_integer'),dict(symbol=a[1],domain='indexed_real_family')],
                    'Не связана конечная индексированная семья точек угла')
            return certificate(lib,'simple_phase_root_slopes',dict(points=task['given_points']),
                dict(construction=f'sum abs(x-{a[1]}[j]), j=1..{a[2]}'),
                'Конечная сумма непрерывна. В заданной точке каждое совпадающее слагаемое увеличивает скачок наклона на два, остальные дают одинаковые производные с обеих сторон.')
        if kind in ('abstract_difference_quotient_limit','sequential_derivative_characterization','derivative_at_discontinuity',
                    'derivative_periodicity_proof','derivative_symmetry_proof','derivative_at_from_continuous_factor',
                    'prove_derivative_nonexistence_and_one_sided_values'):return quotient_principles(task,lib)
        return derivative_algebra(task,lib)
    except (poly.NotRational,poly.Undefined) as exc:
        raise Unsupported('Исходное условие требует другой точной алгебраической ветви') from exc


ORDER_WORDS={'n','n>=1','positive integer n','arbitrary positive integer n'}
HIGHER_SOURCE_FIELDS={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256',
            'page_png_sha256','literal_requirement','printed_hint','printed_occurrence','printed_occurrences',
            'notation_review','printed_instruction','section','source_issue','printed_goal','requested_operator'}
HIGHER_HEADINGS={
    'symbolic_order_derivative':{'Найти производную n-го порядка.','Найти y^(n).','Найти P^(n)(x).'},
    'symbolic_order_derivative_identity':{'Доказать тождество для производной порядка n.',
        'Доказать равенство, применяя метод математической индукции согласно указанию.','Доказать формулу.',
        'Используя данное комплексное разложение, доказать формулу n-й производной.'},
    'symbolic_trigonometric_polynomial_derivative':{'Преобразовать sin^(2p)(x) в сумму A_k cos(2kx) и найти f^(n).',
        'Найти производную n-го порядка.','Найти f^(n)(x).','Найти f^(n) при целом положительном p (см. предыдущую задачу).'},
}
HIGHER_KINDS=frozenset({'higher_chain_rule_proof','symbolic_trigonometric_polynomial_derivative',
    'symbolic_order_derivative_identity','orthogonal_polynomial_ode','orthogonal_polynomial_formula_and_ode',
    'symbolic_higher_composition_proof','differential_operator_shift','euler_operator_variable_change',
    'inverse_function_higher_derivatives','parametric_derivatives_from_successive_differentials',
    'piecewise_jet_matching','rectilinear_motion_from_position','order_of_differentiability'})
RATIONAL_FORMULA=re.compile(r'[0-9x+\-*/^().\s]+')


def higher_packet(task,fields,*,literal=None,source_hints=()):
    meta=task.get('source',{});kind=task['kind']
    permitted=HIGHER_HEADINGS.get(kind,()) if literal is None else ({literal} if isinstance(literal,str) else literal)
    require(isinstance(meta,dict) and not set(meta)-HIGHER_SOURCE_FIELDS and
            not set(task)-({'kind','id','source','schema','transcription'}|set(fields)) and
            meta.get('literal_requirement') in (None,*permitted) and meta.get('printed_hint') in (None,*source_hints),
            'Не связано полное условие, печатная формула или указание о способе')
    return meta


def higher_certificate(lib,method,scope,value,*argument,**proof):
    require(method in lib.data.get('higher_derivative_transitions',()),'Не объявлен общий переход для высшей производной')
    return dict(theorem='higher_derivative.'+method,scope=scope,argument=argument,**proof),value


def higher_routing(task,kind):
    if kind in HIGHER_KINDS or scale_routing(task,kind) or remaining_derivative_head(task,kind):return True
    if kind=='symbolic_order_point_derivative':return 'hypothesis' in task
    if kind=='symbolic_order_derivative':
        text=task.get('function','')
        if not isinstance(text,str) or not isinstance(task.get('source',{}),dict):return False
        hypothesis=task.get('hypothesis')
        return bool(task.get('source',{}).get('printed_hint')=='Разложить функцию на простейшие дроби.'
                    or isinstance(hypothesis,str) and hypothesis.endswith(' is any polynomial') or '...' in text
                    or exponential_wave_candidate(text)
                    or task.get('variable')=='x' and '/' in text and RATIONAL_FORMULA.fullmatch(text))
    if kind=='composite_function_differentiation':
        args=task.get('inner_arguments')
        return task.get('requested_output')==['second_differential'] and isinstance(args,dict) and len(args)==2 and bool(task.get('parameters'))
    if kind=='parametric_curve_derivatives':
        coords=task.get('coordinates')
        return isinstance(coords,list) and any(s.startswith('diff(') for s in coords if isinstance(s,str))
    return (kind=='mathematical_question' and task.get('requested_output')==['all derivative orders at zero']
            and isinstance(task.get('off_zero'),str))


def nth_polynomial_or_rational(task,lib):
    origin=higher_packet(task,{'function','variable','order','hypothesis'},source_hints=('Разложить функцию на простейшие дроби.',))
    text=task['function'];x=task['variable'];v=('v',x)
    require(task.get('order') in ORDER_WORDS and re.fullmatch(NAME,x) and x!='n','Общий порядок должен быть натуральным')
    if origin.get('printed_hint') or x=='x' and '/' in text and RATIONAL_FORMULA.fullmatch(text):
        require('hypothesis' not in task,'Для дроби не должны добавляться невыведенные гипотезы')
        raw=m.parse(text,x);p,d=poly.rf(raw,x);g=poly.pgcd(p,d)
        p,d=poly.pdiv(p,g)[0],poly.pdiv(d,g)[0]
        quotient,rem=poly.pdiv(p,d)
        from graphs import rational_roots
        from tasks import _fraction_weights
        poles=[];remaining=d
        for root in rational_roots(d):
            require(not root.b,'Для простейшей дроби требуется точное разложение на рациональные полюса')
            factor=(-root.a,Fraction(1));order=0
            while len(remaining)>1:
                v2,remainder=poly.pdiv(remaining,factor)
                if any(remainder):break
                remaining=v2;order+=1;poles.append((root.a,order,poly.pdiv(d,poly.pp(factor,order))[0]))
        require(len(remaining)==1 and poles,'Полное разложение знаменателя на линейные множители пока открыто')
        weights=_fraction_weights(rem,poles)
        require(weights is not None,'Сумма выбранных простейших дробей не восстановила точный числитель')
        terms=[dict(pole=q(a),order=k,weight=q(w)) for w,(a,k,_) in zip(weights,poles) if w]
        return higher_certificate(lib,'differentiate_partial_fractions',dict(original=m.parse(text,x),raw_guards=domain_conditions(raw),order='positive integer n'),
            dict(polynomial=tuple(map(q,quotient)),partial_fractions=terms,
                 nth_pole_factor='(-1)^n * (k+n-1)!/(k-1)! * (x-a)^(-k-n)'),
            'Выполнить требуемое разложение. Каждая дробь проверена по общему знаменателю.',
            'Применить проверяемую рекурсию производной обратной степени. Для полиномиальной части действует обычный падающий факториал.')
    require('printed_hint' not in origin,'Неизвестное указание для полиномиальной формулы')
    if 'hypothesis' in task:
        match_=re.fullmatch(rf'exp\(({NAME})\*{x}\)\*({NAME})\({x}\)',text)
        if not match_:
            back=re.fullmatch(rf'({NAME})\({x}\)\*exp\(({NAME})\*{x}\)',text)
            a,P=(back[2],back[1]) if back else (None,None)
        else:a,P=match_.groups()
        require(a and len({a,P,x,'n'})==4 and task['hypothesis']==f'{P} is any polynomial','Не связаны постоянная экспоненты и произвольный многочлен')
        exp=('exp',('mul',('s',a),v));d,derivation=table(exp,x,lib)
        require(same_value(d,m.mul(('s',a),exp)),'Первый шаг экспоненциального ядра не прошёл проверку')
        return higher_certificate(lib,'symbolic_leibniz',dict(variable=x,polynomial=P,exponential_rate=a,order='positive integer n'),
            dict(formula=f'exp({a}*{x}) * sum_(j=0)^min(n,deg({P})) binomial(n,j)*{a}^(n-j)*D^j {P}({x})',
                 zero_rate=f'D^n {P}({x}) when {a}=0'),
            'Первый шаг экспоненциального ядра проверен таблицей. При повторении он вносит одну степень постоянной.',
            'Правило Лейбница и тождество Паскаля дают коэффициенты для всех порядков. Производные полинома выше его степени исчезают.',
            kernel_table=derivation)
    match_=re.fullmatch(rf'({NAME})0\*{x}\^n\+\1(?:1|\[1\])\*{x}\^\(n-1\)\+\.\.\.\+\1n',text)
    require(match_,'Многочлен должен быть связан с семейством коэффициентов и тем же максимальным порядком')
    c=match_[1]
    return higher_certificate(lib,'symbolic_leibniz',dict(variable=x,order='positive integer n',coefficient_family=c),
        dict(formula=f'n!*{c}0'),
        'Производная степени j за j шагов даёт j!, следующий шаг её обнуляет. В степени n остаётся ровно ведущий член.')


def inverse_or_differential(task,lib):
    kind=task['kind'];extra={'requested_output'}
    if kind=='inverse_function_higher_derivatives':
        higher_packet(task,{'relation'}|extra,literal='Find the first four derivatives of the inverse to a sufficiently differentiable function, assuming those derivatives exist.')
        rel=re.fullmatch(rf'({NAME})=({NAME})\(({NAME})\)',task['relation'])
        require(rel and len(set(rel.groups()))==3 and task['requested_output']==['inverse derivatives of orders 1,2,3,4'],
                'Нужны четыре производные именно обратной функции')
        y,f,x=rel.groups()
        # X_j is the j-th derivative of f, differentiation shifts each j.
        d1=('s','p');d2=('s','q');d3=('s','r');d4=('s','s')
        swaps={d1:d2,d2:d3,d3:d4};cur=m.div(ONE,d1);values=[cur];records=[]
        for k in range(3):
            derivative=differentiate_jet(cur,swaps,lib);records.append(derivative)
            cur=m.div(derivative,d1);values.append(cur)
        return higher_certificate(lib,'moving_coordinate_operator',dict(independent=y,original_argument=x,function=f,
              jets=dict(p='f′(x)',q='f″(x)',r='f‴(x)',s='f^(4)(x)'),nonzero_first_derivative=True),
            dict(orders=[1,2,3,4],values=values),
            'Из тождества прямой и обратной функций следует f′(x) не равна нулю при существовании конечной обратной производной.',
            'На каждом шаге применять D_y=(f′(x))^(-1)D_x к предыдущей производной.',
            differentiated_jet_values=records)
    higher_packet(task,{'coordinates','orders'}|extra,literal='Express y″ and y‴ in terms of the successive differentials of x and y, without taking x as the independent variable.')
    require(task['requested_output']==['formulas in successive differentials'] and task['orders']==[2,3] and
            isinstance(task['coordinates'],list) and len(task['coordinates'])==2,'Не связаны обе производные или обе зависимые координаты')
    coords=[re.fullmatch(rf'({NAME})\(({NAME})\)',s) for s in task['coordinates']]
    require(all(coords) and coords[0][2]==coords[1][2] and len({coords[0][1],coords[1][1],coords[0][2]})==3,
            'Две координаты должны зависеть от одного параметра')
    x,y=(c[1] for c in coords)
    names=[tuple(('s',f'd{i}{g}') for i in range(1,4)) for g in (x,y)]
    flow={a:b for j in names for a,b in zip(j,j[1:])};den=names[0][0];rate=m.div(names[1][0],den)
    second=m.div(differentiate_jet(rate,flow,lib),den)
    third=m.div(differentiate_jet(second,flow,lib),den)
    return higher_certificate(lib,'moving_coordinate_operator',dict(coordinates=(x,y),nonzero=den,exterior_parameter=coords[0][2]),
        dict(orders=[2,3],values=(second,third)),
        'Начать с dy/dx. К результату дважды применить оператор d/dx с правилом частного.',
        'При каждом дифференцировании сохранять все последующие дифференциалы обеих зависимых координат.')


def differentiate_jet(term,flow,lib):
    """Take formal d by the same input derivative table and the recorded jet shifts."""
    x='__flow';v=('v',x);bindings={};result_=ZERO
    for i,(u,w) in enumerate(flow.items()):
        others={t:('s',f'__stationary{j}') for j,t in enumerate(flow) if t!=u}
        renamed=m.substitute(term,others|{u:v})
        derivative=table(renamed,x,lib)[0]
        recovered=m.substitute(derivative,{v:u}|{b:a for a,b in others.items()})
        result_=m.add(result_,m.mul(recovered,w))
    return result_


def trig_finite_spectrum(task,lib):
    higher_packet(task,{'function','positive_integer_parameters','required_intermediate','hint'})
    match_=re.fullmatch(rf'(sin|cos)\(({NAME})\)\^\(2\*({NAME})(\+1)?\)',task['function'])
    require(match_,'Требуется синус или косинус в объявленной целой степени')
    mode,x,p,odd=match_.groups();par=task['positive_integer_parameters']
    require(isinstance(par,list) and len(par)==2 and p in par and x not in par and len(set(par))==2,
            'Не связаны порядок и целый показатель')
    n=next(k for k in par if k!=p);power=f'2*{p}'+('+1' if odd else '')
    intermediate=task.get('required_intermediate')
    require(intermediate in (None,f'sum_(k=0)^{p} A_k*cos(2*k*{x})') and
            (not intermediate or mode=='sin' and not odd) and
            task.get('hint') in (None,'sin x=(t-conj(t))/(2i), t=cos x+i sin x; use de Moivre'),
            'Не сохранена точная форма требуемого гармонического разложения')
    u=('v',x);s=('sin',u);c=('cos',u)
    transitions=(table(s,x,lib)[0],table(c,x,lib)[0])
    require(same_value(transitions[0],c) and same_value(transitions[1],m.neg(s)),'Тригонометрический цикл не подтвердился')
    coefficient='binomial(m,j)/(2^m)' if mode=='cos' else '(-1)^j*binomial(m,j)/(2*i)^m'
    value=dict(power=power,finite_modes=dict(index='0<=j<=m',frequency='m-2*j',coefficient=coefficient,
        mode=f'exp(i*(m-2*j)*{x})',nth_multiplier=f'(i*(m-2*j))^{n}'),
        zero_frequency='n>0 annihilates the mode',combine_conjugate_pairs=True)
    if intermediate:
        value['real_cosine_expansion']=dict(constant=f'binomial(2*{p},{p})/2^(2*{p})',
            mode_weight=f'(-1)^k*binomial(2*{p},{p}-k)*2^(1-2*{p})',frequency='2*k',index=f'1<=k<={p}')
    return higher_certificate(lib,'finite_harmonic_differentiation',dict(variable=x,integer_parameters=par,required_intermediate=intermediate),
        value,'Вывести частоты и коэффициенты по биному Ньютона для exp(ix) и exp(−ix).',
        'Проверенный цикл синуса и косинуса замыкается за четыре шага. Для одной частоты шаг даёт её множитель, а весь результат получается конечной суммой.',
        derivative_cycle=transitions)


def symbolic_composition(task,lib):
    kind=task['kind']
    if kind=='higher_chain_rule_proof':
        higher_packet(task,{'function','variable','order','hypothesis','identity'},literal='Доказать формулу n-й производной аффинной композиции.')
        require(task['function']=='f(a*x+b)' and task['variable']=='x' and task['order'] in ORDER_WORDS
                and task['hypothesis']=='f has an n-th derivative' and task['identity']=='D^n f(ax+b)=a^n*f^(n)(ax+b)',
                'Внешняя функция и аффинное отображение не связаны с заявленным порядком')
        return higher_certificate(lib,'successive_chain_coefficients',dict(variable='x',function='f',inner='a*x+b',parameters=['a','b']),
            dict(formula='a^n*f^(n)(a*x+b)'),
            'При дифференцировании одного внешнего коэффициента шаг всегда вносит множитель a.',
            'База и шаг индукции работают также при a=0, когда композиция постоянна.')
    if kind=='symbolic_order_point_derivative':
        higher_packet(task,{'function','point','order','hypothesis'},literal='Найти f^(n)(a) при указанной гладкости φ.')
        require(task['function']=='(x-a)^n*phi(x)' and task['point']=='a' and task.get('order','n') in ORDER_WORDS and
                task['hypothesis']=='phi has a continuous derivative of order n-1 in a neighborhood of a',
                'Требуется точная кратность нулевого множителя и достаточный порядок гладкости')
        return higher_certificate(lib,'successive_chain_coefficients',dict(order='positive integer n',center='a',known_outer_regular_order='n-1'),
            dict(value='n!*phi(a)'),
            'Лейбниц для порядка n−1 даёт первый член n!(x−a)φ(x), у остальных кратность множителя не меньше двух.',
            'Разделить на x−a и взять предел с заданной непрерывностью. Производную n-го порядка у φ не предполагать.')
    higher_packet(task,{'function','assumptions','claim','displayed_terms'},literal={
        'Доказать форму n-й производной композиции с коэффициентами, не зависящими от внешней функции.',
        'Доказать указанную формулу n-й производной f(x²).'})
    f=task['function']
    if f=='y=f(u), u=phi(x)':
        require(task['assumptions']==['f and phi n times differentiable'] and
                task['claim']=='D_x^n y=sum_(k=1)^n A_k(x)*f^(k)(u), coefficients independent of f' and 'displayed_terms' not in task,
                'Не заданы нужные производные внутренней и внешней функций')
        val=dict(coefficient_initial='A[1,1]=phi′',recurrence='A[r+1,k]=D_x A[r,k]+phi′*A[r,k-1]',
                 missing_indices='zero',formula='sum_(k=1)^n A[n,k]*f^(k)(phi(x))')
    else:
        require(f=='f(x^2)' and set(task.keys())&{'assumptions','claim'}==set() and task['displayed_terms']==[
            '(2x)^n*f^(n)(x^2)','n*(n-1)*(2x)^(n-2)*f^(n-1)(x^2)',
            'n*(n-1)*(n-2)*(n-3)/2!*(2x)^(n-4)*f^(n-2)(x^2)','...'],
            'Коэффициенты или внутренняя квадратичная функция отличаются от напечатанных')
        val=dict(formula='sum_(j=0)^floor(n/2) n!/(j!*(n-2*j)!)*(2*x)^(n-2*j)*f^(n-j)(x^2)',
                 combinatorial_term='j choices of h^2 and n-2j choices of 2xh in the ordinary Taylor coefficient')
    return higher_certificate(lib,'successive_chain_coefficients',dict(source=f,order='positive integer n',outer_regular_order='n'),val,
        'Применить производную к коэффициенту и к значению внешней производной. Вторая ветвь повышает индекс внешней производной на один.',
        'Для квадратичной внутренней функции остаются два приращения. Биномиальный выбор их кратностей даёт указанную конечную сумму.')

def exponential_wave_candidate(text):
    return bool(re.search(r'\bexp\s*\(',text) and re.search(r'\b(?:sin|cos)\s*\(',text))


def exponential_wave_order(task,lib):
    """Find the constant two-dimensional derivative operator from the input."""
    x=task.get('variable','x');text=task['function'];order=task.get('order')
    n='n' if isinstance(order,str) and order in ORDER_WORDS else order
    reserved=m.FUNCTIONS|set(m.ALIASES)|{'pi','e'}
    require(isinstance(x,str) and isinstance(n,str) and re.fullmatch(NAME,x) and re.fullmatch(NAME,n)
            and x!=n and not {x,n}&reserved,'Expected a real variable and an independent positive integer order')
    names=set(re.findall(NAME,text))-reserved-{x}
    if n in names:return None
    raw=m.parse(text,x,names)
    if raw[0]!='mul' or {raw[1][0],raw[2][0]} not in ({'exp','sin'},{'exp','cos'}):return None
    amp,wave=raw[1:] if raw[1][0]=='exp' else raw[1:][::-1]
    require(not domain_conditions(raw),'The kernel has restrictions on its original domain')
    a,da=table(amp[1],x,lib);b,db=table(wave[1],x,lib)
    require(not any(m.variable_in(r,x) for r in (a,b)),'Both input phases must be affine')
    v=('v',x);zero={v:ZERO}
    require(all(same_value(expr,m.add(m.mul(rate,v),m.substitute(expr,zero)))
                for expr,rate in ((amp[1],a),(wave[1],b))),'The affine phase identities did not verify')
    sine=m.mul(amp,('sin',wave[1]));cosine=m.mul(amp,('cos',wave[1]))
    targets=(m.add(m.mul(a,sine),m.mul(b,cosine)),m.add(m.mul(m.neg(b),sine),m.mul(a,cosine)))
    steps=tuple(table(kernel,x,lib) for kernel in (sine,cosine))
    require(all(same_value(got,expected) for (got,_),expected in zip(steps,targets)),
            'The derivative operator on the two original kernels did not verify')
    nonzero=m.add(m.power(a,2),m.power(b,2));rho=('sqrt',nonzero)
    def permitted(expr):
        guards={'nonzero':(nonzero,rho),'positive':(nonzero,rho),'nonnegative':(nonzero,rho)}
        return all(known_guard((kind,operand),{'assumptions':[],'parameters':names}) or
                   any(same_value(operand,e) for e in guards.get(kind,()))
                   for kind,operand in domain_conditions(expr))
    proposed=task.get('proposed');phase=task.get('phase')
    angle='phi'
    while angle in names|{x,n}:angle+='_'
    if proposed is not None:
        require(isinstance(phase,list) and len(phase)==2 and all(isinstance(s,str) and s.count('=')==1 for s in phase),
                'A proposed phase identity requires both phase equations')
        equations=[s.split('=') for s in phase]
        lhs=[re.fullmatch(rf'(sin|cos)\(\s*({NAME})\s*\)',s.strip()) for s,_ in equations]
        require(all(lhs) and {label[1] for label in lhs}=={'sin','cos'} and lhs[0][2]==lhs[1][2],
                'Sine and cosine have to bind to the same phase')
        angle=lhs[0][2]
        require(angle not in names|{x,n}|reserved and nonzero!=ZERO,'The claimed angle must be new and defined')
        for label,(_,rhs) in zip(lhs,equations):
            expr=m.parse(rhs,x,names)
            require(not m.variable_in(expr,x) and permitted(expr) and
                    same_value(expr,('div',b if label[1]=='sin' else a,rho)),
                    'The supplied phase does not match the computed rates')
    else:
        require(phase is None,'Phase equations without a proposed identity are unsupported')
    exponent=m.div(('s',n),q(2));rotated=m.add(wave[1],m.mul(('s',n),('s',angle)))
    formula=m.mul(m.mul(amp,('rpow',nonzero,exponent)),(wave[0],rotated))
    if proposed is not None:
        candidate=m.parse(proposed,x,names|{n,angle})
        require(permitted(candidate) and same_value(candidate,formula),
                'The proposed power, phase or domain differs from the computed derivative')
    return higher_certificate(lib,'finite_harmonic_differentiation',
        dict(source=raw,variable=x,positive_integer_order=n,nonzero_radius=nonzero,angle=angle,
             phase_cosine=source(('div',a,rho)),phase_sine=source(('div',b,rho))),
        dict(identity=source(formula) if nonzero!=ZERO else '0',
             degenerate_case='Both rates zero: every positive-order derivative is zero, without a phase.'),
        'По таблице производных пара из синуса и косинуса переходит в ту же пару с постоянными коэффициентами.',
        'После деления матрицы на её радиус остаётся поворот. Индукция по порядку складывает углы поворота и умножает радиусы.',
        first_derivative_matrix=((a,b),(m.neg(b),a)),phase_table=(da,db),kernel_table=steps)


def symbolic_identity(task,lib):
    meta=higher_packet(task,{'function','variable','order','proposed','phase','given','hint','claim','domain','C_n','S_n'},
         source_hints=('Применить формулу Муавра.',))
    text=task['function'];x=('v','x')
    if (not set(task)&{'given','claim','domain','C_n','S_n','hint'} and not meta.get('printed_hint')
            and exponential_wave_candidate(text)):
        result=exponential_wave_order(task,lib)
        if result is not None:return result
    require(task.get('variable','x')=='x','The remaining identity requires the displayed variable')
    if 'given' in task:
        require(text=='1/(1+x^2)' and task['given']=='1/(1+x^2)=(1/(x-i)-1/(x+i))/(2*i)' and
                task.get('proposed')=='(-1)^n*n!/(1+x^2)^((n+1)/2)*sin((n+1)*arccot(x))'
                and task.get('hint') in (None,'Применить формулу Муавра.') and not set(task)&{'phase','C_n','S_n','claim','domain'},
                'Простейшие комплексные дроби или главный аргумент не связаны с заявленным тождеством')
        return higher_certificate(lib,'differentiate_partial_fractions',dict(original='1/(1+x^2)',domain='all real x',
                required_decomposition=task['given'],phase='arccot(x) in (0,pi)'),
            dict(identity=task['proposed'],poles=['i','-i']),
            'В заданном разложении общий знаменатель (x−i)(x+i)=1+x², разность числителей равна 2i.',
            'Порядок каждого полюса повысить до n+1 с множителем (−1)^n n!. Фазы двух полюсов сопряжены.',
            'Взять разность полярных степеней по формуле Муавра.')
    seed=re.fullmatch(r'x\^\(n-1\)\*exp\(([^()/]+)/x\)',text)
    if seed:
        c=seed[1]
        require(task.get('order') in ORDER_WORDS and task.get('domain')=='x!=0' and
                task.get('claim')==f'D^n[x^(n-1)*exp({c}/x)]=(-{c})^n*exp({c}/x)/x^(n+1)' and
                not set(task)&{'proposed','phase','hint','C_n','S_n'},
                'Условия полюса или коэффициент индукционной формулы не совпадают')
        names=[c] if re.fullmatch(NAME,c) else []
        phase=m.parse(c,None,names);first=('exp',('div',phase,x))
        actual=table(first,'x',lib)[0];expected=m.div(m.mul(m.neg(phase),first),m.power(x,2))
        require(same_value(actual,expected),'База индукции для экспоненциального полюса не подтвердилась')
        return higher_certificate(lib,'order_recurrence_by_product',dict(domain='x!=0',order='n positive integer',factor=phase),
            dict(identity=task['claim'],initial=actual,recurrence='D^(n+1)(x*g_n)=x*D(D^n g_n)+(n+1)*D^n g_n'),
            'Проверить базу n=1 таблицей. Для перехода выписать однократное дифференцирование D^n g_n.',
            'Из общего Лейбница для x*g_n остаются только два слагаемых. Части с коэффициентом n+1 сокращаются.')
    require(meta.get('literal_requirement')!='Доказать равенство, применяя метод математической индукции согласно указанию.'
            or text=='x^n*ln(x)','Печатное требование индукции не связано с выбранным доказательством')
    if text=='x^n*ln(x)':
        require(task.get('order') in ORDER_WORDS and task.get('domain')=='x>0' and
                task.get('claim')=='n!*(ln(x)+sum_(k=1)^n 1/k)' and
                not set(task)&{'proposed','phase','hint','C_n','S_n'},'Не связаны логарифм, порядок и гармоническая сумма')
        return higher_certificate(lib,'order_recurrence_by_product',dict(domain='x>0',order='n positive integer'),
            dict(identity=task['claim'],seed='ln(x)',harmonic_recurrence='H[n+1]=H[n]+1/(n+1)'),
            'Применить Лейбница к x*(x^n ln x), после n+1 производных остаются два слагаемых.',
            'Производная уже вычисленного n!(ln x+H_n) даёт ровно недостающий член 1/(n+1).')
    require(text=='sin(x)/x' and task.get('order')=='2*n' and task.get('domain')=='x!=0' and
            task.get('claim')=='(2*n)!/x^(2*n+1)*(C_n(x)*sin(x)-S_n(x)*cos(x))' and
            task.get('C_n')=='sum_(j=0)^n (-1)^j*x^(2*j)/(2*j)!' and
            task.get('S_n')=='sum_(j=0)^(n-1) (-1)^j*x^(2*j+1)/(2*j+1)!' and
            not set(task)&{'proposed','phase','hint'},
            'Не связаны обе конечные суммы и чётный запрошенный порядок')
    return higher_certificate(lib,'symbolic_leibniz',dict(domain='x!=0',order='2*n'),
        dict(identity=task['claim'],even_sum=task['C_n'],odd_sum=task['S_n']),
        'Вывести производные обратной степени из падающего факториала. К синусу применить четырёхшаговый цикл.',
        'В конечной формуле Лейбница сократить биномиальный коэффициент с факториалом полюса. Разделить по чётности индекса, получив ровно C_n и S_n.')


RODRIGUES={
    'P_m(x)=D^m[(x^2-1)^m]/(2^m*m!), m=0,1,...':
        ('P','x^2-1','-2*m*x','x^2-1','0','0',-1,
         'Differentiate (x²−1)u′=2mxu m+1 times, u=(x²−1)^m.'),
    'L_m(x)=exp(x)*D^m[x^m*exp(-x)], m=0,1,...':
        ('L','x','x-m','x','-x','-1',1,"xu′+(x−m)u=0 for u=x^m exp(-x)"),
    'H_m=(-1)^m*exp(x^2)*D^m exp(-x^2), m=0,1,...':
        ('H','1','2*x','1','-x^2','-2*x',1,"u′+2xu=0 for u=exp(-x²)"),
}


def rodrigues(task,lib):
    higher_packet(task,{'family','identity','printed_hint','hint'},literal=(
        'Доказать уравнение для многочленов Чебышева с напечатанной нормировкой.',
        'Доказать уравнение для многочленов Лежандра.',
        'Найти явное выражение многочлена и доказать дифференциальное уравнение.',
        'Найти явное выражение многочлена Эрмита и доказать уравнение.'))
    f=task['family']
    if f=='T_m(x)=2^(1-m)*cos(m*acos(x)), m=1,2,...':
        require(task['identity']=='(1-x^2)*T_m_second-x*T_m_prime+m^2*T_m=0' and
                task['kind']=='orthogonal_polynomial_ode' and not set(task)&{'printed_hint','hint'},
                'Сохраняем точный порядок дифференциального уравнения Чебышёва')
        t=('v','t');cos=('cos',t);d=table(cos,'t',lib)[0];second=table(d,'t',lib)[0]
        first_square=m.power(d,2);x=('v','x')
        require(same_value(first_square,m.add(ONE,m.neg(m.power(cos,2)))) and same_value(second,m.neg(cos)),
                'Коэффициенты фазовой подстановки не проверены')
        return higher_certificate(lib,'differentiate_seed_identity',dict(seed='cos(m*t)',coordinate='x=cos(t), t in (0,pi)',order='m>=1'),
            dict(ode=task['identity'],coefficient_lift=('1-x^2','-x'),polynomial_extension=True),
            'Дважды продифференцировать по t через x=cos t. Получается оператор (1−x²)D_x²−xD_x.',
            'Косинус кратной фазы удовлетворяет уравнению по t и по рекурсии является многочленом от x.',
            'Полиномиальное равенство, проверенное на (−1,1), справедливо на всей прямой.')
    spec=RODRIGUES.get(f);require(spec,'Не связан исходный вес формулы Родрига с линейным уравнением')
    name,A,B,R,G,r,sign,hint=spec
    require(task.get('printed_hint',task.get('hint')) in (None,hint) and
            task['kind']==('orthogonal_polynomial_ode' if name=='P' else 'orthogonal_polynomial_formula_and_ode'),
            'Осталось дополнительное указание или требование явной формулы')
    D=lambda a:table(a,'x',lib)[0];P=lambda a:m.parse(a,'x',['m'])
    A,B,R,G,r=map(P,(A,B,R,G,r));p=('s','m');k=m.add(p,ONE)
    log_derivative=m.add(m.mul(p,m.div(D(R),R)),D(G))
    require(same_value(m.add(m.mul(A,log_derivative),B),ZERO) and same_value(r,D(G)),
            'Первое уравнение для веса не проверено с заявленным логарифмическим преобразованием')
    # D^(m+1)(A u' + B u), A quadratic at most and B affine.
    require(D(D(D(A)))==ZERO and D(D(B))==ZERO,'Здесь нужен проверяемый конечный набор коэффициентов Лейбница')
    C=m.add(m.mul(m.mul(q(1,2),m.mul(k,p)),D(D(A))),m.mul(k,D(B)))
    B1=m.add(B,m.mul(k,D(A)))
    expanded=(m.add(C,m.add(m.mul(B1,r),m.mul(A,m.add(m.power(r,2),D(r))))),
              m.add(B1,m.mul(q(2),m.mul(A,r))),A)
    jets=[('s',f'Y{j}') for j in range(3)];operator=ZERO
    for coefficient,y in zip(expanded,jets):operator=m.add(operator,m.mul(q(sign),m.mul(coefficient,y)))
    written=task['identity']
    for suffix,j in (('_second',2),('_prime',1),('',0)):written=written.replace(name+'_m'+suffix,f'Y{j}')
    require(re.fullmatch(r'.+?=0',written),'Обязано быть равенство линейного выражения нулю')
    target=m.parse(written[:-2],'x',['m','Y0','Y1','Y2'])
    require(same_value(operator,target),'Лейбниц и сопряжение веса не дали напечатанный оператор')
    ans=dict(ode=task['identity'],coefficients=tuple(m.mul(q(sign),c) for c in expanded))
    if name=='L':ans['explicit']='m!*sum_(j=0)^m (-1)^j*binomial(m,j)*x^j/j!'
    if name=='H':ans['explicit']='m!*sum_(j=0)^floor(m/2) (-1)^j*(2*x)^(m-2*j)/(j!*(m-2*j)!)'
    return higher_certificate(lib,'differentiate_seed_identity',dict(family=f,integer_index='m>=0',seed_before_differentiation=(A,B),
                coefficient_log_derivative=r),ans,
        'Проверить линейное уравнение для веса через его логарифмическую производную на ненулевых участках.',
        'Применить конечный Лейбниц к уравнению m+1 раз. Третья производная старшего коэффициента и вторая производная младшего равны нулю.',
        'Сопрячь оператор весом и точно сравнить с исходными коэффициентами. Полиномиальность даёт равенство и в нулях веса.',
        *(( 'Явные коэффициенты следуют из конечного Лейбница или из коэффициентов exp(2xt−t²).',) if name!='P' else ()),
        differentiated_coefficients=(C,B1,A),expanded_identity=operator)

def operator_change(task,lib):
    if task['kind']=='differential_operator_shift':
        higher_packet(task,{'operator','D','assumptions','claim'},literal=
            'Доказать операторное тождество для дифференциального многочлена с переменными коэффициентами.')
        require(task['operator']=='f(D)=sum_(k=0)^n p_k(x)*D^k' and task['D']=='d/dx' and
                task['assumptions']==['p_k(x) continuous','lambda constant'] and
                task['claim']=='f(D){exp(lambda*x)*u}=exp(lambda*x)*f(D+lambda)u',
                'Коэффициенты должны умножать оператор слева, а λ быть постоянной')
        x=('v','x');rate=('s','lambda');e=('exp',('mul',rate,x));u=('u',x)
        proof=table(('mul',e,u),'x',lib,{'u'})[0]
        target=m.mul(e,m.add(('derivative_at_unknown','u',x),m.mul(rate,u)))
        require(same_value(proof,target),'Однократное сопряжение экспонентой не подтвердилась')
        return higher_certificate(lib,'moving_coordinate_operator',dict(operator=task['operator'],coefficients_multiply_on_left=True,
            sufficient_givens='appropriate derivatives of u through order n'),dict(identity=task['claim']),
            'Первое сопряжение D экспонентой вычислить таблицей. Повторение переносит каждую степень D.',
            'Коэффициенты p_k(x) в исходной сумме умножают результат слева, так что дифференцирование на них не переносится.',
            first_operator_check=proof)
    higher_packet(task,{'equation','substitution','target','D'},literal=
        'Доказать указанное преобразование уравнения при замене независимой переменной.')
    require((task['equation'],task['substitution'],task['target'],task['D'])==
            ('sum_(k=0)^n a_k*x^k*D_x^k y=0','x=exp(t)','sum_(k=0)^n a_k*D*(D-1)*...*(D-k+1)y=0','d/dt'),
            'Производные, множители и координатная подстановка должны совпадать с исходным уравнением')
    return higher_certificate(lib,'moving_coordinate_operator',dict(source_domain='x>0',substitution=task['substitution']),
        dict(transformed_equation=task['target'],kernel_recurrence='T_0=1; T_(k+1)=(D_t-k)T_k'),
        'При x=e^t оператор x D_x превращается в D_t.',
        'В производной D_t(x^k D_x^k y) один член равен k раз прежний результат, второй даёт x^(k+1) D_x^(k+1)y. Это проверяет индукционный шаг.')


def local_order(task,lib):
    kind=task['kind']
    if kind=='mathematical_question':
        higher_packet(task,{'off_zero','at_zero','requested_output'},literal='Доказать бесконечную дифференцируемость в 0 и построить график.')
        s=re.fullmatch(r'exp\(-([0-9]+(?:/[0-9]+)?)/x\^([1-9][0-9]*)\)',task['off_zero'])
        require(s and int(s[2])%2==0 and Fraction(s[1])>0 and task['at_zero']=='0'
                and task['requested_output']==['all derivative orders at zero'],
                'Требуется затухающая экспонента одинаковой чётной степени с обеих исходных сторон')
        c,p=Fraction(s[1]),int(s[2])
        return higher_certificate(lib,'derivative_orders_at_exception',dict(source=task['off_zero'],anchor=ZERO),
            dict(all_orders_at_zero=ZERO,recurrent_polynomial=f'P_0=1; P_(j+1)=-z²*D_z P_j+{p*c}*z^{p+1}*P_j',
                 z='1/x'), 'По таблице производная сохраняет общий экспоненциальный множитель и меняет лишь полином от 1/x.',
            'На обеих сторонах в разностном отношении экспонента подавляет добавочную степень 1/x и любую степень полинома.',
            'Индукция по порядку доказывает нулевое значение каждого производного в нуле.')
    higher_packet(task,{'off_zero','at_zero','n'},literal='Доказать существование производных в 0 до порядка n и отсутствие производной порядка n+1.')
    require(task['off_zero']=='x^(2*n)*sin(1/x)' and task['at_zero']=='0' and task['n']=='natural',
            'Не связаны кратность амплитуды, обратная фаза и нулевая точка')
    return higher_certificate(lib,'derivative_orders_at_exception',dict(source=task['off_zero'],n='positive integer'),
        dict(greatest_finite_order='n',derivatives_through_n_at_zero=ZERO,
             leading_punctured_term='(-1)^k*x^(2*n-2*k)*sin(1/x+k*pi/2)'),
        'Наименьшая степень x при каждом шаге получается только дифференцированием обратной фазы. Остальные члены имеют больший порядок.',
        'До n-й производной разностное отношение ещё затухает. На следующем шаге выбрать последовательности постоянных ненулевых фаз и разделить на x.')


def local_coordinates(task,lib):
    kind=task['kind']
    if kind=='parametric_curve_derivatives':
        meta=higher_packet(task,{'coordinates','parameter','parameters','stated_conditions','orders','requested_output'})
        t=task['parameter'];coords=task['coordinates']
        fn=re.fullmatch(rf'diff\(({NAME})\({t}\),{t}\)',coords[0])
        require(fn and len(coords)==2 and coords[1]==f'{t}*{coords[0]}-{fn[1]}({t})'
                and task['orders']==[1,2,3] and not task.get('parameters') and not task.get('stated_conditions')
                and meta.get('printed_instruction') in (None,'Найти производные y′ₓ, y″ₓ², y‴ₓ³ от функции y = y(x), заданной параметрически, если')
                and task['requested_output']==['derivatives_as_functions_of_parameter'],
                'Нужны три производные подлинной параметрической пары Лежандра')
        return higher_certificate(lib,'moving_coordinate_operator',dict(parameter=t,function=fn[1],regularity='d²f/dt² != 0'),
            dict(values=(t,'1/f″(t)','-f‴(t)/(f″(t))^3')),
            'Вывести dx/dt=f″(t), dy/dt=t*f″(t) из исходной пары. Сократить только на регулярной ветви.',
            'К результату последовательно применить D_x=(f″(t))^(-1)D_t.')
    if kind=='rectilinear_motion_from_position':
        meta=higher_packet(task,{'position','time','evaluate_at','requested_output'},literal=(
             'Найти скорость и ускорение, а также оба значения при заданном времени.',
             'Find velocity and acceleration, and both values at the specified time.'))
        t=task['time'];raw=m.parse(task['position'],t);at=m.parse(task['evaluate_at'],None)
        require(task['requested_output']==['velocity','acceleration','both_at_specified_time'] and
                meta.get('printed_goal') in (None,f'Find velocity, acceleration and both at {t}={task["evaluate_at"]}.')
                and meta.get('requested_operator') in (None,'kinematics') and
                not domain_conditions(raw,True) and m.num(at) is not None,'Требуются обе производные на допустимом времени')
        v,p=table(raw,t,lib);a,r=table(v,t,lib);sub={('v',t):at}
        return higher_certificate(lib,'moving_coordinate_operator',dict(position=raw,time=t,at=at),
            dict(velocity=v,acceleration=a,velocity_at=m.simplify(m.substitute(v,sub)),
                 acceleration_at=m.simplify(m.substitute(a,sub))),
            'Последовательно применить исходную таблицу к координате и к её первой производной. Затем подставить заданное время.',
            table_steps=(*p,*r))
    if kind=='piecewise_jet_matching':
        higher_packet(task,{'variable','join','branches','given','requested_output'},literal=
            'Choose a,b,c so that the extension is twice differentiable at the join.')
        x,z=task['variable'],task['join'];(lo,f),(hi,g)=task['branches'];fn=re.fullmatch(rf'({NAME})\({x}\)',f)
        insist=['all coefficients','necessity and sufficiency']
        require(fn and lo==f'{x}<={z}' and hi==f'{x}>{z}' and task['given']=='f twice differentiable up to its right endpoint from the left'
                and g==f'a*({x}-{z})^2+b*({x}-{z})+c' and task['requested_output']==insist,
                'Нужно согласовать значения и оба порядка на том же стыке')
        h=('v','h');pol=m.parse('a*h^2+b*h+c','h',['a','b','c']);d,p=table(pol,'h',lib);dd,r=table(d,'h',lib)
        known=tuple(m.simplify(m.substitute(e,{h:ZERO})) for e in (pol,d,dd))
        require(known==( ('s','c'),('s','b'),m.mul(q(2),('s','a')) ),
                'Таблица правой вставки не дала требуемые три коэффициента')
        return higher_certificate(lib,'moving_coordinate_operator',dict(join=z,left_function=fn[1],right_jets=known),
            dict(c=f'{fn[1]}({z})',b=f'{fn[1]}′_−({z})',a=f'{fn[1]}″_−({z})/2'),
            'Согласовать значение со значением в самой точке. Сходимость первого разностного отношения требует равных наклонов.',
            'Для производной F′ применить тот же аргумент, теперь согласовать её наклоны. Это также достаточно.',
            table_steps=(*p,*r))
    x,=task['variables'];pars=task['parameters'];fs=task['inner_arguments'];names=list(fs)
    hypotheses=task['stated_conditions'];text=task['outer_expression']
    require(len(names)==2 and task['requested_output']==['second_differential'] and task['inner_regularities']==dict.fromkeys(names,2)
            and all(fs[k]==f'{k}({x})' for k in names),
            'Требуются две внутренние функции с производными обоих порядков')
    raw=m.parse(text,None,[*pars,*names])
    first,second=names
    opening=f'Пусть {first} и {second} — дважды дифференцируемые функции переменной {x}. Найти d²y для y={text}'
    if hypotheses:
        own=m.context(dict(variable=x,parameters=pars,parameter_conditions=hypotheses))
        require(all(c.endswith('>0') and c[:-2] in pars for c in hypotheses)
                and (raw[0]!='rpow' or raw[1][0]!='s' or raw[1][1] not in pars or
                     m.constant_defined(raw[1],own) and m.sign(raw[1],own)==1),
                'Область исходной степени и печатное условие требуют отдельной проверки')
        ending=' ('+', '.join(hypotheses)+').'
    else:ending=' ('+' и '.join(pars)+' постоянные).'
    higher_packet(task,{'outer_expression','inner_arguments','variables','inner_regularities','parameters','stated_conditions','requested_output'},
                  literal=opening+ending)
    def partial(e,t):
        v=('v',t);s=('s',t);rate=table(m.substitute(e,{s:v}),t,lib)[0]
        return m.substitute(rate,{v:s})
    u,v=names;du,dv=(partial(raw,t) for t in names)
    mixed=partial(du,v)
    require(same_value(mixed,partial(dv,u)),'Смешанные коэффициенты не совпадают на исходной гладкой области')
    return higher_certificate(lib,'moving_coordinate_operator',dict(outside=raw,inside=fs,domain=domain_conditions(raw,True),hypotheses=hypotheses,independent=x),
        dict(coefficient_terms=dict(d2u=du,d2v=dv,du_du=partial(du,u),du_dv=m.mul(q(2),mixed),dv_dv=partial(dv,v))),
        'Построить первый дифференциал внешней функции в двух переменных и продифференцировать ещё раз.',
        'Сохранять d²u и d²v, поскольку оба аргумента зависят от исходной координаты.')


def higher_derivative_goal(task,lib,request):
    kind=task['kind']
    try:
        if remaining_derivative_head(task,kind):return remaining_derivative_goal(task,lib)
        if scale_routing(task,kind):return derivative_scale_goal(task,lib)
        if kind=='symbolic_order_derivative':
            if exponential_wave_candidate(task['function']) and set(task)<={'kind','id','source','schema','transcription','function','variable','order'}:
                higher_packet(task,{'function','variable','order'})
                result=exponential_wave_order(task,lib)
                if result is not None:return result
            try:return nth_polynomial_or_rational(task,lib)
            except Unsupported:
                if task.get('source',{}).get('printed_hint'):raise
                from tasks import symbolic_order
                plan,value=symbolic_order(task,lib,request)
                return dict(plan,theorem='method.symbolic_taylor_coefficients',
                            argument=('Построить точный коэффициент заданного порядка в исходной области.',)),value
        if kind=='symbolic_order_derivative_identity':return symbolic_identity(task,lib)
        if kind=='symbolic_trigonometric_polynomial_derivative':return trig_finite_spectrum(task,lib)
        if kind in ('symbolic_higher_composition_proof','higher_chain_rule_proof','symbolic_order_point_derivative'):
            return symbolic_composition(task,lib)
        if kind in ('orthogonal_polynomial_formula_and_ode','orthogonal_polynomial_ode'):return rodrigues(task,lib)
        if kind in ('inverse_function_higher_derivatives','parametric_derivatives_from_successive_differentials'):
            return inverse_or_differential(task,lib)
        if kind in ('differential_operator_shift','euler_operator_variable_change'):return operator_change(task,lib)
        if kind in ('order_of_differentiability','mathematical_question'):return local_order(task,lib)
        return local_coordinates(task,lib)
    except (poly.NotRational,poly.Undefined) as e:
        raise Unsupported('Нужна отдельная гипотеза о допустимости исходной алгебраической ветви') from e


MVT_HEADINGS={
    'rolle_verification':'Проверить справедливость теоремы Ролля для заданной функции.',
    'rolle_hypothesis_failure':'Объяснить кажущееся противоречие с теоремой Ролля.',
    'rolle_endpoint_limits':'Доказать существование внутренней точки с нулевой производной.',
    'iterated_rolle':('Доказать наличие внутреннего нуля производной порядка p+q+1.','Доказать существование нуля n-й производной.'),
    'polynomial_root_interlacing':'Доказать вещественность всех корней последовательных производных.',
    'orthogonal_polynomial_root_location':'Доказать указанное расположение всех корней многочлена.',
    'parallel_tangent_chord':'Найти точку кривой, касательная в которой параллельна данной хорде.',
    'lagrange_hypothesis_failure':'Верна ли формула конечных приращений на данном отрезке?',
    'mean_value_interpolation':'Найти функцию θ(x,Δx) для формулы конечных приращений при 0<θ<1.',
    'mean_value_points':'Определить промежуточное значение c в формуле конечных приращений на [0,2].',
    'mean_value_selection_discontinuity':'Доказать, что функция ξ(x), удовлетворяющая равенству, разрывна в любом сколь угодно малом интервале (0,ε).',
    'converse_mean_value_counterexample':'Для всякой ли ξ можно найти x1<ξ<x2 с указанным наклоном хорды? Рассмотреть приведённый пример.',
    'mean_value_inequality_proof':'Доказать указанное неравенство.',
    'cauchy_hypothesis_failure':'Объяснить, почему не верна формула Коши на заданном сегменте.',
    'cauchy_mean_value_proof':'Доказать формулу с определителем и промежуточной точкой.',
    'mean_value_unbounded_derivative':'Доказать прямое утверждение и построить пример, опровергающий обратное.',
    'bounded_derivative_uniform_continuity':'Доказать равномерную непрерывность на конечном или бесконечном интервале.',
    'asymptotic_derivative_mvt':('Доказать предел f(x)/x→0.','Доказать равенство нижнего предела и следствие при существовании предела f′.'),
    'one_sided_derivative_limit_proof':'Доказать существование односторонней производной и указанное равенство при условиях 1–3.',
    'derivative_characterizes_function':'Доказать, что из тождества следует указанный вид функции.',
}
MVT_META={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','literal_requirement',
          'section','printed_occurrence','source_issue'}
MVT_KINDS=set(MVT_HEADINGS)|{'identity_from_equal_derivatives','inverse_trig_identity_on_domain',
    'existential_mean_value_inequality','kinematic_mean_value_bound'}


def mvt_require(ok,reason):
    if not ok:raise Unsupported(reason)


def mvt_packet(task,fields):
    headings=MVT_HEADINGS.get(task['kind'],());meta=task.get('source',{})
    if isinstance(headings,str):headings=(headings,)
    mvt_require(isinstance(meta,dict) and not set(meta)-MVT_META and meta.get('literal_requirement') in (None,*headings)
                and not set(task)-{'kind','id','source','schema','transcription'}-set(fields),
                'Не связано дополнительное требование формулы среднего либо исходная область')


def mvt_certificate(lib,key,scope,value,*argument,**data):
    mvt_require(key in lib.data.get('mvt_transitions',()),'Нет общего доказательного перехода по формуле среднего')
    return dict(theorem='mean_value.'+key,scope=scope,argument=argument,**data),value


def mvt_routing(task,kind):
    if kind in MVT_KINDS:return True
    text=task.get('statement','')
    return kind=='proof_about_real_functions' and isinstance(text,str) and any(
        grammar.fullmatch(text) for grammar in INTERVAL_CLAIMS)


def rolle_goals(task,lib):
    kind=task['kind']
    if kind=='rolle_verification':
        from graphs import rational_roots
        mvt_packet(task,{'function','interval'})
        mvt_require(task['interval']=='not explicitly specified on the printed page','Необходимо связать указанные концы')
        f=m.parse(task['function'],'x');ctx=m.context(dict(variable='x'))
        mvt_require(all(known_guard(g,ctx) for g in domain_conditions(f,True)),'Гладкость нужна на всех рассматриваемых концах')
        p,d=poly.rf(f,'x');fd,tree=table(f,'x',lib);p1,d1=poly.rf(fd,'x')
        mvt_require(len(d)==len(d1)==1 and len(p1)>1,'Нужен негладкий случай либо корни непостоянной полиномиальной производной')
        roots=sorted(set(rational_roots(p)),key=cmp_to_key(line.compare));stationary=rational_roots(p1)
        mvt_require(len(roots)>=2 and all(any(line.compare(a,z)<0 and line.compare(z,b)<0 for z in stationary)
                    for a,b in zip(roots,roots[1:])), 'Не удалось проверить последовательные равные значения')
        return mvt_certificate(lib,'rolle_root_count',dict(function=f,scope='all equal endpoint levels on R'),
            dict(function_zeros=[line.quadratic_term(z) for z in roots],derivative_zeros=[line.quadratic_term(z) for z in stationary]),
            'Точно вычислить нули функции и производной. Между соседними нулями функции найден внутренний нуль производной.',
            'На промежутке без стационарных точек производная одного строгого знака, так что равные значения в концах невозможны.',
            table_steps=tree)
    if kind=='rolle_hypothesis_failure':
        mvt_packet(task,{'function','zeros','interval','claim'})
        mvt_require((task['function'],task['zeros'],task['interval'],task['claim'])==
            ('1-cbrt(x^2)',['-1','1'],'[-1,1]','derivative does not equal zero in the interval wherever it exists'),
            'Нужно связать одинаковые значения и каждую особую точку')
        f=m.parse(task['function'],'x');d,tree=table(f,'x',lib)
        return mvt_certificate(lib,'rolle_root_count',dict(interval=(-1,1),equal_endpoint_values=ZERO),
            dict(applicable=False,exception=ZERO,ordinary_derivative_exists_here=False,finite_formula=d),
            'В нуле разностное отношение равносильно −|h|^(2/3)/h и не имеет конечного предела.',
            'Вне нуля таблица даёт ненулевой наклон. Отсутствие производной в исходном интервале объясняет неприменимость Ролля.',
            table_steps=tree)
    if kind=='rolle_endpoint_limits':
        mvt_packet(task,{'assumptions','claim'})
        mvt_require(task['assumptions']==['differentiable with finite derivative throughout (a,b), possibly infinite endpoints',
            'lim_(x->a+)f=lim_(x->b-)f'] and task['claim']=='exists c in (a,b) with f′(c)=0',
            'Требуются оба равных концевых предела на исходном интервале')
        return mvt_certificate(lib,'rolle_root_count',dict(common_endpoint_limit='finite or signed infinite',domain='(a,b)'),
            dict(exists_zero_of_derivative=True),
            'Для непостоянной функции выбрать внутреннее значение, отличное от общего предела. На бесконечном пределе любое конечное значение подходит.',
            'Выбрать по обеим сторонам точки с значениями по одну сторону от выбранного. На компактном отрезке есть внутренний экстремум.',
            'Внутренний экстремум имеет нулевую производную. Для постоянной функции можно взять любую точку.')
    if kind=='iterated_rolle':
        mvt_packet(task,{'assumptions','claim'})
        a=task['assumptions'];assertion=task['claim']
        many=['f^(n-1) continuous on [x0,xn]','f^(n) exists on (x0,xn)','x0<x1<...<xn, all f(xi) equal']
        ends=['f^(p+q) continuous on [a,b]','f^(p+q+1) exists on (a,b)','f^(j)(a)=0 for j=0..p; f^(j)(b)=0 for j=0..q']
        mvt_require((a,assertion) in ((many,'exists xi in (x0,xn): f^(n)(xi)=0'),
                                    (ends,'exists c in (a,b): f^(p+q+1)(c)=0')),
                    'Связаны должны быть число корней, требуемые кратности и все производные')
        return mvt_certificate(lib,'rolle_root_count',dict(assumptions=a),
            dict(claim=assertion,initial_zero_count='n+1' if a==many else 'p+q+2 counting multiplicities'),
            'Из равных исходных значений получить нули, вычитая общий уровень. Между подряд идущими нулями применить Ролля.',
            'При переходе к производной наследуются все нули со сниженной на единицу кратностью. Совместный счёт уменьшается максимум на один.',
            'После нужного числа шагов остаётся внутренний нуль.')
    if kind=='polynomial_root_interlacing':
        mvt_packet(task,{'family','hypothesis','claim'})
        mvt_require((task['family'],task['hypothesis'],task['claim'])==
            ('P_n=sum_(k=0)^n a_k*x^(n-k), all coefficients real, a0 nonzero','all roots real',
             'all roots of derivatives of orders 1..n-1 are real'),'Нет точной степени или исходного числа вещественных корней')
        return mvt_certificate(lib,'rolle_root_count',dict(real_roots_count='n including multiplicities',leading_coefficient_nonzero=True),
            dict(all_successive_derivative_roots_real=True),
            'Производная наследует кратные корни со сниженной кратностью и получает по корню между различными последовательными корнями.',
            'Счёт даёт степень n−1, значит, не остаётся места для иных корней. Повторить для следующей производной.')
    mvt_packet(task,{'family','requested_root_region'})
    spec={
        'D^n[(x²-1)^n]/(2^n*n!)':('(-1,1)','both endpoints retain multiplicity n-j after j steps'),
        'exp(x)*D^n[x^n*exp(-x)]':('(0,+infinity)','0 retains multiplicity n-j; all differentiated weights vanish on the positive tail'),
        '(-1)^n*exp(x²)*D^n exp(-x²)':('real line','all differentiated weights vanish on both tails'),
    }
    s=spec.get(task['family'])
    mvt_require(s and task['requested_root_region']==s[0],'Требуется расположение всех корней на исходном интервале веса')
    return mvt_certificate(lib,'rolle_root_count',dict(family=task['family'],integer_order='n>=0',inherited_zero_or_tail=s[1]),
        dict(all_root_region=s[0],distinct_count='n'),
        'Обычный Ролль даёт новые нули между имеющимися. Для бесконечной границы применять Ролля с общими нулевыми пределами.',
        'На каждом шаге использовать унаследованный конечный нуль веса или его нулевые хвосты, получая минимум один дополнительный внутренний нуль.',
        'Получаются n различных корней. Производящий множитель вдоль области ненулевой, а итоговый многочлен имеет степень n.')


def interpolation(task,lib):
    from graphs import rational_roots
    kind=task['kind'];x=('v','x');ctx=m.context(dict(variable='x'))
    if kind=='parallel_tangent_chord':
        mvt_packet(task,{'curve','chord'})
        mvt_require(task['curve'].startswith('y='),'Вход должен задавать явную кривую')
        f=m.parse(task['curve'][2:],'x')
        pair=[[m.parse(c,None) for c in pt] for pt in task['chord']]
        mvt_require(len(pair)==2 and all(len(p)==2 for p in pair) and not domain_conditions(f,True) and
                    all(m.num(t) is not None for p in pair for t in p),'Нужна полная полиномиальная кривая и две числовые точки')
        (a,u),(b,v)=pair
        mvt_require(a!=b and all(same_value(m.substitute(f,{x:z}),y) for z,y in pair),'Точки не образуют исходную хорду')
        slope=m.div(m.add(v,m.neg(u)),m.add(b,m.neg(a)));d,tree=table(f,'x',lib)
        p,z=poly.rf(m.add(d,m.neg(slope)),'x');mvt_require(len(p)>1,'Нужно исчерпывающе решить нетождественный уровень')
        values=[]
        for r in rational_roots(p):
            h=q(r.a) if not r.b else m.add(q(r.a),m.mul(q(r.b),('sqrt',q(r.d))))
            values.append((h,m.simplify(m.substitute(f,{x:h}))))
        return mvt_certificate(lib,'secant_derivative_candidates',dict(curve=f,chord=pair,slope=slope),
            dict(points=values),'Проверить принадлежность обоих концов кривой. Вычислить наклон хорды, приравнять его производной и найти все корни.',
            table_steps=tree)
    if kind=='mean_value_points':
        mvt_packet(task,{'branches','interval'})
        mvt_require(task['interval']=='[0,2]' and [k[0] for k in task['branches']]==['0<=x<=1','1<x<+infinity'],
                    'Не связаны две области с общим стыком и заданным отрезком')
        left,right=(m.parse(k[1],'x') for k in task['branches'])
        def at(e,c):return m.simplify(m.substitute(e,{x:q(c)}))
        a,b=at(left,0),at(right,2)
        d1,d2=table(left,'x',lib)[0],table(right,'x',lib)[0]
        mvt_require(not domain_conditions(left,True) or all(known_guard(g,ctx) for g in domain_conditions(left,True)),
                    'Левая область не выдерживает исходных ограничений')
        mvt_require(all(g==('nonzero',x) or known_guard(g,ctx) for g in domain_conditions(right,True)) and
                    same_value(at(left,1),at(right,1)) and same_value(at(d1,1),at(d2,1)),
                    'Правый след или производная не согласуются в 1')
        slope=m.div(m.add(b,m.neg(a)),q(2));chosen=[]
        for d,l,u in ((d1,0,1),(d2,1,2)):
            p,g=poly.rf(m.add(d,m.neg(slope)),'x')
            mvt_require(any(p),'Каждая точка линейной ветви подходит, нужен отдельный ответ')
            for root in rational_roots(p):
                if line.compare(line.Quadratic(Fraction(l)),root)<0 and line.compare(root,line.Quadratic(Fraction(u)))<0:
                    z=q(root.a) if not root.b else m.add(q(root.a),m.mul(q(root.b),('sqrt',q(root.d))))
                    chosen.append(z)
        if same_value(at(d1,1),slope):chosen.append(ONE)
        return mvt_certificate(lib,'secant_derivative_candidates',dict(interval=(0,2),original_branches=(left,right)),
            dict(slope=slope,points=chosen),'Сверить исходное значение и обе производные в стыке. Вычислить единый секущий наклон из двух концов.',
            'Решить уравнение наклона отдельно на каждой открытой ветви и отдельно проверить точку стыка.')
    mvt_packet(task,{'function','identity'})
    mvt_require(task['identity']=='f(x+h)-f(x)=h*f′(x+theta*h)','Изменена требуемая формула θ или шкала приращения')
    text=task['function'];h=('s','h');t=('s','xi')
    if text=='1/x':
        return mvt_certificate(lib,'secant_derivative_candidates',dict(domain='x(x+h)>0, h!=0'),
            dict(xi='sign(x)*sqrt(x*(x+h))',theta='(xi-x)/h',zero_increment='any theta in (0,1) where f defined'),
            'Сократить секущее отношение до −1/(x(x+h)). Приравнять −1/xi² и выбрать знак той же ветви.',
            'Геометрическое среднее двух положительных модулей лежит между ними. Противоположные знаки делителей нарушают исходный промежуток.')
    if text=='exp(x)':
        f=('exp',x);d,tree=table(f,'x',lib)
        mvt_require(d==f,'Табличная экспонента не дала ту же функцию')
        return mvt_certificate(lib,'secant_derivative_candidates',dict(domain='all real endpoints, h!=0'),
            dict(xi='x+ln((exp(h)-1)/h)',theta='ln((exp(h)-1)/h)/h',zero_increment='any theta in (0,1)'),
            'Секущее отношение равно exp(x)*(exp(h)-1)/h и положительно. Решить уравнение производной логарифмом.',
            'По строгой монотонности экспоненты её секущий наклон лежит строго между производными в концах.',
            table_steps=tree)
    expression,_,restriction=text.partition(', ')
    params=sorted(set(re.findall(r'[A-Za-z]\w*',expression)) - {'x'})
    mvt_require(not restriction or restriction=='a!=0' and 'a' in params,'Не связана ненулевость старшего коэффициента')
    f=m.parse(expression,'x',params)
    mvt_require(not domain_conditions(f,True),'Требуется гладкий полином на всём исходном сегменте')
    d,tree=table(f,'x',lib);sec=m.div(m.add(m.substitute(f,{x:m.add(x,h)}),m.neg(f)),h)
    target=m.add(m.substitute(d,{x:t}),m.neg(sec));num,den=m.rational_form(target)
    by={}
    for mon,coef in num.items():
        no=dict(mon);order=no.pop(t,0);by.setdefault(order,{})[tuple(sorted(no.items(),key=str))]=coef
    n=max(by,default=0)
    mvt_require(n in (1,2) and all(j>=0 for j in by),'Нужна точная линейная или квадратная формула уровня производной')
    frac=[m.poly_expr(by.get(j,{})) for j in range(n+1)]
    if n==1:values=[m.div(m.neg(frac[0]),frac[1])]
    else:
        A,B,C=frac[2],frac[1],frac[0];root=('sqrt',m.add(m.power(B,2),m.neg(m.mul(q(4),m.mul(A,C)))))
        values=[m.div(m.add(m.neg(B),m.mul(q(s),root)),m.mul(q(2),A)) for s in (-1,1)]
    return mvt_certificate(lib,'secant_derivative_candidates',dict(function=f,original_condition=restriction,increment_nonzero=True),
         dict(secant_slope=sec,equation_coefficients=frac,xi_candidates=values,
              required_filter='retain real xi strictly between x and x+h',theta='(xi-x)/h',zero_increment='any theta in (0,1)'),
         'Вычислить исходное разностное отношение при h≠0. Полином производной в xi приравнять секущему наклону.',
         'Решить точное уравнение и отобрать корни внутри отрезка в правильной ориентации шага. Существование гарантирует теорема Лагранжа.',
         table_steps=tree)



def endpoint_limit_and_trip_bounds(task,lib):
    if not lib.data.get('typed_source_reductions'):return None
    kind=task['kind']
    if kind=='one_sided_derivative_limit_proof':
        mvt_packet(task,{'assumptions','claim'})
        a=task.get('assumptions',[])
        literal='printed limit subscript x→x0+∞; text names its value f′(x0+0) and says finite or infinite'
        valid='lim_(x->x0+) f′(x) exists, finite or infinite'
        if (len(a)!=3 or a[:2]!=['f defined and continuous on [x0,X]','f′ finite on (x0,X)'] or
                a[2] not in (literal,valid) or task.get('claim')!='f′_+(x0)=f′(x0+0)'):return None
        value=dict(equality='right derivative at the finite endpoint equals the right limit of the derivative when that limit exists')
        if a[2]==literal:
            value.update(printed_claim_holds=False,counterexample=dict(
                function='atan(x-x0)',endpoint_derivative=ONE,derivative_limit_at_positive_infinity=ZERO))
        return dict(theorem='method.finite_endpoint_mean_value_scope',argument=[
            'На каждом [x₀,x₀+h] применяем формулу Лагранжа. Частное приращений равно f′(cₕ), где x₀<cₕ<x₀+h.',
            'Поэтому применим именно предел производной при cₕ→x₀ справа, в том числе бесконечный предел.',
            'Предел при x→+∞ к этому выводу не относится. У arctan(x−x₀) правая производная в x₀ равна единице, а предел производной на бесконечности равен нулю.'
        ]),value
    if kind=='kinematic_mean_value_bound':
        mvt_packet(task,{'assumptions','claim','requested_output'})
        original='A car starts at A, completes its journey after time t, and travels distance s'
        rest='The initial and final velocities are zero and acceleration means its magnitude'
        a=task.get('assumptions',[])
        if (a not in ([original],[original,rest]) or task.get('requested_output')!=['prove_bound_from_kinematic_model']
                or task.get('claim')!='At some moment the acceleration was at least 4*s/t^2'):return None
        value=dict(bound='max |v′| >= 4*s/t^2',scope='continuously differentiable velocity and zero initial and final speeds')
        if len(a)==1:
            value.update(printed_claim_holds=False,counterexample=dict(
                time=ONE,velocity='tau on [0,1]',distance=q(1,2),largest_acceleration=ONE,claimed_lower_bound=q(2)))
        return dict(theorem='method.two_endpoint_speed_envelope',argument=[
            'Если скорость на обоих концах нулевая и |v′|≤M, формула среднего с левого и правого концов даёт |v(τ)|≤M min(τ,t−τ).',
            'Площадь под огибающим треугольником равна Mt²/4. Из s=∫|v| следует указанная оценка.',
            'Если поездка просто закончилась в отмеченный момент, нулевая конечная скорость не следует из пройденной длины. При v(τ)=τ на [0,1] ускорение всюду равно единице, а напечатанная граница даёт два.',
            'Для знакового ускорения мгновенное торможение также не даёт нужной положительной границы. Гладкий пример v(τ)=τ(1−τ³) имеет нулевые концы, путь 3/10 и максимум v′, равный единице.'
        ]),value
    return None


def mean_value_theory(task,lib):
    kind=task['kind']
    if kind=='lagrange_hypothesis_failure':
        mvt_packet(task,{'function','interval','assumption'})
        mvt_require(task['interval']=='[a,b]' and task['assumption']=='a*b<0' and
                    ('nonzero',('v','x')) in domain_conditions(m.parse(task['function'],'x'),True),
                    'Нужно найти исходный полюс внутри заданного отрезка')
        return mvt_certificate(lib,'secant_interval_scope',dict(a_less_than_b=True,opposite_signs=True),
            dict(applicable=False,point_of_undefinedness=ZERO),
            'Нуль лежит между разными знаками концов. Исходный знаменатель в нуле не определяет функцию, значит, Лагранж неприменим.')
    if kind=='mean_value_selection_discontinuity':
        mvt_packet(task,{'at_zero','off_zero','given'})
        mvt_require((task['at_zero'],task['off_zero'],task['given'])==
            ('0','x*sin(ln(x)), x>0','f(x)-f(0)=x*f′(xi(x)), 0<xi(x)<x'),
            'Для ветви выбора нужны непрерывная фаза, её неограниченность и точный диапазон секущих')
        f=m.parse('x*sin(ln(x))','x');d,tree=table(f,'x',lib)
        return mvt_certificate(lib,'secant_interval_scope',dict(relative_domain='0<xi(x)<x',secant_range=(-1,1)),
            dict(continuous_selection_on_any_origin_interval=False,derivative=d,derivative_amplitude='sqrt(2)'),
            'При непрерывном выборе ln(xi(x)) непрерывна и не ограничена снизу из-за xi(x)<x. Её образ содержит целый левый луч.',
            'Производная равна sin(ln xi)+cos(ln xi) и на любом левом фазовом луче достигает sqrt(2). Секущая sin(ln x) всегда не больше 1.',
            table_steps=tree)
    if kind=='converse_mean_value_counterexample':
        mvt_packet(task,{'given','desired','example'})
        spec=task['example'];f=m.parse(spec['function'],'x');p=poly.rf(f,'x')[0]
        mvt_require((task['given'],task['desired'])==('f′ continuous on (a,b)','(f(x2)-f(x1))/(x2-x1)=f′(xi)') and
                    len(p)==4 and p[3]>0 and p[2]==0 and spec['xi']=='0' and spec['interval']=='[-1,1]',
                    'Нужна проверка всех хорд, строго охватывающих указанную точку')
        d,tree=table(f,'x',lib)
        return mvt_certificate(lib,'secant_interval_scope',dict(x1_less_than_zero_less_than_x2=True,example=f),
            dict(converse_valid=False,derivative_at_point=q(p[1])),
            'Наклон хорды отличается от производной в нуле на положительный старший коэффициент, умноженный на x₁²+x₁x₂+x₂².',
            'Эта квадратичная форма строго положительна при разных концах.',table_steps=tree)
    if kind=='mean_value_inequality_proof':
        mvt_packet(task,{'claim','hypotheses'})
        claim=task['claim'];args=task['hypotheses']
        absolute=re.fullmatch(r'abs\((sin|atan)\(([a-z])\)-\1\(([a-z])\)\)<=abs\(\2-\3\)',claim)
        if absolute and not args:
            f=m.parse(absolute[1]+'(x)','x');d,tree=table(f,'x',lib)
            reason='|cos(ξ)|≤1' if absolute[1]=='sin' else '0<1/(1+ξ²)≤1'
            return mvt_certificate(lib,'derivative_bound_for_increments',dict(smooth_on='R',derivative=d),dict(proved=claim),
                'Для разных концов выбрать промежуточную точку теоремой Лагранжа. Для совпавших равенство непосредственное.',
                'Ограничить модуль производной '+reason+' и умножить на длину отрезка.',table_steps=tree)
        if (args,claim)==(['0<y<x','p>1'],'p*y^(p-1)*(x-y)<=x^p-y^p<=p*x^(p-1)*(x-y)'):
            f=m.parse('x^p','x',['p']);d,tree=table(f,'x',lib)
            monotone='p*t^(p-1) возрастает на положительных аргументах, так как p>1.'
        elif (args,claim)==(['0<b<a'],'(a-b)/a<ln(a/b)<(a-b)/b'):
            f=m.parse('ln(x)','x');d,tree=table(f,'x',lib)
            monotone='1/t строго убывает между положительными концами. Разность логарифмов равна логарифму отношения.'
        else:raise Unsupported('Не связаны производная и её точные оценки на исходном отрезке')
        return mvt_certificate(lib,'derivative_bound_for_increments',dict(hypotheses=args,derivative=d),dict(proved=claim),
            'Все концы и отрезок положительны. Получить внутренний аргумент производной по Лагранжу.',monotone,
            'Подставить производные на концах как границы и умножить на строго положительную длину.',table_steps=tree)
    if kind=='cauchy_hypothesis_failure':
        mvt_packet(task,{'functions','interval','form'})
        mvt_require((task['functions'],task['interval'],task['form'])==
            (['x^2','x^3'],'[-1,1]','ratio of increments equals ratio of derivatives'),
            'Нужно проверить оба делителя и равенство с учётом собственной области')
        return mvt_certificate(lib,'secant_interval_scope',dict(interval=(-1,1),g_increment=q(2)),
            dict(ratio_valid=False,cross_multiplied_witness=ZERO),
            'Равенство приращений после умножения крест-накрест требует c=0. Там производная знаменателя 3c² тоже нулевая.',
            'Во всех точках c≠0 отношение производных равно 2/(3c), что не может равняться нулевому отношению приращений.')
    if kind=='cauchy_mean_value_proof':
        mvt_packet(task,{'hypotheses','claim'})
        mvt_require(task['hypotheses']==['f differentiable on [x1,x2]','x1*x2>0','x1<x2'] and
                    task['claim']=='(x1*f(x2)-x2*f(x1))/(x1-x2)=f(xi)-xi*f′(xi), x1<xi<x2',
                    'Исходная ветвь должна целиком избегать нуля')
        return mvt_certificate(lib,'secant_interval_scope',dict(interval='[x1,x2]',no_zero=True),
            dict(auxiliary_pair=('f(x)/x','1/x'),same_point='xi in (x1,x2)'),
            'Выбрать F=f/x и G=1/x, чтобы их приращения дали левую дробь. Одноимённость концов позволяет делить по всему отрезку.',
            'По правилу частного F′=(xf′−f)/x² и G′=−1/x². Вторая производная здесь ненулевая во всех точках.',
            'Применить Коши к F,G и сократить x². Получается требуемая правая часть в той же промежуточной точке.')
    if kind in ('mean_value_unbounded_derivative','bounded_derivative_uniform_continuity','asymptotic_derivative_mvt'):
        mvt_packet(task,{'assumptions','claim','corollary'});a=task['assumptions'];claim=task.get('claim')
        if a==['(a,b) finite','f differentiable and unbounded on (a,b)'] and claim=='f′ is unbounded on (a,b)':
            return mvt_certificate(lib,'derivative_bound_for_increments',dict(interval='(a,b)',finite_length=True),
                dict(proved=claim,converse_counterexample='sqrt(x) on (0,1)'),
                'Фиксировать внутреннюю точку t. Если бы |f′|≤M, Лагранж дал бы |f(x)|≤|f(t)|+M(b−a) для всех x.',
                'Обратное опровергает ограниченная sqrt(x) на (0,1), её производная 1/(2sqrt(x)) не ограничена.')
        if a==['(a,b) finite or infinite','f differentiable on (a,b)','f′ bounded there'] and claim is None:
            return mvt_certificate(lib,'derivative_bound_for_increments',dict(interval='(a,b)',finite_length_optional=True),
                dict(uniformly_continuous=True,modulus='M*delta'),
                'Взять любые две точки исходного интервала. Их компактный отрезок лежит внутри.',
                'Применить Лагранжа и ограничить модуль приращения через M|x−y|. Выбрать δ=ε/(1+M), одинаковое для всех пар.')
        if a==['f differentiable on (x0,+infinity)','f′(x)→0 at +infinity'] and claim=='f(x)=o(x)':
            return mvt_certificate(lib,'moving_secant_on_tail',dict(assumptions=a),dict(proved=claim,auxiliary_segment='[X,x]'),
                'Для ε>0 выбрать X>max(x₀,0) так, что |f′(t)|<ε при t≥X.',
                'Лагранж на [X,x] даёт |f(x)/x|≤|f(X)|/x+ε(x−X)/x. При x→∞ первая часть исчезает, а вторая не больше ε.')
        if (a,claim,task.get('corollary'))==(['f differentiable on (x0,+infinity)','f(x)=o(x) at +infinity'],
                'liminf_(x->+infinity) abs(f′(x))=0','if lim f′=k exists, then k=0'):
            return mvt_certificate(lib,'moving_secant_on_tail',dict(assumptions=a),
                dict(proved=claim,auxiliary_segment='[x/2,x]',corollary=task['corollary']),
                'Для больших x отрезок [x/2,x] внутри исходного интервала. Лагранж даёт ξ в нём с f′(ξ)=2f(x)/x−f(x/2)/(x/2).',
                'Правая часть стремится к нулю, а ξ≥x/2→∞. Модуль неотрицателен, поэтому нижний предел нулевой. При существующем пределе это даёт k=0.')
        raise Unsupported('Не связаны ограниченность длины, хвост производной или область исходного приращения')
    if kind=='existential_mean_value_inequality':
        mvt_packet(task,{'assumptions','claim','requested_output'})
        a=task['assumptions'];claim=task['claim'];outputs=task['requested_output']
        if (a,claim,outputs)==(['a<b','f is continuous on [a,b], has a finite derivative on (a,b), and is not affine on [a,b]'],
            "There exists c in (a,b) with |f'(c)|>|(f(b)-f(a))/(b-a)|",['mathematical_proof','geometric_illustration']):
            return mvt_certificate(lib,'derivative_bound_for_increments',dict(domain='[a,b]',non_affine=True),
                dict(proved=claim,auxiliary_function='subtract the endpoint chord',geometric_interpretation='some tangent steeper in modulus than the chord'),
                'Вычесть хорду, получив g с нулями на концах, но g(c)≠0 в некоторой внутренней точке.',
                'Лагранж на [a,c] и [c,b] даёт значения g′ противоположных строгих знаков. Выбрать знак, усиливающий модуль наклона хорды.')
        if (a,claim,outputs)==(['a<b','f has a second derivative on [a,b]',"f'(a)=f'(b)=0"],
            "There exists c in (a,b) with |f''(c)| >= 4*|f(b)-f(a)|/(b-a)^2",['mathematical_proof']):
            return mvt_certificate(lib,'derivative_bound_for_increments',dict(domain='[a,b]',zero_end_slopes=True),
                dict(proved=claim,majorant="|f'(t)| < K*min(t-a,b-t) under the negated claim"),
                'Если K=0, подойдёт любая внутренняя точка. Иначе предположить |f″|<K и применить Лагранжа к f′ от обоих концов.',
                'Полученная треугольная оценка непрерывна. Её интеграл равен K(b−a)²/4, а интеграл |f′| строго меньше.',
                'Это противоречит K=4|f(b)−f(a)|/(b−a)² по формуле Ньютона–Лейбница.')
    raise Unsupported('Нужно связать конечный односторонний предел или необходимые кинематические условия')


def derivative_identities(task,lib):
    kind=task['kind']
    if kind=='identity_from_equal_derivatives':
        mvt_packet(task,{'assumptions','claim','requested_output'})
        a=task['assumptions'];x=('v','x')
        mvt_require(len(a)==4 and a[0].startswith('f(x)=') and a[1].startswith('g(x)=') and a[2] in ('x<1','x>1')
            and a[3]=='arctangent takes its principal real values' and task['claim']=='Check that f and g have the same derivative here and derive their relation'
            and task['requested_output']==['prove_derivative_equality','determine_constant_on_given_interval'],
            'Требуется одна полная компонента исходной непрерывности')
        f,g=(m.parse(s[5:],'x') for s in a[:2]);d,tr=table(f,'x',lib);dg,tg=table(g,'x',lib)
        ctx=m.context(dict(variable='x'))
        guards=[guard for e in (f,g) for guard in domain_conditions(e,True)]
        mvt_require(all(known_guard(guard,ctx) or guard[0]=='nonzero' and
            (same_value(guard[1],m.add(ONE,m.neg(x))) or same_value(guard[1],m.add(x,m.neg(ONE))))
            for guard in guards) and same_value(d,dg),
            'Не удалось доказать равенство производных на всей заданной компоненте')
        if a[2]=='x<1':
            res=m.simplify(m.substitute(m.add(f,m.neg(g)),{x:ZERO}));anchor='x=0'
        else:
            mvt_require((f,g)==(m.parse('atan((1+x)/(1-x))','x'),('atan',x)),'Нужна проверенная разность пределов или значение в компоненте')
            res=m.mul(q(Fraction(-3,4)),('pi',));anchor='x→+∞, f→−π/4 and g→π/2'
        return mvt_certificate(lib,'zero_derivative_connected',dict(domain=a[2],anchor=anchor,f=f,g=g),
            dict(common_derivative=d,constant_difference=res),'Проверить исходную область и производные. Нулевая производная разности делает её постоянной по Лагранжу.',
            'Подставить внутреннюю точку либо перейти к пределу по той же компоненте, чтобы найти постоянную.',table_steps=[*tr,*tg])
    if kind=='inverse_trig_identity_on_domain':
        mvt_packet(task,{'assumptions','claim','requested_output'});a=task['assumptions'];c=task['claim'];o=task['requested_output']
        if (a,c,o)==(['abs(x)>=1'],'2*atan(x)+asin(2*x/(1+x^2))=pi*sgn(x)',
                     ['prove_identity_on_both_components_including_boundaries']):
            return mvt_certificate(lib,'principal_branch_identity',dict(domain=a,principal_range='[-pi/2,pi/2]'),dict(proved=c),
                'Положить u=2 arctan x. Для x≥1 u∈[π/2,π), поэтому π−u в главной ветви arcsin и имеет синус sin u.',
                'По формуле двойного угла sin u=2x/(1+x²). Отрицательная компонента следует по нечётности, включая оба края.')
        if (a,c,o)==(['abs(x)<=1/2'],'3*acos(x)-acos(3*x-4*x^3)=pi',['prove_identity_including_endpoints']):
            return mvt_certificate(lib,'principal_branch_identity',dict(domain=a,principal_range='[0,pi]'),dict(proved=c),
                'При u=arccos x имеем π/3≤u≤2π/3. Значит 3u−π∈[0,π] и arccos(cos(3u−π))=3u−π.',
                'Тройной косинус даёт cos(3u−π)=3x−4x³. Оба конца допустимы в замкнутой главной ветви.')
        raise Unsupported('Требуется связать алгебраический аргумент с полной областью главной ветви')
    mvt_packet(task,{'assumptions','claim','requested_output','regularity','domain','quantification','identity'})
    if 'identity' in task:
        a=task.get('regularity'),task.get('domain'),task.get('quantification'),task['identity'],task['claim']
        mvt_require(a[1:3]==('R','all real x,h'),'Нужна свобода двух концов для дифференцирования тождества')
        if (a[0],*a[3:])==('C^1','f(x+h)-f(x)=h*f′(x)','f(x)=a*x+b'):
            return mvt_certificate(lib,'zero_derivative_connected',dict(domain='R',parameters='all real x,h'),dict(form='A*x+B'),
                'Фиксировать x и дифференцировать по h. Получить f′(x+h)=f′(x), значит, f′ постоянно.',
                'Вычесть найденную линейную часть. Остаток с нулевой производной постоянен на R.')
        if (a[0],*a[3:])==('C^2','f(x+h)-f(x)=h*f′(x+h/2)','f(x)=a*x²+b*x+c'):
            return mvt_certificate(lib,'zero_derivative_connected',dict(domain='R',parameters='all real midpoints and halfwidths'),dict(form='A*x^2+B*x+C'),
                'Заменить концы на u−v,u+v. Равенство f(u+v)−f(u−v)=2v f′(u) дифференцировать по v, затем ещё раз по v.',
                'Первая производная даёт сумму двух f′, вторая даёт f″(u+v)−f″(u−v)=0. Концы произвольны, f″ постоянно.',
                'Дважды применить нулевую производную после вычитания полиномиальной части.')
        raise Unsupported('Не удалось выбрать свободные координаты в тождестве для производных')
    a=task['assumptions'];c=task['claim'];o=task['requested_output']
    if (a,c,o)==(['f is differentiable on (a,b)',"f'(x)=0 for every x in (a,b)"],
                 'f is constant on (a,b)',['proof_on_connected_interval']):
        return mvt_certificate(lib,'zero_derivative_connected',dict(domain='(a,b)'),dict(constant=True),
            'Отрезок между любыми двумя точками лежит внутри исходного интервала. Приращение равно внутренней производной на длину по Лагранжу.')
    if (a,c,o)==(['f is differentiable on R',"f'(x)=k on R with k constant"],
                 'All and only such functions are f(x)=kx+b',['prove_form_and_converse']):
        return mvt_certificate(lib,'zero_derivative_connected',dict(domain='R'),dict(form='k*x+B'),
            'Вычесть kx, тогда у остатка нулевая производная и он постоянен. Обратно, производная kx+B равна k.')
    if (a,c,o)==(['f^(n)(x)=0 throughout an interval','n is a positive integer'], 'Characterize f',
                 ['all_functions_with_nth_derivative_identically_zero']):
        return mvt_certificate(lib,'zero_derivative_connected',dict(domain='interval',order='positive integer n'),dict(maximum_polynomial_degree='n-1'),
            'У f^(n−1) нулевая производная, значит она постоянна. Вычесть подходящую кратную x^(n−1), чтобы занулить производную порядка n−1.',
            'Повторить до нулевого порядка. Обратное следует из понижения степени многочлена каждым дифференцированием.')
    if (a,c,o)==(['f is smooth on R','n is a fixed natural number','for every x there exists n_x in {1,...,n} with f^(n_x)(x)=0'],
                 'f is a polynomial',['proof_with_position_dependent_derivative_order']):
        return mvt_certificate(lib,'zero_derivative_connected',dict(domain='R',finite_closed_cover=True),dict(maximum_polynomial_degree='n-1'),
            'Замкнутые нулевые множества производных порядков 1..n покрывают R. Их внутренности имеют плотное объединение.',
            'Иначе в некотором открытом интервале можно последовательно выбрать вложенные непустые открытые интервалы вне каждого замкнутого множества.',
            'На каждой внутренности f^(n)=0 дифференцированием местного тождества. По непрерывности это верно везде, после чего применяется случай одной нулевой производной.')
    if (a,c,o)==(['y is differentiable on R','lambda is constant',"y'=lambda*y on R"],
                 'All and only solutions have form y=C*exp(lambda*x) with arbitrary constant C',['prove_form_and_converse']):
        return mvt_certificate(lib,'zero_derivative_connected',dict(domain='R',multiplier='exp(-lambda*x)>0'),dict(form='C*exp(lambda*x)'),
            'Умножить на exp(−λx). По правилу произведения производная результата exp(−λx)(y′−λy)=0.',
            'По Лагранжу множимое произведение постоянно. Обратная подстановка в дифференциальное тождество даёт все C.')
    raise Unsupported('Не удалось связать нулевую производную с исходным тождеством на всём интервале')


INTERVAL_CLAIMS=tuple(re.compile(p) for p in (
    r'Последовательные производные (\w+) и (\w+) совпадают до порядка (\w+)−1 в (\w+)\. Производная порядка \3 первой строго больше справа\. Доказать строгое неравенство справа\.',
    r'Пусть φ,ψ n раз дифференцируемы, φ\^\(k\)\(x₀\)=ψ\^\(k\)\(x₀\) для k=0,\.\.\.,n−1 и φ\^\(n\)\(x\)>ψ\^\(n\)\(x\) при x>x₀\. Доказать φ\(x\)>ψ\(x\) при x>x₀\.',
    r'Доказать строгую монотонность P\(x\)=a₀\+a₁x\+…\+aₙxⁿ \(n≥1, aₙ≠0\) на каждом из интервалов \(−∞,−x₀\), \(x₀,\+∞\) при достаточно большом x₀>0\.',
    r'Доказать строгую монотонность непостоянной R\(x\)=\(a₀\+…\+aₙxⁿ\)/\(b₀\+…\+bₘxᵐ\), aₙbₘ≠0, на \(−∞,−x₀\) и \(x₀,\+∞\) при достаточно большом x₀>0\.',
    r'Доказать возрастание \(1\+1/x\)\^x на интервалах \(−∞,−1\) и \(0,\+∞\)\.',
    r'Для x>0 доказать \(1\+1/x\)\^x<e<\(1\+1/x\)\^\(x\+1\)\.',
    r'Доказать x\^α−1>α\(x−1\) для α≥2, x>1\.',
    r'Доказать x\^\(1/n\)−a\^\(1/n\)<\(x−a\)\^\(1/n\) при n>1, x>a>0\.',
    r'Доказать на \(0,\+∞\) выпуклость снизу для xⁿ \(n>1\), eˣ, x ln x и выпуклость сверху для xⁿ \(0<n<1\), ln x\.',
))


def interval_comparison(task,lib):
    mvt_packet(task,{'statement','requested_output'})
    e=task['statement'];n=next(j for j,p in enumerate(INTERVAL_CLAIMS) if p.fullmatch(e));o=task['requested_output']
    mvt_require(o==(['all_five_convexity_claims'] if n==8 else ['proof']),'Не поддержана вся область запрошенных утверждений')
    if n<2:
        return mvt_certificate(lib,'iterate_derivative_comparison',dict(base_point='x₀',scope='right of x₀'),
            dict(strict=True,auxiliary='φ−ψ'),
            'Вычесть вторую функцию. Из совпадения всех начальных коэффициентов получаем нулевые значения производных до порядка n−1.',
            'Применить поиск промежуточной точки к каждой следующей производной на отрезке от x₀ до x. Положительный верхний порядок последовательно даёт все нижние.')
    if n<4:
        return mvt_certificate(lib,'iterate_derivative_comparison',dict(scope='two tails',original_function_nonconstant=True),
            dict(strict=True,auxiliary='leading term of the derivative numerator'),
            'В полиноме производная непостоянной функции ненулевая. В дроби знак определяется P′Q−PQ′, который иначе сделал бы функцию постоянной.',
            'Ненулевой старший член доминирует обеими сторонами достаточно далеко. У дроби там также ненулевой исходный знаменатель, и его квадрат положителен.',
            'У производной строгий постоянный знак на каждом хвосте. Применить Лагранжа на отрезках внутри каждого хвоста.')
    if n<6:
        return mvt_certificate(lib,'derivative_bound_for_increments',dict(domain='positive log argument',auxiliary='log1p(t)−t/(1+t)'),
            dict(proved=e),
            'Для t>−1 функция H(t)=ln(1+t)−t/(1+t) имеет H(0)=0 и H′(t)=t/(1+t)², значит H(t)>0 при t≠0.',
            'При t=1/x исходное выражение положительно в обеих открытых ветвях. Производная его логарифма равна H(1/x).'
            if n==4 else 'При t=1/x>0 получаем нижнюю оценку логарифма. Верхняя ln(1+t)<t следует из производной t/(1+t) разности t−ln(1+t).',
            'Применить Лагранжа отдельно на каждой ветви.' if n==4 else 'Умножить на положительные x и x+1 соответственно и применить возрастающую экспоненту.')
    if n<8:
        if n==6:
            scope='x>1, α≥2';expr='x^a-1-a*(x-1)';params=['a']
            argument='Разность имеет нуль при x=1 и производную α(x^(α−1)−1)>0 при x>1.'
        else:
            scope='x>a>0, n>1';expr='(x-a)^(1/n)-x^(1/n)+a^(1/n)';params=['a','n']
            argument='Разность начинается с нуля при x=a и имеет положительную производную p((x−a)^(p−1)−x^(p−1)), так как 0<p=1/n<1.'
        f=m.parse(expr,'x',params);d,tree=table(f,'x',lib)
        return mvt_certificate(lib,'iterate_derivative_comparison',dict(domain=scope,auxiliary=f),dict(proved=e,derivative=d),
            argument,'Нуль в начальной точке и знак производной на открытой ветви дают сравнение по Лагранжу.',table_steps=tree)
    variants=(('x^n',['n'],'n>1','positive'),('exp(x)',[],'','positive'),('x*ln(x)',[],'','positive'),
              ('x^n',['n'],'0<n<1','negative'),('ln(x)',[],'','negative'))
    checks=[];trees=[]
    for f,p,h,s in variants:
        d,tree=table(m.parse(f,'x',p),'x',lib);d2,tr=table(d,'x',lib)
        checks.append(dict(function=f,hypothesis=h,second_derivative=d2,sign=s));trees.extend([*tree,*tr])
    return mvt_certificate(lib,'iterate_derivative_comparison',dict(domain='x>0',convexity='all five supplied functions'),
        dict(checks=checks),'Дважды дифференцировать каждую функцию. Знак степенной ветви задаёт n(n−1), остальные знаки следуют из x>0.',
        'На любом внутреннем отрезке сравнить два секущих наклона по Лагранжу и знаку второй производной.',table_steps=trees)


def mvt_goal(task,lib):
    audit=endpoint_limit_and_trip_bounds(task,lib)
    if audit is not None:return audit
    kind=task['kind']
    if kind.startswith(('rolle_','iterated_rolle','polynomial_root_interlacing','orthogonal_polynomial_root_location')):
        return rolle_goals(task,lib)
    if kind in ('parallel_tangent_chord','mean_value_points','mean_value_interpolation'):
        return interpolation(task,lib)
    if kind in ('derivative_characterizes_function','identity_from_equal_derivatives','inverse_trig_identity_on_domain'):
        return derivative_identities(task,lib)
    if kind=='proof_about_real_functions':return interval_comparison(task,lib)
    return mean_value_theory(task,lib)


INF={'-inf','+inf'}
SUPERS=str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')
SOURCE_META={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','literal_requirement',
             'heading_page','source_continues_on_pdf_page','continued_on_pdf_page'}
LOCAL_NAME=r'[A-Za-z_][A-Za-z_0-9]*'
ROOT_LEVEL_HEADINGS=(
    'Определить число вещественных корней и отделить эти корни.',
    'При каком условии один вещественный корень? Изобразить соответствующую область на плоскости (p,q).',
    'При каком условии три вещественных корня? Изобразить соответствующую область на плоскости (p,q).',
)
ROOT_LEVEL_OUTPUTS=(['all_real_root_counts_and_isolating_intervals'],
                    ['conditions_for_one_real_roots'],['conditions_for_three_real_roots'])


def insist(condition,reason):
    if not condition:raise Unsupported(reason)


def text_form(s):
    return re.sub('[⁰¹²³⁴⁵⁶⁷⁸⁹]+',lambda a:'^'+a[0].translate(SUPERS),s).replace('−','-')


def number_names(text,variable):
    return sorted(set(re.findall(LOCAL_NAME,text))-m.FUNCTIONS-set(m.ALIASES)-{'e','pi',variable})


def local_geometry_certificate(lib,method,scope,value,*argument,**data):
    insist(method in lib.data.get('local_geometry_transitions',()),'Transition absent from the active library')
    return dict(theorem='local_geometry.'+method,scope=scope,argument=argument,**data),value


def level_input(task):
    fields={'kind','id','source','schema','transcription','given','variable','requested_output'}
    meta=task.get('source',{})
    insist(not set(task)-fields and isinstance(meta,dict) and not set(meta)-SOURCE_META and
           meta.get('literal_requirement') in (None,*ROOT_LEVEL_HEADINGS),
           'Additional conditions of the root problem are not bound')
    body,*scope=text_form(task['given']).split(',')
    insist(len(scope)<=1 and body.count('=')==1,'One level equation and at most one explicit interval are required')
    name=task.get('variable','x');par=number_names(body,name)
    insist(len(par) in (1,2),'A parametrized level equation is required')
    lhs,rhs=(m.parse(s.strip(),name,par) for s in body.split('='));x=('v',name)
    domain=scope[0].strip() if scope else None
    match=re.fullmatch(r'(.+?)\s*(<=|<)\s*'+re.escape(name)+r'\s*(<=|<)\s*(.+)',domain or '')
    insist(domain is None or match,'The original interval has not been parsed')
    limits=('-inf','+inf',False,False) if match is None else (
        m.simplify(m.parse(match[1],None)),m.simplify(m.parse(match[4],None)),match[2]=='<=',match[3]=='<=')
    return name,x,par,lhs,rhs,limits


def split_level(lhs,rhs,p):
    raw=('add',lhs,('mul',q(-1),rhs));guards=domain_conditions(raw)
    insist(not any(m.contains(t,p) for _,t in guards),'An original parameter-dependent domain needs a separate proof')
    n,d=m.rational_form(raw)
    insist(not any(m.contains(a,p) for mon in d for a,_ in mon),'A parameter denominator cannot be cleared')
    parts=[{},{}]
    for mon,z in n.items():
        factors=dict(mon);k=factors.pop(p,0)
        insist(k in (0,1) and not any(m.contains(a,p) for a in factors),'The equation is not affine in the free level')
        parts[k][tuple((a,j) for a,j in mon if a!=p)]=z
    den=m.poly_expr(d);a,b=(m.div(m.poly_expr(f),den) for f in parts)
    insist(b!=ZERO,'The requested level does not affect the equation')
    return m.div(m.neg(a),b),a,b,guards


def value_at(expr,x,v,ctx):
    z=m.substitute(expr,{x:v})
    insist(m.constant_defined(z,ctx),'A source endpoint is undefined')
    return m.simplify(z)


def quadratic_point(z):
    return q(z.a) if not z.b else m.add(q(z.a),m.mul(q(z.b),('sqrt',q(z.d))))


def rational_profile(h,name,guards,interval):
    """Derive the cuts from the derivative, original guards and interval. No root hints."""
    v=('v',name);p,d=poly.rf(h,name);g=poly.pgcd(p,d);p=poly.pdiv(p,g)[0];d=poly.pdiv(d,g)[0]
    derivative=poly.quotient_derivative_numerator(p,d)
    insist(any(derivative),'A constant level profile can give an entire interval of roots')
    holes=[]
    for kind,e in guards:
        insist(kind=='nonzero','A nonrational original domain requires a different range profile')
        a,b=poly.rf(e,name)
        insist(any(a),'The original domain is empty')
        holes.extend(rational_roots(a));holes.extend(rational_roots(b))
    def cut(u):
        if isinstance(u,str):return u
        n=m.num(u);insist(n is not None,'Exact rational cuts are required for the rational profile')
        return line.Quadratic(n)
    a,b=map(cut,interval[:2]);lc,rc=interval[2:]
    insist(line.compare(a,b)<0,'The requested interval is empty or a singleton')
    zones=[]
    for z in sorted([*holes,*rational_roots(d),*rational_roots(derivative)],key=cmp_to_key(line.compare)):
        if line.compare(a,z)<0 and line.compare(z,b)<0 and (not zones or line.compare(zones[-1],z)!=0):zones.append(z)
    def term(z):return z if isinstance(z,str) else quadratic_point(z)
    def hole(z):return any(line.compare(z,u)==0 for u in holes)
    levels={'-inf':'-inf','+inf':'+inf'}
    def remember(y):
        for t,z in levels.items():
            if line.compare(y,z)==0:return t
        t=term(y);levels[t]=y
        return t
    def limit(z,sample):
        if isinstance(z,str):
            degree=len(p)-len(d)
            if degree<0:return remember(line.Quadratic(0))
            if degree==0:return remember(line.Quadratic(p[-1]/d[-1]))
            return '+inf' if p[-1]*d[-1]*((-1)**degree if z=='-inf' else 1)>0 else '-inf'
        if line.peval(d,z).sign():return remember(ordinate(p,d,z))
        return '+inf' if line.peval(p,z).sign()*line.sign(peval(d,sample))>0 else '-inf'
    ends=[a,*zones,b];branches=[];points=[]
    for lo,hi in zip(ends,ends[1:]):
        sample=line.between(lo,hi);direction=line.sign(peval(derivative,sample))
        insist(direction in (-1,1),'Every open branch needs a strict derivative sign')
        branches.append((term(lo),term(hi),limit(lo,sample),limit(hi,sample),direction))
    for i,z in enumerate(ends):
        if not isinstance(z,str) and line.peval(d,z).sign() and not hole(z) and (0<i<len(ends)-1 or (lc if not i else rc)):
            points.append((term(z),remember(ordinate(p,d,z))))
    return branches,points,dict(rational_numerator=tuple(map(q,p)),rational_denominator=tuple(map(q,d)),
        derivative_numerator=tuple(map(q,derivative)),excluded_cuts=[term(u) for u in holes],
        ordered_levels=sorted(levels,key=cmp_to_key(lambda u,w:line.compare(levels[u],levels[w]))))


def level_order(branches,points,order=None):
    candidates={v for a,b,l,r,s in branches for v in (l,r)}|{v for _,v in points}|INF
    if order is None:
        ctx=m.context(dict(variable='x'))
        def compare(a,b):
            if a==b or isinstance(a,str) or isinstance(b,str):return line.compare(a,b)
            s=m.sign(m.add(a,m.neg(b)),ctx)
            insist(s in (-1,1),'Distinct endpoint expressions have no proved order')
            return s
        order=sorted(candidates,key=cmp_to_key(compare))
    insist(candidates==set(order) and len(order)==len(candidates) and order[0]=='-inf' and order[-1]=='+inf',
           'The exact distinct endpoint levels must all be ordered')
    ranks={v:j for j,v in enumerate(order)}
    for _,_,a,b,s in branches:
        insist((ranks[b]-ranks[a])*s>0,'Endpoint traces disagree with the proposed strict branch direction')
    return order,ranks


def roots_from_profile(branches,points,parameter,order=None,always=()):
    order,ranks=level_order(branches,points,order)
    def case(condition,rank,exact=False):
        intervals=[];isolated=list(always)
        for a,b,l,r,d in branches:
            lo,hi=sorted((ranks[l],ranks[r]))
            if (lo<rank<hi if exact else lo<=rank<hi):intervals.append((a,b))
        if exact:isolated.extend(x for x,y in points if ranks[y]==rank)
        return dict(level_condition=condition,root_count=len(intervals)+len(isolated),
                    open_intervals_with_one_root=intervals,isolated_roots=isolated)
    cases=[]
    for j,(a,b) in enumerate(zip(order,order[1:])):
        cases.append(case((a,'<',parameter,'<',b),j))
        if b!='+inf':cases.append(case((parameter,'=',b),j+1,True))
    return cases


def exact_profile(h,name,guards,interval,lib):
    try:return rational_profile(h,name,guards,interval)
    except poly.NotRational:pass
    x=('v',name);ctx=m.context(dict(variable=name));num,den=m.rational_form(h)
    insist(len(num)==len(den)==1,'A new monotone profile is needed for this expression')
    (n,c),=num.items();(d,e),=den.items();c/=e
    insist(c>0,'An orientation-preserving scale is needed')
    C=q(c);rad=lambda u:('sqrt',q(u))
    def scale(t):return m.mul(C,t)
    def guard_scope(logarithm=False,nonzero=False):
        for g in guards:
            k,u=g
            if known_guard(g,ctx):continue
            if logarithm and k=='positive' and same_value(u,x):continue
            if nonzero and k=='nonzero':
                P,D=poly.rf(u,name)
                if any(P) and len(D)==1 and not any(P[:-1]):continue
            raise Unsupported('An extra original restriction would remove part of a proposed branch')
    def finish(branches,points,order,proof,**data):
        df,steps=table(h,name,lib)
        return branches,points,dict(ordered_levels=order,derivative=df,table_steps=steps,
            sign_argument=proof,**data)
    entire=interval==('-inf','+inf',False,False)
    if n==((('ln',x),1),) and d==((x,1),) and entire:
        guard_scope(logarithm=True,nonzero=True);E=('exp',ONE);peak=scale(m.div(ONE,E))
        return finish([(ZERO,E,'-inf',peak,1),(E,'+inf',peak,ZERO,-1)],[(E,peak)],
            ['-inf',ZERO,peak,'+inf'],
            'На x>0 знак производной равен знаку 1−ln x. При x→0+ отношение стремится к −∞, при x→+∞ к 0 сверху.',
            original_domain='x>0')
    if len(n)==len(d)==1 and n[0][0][0]=='exp' and n[0][1]==1 and d[0][0]==x and entire:
        rate,divisor=poly.rf(n[0][0][1],name);power=d[0][1]
        insist(len(rate)==2 and len(divisor)==1 and rate[1]>0 and power>0 and power%2==0,
               'The growing exponential profile needs an even positive divisor power')
        guard_scope(nonzero=True);edge=q(power*divisor[0]/rate[1]);peak=value_at(h,x,edge,ctx)
        return finish([('-inf',ZERO,ZERO,'+inf',1),(ZERO,edge,'+inf',peak,-1),(edge,'+inf',peak,'+inf',1)],
            [(edge,peak)],['-inf',ZERO,peak,'+inf'],
            'После выделения положительной экспоненты знак задают ax−p и x^(p+1). На отрицательном хвосте экспонента затухает, на положительном обгоняет степенной делитель.',
            original_domain='x!=0',linear_rate=q(rate[1]/divisor[0]),denominator_power=power)
    if len(n)==1 and n[0][0][0]=='cosh' and n[0][1]==1 and d==((x,1),) and entire:
        phase=n[0][0][1];p,d0=poly.rf(phase,name)
        insist(len(p)==2 and p[0]==0 and len(d0)==1,'An odd linear hyperbolic phase is required')
        guard_scope(nonzero=True);w=q(abs(p[1]/d0[0]));u=('s','__c');minus=m.neg(u)
        level=m.div(scale(('cosh',m.mul(w,u))),u);below=m.neg(level)
        return finish([('-inf',minus,'-inf',below,1),(minus,ZERO,below,'-inf',-1),
            (ZERO,u,'+inf',level,-1),(u,'+inf',level,'+inf',1)],[(minus,below),(u,level)],
            ['-inf',below,level,'+inf'],
            'На положительной ветви знак производной задаёт wx tanh(wx)−1. Это строго возрастающая функция от −1 до +∞, её единственный нуль задаёт c. Нечётность исходного отношения отражает ветвь.',
            original_domain='x!=0',auxiliary_definition=dict(variable=u,condition='positive_unique_root',
                equation=(m.mul(m.mul(w,u),('tanh',m.mul(w,u))),ONE)))
    if len(n)==2 and not d:
        components={a[0]:(a[1],j) for a,j in n};sg=components.get('sin');cg=components.get('cos')
        insist(sg and cg and sg[0]==cg[0] and sg[1]>0 and cg[1]==1,'The trigonometric level needs a sine power times cosine')
        phase=sg[0];p,d0=poly.rf(phase,name)
        insist(len(p)==2 and p[0]==0 and p[1]>0 and len(d0)==1,'The phase must be an increasing linear coordinate')
        a=q(p[1]/d0[0]);p=sg[1];upper=m.div(('pi',),a)
        insist(interval[0]==ZERO and same_value(interval[1],upper),'The source interval must be a full positive sine half-wave')
        guard_scope();at=m.div(('atan',rad(p)),a);right=m.add(upper,m.neg(at))
        peak=scale(m.div(('rpow',q(Fraction(p,p+1)),q(Fraction(p,2))),rad(p+1)));low=m.neg(peak)
        points=[(at,peak),(right,low)]
        if interval[2]:points.insert(0,(ZERO,ZERO))
        if interval[3]:points.append((upper,ZERO))
        return finish([(ZERO,at,ZERO,peak,1),(at,right,peak,low,-1),(right,upper,low,ZERO,1)],points,
            ['-inf',low,ZERO,peak,'+inf'],
            'Внутри полуволны синус положителен. После выделения положительных множителей знак задаёт (p+1)cos²−1. Нули находятся в двух симметричных точках. Значения выводятся из sin²+cos²=1.',
            source_interval=interval,sine_power=p,phase=phase)
    raise Unsupported('The derivative or boundary levels of this elementary profile remain open')


def level_roots(task,lib):
    name,x,pars,lhs,rhs,interval=level_input(task)
    if len(pars)==2:return depressed_cubic(task,lib,name,x,pars,lhs,rhs,interval)
    insist(task.get('requested_output') in (None,['all_real_root_counts_and_isolating_intervals']),
           'The root equation adds an unrepresented output')
    parameter=('s',pars[0]);h,A,B,raw_guards=split_level(lhs,rhs,parameter)
    p,d=poly.rf(B,name);fixed=[];splits=[];ctx=m.context(dict(variable=name))
    def guard_at(k,g,z,t):
        original=m.substitute(g,{x:t})
        if known_guard((k,original),ctx):return True
        try:
            n,d=poly.rf(g,name);ds=line.peval(d,z).sign()
            if not ds:return False
            sign=line.peval(n,z).sign()*ds
        except (poly.NotRational,poly.Undefined):
            sign=m.sign(original,ctx)
        insist(sign in (-1,0,1),'An original guard at a vanishing level coefficient remains undecided')
        return sign!=0 if k=='nonzero' else sign==1 if k=='positive' else sign>=0
    for z in sorted(set(rational_roots(p)),key=cmp_to_key(line.compare)):
        t=quadratic_point(z)
        if not line.peval(d,z).sign():continue
        if not all(guard_at(k,g,z,t) for k,g in raw_guards):continue
        a=value_at(A,x,t,ctx);n=m.sign(a,ctx)
        insist(n in (-1,0,1),'The original equation on a vanishing level coefficient is undecided')
        if n==0:
            insist(interval==('-inf','+inf',False,False),'A fixed exceptional root must be checked on the printed interval')
            fixed.append(t)
        splits.append((t,a,n))
    guards=tuple(dict.fromkeys([*raw_guards,*domain_conditions(h),('nonzero',B)]))
    branches,points,evidence=exact_profile(h,name,guards,interval,lib)
    cases=roots_from_profile(branches,points,parameter,evidence.pop('ordered_levels'),fixed)
    return local_geometry_certificate(lib,'roots_by_monotone_image',dict(variable=name,parameter=parameter,lhs=lhs,rhs=rhs,
        original_guards=raw_guards,interval=interval,exceptional_coefficients=splits),dict(cases=cases),
        'Выделить уровень как отдельный параметр. При нулевом коэффициенте проверить исходное уравнение отдельно.',
        'На каждой открытой строго монотонной ветви промежуточное значение даёт ровно один корень при строгом сравнении с обоими следами.',
        'На граничном уровне отдельно добавить только допустимые точки. Параметрические условия исчерпывают прямую.',
        transformed_function=h,branches=branches,endpoint_points=points,**evidence)


def depressed_cubic(task,lib,name,x,pars,lhs,rhs,interval):
    labels=task.get('requested_output');supported=(['conditions_for_one_real_roots'],['conditions_for_three_real_roots'])
    insist(labels in supported and interval==('-inf','+inf',False,False),'An exact cubic root-count target on R is required')
    a,b=(('s',p) for p in pars);raw=('add',lhs,('mul',q(-1),rhs))
    insist(not domain_conditions(raw),'The original cubic domain has a hole')
    if same_value(raw,m.add(m.power(x,3),m.add(m.mul(b,x),a))):a,b=b,a
    insist(same_value(raw,m.add(m.power(x,3),m.add(m.mul(a,x),b))) or
        same_value(m.neg(raw),m.add(m.power(x,3),m.add(m.mul(a,x),b))),
        'A depressed monic cubic with two free coefficients is required')
    discriminant=m.add(m.mul(q(4),m.power(a,3)),m.mul(q(27),m.power(b,2)))
    return local_geometry_certificate(lib,'roots_by_monotone_image',dict(variable=name,p=a,q=b,original_equation=(lhs,rhs)),
        dict(target_real_count=1 if labels==supported[0] else 3,critical_discriminant=discriminant,
            counts=[dict(sign=1,distinct=1,with_multiplicity=1),dict(sign=-1,distinct=3,with_multiplicity=3),
                    dict(sign=0,origin=False,distinct=2,with_multiplicity=3),dict(sign=0,origin=True,distinct=1,with_multiplicity=3)]),
        'Если p≥0, кубическая функция строго возрастает. При p<0 критические точки ±sqrt(−p/3).',
        'Произведение двух критических значений равно q²+4p³/27. Сопоставить строгие знаки и хвосты для всех трёх ветвей.',
        'Нулевой уровень на общей границе даёт один двукратный корень, а при p=q=0 возникает трёхкратный корень.')


def tail_envelope(task,lib):
    fields={'kind','id','source','given','requested_output'};meta=task.get('source',{})
    insist(not set(task)-fields and not set(meta)-SOURCE_META and meta.get('literal_requirement') in
           (None,'Определить M(x)=sup f и m(x)=inf f и построить их графики.') and
           task.get('requested_output')==['lower_and_upper_envelopes'],'The moving half-line and both bounds are required')
    given=text_form(task['given'])
    pattern=rf'f\(({LOCAL_NAME})\)\s*=\s*(.+),\s*({LOCAL_NAME})\s*<\s*\1\s*<\s*\+inf(?:inity|ty)?'
    parsed=re.fullmatch(pattern,given);insist(parsed and parsed[1]!=parsed[3],'An open moving right half-line is required')
    coord,expr,cutoff=parsed.groups();x=('v',coord);h=m.parse(expr,coord);guards=domain_conditions(h)
    branches,pts,data=rational_profile(h,coord,guards,('-inf','+inf',False,False))
    insist(not data['excluded_cuts'] and all(m.num(y) is not None for _,y in pts) and all(m.num(z) is not None for z,_ in pts),
           'An unresolved source hole or algebraic-level comparison remains on the moving half-line')
    p,d=poly.rf(h,coord);tail=branches[-1][3]
    fixed=[(line.Quadratic(m.num(a)),line.Quadratic(m.num(v))) for a,v in pts]
    levels=[v for _,v in fixed]
    if not isinstance(tail,str):
        insist(m.num(tail) is not None,'A rational tail level is required');levels.append(line.Quadratic(m.num(tail)))
    cuts=[a for a,_ in fixed]
    for v in levels:
        eq=poly.pa(p,line.pscale(d,-v.a));cuts.extend(rational_roots(eq))
    cuts=sorted(set(cuts),key=cmp_to_key(line.compare));ends=['-inf',*cuts,'+inf'];u=('v',cutoff)
    def case(v):
        candidate=[(ordinate(p,d,v),m.substitute(h,{x:u}),False),
                   (tail if isinstance(tail,str) else line.Quadratic(m.num(tail)),tail,False)]
        candidate.extend((y,quadratic_point(y),True) for a,y in fixed if line.compare(a,v)>0)
        def bound(direction):
            y,label,attained=sorted(candidate,key=cmp_to_key(lambda a,b:direction*line.compare(a[0],b[0])))[0]
            # A limiting value at the moving endpoint may also occur strictly inside the half-line.
            eligible=any(k[2] and line.compare(k[0],y)==0 for k in candidate)
            return dict(value=label,attained=eligible)
        return dict(lower=bound(1),upper=bound(-1))
    def term(z):return z if isinstance(z,str) else quadratic_point(z)
    spans=[dict(open_interval=(term(a),term(b)),**case(line.Quadratic(line.between(a,b)))) for a,b in zip(ends,ends[1:])]
    points=[dict(at=term(z),**case(z)) for z in cuts]
    return local_geometry_certificate(lib,'bounds_on_moving_open_domains',dict(variable=coord,cutoff=cutoff,raw_guards=guards),
         dict(open_cells=spans,boundary_points=points),
         'Для открытого хвоста сравнить правый след в x, предел на бесконечности и значения строго правых стационарных точек.',
         'Набор допустимых точек меняется только при пересечении абсциссы стационарной точки. Порядок значений меняется только при совпадении правого следа с постоянным уровнем.',
         'Разделить прямую по всем этим равенствам. В каждой ячейке сравнить кандидатов, не засчитывая открытый край как точку достижения.',
         critical_points=pts,tail_limit=tail,deterministic_level_cuts=list(map(term,cuts)))


def parametric_packet(task):
    local=task['kind']=='parametric_local_derivative';src=task.get('source',{})
    base={'kind','id','source','schema','transcription','coordinates','parameter'}
    fields={'requested_output','targets'} if local else {'parameters','stated_conditions','orders','requested_output'}
    headings=(None,'Построить эскиз, найти y′_x, значения при x=0 и x=-1 и все точки M с y′=0.') if local else (
        None,'Найти производные y′_x (параметры положительны).',
        'Найти указанное отношение дифференциалов (производную одной функции по другой).')
    insist(not set(task)-base-fields and isinstance(src,dict) and not set(src)-SOURCE_META-{'parameter_rename'} and
           src.get('literal_requirement') in headings,'An additional coordinate condition needs a separate proof')
    if local:
        insist(task.get('requested_output')==['derivative_formula','derivatives_at_requested_x','all_zero_derivative_points'],
               'All source slope and stationary point requests must be bound')
    else:
        insist(not task.get('parameters') and not task.get('stated_conditions') and task.get('orders')==[1] and
               task.get('requested_output')==['derivatives_as_functions_of_parameter'],'Full first derivative of a fixed rational chart is required')
    n=task['parameter'];x=('v',n);parsed=tuple(m.parse(text_form(e),n) for e in task['coordinates'])
    insist(len(parsed)==2,'A planar chart requires two coordinates')
    return n,x,parsed


def rational_coordinate_jet(task,lib):
    name,v,xy=parametric_packet(task);X,Y=xy;dx,xproof=table(X,name,lib);dy,yproof=table(Y,name,lib)
    ctx=m.context(dict(variable=name));polys=[poly.rf(e,name) for e in (X,Y,dx,dy)]
    (xp,xd),(yp,yd),(p,dp),(r,dr)=polys
    insist(any(p),'The independent coordinate is constant throughout the source')
    guards=tuple(dict.fromkeys(g for e in xy for g in domain_conditions(e)))
    natural=[]
    for rel,e in guards:
        insist(rel=='nonzero','A nonrational coordinate guard is unresolved')
        a,b=poly.rf(e,name);insist(any(a),'The original chart has empty domain')
        natural.extend([*rational_roots(a),*rational_roots(b)])
    def equal(a,b):return line.compare(a,b)==0
    def allowed(z):return all(not equal(z,h) for h in natural)
    def roots(p):return sorted(set(rational_roots(p)),key=cmp_to_key(line.compare))
    singular=[t for t in roots(p) if allowed(t)]
    def differentiate(p):return poly.trim([i*c for i,c in enumerate(p) if i] or [Fraction(0)])
    def difference_order(a,b,z):
        # Order of P(t)/Q(t)-P(z)/Q(z), with Q(z) != 0.
        n=line.peval(a,z);d=line.peval(b,z)
        insist(d.sign()!=0,'An original coordinate denominator vanishes at the candidate')
        for j in range(1,max(len(a),len(b))):
            a,b=differentiate(a),differentiate(b)
            lead=line.peval(a,z).mul(d).add(line.peval(b,z).mul(n).neg())
            if lead.sign():
                from math import factorial
                return j,lead.scale(Fraction(1,factorial(j)))
        return None,None
    def local(z):
        a,A=difference_order(xp,xd,z);b,B=difference_order(yp,yd,z)
        insist(a is not None,'The independent coordinate has no nonconstant germ')
        if b is None or b>a:answer=ZERO
        else:
            # The jets in difference_order are scaled by Q(z)^2.
            xx=line.peval(xd,z);yy=line.peval(yd,z)
            w=B.mul(xx.mul(xx));d=A.mul(yy.mul(yy));sign=w.sign()*d.sign()
            if b==a:
                conjugate=line.Quadratic(d.a,-d.b,d.d)
                answer=quadratic_point(w.mul(conjugate).scale(1/(d.a*d.a-d.b*d.b*d.d)))
            else:answer=dict(infinite_on_parameter_sides=(sign*(-1)**(a-b),sign))
        return dict(parameter=quadratic_point(z),ordered_germs=(a,b),
            independent_coordinate_sides=(A.sign()*(-1)**a,A.sign()),derivative=answer)
    stationary=[local(z) for z in singular];tangent=m.div(dy,dx)
    result=dict(formula=tangent,regular_condition=('nonzero',dx),exceptional=stationary)
    if task['kind']=='parametric_local_derivative':
        insist(any(r),'The zero-slope locus includes an entire regular branch')
        targets=[]
        def point(z):return tuple(quadratic_point(ordinate(*p,z)) for p in ((xp,xd),(yp,yd)))
        for text in task['targets']:
            a=m.num(m.parse(text,None));insist(a is not None,'A rational coordinate level is required')
            locations=roots(poly.pa(xp,line.pscale(xd,-a)))
            targets.append(dict(coordinate=q(a),points=[dict(point=point(z),parameter=quadratic_point(z),
                derivative=local(z)['derivative'] if any(equal(z,h) for h in singular) else
                    quadratic_point(ordinate(poly.pm(r,dp),poly.pm(dr,p),z))) for z in locations if allowed(z)]))
        zeros=[z for z in roots(r) if allowed(z) and not any(equal(z,h) for h in singular)]
        zeros.extend(z for z,row in zip(singular,stationary) if row['derivative']==ZERO)
        result.update(at_requested_x=targets,all_stationary_points=[point(z) for z in zeros])
    return local_geometry_certificate(lib,'relative_coordinate_germs',dict(parameter=name,coordinates=xy,raw_guards=guards),result,
        'На регулярных участках отношение производных следует из цепочки. Первоначальные условия координат проверяются до сокращения.',
        'При нулевой скорости x сравнить первый ненулевой порядок обоих исходных приращений по параметру. Чётность x указывает, на какой стороне координаты существуют ветви.',
        'Уровни x и нули наклона получить из точных уравнений с исключением недопустимых точек.',
        table_steps=[*xproof,*yproof])


def deviation_optimum(task,lib):
    meta=task.get('source',{})
    headings=(None,'Найти q, минимизирующее E_P=sup abs(P(x)) на [-1,1].',
        'Найти b наименьшего абсолютного отклонения и величину этого отклонения.')
    insist(not set(task)-{'kind','id','source','given'} and not set(meta)-SOURCE_META and
           meta.get('literal_requirement') in headings,'An additional approximation norm or hypothesis is unresolved')
    t=text_form(task['given']);coords=re.fullmatch(rf'{LOCAL_NAME}\(({LOCAL_NAME})\)\s*=\s*(.+),\s*\1 in \[([^,]+),([^,]+)\]',t)
    if coords:
        name,expr,a,b=coords.groups();domain=(m.parse(a,None),m.parse(b,None),True,True)
        names=number_names(expr,name);insist(len(names)==1,'A single free coefficient is required')
        p,=names;x=('v',name);v=('s',p)
        h,A,B,guards=split_level(m.parse(expr,name,[p]),ZERO,v)
        bnum=m.num(B);insist(bnum not in (None,0),'The adjustable coefficient must shift all values equally')
        branches,pts,plan=rational_profile(A,name,guards,domain)
        values=plan['ordered_levels'];bounds=values[1],values[-2];detail=dict(curve=A,domain=domain,branches=branches)
    else:
        match=re.fullmatch(rf'f\s*=\s*([^,]+),\s*g\s*=\s*(.+) on \[({LOCAL_NAME}),({LOCAL_NAME})\]',t)
        insist(match and match[3]!=match[4],'A uniform deviation on a closed interval is required')
        f,g,a,b=match.groups();unknowns=set(number_names(f+' '+g,'x'))-{a,b}
        insist(len(unknowns)==1,'A single additive adjustable coefficient is required');p,=unknowns
        v=('s',p);name='x';x=('v',name);a,b=('s',a),('s',b)
        F,G=(m.parse(e,name,[a[1],b[1],p]) for e in (f,g));_,A,B,guards=split_level(F,G,v)
        bnum=m.num(B);insist(bnum not in (None,0) and not guards,'A constant shift on the original interval is required')
        center=m.div(m.add(a,b),q(2))
        shift=m.simplify(m.add(A,m.neg(m.power(m.add(x,m.neg(center)),2))))
        insist(not m.variable_in(shift,name),'The residual must have its quadratic vertex at the interval midpoint')
        bounds=shift,m.add(shift,m.power(m.div(m.add(b,m.neg(a)),q(2)),2))
        detail=dict(curve=A,domain=(a,b,True,True),source_condition=('<=',a,b),vertex=center)
    lo,hi=bounds;middle=m.div(m.add(lo,hi),q(2))
    return local_geometry_certificate(lib,'center_image_for_uniform_deviation',dict(coefficient=p,shift_weight=B,**detail),
         dict(optimal_coefficient=m.div(m.neg(middle),B),minimum_deviation=m.div(m.add(hi,m.neg(lo)),q(2))),
         'Выделить неизменяемое отклонение и прибавляемую постоянную. Найти крайние значения исходного отклонения на всём отрезке.',
         'Модули обоих крайних значений после сдвига не могут быть меньше половины ширины диапазона. Центрирование даёт равенство и минимально.',
         original_image_bounds=bounds)


def integer_maximum(task,lib,request):
    meta=task.get('source',{});match=re.fullmatch(rf'(.+),\s*({LOCAL_NAME})>=1 integer',task.get('given',''))
    insist(not set(task)-{'kind','id','source','given'} and not set(meta)-SOURCE_META and meta.get('literal_requirement') in
           (None,'Определить наибольший член последовательности.') and match,
           'The original sequence must have natural indices starting at one')
    text,name=match.groups();n=('v',name);e=m.parse(text,name)
    if e[0]!='rpow' or e[1]!=n or not same_value(e[2],m.div(ONE,n)):
        child=dict(kind='discrete_global_extremum',goal=dict(sequence=text,goal='maximum'),
                   assumptions=[name+' is a positive integer'])
        proof=request('Сравнить соседние члены на натуральных индексах',child)
        return local_geometry_certificate(lib,'discrete_maximum_on_ordered_indices',dict(index=name,start=1),proof['value'],
             'Для положительных членов сравнить соседние отношения на исходных целых индексах. Доказать все места смены знака и значения кандидатов.')
    log=m.div(('ln',n),n);profile,points,data=exact_profile(log,name,[('positive',n),('nonzero',n)],('-inf','+inf',False,False),lib)
    turning,=points;insist(same_value(turning[0],('exp',ONE)),'The logarithmic turning point is unresolved')
    # Series for exp(1) gives 2<e<3 by factorials and the geometric tail.
    left,right=2,3;L,R=left**right,right**left;winner=left if L>R else right
    result=dict(extremum='maximum',value=('rpow',q(winner),q(Fraction(1,winner))),all_attaining_indices=[winner,winner])
    return local_geometry_certificate(lib,'discrete_maximum_on_ordered_indices',dict(index=name,start=1),result,
        'Положительные члены можно сравнить после логарифмирования. Производная логарифма даёт единственный поворот при e.',
        'Ряд e=1+1+1/2!+… и строгая геометрическая оценка хвоста дают 2<e<3. Кандидаты — соседние целые 2,3.',
        'Возведение в общую положительную целую степень позволяет сравнить точные целые 2³ и 3².',
        logarithmic_profile=profile,integer_candidates=(left,right),powered_values=(L,R),**data)


def coefficient_points(e,power,name,lib):
    values=[e];proof=[]
    for _ in range(power):
        d,t=table(values[-1],name,lib);values.append(d);proof.extend(t)
    return values,proof


def graph_contact(task,lib):
    meta=task.get('source',{});headings=(None,
        'Подобрать k и b, чтобы прямая имела с кубической кривой касание порядка выше первого.',
        'Подобрать a, b и c, чтобы парабола имела касание второго порядка с экспонентой при x=x0.')
    insist(not set(task)-{'kind','id','source','curves','variable','contact_point','order'} and not set(meta)-SOURCE_META
        and meta.get('literal_requirement') in headings,'A different contact condition remains open')
    name=task['variable'];x=('v',name);left,right=map(text_form,task['curves']);pars=number_names(left,name)
    known=task['contact_point']!='unknown';point_text=task['contact_point'];point_names=number_names(point_text,name) if known else []
    par=[*pars,*point_names];ctx=m.context(dict(variable=name,parameters=par));P=m.parse(left,name,pars);F=m.parse(right,name)
    insist(not domain_conditions(P) and not domain_conditions(F,True),'The contact needs the original smooth domain')
    p,d=m.rational_form(P);coeffs={}
    for mon,c in p.items():
        atoms=dict(mon);k=atoms.pop(x,0);insist(len(atoms)==1 and c==1,'Use independent polynomial coefficients')
        a,power=next(iter(atoms.items()));insist(a in [("s",z) for z in pars] and power==1 and k not in coeffs,
            'A coefficient must determine a unique monomial');coeffs[k]=a
    degree=len(coeffs)-1
    insist(d=={():Fraction(1)} and 1<=degree<=2 and set(coeffs)==set(range(degree+1)) and
           (task['order']==degree if known else task['order']=='>1' and degree==1),
           'The desired matching order must agree with the degree of the free polynomial')
    rows,steps=coefficient_points(F,degree+1,name,lib)
    if known:locations=[m.parse(point_text,None,point_names)]
    else:
        n,d=poly.rf(rows[-1],name);insist(any(n) and len(d)==1,'The next derivative must have isolated real zeros')
        locations=[quadratic_point(z) for z in rational_roots(n)]
    from math import factorial
    results=[]
    for z in locations:
        v=[value_at(y,x,z,ctx) for y in rows[:-1]];formula=ZERO
        for k,value in enumerate(v):formula=m.add(formula,m.mul(m.div(value,q(factorial(k))),m.power(m.add(x,m.neg(z)),k)))
        poly_terms,den=m.rational_form(formula);insist(den=={():Fraction(1)},'A polynomial expansion is required')
        groups={k:{} for k in coeffs}
        for mon,c in poly_terms.items():
            factors=dict(mon);k=factors.pop(x,0);groups[k][tuple(factors.items())]=c
        results.append(dict(point=z,parameters={coeffs[k][1]:m.poly_expr(v) for k,v in groups.items()},
            order=degree if known else '>=2'))
        if known:insist(m.nonzero(value_at(rows[-1],x,z,ctx),ctx),'The next derivatives fail to distinguish exact contact order')
    return local_geometry_certificate(lib,'match_coordinate_jets',dict(reference=F,free_polynomial=P,order=task['order']),dict(contacts=results),
        'Приравнять значения и производные в общей точке. Когда степень свободной кривой уже исчерпана, следующий порядок определяет допустимые точки контакта.',
        'Коэффициенты восстановить из многочлена Тейлора в найденной точке. Для требуемого точного порядка проверить различие следующей производной.',
        table_steps=steps)


def osculating_circle(task,lib):
    from plane_geometry import curvature
    meta=task.get('source',{});headings=(None,'Найти радиус и центр кривизны гиперболы в указанной точке.')
    insist(not set(task)-{'kind','id','source','implicit_curve','at','requested'} and not set(meta)-SOURCE_META
           and meta.get('literal_requirement') in headings and task.get('requested')==['radius','center'],
           'Both pieces of the osculating circle and its specified point are required')
    text=text_form(task['implicit_curve']);insist(text.count('=')==1,'A single implicit equation is required')
    left,right=(m.parse(w,'x',['y']) for w in text.split('='));x=('v','x');y=('s','y');ctx=m.context(dict(variable='x'))
    a,b=(m.parse(str(u),None) for u in task['at']); repl={x:a,y:b}
    insist(all(m.constant_defined(m.substitute(e,repl),ctx) for e in (left,right)) and
           same_value(m.substitute(left,repl),m.substitute(right,repl)),'The specified point is not proved to belong to the original curve')
    f,A,B,raw=split_level(left,right,y)
    insist(m.nonzero(value_at(B,x,a,ctx),ctx),'The chosen graph coordinate is singular at the specified point')
    rows,steps=coefficient_points(f,2,'x',lib);df,d2=rows[1:]
    guards=dict(natural_guards=tuple(dict.fromkeys([*domain_conditions(f),*raw,('nonzero',B)])),
        smooth_guards=domain_conditions(f,True))
    calc,circle=curvature(((x,f),(ONE,df),(ZERO,d2)),guards,'x',[],[],a)
    insist(circle['center'] is not None,'A zero curvature point has no finite center')
    speed=calc['speed_squared'];den=('abs',calc['determinant']);R=m.div(m.mul(speed,('sqrt',speed)),den)
    return local_geometry_certificate(lib,'match_coordinate_jets',dict(original_equation=(left,right),original_point=(a,b),raw_guards=guards),
        dict(point=(a,b),center=circle['center'],radius=R),
        'Сначала доказать принадлежность исходной точке и разрешимость относительно ординаты.',
        'Вычислить две производные в координате x. Смещение центра ортогонально скорости, а скалярное произведение с ускорением равно квадрату скорости.',
        'Радиус есть длина этого смещения. При нулевой кривизне конечный круг отсутствует.',
        table_steps=steps,contact_calculation=calc)


EXTREMA_DEFINITION='Strict maximum/minimum in a two-sided open neighborhood contained in the domain.'


def everywhere_guard(g,coord,ctx):
    if known_guard(g,ctx):return True
    k,u=g
    if k not in ('nonzero','positive','nonnegative'):return False
    try:p,d=poly.rf(u,coord)
    except (poly.NotRational,poly.Undefined):return False
    if not any(p):return k=='nonnegative' and not rational_roots(d)
    if rational_roots(d) or rational_roots(p):return False
    return k=='nonzero' or p[0]*d[0]>0


def regular_scalar_extrema(task,lib):
    meta=task.get('source',{});definition=meta.get('definition');coord=task['variable'];x=('v',coord)
    insist(not set(task)-{'kind','id','source','function','variable','parameters','stated_conditions','method_requirement','requested_output'}
        and not set(meta)-SOURCE_META-{'definition_page','definition'} and definition in (None,EXTREMA_DEFINITION)
        and task.get('requested_output')==['all_strict_local_extrema','justification_on_original_domain'] and
        task.get('method_requirement','any') in ('any','first_derivative_test') and
        not task.get('parameters') and not task.get('stated_conditions'),'Unbound extrema contract or nonregular source')
    raw=m.parse(task['function'],coord);ctx=m.context(dict(variable=coord));D,steps=table(raw,coord,lib)
    def supported_log_guard(g):
        k,u=g
        return k in ('positive','nonnegative','nonzero') and same_value(u,x)
    left=domain_conditions(raw);smooth=domain_conditions(raw,True)
    logs=bool(any(k=='positive' and same_value(u,x) for k,u in left))
    insist(all(everywhere_guard(g,coord,ctx) or logs and supported_log_guard(g) for g in (*left,*smooth)),
        'An original interior or boundary singularity has no derivative coverage')
    # For positive x, remove proved positive factors before substituting u=ln(x).
    from graphs import split_common_factors
    n,d=m.rational_form(D)
    def positive(a):
        return logs and (a==x or a==('sqrt',x)) or a[0]=='exp' and not domain_conditions(a)
    facts=[]
    def reduce_sign(p):
        fs,g=split_common_factors(p,positive);facts.extend(fs.items());return g
    n,d=map(reduce_sign,(n,d));asgn=m.div(n,d)
    roll='__u';atom=('ln',x);u=('v',roll)
    representative=m.substitute(asgn,{atom:u}) if logs else asgn
    # Positive x coordinates may still occur in purely rational derivatives.
    p,q0=poly.rf(representative,roll if logs else coord);num=rational_roots(p);den=rational_roots(q0)
    insist(not den and any(p),'A singular or identically flat derivative requires a separate branch argument')
    nums=sorted(set(num),key=cmp_to_key(line.compare));edges=['-inf',*nums,'+inf'];signs=[];extrema=[]
    for a,b in zip(edges,edges[1:]):
        v=line.between(a,b);signs.append(line.sign(peval(p,v)*peval(q0,v)))
    for a,z,b in zip(signs,nums,signs[1:]):
        if a*b!=-1:continue
        at=quadratic_point(z);point=('exp',at) if logs else at
        value=value_at(raw,x,point,ctx)
        extrema.append(dict(type='strict_maximum' if a>0 else 'strict_minimum',point=point,value=value))
    return local_geometry_certificate(lib,'local_extrema_from_complete_signs',dict(original=raw,scope='x>0' if logs else 'R',guards=left),
         dict(extrema=extrema),'Найти табличную производную и снять только доказанно положительные множители.',
         'В логарифмической координате положительная полуось строго отображается на всю прямую. Иначе остаётся исходная переменная.',
         'Выделить все корни знакового многочлена и проверить знаки на каждом промежутке. Учесть лишь точки, где знак меняется.',
         table_steps=steps,positive_factors=facts,sign_representative=representative,
         sign_cells=signs,critical_coordinates=[quadratic_point(z) for z in nums])


def exponent_profile(task,lib):
    meta=task.get('source',{});kind=task['kind'];name=task.get('variable','x');x=('v',name)
    insist(not set(task)-{'kind','id','source','function','variable','parameters','stated_conditions','method_requirement',
                'requested_output','given_domain'} and not set(meta)-SOURCE_META-{'definition_page','definition','printed_instruction'} and
           meta.get('definition') in (None,EXTREMA_DEFINITION) and task.get('method_requirement','any') in ('any','first_derivative_test'),
           'The original exponent-domain or method obligation is unresolved')
    text=str(task['function']);p=task.get('parameters');guards=task.get('stated_conditions')
    if kind=='function_bounds':
        insist(task.get('given_domain')=='(0,+inf)' and task.get('requested_output')==['infimum','supremum'],
            'The argument must describe both bounds on the positive original half-line')
    else:insist(task.get('requested_output')==['all_strict_local_extrema','justification_on_original_domain'],
                'All strict extrema on the original domain are required')
    partial_patterns=(rf'exp\(-{name}\)\*sum\({name}\^({LOCAL_NAME})/factorial\(\1\),\1=0\.\.({LOCAL_NAME})\)',
                      rf'\(sum\({name}\^({LOCAL_NAME})/factorial\(\1\),\1,0,({LOCAL_NAME})\)\)\*exp\(-{name}\)')
    partial=next((a for pattern in partial_patterns if (a:=re.fullmatch(pattern,text))),None)
    if partial:
        insist(meta.get('printed_instruction') in (None,'Найти нижнюю грань (inf) и верхнюю грань (sup)'),
            'The stated source instructions require a different extremum method')
        n=partial[2];insist(p==[n] and guards in ([n+' positive integer'],[n+' is the natural summation order']),
            'The upper index must be a positive integer from the original assumptions')
        if kind=='function_bounds':
            value=dict(infimum=dict(value=ZERO,attained=False),supremum=dict(value=ONE,attained=False))
            extra='На x>0 производная строго отрицательна. Хвост полинома с экспонентой стремится к 0, правый след в 0 равен 1.'
        else:
            value=dict(extrema=[dict(type='strict_maximum',point=ZERO,value=ONE,condition=f'{n} odd')],
                       no_other_extrema=True)
            extra='При нечётном верхнем индексе знак меняется с плюса на минус, а при чётном убывание сохраняется через единственный нуль.'
        return local_geometry_certificate(lib,'local_extrema_from_complete_signs',dict(variable=name,summation_order=n,assumptions=guards),value,
            'Дифференцировать конечную сумму и сдвинуть индекс на единицу. Слагаемые от производной экспоненты сокращаются, кроме последнего.',
            extra,derivative=f'-exp(-{name})*{name}^{n}/factorial({n})')
    insist(kind=='classify_extrema' and isinstance(p,list) and len(p)==2 and guards==[f'{p[0]} and {p[1]} are positive integers'],
           'The two exponents must be positive integers throughout the real line')
    u,v=(('s',s) for s in p);h=m.parse(text,name,p)
    insist(same_value(h,m.mul(('rpow',x,u),('rpow',m.add(ONE,m.neg(x)),v))) and
           all(k=='positive' and (same_value(e,x) or same_value(e,m.add(ONE,m.neg(x)))) for k,e in domain_conditions(h)),
           'Both original bases and powers must be linked to the unit product')
    # Integer powers are defined for all real bases, unlike the generic rpow branch.
    insist(h[0]=='mul' and all(z[0]=='rpow' for z in h[1:]),'A directly given product of integer powers is required')
    critical=m.div(u,m.add(u,v))
    return local_geometry_certificate(lib,'local_extrema_from_complete_signs',dict(variable=name,integer_exponents=p,original=h),
        dict(extrema=[dict(type='strict_minimum',point=ZERO,value=ZERO,condition=p[0]+' even'),
                       dict(type='strict_minimum',point=ONE,value=ZERO,condition=p[1]+' even'),
                       dict(type='strict_maximum',point=critical,value=m.substitute(h,{x:critical}))],no_other_extrema=True),
        'Применить правило производной целой степени на всей прямой. Среди ненулевых баз знак оставшегося линейного множителя меняется в m/(m+n).',
        'В нулях баз сохранить знак соседнего ненулевого множителя. Чётный порядок даёт минимум, нечётный — разные знаки функции.',
        derivative_factorization=['x^(m−1)','(1−x)^(n−1)','m−(m+n)x'])


def preserve_extrema(task,lib):
    meta=task.get('source',{});given=task.get('given')
    insist(not set(task)-{'kind','id','source','given'} and not set(meta)-SOURCE_META and given in (
           'f(x)>=0,F(x)=C*f(x)^2,C>0','phi strictly increasing on entire real line'),
           'An order preserving transform on the whole image must be proved')
    scale=given.startswith('f(x)');scope='nonnegative image of f, C>0' if scale else 'all real values of f'
    return local_geometry_certificate(lib,'order_preserving_transforms',dict(original=given,scope=scope),
        dict(same_points_of_minima_and_maxima=True,strict_and_nonstrict=True),
        'Умножение на C>0 и квадрат на неотрицательной полуоси строго сохраняют порядок.' if scale
            else 'Использовать заданное строгое возрастание на образе исходной функции.',
        'В любой допустимой окрестности сравнение с центральным значением эквивалентно сравнению образов, включая равенство.')


def positive_power_extremum(task,lib):
    meta=task.get('source',{});given=task.get('given','')
    insist(not set(task)-{'kind','id','source','given'} and not set(meta)-SOURCE_META,
           'Additional source constraints of the optimization are unresolved')
    h=meta.get('literal_requirement')
    if given=='Varied base b of a logarithmic system':
        insist(h in (None,'Найти системы логарифмов, в которых существуют числа, равные своему логарифму.'),'Incorrect goal for the base')
        x=('v','x');profile,pts,data=exact_profile(m.div(('ln',x),x),'x',[('positive',x)],('-inf','+inf',False,False),lib)
        return local_geometry_certificate(lib,'roots_by_monotone_image',dict(base='b>0 and b!=1',source_variable='x>0'),
            dict(bases=dict(lower=ZERO,lower_attained=False,upper=('exp',pts[0][1]),upper_attained=True,excluded=[ONE])),
            'Для допустимого основания равенство log_b x=x эквивалентно ln x/x=ln b. Найти диапазон отношения по знаку производной.',
            'Сравнить ln b с верхним уровнем и перевести через возрастающую экспоненту.',root_profile=profile,**data)
    p=re.fullmatch(rf'Two positive numbers with fixed (sum|product) ({LOCAL_NAME}); ({LOCAL_NAME}),({LOCAL_NAME})>0',given)
    insist(p and len(set(p.groups()[1:]))==3,'The fixed positive sum or product and independent exponents must be bound')
    mode,a,mn,nn=p.groups();a,u,v=(('s',z) for z in (a,mn,nn));tot=m.add(u,v)
    expected='Определить наибольшее произведение m-й и n-й степеней.' if mode=='sum' else 'Определить наименьшую сумму m-й и n-й степеней.'
    insist(h in (None,expected),'The printed objective disagrees with the eliminated positive constraint')
    def power(b,e):return 'rpow',b,e
    if mode=='sum':
        x,y=m.div(m.mul(a,u),tot),m.div(m.mul(a,v),tot);value=m.mul(power(x,u),power(y,v));direction='maximum'
        proof='Выразить второе число как a−x на (0,a). Знак логарифмической производной задаёт m(a−x)−nx. При единственной смене плюс→минус получается глобальный максимум.'
    else:
        x=power(m.div(m.mul(v,power(a,v)),u),m.div(ONE,tot));y=m.div(a,x);value=m.add(power(x,u),power(y,v));direction='minimum'
        proof='Подставить a/x на (0,+∞). После выделения положительных степеней знак производной задаёт mx^(m+n)−na^n. При единственной смене минус→плюс получается глобальный минимум.'
    return local_geometry_certificate(lib,'eliminate_positive_constraint',dict(constraint=mode,fixed_value=a,positive_exponents=(u,v)),
        dict(type=direction,attained=True,point=(x,y),value=value),proof,
        'Обе найденные координаты положительны, удовлетворяют исходному ограничению и исчерпывают внутренние точки оптимума.')


def ratio_parametrization(task,lib):
    meta=task.get('source',{});t=task.get('relation','');body,*clauses=text_form(t).split(',')
    insist(not set(task)-{'kind','id','source','relation','requested_output'} and not set(meta)-SOURCE_META and
           meta.get('literal_requirement') in (None,'Представить уравнение в параметрической форме и построить кривую.') and
           task.get('requested_output')==['parametric_equations_covering_original_curve'],
           'The complete original parametrization must be the mathematical goal')
    separ=re.fullmatch(r'(.+?)(?:=)(.+)',body);insist(separ,'One real equation is required')
    conditions=[s.strip() for s in clauses];hint='';params=[p for p in number_names(body,'x') if p!='y']
    if conditions and '. Hint ' in conditions[-1]:
        conditions[-1],hint=conditions[-1].split('. Hint ',1);hint=hint.rstrip('.')
    insist(not hint or hint=='y=t*x','This printed substitution was not implemented')
    x=('v','x');y=('s','y');u=('s','t');real_u=('v','t')
    lhs,rhs=(m.parse(e,'x',['y',*params]) for e in separ.groups())
    if [lhs,rhs]==[('rpow',x,y),('rpow',y,x)] and conditions==['x>0','y>0']:
        h=('rpow',u,m.div(ONE,m.add(u,m.neg(ONE))))
        return local_geometry_certificate(lib,'cover_by_ratio_and_exceptional_axis',dict(original_equation=(lhs,rhs),domain='x>0,y>0'),
            dict(branches=[dict(conditions=['t>0','t!=1'],coordinates=(h,m.mul(u,h))),
                           dict(conditions=['s>0'],coordinates=(('s','s'),('s','s')))]),
            'На положительной области логарифмировать и взять отношение t=y/x. Получается (t−1)ln x=ln t.',
            'При t≠1 выразить x и восстановить y. При t=1 вся положительная диагональ, которую нельзя потерять при делении.')
    insist(not set(params)&{'t'} and conditions==[p+'>0' for p in params],
        'Unbound source parameters or inequalities remain')
    raw=('add',lhs,('mul',q(-1),rhs));insist(not domain_conditions(raw),'The original relation has a nonpolynomial restriction')
    # The exceptional y-axis must be solved before dividing by x.
    axis=m.simplify(m.substitute(raw,{x:ZERO,y:('v','y')}));an,ad=poly.rf(axis,'y')
    insist(any(an) and len(ad)==1,'An entire exceptional axis needs its own branch')
    axis_points=[(ZERO,quadratic_point(z)) for z in sorted(set(rational_roots(an)),key=cmp_to_key(line.compare))]
    repl=m.substitute(raw,{y:m.mul(u,x)});poly_x,d=m.rational_form(repl)
    insist(d=={():Fraction(1)} and poly_x,'A polynomial radial equation is required')
    groups={}
    for mon,c in poly_x.items():
        k=dict(mon).get(x,0);groups.setdefault(k,{})[tuple((a,j) for a,j in mon if a!=x)]=c
    lo,hi=min(groups),max(groups);insist(len(groups)==2 and hi-lo in (1,2),'After removing the exceptional axis the radial equation must be linear or quadratic')
    A,B=(m.poly_expr(groups[k]) for k in (hi,lo));At=m.substitute(A,{u:real_u})
    p,d=poly.rf(At,'t');insist(any(p) and len(d)==1,'Need full vanishing levels of the radial leading coefficient')
    ctx=m.context(dict(variable='t',parameters=params,parameter_conditions=conditions))
    for root in rational_roots(p):
        z=m.substitute(B,{u:quadratic_point(root)})
        insist(known_guard(('nonzero',z),ctx),'A leading-coefficient zero could admit an entire ray')
    val=m.div(m.neg(B),A);positive=None
    if hi-lo==2:
        scoped=m.substitute(val,{u:real_u})
        insist(everywhere_guard(('positive',scoped),'t',ctx),'No uniform sign for the radial square root')
        positive=True;val=('sqrt',val)
    xs=[val,m.neg(val)] if positive else [val]
    branches=[dict(parameter='t in R',conditions=[('nonzero',A),('nonzero',z)],coordinates=(z,m.mul(u,z))) for z in xs]
    return local_geometry_certificate(lib,'cover_by_ratio_and_exceptional_axis',dict(original_equation=(lhs,rhs),source_parameters=conditions),
        dict(branches=branches,axis_points=axis_points),
        'В исходном уравнении сначала решить x=0. Для остальных точек выбрать t=y/x.',
        'После подстановки сохраняется ненулевой множитель x. Остаток — линейное или квадратное уравнение для x.',
        'Решить его во всех знаковых ветвях. Проверить нули старшего коэффициента, ограничения радикала и обратное соответствие.',
        radial_factorization=dict(axis_power=lo,remaining_degree=hi-lo,lead=A,constant=B))


def inverse_branch_image(task,lib):
    kind=task['kind'];meta=task.get('source',{});theory=kind=='inverse_existence_and_derivative';many=kind=='inverse_branches_derivative'
    fields={'equation','hypotheses'} if theory else {'forward','requested_output'} if many else {'forward'}
    headings=(None,'Доказать существование однозначной функции и найти её производную.') if theory else (
        None,'Выделить однозначные непрерывные ветви обратных функций, найти их производные и построить графики.') if many else (
        None,'Определить области существования обратных функций и найти их производные.')
    insist(not set(task)-{'kind','id','source'}-fields and not set(meta)-SOURCE_META and meta.get('literal_requirement') in headings,
           'The source inverse question has an unbound condition')
    if many:insist(task.get('requested_output')==['all_continuous_inverse_branches','derivatives_of_inverse_branches'],
                    'All original inverse branches and their derivatives are required')
    if theory:
        text=text_form(task['equation']);name='y';both=re.fullmatch(r'(.+)\s*=\s*x',text)
        insist(both,'The equation must define a function of its right-hand coordinate')
        body=both[1];params=number_names(body,name);cond=task['hypotheses'];scope='R'
    else:
        text=text_form(task['forward']);name='x';body,sep,condition=text.partition(', ')
        insist(not sep or condition=='x>0','The stated input interval is unsupported')
        scope=condition or 'R';params=[];cond=[]
    x=('v',name);F=m.parse(body,name,params);guard=domain_conditions(F);D,steps=table(F,name,lib)
    domain=('-inf','+inf',False,False)
    rows=[];points=[];extra={}
    if params:
        insist(len(params)==1 and cond==[f'0<={params[0]}<1'] and not guard,
               'The oscillatory perturbation must have magnitude strictly below one')
        eps=('s',params[0]);expected=m.add(x,m.neg(m.mul(eps,('sin',x))))
        insist(same_value(F,expected),'No bound on this perturbation guarantees strict monotonicity')
        rows=[('-inf','+inf','-inf','+inf',1)]
        extra['range_argument']='Производная не меньше 1−ε>0, колеблющееся слагаемое ограничено и сохраняет оба бесконечных хвоста.'
    elif not cond:
        try:rows,points,extra=rational_profile(F,name,guard,domain if scope=='R' else (ZERO,'+inf',False,False))
        except (poly.NotRational,Unsupported):pass
    if not rows:
        if same_value(F,m.add(x,('ln',x))) and scope=='x>0' and all(k=='positive' and same_value(u,x) for k,u in guard):
            rows=[(ZERO,'+inf','-inf','+inf',1)]
            extra['range_argument']='На x>0 оба слагаемых строго возрастают. Логарифм расходится слева, а x неограничен справа.'
        elif scope=='R' and not guard:
            if same_value(F,m.add(x,('exp',x))) or F==('sinh',x):
                rows=[('-inf','+inf','-inf','+inf',1)]
                extra['range_argument']='Табличная производная строго положительна, исходные экспоненты дают противоположные бесконечные следы.'
            elif F==('tanh',x):
                rows=[('-inf','+inf',q(-1),ONE,1)]
                extra['range_argument']='Производная sech² положительна, экспоненциальное определение даёт два открытых следа −1 и 1.'
            elif many:
                P,Q=m.rational_form(F);slopes=[];z=('v','u')
                insist(Q=={():Fraction(1)} and isinstance(P,dict),'A finite polynomial in one positive exponential is required')
                for mon in P:
                    if not mon:slopes.append((mon,Fraction(0)));continue
                    insist(len(mon)==1 and mon[0][1]==1 and mon[0][0][0]=='exp','Several independent exponential bases are not ordered')
                    r,d=poly.rf(mon[0][0][1],name)
                    insist(len(r)==2 and r[0]==0 and len(d)==1,'Only linear unshifted exponentials admit this image map')
                    slopes.append((mon,r[1]/d[0]))
                a=min((u for _,u in slopes if u),key=abs)
                powers=[(k,r/a) for k,r in slopes];insist(all(s>=0 and s.denominator==1 for _,s in powers),'No positive-coordinate common power base')
                expr=m.poly_expr({((z,int(s)),) if s else ():P[k] for k,s in powers})
                raw_rows,raw_points,extra=rational_profile(expr,'u',[],(ZERO,'+inf',False,False))
                def pull(t):
                    if t==ZERO:return '-inf' if a>0 else '+inf'
                    if t=='+inf':return '+inf' if a>0 else '-inf'
                    return m.div(('ln',t),q(a))
                rows=[(pull(L),pull(R),l,r,s) if a>0 else (pull(R),pull(L),r,l,-s) for L,R,l,r,s in raw_rows]
                if a<0:rows.reverse()
                points=[(pull(t),v) for t,v in raw_points]
                extra['range_argument']='Ввести положительную экспоненту u как координату. Вычислить строгие ветви полинома в u и перенести их с ориентацией экспоненты.'
                extra['substitution']=('exp',m.mul(q(a),x))
    insist(rows and (not theory or len(rows)==1 and rows[0][2:4]==('-inf','+inf')),
           'Strict invertibility on the required whole domain is unresolved')
    cuts={a for a,_ in points};out=[]
    for a,b,l,r,s in rows:
        z=(a,b,a in cuts,b in cuts);image=(l,r,a in cuts,b in cuts) if s>0 else (r,l,b in cuts,a in cuts)
        out.append(dict(forward_domain=z,inverse_domain=image,orientation=s,
            derivative=m.div(ONE,D),formula_condition=('nonzero',D),
            endpoint_slopes='one-sided if reached; unbounded when the forward derivative vanishes'))
    return local_geometry_certificate(lib,'inverse_from_strict_branches',dict(original=F,variable=name,source_restriction=scope,conditions=cond),
        dict(branches=out,critical_source_points=points),
        'Доказать строгую монотонность каждой исходной ветви и вычислить оба предельных уровня.',
        'Область обратной ветви — полученный образ. Включить только исходно допустимые концы, переставив их при убывании.',
        'Из исходного равенства или разностного отношения получить обратную производную 1/F′ только там, где F′ ненулевая.',
        table_steps=steps,**extra)


def polar_graph_jet(task,lib):
    meta=task.get('source',{});origin=meta.get('polar_data');name=task.get('parameter');params=task.get('parameters');v=('v',name)
    insist(not set(task)-{'kind','id','source','coordinates','parameter','parameters','stated_conditions','orders','requested_output','polar_chart'}
           and not set(meta)-SOURCE_META-{'polar_data'} and meta.get('literal_requirement') in (None,'Найти y′_x для заданной полярной кривой.')
           and isinstance(origin,dict) and set(origin)=={'r','phi','printed_definition'} and origin['phi']==name and
           origin['printed_definition']=='r=sqrt(x^2+y^2), phi=atan(y/x)' and not task.get('stated_conditions') and
           task.get('orders')==[1] and task.get('requested_output')==['derivatives_as_functions_of_parameter'],
           'The original polar branch and the requested coordinate must be preserved')
    if 'polar_chart' in task:
        insist(task['polar_chart']==dict(radius=origin['r'],radial_coordinate='sqrt(x^2+y^2)',
               angular_coordinate='atan(y/x)',parameter=name),
               'The typed polar coordinates must agree exactly with the printed chart')
    r=m.parse(origin['r'],name,params);X,Y=(m.parse(z,name,params) for z in task['coordinates']);cs,sn=('cos',v),('sin',v)
    insist(same_value(X,m.mul(r,cs)) and same_value(Y,m.mul(r,sn)) and not domain_conditions(r,True) and
           not domain_conditions(X,True) and not domain_conditions(Y,True),
           'The supplied parametric coordinates must implement the original polar functions and guards')
    dr,steps=table(r,name,lib);dx=m.add(m.mul(dr,cs),m.neg(m.mul(r,sn)));dy=m.add(m.mul(dr,sn),m.mul(r,cs))
    return local_geometry_certificate(lib,'relative_coordinate_germs',dict(angle=name,angle_interval='(-pi/2,pi/2)',original_radius=r,
         radial_condition=('positive',r),branches=('x>0','x<0')),dict(regular_slope=m.div(dy,dx),regular_condition=('nonzero',dx),
         zero_horizontal_speed='vertical tangent because the total speed remains nonzero'),
         'Из φ=arctan(y/x) получить главную угловую ветвь. При x≠0 исходный радиус положителен.',
         'На каждой из двух ветвей x и y одновременно получают знак горизонтальной координаты. Он сокращается в их производном отношении.',
         'Норма вектора скорости равна sqrt(r′²+r²)>0. При нулевой скорости x касательная вертикальна, конечный наклон отсутствует.',
         table_steps=steps,unoriented_jet=(dx,dy),source_polar_chart=source_polar_coverage(r,name,params))


def curvature_radius(task,lib):
    from plane_geometry import equation_chart,curvature
    meta=task.get('source',{})
    insist(not set(task)-{'kind','id','source','curve','representation','printed_conditions'} and not set(meta)-SOURCE_META
           and meta.get('literal_requirement') in (None,'Определить радиус кривизны заданной кривой.') and
           task.get('representation')=='implicit' and not task.get('printed_conditions'),
           'The complete real implicit curve is required')
    text=task['curve'].replace('real_cuberoot','cbrt');xy,name,ps,conditions,coverage=equation_chart(text)
    insist(text.startswith('cbrt(') and 'degenerate' in coverage,
           'A complete parametric astroid and its zero-scale case are required')
    a=m.parse(ps[0],None,ps) if ps else None;insist(a is not None and len(ps)==1,'A real astroid scale is required')
    v=('v',name);cos,sin=('cos',v),('sin',v);steps=[];jet=[xy]
    for _ in range(2):
        rows=[table(e,name,lib) for e in jet[-1]];jet.append(tuple(y for y,_ in rows));steps.extend(t for _,proof in rows for t in proof)
    info,out=curvature(jet,dict(natural_guards=(),smooth_guards=()),name,ps,conditions)
    speed,det=info['speed_squared'],info['determinant'];s=m.mul(sin,cos)
    insist(same_value(speed,m.mul(q(9),m.mul(m.power(a,2),m.power(s,2)))) and
           same_value(det,m.mul(q(-9),m.mul(m.power(a,2),m.power(s,2)))),
           'Cannot factor the speed and determinant in the original astroid coordinate')
    radius=m.mul(q(3),('abs',m.mul(a,s)))
    return local_geometry_certificate(lib,'match_coordinate_jets',dict(original=task['curve'],parameter=name,coverage=coverage),
        dict(radius=radius,regular_conditions=[('nonzero',a),('nonzero',s)],
             cusp_radius_limit=ZERO,zero_scale='isolated point; no circle of curvature'),
        'Кубические координаты покрывают исходную астроиду. Найти скорость и ускорение, затем проверить факторизацию квадрата скорости и определителя.',
        'На регулярной дуге радиус равен квадрату скорости в степени 3/2, делённому на модуль определителя.',
        'В остриях исходная скорость нулевая, поэтому остаётся только предельный радиус. При нулевом масштабе кривая вырождается в точку.',
        table_steps=steps,squared_speed=speed,determinant=det)


def local_geometry_routing(task,kind):
    if kind in ('parametric_local_derivative','uniform_deviation_optimum','fit_curve_contact','osculating_circle',
                'extremum_preservation','constrained_extremum','curve_parametrization','inverse_existence_and_derivative',
                'inverse_domain_derivative','inverse_branches_derivative'):return True
    if kind=='curve_curvature_radius':
        shape=task.get('curve')
        return (task.get('representation')=='implicit' and isinstance(shape,str) and bool(re.fullmatch(
            rf'cbrt\(x\)\^2\+cbrt\(y\)\^2=cbrt\({LOCAL_NAME}\)\^2',shape.replace('real_cuberoot','cbrt'))))
    if kind=='extremum_envelope':return task.get('requested_output')==['lower_and_upper_envelopes']
    if kind=='discrete_extremum':return isinstance(task.get('given'),str) and 'integer' in task['given']
    if kind=='real_root_count_isolation':
        given=task.get('given');variable=task.get('variable','x')
        source=task.get('source',{})
        requests_family=task.get('requested_output') in ROOT_LEVEL_OUTPUTS or (
            isinstance(source,dict) and source.get('literal_requirement') in ROOT_LEVEL_HEADINGS)
        return (requests_family and isinstance(given,str) and isinstance(variable,str) and
                bool(number_names(given.split(',')[0],variable)))
    if kind=='parametric_curve_derivatives':
        meta=task.get('source',{});coords=task.get('coordinates',())
        return (isinstance(meta,dict) and 'polar_data' in meta or isinstance(meta,dict) and
                meta.get('literal_requirement')=='Найти указанное отношение дифференциалов (производную одной функции по другой).'
                and isinstance(coords,list) and len(coords)==2 and not task.get('parameters') and
                all(isinstance(z,str) and not set(re.findall(LOCAL_NAME,z))-{task.get('parameter')} for z in coords))
    f=task.get('function')
    if not isinstance(f,str):return False
    if kind=='function_bounds':return 'sum(' in f and 'factorial(' in f and task.get('given_domain')=='(0,+inf)'
    if kind!='classify_extrema':return False
    if task.get('parameters'):
        return 'factorial(' in f and 'sum(' in f or len(task['parameters'])==2 and ' are positive integers' in str(task.get('stated_conditions'))
    return 'ln(' in f and 'exp(' not in f and ('sqrt(' in f or 'atan(' in f or '^2/' in f)


def local_geometry_goal(task,lib,request):
    kind=task['kind']
    if kind=='discrete_extremum':return integer_maximum(task,lib,request)
    if kind=='parametric_curve_derivatives' and 'polar_data' in task.get('source',{}):return polar_graph_jet(task,lib)
    if kind=='classify_extrema' and not task.get('parameters'):return regular_scalar_extrema(task,lib)
    handler={'real_root_count_isolation':level_roots,'extremum_envelope':tail_envelope,
             'uniform_deviation_optimum':deviation_optimum,'fit_curve_contact':graph_contact,
             'parametric_local_derivative':rational_coordinate_jet,'parametric_curve_derivatives':rational_coordinate_jet,
             'osculating_circle':osculating_circle,'function_bounds':exponent_profile,'classify_extrema':exponent_profile,
             'extremum_preservation':preserve_extrema,'constrained_extremum':positive_power_extremum,
             'curve_parametrization':ratio_parametrization,'inverse_existence_and_derivative':inverse_branch_image,
             'inverse_domain_derivative':inverse_branch_image,'inverse_branches_derivative':inverse_branch_image,
             'curve_curvature_radius':curvature_radius}[kind]
    return handler(task,lib)


SCALE_GOALS={'higher_derivative_functional','successive_differentials_with_dependent_coordinate',
             'local_factor_sign_and_parity','inverse_change','derivative_inequality','compare_inverse_measurement_errors'}
SCALE_INEQUALITIES=tuple(map(re.compile,(
    r'1/2\^\((?P<p>\w+)-1\)<=(?P<x>\w+)\^\1\+\(1-\2\)\^\1<=1, 0<=\2<=1,\1>1',
    r'\((?P<x>\w+)\+(?P<a>\w+)\)/2\^\(\((?P<n>\w+)-1\)/\3\)<=\(\1\^\3\+\2\^\3\)\^\(1/\3\)<=\1\+\2, \1>0,\2>0,\3>1',
    r'(?P<x>\w+)\^(?P<m>\w+)\*\((?P<a>\w+)-\1\)\^(?P<n>\w+)<=\(\2\^\2\*\4\^\4/\(\2\+\4\)\^\(\2\+\4\)\)\*\3\^\(\2\+\4\), \2>0,\4>0,0<=\1<=\3',
    r'abs\((?P<a>\w+)\*sin\((?P<x>\w+)\)\+(?P<b>\w+)\*cos\(\2\)\)<=sqrt\(\1\^2\+\3\^2\)',
)))
DAMPED_COSINE=re.compile(r'exp\((?P<a>(?:-\d+\*|-\d*/\d+\*|-))(?P<x>[A-Za-z]\w*)\^(?P<k>[1-9]\d*)\)\*cos\((?P<b>\d+\*|\d+/\d+\*)?\2\^\3\)')


def scale_routing(task,kind):
    if kind in SCALE_GOALS:return True
    if kind=='function_bounds' and task.get('given_domain')=='R' and isinstance(task.get('function'),str):
        wave=DAMPED_COSINE.fullmatch(task['function'])
        return bool(wave and int(wave['k'])%2==0 and task.get('requested_output')==['infimum','supremum'])
    if kind=='prove_inequality' and isinstance(task.get('given'),str):
        given=task['given'].replace('²','^2')
        if given.endswith(' for all real x'):
            try:full_line_rational_claims(task)
            except (Unsupported,poly.NotRational,poly.Undefined):return False
            return True
        return any(r.fullmatch(given) for r in SCALE_INEQUALITIES)
    if kind=='composite_function_differentiation' and task.get('requested_output')==['second_derivative']:
        args=task.get('inner_arguments');x=task.get('variables');outer=task.get('outer_expression')
        return bool(isinstance(args,dict) and len(args)==2 and isinstance(x,list) and len(x)==1 and not task.get('parameters')
                    and not task.get('stated_conditions')
                    and outer=='sqrt('+'^2+'.join(args)+'^2)')
    return False


def scale_packet(task,fields,headings=()):
    source=task.get('source',{})
    require(isinstance(source,dict) and not set(source)-HIGHER_SOURCE_FIELDS-{'printed_group_instruction','section_title','definition_ref','note'} and
            not set(task)-{'kind','id','source','schema','transcription'}-set(fields) and
            all(source.get(k) in (None,*headings) for k in ('literal_requirement','printed_instruction','printed_group_instruction')) and
            not any(source.get(k) for k in ('printed_hint','source_issue','printed_goal','requested_operator')),
            'В печатном условии остался несвязанный вывод или способ')


def formal_functional_scale(task,lib):
    scale_packet(task,{'function','variable','derivative_order','parameters','stated_conditions','method_requirement',
                       'requested_output','function_symbols'},("Найти y'', если",))
    x=task['variable'];names=task['function_symbols'];meta=task.get('source',{})
    require(isinstance(x,str) and re.fullmatch(NAME,x) and isinstance(names,list) and len(names)==1 and
            re.fullmatch(NAME,names[0]) and names[0]!=x and not task.get('parameters') and not task.get('stated_conditions') and
            task.get('derivative_order')==2 and task.get('method_requirement')=='table_and_rules' and
            task.get('requested_output')==['second_derivative','original_domain_and_derivative_existence_scope'] and
            meta.get('definition_ref') in (None,{'pdf_page':108,'statement':'Higher derivatives are successive ordinary derivatives whenever the respective operations are meaningful.'}) and
            meta.get('note') in (None,'The printed f(x) is arbitrary, not a missing elementary formula; retain the functional derivative task.'),
            'Нужны обычные последовательные производные на исходной области')
    f,=names;raw=m.parse(task['function'],x,extra_functions={f})
    u=(f,('v',x));require(raw==('ln',u),'Ожидается положительный аргумент логарифма')
    y,p,r=(('s',s) for s in ('u0','u1','u2'))
    local=m.substitute(raw,{u:y})
    first=m.simplify(differentiate_jet(local,{y:p},lib))
    second=m.simplify(differentiate_jet(first,{y:p,p:r},lib))
    return higher_certificate(lib,'differentiate_a_functional_jet',dict(variable=x,function=f,scope='f>0 and first two ordinary derivatives exist'),
         dict(first=first,second=second,jet={y[1]:u,p[1]:('derivative_at_unknown',f,('v',x)),r[1]:('nth_derivative_at_unknown',2,f,('v',x))}),
         'Ввести значения внутренней функции и её последовательных производных. У логарифма сохранить строго положительное исходное значение.',
         'Дважды продифференцировать по таблице, сдвигая порядок каждого внутреннего элемента на единицу.')


def successive_coordinate_scale(task,lib):
    from collections import Counter
    scale_packet(task,{'function','coordinate','orders'},('Find d²y, d³y, d⁴y for y=f(x), with x itself a function of an independent variable.',))
    coord=re.fullmatch(rf'({NAME})\(({NAME})\)',task['coordinate'])
    f=re.fullmatch(rf'({NAME})\(({NAME})\)',task['function'])
    req=task['orders'];require(coord and f and f[2]==coord[1] and len({*coord.groups(),f[1]})==3 and
       isinstance(req,list) and req and all(type(k) is int and 1<=k<=8 for k in req) and
       (not task.get('source',{}).get('literal_requirement') or req==[2,3,4]),'Не связано независимое приращение или запрошенные порядки')
    jets={(0,()):1};answers={}
    for k in range(1,max(req)+1):
        new=Counter()
        for (outer,inner),coefficient in jets.items():
            new[outer+1,(1,*inner)]+=coefficient
            for j,order in enumerate(inner):
                nxt=tuple(sorted((*inner[:j],order+1,*inner[j+1:])))
                new[outer,nxt]+=coefficient
        jets=new
        if k in req:answers[str(k)]=[dict(outer_order=o,inner_orders=list(i),coefficient=c) for (o,i),c in sorted(jets.items())]
    return higher_certificate(lib,'successive_coordinate_product_rule',
        dict(inner=task['coordinate'],outer=f[1],requires_differentiability_through=max(req)),answers,
        'Построить первый дифференциал цепным правилом. На каждом шаге либо увеличить порядок внешней производной и добавить dx, либо продифференцировать один внутренний множитель.',
        'Сложить коэффициенты одинаковых произведений. Приращение независимого аргумента удерживать постоянным.')


def local_parity_scale(task,lib):
    scale_packet(task,{'function','point','assumptions'},('Investigate the extremum at x0 of (x−x0)^n phi(x), where n is natural, phi is continuous at x0 and phi(x0) is nonzero.',))
    match_=re.fullmatch(rf'\(({NAME})-({NAME})\)\^({NAME})\*({NAME})\(\1\)',task['function'])
    require(match_ and len(set(match_.groups()))==4 and task['point']==match_[2] and
            task['assumptions']==[f'{match_[3]} positive integer',f'{match_[4]} continuous at {match_[2]}',f'{match_[4]}({match_[2]}) nonzero'],
            'Не установлены кратность, непрерывность множителя и его ненулевость в точке')
    x,z,n,f=match_.groups()
    return higher_certificate(lib,'local_sign_from_nonzero_continuous_factor',dict(point=z,index=n,factor=f),
        dict(at=ZERO,odd='neither extremum',even={'positive_factor':'strict minimum','negative_factor':'strict maximum'}),
        'В точке степенной множитель равен нулю. Непрерывный ненулевой множитель сохраняет знак в некоторой окрестности.',
        'Нечётная степень меняет знак, а чётная положительна на обоих проколотых полуинтервалах.')


def damped_cosine_scale(task,lib):
    scale_packet(task,{'function','variable','given_domain','requested_output'},('Найти нижнюю грань (inf) и верхнюю грань (sup)',))
    hit=DAMPED_COSINE.fullmatch(task['function'])
    require(hit and hit['x']==task['variable'] and int(hit['k'])%2==0 and task['given_domain']=='R' and
            task.get('requested_output')==['infimum','supremum'],'Вещественная область и образ чётной степени не подтверждены')
    a=Fraction(hit['a'].removesuffix('*').removeprefix('-') or '1')
    b=Fraction(hit['b'].removesuffix('*')) if hit['b'] else Fraction(1)
    require(a>0 and b>0,'Амплитуда должна затухать при положительной частоте')
    A,B=q(a),q(b);phase=m.add(m.PI,m.neg(('atan',q(a/b))));t=m.div(phase,B)
    value=m.mul(m.div(m.neg(B),('sqrt',q(a*a+b*b))),('exp',m.mul(m.neg(A),t)))
    return higher_certificate(lib,'earliest_negative_extremum_under_damping',
         dict(image_of_even_power=(ZERO,'+inf'),decay=A,frequency=B,first_negative_critical_parameter=t),
         dict(infimum=value,supremum=ONE,infimum_attained=True,supremum_attained=True),
         'У чётной степени на вещественной прямой образ [0,+∞). Вывести производную по этой координате и определить первое стационарное значение внутри отрицательной полуволны.',
         'Следующие отрицательные минимумы имеют ту же фазу по модулю периода и меньший модуль при экспоненциальном затухании. Снаружи отрицательных полуволн значения неотрицательны. Верхняя грань 1 достигается при нулевой фазе.')


def scale_inequality(task,lib):
    scale_packet(task,{'given','requested_output'},('Доказать неравенство.','Доказать обе оценки.'))
    require(task.get('requested_output',['proof'])==['proof'],'Нужна проверка печатного неравенства')
    hit,kind=next(((r.fullmatch(task['given'].replace('²','^2')),j) for j,r in enumerate(SCALE_INEQUALITIES)
                   if r.fullmatch(task['given'].replace('²','^2'))),(None,None))
    require(hit and len(set(hit.groups()))==len(hit.groups()),'Исходные параметры и переменная должны быть различимы')
    scope=hit.groupdict();val=dict(proven=True,comparison=task['given'])
    if kind in (0,1):
        return higher_certificate(lib,'normalized_power_sum_bounds',scope,val,
              'На [0,1] степень p>1 не увеличивает число, то есть t^p≤t. Это даёт верхнюю границу суммы двух дополняющих долей.',
              'Производная суммы меняет знак с минуса на плюс в 1/2. Значение в точке равно 2^(1−p).',
              *(() if kind==0 else ('Нормировать исходные положительные слагаемые их суммой и извлечь положительный корень из обеих границ.',)))
    if kind==2:
        return higher_certificate(lib,'stationary_balance_of_positive_endpoint_powers',scope,val,
              'При a=0 исходная область состоит из точки и неравенство обращается в равенство. При a>0 значения в обоих концах нулевые.',
              'Внутри области производная логарифма имеет знак m(a−x)−nx. Подстановка единственного максимума ma/(m+n) даёт заявленный коэффициент.')
    return higher_certificate(lib,'unit_trigonometric_vector_norm_bound',scope,val,
              'Норма вектора (sin x,cos x) равна единице. Неравенство Коши для скалярного произведения с (a,b) даёт заявленную оценку для любого x.')


def inverse_quadratic_change(task,lib):
    from integrals import affine
    scale_packet(task,{'variable','function','at','desired_change','requested_output'},(
      'Период T=2π√(l/g), g=9,8 м/с². На сколько изменить длину l=0,2 м, чтобы период увеличился на 0,05 с? Условие продолжается на с.107.',))
    x=task['variable'];v=('v',x);raw=m.parse(task['function'],x);at=m.parse(task['at'],None);dy=m.parse(task['desired_change'],None)
    require(task['requested_output']==['length_change'] and raw[0]=='mul' and raw[2][0]=='sqrt','Нужна положительная ветвь квадратного корня')
    C,r=raw[1],raw[2][1];a,c=affine(r,x);ctx=m.context(dict(variable=x))
    require(all(known_guard(guard,ctx) for guard in domain_conditions(r)),
            'Неразрешённая область внутри корня')
    t=m.simplify(m.substitute(raw,{v:at}));t1=m.add(t,dy)
    def sign(e):
        from quadrature import enclose
        low,high=enclose(e,None)
        return 1 if low>0 else -1 if high<0 else 0 if low==high==0 else None
    require(all(m.constant_defined(e,ctx) for e in (a,c,C,at,dy,t,t1)) and sign(a) in (-1,1) and sign(C)==1 and
            sign(t)==1 and sign(t1) in (0,1),'Начальное и конечное значения должны принадлежать одной обратимой ветви')
    require(not task.get('source',{}).get('literal_requirement') or
         (x=='l' and task['function']=='2*pi*sqrt(l/(49/5))' and task['at']=='1/5' and task['desired_change']=='1/20'),
         'Числовые условия печатной задачи должны совпадать с параметрами')
    change=m.div(m.mul(dy,m.add(m.mul(q(2),t),dy)),m.mul(a,m.power(C,2)))
    linear=m.div(m.mul(dy,m.mul(q(2),t)),m.mul(a,m.power(C,2)))
    return higher_certificate(lib,'exact_inverse_change_on_nonnegative_square_root_branch',
       dict(function=raw,start=at,end_height=t1),dict(length_change=m.simplify(change),linearization=m.simplify(linear)),
       'Доказать, что оба значения принадлежат одной ветви квадратного корня. Возвести нормированное новое значение в квадрат и обратить линейное выражение под корнем.',
       'Вычесть исходное значение. Линейная часть получается из той же формулы отбрасыванием квадрата приращения.')


def derivative_scale_goal(task,lib):
    require(lib.data.get('residual_series_and_derivative_scales'),'В библиотеке нет дополнительных переходов по масштабу')
    kind=task['kind'];transition={'higher_derivative_functional':formal_functional_scale,
        'successive_differentials_with_dependent_coordinate':successive_coordinate_scale,
        'local_factor_sign_and_parity':local_parity_scale,'function_bounds':damped_cosine_scale,
        'inverse_change':inverse_quadratic_change,'derivative_inequality':harmonic_derivative_region,
        'compare_inverse_measurement_errors':inverse_table_error_order,'composite_function_differentiation':squared_norm_curve}.get(kind)
    if kind=='prove_inequality':
        transition=full_line_rational_bound if task['given'].endswith(' for all real x') else scale_inequality
    require(transition,'Нужна отдельная проверка сравнений наклонов на исходной ветви')
    return transition(task,lib)

def squared_norm_curve(task,lib):
    x,=task['variables'];args=task['inner_arguments'];u,v=args
    name=rf'({NAME})\({re.escape(x)}\)'
    f,g=(re.fullmatch(name,args[s]) for s in (u,v))
    require(f and g and f[1]!=g[1] and task.get('inner_regularities')=={f[1]:2,g[1]:2} and not task.get('stated_conditions')
            and not task.get('parameters') and task['requested_output']==['second_derivative'],
            'Не подтверждены обе гладкие координаты и запрошенный порядок')
    heading='Пусть u=φ(x) и v=ψ(x) дважды дифференцируемы. Найти y″ для y=sqrt(u^2+v^2).'
    scale_packet(task,{'variables','inner_arguments','inner_regularities','stated_conditions','requested_output','outer_expression','parameters'},(heading,))
    require(not task.get('source',{}).get('literal_requirement') or (args=={'u':'phi(x)','v':'psi(x)'} and x=='x'),
            'Обозначения должны совпадать с печатными')
    a,b=(('s',j) for j in (u,v))
    root=m.parse(task['outer_expression'],None,[u,v]);rad=m.add(m.power(a,2),m.power(b,2))
    require(root==('sqrt',rad),'Нужна евклидова норма исходных координат')
    jet_names=[]
    for base in ('du','dv','d2u','d2v'):
        while base in args or base in jet_names:base='_'+base
        jet_names.append(base)
    a1,b1,a2,b2=(('s',j) for j in jet_names)
    dot=m.add(m.mul(a,a1),m.mul(b,b1))
    acc=m.add(m.add(m.power(a1,2),m.power(b1,2)),m.add(m.mul(a,a2),m.mul(b,b2)))
    regular=m.add(m.div(acc,root),m.neg(m.div(m.power(dot,2),m.power(root,3))))
    return higher_certificate(lib,'second_derivative_of_pointwise_norm',
         dict(independent=x,components=args,jet=dict(zip(jet_names,(u+'′',v+'′',u+'″',v+'″')))),
         dict(nonzero_position=regular,zero_position=[
             dict(condition='velocity nonzero',first_derivative='does not exist'),
             dict(condition='velocity zero and acceleration nonzero',second_derivative=('sqrt',m.add(m.power(a2,2),m.power(b2,2)))),
             dict(condition='velocity and acceleration zero',second_derivative=ZERO,
                  required='all zeros in some neighborhood have zero velocity; otherwise an ordinary second derivative is not defined')]),
         'В регулярной точке дважды применить правило цепочки к квадратному корню суммы квадратов.',
         'При нулевом положении первый порядок разложения даёт угол при ненулевой скорости. При ненулевом ускорении и нулевой скорости вторая степень изолирует нуль, а производная нормы равна h умножить на норму ускорения плюс o(h).',
         'При нулевых скорости и ускорении |y′(x+h)|≤||w′(x+h)||=o(|h|) в точках существования. Обычная вторая производная требует, чтобы первая существовала на некоторой окрестности, включая возможные нули.')


def harmonic_derivative_region(task,lib):
    from integrals import affine
    scale_packet(task,{'curve','domain','threshold'},('Определить участки синусоиды, где |y′| превышает 1.',))
    hit=re.fullmatch(r'y=(.+)\*sin\((.+)\)',task['curve'])
    domain=re.fullmatch(r'(\[|\()([^,]+),([^,]+)(\]|\))',task['domain'])
    thr=re.fullmatch(r'abs\(y_prime\)>(.+)',task['threshold'])
    require(hit and domain and thr,'Не связана амплитуда, исходный интервал или строгое сравнение')
    x='x';P=m.parse(hit[1],None);phase=m.parse(hit[2],x);a,c=affine(phase,x);L=m.parse(thr[1],None)
    ctx=m.context(dict(variable=x))
    lo,hi=(m.parse(domain[k],None) for k in (2,3))
    require(not domain_conditions(phase) and all(m.constant_defined(z,ctx) for z in (P,a,c,L,lo,hi)),
            'Не проверена определённость гармоники и границ')
    P0,a0,L0=map(lambda z:m.num(m.simplify(z)),(P,a,L))
    require(None not in (P0,a0,L0) and 0<L0<abs(P0*a0) and
       (not task.get('source',{}).get('literal_requirement') or L0==1),'Порог должен быть строго внутри диапазона модуля амплитуды')
    from quadrature import enclose
    l,_=enclose(m.add(hi,m.neg(lo)),None)
    require(l>0,'Интервал должен иметь проверенный порядок границ')
    h=('acos',q(L0/abs(P0*a0)))
    derivative,steps=table(m.mul(P,('sin',phase)),x,lib)
    return higher_certificate(lib,'periodic_windows_of_harmonic_derivative',dict(derivative=derivative,source_interval=(lo,hi,domain[1]=='[',domain[4]==']')),
         dict(phase=phase,half_width=h,centers='k*pi, k any integer',interval_intersection=task['domain'],strict_phase_bounds=True),
         'Вычислить производную. После деления на модуль ненулевой амплитуды остаётся нижний порог для модуля косинуса.',
         'На каждом полупериоде сравнить расстояние фазы до кратного π с arccos порога. Пересечь прообразы всех открытых окон с исходным интервалом.',
         table_steps=steps)


def inverse_table_error_order(task,lib):
    scale_packet(task,{'tables','accuracy','requested_output'},(
      'Доказать, что при одинаковом числе десятичных знаков углы по логарифмической таблице тангенсов определяются точнее, чем по логарифмической таблице синусов.',))
    matches=[re.fullmatch(rf'log(\d+)\((tan|sin)\(({NAME})\)\)',text) for text in task.get('tables',())]
    require(len(matches)==2 and all(matches) and matches[0][2]=='tan' and matches[1][2]=='sin' and
         matches[0][1]==matches[1][1] and matches[0][3]==matches[1][3] and int(matches[0][1])>1 and
         task['accuracy']=='equal decimal places' and task['requested_output']==['proof_of_angle_accuracy_comparison'],
         'Нужны одинаковая точность и один аргумент двух логарифмических таблиц')
    b=int(matches[0][1]);x=matches[0][3];u=('v',x);s=('sin',u);c=('cos',u);log=('ln',q(b))
    require(not task.get('source',{}).get('literal_requirement') or b==10,'Десятичный логарифм требуется печатной задачей')
    return higher_certificate(lib,'narrower_inverse_errors_from_dominating_derivative',dict(common_table_branch=(ZERO,m.div(m.PI,q(2))),angle=x),
          dict(tangent_slope=m.div(ONE,m.mul(log,m.mul(s,c))),sine_slope=m.div(c,m.mul(log,s)),
               tangent_error_interval='strictly inside the sine error interval for any positive common tolerance'),
          'Обе логарифмические функции строго возрастают на табличной ветви. Отношение их производных равно 1/cos² угла и строго больше единицы.',
          'Для отклонения в любую сторону от одного истинного угла теорема о среднем для разности показывает большее изменение логарифма тангенса.',
          'Одинаковый допуск поэтому даёт строго меньший интервал углов. Доказательство сравнивает конечные отклонения, включая попадание верхнего допуска синуса за предел его образа.')


def full_line_rational_claims(task):
    from graphs import comparison_inputs
    comparisons,restrictions,_=comparison_inputs(task)
    require(len(comparisons)==2 and not restrictions,'Нужны обе оценки на всей вещественной прямой')
    def quad(poly_,strict):
        require(len(poly_)<=3,'Не доказан знак многочлена выше второй степени')
        c,b,a=(*poly_,*([0]*(3-len(poly_))))
        require(a>0 or a==b==0,'Нужна ограниченная снизу квадратичная форма')
        low=c-b*b/(4*a) if a>0 else c
        require(low>0 if strict else low>=0,'Нижнее значение не даёт требуемый знак')
        return q(low)
    witnesses=[]
    for a,b,strict in comparisons:
        for guard,e in domain_conditions(a)+domain_conditions(b):
            p,d=poly.rf(e,'x')
            require(guard=='nonzero' and len(d)==1 and d[0]>0,'Не проверено исходное ограничение рациональной функции')
            quad(p,True) if p[-1]>=0 else quad(tuple(-z for z in p),True)
        p,d=poly.rf(m.add(b,m.neg(a)),'x')
        if d[-1]<0:p,d=tuple(-z for z in p),tuple(-z for z in d)
        witnesses.append((quad(p,strict),quad(d,True)))
    return witnesses


def full_line_rational_bound(task,lib):
    witnesses=full_line_rational_claims(task)
    return higher_certificate(lib,'rational_bounds_from_exact_quadratic_minima',dict(original_domain='R'),
       dict(proven=True,comparison=task['given']),
       'Проверить исходные знаменатели на всей прямой, выделяя полный квадрат. Затем привести каждую разность к общему знаменателю.',
       'Снова выделить полный квадрат в числителе и проверить его минимальное значение и строгость исходных знаков.',
       exact_minima=witnesses)


REMAINING_DERIVATIVE_KINDS={'curve_concavity_at_points'}


def remaining_derivative_head(task,kind):
    return kind in REMAINING_DERIVATIVE_KINDS


def concavity_at_incident_points(task,lib):
    from integrals import affine
    scale_packet(task,{'function','points','requested_output'},('Исследовать направление вогнутости в указанных точках.',))
    x='x';raw=m.parse(task['function'],x);ctx=m.context(dict(variable=x));v=('v',x)
    terms=raw[1:] if raw[0]=='add' else (raw,)
    root=next((u for u in terms if u[0]=='cbrt'),None)
    require(root and task['requested_output']==['concavity_at_each_printed_point'] and not domain_conditions(raw),
            'Не подтверждена гладкая ветвь кубического корня')
    offset=m.add(raw,m.neg(root))
    require(not m.variable_in(m.simplify(offset),x) and m.constant_defined(m.simplify(offset),ctx),'Исходная добавка должна быть постоянной')
    a,b=affine(root[1],x);require(m.num(a) not in (None,0),'Нужен простой корень аффинного радиканда')
    results=[]
    for pt in task['points']:
        require(isinstance(pt,list) and len(pt)==2 and all(type(v) in (int,str) for v in pt),'Требуются обе координаты точки')
        t,y=(m.parse(str(z),None) for z in pt);actual=m.simplify(m.substitute(raw,{v:t}))
        require(all(m.constant_defined(w,ctx) for w in (t,y,actual)),'Не подтверждена принадлежность точки графику')
        if not same_value(actual,y):
            require(m.sign(m.add(actual,m.neg(y)),ctx) in (-1,1),'Не доказано различие ординат')
            results.append(dict(point=pt,classification='not_on_graph',actual_ordinate=actual));continue
        z=m.sign(m.substitute(root[1],{v:t}),ctx);require(z in (-1,0,1),'Не доказан знак исходного радиканда')
        results.append(dict(point=pt,classification='concave_up' if z==-1 else 'concave_down' if z==1 else 'second derivative undefined; concavity reverses between regular sides'))
    value=m.div(m.mul(q(-2,9),m.power(a,2)),m.power(root,5))
    conclusion=dict(second_derivative_on_regular_points=value,each_requested_point=results)
    outside=[row for row in results if row['classification']=='not_on_graph']
    if outside:
        conclusion.update(printed_claim_holds=False,counterexample=dict(nonincident_points=outside))
    return higher_certificate(lib,'cubic_root_concavity_on_incident_points',dict(source=raw),
          conclusion,
          'Сначала подставить абсциссу и проверить принадлежность исходной кривой. Для точки вне графика направление вогнутости в ней не определено.',
          'В регулярной точке знак второй производной противоположен знаку аффинного радиканда. При нулевом радиканде формула имеет особенность и знаки исследуются отдельно с обеих сторон.')


def remaining_derivative_goal(task,lib):
    require(lib.data.get('remaining_analysis_proofs'),'Переходы к сохранённым условиям отсутствуют')
    if task['kind']=='curve_concavity_at_points':return concavity_at_incident_points(task,lib)
    return complete_source_endpoint_table(task,lib)


def lifted_table_input(task):
    if task.get('kind')!='differentiate' or not isinstance(task.get('function'),str):return False
    src=task.get('source',{});fn=task['function']
    return (src.get('printed_instruction') in (None,PRINTED_TABLE) and task.get('method_requirement') in (None,'table_and_rules') and
        ('sqrt(' in fn and '+asin(' in fn or 'sqrt(' in fn and '*asin(' in fn or fn.startswith('asin(sin(') or
         fn.startswith('exp(') and 'asin(' in fn and '*(' in fn))


def source_table_endpoint_transport(task,lib,spec):
    """Finish a table calculation at the regular chart's two ends."""
    from integrals import affine
    from ordinary_series import constant_sign
    from verify import same_value
    x,pars,conditions,ctx=scalar_context(task);v=('v',x)
    raw=m.parse(task['function'],x,pars)
    phi=next((e for _,e in expression_positions(raw) if e[0]=='asin'),None)
    require(phi,'An inverse-sine coordinate must be bound')
    plan={}
    if spec=='compensating_arc':
        require(raw[0]=='add','Need both terms of the original arc profile')
        rst=next((e for _,e in expression_positions(raw) if e[0]=='sqrt' and m.variable_in(e,x)),None)
        require(rst,'An original square root must occur')
        phase=phi[1];slope,offset=affine(phase,x)
        require(all(m.constant_defined(e,ctx) for e in (slope,offset)) and constant_sign(slope,ctx)==1,
                'The inverse sine must be normalized by a positive radius')
        radius=m.simplify(m.div(ONE,slope));h=m.simplify(m.div(m.neg(offset),slope))
        u=m.add(v,m.neg(h));B=rst[1]
        require(not domain_conditions(B) and same_value(B,m.add(m.power(radius,2),m.neg(m.power(u,2)))),
                'The square root and inverse sine must describe the same circle')
        root_part,angle_part=raw[1:]
        if not m.contains(root_part,rst):root_part,angle_part=angle_part,root_part
        A=m.simplify(m.div(root_part,rst));C=m.simplify(m.div(angle_part,phi))
        allowed=domain_conditions(rst)+domain_conditions(phi)
        require(all(g in allowed or known_guard(g,ctx) for g in domain_conditions(raw)) and
           same_value(root_part,m.mul(A,rst)) and same_value(angle_part,m.mul(C,phi)) and
           not domain_conditions(A) and not m.variable_in(C,x) and m.constant_defined(C,ctx),
           'Original term multipliers and exclusions must be preserved')
        t,c=affine(A,x);require(all(m.constant_defined(e,ctx) for e in (t,c)), 'The radial multiplier must be affine and defined')
        num=m.simplify(m.add(m.add(m.mul(t,B),m.neg(m.mul(A,u))),C))
        formula=m.simplify(m.div(num,rst));end=[]
        for s in (-1,1):
            z=m.simplify(m.add(h,m.mul(q(s),radius)))
            sign=constant_sign(m.simplify(m.substitute(num,{v:z})),ctx)
            require(sign in (-1,0,1),'The sign of the original combined numerator at the endpoint remains unresolved')
            end.append(dict(point=z,slope_from_inside=ZERO if sign==0 else '+inf' if sign==1 else '-inf'))
        val=dict(formula=formula,closed_natural_interval=(end[0]['point'],end[1]['point']),
                 ordinary_chart='open relative interior',endpoints=end)
        plan.update(common_radicand=B,normalized_phase=phase,combined_numerator=num)
        steps=('Привести радикал и арксинус к одному радиусу. Продифференцировать внутри интервала и сложить слагаемые с общим положительным знаменателем.',
               'Целый числитель либо имеет простой или более высокий ноль, либо имеет ненулевой след. Знаменатель стремится к нулю как квадратный корень расстояния до края. Теорема Лагранжа переносит вычисленный предел на относительную производную.')
    else:
        require(phi==('asin',v) and len(pars)==1 and not conditions,'Need one fixed phase rate on the inverse-sine chart')
        a=('s',pars[0]);text=f'{pars[0]}*asin({x})';u=m.parse(text,x,pars)
        target=m.parse(f'exp({text})*(cos({text})+sin({text}))',x,pars)
        require(raw==target,'The outer trigonometric and exponential phases must agree exactly')
        formula=m.div(m.mul(q(2),m.mul(a,m.mul(('exp',u),('cos',u)))),('sqrt',m.add(ONE,m.neg(m.power(v,2)))))
        edges=[]
        for s in (-1,1):
            t=m.mul(q(s,2),m.PI);p=m.mul(a,t)
            finite=m.mul(q(2*s),m.mul(m.power(a,2),m.mul(('exp',p),('sin',p))))
            edges.append(dict(point=q(s),zero_parameter_derivative=ZERO,nonzero_cosine={
                'direction_of_infinity':m.mul(a,('cos',p))},zero_cosine={'finite_relative_derivative':finite}))
        val=dict(formula=formula,closed_natural_interval=(q(-1),ONE),ordinary_chart='open relative interior',endpoints=edges)
        plan.update(original_phase=phi,constant_rate=a)
        steps=('Использовать координату u=arcsin x. Слагаемые производной наружного произведения сокращаются до 2a exp(au)cos(au).',
               'На каждом краю cos u стремится к нулю из положительных чисел. При ненулевом следе cos(au) получаем бесконечность по знаку; в общем нуле делим первые ненулевые линейные члены косинусов. Случай a=0 даёт постоянную функцию.')
    return higher_certificate(lib,'relative_endpoint_slopes_from_common_inverse_sine_chart',dict(source=raw,conditions=conditions),
            val,*steps,**plan)


def folded_inverse_sine_fraction(task,lib):
    x,pars,conditions,ctx=scalar_context(task);v=('v',x)
    require(len(pars)==1 and not conditions,'Expected one fixed trigonometric angle')
    a=('s',pars[0]);S,C=('sin',a),('cos',a);s,c=('sin',v),('cos',v)
    target=m.parse(f'asin(sin({pars[0]})*sin({x})/(1-cos({pars[0]})*cos({x})))',x,pars);D=target[1][2]
    raw=m.parse(task['function'],x,pars)
    require(raw==target,'The original sine products and denominator must agree')
    G=m.add(c,m.neg(C));volume=m.div(m.mul(S,('sign',G)),D)
    return higher_certificate(lib,'folded_inverse_sine_derivative_from_square_gap',dict(original_denominator=D,fixed_angle=a),
        dict(source_domain=('nonzero',D),formula=volume,zero_sine_parameter='constant zero wherever defined',
             folds=dict(condition=('zero',G),requires_nonzero_parameter_sine=True,
                 left=m.div(m.mul(S,('sign',s)),D),right=m.div(m.neg(m.mul(S,('sign',s))),D))),
        'Знаменатель неотрицателен как разность единицы и произведения косинусов. Сохранить исключение его нулей.',
        'По тождеству синуса и косинуса квадрат дополнения аргумента равен (cos x−cos a)²/D². Это обосновывает исходный арксинус и даёт модуль при извлечении корня.',
        'Нулевой синус параметра даёт постоянную ветвь. Иначе в точках равенства косинусов знак разности меняется, потому что синус переменной ненулевой. Теорема Лагранжа даёт указанные относительные наклоны.')


def complete_source_endpoint_table(task,lib):
    wanted=['finite_derivative','natural_domain_and_boundary_notes']
    contract(task,{'function'},wanted if 'requested_output' in task else None,params=True,conditions=True)
    require(task.get('requested_output',wanted)==wanted,'The full original derivative and endpoint report is required')
    if task['function'].startswith('asin(sin('):return folded_inverse_sine_fraction(task,lib)
    spec='compensating_arc' if 'sqrt(' in task['function'] else 'exponential_harmonic'
    return source_table_endpoint_transport(task,lib,spec)


NOTATION_NOTES=(
    # A transcription note is accepted only together with the node it describes in the untouched tree.
    (re.compile(r'(\w+)-th root of (\w+)'),lambda a,x:('rpow',m.parse(a[2],x),('div',ONE,m.parse(a[1],x)))),
    (re.compile(r'Colon denotes division\.'),lambda a,x:'div'),
    (re.compile(r'cth\((.+)\) encoded as cosh\(\1\)/sinh\(\1\)'),
     lambda a,x:('div',('cosh',m.parse(a[1],x)),('sinh',m.parse(a[1],x)))),
)


def bound_notation(task,x,raw):
    """Check a printed-notation note against the raw tree and remove it from the provenance."""
    src=task.get('source',{})
    if not isinstance(src,dict) or 'source_notation' not in src:return task
    label=src['source_notation'];nodes=[e for _,e in expression_positions(raw)]
    for pattern,node in NOTATION_NOTES:
        found=pattern.fullmatch(label) if isinstance(label,str) else None
        if not found:continue
        wanted=node(found,x)
        require(any(e[0]==wanted for e in nodes) if isinstance(wanted,str) else wanted in nodes,
                'The notation note does not describe a node of the original expression')
        return dict(task,source={k:v for k,v in src.items() if k!='source_notation'})
    raise Unsupported('The original notation is not bound by the table')


def variable_conditions(task,x):
    """Separate strict conditions on the variable itself; they are compared with the derived domain."""
    own=[];rest=[]
    for c in task.get('stated_conditions',[]):
        text=c.replace(' ','') if isinstance(c,str) else None
        found=re.fullmatch(rf'({NAME})([<>])(-?\d+(?:/\d+)?)',text or '')
        if found and found[1]==x:own.append((1 if found[2]=='>' else -1,Fraction(found[3])))
        else:rest.append(c)
    return own,(dict(task,stated_conditions=rest) if own else task)


def monotone_guard_domain(guards,x,ctx):
    """Push every source guard through strictly monotone outer functions down to affine sign conditions."""
    from ordinary_series import constant_sign
    rays=[];holes=[]
    def fixed(e):
        if not m.variable_in(e,x):
            s=constant_sign(e,ctx)
            require(s is not None,'A constant sign in a source guard is not decided')
            return s
        op=e[0]
        if op in ('cosh','exp','rpow'):return 1
        if op in ('mul','div'):
            a,b=fixed(e[1]),fixed(e[2])
            return a*b if a and b else None
        if op=='pow':
            a=fixed(e[1])
            return a if a is None or e[2]%2 else abs(a)
        return None
    def affine_pair(e):
        try:p,d=poly.rf(e,x)
        except (poly.NotRational,poly.Undefined):return None
        if len(d)!=1 or len(p)!=2:return None
        return p[1]/d[0],p[0]/d[0]
    def positive(e,s):
        g=fixed(e)
        if g is not None:
            require(g*s>0,'The original real domain is empty');return
        line=affine_pair(e)
        if line:rays.append((s*line[0],s*line[1]));return
        op=e[0]
        if op=='ln':positive(m.add(e[1],q(-1)),s)
        elif op in ('sinh','tanh','atan','asin','cbrt'):positive(e[1],s)
        elif op=='sqrt':
            require(s>0,'The original real domain is empty');positive(e[1],1)
        elif op=='pow' and e[2]%2:positive(e[1],s)
        elif op=='pow':
            require(s>0,'The original real domain is empty');nonzero(e[1])
        elif op in ('mul','div'):
            a,b=fixed(e[1]),fixed(e[2])
            require((a is None)!=(b is None),'A product guard needs one factor of constant sign')
            positive(e[2] if b is None else e[1],s*(a or b))
        else:raise Unsupported('No monotone reduction for the source guard '+op)
    def nonzero(e):
        g=fixed(e)
        if g is not None:
            require(g!=0,'The original real domain is empty');return
        line=affine_pair(e)
        if line:holes.append(-line[1]/line[0]);return
        op=e[0]
        if op=='ln':nonzero(m.add(e[1],q(-1)))
        elif op in ('sinh','tanh','atan','asin','cbrt','sqrt','pow'):nonzero(e[1])
        elif op=='mul':nonzero(e[1]);nonzero(e[2])
        elif op=='div':nonzero(e[1])
        else:raise Unsupported('No monotone reduction for the source guard '+op)
    for relation,e in guards:
        require(relation in ('positive','nonzero'),'A closed boundary needs a one-sided derivative argument')
        (positive(e,1) if relation=='positive' else nonzero(e))
    lower=max((-b/a for a,b in rays if a>0),default=None)
    upper=min((-b/a for a,b in rays if a<0),default=None)
    require(lower is None or upper is None or lower<upper,'The original real domain is empty')
    inside=sorted({h for h in holes if (lower is None or h>lower) and (upper is None or h<upper)})
    return dict(lower='-inf' if lower is None else q(lower),upper='+inf' if upper is None else q(upper),
                excluded=[q(h) for h in inside])


def isolated_polynomial_roots(g):
    """Sturm isolation of all real roots; every root must be simple."""
    from graphs import sturm_intervals
    dg=tuple(i*c for i,c in enumerate(g) if i)
    require(len(g)>1 and len(poly.pgcd(g,dg))==1,'Every zero of the radicand must be simple')
    _,cells,_=sturm_intervals(g)
    return sorted(cells),dg


def sign_at_isolated_root(g,cell,value,rounds=48):
    """Shrink the isolating cell by exact bisection until an interval evaluation has one sign."""
    lo,hi=cell
    if lo!=hi and not peval(g,hi):lo=hi
    for _ in range(rounds):
        try:a,b=value((lo,hi))
        except (Unsupported,ArithmeticError):a,b=-1,1
        if a>0 or b<0 or a==b==0:return (a>0)-(b<0),(lo,hi)
        if lo==hi:break
        mid=(lo+hi)/2;s=peval(g,mid)
        if not s:lo=hi=mid
        elif (s>0)==(peval(g,hi)>0):hi=mid
        else:lo=mid
    return None,(lo,hi)


def cube_root_factor_profile(raw,x,ctx,lib):
    """One cube root of a polynomial times a multiplier that is smooth on the whole line."""
    from functools import reduce
    from quadrature import enclose
    from scalar_proofs import global_guard
    def factors(e):
        return [*factors(e[1]),*factors(e[2])] if e[0]=='mul' else [e]
    fs=factors(raw);rs=[e for e in fs if e[0]=='cbrt']
    require(len(rs)==1,'Need one cube root factor with a separately smooth multiplier')
    root=rs[0];rest=[f for f in fs if f!=root];p=reduce(m.mul,rest,ONE);g=root[1]
    require(not domain_conditions(g) and all(global_guard(h,x,ctx) for h in domain_conditions(p,True)),
            'The original multiplier and inner polynomial must be smooth on all real inputs')
    pv,dv=poly.rf(g,x)
    require(len(dv)==1,'The radicand must be a polynomial')
    pv=tuple(c/dv[0] for c in pv);cells,dg=isolated_polynomial_roots(pv)
    def interval_poly(coefficients):
        def run(cell):
            lo,hi=cell;a=b=Fraction(0)
            for c in reversed(coefficients):
                products=[a*lo,a*hi,b*lo,b*hi];a,b=min(products)+c,max(products)+c
            return a,b
        return run
    special=[]
    for cell in cells:
        c,cell=sign_at_isolated_root(pv,cell,interval_poly(dg))
        require(c in (-1,1),'The slope of the radicand at its simple zero is not signed')
        vanishing=False
        for f in rest:
            try:hv,hd=poly.rf(f,x)
            except (poly.NotRational,poly.Undefined):continue
            common=poly.pgcd(pv,hv) if any(hv) else pv
            if len(common)>1:
                count=poly.distinct_root_counter(common)
                vanishing|=(not peval(common,cell[1])) if cell[0]==cell[1] else count(cell[0])-count(cell[1])>0
        if vanishing:a=0
        else:
            a,cell=sign_at_isolated_root(pv,cell,lambda box:enclose(p,box))
            require(a in (-1,1),'A simple root with a verified signed multiplier is required')
        slope=ZERO if a==0 else '+inf' if a*c>0 else '-inf'
        special.append(dict(isolating_interval=(q(cell[0]),q(cell[1])),radicand=g,source_value=ZERO,left=slope,right=slope,
                            finite_ordinary_derivative=ZERO if slope==ZERO else None))
    return special


def original_boundary_derivative(task,lib):
    """Finish ordinary and one-sided derivatives on the untouched expression's domain."""
    x=task.get('variable','x')
    require(isinstance(x,str) and re.fullmatch(NAME,x),'The variable is not named')
    own,rest=variable_conditions(task,x)
    x,pars,conditions,ctx=scalar_context(rest);v=('v',x)
    fn=task['function'];raw=m.parse(fn,x,pars)
    noted=rest is not task or 'source_notation' in task.get('source',{})
    rest=bound_notation(rest,x,raw)
    out=['finite_derivative','natural_domain_and_boundary_notes']
    contract(rest,{'function'},out if 'requested_output' in task else None,params=True,conditions=True)
    guards=domain_conditions(raw);smooth=domain_conditions(raw,True)
    plan=dict(source=raw,conditions=task.get('stated_conditions',[]),original_guards=guards)
    rule='raw_guards_and_leading_exceptional_derivative'
    if noted:
        require(not pars and not conditions,'A parameter family of domains needs its own partition')
        domain=monotone_guard_domain(guards,x,ctx)
        require(monotone_guard_domain([*guards,*smooth],x,ctx)==domain,
                'A table rule loses a point of the original domain; it needs a separate one-sided argument')
        for side,bound in own:
            edge=domain['lower' if side>0 else 'upper']
            require(not isinstance(edge,str) and (m.num(edge)-bound)*side>=0,
                    'The stated condition on the variable cuts the natural domain')
        plan['exact_domain']=domain;special=[];rule='monotone_guard_reduction_to_exact_domain'
        proof_steps=('Каждое условие исходной операции провести через строго монотонные внешние функции до знака линейного выражения. '
                     'Пересечение полученных лучей и исключённых точек даёт точную область; условия на переменную из постановки ею уже обеспечены.',
                     'На этой открытой области все строгие условия таблицы выполнены, поэтому таблица применяется к исходному дереву без потери точек.')
    elif raw[0]=='rpow':
        phase,gap,boundaries=folded_trig_power_chart(raw,x,ctx)
        require(not conditions,'The whole real phase is required')
        plan.update(exact_domain=gap,folding_phase=phase)
        special=boundaries
        proof_steps=('Нули синуса исключены, поскольку в них знаменатель исходного отношения обращается в ноль. Во всех других точках основание положительно.',
                     'У нуля косинуса числитель arcsin(sin² θ) имеет главный прирост −√2|Δθ|, а знаменатель имеет изменение порядка Δθ². Возведение положительного отношения в гладкую переменную степень переносит найденные односторонние наклоны.')
    elif 'cot(' in fn:
        require(not conditions,'The whole real phase is required')
        phase,gap,folds=cube_root_cotangent_chart(raw,x,ctx)
        plan.update(exact_domain=gap,folding_phase=phase)
        special=folds
        proof_steps=('Котангенс имеет простой ноль на каждом уровне cos θ=0 и исходный полюс при sin θ=0.',
                     'В окрестности нуля вынести наименьшую степень модуля. Её коэффициент и сравнение порядка с единицей определяют оба наклона.')
    elif 'cbrt(' in fn:
        require(not pars and not conditions,'Need fixed real coefficients on the whole line')
        special=cube_root_factor_profile(raw,x,ctx,lib)
        plan['exact_domain']='R'
        proof_steps=('Доказать гладкость множителя на всей прямой и изолировать по Штурму все нули подкубического полинома; все они простые.',
                     'В простом нуле кубический корень имеет порядок 1/3. Знак произведения наклона полинома и непрерывного множителя определяет обе бесконечности. При нулевом гладком множителе полный порядок больше единицы, и производная равна нулю.')
    else:raise Unsupported('No exact exceptional-point model matches this raw expression')
    formula,table_steps=table(raw,x,lib)
    return certificate(lib,rule,plan,
        dict(formula=formula,domain=plan['exact_domain'],regular_guards=smooth,exceptional_points=special),
        *proof_steps,source_expression=raw,smooth_domain=smooth,table_steps=table_steps)


def folded_trig_power_chart(raw,x,ctx):
    from integrals import affine
    from ordinary_series import constant_sign
    B,P=raw[1:]
    require(B[0]=='div' and B[1][0]=='asin' and B[2][0]=='acos' and
            all(z[0]=='pow' and z[2]==2 for z in (B[1][1],B[2][1])),'Need a square-sine inverse-angle ratio')
    f,g=B[1][1][1],B[2][1][1]
    require(f[0]=='sin' and g==('cos',f[1]) and not domain_conditions(f[1]) and
            not domain_conditions(P,True),'The same real phase and a globally smooth exponent are required')
    slope,_=affine(f[1],x);sgn=constant_sign(slope,ctx)
    require(sgn in (-1,1),'The common phase must cross each exceptional level')
    F=m.div(m.mul(q(2*sgn),m.mul(('sqrt',q(2)),slope)),m.PI)
    return f[1],(('nonzero',f),),dict(level=('zero',g),value=ONE,
            left=m.mul(F,P),right=m.neg(m.mul(F,P)),finite_derivative='zero exactly when the original exponent at the level vanishes')


def cube_root_cotangent_chart(raw,x,ctx):
    from integrals import affine
    from ordinary_series import constant_sign
    def summands(e):
        if e[0]=='add':return [*summands(e[1]),*summands(e[2])]
        return [e]
    c={};wave=None
    for term in summands(raw):
        coef,root=(term[1],term[2]) if term[0]=='mul' else (ONE,term)
        a=m.num(m.simplify(coef))
        require(a is not None and m.constant_defined(coef,ctx) and root[0]=='cbrt' and root[1][0]=='pow' and
                root[1][1][0]=='cot' and root[1][2]>0 and root[1][2]%2==0,
                'Need checked even cube-root powers of a cotangent')
        w=root[1][1]
        require(wave is None or w==wave,'All factors must use the same principal phase')
        wave=w;p=root[1][2];c[p]=c.get(p,0)+a
    require(wave and not domain_conditions(wave[1]),'The original phase must be defined everywhere')
    slope,_=affine(wave[1],x)
    require(constant_sign(slope,ctx) in (-1,1),'A nonzero affine phase is required')
    lead=min((k for k,v in c.items() if v),default=None)
    up='+inf' if lead is not None and c[lead]>0 else '-inf'
    dn='-inf' if up=='+inf' else '+inf'
    return wave[1],(('nonzero',('sin',wave[1])),),dict(level=('zero',('cos',wave[1])),
        value=ZERO,order=q(lead,3) if lead is not None else None,
        left=dn if lead is not None and lead<3 else ZERO,right=up if lead is not None and lead<3 else ZERO,
        finite_ordinary_derivative=ZERO if lead is None or lead>3 else None)


def arccos_substitution_endpoint(task,lib):
    from ordinary_series import constant_sign
    out=['finite_derivative','explicit_intermediate_variable_chain','natural_domain_and_boundary_notes']
    contract(task,{'function','required_substitution'},out,('intermediate_substitution',),True,True)
    x,pars,conditions,ctx=scalar_context(task)
    require(not pars and not conditions,'The full principal interval and fixed real coefficients are required')
    v=('v',x);raw=m.parse(task['function'],x);inside=('acos',v);u='u' if x!='u' else 'z'
    text=task.get('required_substitution')
    if text:
        name,sep,value=text.partition('=')
        require(sep and re.fullmatch(NAME,name) and name!=x and m.parse(value,x)==inside,'The required substitution differs')
        u=name
    z=('v',u);outer=m.substitute(raw,{inside:z})
    live={g for g in domain_conditions(outer,True) if m.variable_in(g[1],u)}
    require(m.variable_in(outer,u) and not m.variable_in(outer,x) and live=={('positive',z)}
            and all(known_guard(g,ctx) for g in domain_conditions(outer,True) if g[1]!=z),
            'All occurrences must descend through one arccos chart and keep the positive logarithmic guard')
    f,d=table(inside,x,lib);g,e=table(outer,u,lib)
    vpi=m.simplify(m.substitute(g,{z:m.PI}));sign=constant_sign(vpi,ctx)
    require(sign in (-1,1) and m.constant_defined(m.substitute(outer,{z:m.PI}),ctx),
            'The endpoint behavior must be proved from the raw outer function')
    derivative=m.mul(f,m.substitute(g,{z:inside}))
    return certificate(lib,'log_chart_substitution_with_relative_endpoint',dict(
        original=raw,original_guards=domain_conditions(raw),exact_domain='[-1,1)'),dict(
        inner=inside,outer=outer,substitution_variable=u,formula=derivative,
        at_left_relative='+inf' if sign<0 else '-inf',right_excluded=True),
        'Найти общее вхождение arccos и проверить, что замена охватывает исходное дерево. Положительный аргумент логарифма сохраняет левый край и исключает правый.',
        'Продифференцировать внешнее выражение и внутреннюю координату по таблице. На левом краю внешняя производная имеет проверенный ненулевой след, поэтому теорема Лагранжа переносит бесконечный наклон на исходное разностное отношение.',
        inner_table=d,outer_table=e,left_outer_slope=vpi)


def source_polar_coverage(radius,name,parameters):
    """Construct the exact inverse chart and its radial branch predicates."""
    t=('v',name);co,si=('cos',t),('sin',t)
    point=m.mul(radius,co),m.mul(radius,si)
    polar=dict(source_x_nonzero=True,angle_interval=(m.mul(q(-1,2),m.PI),m.mul(q(1,2),m.PI),False,False),
        radial_condition=('positive',radius),radii_partition='positive radial expression in the original angle interval',
        branches=[dict(sign=s,coordinates=tuple(m.mul(q(s),z) for z in point)) for s in (1,-1)],
        reconstruction='tan(t)=y/x on the principal branch, and |x|=r*cos(t); the sign of x fixes both coordinates')
    if radius[0]=='mul':
        A,F=radius[1:]
        if F[0]=='s' and A[0]!='s':A,F=F,A
        if A[0]=='s' and A[1] in parameters:
            p=A[1]
            if F==t:
                polar['radii_partition']=[dict(parameter=p+'>0',angle=name+'>0'),
                    dict(parameter=p+'<0',angle=name+'<0'),dict(parameter=p+'=0',angle='empty')]
            elif F==('add',ONE,co) or F==('add',co,ONE) or F[0]=='exp' and not domain_conditions(F):
                polar['radii_partition']=[dict(parameter=p+'>0',angle='whole principal interval'),
                    dict(parameter=p+'<=0',angle='empty')]
    return polar
