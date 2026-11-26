"""Typed goal compilation into the one limit graph, with explicit domain scope.

This module constructs a definition, not an answer or a second solver.
The verifier reconstructs the same compilation and replays the inner proof.
"""
import re
import expressions as m
import intervals as real_intervals
from model import canonical,freeze,q,rational,ONE,ZERO,Unsupported
from operations import WINDOW_SIDES, expression_positions, finite_endpoint_symbol


def bind_printed_geometry(task,field,value):
    """Check the source tag or direction even when the expected task and certificate agree."""
    text=task.get('source',{}).get('literal_requirement','')
    if not isinstance(text,str):raise Unsupported('The printed geometric requirement must be text')
    text=text.casefold().replace('_',' ').replace('-',' ')
    if field=='sample':
        if not re.search(r'вершин|угл|corner|sample point|tagged point',text):return
        axes=((('upper',r'верхн\w*|upper|top'),('lower',r'нижн\w*|lower|bottom')),
              (('right',r'прав\w*|right'),('left',r'лев\w*|left')))
        words=[]
        for directions in axes:
            match=[key for key,pattern in directions if re.search(r'\b(?:'+pattern+r')\b',text)]
            if len(match)!=1:raise Unsupported('An unambiguous printed sampling corner is required')
            words.extend(match)
        stated='_'.join(words)
    else:
        if not re.search(r'часов\w*\s+стрелк|clockwise',text):return
        matches=re.findall(r'\b(против(?:\s+хода)?|по(?:\s+ходу)?)\s+часов\w*\s+стрелк\w*\b|\b((?:counter\s*|anti\s*)?clockwise)\b',text)
        directions={('counterclockwise' if a.startswith('против') or b.startswith(('counter','anti')) else 'clockwise') for a,b in matches}
        if len(directions)!=1:raise Unsupported('An unambiguous printed direction of traversal is required')
        stated=directions.pop()
    if stated!=value or re.search(r'\b(?:не|необходимо\s+избегать|not|except)\b',text):
        raise Unsupported('The geometric choice contradicts the printed requirement: '+field)


def source(e):
    """Lossless parser-compatible text; never cancel original domain restrictions."""
    e=freeze(e);op=e[0]
    if op=='q':return str(e[1]) if e[2]==1 else f'({e[1]}/{e[2]})'
    if op in ('v','s'):return e[1]
    if op=='pi':return 'pi'
    if op in ('min','max'):return op+'('+source(e[1])+','+source(e[2])+')'
    if op in m.FUNCTIONS or op=='factorial':return op+'('+source(e[1])+')'
    if op=='pow':return '('+source(e[1])+')^('+str(e[2])+')'
    if op=='rpow':return '('+source(e[1])+')^('+source(e[2])+')'
    if op in ('add','mul','div'):return '('+source(e[1])+{'add':'+','mul':'*','div':'/'}[op]+source(e[2])+')'
    raise Unsupported('Не поддерживается запись выражения: '+str(op))


def domain_conditions(e,smooth=False,*,positive_integer_exponents=()):
    e=freeze(e);op=e[0];out=[]
    for child in e[1:]:
        if isinstance(child,tuple):out.extend(domain_conditions(child,smooth,positive_integer_exponents=positive_integer_exponents))
    if op=='div':out.append(('nonzero',e[2]))
    elif op=='pow' and e[2]<=0:out.append(('nonzero',e[1]))
    elif op=='ln' or op=='rpow' and e[2] not in positive_integer_exponents:out.append(('positive',e[1]))
    elif op=='sqrt':out.append(('positive' if smooth else 'nonnegative',e[1]))
    elif op in ('cbrt','abs') and smooth:out.append(('nonzero',e[1]))
    elif op in ('tan','sec'):out.append(('nonzero',('cos',e[1])))
    elif op in ('cot','csc'):out.append(('nonzero',('sin',e[1])))
    elif op in ('asin','acos'):
        out.append(('positive' if smooth else 'nonnegative',('add',ONE,('mul',q(-1),('pow',e[1],2)))))
    return list({canonical(g):g for g in out}.values())


def guard_source(g):
    relation,e=g
    return source(e)+{'nonzero':'!=0','positive':'>0','nonnegative':'>=0'}[relation]


def known_guard(g,ctx):
    relation,e=g
    if not m.constant_defined(e,ctx):return False
    if relation=='nonzero':return m.nonzero(e,ctx)
    if relation=='positive':return m.sign(e,ctx)==1
    return m.known_nonnegative(e,ctx)


def compile_derivative(task):
    fields={'kind','function','variable','point','parameters','stated_conditions','method_requirement',
            'schema','id','source','transcription','requested_output'}
    ignored={'stated_domain','variable_domain','parameter_conditions','assumptions','conditions','domain','approach'}
    if set(task)-fields-ignored or any(k in task and task[k] not in (None,[],()) for k in ignored):
        raise Unsupported('Неизвестные поля или неподдерживаемые ограничения производной')
    if 'method_requirement' in task and task['method_requirement'] not in ('from_definition','table_and_rules'):
        raise Unsupported('Неизвестное требование метода производной')
    outputs=task.get('requested_output',[])
    if not isinstance(outputs,(list,tuple)) or any(o not in ('derivative_formula','finite_derivative','natural_domain_and_boundary_notes') for o in outputs):
        raise Unsupported('Не поддержан запрошенный результат вычисления производной')
    kind=task.get('kind');variable=task.get('variable','x')
    if kind not in ('differentiate','derivative_at'):raise Unsupported('Неизвестный вид производной')
    if kind=='differentiate' and 'point' in task:raise Unsupported('Точка допустима только для производной в точке')
    if not isinstance(task.get('parameters',[]),(list,tuple)) or not isinstance(task.get('stated_conditions',[]),(list,tuple)):
        raise Unsupported('Неверный список параметров или условий производной')
    for p in task.get('parameters',[]):
        if not isinstance(p,str) and (not isinstance(p,dict) or set(p)-{'symbol','domain','independent_of'}):
            raise Unsupported('Неизвестные ограничения постоянного параметра')
    if not all(isinstance(c,str) for c in task.get('stated_conditions',[])):
        raise Unsupported('Исходное условие должно быть строкой')
    params=[p if isinstance(p,str) else p['symbol'] for p in task.get('parameters',[])]
    m.context({'variable':variable,'parameters':task.get('parameters',[])})
    f=m.parse(task['function'],variable,params)
    names=set(params)|{variable}|m.FUNCTIONS|set(m.ALIASES)|{'pi','e'}
    def fresh(name):
        while name in names:
            name += '_'
        names.add(name);return name
    h=fresh('__h');a=fresh('__at')
    point=('s',a) if kind=='differentiate' else m.parse(str(task['point']),None,params)
    replacement={('v',variable):point}
    at=m.substitute(f,replacement)
    shifted=m.substitute(f,{('v',variable):('add',point,('v',h))})
    quotient=('div',('add',shifted,('mul',q(-1),at)),('v',h))
    stated=[]
    for condition in task.get('stated_conditions',[]):
        match=re.fullmatch(r'(.+?)\s*(!=|>|<|=)\s*(.+)',condition)
        if not match:raise Unsupported('Неподдерживаемое исходное условие производной')
        lhs,op,rhs=match.groups()
        left=m.substitute(m.parse(lhs,variable,params),replacement)
        right=m.substitute(m.parse(rhs,variable,params),replacement)
        if op=='=':
            if left[0]!='s' or right!=ZERO:raise Unsupported('Равенство параметров пока не поддерживается')
            stated.append(source(left)+'=0');continue
        delta=('add',right,('mul',q(-1),left)) if op=='<' else ('add',left,('mul',q(-1),right))
        stated.append(guard_source(('nonzero' if op=='!=' else 'positive',delta)))
    inner={'kind':'limit','expression':source(quotient),'variable':h,
           'parameters':params+([a] if kind=='differentiate' else []),
           'approach':{'point':'0','side':'both'},'parameter_conditions':stated,
           'derived_by':'derivative_definition'}
    base=m.context(inner)
    natural=domain_conditions(f);sufficient=domain_conditions(f,True)
    def remaining(conditions):
        return [g for g in conditions if not known_guard((g[0],m.substitute(g[1],replacement)),base)]
    natural_open=remaining(natural);smooth_open=remaining(sufficient)
    if kind=='differentiate':
        inner['parameter_conditions']=stated+[guard_source((r,m.substitute(g,replacement))) for r,g in smooth_open]
    ctx=m.context(inner)
    smooth_covered=True
    if kind=='differentiate':
        original_scope=m.context({**inner,'parameter_conditions':stated+
            [guard_source((r,m.substitute(g,replacement))) for r,g in entailed_domain_guards(natural)]})
        smooth_covered=all(known_guard((r,m.substitute(g,replacement)),original_scope) for r,g in sufficient)
    return {'method':'derivative_definition','function_ast':f,'point_ast':point,'point_function_ast':at,
            'shifted_function_ast':shifted,
            'point_defined':m.constant_defined(at,ctx),'compiled_limit_task':inner,
            'natural_domain':natural,'sufficient_formula_domain':sufficient,
            'display_natural_domain':[guard_source(g) for g in natural_open],
            'display_sufficient_domain':[guard_source(g) for g in smooth_open],
            'boundary_obligations':'pending' if kind=='differentiate' and not smooth_covered else 'none_from_syntax',
            'formula_scope':{'quantified_symbol':a,'replacement_variable':variable} if kind=='differentiate' else None,
            'power_convention':'Nonintegral real powers use positive bases; real odd roots must be expressed with cbrt.',
            'domain_formulas_are_not_solved_intervals':True}


def compile_point_derivative_side(compilation,side,order):
    """Bind the same original function to a punctured right-interval MVT goal."""
    if side not in ('right','left'):raise Unsupported('Неизвестная сторона производной')
    if type(order) is not int or not 1<=order<=12:raise Unsupported('Недопустимая точность производной')
    inner=compilation['compiled_limit_task']
    ctx=m.context(inner);ctx['order']=order;ctx['evaluation_side']=side
    raw=freeze(compilation['shifted_function_ast'])
    shifted_task={**inner,'expression':source(raw),'derived_by':'point_derivative_mvt'}
    expression,normalization=m.normalized(shifted_task,ctx,side)
    return {'side':side,'order':order,'context':ctx,'normalization':normalization,
            'raw_shifted_function':raw,'normalized_expression':expression,
            'goal':('point_derivative',expression)}


def inverse_definition_profile(task):
    """Recognize a fully defined affine argument before using an inverse relation."""
    from integrals import affine
    if (task.get('kind')!='differentiate' or task.get('method_requirement')!='from_definition'
            or task.get('stated_conditions') or not isinstance(task.get('function'),str)):
        return None
    try:
        compiled=compile_derivative(task);f=compiled['function_ast'];var=task.get('variable','x')
        if f[0] not in ('sqrt','cbrt','asin','acos','atan') or domain_conditions(f[1]):return None
        slope,offset=affine(f[1],var);s=m.num(slope)
        if s is None or not s:return None
        ctx=m.context(compiled['compiled_limit_task'])
        if not m.constant_defined(offset,ctx):return None
    except (Unsupported,ArithmeticError,TypeError,ValueError):
        return None
    return compiled,f,var,s,offset


def inverse_definition_derivative(task,library):
    if not library.data.get('inverse_definition_differences'):
        raise Unsupported('No admitted difference identities for the defining inverse')
    profile=inverse_definition_profile(task)
    if profile is None:raise Unsupported('The original affine inverse and assigned domain are unavailable')
    compiled,f,var,s,offset=profile;operator,u=f;x=('v',var);power=lambda a,n:('pow',a,n)
    pos=1 if s>0 else -1;direction=pos;boundaries=[]
    if operator in ('sqrt','cbrt'):
        degree=2 if operator=='sqrt' else 3
        factor=('mul',q(degree),f if degree==2 else power(f,2))
        equation='U^2-V^2=(U-V)(U+V)' if degree==2 else 'U^3-V^3=(U-V)(U^2+UV+V^2)'
        argument=['Обозначим два исходных значения корня U и V. Их степени различаются ровно на a·h, где a — наклон внутреннего выражения.',
                  'Раскладываем разность степеней. На исходной проколотой области получаем разностное отношение a, делённое на сумму степенных произведений.',
                  'Эта сумма стремится к ненулевой величине при ненулевом корне. При нулевом корне масштаб знаменателя равен |a·h|^((d−1)/d).']
        ends=[(0,('right',) if s>0 else ('left',))] if degree==2 else [(0,('left','right'))]
    else:
        direction=-pos if operator=='acos' else pos
        if operator=='atan':
            factor=('add',ONE,power(u,2));ends=[]
            equation='tan(U)-tan(V)=sin(U−V)/(cos(U)cos(V))'
        else:
            factor=('sqrt',('add',ONE,('mul',q(-1),power(u,2))))
            equation=('sin(U)-sin(V)=2 sin((U−V)/2) cos((U+V)/2)' if operator=='asin'
                      else 'cos(U)-cos(V)=−2 sin((U−V)/2) sin((U+V)/2)')
            ends=[(wall,('right' if -wall*pos>0 else 'left',)) for wall in (-1,1)]
        argument=['Вводим исходные значения обратной функции U,V. Они лежат на главной ветви и U−V стремится к нулю по её непрерывности.',
                  'Разность значений прямой функции равна a·h. Применяем точное тождество и основной предел sin t/t. Сохраняем знак синуса или косинуса на главной ветви.',
                  'На краю ветви линейный множитель обращается в ноль. В том же тождестве остаётся квадрат фазового приращения, и модуль разностного отношения неограниченно растёт.']
        if operator=='atan':argument.pop()
    numerator=q(-s if operator=='acos' else s)
    formula=m.div(numerator,factor)
    for wall,sides in ends:
        location=m.simplify(m.div(m.add(q(wall),m.neg(offset)),q(s)))
        limits={side:('+inf' if direction>0 else '-inf') if side in sides else 'no_original_approach'
                for side in ('left','right')}
        boundaries.append(dict(point=location,inner_value=q(wall),one_sided_quotient_limits=limits))
    if boundaries:argument.append('Проверяем обе стороны каждой границы. На допустимой стороне знак берётся из монотонности исходного корня или главной обратной ветви.')
    return dict(theorem='method.difference_of_defining_inverse_values',argument=argument,identity=equation,
                original_function=f,variable=x,affine_slope=q(s),affine_offset=offset,
                source_domain=compiled['natural_domain'],verified_boundaries=boundaries),dict(
                derivative=formula,natural_domain=compiled['natural_domain'],
                finite_derivative_domain=compiled['sufficient_formula_domain'],boundary=boundaries)


def derivative_conclusion(task,compilation,child):
    status=child['status'];value=None
    result={'status':status,'value':None,'formula_scope':compilation['formula_scope'],
            'boundary_obligations':compilation['boundary_obligations'],
            'method_status':'pointwise_elementary_derivative_table' if child.get('schema')=='original-table-derivative/v1' else 'mvt_local_derivative_limit' if child.get('schema')=='point-derivative-chain-run/v1' else 'definition_quotient'}
    if status=='SOLVED_CASES':
        result['status']='CASE_FORMULA_REVIEW_PENDING'
    elif task['kind']=='derivative_at' and status in ('DOMAIN_ERROR','DOES_NOT_EXIST'):
        result['status']='NO_FINITE_DERIVATIVE'
    elif status=='SOLVED' or child.get('schema')=='original-table-derivative/v1' and status=='FORMULA_ON_SUFFICIENT_DOMAIN':
        value=freeze(child['value'])
        if value in ('+inf','-inf'):result['status']='NO_FINITE_DERIVATIVE'
        elif task['kind']=='differentiate':
            scope=compilation['formula_scope']
            value=m.substitute(value,{('s',scope['quantified_symbol']):('v',scope['replacement_variable'])})
            if compilation['boundary_obligations']=='pending':result['status']='FORMULA_ON_SUFFICIENT_DOMAIN'
        result['value']=value
    if task.get('method_requirement')=='from_definition' and status in ('SOLVED','SOLVED_CASES'):
        def rules(node):
            if 'cases' in node:return set().union(*(rules(c) for c in node['cases']))
            return {n['rule'] for s in node.get('sides',[]) for n in (s.get('proof') or {}).get('nodes',[])}
        selected=rules(child)
        if any(r.startswith(('derivative.','limit.lhopital','point_derivative.')) for r in selected) or selected.intersection({'germ.asin','germ.atan'}):
            result['method_status']='direct_definition_method_review_pending'
            if result['status'] in ('SOLVED','FORMULA_ON_SUFFICIENT_DOMAIN'):result['status']='METHOD_REVIEW_PENDING'
    return result


def compile_global_task(task,library):
    kind=task.get('kind',task.get('task_type'))
    compilers=library.data.get('task_compilers',{});method=compilers.get(kind)
    if kind=='cartesian_field_operator' and library.data.get('cartesian_boundary_flux'):
        from cartesian_fields import compile_operator
        return compile_operator(task)
    if kind=='series_convergence' and 'series_classification' in library.data['predicates']:
        from finite_sums import compile_series_bound
        return compile_series_bound(task)
    if kind=='functional_series_convergence_set' and 'parameter_series_sets' in library.data['predicates']:
        from finite_sums import compile_functional_series
        return compile_functional_series(task)
    if kind=='formal_vector_identity' and method=='cartesian_component_identity':
        from cartesian_fields import compile_identity
        return compile_identity(task)
    if kind in ('proof','prove') and method=='finite_sum_identity':
        goal=task.get('goal')
        if (isinstance(goal,dict) and isinstance(goal.get('proposition'),str) and
                not re.search(r'\bsum\s*\(',goal['proposition']) and compilers.get('prove_equality')=='scoped_real_equality'):
            return compile_real_equality(task)
        from finite_sums import compile_sum
        return compile_sum(task)
    if kind in ('real_inequality','solve_real_inequality') and method=='quadratic_real_partition':
        return compile_real_inequality(task)
    if kind=='prove_equality' and method=='scoped_real_equality':
        return compile_real_equality(task)
    if kind in ('proof_about_real_functions','prove_continuity') and method=='relative_real_continuity':
        return compile_continuity(task)
    if kind=='prove_boundedness' and method=='closed_ray_bound':
        return compile_continuity(task)
    raise Unsupported('В этом снимке не объявлен метод для исходной цели')


def interval_continuity_claim(statement):
    """Bind each moving end and dummy variable to the interval in the source."""
    name=r'[A-Za-z][A-Za-z0-9_]*'
    match=re.fullmatch(rf'(?i:При непрерывной) ({name}) (?i:на) \[({name}),\s*({name})\] '
                       rf'(?i:доказать непрерывность) (.+) (?i:на) \[\2,\s*\3\]',statement)
    if not match:return None
    function,left,right,claim=match.groups()
    expressions=[];labels=set()
    for item in re.split(r',\s*(?=[A-Za-z]\w*\s*\()|\s+и\s+',claim):
        bound=re.fullmatch(rf'({name})\(({name})\)\s*=\s*(inf|sup)_\{{({name})≤([^\W\d]\w*)≤({name})\}}'
                           rf'\s*{re.escape(function)}\(\5\)',item.strip())
        if not bound:raise Unsupported('Не распознаны все границы экстремума и аргумент исходной функции')
        label,variable,op,lo,dummy,hi=bound.groups()
        if (label in labels or {label,variable,dummy}.intersection({function,left,right})
                or len({label,variable,dummy})!=3):
            raise Unsupported('Обозначения границ, функции и связанных переменных должны различаться')
        if (lo,hi)==(left,variable):side='prefix'
        elif (lo,hi)==(variable,right):side='suffix'
        else:raise Unsupported('Промежуток экстремума не совпадает с заявленной движущейся частью отрезка')
        labels.add(label);expressions.append(f'{side}_{op}({function})')
    return [function],expressions,[left,right]


def compile_continuity(task):
    """Read premises and *every* continuity conclusion on one arbitrary real domain."""
    common={'kind','id','source','requested_output'}
    reference=task.get('source',{})
    if not isinstance(reference,dict) or set(reference)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_pages','pdf_sha256'}:
        raise Unsupported('Дополнительные сведения в источнике требуют разбора условий задачи')
    if task.get('requested_output',['proof'])!=['proof']:
        raise Unsupported('Дополнительный требуемый результат не разобран')
    if task['kind'] in ('proof_about_real_functions','prove_boundedness'):
        bound=compile_ray_bound(task,common)
        if bound is not None:return bound
    interval=None
    if task['kind']=='proof_about_real_functions':
        if set(task)-common-{'statement'} or not isinstance(task.get('statement'),str):
            raise Unsupported('Не разобраны поля исходного утверждения')
        statement=task['statement'].strip().removesuffix('.')
        clause=r'\s+доказать\s+непрерывность\s+(.+)'
        match=(re.fullmatch(r'Если\s+(.+?)\s+непрерывна\s*,'+clause,statement,re.I) or
               re.fullmatch(r'Для\s+непрерывных\s+(.+?)'+clause,statement,re.I))
        if match:
            functions=continuous=re.split(r'\s+и\s+|\s*,\s*',match[1])
            expressions=re.split(r'\s+и\s+',match[2])
        else:
            parsed=interval_continuity_claim(statement)
            if not parsed:raise Unsupported('Не разобраны все условия и выводы теоремы о функциях')
            functions,expressions,interval=parsed
            continuous=functions
    else:
        if set(task)-common-{'functions','continuous_functions','expressions','closed_interval'}:
            raise Unsupported('Не разобраны условия или дополнительные требования непрерывности')
        functions=task.get('functions');continuous=task.get('continuous_functions');expressions=task.get('expressions')
        if 'closed_interval' in task:
            interval=task['closed_interval']
            if not isinstance(interval,list) or len(interval)!=2:raise Unsupported('Нужны оба конца отрезка')
    operators=('min','max',*WINDOW_SIDES) if interval is not None else ('min','max')
    reserved=m.FUNCTIONS|m.ALIASES.keys()|{'lg','pi','e',*operators}
    for names in (functions,continuous):
        if (not isinstance(names,list) or not all(isinstance(n,str) and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n)
                and n not in reserved for n in names)
                or len(names)!=len(set(names))):
            raise Unsupported('Нужен список различных имён действительных функций')
    if not set(continuous)<=set(functions):raise Unsupported('Не объявлена функция из условия непрерывности')
    if not isinstance(expressions,list) or not expressions or not all(isinstance(s,str) and s.strip() for s in expressions):
        raise Unsupported('Нужен непустой список выражений для доказательства непрерывности')
    if interval is not None:
        symbolic=all(finite_endpoint_symbol(n) and n not in reserved
                     and n not in functions for n in interval)
        numeric=all(type(n) is int for n in interval) and interval[0]<=interval[1]
        if not (symbolic or numeric):raise Unsupported('Нужны упорядоченные целые или обозначения концов замкнутого отрезка')
    leaves={('s',n):('function',n) for n in functions}
    terms=[]
    for expr in expressions:
        modulus=re.fullmatch(r'\|([^|]+)\|',expr.strip())
        raw=m.parse('abs('+modulus[1]+')' if modulus else expr,None,functions,operators)
        terms.append(m.substitute(raw,leaves))
    ctx=dict(domain='function_continuity',source_domain='arbitrary_real_subset',
             functions=functions,continuous_functions=continuous)
    if interval is not None:ctx.update(source_domain='closed_real_interval',interval_endpoints=interval)
    goal=('continuous_on',terms[0]) if len(terms)==1 else ('all_continuous',tuple(terms))
    return dict(method='relative_real_continuity',context=ctx,goal=goal)


def compile_ray_bound(task,common):
    name=r'[A-Za-z][A-Za-z0-9_]*'
    if task['kind']=='proof_about_real_functions':
        text=task.get('statement')
        if not isinstance(text,str):return None
        match=re.fullmatch(rf'Если ({name}) (непрерывна|определена) на (?:\[({name}),\+∞\)|\(-∞,({name})\])'
                           r'(?: и существует конечный предел на ([+-]∞))?, то \1 ограничена на этом промежутке\.?',
                           text.strip().replace('−','-'))
        if not match:return None
        f,property_name,right,left,end=match.groups()
        if set(task)-common-{'statement'} or end is not None and (end=='+∞')!=bool(right):
            raise Unsupported('Дополнительные требования или предел вне исходного луча')
        endpoint,side=right or left,'right' if right else 'left'
        continuous,finite=property_name=='непрерывна',end is not None
    else:
        if set(task)-common-{'function','ray_endpoint','ray_side','continuous','finite_limit_at_infinite_end'}:
            raise Unsupported('Не разобраны все условия ограниченности на луче')
        f,endpoint,side=(task.get(k) for k in ('function','ray_endpoint','ray_side'))
        continuous=task.get('continuous',False)
        finite=task.get('finite_limit_at_infinite_end',False)
    if (not isinstance(f,str) or not re.fullmatch(name,f) or not finite_endpoint_symbol(endpoint) or f==endpoint
            or side not in ('left','right') or type(continuous) is not bool or type(finite) is not bool):
        raise Unsupported('Требуются именованная функция, конечный конец луча, сторона и точные гипотезы')
    ctx=dict(domain='function_continuity',source_domain='closed_real_ray',ray_endpoint=endpoint,ray_side=side,
             functions=[f],continuous_functions=[f] if continuous else [],finite_end_limits=[f] if finite else [])
    return dict(method='closed_ray_bound',context=ctx,goal=('bounded_on',('function',f)))


def equality_domain_witness(symbols,comparisons,guards):
    """Construct a point in the declared scope; certify it on the raw comparisons."""
    empty={'parameters':[],'assumptions':[]}
    def holds(guard,values):
        relation,raw=guard
        return known_guard((relation,m.substitute(raw,values)),empty)
    local_guards=tuple(dict.fromkeys((*guards,*entailed_domain_guards(guards))))
    for seed in (ZERO,ONE,q(-1)):
        values={}
        for i,atom in enumerate(symbols):
            later=symbols[i+1:]
            relevant=[g for g in local_guards if m.contains(g[1],atom) and not any(m.contains(g[1],v) for v in later)]
            if not relevant:
                values[atom]=seed
                continue
            bounds=[]
            for left,_,right in comparisons:
                if atom not in (left,right):continue
                bound=m.substitute(right if left==atom else left,values)
                if m.constant_defined(bound,empty):bounds.append(m.simplify(bound))
            # Candidate coordinates need only discovery. Every accepted comparison is checked exactly.
            candidates=[seed,ZERO,ONE,q(-1),q(2),q(-2),m.mul(q(1,2),m.PI),m.mul(q(1,4),m.PI)]
            candidates.extend(m.add(b,offset) for b in bounds for offset in (ONE,q(-1)))
            candidates.extend(m.mul(q(1,2),m.add(a,b)) for j,a in enumerate(bounds) for b in bounds[j+1:])
            point=next((u for u in dict.fromkeys(candidates) if all(holds(g,{**values,atom:u}) for g in relevant)),None)
            if point is None:break
            values[atom]=point
        else:
            if all(holds(g,values) for g in guards):return {atom[1]:value for atom,value in values.items()}
    raise Unsupported('Не удалось подтвердить непустоту заявленной области точной подстановкой')


def compile_real_equality(task):
    """Equality at every declared real point; neither side supplies premises."""
    fields={'kind','variable','parameters','assumptions','punctured_at','id','source','source_number','schema'}
    kind=task.get('kind',task.get('task_type'))
    proposition=kind in ('prove','proof')
    if proposition:
        fields.update({'goal','task_type','method_requirement','requested_output','source_statement',
                       'source_edition','source_pdf_page','transcription_notes','program_status'})
        goal=task.get('goal')
        if (not isinstance(goal,dict) or set(goal)!={'proposition'} or task.get('method_requirement') is not None
                or task.get('requested_output',['proof'])!=['proof'] or task.get('transcription_notes')
                or any(task[k] not in ('prove','proof') for k in ('kind','task_type') if k in task)):
            raise Unsupported('Нераспознанная область, вывод или требование доказательства')
    else:fields.update({'left','right'})
    if set(task)-fields or not proposition and kind!='prove_equality':
        raise Unsupported('Неизвестные поля или ограничения доказываемого равенства')
    variable=task.get('variable','x');params=task.get('parameters',[])
    if not isinstance(params,(list,tuple)) or any(not isinstance(p,str) and
            (not isinstance(p,dict) or set(p)-{'symbol','domain','independent_of'}) for p in params):
        raise Unsupported('Некорректные объявления параметров равенства')
    names=m.context({'variable':variable,'parameters':params})['parameters']
    parse=lambda text:m.parse(text,variable,names)
    def equation(parts):
        if len(parts)!=2 or not all(isinstance(p,str) and p.strip() for p in parts):
            raise Unsupported('Нужно одно явно записанное равенство двух выражений')
        return tuple(parse(p) for p in parts)
    if proposition:
        printed=goal['proposition']
        left,right=equation(printed.split('=') if isinstance(printed,str) else ())
    else:left,right=equation((task.get('left'),task.get('right')))
    at='__at'
    while at in names or at==variable:at+='_'
    var=('v',variable);point=('s',at);comparisons=[]
    stated=task.get('assumptions',[])
    if not isinstance(stated,(list,tuple)) or not all(isinstance(s,str) for s in stated):
        raise Unsupported('Ограничения равенства должны быть списком строк')
    declared_real={s+suffix for s in [*names,variable] for suffix in (' is real',' in R','∈R')}
    stated=[s for s in stated if s.strip() not in declared_real]
    if 'source_statement' in task:
        statement=task['source_statement']
        match=re.fullmatch(r'(?:Доказать|Prove)\s*:?\s+(.+?)\.?',statement.strip(),re.I) if isinstance(statement,str) else None
        if not match or stated or 'punctured_at' in task or equation(match[1].split('='))!=(left,right):
            raise Unsupported('Печатное утверждение и его условия не связаны с предъявленной целью')
    for item in stated:
        match=re.fullmatch(r'(.+?)\s*(!=|>|<)\s*([^<>=!]+)',item)
        if not match:raise Unsupported('Ожидалось строгое сравнение или условие ненулевого значения')
        comparisons.append((parse(match[1]),match[2],parse(match[3])))
    center=None
    if 'punctured_at' in task:
        value=task['punctured_at']
        if not isinstance(value,str) and type(value) is not int:raise Unsupported('Некорректная исключённая точка')
        center=m.parse(str(value),None,names)
        comparisons.append((var,'!=',center))
    guards=[]
    for lhs,op,rhs in comparisons:
        if op=='<':lhs,rhs=rhs,lhs
        raw=lhs if rhs==ZERO else ('add',lhs,('mul',q(-1),rhs))
        guards.append(('nonzero' if op=='!=' else 'positive',raw))
    ctx=m.context({'variable':variable,'parameters':names+[at],
                   'parameter_conditions':[guard_source((r,m.substitute(e,{var:point}))) for r,e in guards]})
    witness=equality_domain_witness([*(('s',name) for name in names),var],comparisons,guards)
    ctx.update(domain='real_equality',variable=variable,point=point,point_symbol=at,side='pointwise',
               source_guards=guards[:len(stated)],punctured_at=center,domain_witness=witness)
    return {'method':'scoped_real_equality','context':ctx,'left':left,'right':right,
            'left_domain':domain_conditions(left),'right_domain':domain_conditions(right),'goal':('real_equal',left,right)}


def compile_real_inequality(task):
    """Global real-line goal; local punctured-neighborhood facts are not used."""
    spec=task.get('goal',task)
    if not isinstance(spec,dict):raise Unsupported('Неверная запись глобальной цели')
    variable=spec.get('variable',task.get('variable','x'))
    metadata={'kind','task_type','id','source_number','source_edition','source_pdf_page',
              'source_statement','transcription_notes','program_status'}
    fields={'variable','parameters','assumptions','left','relation','right','goal'}
    constraints={'stated_domain','stated_conditions','parameter_conditions','variable_domain','conditions','domain'}
    if set(task)-metadata-fields-constraints or any(k in task and task[k] not in (None,[],()) for k in constraints):
        raise Unsupported('Неизвестные поля или дополнительные ограничения неравенства не поддержаны')
    if spec is not task:
        if not isinstance(spec,dict) or set(spec)-{'variable','left','relation','right'}:
            raise Unsupported('Вложенная цель содержит неподдержанные поля или ограничения')
        if any(k in task for k in ('left','relation','right')) or 'variable' in task and task['variable']!=variable:
            raise Unsupported('Противоречащие или повторные записи цели неравенства')
    parameters=task.get('parameters',[])
    allowed={variable+' is real',variable+' in R',variable+'∈R'}
    allowed.update((p if isinstance(p,str) else p['symbol'])+' is real' for p in parameters)
    if not isinstance(task.get('assumptions',[]),(list,tuple)) or any(not isinstance(a,str) or a not in allowed for a in task.get('assumptions',[])):
        raise Unsupported('Дополнительные ограничения неравенства требуют явного представления области')
    ctx=m.context({'variable':variable,'parameters':parameters})
    ctx.update(variable=variable,point=None,side=None,order=None,domain='global_real_line',scope='all_real_points')
    if not isinstance(spec.get('relation'),str):raise Unsupported('Отношение должно быть строкой')
    relation={'≤':'<=','≥':'>=','≠':'!=','=':'=='}.get(spec['relation'],spec['relation'])
    if relation not in real_intervals.RELATIONS:raise Unsupported('Неизвестное отношение на действительной прямой')
    expression=('add',m.parse(spec['left'],variable,ctx['parameters']),
                ('mul',q(-1),m.parse(spec['right'],variable,ctx['parameters'])))
    return {'method':'quadratic_real_partition','context':ctx,'expression':expression,
            'goal':('real_solution',expression,relation),'relation':relation}


def function_sign_sets(task,lib,request):
    """Trichotomy on the unchanged original domain; each relation has its own global proof."""
    roles=(('zero set','=='),('strict positive set','>'),('strict negative set','<'))
    fields={'kind','task_type','id','source_number','source_edition','source_pdf_pages','source_statement',
            'program_status','goal','transcription_notes'}
    constraints={'parameters','assumptions','stated_domain','stated_conditions','parameter_conditions','variable_domain','conditions','domain'}
    spec=task.get('goal')
    if (not lib.data.get('function_sign_sets') or set(task)-fields-constraints or task.get('transcription_notes')
            or any(task[k]!='function_sign_sets' for k in ('kind','task_type') if k in task)
            or not isinstance(spec,dict) or set(spec)!={'variable','expression','goals'}
            or spec['goals']!=[label for label,_ in roles]):
        raise Unsupported('Unresolved source domain, sign questions or additional requirements')
    x=spec['variable'];f=spec['expression']
    ctx=m.context({'variable':x,'parameters':task.get('parameters',[])})
    expr=m.parse(f,x,ctx['parameters'])
    if 'source_statement' in task:
        printed=re.fullmatch(r'Для\s+f\((\w+)\)\s*=\s*(.*?)\s+найти\s+(\w+),\s*для\s+которых\s*(.*?)\.?',task['source_statement'])
        expected=f'1)f({x})=0;2)f({x})>0;3)f({x})<0'
        if (not printed or printed[1]!=x or printed[3]!=x or m.parse(printed[2],x,ctx['parameters'])!=expr
                or ''.join(printed[4].split())!=expected):
            raise Unsupported('Printed statements, assumptions and three requested relations must agree')
    original={k:task[k] for k in constraints if k in task}
    values={};pending=[]
    for label,relation in roles:
        child=dict(kind='real_inequality',variable=x,left=f,relation=relation,right='0',**original)
        try:values[relation]=request(label,child)['value']
        except Unsupported as exc:pending.append(str(exc))
    domain=domain_conditions(expr)
    if pending:
        guards=', '.join(guard_source(g) for g in domain) or 'all real inputs under original constraints'
        raise Unsupported(f'{len(values)}/3 sign questions proved on {guards}. '+' | '.join(pending))
    return {'variable':x,'source_expression':expr,'natural_domain':domain,'source_constraints':original},values


def entailed_domain_guards(domain):
    """Exact existing nonzero/root consequences; raw domain stays separately stored."""
    unique = lambda values: tuple({canonical(v):freeze(v) for v in values}.values())
    facts = unique(g for g in domain if g[0]!='nonnegative')
    for _ in range(12):
        more = []
        for r,e in facts:
            if r in ('positive','nonzero') and e[0] in ('mul','div'): more.extend(('nonzero',c) for c in e[1:])
            if r=='nonzero' and e[0] in ('abs','cbrt','pow'): more.append(('nonzero',e[1]))
            if r in ('positive','nonzero') and e[0]=='sqrt': more.append(('positive',e[1]))
        extended = unique(facts+tuple(more))
        if extended==facts: return facts
        facts = extended
    raise Unsupported('Domain inference bound')


def compile_partial_bundle(task,contract=None,*,expand_prefixes=True):
    fields = {'kind','function','variables','parameters','derivative_orders','requested_partials','stated_conditions',
              'method_requirement','requested_output','schema','id','source','transcription'}
    if not isinstance(task,dict) or set(task)-fields or task.get('kind') != 'partial_derivatives': raise Unsupported('Unknown partial derivative source fields')
    variables = task.get('variables'); parameters = task.get('parameters',[]); orders = task.get('derivative_orders',[1])
    if not isinstance(variables,(list,tuple)) or not 1<=len(variables)<=4 or not all(isinstance(v,str) for v in variables) or len(set(variables))!=len(variables): raise Unsupported('Invalid coordinate list')
    if not isinstance(parameters,(list,tuple)) or any(not isinstance(p,str) and (not isinstance(p,dict) or set(p)-{'symbol','domain'} or p.get('domain','real')!='real') for p in parameters): raise Unsupported('Unknown fixed parameter conditions')
    names = [p if isinstance(p,str) else p['symbol'] for p in parameters]
    requested = task.get('requested_output',[])
    selected = ()
    if 'requested_partials' in task:
        paths = task['requested_partials']; bounds = (contract or {}).get('selected_path_limits',{})
        if ('derivative_orders' in task or not bounds or not isinstance(paths,(list,tuple)) or not paths
                or expand_prefixes and len(paths)>bounds['count']):
            raise Unsupported('Expected a bounded list of selected partials without a second order specification')
        if any(not isinstance(p,(list,tuple)) or not p or expand_prefixes and len(p)>bounds['length'] or
               any(v not in variables for v in p) for p in paths):
            raise Unsupported('Invalid coordinate or length in selected partial')
        selected = tuple(map(tuple,paths))
        if len(set(selected))!=len(selected): raise Unsupported('Repeated selected partial')
        indices = tuple(dict.fromkeys(p[:k] for p in selected for k in range(1,len(p)+1))) if expand_prefixes else ()
        orders = sorted({len(p) for p in selected}); outputs = {'specified_partial_derivatives'}
    else:
        if not isinstance(orders,(list,tuple)) or any(type(o) is not int for o in orders) or tuple(orders) not in ((1,),(1,2)): raise Unsupported('Only full first and second partial bundles are supported')
        indices = [(v,) for v in variables]+([(v,w) for v in variables for w in variables] if 2 in orders else [])
        outputs = {'first_partial_derivatives'}|({'second_partial_derivatives'} if 2 in orders else set())
    if not isinstance(requested,(list,tuple)) or set(requested)-outputs: raise Unsupported('Unimplemented partial output requirement')
    method = task.get('method_requirement','table_and_rules')
    if method not in ('table_and_rules','from_definition'): raise Unsupported('Unimplemented partial derivative method')
    conditions = task.get('stated_conditions',[])
    if not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions): raise Unsupported('Invalid partial source conditions')
    dummy = '__partial_section'
    while dummy in list(variables)+names: dummy += '_'
    m.context({'variable':dummy,'parameters':list(variables)+names})
    common = m.parse(task['function'],None,list(variables)+names)
    return {'function':task['function'],'variables':tuple(variables),'parameters':names,'orders':tuple(orders),
            **({'selected_paths':selected} if selected else {}),
            'stated_conditions':tuple(conditions),'method_requirement':method,'indices':tuple(indices),
            'natural_domain':tuple(domain_conditions(common)),'domain_guards':entailed_domain_guards(domain_conditions(common)),
            'index_order':'left-to-right differentiation sequence',
            'scope':'coordinate sections only; no joint differentiability or total differential conclusion'}


def partial_child_task(plan,index,values):
    coordinate = index[-1]
    function = plan['function'] if len(index)==1 else source(values[index[:-1]])
    return {'kind':'differentiate','function':function,'variable':coordinate,
            'parameters':[v for v in plan['variables'] if v!=coordinate]+plan['parameters'],
            'stated_conditions':list(plan['stated_conditions'])+[guard_source(g) for g in plan['domain_guards']],
            'method_requirement':plan['method_requirement']}


def ordinary_kernel_plan(task,contract):
    from integrals import polynomial_affine_kernels
    spec=contract.get('ordinary_kernel_leibniz')
    selected=task.get('requested_partials')
    if not spec or not selected or len(task.get('variables',()))!=1 or task.get('stated_conditions') or task.get('method_requirement','table_and_rules')!='table_and_rules':
        raise Unsupported('Requires selected ordinary table derivatives on their original real domain')
    plan=compile_partial_bundle(task,contract,expand_prefixes=False)
    if max(plan['orders'])<3 or plan['natural_domain']:raise Unsupported('Requires a smooth globally defined polynomial kernel')
    x=plan['variables'][0];f=m.parse(task['function'],x,plan['parameters'])
    for coefficients,kernel,slope,_ in polynomial_affine_kernels(f,x):
        if m.num(slope) is None:continue
        steps=spec['kernel_steps'];tag=kernel[0];sign=1;cycle=[]
        while (tag,sign) not in cycle:
            if tag not in steps or steps[tag][1] not in (-1,1):raise Unsupported('Open elementary derivative cycle')
            cycle.append((tag,sign));tag,s=steps[tag];sign*=s
        if (tag,sign)!=cycle[0]:raise Unsupported('Nonperiodic elementary kernel')
        return {'variable':x,'parameters':plan['parameters'],'orders':tuple(map(len,plan['selected_paths'])),
                'polynomial':tuple(m.q(c) for c in coefficients),'kernel':kernel,'slope':slope,'cycle':tuple(cycle)}
    raise Unsupported('No polynomial with an affine elementary kernel')


def ordinary_kernel_children(plan):
    tags=dict.fromkeys(t for t,s in plan['cycle'])
    return [dict(kind='differentiate',function=source((t,plan['kernel'][1])),variable=plan['variable'],
                 parameters=plan['parameters'],method_requirement='table_and_rules',stated_conditions=[]) for t in tags]


def ordinary_kernel_values(plan,replay=False):
    from math import comb
    from integrals import polynomial_expression
    from polynomial import pa
    p=tuple(m.num(c) for c in plan['polynomial']);slope=m.num(plan['slope'])
    cycle=plan['cycle'];x=plan['variable'];arg=plan['kernel'][1];orders=plan['orders']
    def add_term(t,tag,poly,factor):
        t[tag]=pa(t.get(tag,(0,)),tuple(c*factor for c in poly))
    def diff(poly):return tuple(i*c for i,c in enumerate(poly) if i) or (0,)
    def formula(state):
        terms=[]
        for tag,poly in sorted(state.items()):
            if any(poly):
                factor=polynomial_expression(poly,x);kernel=(tag,arg)
                terms.append(kernel if factor==m.ONE else ('mul',factor,kernel))
        f=terms[0] if terms else m.ZERO
        for term in terms[1:]:f=('add',f,term)
        return m.substitute(f,{('v',x):('s',x)})
    if not replay:
        results=[]
        for n in orders:
            state={};poly=p
            for j in range(min(n,len(p)-1)+1):
                tag,s=cycle[(n-j)%len(cycle)]
                add_term(state,tag,poly,comb(n,j)*s*slope**(n-j));poly=diff(poly)
            results.append(formula(state))
        return tuple(results)
    # Check the n-step differential operator independently of the finite Leibniz sum.
    next_tags={tag:(cycle[(i+1)%len(cycle)][0],s*cycle[(i+1)%len(cycle)][1]) for i,(tag,s) in enumerate(cycle)}
    state={cycle[0][0]:p};by_order={}
    for n in range(1,max(orders)+1):
        after={}
        for tag,poly in state.items():
            other,s=next_tags[tag]
            add_term(after,tag,diff(poly),1);add_term(after,other,poly,s*slope)
        state=after
        if n in orders:by_order[n]=formula(state)
    return tuple(by_order[n] for n in orders)


def partial_component_value(plan,index,child):
    """Caller must replay the exact child task before accepting its common value."""
    from integrals import derivative_on_domain
    if child.get('status')!='SOLVED': raise Unsupported('Partial boundary, method or proof remains incomplete')
    coordinate = index[-1]; actual = compile_derivative(child['task'])
    original = compile_derivative({**child['task'],'function':plan['function']})
    inner = original['compiled_limit_task']; count = len(child['task']['stated_conditions'])
    ctx = m.context({**inner,'parameter_conditions':inner['parameter_conditions'][:count]})
    point = original['formula_scope']['quantified_symbol']
    if any(a['relation']=='zero' and a['symbol'] in set(plan['variables'])|{point} for a in ctx['assumptions']): raise Unsupported('Coordinate equalities need an open-neighborhood proof')
    replacement = {('v',coordinate):('s',point)}
    if not all(known_guard((r,m.substitute(e,replacement)),ctx) for r,e in original['natural_domain']): raise Unsupported('Original boundary or domain coverage remains pending')
    cover = {'variable':coordinate,'domain_point':point,'domain_context':ctx}
    value = derivative_on_domain(cover,child,actual['formula_scope']['quantified_symbol'])
    value = m.substitute(value,{('v',coordinate):('s',coordinate)})
    m.parse(source(value),None,list(plan['variables'])+plan['parameters'])
    return value


COMPOSED_GOALS={'order_certificate':('order-certificate/v1','ORDER_PROOF_PENDING'),
                'elementary_proof':('elementary-proof/v1','ELEMENTARY_PROOF_PENDING'),
                'source_integral_transform':('source-integral-transform/v1','INTEGRAL_TRANSFORM_PENDING'),
                'source_surface_field':('source-surface-field/v1','SURFACE_FIELD_PENDING'),
                'source_spatial_moment':('source-spatial-moment/v1','SPATIAL_MOMENT_PENDING'),
                'source_geometric_domains':('source-geometric-domains/v1','GEOMETRIC_DOMAIN_PENDING'),
                'source_asymptotic_proof':('source-asymptotic-proof/v1','ASYMPTOTIC_PROOF_PENDING'),
                'real_function_proof':('real-function-proof/v1','REAL_FUNCTION_PROOF_PENDING'),
                'derivative_proof':('derivative-proof/v1','DERIVATIVE_PROOF_PENDING'),
                'plane_geometry':('plane-geometry/v1','PLANE_GEOMETRY_PENDING'),
                'exact_ordinary_order':('exact-ordinary-order/v1','ORDINARY_ORDER_PENDING'),
                'measurement_uncertainty':('measurement-uncertainty/v1','MEASUREMENT_ERROR_PENDING'),
                'source_vector_calculus':('source-vector-calculus/v1','VECTOR_CALCULUS_PENDING'),
                'source_planar_composition':('source-planar-composition/v1','PLANAR_COMPOSITION_PENDING'),
                'source_geometric_application':('source-geometric-application/v1','GEOMETRIC_APPLICATION_PENDING'),
                'scalar_source_proof':('scalar-source-proof/v1','SCALAR_PROOF_PENDING'),
                'polynomial_interpolation':('verified-interpolation/v1','INTERPOLATION_PENDING'),
                'bernstein_approximation':('bernstein-polynomials/v1','BERNSTEIN_PENDING'),
                'stirling_application':('stirling-factorials/v1','STIRLING_REDUCTION_PENDING'),
                'product_and_approximation_claim':('product-approximation-proof/v1','PRODUCT_THEOREM_PENDING'),
                'applied_extremum':('normalized-applied-extremum/v1','GEOMETRIC_MODEL_PENDING'),
                'certified_numeric_approximation':('numeric-taylor-enclosure/v1','CERTIFIED_APPROXIMATION_PENDING'),
                'approximate_equation_roots':('certified-root-iterations/v1','CERTIFIED_ROOTS_PENDING'),
                'parameter_improper_evaluation':('parameter-improper-evaluation/v1','INTEGRAL_METHOD_PENDING'),
                'fourier_integral_representation':('fourier-integral-representation/v1','FOURIER_MOMENTS_PENDING'),
                'fourier_coefficient_relation':('fourier-coefficient-transport/v1','FOURIER_RELATION_PENDING'),
                'source_series_algebra':('source-series-algebra/v1','SERIES_ALGEBRA_PENDING'),
                'abstract_series_theorem':('abstract-series-theorem/v1','SERIES_THEOREM_PENDING'),
                'explicit_cauchy_series':('cauchy-series-tails/v1','CAUCHY_SERIES_PENDING'),
                'ordinary_series_proof':('ordinary-series-proof/v1','ORDINARY_SERIES_PENDING'),
                'certified_series_prefix':('certified-series-prefix/v1','SERIES_CUTOFF_PENDING'),
                'compute_limit':('structured-limit/v1','SOURCE_LIMIT_PENDING'),
                'power_series_boundary':('power-series-boundary/v1','SERIES_DOMAIN_PENDING'),
                'continuous_least_squares':('continuous-least-squares/v1','LEAST_SQUARES_PENDING'),
                'source_parameter_integral':('source-parameter-integral/v1','PARAMETER_INTEGRAL_PENDING'),
                'improper_space_integrals':('improper-space-integral/v1','IMPROPER_SPACE_PENDING'),
                'source_global_extrema':('source-global-extrema/v1','SOURCE_EXTREMA_PENDING'),
                'finite_interval_integral':('finite-interval-primitive/v1','DEFINITE_INTEGRAL_PENDING'),
                'continuous_riemann_limit':('continuous-riemann-limit/v1','RIEMANN_LIMIT_PENDING'),
                'find_leading_term_and_order':('relative-leading-term/v1','ASYMPTOTIC_ORDER_PENDING'),
                'higher_derivative':('ordinary-differentiation/v1','HIGHER_DERIVATIVE_PENDING'),
                'sided_derivatives':('sided-derivative-cells/v1','SIDED_DERIVATIVE_PENDING'),
                'derivative_signs':('derivative-sign-chart/v1','DERIVATIVE_SIGN_PENDING'),
                'printed_inequality':('printed-inequality/v1','INEQUALITY_PROOF_PENDING'),
                'curve_contacts':('curve-contact-geometry/v1','CURVE_CONTACT_PENDING'),
                'symbolic_order':('symbolic-order-coefficients/v1','SYMBOLIC_ORDER_PENDING'),
                'infinite_power_series_expansion':('analytic-power-series/v1','POWER_SERIES_PENDING'),
                'successive_composition':('successive-composition/v1','COMPOSITE_DERIVATIVE_PENDING'),
                'sequence_liminf_limsup':('sequence-tail-bounds/v1','SEQUENCE_ENVELOPES_PENDING'),
                'discrete_global_extremum':('sequence-extremum/v1','SEQUENCE_EXTREMUM_PENDING'),
                'real_root_count_isolation':('isolated-real-roots/v1','ROOT_ISOLATION_PENDING'),
                'sequence_range_and_envelopes':('sequence-range-and-tail/v1','SEQUENCE_RANGE_PENDING'),
                'partial_sum_convergence':('partial-sum-convergence/v1','CAUCHY_TAIL_PENDING'),
                'finite_sum_context':('finite-sum-context/v1','SUM_CONTEXT_PENDING'),
                'sequence_term_at':('sequence-term-at/v1','SEQUENCE_TERM_PENDING'),
                'sequence_expression_nonzero':('sequence-expression-nonzero/v1','INTEGER_DOMAIN_PENDING'),
                'sequence_expression_limit':('sequence-expression-limit/v1','SEQUENCE_LIMIT_PENDING'),
                'finite_product_identity':('finite-product-identity/v1','PRODUCT_IDENTITY_PENDING'),
                'finite_product_limit':('finite-product-limit/v1','PRODUCT_LIMIT_PENDING'),
                'contracting_integer_power_limit':('contracting-integer-power-limit/v1','POWER_LIMIT_PENDING'),
                'contracting_expression_nonzero':('contracting-expression-nonzero/v1','INTEGER_DOMAIN_PENDING'),
                'contracting_power_expression_limit':('contracting-power-expression-limit/v1','POWER_COMPOSITION_PENDING'),
                'infinite_rational_product':('infinite-rational-product/v1','PRODUCT_PENDING'),
                'finite_sum_formula':('finite-sum-formula/v1','SUM_FORMULA_PENDING'),
                'finite_sum_bound':('finite-sum-bound/v1','SUM_BOUND_PENDING'),
                'finite_sum_or_product_sequence_limit':('finite-sum-limit/v1','FINITE_SUM_LIMIT_PENDING'),
                'level_sets':('level-set-family/v1','LEVEL_FAMILY_PENDING'),
                'function_increment':('function-increment/v1','INCREMENT_PENDING'),
                'linear_approximation':('linear-approximation/v1','LINEAR_APPROXIMATION_PENDING'),
                'root_linearization':('root-linearization/v1','ROOT_LINEARIZATION_PENDING'),
                'uniform_continuity':('uniform-continuity/v1','CONTINUITY_MODULUS_PENDING'),
                'quantifier_continuity':('neighborhood-quantifiers/v1','CONTINUITY_QUANTIFIERS_PENDING'),
                'solve_functional_equation':('functional-characterization/v1','FUNCTIONAL_EQUATION_PENDING'),
                'complex_power_series_disk':('complex-series-disk/v1','COMPLEX_DISK_PENDING'),
                'fourier_expansion':('fourier-expansion/v1','FOURIER_EXPANSION_PENDING'),
                'epsilon_delta_proof':('pointwise-modulus/v1','LOCAL_MODULUS_PENDING'),
                'multivariate_taylor':('multivariate-taylor/v1','TAYLOR_PENDING'),
                'implicit_derivative':('implicit-derivative/v1','IMPLICIT_DERIVATIVE_PENDING'),
                'composite_function_differentiation':('formal-composition/v1','COMPOSITE_DERIVATIVE_PENDING'),
                'sampled_field_taylor':('sampled-field-taylor/v1','TAYLOR_PENDING'),
                'local_geometry':('local-geometry/v1','LOCAL_GEOMETRY_PENDING'),
                'multivariate_operator_proof':('multivariate-operator-proof/v1','MULTIVARIATE_PROOF_PENDING'),
                'series_sum':('telescoping-series/v1','SERIES_SUM_PENDING'),
                'integrate_by_series':('termwise-integral/v1','SERIES_INTEGRAL_PENDING'),
                'power_series_quadrature':('power-series-quadrature/v1','SERIES_INTEGRAL_PENDING'),
                'series_numeric_approximation':('series-numeric-bounds/v1','SERIES_PRECISION_PENDING'),
                'parametric_curve_derivatives':('parametric-curve-derivatives/v1','PARAMETRIC_DERIVATIVES_PENDING'),
                'implicit_graph_derivatives_and_values':('implicit-graph-values/v1','IMPLICIT_GRAPH_VALUES_PENDING'),
                'inverse_definition_derivative':('inverse-definition-derivative/v1','DEFINITION_DERIVATIVE_PENDING'),
                'elementary_taylor_limit':('source-asymptotic-proof/v1','TAYLOR_LIMIT_PENDING'),
                'differentiate_floor_expression':('integer-step-derivative/v1','INTEGER_STEP_DERIVATIVE_PENDING'),
                'uniform_sequence_convergence':('uniform-sequence/v1','UNIFORM_CONVERGENCE_PENDING'),
                'uniform_series_convergence':('uniform-series-majorant/v1','UNIFORM_SERIES_PENDING'),
                'source_uniform_functional':('source-uniform-functional/v1','UNIFORM_FUNCTIONAL_PENDING'),
                'exact_form':('exact-form/v1','EXACT_FORM_PENDING'),
                'oriented_boundary_integral':('oriented-boundary/v1','BOUNDARY_INTEGRAL_PENDING'),
                'integral_reduction_family':('indexed-moment/v1','MOMENT_REDUCTION_PENDING'),
                'indefinite_integral_recurrence':('primitive-recurrence/v1','PRIMITIVE_RECURRENCE_PENDING'),
                'functional_primitive':('functional-primitive/v1','FUNCTIONAL_PRIMITIVE_PENDING'),
                'defined_riemann_integral':('defined-riemann-integral/v1','RIEMANN_DEFINITION_PENDING'),
                'source_definite_trace':('source-definite-trace/v1','DEFINITE_TRACE_PENDING'),
                'source_endpoint_limit':('source-endpoint-limit/v1','ENDPOINT_LIMIT_PENDING'),
                'interval_integral_proof':('interval-integral-proof/v1','INTERVAL_INTEGRAL_PROOF_PENDING'),
                'improper_integral':('improper-integral/v1','IMPROPER_INTEGRAL_PENDING'),
                'line_integral':('line-integral/v1','LINE_INTEGRAL_PENDING'),
                'spatial_reduction':('spatial-reduction/v1','SPATIAL_INTEGRAL_PENDING'),
                'cartesian_flux':('cartesian-flux/v1','FLUX_PENDING'),
                'solid_sections':('solid-sections/v1','SOLID_SECTIONS_PENDING'),
                'curve_metric':('curve-metric/v1','CURVE_METRIC_PENDING'),
                'curve_curvature_radius':('plane-curve-radius/v1','CURVATURE_PENDING'),
                'surface_area':('surface-metric-patch/v1','SURFACE_AREA_PENDING'),
                'bound_curve_integral':('bound-curve-integral/v1','CURVE_ENDPOINTS_PENDING'),
                'greens_boundary_integral':('source-green-integral/v1','BOUNDARY_SOURCE_PENDING'),
                'bounded_section_measure':('bounded-section-measure/v1','SECTION_MEASURE_PENDING'),
                'geometric_moments':('geometric-moments/v1','GEOMETRIC_MOMENTS_PENDING'),
                'planar_domain':('planar-domain/v1','PLANAR_DOMAIN_PENDING'),
                'function_sign_sets':('function-sign-sets/v1','SIGN_SETS_PENDING'),
                'plane_measure':('plane-measure/v1','PLANE_MEASURE_PENDING'),
                'rectangular_grid_sums':('rectangular-grid-sums/v1','RECTANGULAR_SUM_PENDING'),
                'area_from_line_integral':('area-from-line-integral/v1','BOUNDARY_AREA_PENDING'),
                'linear_primitive':('linear-primitive/v1','INTEGRAL_PENDING'),
                'rational_primitive_algebraic_part':('rational-primitive-part/v1','INTEGRAL_PENDING'),
                'rational_primitive_criterion':('rational-primitive-criterion/v1','INTEGRAL_PENDING'),
                'quadratic_radical_primitive_proof':('quadratic-radical-primitive-proof/v1','INTEGRAL_PENDING'),
                'partial_fraction_symmetry':('partial-fraction-symmetry/v1','INTEGRAL_PENDING'),
                'restricted_function_image':('function-image/v1','IMAGE_PENDING'),
                'function_bounds':('function-bounds/v1','BOUNDS_PENDING'),
                'real_function_domain_and_range':('function-image/v1','IMAGE_PENDING'),
                'real_function_domain':('natural-real-domain/v1','DOMAIN_PENDING'),
                'classify_extrema':('strict-extrema-run/v1','EXTREMA_PENDING'),
                'definite_quadrature':('definite-quadrature/v1','QUADRATURE_PENDING'),
                'euler_integral_evaluation':('euler-integral/v1','EULER_INTEGRAL_PENDING'),
                'cartesian_slices':('cartesian-slices/v1','REGION_PENDING'),
                'reverse_iterated_integral':('cartesian-slices/v1','REGION_PENDING'),
                'variable_endpoint_integral_derivative':('integral-endpoint-derivative/v1','INTEGRAL_DERIVATIVE_PENDING'),
                'definite_integral_sign':('finite-integral-order/v1','INTEGRAL_ORDER_PENDING'),
                'compare_definite_integrals':('finite-integral-order/v1','INTEGRAL_ORDER_PENDING'),
                'mean_function_value':('finite-integral-mean/v1','INTEGRAL_MEAN_PENDING'),
                'weighted_mean_integral_estimate':('weighted-integral-mean/v1','WEIGHTED_MEAN_PENDING'),
                'ellipsoid_moment':('ellipsoid-moment/v1','ELLIPSOID_MOMENT_PENDING'),
                'iterated_integral':('iterated-integral/v1','ITERATED_INTEGRAL_PENDING'),
                'integral_substitution_validity':('substitution-validity/v1','SUBSTITUTION_VALIDITY_PENDING'),
                'continuous_extension':('continuous-extension/v1','EXTENSION_PENDING'),
                'discontinuity_classification':('continuity-classification/v1','CONTINUITY_PENDING'),
                'piecewise_continuity':('continuity-classification/v1','CONTINUITY_PENDING'),
                'pointwise_limit_continuity':('pointwise-limit-continuity/v1','CONTINUITY_PENDING'),
                'differential_operator':('differential-operator/v1','OPERATOR_PENDING'),
                'exact_differential_endpoints':('exact-form/v1','EXACT_FORM_PENDING'),
                'first_and_second_total_differentials':('total-differentials/v1','TOTAL_DIFFERENTIAL_PENDING'),
                'differential_coordinate_change':('differential-coordinate-change/v1','COORDINATE_CHANGE_PENDING'),
                'implicit_differential_identity':('implicit-differential-identity/v1','DIFFERENTIAL_INVARIANT_PENDING'),
                'implicitly_coupled_system':('implicit-system-differentiation/v1','IMPLICIT_SYSTEM_PENDING'),
                'formal_differential_identity':('abstract-field-equation/v1','FIELD_EQUATION_PENDING'),
                'eliminate_arbitrary_functions':('abstract-field-equation/v1','FIELD_EQUATION_PENDING'),
                'multivariable_limit':('joint-limit/v1','JOINT_LIMIT_PENDING'),
                'multivariate_continuity':('joint-limit/v1','JOINT_CONTINUITY_PENDING'),
                'discontinuity_set':('continuity-locus/v1','CONTINUITY_LOCUS_PENDING'),
                'compare_ordered_partials':('ordered-partial-equality/v1','PARTIAL_EQUALITY_PENDING'),
                'multivariate_extrema':('multivariate-extrema/v1','EXTREMA_PENDING'),
                'constrained_extrema':('multivariate-extrema/v1','EXTREMA_PENDING'),
                'potential_from_differential':('exact-form/v1','EXACT_FORM_PENDING'),
                'scalar_field_geometry':('scalar-field-geometry/v1','FIELD_GEOMETRY_PENDING'),
                'tangent_geometry':('tangent-geometry/v1','TANGENT_GEOMETRY_PENDING')}


COMPOSED_SCHEMAS=frozenset(schema for schema,_ in COMPOSED_GOALS.values())


def function_increment(task,library,request):
    """Derive finite changes from two source values, and local rates from a point derivative."""
    fields={'kind','id','source','function','variable','at','to','increment','increment_symbol','parameters',
            'stated_conditions','source_step_description','requested_output'}
    if set(task)-fields or library.data.get('task_compilers',{}).get('function_increment')!='finite_change_and_local_rate':
        raise Unsupported('Unknown finite-change requirement or method')
    v=task['variable'];pars=task.get('parameters',[]);conds=task.get('stated_conditions',[])
    want=task['requested_output'];names=list(pars)
    if not isinstance(want,(list,tuple)) or not want or len(set(want))!=len(want):
        raise Unsupported('Distinct requested quantities are required')
    m.context(dict(variable=v,parameters=pars))
    if task['at']==v:names.append(v)
    if 'increment_symbol' in task:names.append(task['increment_symbol'])
    dummy='__change'
    while dummy in [v,*names]:dummy+='_'
    raw=m.parse(task['function'],v,pars);begin=m.parse(str(task['at']),None,names)
    fixed=[g for g in domain_conditions(raw) if g[0] in ('nonzero','positive') and g[1][0]=='s' and g[1][1] in pars]
    conditions=list(conds)+[guard_source(g) for g in fixed]
    ctx=m.context(dict(variable=dummy,parameters=names,parameter_conditions=conditions))
    if not m.constant_defined(begin,ctx):raise Unsupported('The original starting argument is undefined')
    value_at=lambda point:m.substitute(raw,{('v',v):point})
    at=value_at(begin)
    if not m.constant_defined(at,ctx):raise Unsupported('A source value is undefined at the starting point')
    instant={'tangent_slope','instantaneous_velocity','instantaneous_stretch_factor'}
    if set(want)<=instant:
        if {'to','increment','increment_symbol','source_step_description'}&set(task) or v in names:
            raise Unsupported('A point derivative requires a fixed evaluation point and no finite displacement')
        sub=dict(kind='derivative_at',function=task['function'],variable=v,point=source(begin),parameters=pars,stated_conditions=conditions)
        derivative=freeze(request('instantaneous rate from the point derivative',sub)['value'])
        return {'point':begin,'source_value':m.simplify(at),'derivative':derivative,'natural_parameter_guards':fixed},{key:m.simplify(('abs',derivative)) if key=='instantaneous_stretch_factor' else derivative for key in want}
    rates={'secant_slope','mean_velocity','mean_stretch_factor'}
    local={'differential','comparison','linearized_value'} if library.data.get('finite_linearization') else set()
    if (('increment' in task)==('to' in task) or set(want)-rates-local-{'argument_increment','function_increment','numerical_value'}
            or 'numerical_value' in want and len(set(want)&rates)!=1):
        raise Unsupported('Specify one displacement or destination and the requested finite quantities')
    supplied=m.parse(str(task.get('increment',task.get('to'))),None,names)
    if not m.constant_defined(supplied,ctx):raise Unsupported('The original displacement or destination is undefined')
    end=m.add(begin,supplied) if 'increment' in task else supplied
    step=m.add(end,m.neg(begin));after=value_at(end)
    if not m.constant_defined(after,ctx):raise Unsupported('A source value is undefined at the destination')
    change=m.add(after,m.neg(at));plan={'start':begin,'end':end,'value_before':m.simplify(at),'value_after':m.simplify(after),'natural_parameter_guards':fixed}
    quantities={'argument_increment':step,'function_increment':change}
    if set(want)&local:
        from quadrature import enclose
        job=dict(kind='derivative_at',variable=v,function=task['function'],point=source(begin),parameters=pars,stated_conditions=conditions)
        slope=freeze(request('derivative for the first-order change',job)['value'])
        linear=m.simplify(m.mul(slope,step));plan['point_derivative']=slope
        quantities.update(differential=linear,linearized_value=m.simplify(m.add(at,linear)))
        if 'comparison' in want:
            remainder=m.simplify(m.add(change,m.neg(linear)));sgn=m.sign(remainder,ctx)
            if sgn not in (-1,0,1):
                lo,hi=enclose(remainder,None)
                sgn=1 if lo>0 else -1 if hi<0 else 0 if lo==hi==0 else None
            if sgn is None:raise Unsupported('The ordering of the two increments is not certified')
            quantities['comparison']={'relation':{-1:'<',0:'=',1:'>'}[sgn],'exact_minus_differential':remainder}
    if set(want)&rates:
        if not m.nonzero(step,ctx):raise Unsupported('The displacement must be nonzero')
        if 'mean_velocity' in want or 'mean_stretch_factor' in want:
            from quadrature import enclose,guard_bounds
            def on_segment(relation,expression):
                left,right=enclose(begin,None),enclose(end,None)
                return guard_bounds(relation,expression,(min(left[0],right[0]),max(left[1],right[1])),[v])
            if 'mean_velocity' in want and m.sign(step,ctx)!=1:raise Unsupported('Elapsed time must be positive')
            for g in domain_conditions(raw,'mean_stretch_factor' in want):
                if not known_guard(g,ctx):on_segment(*g)
        rate=m.div(change,step)
        if 'mean_stretch_factor' in want:
            sub=dict(kind='differentiate',function=task['function'],variable=v,parameters=pars,stated_conditions=[guard_source(g) for g in fixed],method_requirement='table_and_rules')
            slope=freeze(request('monotonicity on the segment',sub)['value'])
            if not (m.known_nonnegative(slope,ctx) or m.known_nonnegative(m.neg(slope),ctx)):
                try:on_segment('nonnegative',slope)
                except Unsupported:on_segment('nonnegative',m.neg(slope))
            plan['monotone_derivative']=slope
        quantities.update(secant_slope=rate,mean_velocity=rate,mean_stretch_factor=m.simplify(('abs',rate)))
        if 'numerical_value' in want:
            number=quantities[next(iter(set(want)&rates))]
            if m.num(number) is None:raise Unsupported('An explicit numerical value is still required')
            quantities['numerical_value']=number
    return plan,{key:quantities[key] for key in want}


def composed_kind(task):
    if task.get('kind') in ('series_theorem','series_proposition') and ('series_statement' in task or
            task.get('kind')=='series_theorem' and 'обратных членам арифметической прогрессии' in str(task.get('statement',''))):
        return 'abstract_series_theorem'
    if task.get('kind')=='series_convergence' and task.get('method_requirement')=='cauchy_tail_criterion':
        return 'explicit_cauchy_series'
    if task.get('kind') in ('series_tail_length','series_tail_accuracy'):
        return 'certified_series_prefix'
    if task.get('kind') in ('power_series_convergence_set','generalized_series_convergence_set'):return 'power_series_boundary'
    if (task.get('kind')=='functional_series_convergence_set' and isinstance(task.get('variables'),list)
            and len(task['variables'])==1 and 'term' in task):return 'power_series_boundary'
    kind=task.get('kind',task.get('task_type'))
    if kind in ('algebraic_primitive_parameter_condition','verify_parameterized_primitive'):
        return 'quadratic_radical_primitive_proof'
    if kind=='differentiate' and inverse_definition_profile(task) is not None:return 'inverse_definition_derivative'
    if kind=='limit' and task.get('method_requirement')=='use_elementary_taylor_expansions_I_V':return 'elementary_taylor_limit'
    from elementary_proofs import routing as elementary_routing
    if elementary_routing(task,kind):return 'elementary_proof'
    if (kind in ('laplace_transform','weierstrass_transform','unitary_fourier_transform','inverse_fourier_half_line')
            or kind=='parameter_improper_evaluation' and task.get('method_requirement')=='specified_double_representation'):
        return 'source_integral_transform'
    if kind in ('bessel_equation_identity','prove_integral_identity','uniform_integral_identity','parameter_integral_identity',
                'integral_pde_identity','level_curve_integration_proof','vanishing_integral_function_proof','differentiate_moving_integral',
                'differentiate_shifted_integral','integral_parameter_series','integral_asymptotic_equivalence','integral_monotonicity'):
        from quadrature import integral_identity_profiles
        if integral_identity_profiles(task):return 'source_parameter_integral'
    if kind=='surface_geometry' and 'angle between normals' in str(task.get('source_formula','')):
        return 'source_geometric_domains'
    if (kind=='stokes_circulation' and 'described as an ellipse' in str(task.get('curve',''))
            or kind=='formal_vector_identity' and 'given' in task and 'claim' in task):
        return 'source_vector_calculus'
    if (kind=='prove_second_order_euler_identity' or kind=='formal_differential_identity' and
            ('homogeneous degree' in str(task.get('given','')) or task.get('source',{}).get('printed_partial') in ('The first partial denominator visibly reads dz, not dx.','The first partial denominator reads dx.'))):
        return 'multivariate_operator_proof'
    if ((kind=='finite_sum_or_product_sequence_limit' and 'first_root_indices' in task.get('goal',{}))
            or kind=='characterize_convergence_by_envelope_algebra'):
        return 'source_series_algebra'
    if kind=='multivariate_continuity':
        title=task.get('source',{}).get('literal_requirement','')
        if 'и нарушение совместной непрерывности' in title:
            from geometric_domains import homogeneous_radial_claim
            try:homogeneous_radial_claim(task)
            except (Unsupported,TypeError,ValueError,AttributeError,KeyError,ZeroDivisionError):pass
            else:return 'source_geometric_domains'
        if title.startswith('Доказать непрерывность') and 'F(u,v)' in title and 'valued in' in str(task.get('given','')):
            return 'source_geometric_domains'
    from surface_fields import surface_field_goal
    if surface_field_goal(task):return 'source_surface_field'
    from graphs import graphical_goal_kind
    if graphical_goal_kind(task):return 'source_geometric_domains'
    from geometric_domains import selected_residual_geometry
    if selected_residual_geometry(task) is not None:return 'source_geometric_domains'
    from plane_domains import spatial_moment_admission
    if spatial_moment_admission(task):return 'source_spatial_moment'
    from geometric_domains import geometric_domain_goal
    if geometric_domain_goal(task):return 'source_geometric_domains'
    from quadrature import source_endpoint_limit_admission
    if source_endpoint_limit_admission(task):return 'source_endpoint_limit'
    if (kind in ('explain_fundamental_theorem_failure','definite_integral_of_composition') or
            kind=='definite_integral' and task.get('goal') in ('Evaluate the integral of the derivative.','Evaluate the definite integral.')):
        return 'source_definite_trace'
    from ordinary_series import routing as ordinary_series_routing
    if ordinary_series_routing(task,kind):return 'ordinary_series_proof'
    from planar_integrals import planar_composition_goal,geometric_application_goal
    if planar_composition_goal(task):return 'source_planar_composition'
    if geometric_application_goal(task):return 'source_geometric_application'
    if kind=='prove' and task.get('requested_output')==['proof','conditions_and_scope']:
        from integrals import affine_primitive_claim_goal
        if affine_primitive_claim_goal(task):return 'functional_primitive'
    if kind in ('primitive_formula_proof','rational_substitution_theorem','real_indexed_root_primitive','prove_integral_elementary','piecewise_integral','formal_function_primitive','recover_from_composite_derivative','inverse_function_primitive_theorem',
                'prove_integral_representation','characterize_elementary_integrability','elementarity_criterion_for_binomial_integral','integral_source_notation'):
        return 'functional_primitive'
    if kind in ('riemann_sum','darboux_sums','riemann_integral_by_definition','riemann_integrability_proposition'):
        return 'defined_riemann_integral'
    if (kind=='definite_integral' and task.get('requested_output')==['integral_value_and_derivation']
            and str(task.get('integrand','')).startswith('ln(') and len(task.get('parameters',[]))==1
            and any(str(s).startswith('abs(') for s in task.get('stated_conditions',[]))):
        return 'defined_riemann_integral'
    if kind in ('parameter_sequence_classification','sequence_integral_interchange','uniform_taylor_error',
                'uniform_series_tail_length','uniform_sequence_theorem'):
        return 'source_uniform_functional'
    from uniform import functional_transport_routing
    if functional_transport_routing(task,kind):return 'source_uniform_functional'
    functional=task.get('functional_statement')
    if isinstance(functional,dict) and (kind in ('functional_series_regularity','functional_series_example',
                                                 'functional_series_theorem','function_sequence_example','series_proposition') or
            kind=='series_operation_justification' and functional.get('question')=='termwise differentiation'):
        return 'source_uniform_functional'
    branches=task.get('branches')
    if (kind=='classify_differentiability_at_point' and isinstance(branches,list) and branches
            and isinstance(branches[0],dict) and re.fullmatch(r'\w+\^\w+\*sin\(1/\w+\)',str(branches[0].get('function')))):
        return 'derivative_proof'
    from limit_proofs import routing as asymptotic_routing
    if asymptotic_routing(task,kind):return 'source_asymptotic_proof'
    from real_functions import routing as real_function_routing
    if real_function_routing(task,kind):return 'real_function_proof'
    from derivative_proofs import routing as derivative_proof_routing
    if derivative_proof_routing(task,kind):return 'derivative_proof'
    from finite_sums import coefficient_transport_routing
    if coefficient_transport_routing(task,kind):return 'source_series_algebra'
    if (kind in ('rational_series_radius','formal_reciprocal_expansion','series_ode_identity','series_identity_proof','uniform_partial_sums',
                 'nth_derivative_from_series','simultaneous_infinite_power_series','variable_integral_power_series','sum_of_power_series_by_method',
                 'power_series_and_sum','general_power_series_operation','power_series_radius_theorem')
            or kind=='finite_expansion' and 'extended_value_at_center' in task
            or kind=='infinite_power_series_expansion' and ('required_powers' in task or 'conditions' in task or 'additional_series' in task
                or isinstance(task.get('source'),dict) and task['source'].get('literal_requirement')=='Применяя различные методы, найти разложение в степенной ряд.')):
        return 'source_series_algebra'
    from plane_geometry import KINDS as planar_kinds
    if kind in planar_kinds:return 'plane_geometry'
    if kind=='measurement_uncertainty':return kind
    if (kind in ('differential_of_independent_variable','ordinary_derivative_order')
            or kind=='partial_derivatives' and 'method_requirement' not in task
            and task.get('source',{}).get('requested_ordinary_orders')):
        return 'exact_ordinary_order'
    if kind=='prove_or_decide_integral_statement':return 'interval_integral_proof'
    if kind=='mean_value_application':return 'mean_function_value'
    if (kind in ('periodicity_of_integrals','proof_about_integrals','integral_identity_proof',
                 'integral_derivative_theorem','integral_derivative_example','integral_accumulation_function',
                 'integral_mean_limit_theorem','mean_on_infinite_interval','integral_mean_value_proof',
                 'integral_inequality_proof','integral_bound','limit_of_parameter_dependent_integral','limit_of_integral')
            or kind=='iterated_integral' and isinstance(task.get('integrand'),str)
            and re.search(r'\b(?:piecewise|sgn|sign|floor)\s*\(',task['integrand'])):
        return 'interval_integral_proof'
    path=task.get('path')
    from cartesian_fields import planar_field_goal
    if planar_field_goal(task):return 'source_vector_calculus'
    if (kind in ('surface_flux','surface_flux_and_divergence_check','orthogonal_coordinate_curl','orthogonal_coordinate_divergence',
                 'curl_norm_direction_at_point','curl_small_circle_circulation','rigid_rotation_curl','singular_radial_flux',
                 'radial_field_potential','radial_field_work','finite_mass_gravity_potential','angular_circulation',
                 'planar_flux_and_circulation','fluid_mass_balance','heat_conduction_balance','divergence_theorem_proof',
                 'newton_potential_gradient_identity','poisson_newtonian_potential')
            or kind=='formal_vector_identity' and {'field','expression','surface'}&task.keys()
            or kind=='oriented_boundary_integral' and isinstance(task.get('boundary_of'),dict) and 'cylinder' in task['boundary_of']
            or kind=='line_integral' and (isinstance(path,dict) and path.get('geometry')=='shortest great-circle arc'
                or isinstance(path,list) and any(isinstance(seg,dict) and 'direction' in seg for seg in path))
            or kind=='exact_form' and isinstance(task.get('source'),dict) and task['source'].get('literal_requirement') in (
                'Убедиться в потенциальности и найти работу вдоль пути от M к N в положительном октанте.',
                'Найти потенциал гравитационного поля точечной массы в начале координат.')):
        return 'source_vector_calculus'
    from scalar_proofs import routing as scalar_proof_routing
    if scalar_proof_routing(kind,task.get('goal')):return 'scalar_source_proof'
    from cartesian_fields import multivariate_proof_routing
    if multivariate_proof_routing(task,kind):return 'multivariate_operator_proof'
    if kind in ('implicit_differentials','implicit_symbolic_derivative','derivative_on_implicit_graph',
                'partial_differential_equation','symbolic_order_partial_derivative','total_differential_symbolic_order',
                'total_differential_and_partials','count_implicit_branches','implicit_inverse_existence',
                'implicit_inverse_theorem','continuous_implicit_uniqueness','implicit_function_identity',
                'arbitrary_composite_partial_identity','operator_product_identity'):
        return 'multivariate_operator_proof'
    if kind=='composite_function_differentiation' and task.get('requested_output') in (['dn'],['radial_laplacian']):
        return 'multivariate_operator_proof'
    if (kind=='composite_function_differentiation' and task.get('requested_output')==['d1_d2']
            and isinstance(task.get('variables'),list) and all(isinstance(x,str) for x in task['variables'])
            and task.get('inner_arguments')==['sqrt('+'+'.join(x+'^2' for x in task['variables'])+')']):
        return 'multivariate_operator_proof'
    if kind in ('multivariate_taylor_problem','multivariate_average_expansion','multivariate_infinite_series',
                'implicit_taylor_series','tangent_plane_limit','surface_geometry','plane_curve_singularity',
                'plane_curve_envelope','plane_curve_discriminant','surface_envelope','outward_normal_derivative','normal_derivative_identity',
                'loxodrome_constant_angle','surface_section_tangent_angle'):
        return 'local_geometry'
    if kind in ('proof','prove') and isinstance(task.get('goal'),dict):
        claim=task['goal'].get('proposition','')
        if isinstance(claim,str) and (claim.endswith(', by corresponding cuts') or ' in Q:' in claim or claim.startswith(('inf(','sup(','Every nonempty real set bounded')) or
                ('<' in claim or '>' in claim) and any(s in claim for s in ('factorial(','product(','sum(','abs(','^'))):
            return 'order_certificate'
    if kind in ('prove_and_apply_root_linearization','root_increment_law','remainder_inequality'):return 'root_linearization'
    if kind in ('approximate_function_value','sector_area_change'):return 'linear_approximation'
    if kind in ('riemann_sum_limit','darboux_sum_limit'):return 'rectangular_grid_sums'
    if kind in ('planar_exact_integral','planar_integral_mean','planar_area','polar_change_bounds','polar_integral_reduction','planar_integral_reduction'):
        return 'plane_measure'
    from planar_integrals import curve_chart_goal
    if curve_chart_goal(task):return 'source_vector_calculus'
    if kind=='space_curve_length' or kind=='line_integral' and isinstance(task.get('path'),dict) and 'map' in task['path']:
        return 'bound_curve_integral'
    if (kind=='line_integral_from_geometric_locus' and 'coefficients' in task and 'orientation' in task
            and isinstance(task.get('curve'),str) and task['curve'].count('=')==1):
        return 'greens_boundary_integral'
    if kind=='continuous_least_squares':return 'continuous_least_squares'
    if kind in ('improper_multiple_integral','improper_multidimensional_convergence','improper_convergence_proof','improper_exhaustion_proof'):
        return 'improper_space_integrals'
    if kind in ('parameter_integral_source_goal','parameter_integral_continuity','parameter_integral_derivative',
                'parameter_integral_identity','integral_parameter_series','integral_series_identity','iterated_integral'):
        from quadrature import compact_parameter_integral_goal
        if compact_parameter_integral_goal(task):return 'source_parameter_integral'
    if kind in ('integral_reduction_family','indefinite_integral_recurrence',
                'polynomial_weighted_primitive_identity','polynomial_family_primitive'):
        from quadrature import boundary_reduction_candidate
        if boundary_reduction_candidate(task):return 'source_parameter_integral'
    if kind=='euler_integral_identity' and isinstance(task.get('claim'),str) and (
            task['claim'].startswith('prod_') or 'Gamma(' in task['claim']):
        return 'source_parameter_integral'
    if kind in ('euler_integral_evaluation','euler_integral_identity','parameter_improper_evaluation'):
        from quadrature import euler_endpoint_candidate
        if euler_endpoint_candidate(task):return 'source_parameter_integral'
    if kind=='elliptic_integral_derivatives' or kind=='parameter_integral_identity' and ('formula' in task or 'claim' in task):
        return 'source_parameter_integral'
    if kind=='hermite_orthogonality' or kind=='mathematical_question' and task.get('requested_output')==['piecewise_function'] and isinstance(task.get('function'),str):
        return 'source_parameter_integral'
    if kind in ('fresnel_integrals','principal_value_integral'):return 'source_parameter_integral'
    if (kind in ('limit_improper_integral','parameter_integral_continuity','parameter_integral_derivative','uniform_parameter_integral','uniform_convergence_neighborhood',
                 'uniform_tail_bound','uniform_convergence_quantifiers','uniform_no_integrable_majorant','limit_integral_interchange',
                 'improper_identity','improper_integral_convergence_parameters','evaluate_via_parameter','parameter_definite_integral',
                 'special_function_integral_identity','smoothness_parameter_integral','differentiate_dirichlet_integral','frullani_identity')
            or kind=='mathematical_question' and task.get('requested_output')==['discontinuities']
               and task.get('limits')=='0..inf' and 'integrand' in task
            or kind=='parameter_improper_evaluation' and (task.get('method_requirement') in
               ('use_given_integral','differentiate_under_integral','specified_representation','derive_from_abel_regularization')
               or task.get('method_requirement') is None and task.get('limits') in ('0..1','1..inf'))):
        return 'source_parameter_integral'
    if kind in ('multivariate_bounds','multivariate_extrema_proof','optimization_application'):
        return 'source_global_extrema'
    if (kind=='constrained_extrema' and task.get('source_formula')=='sum_(i,j=1)^n a_ij*x_i*x_j'
            or kind=='prove_inequality' and 'source_formula' in task and task.get('requested_output')==['proof']):
        return 'source_global_extrema'
    if kind=='mathematical_question' and task.get('method_requirement')=='newton_leibniz' and 'integrand' in task:return 'finite_interval_integral'
    if kind=='sequence_expression_limit' and task.get('method_requirement')=='definite_integral':return 'continuous_riemann_limit'
    if (kind=='sequence_expression_limit' and 'index' in task and task.get('method_requirement') in (None,'any')
            and isinstance(task.get('expression'),str) and re.search(r'\bsum\s*\(',task['expression'])):
        return 'finite_sum_or_product_sequence_limit'

    if kind in ('one_sided_derivative_investigation','one_sided_derivative_functions','global_one_sided_derivatives',
                'generalized_one_sided_derivatives','investigate_differentiability','continuity_and_no_one_sided_derivative'):return 'sided_derivatives'
    if (kind=='differentiate' and task.get('requested_output')==['finite_derivative','natural_domain_and_boundary_notes']
            and ('branches' in task or 'abs(' in str(task.get('function','')))):return 'sided_derivatives'
    if kind in ('strict_monotonicity_intervals','concavity_and_inflection'):return 'derivative_signs'
    if (kind=='prove_inequality' and 'given' in task or kind=='proof_about_real_functions'
            and isinstance(task.get('statement'),str) and task['statement'].startswith('Доказать ')
            and any(word in task['statement'] for word in (' при ',' для ')) and any(op in task['statement'] for op in ('<','>','≤','≥'))):return 'printed_inequality'
    if kind in ('plane_tangent_and_normal','contact_order','cycloid_tangent_construction','parametric_tangent_construction','tangent_parallelism',
                'parametric_tangent_parallel_plane','constant_tangent_angle_proof'):return 'curve_contacts'
    if kind in ('symbolic_order_derivative','symbolic_order_differential','symbolic_order_point_derivative'):return 'symbolic_order'
    if kind=='composite_function_differentiation' and ('outer_expression' in task or 'outer_differentiability_order' in task):
        return 'successive_composition'
    if kind=='successive_differentials_with_dependent_coordinate':return 'successive_composition'
    if kind=='partial_derivatives' and isinstance(task.get('source'),dict):
        printed=task['source']
        if 'printed_operator_goals' in printed:return 'multivariate_operator_proof'
        if 'required_equality' in printed:return 'compare_ordered_partials'
        if (printed.get('requested_operator')=='differential' or
                str(printed.get('printed_goal','')).startswith('Treat ') and 'find d^' in str(printed.get('printed_goal',''))):
            return 'higher_derivative'
        if (str(printed.get('printed_goal','')).startswith('Prove ')
                or re.search(r'\bY\d*\b',str(printed.get('requested_operator','')))):
            return 'differential_operator'
    if kind in ('cauchy_sequence_convergence','sequence_convergence'):return 'partial_sum_convergence'
    goal=task.get('goal')
    expression=goal.get('expression') if kind=='finite_sum_or_product_sequence_limit' and isinstance(goal,dict) else task.get('expression')
    if (kind in ('finite_sum_or_product_sequence_limit','limit',None) and isinstance(expression,str)
            and re.match(r'\s*product_\{',expression)):
        return 'finite_product_limit'
    if kind in ('prove','proof') and isinstance(goal,dict) and isinstance(goal.get('proposition'),str):
        sides=goal['proposition'].split('=')
        if len(sides)==2 and re.search(r'\bsum\s*\(',sides[1]):return 'finite_sum_context'
    if kind in ('infinite_product_value','infinite_product_identity','infinite_product_convergence'):return 'infinite_rational_product'
    if kind=='finite_sum_sequence_limit':return 'finite_sum_context'
    if kind=='compute_sequence_limit':return 'compute_limit'
    if (kind in (None,'limit') and task.get('variable_domain')=='positive_integers'
            and isinstance(task.get('expression'),str) and re.search(r'\bsum\s*\(',task['expression'])):
        if task.get('parameters') or len(re.findall(r'\bsum\s*\(',task['expression']))>1:return 'finite_sum_context'
        return 'finite_sum_or_product_sequence_limit'
    if kind in ('function_infimum_supremum','function_oscillation'):return 'function_bounds'
    if kind in ('solid_mass','spatial_exact_integral'):return 'spatial_reduction'
    if kind in ('oriented_surface_flux','divergence_integral_transform'):return 'cartesian_flux'
    if kind in ('volume_from_named_solid','section_measure_identity','dense_section_measure','volume_bounded_by_surfaces','bounded_solid_volume','lamina_centroid'):return 'solid_sections'
    if kind=='curve_arc_length' or kind=='solid_of_revolution' and task.get('requested_output')==['surface_area']:return 'curve_metric'
    if kind in ('area_bounded_by_curves','solid_of_revolution'):return 'bounded_section_measure'
    if kind=='integrate':return 'linear_primitive'
    if kind=='real_function_domain' and isinstance(task.get('goal'),dict) and 'variables' in task['goal']:return 'planar_domain'
    if kind=='restricted_real_function_domain':return 'real_function_domain'
    return kind


def integral_charts(task,library):
    if composed_kind(task)=='uniform_continuity':
        options=tuple(library.data.get('uniform_continuity_transitions',()))
        if 'endpoint_obstruction' in options and library.data.get('source_scalar_proofs'):
            i=options.index('endpoint_obstruction')+1
            return (*options[:i],'right_endpoint_obstruction',*options[i:])
        return options
    if composed_kind(task)=='plane_measure':
        return tuple(s['chart'] for s in library.data.get('plane_measure_reductions',())
                     if task.get('kind') in s['goals'] and task.get('method_requirement') in s['methods'])
    if (composed_kind(task)=='greens_boundary_integral' and task.get('method_requirement') is None
            and library.data.get('green_coordinate_boundary')):return ('direct_circle',)
    if task.get('kind')=='integrate':
        from integrals import rational_primitive_charts,elementary_chart_options
        from radical_primitives import radical_chart_options
        prior=rational_primitive_charts(task) if library.data.get('rational_primitive_coordinates') else ()
        algebraic=radical_chart_options(task) if library.data.get('real_radical_coordinates') else ()
        elementary=elementary_chart_options(task) if library.data.get('elementary_primitive_transitions') else ()
        if library.data.get('source_primitive_charts'):
            from source_primitives import chart_options
            elementary+=tuple(c for c in chart_options(task) if c in library.data['source_primitive_charts'])
        if library.data.get('primitive_foundation_transitions'):
            from integrals import foundation_options
            return prior+algebraic+elementary+foundation_options(task)
        return prior+algebraic+elementary
    if composed_kind(task)=='restricted_function_image' and library.data.get('images_of_monotonicity_cells'):
        return ('images_of_monotonicity_cells',)
    if task.get('kind') in ('potential_from_differential','exact_differential_endpoints') and library.data.get('exact_form_potential'):
        return ('coordinate_axes',)+ (('source_form_charts',) if library.data.get('source_form_charts') else ())
    bounds=task.get('integration_order') or task.get('rectangle')
    indexed=(('indexed_euler_expansion',) if task.get('kind')=='iterated_integral'
             and library.data.get('indexed_euler_integrals') and any(
                 isinstance(c,str) and c.endswith(' is a positive integer') for c in task.get('stated_conditions',[])) else ())
    if (task.get('kind')=='iterated_integral' and task.get('requested_output')==['exact_integral']
            and task.get('method_requirement','table_and_rules') in ('table_and_rules','appropriate_substitution')
            and isinstance(bounds,(list,tuple)) and len(bounds)==1):
        return indexed+tuple(name for name in ('semicircle_chart','rationalizing_substitution','endpoint_change_of_variable',
                                       'branched_rational_substitution')
                     if library.data.get(name))
    return indexed


def proposed_substitution_input(task):
    """Read the proposed relation and the original integral, without accepting partition hints."""
    common={'kind','id','source','requested_output'}
    if task.get('requested_output') not in (['assess_substitution'],['explain_formal_substitution_error']):
        raise Unsupported('A verdict on the proposed change of variable is required')
    supers='⁰¹²³⁴⁵⁶⁷⁸⁹⁻⁺'
    digits=str.maketrans('₀₁₂₃₄₅₆₇₈₉₋₊'+supers,'0123456789-+'*2)
    def notation(text):
        text=text.replace('π','pi').replace('−','-').replace('·','*')
        def function(match):
            name,power,arg=match.groups()
            return name+'('+arg+')'+(power or '')
        functions='|'.join(sorted(m.FUNCTIONS|set(m.ALIASES)))
        text=re.sub(r'\b('+functions+r')(['+supers+r']+)?\s+([A-Za-z_]\w*)',function,text)
        return re.sub('['+supers+']+',lambda s:'^('+s[0].translate(digits)+')',text)
    if 'statement' in task:
        if set(task)-common!={'statement'}:raise Unsupported('Ambiguous source integral')
        match=re.fullmatch(r'\s*∫([₋₊₀-₉]+)(['+supers+r']+|\^[^\s,]+)\s+([^,]+),\s*([^,]+)\s*',task['statement'])
        if not match:raise Unsupported('Unrecognized integral and substitution notation')
        low,high,body,relation=match.groups();low=low.translate(digits);high=high.lstrip('^').translate(digits)
        differential=re.fullmatch(r'(.*?)\bd([A-Za-z_]\w*)\s*(/.*)?',body.strip())
        if not differential:raise Unsupported('Expected an explicit differential in the source integral')
        numerator,v,tail=differential.groups();density='('+ (numerator.strip() or '1')+')'+(tail or '')
        names=set(re.findall(r'[A-Za-z_]\w*',notation(relation)))-m.FUNCTIONS-set(m.ALIASES)-{v,'pi','e'}
        if len(names)!=1:raise Unsupported('Expected one new coordinate in the proposed equation')
        t=names.pop()
    else:
        fields=('variable','new_variable','lower','upper','integrand','substitution')
        if set(task)-common!=set(fields):raise Unsupported('Expected only the source integral and proposed relation')
        v,t,low,high,density,relation=(task[k] for k in fields)
    if not isinstance(t,str) or not isinstance(relation,str):raise Unsupported('Expected two named coordinates and a proposed equation')
    m.context(dict(variable=v,parameters=[t]))
    def real_powers(e):
        # In a real integral numerical thirds use the real cube root on both half-lines.
        if e[0]=='rpow' and m.constant_defined(e[2],{'parameters':[],'assumptions':[]}):
            p=m.num(m.simplify(e[2]))
            if p is not None and p.denominator==3 and abs(p.numerator)<=m.MAX_INTEGER_POWER:
                return ('cbrt',('pow',real_powers(e[1]),p.numerator))
        return tuple(real_powers(child) if isinstance(child,tuple) else child for child in e)
    def parse(text,variable=None,parameters=()):
        return real_powers(m.parse(notation(str(text)),variable,parameters))
    sides=relation.split('=')
    if len(sides)!=2:raise Unsupported('Expected a single proposed equality')
    lhs,rhs=(m.substitute(parse(side,v,[t]),{('s',t):('v',t)}) for side in sides)
    return v,t,parse(low),parse(high),parse(density,v),lhs,rhs


def check_transcribed_formula(notes,goal,printed):
    """Check editorial declarations against the parsed formula, before simplifying it."""
    from operations import expression_positions
    variable=goal['variable'];parameters=goal.get('parameters',[])
    parse=lambda text:m.parse(text,variable,parameters)
    raw=parse(goal['expression'])
    def prepend_factor(left,right):
        # A*B/C and A*(B/C) have the same raw divisors. Never move a factor across a sum.
        if right[0] in ('mul','div'):return (right[0],prepend_factor(left,right[1]),right[2])
        return ('mul',left,right)
    if not isinstance(notes,list) or not all(isinstance(n,str) for n in notes):
        raise Unsupported('Нужен список пояснений к записи формулы')
    for note in notes:
        definition=re.fullmatch(r'Printed (\w+)\((\w+)\)=(.+); exact definition expansion is used\.',note)
        if definition and definition[1] in printed.get('notation_definitions',{}) and definition[2]==variable:
            template=m.parse(printed['notation_definitions'][definition[1]],'z')
            body=m.substitute(template,{('v','z'):('v',variable)})
            if parse(definition[3])==body and m.contains(raw,body):continue
        powers=re.fullmatch(r'Both powers\s*(.+?) are printed; retain the outer brackets\.',note)
        if powers:
            exponent=parse(powers[1])
            if (raw[0]=='rpow' and raw[2]==exponent and
                    sum(e[0]=='rpow' and e[2]==exponent for _,e in expression_positions(raw[1]))==1):continue
        product=re.fullmatch(r'The multiplication by (.+?) attaches to the (square|cube)-root term only; '
                             r'it is inside the enclosing bracket after the subtraction\.',note)
        if product and raw[0]=='add' and raw[2][:2]==('mul',q(-1)):
            term=raw[2][2];root='sqrt' if product[2]=='square' else 'cbrt';factor=parse(product[1])
            if any(e[0]==root and term in (('mul',e,factor),prepend_factor(e,factor))
                   for _,e in expression_positions(term)):continue
        raise Unsupported('Пояснение к записи формулы не подтверждено исходным выражением')


def group_heading(instruction,task):
    """Resolve the shared printed heading and its explicit scope exceptions."""
    result=dict(instruction)
    for old,new in [('printed_group_instruction','printed_instruction'),('status','method_binding_status')]:
        if old not in result:continue
        if new in result:raise Unsupported('Два источника одного поля печатного заголовка')
        result[new]=result.pop(old)
    heading=result.get('printed_instruction')
    first=re.search(r' \(group begins on page\s*(\d+)\)\.$',heading) if isinstance(heading,str) else None
    if first:
        if any(type(p) is not int or p<int(first[1]) for p in task.get('source_pdf_pages',[])):
            raise Unsupported('Источник предшествует указанному началу группы')
        result['printed_instruction']=heading[:first.start()]
    if 'requirement_note' in result:
        scope=re.fullmatch(r'No (?:imperative|mandatory) [A-Za-z-]+ clause (?:occurs|appears) in the computational group\.'
                           r'(?:\s*(\d+) explicitly asks applicability and is excluded\.)?',result.pop('requirement_note'))
        if not scope:raise Unsupported('Пояснение о границах общего требования не разобрано')
        if scope[1]:
            number=task.get('source_exercise_number')
            if type(number) is not int or number==int(scope[1]):
                raise Unsupported('Принадлежность условия к группе с этим заголовком не установлена')
            if 'source_number' in task and not re.fullmatch(str(number)+r'(?:[a-zа-я]|[:.]\w+)?',str(task['source_number'])):
                raise Unsupported('Не совпадают обозначения упражнения в исходных данных')
    return result


def classify_continuity(task,library,request):
    """Partition the original domain of continuous elementary operations, then test its cuts."""
    from graphs import domain_partition
    from polynomial import NotRational,Undefined
    from verify import same_value,different_value
    kind=task['kind'];piecewise=kind=='piecewise_continuity'
    fields={'id','kind','source','variable','requested_output','branches' if piecewise else 'expression'}
    outputs=(['classify continuity'] if piecewise else ['all exceptional points on original real domain and its boundary',
                                                       'classification and one-sided behavior'])
    if (library.data.get('task_compilers',{}).get(kind)!='finite_domain_continuity' or set(task)-fields
            or task.get('requested_output')!=outputs):
        raise Unsupported('A different domain, output or method for the continuity question remains')
    provenance=task.get('source',{})
    if (not isinstance(provenance,dict) or set(provenance)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement','complete_obligation'}
            or provenance.get('literal_requirement') not in (None,'Исследовать на непрерывность и изобразить функцию графически.',
            'Исследовать на непрерывность и нарисовать эскиз графика.','Определить все точки разрыва функции и исследовать их характер.')
            or provenance.get('complete_obligation') not in (None,'The full rational graph certificate supplies the complete domain cuts, their types and adjacent signs at poles.')):
        raise Unsupported('Unparsed source obligation in the continuity question')
    var=task['variable'];ctx=m.context({'variable':var});override=None
    if piecewise:
        branches=task['branches']
        if set(branches)!={'except_point','point','point_value'}:raise Unsupported('A different piecewise domain needs a partition')
        text=branches['except_point'];original_point=m.parse(branches['point'],None)
        if not m.constant_defined(original_point,ctx):raise Unsupported('The original assigned point is not a real scalar')
        override=m.simplify(original_point)
        if override[0]!='q':raise Unsupported('Point assignment lacks a fixed rational coordinate')
        label=branches['point_value']
        if label=='arbitrary' or label!='e' and re.fullmatch(r'[A-Za-z]',label):
            assigned=('s','A' if label=='arbitrary' else label)
        else:
            assigned=m.parse(label,None)
            if not m.constant_defined(assigned,ctx):raise Unsupported('Undefined assigned value')
            assigned=m.simplify(assigned)
    else:text=task['expression']
    if not piecewise and library.data.get('step_level_continuity') and re.search(r'\b(?:floor|sign)\(',text):
        from graphs import step_level_continuity
        return step_level_continuity(text,var)
    raw=m.parse(text,var)
    def continuous_nodes(e):
        if e[0] not in m.FUNCTIONS|{'q','v','pi','add','mul','div','pow'}:
            raise Unsupported('Continuity of a source operation still requires proof: '+e[0])
        for arg in e[1:]:
            if isinstance(arg,tuple):continuous_nodes(arg)
    continuous_nodes(raw)
    guards=domain_conditions(raw)
    if override is not None:guards.append(('nonzero',m.add(('v',var),m.neg(override))))
    try:plan,_=domain_partition(var,guards,simplify_guards=True)
    except (NotRational,Undefined) as exc:raise Unsupported('A complete real zero or sign set is needed for a domain constraint') from exc
    cuts=list(map(real_intervals.read_quadratic_term,plan['cuts']))
    cells=plan['open_cells'];membership=list(plan['point_membership']);points=[]
    for i,cut in enumerate(cuts):
        x=q(cut.a) if not cut.b else m.add(q(cut.a),m.mul(q(cut.b),('sqrt',q(cut.d))))
        defined=membership[i]
        is_override=override is not None and x==override
        if defined and all(cells[i:i+2]) and not is_override:continue
        if not any(cells[i:i+2]) and not (defined or is_override):continue
        at=None
        if is_override:at=assigned;membership[i]=True
        elif defined:
            at=m.substitute(raw,{('v',var):x})
            if not m.constant_defined(at,ctx):raise Unsupported('Endpoint value on the original domain remains unproved')
            at=m.simplify(at)
        limits={}
        for side,live in zip(('left','right'),cells[i:i+2]):
            if live:
                goal={'kind':'limit','variable':var,'expression':text,'approach':{'point':source(x),'side':side}}
                limits[side]=freeze(request('limit from the '+side+' at '+source(x),goal)['value'])
        values=list(limits.values());row=dict(point=x,one_sided=limits,value=at)
        if not values:classification='continuous_at_isolated_point'
        elif any(v in ('+inf','-inf') for v in values):classification='infinite_discontinuity'
        elif len(values)==2 and different_value(*values,ctx):classification='jump_discontinuity'
        elif len(values)==1 or same_value(*values):
            limit=values[0]
            if not m.constant_defined(limit,ctx):raise Unsupported('A finite real limit is required at the cut')
            if at is None:classification='removable'
            elif same_value(at,limit):classification='continuous'
            elif at[0]=='s':
                classification='continuous_iff_assigned_value_equals_limit'
                row['otherwise']='removable';row['required_value']=limit
            elif different_value(at,limit,ctx):classification='removable'
            else:raise Unsupported('Agreement with the assigned value is unresolved')
        else:raise Unsupported('The two one-sided limits have not been compared')
        row['classification']=classification;points.append(row)
    return plan,{'domain':real_intervals.make_union(cuts,cells,membership),'points':points,
                 'elsewhere':'continuous_on_each_remaining_domain_interval'}



def affine_square_root_order(expression,x,point,side,scale,magnitude):
    from integrals import affine
    from polynomial import NotRational
    from verify import same_value
    number=m.num(m.simplify(m.parse(point,None)))
    if number is None or side not in ('both','left','right'):return None
    raw=m.parse(expression,x);coordinate=('v',x)
    if raw[0]!='sqrt' or raw[1][0]!='div':return None
    P,Q=raw[1][1:]
    if domain_conditions(P) or domain_conditions(Q):return None
    try:a,b=affine(Q,x)
    except (Unsupported,NotRational):return None
    slope=m.num(a);head=m.num(m.simplify(m.substitute(P,{coordinate:q(number)})))
    if not slope or not head or not same_value(m.add(m.mul(a,q(number)),b),ZERO):return None
    sign=1 if head/slope>0 else -1
    admitted='right' if sign==1 else 'left'
    if side not in ('both',admitted):return None
    coefficient=m.simplify(('sqrt',q(abs(head/slope))))
    out=dict(reference=scale,order=q(1,2),coefficient=coefficient,admitted_side=admitted,
             absolute_size_coefficient=coefficient)
    if sign<0 and not magnitude:
        out.update(printed_claim_holds=False,counterexample=dict(
            domain_side=admitted,signed_reference_negative=True,
            unique_real_magnitude_order=q(1,2),real_power_of_printed_reference='undefined'))
    plan=dict(theorem='method.affine_root_relative_magnitude',local_coordinate=x+'-'+point,reference=scale,
              source_side=side,denominator_slope=a,numerator_value=q(head),relative_sign=sign,
              argument=['Линейный знаменатель меняет знак в исходной точке, а числитель сохраняет ненулевой знак.',
                        'Сравнение с квадратным корнем модуля обратного приращения сводится к непрерывному радикалу с ненулевым пределом.',
                        'На отрицательной стороне проверяем, имеет ли требуемая степень действительное значение на исходной величине сравнения.'])
    return plan,out


def relative_leading_term(task,library,request):
    """Translate the leading germ into the power of the reference size named in the question."""
    if library.data.get('task_compilers',{}).get('find_leading_term_and_order')!='relative_order_of_leading_term':
        raise Unsupported('Не подключено правило для исходной величины сравнения')
    fields={'kind','id','schema','source','variable','expression','approach','original_domain_policy',
            'requested_main_term_template','order_relative_to','requested_output'}
    if (set(task)-fields or task.get('schema','typed-mathematical-task-input/v1')!='typed-mathematical-task-input/v1'
            or task.get('requested_output')!=['leading_term','order','asymptotic_justification','original_real_approach_conditions']
            or task.get('original_domain_policy')!='Original real natural domain; preserve each printed approach and all side/parameter restrictions.'
            or not isinstance(task.get('expression'),str) or not isinstance(task.get('source',{}),dict)
            or set(task.get('source',{}))-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256'}):
        raise Unsupported('Не установлены полное условие, область и запрос главного члена')
    variable=task.get('variable')
    if not isinstance(variable,dict) or set(variable)!={'symbol','domain'} or variable['domain']!='real':
        raise Unsupported('Не установлена действительная переменная')
    x=variable['symbol'];approach=task.get('approach')
    if not isinstance(approach,dict) or set(approach)!={'point','direction'}:
        raise Unsupported('Не установлены точка и сторона подхода')
    point,direction=approach['point'],approach['direction']
    at_infinity=point in ('+inf','-inf')
    if at_infinity:
        side='positive_infinity' if point=='+inf' else 'negative_infinity'
        if direction!=side:raise Unsupported('Сторона не соответствует бесконечному пределу')
        local='1/'+x
        reciprocal=x
    else:
        side={'source_unqualified_finite':'both','right':'right','left':'left'}.get(direction)
        if not side or not isinstance(point,str) or not re.fullmatch(r'\d+',point):
            raise Unsupported('Не разобрана конечная точка или сторона подхода')
        local=x if point=='0' else x+'-'+point
        reciprocal='1/'+(x if point=='0' else '('+local+')')
    reference=task.get('order_relative_to','')
    magnitude=reference=='abs('+reciprocal+') as an infinitely large quantity'
    if magnitude and library.data.get('domain_source_resolutions'):scale,sign='abs('+reciprocal+')',-1
    elif reference==local+' as an infinitesimal':scale,sign=local,1
    elif reference==reciprocal+' as an infinitely large quantity':scale,sign=reciprocal,-1
    else:raise Unsupported('Требуемая величина для сравнения не связана с исходной координатой')
    template='C*'+(x if scale==x else '('+scale+')')+'^n'
    if task.get('requested_main_term_template','').removesuffix(' (C constant)')!=template:
        raise Unsupported('Требуемый вид главного члена не совпадает с величиной сравнения')
    if library.data.get('domain_source_resolutions') and sign==-1 and not at_infinity:
        root_order=affine_square_root_order(task['expression'],x,point,side,scale,magnitude)
        if root_order is not None:return root_order
    if magnitude:raise Unsupported('An absolute reference requires a verified positive magnitude germ')
    child={'kind':'leading_asymptotic_term','expression':task['expression'],'variable':x,'approach':{'point':point,'side':side}}
    proof=request('leading monomial on the original approach',child)
    leading=freeze(proof['value'])
    if leading[0]!='leading_monomial':raise Unsupported('Ненулевой главный член не найден')
    order=rational(leading[1])*sign
    if order<=0:raise Unsupported('Не установлено требуемое направление роста или убывания')
    return {'local_coordinate':local,'reference':scale},{'reference':scale,'order':q(order),'coefficient':leading[2]}


def structured_limit(task,library,request,saved=None):
    """Bind a nested scalar goal to the same limit graph as a flat request."""
    if library.data.get('task_compilers',{}).get('compute_limit')!='structured_scalar_limit':
        raise Unsupported('Не объявлена обработка вложенной цели предела')
    fields={'kind','task_type','id','goal','source_assumptions','assumptions','method_requirement','source',
            'source_number','source_exercise_number','source_subpart','source_edition','source_pdf_page','source_pdf_pages',
            'program_status','main_pass_status','source_statement','transcription_notes','derived_original_domain_conditions','derived_domain_conditions','deferred_reason'}
    printed=library.data.get('printed_scalar_limits')
    if printed:fields.add('source_method')
    kind=task.get('kind',task.get('task_type'))
    analytic=library.data.get('finite_analytic_germ')
    reader_note=False
    if analytic and isinstance(task.get('goal'),dict) and isinstance(task['goal'].get('approach'),dict):
        from limit_proofs import source_reader_notes,power_domain_notes
        reader_note=source_reader_notes(task) or library.data.get('power_divided_differences') and power_domain_notes(task)
    if (set(task)-fields or any(task[k]!=kind for k in ('kind','task_type') if k in task)
            or not reader_note and any(task.get(k) for k in ('derived_original_domain_conditions','derived_domain_conditions'))
            or task.get('transcription_notes') and not (reader_note or printed and 'source_method' in task)
            or 'assumptions' in task and 'source_assumptions' in task):
        raise Unsupported('Во вложенной задаче предела остались дополнительные условия или требования')
    provenance=task.get('source',{})
    if not isinstance(provenance,dict) or set(provenance)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','proof_reuse_only','reader_binding_ref'}:
        raise Unsupported('Источник содержит неразобранные требования')
    goal=task.get('goal')
    if kind=='compute_sequence_limit':
        if not isinstance(goal,dict) or set(goal)-{'variable','expression','approach','source_claim'}:
            raise Unsupported('Дополнительное требование к пределу последовательности')
        var=goal.get('variable'); expr=goal.get('expression')
        if (not isinstance(expr,str) or not isinstance(var,str) or goal.get('source_claim') is not None
                or goal.get('approach')!='positive_integer_index_to_infinity'
                or task.get('assumptions')!=[var+' is a positive integer']
                or task.get('source_statement')!=f'Найти lim({var}→∞) {expr}.'):
            raise Unsupported('Область, текст или цель последовательности требуют отдельной проверки')
        # The typed integer domain already carries the single source assumption.
        task={k:v for k,v in task.items() if k not in ('source_statement','assumptions')}
        goal=dict(variable=var,expression=expr,variable_domain='positive_integers',
                  approach=dict(point='+inf',mode='positive_integer_tail'))
    if (not isinstance(goal,dict) or set(goal)-{'variable','expression','variable_domain','approach','parameters','goal'}
            or not {'variable','expression','approach'}<=goal.keys() or not isinstance(goal['expression'],str)
            or goal.get('goal','limit_value') not in ('limit_value','full scalar limit with proof',
                'find the full original limit, including every admissible source direction and parameter case',
                'complete original limit and all its explicit obligations',
                'Full original source limit on its original real domain, with every admissible parameter case and source direction.',
                'Full original source limit, preserving all source parameter cases and the original real domain.')):
        raise Unsupported('Нужна одна полностью определённая скалярная цель')
    approach=goal['approach']
    if not isinstance(approach,dict) or set(approach)-{'point','side','mode'} or 'point' not in approach:
        raise Unsupported('Не определён вид подхода в исходном условии')
    point=approach['point'];side=approach.get('side');mode=approach.get('mode')
    domain=goal.get('variable_domain','real')
    assumptions=task.get('source_assumptions',task.get('assumptions',[]))
    method=task.get('method_requirement')
    root_scope=None
    if library.data.get('power_divided_differences') and method is None and 'root_' in goal['expression']:
        from limit_proofs import positive_root_scope
        root_scope=positive_root_scope(dict(goal,stated_conditions=assumptions))
    if 'source_method' in task:
        instruction=task['source_method']
        grouped=isinstance(instruction,dict) and 'printed_group_instruction' in instruction
        if grouped:instruction=group_heading(instruction,task)
        if (kind!='compute_limit' or not isinstance(instruction,dict)
                or not {'printed_instruction','explicit_required_method'}<=instruction.keys()
                or set(instruction)-{'printed_instruction','explicit_required_method','section_title','preceding_theory','method_binding_status'}):
            raise Unsupported('Не разобраны все указания к способу вычисления')
        heading=instruction['printed_instruction'];headings=printed['headings']
        if not isinstance(heading,str) or heading not in headings:
            raise Unsupported('Для напечатанного требования к методу нет проверяющего правила')
        # Accept bibliographic context without deriving a method from a theorem's name.
        titles=lambda field:'(?:'+'|'.join(map(re.escape,printed[field]))+')'
        reference=r'(?:[:,]\s*(?:page|p\.|с\.)\s*\d+\.)?'
        note=r'(?: No (?:imperative|mandatory) [A-Za-z-]+ clause (?:appears|occurs) in the (?:printed )?(?:task-group )?heading\.)?'
        for key,pattern in (
                ('section_title',r'(?:§\s*\d+\.\s*)?'+titles('section_titles')),
                ('preceding_theory',titles('theory_titles')+reference+note),
                ('method_binding_status',r'(?:PENDING|REVIEWED|CONFIRMED|VERIFIED)(?:_[A-Z0-9]+)*')):
            if key in instruction and (not isinstance(instruction[key],str) or not re.fullmatch(pattern,instruction[key])):
                raise Unsupported('Контекст содержит указание, требующее отдельной сверки')
        prescribed=headings[heading]
        if instruction['explicit_required_method']!=prescribed or 'method_requirement' in task and method!=prescribed:
            raise Unsupported('Предписание метода не совпадает с печатным указанием')
        if prescribed is not None and prescribed not in library.data.get('scalar_limit_methods',{}):
            raise Unsupported('Не подключена проверка предписанного способа')
        text=f"{heading}: {goal['expression']} при {goal['variable']}→{point}; {side}."
        if grouped:
            text=f"Определить значение {goal['expression']} при {goal['variable']}→{point} ({side})."
        # Fixed-parameter hypotheses can accompany either printed heading.
        # Parsing them with no independent variable prevents a change of approach.
        if not isinstance(assumptions,list) or not all(isinstance(c,str) for c in assumptions):
            raise Unsupported('Недопустимая запись ограничений параметров')
        if assumptions:m.context(dict(variable=goal['variable'],parameters=goal.get('parameters',[]),parameter_conditions=assumptions))
        if (task.get('source_statement')!=text or domain!='real' or not side
                or mode not in ('finite_point','positive_infinity','negative_infinity','magnitude_infinity','book_unsigned_infinity')):
            raise Unsupported('Печатные выражение, условия и направление не сверены с математической целью')
        if task.get('transcription_notes'):check_transcribed_formula(task['transcription_notes'],goal,printed)
        method=prescribed
    elif 'source_statement' in task:
        # Text is a second statement of the goal. Only admit verbatim renderings
        # that bind the expression, variable, point and all indicated directions.
        supported={f"Найти предел {goal['expression']} при {goal['variable']}→{point} ({side}; {mode})."} if side and mode else set()
        if side and mode:
            supported.add(f"Найти/доказать предел {goal['expression']} при {goal['variable']}→{point}; {side}; {mode}.")
        if (task['source_statement'] not in supported or 'method_requirement' in task
                or (domain!='real' and not (domain=='positive_integers' and mode=='positive_integer_tail'))):
            raise Unsupported('Текст условия или предписанный способ не сверены со структурированной целью')
        if mode=='positive_integer_tail' and 'variable_domain' not in goal:
            domain='positive_integers'
        if assumptions:
            if not isinstance(assumptions,list) or not all(isinstance(c,str) for c in assumptions):
                raise Unsupported('Условия применимости предела не разобраны')
            if root_scope is None:
                m.context(dict(variable=goal['variable'],parameters=goal.get('parameters',[]),parameter_conditions=assumptions))
    # Bind the printed spelling above before normalizing a signed infinity.
    point={'+infinity':'+inf','-infinity':'-inf'}.get(point,point)
    if mode=='book_unsigned_infinity' and printed is not None and 'source_method' in task:
        mode='magnitude_infinity';approach=dict(approach,mode=mode)
    if mode=='positive_integer_tail' and domain=='positive_integers' and point in ('infinity','+inf') and side in (None,'both','positive_infinity'):
        target={'point':'+inf','side':'positive_infinity'}
    elif mode=='magnitude_infinity' and domain=='real' and point=='infinity' and side=='both':
        target=dict(approach)
    elif (point in ('+inf','-inf') and (mode is None or mode==('positive_infinity' if point=='+inf' else 'negative_infinity'))
          and side in ('both','positive_infinity' if point=='+inf' else 'negative_infinity')):
        target={'point':point,'side':'positive_infinity' if point=='+inf' else 'negative_infinity'}
    elif domain=='real' and mode in (None,'finite_point') and point not in ('infinity','+inf','-inf') and side in ('left','right','both'):
        target={'point':point,'side':side}
    else:raise Unsupported('Несовместимые область, сторона и точка предела')
    child={k:goal[k] for k in ('variable','expression','parameters') if k in goal}
    child.update(kind='limit',approach=target,variable_domain=domain,stated_conditions=assumptions)
    if method is not None or 'method_requirement' in task:child['method_requirement']=method
    if (analytic and method is None and (saved is None or 'analytic_reduction' in saved)
            and all(isinstance(p,str) for p in child.get('parameters',[]))):
        from limit_proofs import analytic_priority,germ_limit,logarithmic_monomial_tail,derived_notes_hold,sine_powers_at_integer_phase
        from operations import ResourceBound,Unavailable
        probe=dict(child,variable=child.get('variable','x'))
        strategies=[logarithmic_monomial_tail,lambda t:sine_powers_at_integer_phase(t,library)]
        if library.data.get('power_divided_differences'):
            from limit_proofs import structural_power_limit
            strategies.insert(0,structural_power_limit)
        if library.data.get('atom_local_limit_proofs'):
            from limit_proofs import (exponential_over_high_power,germ_with_fixed_domain,logarithmically_controlled_power,
                                     logarithmic_divided_difference_of_roots,logarithms_of_vanishing_sine_phases,square_coordinate_limit)
            strategies.extend((exponential_over_high_power,lambda t:logarithmically_controlled_power(t,library),
                               lambda t:logarithmic_divided_difference_of_roots(t,library),
                               lambda t:logarithms_of_vanishing_sine_phases(t,library),lambda t:square_coordinate_limit(t,library),
                               lambda t:germ_with_fixed_domain(t,library)))
        try:
            if analytic_priority(probe):strategies.append(lambda t:germ_limit(t,library,orders=(2,4,6,8)))
        except (Unsupported,ResourceBound):pass
        for strategy in strategies:
            try:plan,value=strategy(probe)
            except (Unsupported,ResourceBound,Unavailable):continue
            if derived_notes_hold(task,plan):
                return dict(scalar_task=child,analytic_reduction=plan),value
        if reader_note or saved is not None:raise Unsupported('The reviewed parameter or domain observation remains unproved')
    if library.data.get('comparable_tail_scale') and (saved is None or 'growth_scale' in saved) and method is None:
        from operations import comparable_tail_scale,ResourceBound
        try:
            proof,value=comparable_tail_scale(child,recorded=saved['growth_scale']['steps'] if saved is not None else None)
            return {'scalar_task':child,'growth_scale':proof},value
        except (Unsupported,ResourceBound):
            if saved is not None:raise
    def conclusion(result):
        if result['status']=='SOLVED':return result['value']
        if result['status']=='DOES_NOT_EXIST':return {'limit_status':'DOES_NOT_EXIST'}
        if result['status']=='SOLVED_CASES':
            return {'split_parameter':result['split_symbol'],'cases':[
                {'assumptions':b['assumptions'],'conclusion':conclusion(b)} for b in result['cases']]}
        raise Unsupported('Для ветви исходной области нет полного вывода о пределе')
    return {'scalar_task':child},conclusion(request('original scalar limit',child,('SOLVED','DOES_NOT_EXIST','SOLVED_CASES')))


def unit_parameter_scope(outer,parameters,conditions):
    """Each contraction hypothesis belongs to a distinct fixed real parameter."""
    from finite_sums import contraction_domain
    contraction_domain(outer,parameters,conditions)
    return list(parameters),list(conditions)


def project_parameter_context(expr,parameters,conditions):
    """Copy source premises involving the subgoal's symbols, including linked parameters."""
    used={p for p in parameters if m.contains(expr,('s',p))}
    names=[set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',c)).intersection(parameters) for c in conditions]
    while True:
        connected=used.union(*(symbols for symbols in names if used & symbols))
        if connected==used:break
        used=connected
    return dict(parameters=[p for p in parameters if p in used],
                stated_conditions=[c for c,symbols in zip(conditions,names) if not symbols or used & symbols])


def prefix_question(summand, index, outer, lower, offset=0, parameters=(), conditions=()):
    """Alpha-normalize the bound index and the endpoint without simplifying away poles."""
    if index==outer:raise Unsupported('Индекс суммы совпадает с именем внешнего индекса')
    parameters,conditions=unit_parameter_scope(outer,parameters,conditions)
    m.context({'variable':index,'parameters':[outer,*parameters]})
    raw=m.parse(summand,index,[outer,*parameters])
    i,n='i','N'
    while i in parameters:i+='_'
    while n in parameters:n+='_'
    renamed=m.substitute(raw,{('v',index):('v',i),('s',outer):('s',n)})
    scope=project_parameter_context(renamed,parameters,conditions) if parameters else {}
    return dict(kind='finite_sum_formula',summand=source(renamed),index=i,variable=n,lower=lower,upper_offset=offset,**scope)


def partial_sum_convergence(task,library,request):
    """Uniformly bound any difference of two prefixes by a vanishing scalar sequence."""
    from finite_sums import prefix_occurrences,check_printed_cauchy,cauchy_term_majorant,sum_factors
    from polynomial import NotRational,Undefined
    if not library.data.get('finite_sum_cauchy_tail'):
        raise Unsupported('Не объявлен переход от оценки слагаемых к критерию Коши')
    goal=task.get('goal')
    if goal is not None:
        permitted={'id','kind','task_type','goal','source_statement','source_number','source_edition','source_pdf_pages',
                   'transcription_notes','assumptions','program_status'}
        if (set(task)-permitted or task.get('transcription_notes') or not isinstance(goal,dict)
                or any(task[k]!='cauchy_sequence_convergence' for k in ('kind','task_type') if k in task)
                or set(goal)-{'required_method','sequence','source_hint'} or goal.get('required_method')!='Cauchy criterion'
                or 'source_statement' not in task):
            raise Unsupported('Не установлены исходное условие и запрошенный метод')
        expression=goal['sequence']
    else:
        if (set(task)-{'id','kind','sequence','variable','variable_domain'} or task.get('kind')!='sequence_convergence'
                or task.get('variable_domain')!='positive_integers'):
            raise Unsupported('Ожидается цель сходимости на натуральных индексах')
        expression=task['sequence']
    sums=list(prefix_occurrences(expression))
    if len(sums)!=1 or expression.strip()!=expression[sums[0][0]:sums[0][1]]:
        raise Unsupported('Не выделена последовательность частичных сумм с единым слагаемым')
    _,_,index,lower,outer,offset,term=sums[0]
    if 1+offset<lower-1 or (goal is None and task['variable']!=outer):
        raise Unsupported('Границы суммирования не согласованы с областью натурального индекса')
    if goal is not None and task.get('assumptions') not in ([outer+' is a positive integer'],
                                                            [outer+' is a positive integer','angles are radians']):
        raise Unsupported('В постановке остались дополнительные предпосылки')
    extended=bool(library.data.get('cauchy_envelope_composition'))
    raw=m.parse(term,index,[outer],('factorial',) if extended else ())
    if m.contains(raw,('s',outer)):raise Unsupported('При вычитании частичных сумм слагаемое должно быть одинаковым для всех верхних границ')
    if goal is not None:
        try:check_printed_cauchy(task,raw,index,lower,outer,offset,extended)
        except (NotRational,Undefined) as exc:raise Unsupported('Требуется проверка печатной последовательности на исходной области') from exc
    phases=[]
    if extended:
        try:bound,phases=cauchy_term_majorant(raw,index,lower)
        except (NotRational,Undefined) as exc:
            raise Unsupported('Не доказана определённость фазы на всех исходных индексах') from exc
        if phases:term=source(bound)
        try:ratio=sum_factors(bound,index,outer,lower)[2]
        except (Unsupported,NotRational,Undefined):ratio=1
        if lower>=1 and abs(ratio)!=1:
            child=dict(kind='series_convergence',term=term,index=index,start_index=lower,
                       method_requirement='cauchy_tail_criterion',requested_output=['convergence_classification','justification'])
            proof=request('Cauchy estimate for all finite tails of the absolute majorant',child)
            if proof['value'].get('criterion')!='cauchy_tail_criterion' or proof['value'].get('absolute_convergence') is not True:
                raise Unsupported('Не доказана единая оценка сумм модулей на произвольном конечном хвосте')
            return dict(variable=outer,first_tail_term=source(m.add(('v',outer),q(offset+1))),
                        start_index=lower,majorant=term,unit_waves=phases),{'converges':True,'criterion':'Cauchy'}
    question=prefix_question(term,index,outer,lower,offset)
    proof=request('absolute term bound by a telescoping difference',{**question,'kind':'finite_sum_bound'})
    facts=proof['compilation']['facts']
    scale=m.num(m.simplify(m.parse(facts['scalar'],question['variable'])))
    if scale is None:raise Unsupported('Независимость веса от верхних индексов не доказана')
    # For b >= n the differences telescope from n+offset+1 to b+offset.
    # The terminal potential is nonnegative, so the first potential bounds the entire tail.
    u=m.add(('v',outer),q(offset+1))
    start=m.substitute(m.parse(facts['potential'],question['index']),{('v',question['index']):u})
    envelope=source(m.mul(q(abs(scale)),start))
    child=dict(kind='limit',variable=outer,expression=envelope,variable_domain='positive_integers',
               approach={'point':'+inf','side':'positive_infinity'})
    limit=request('vanishing bound uniform in the later prefix',child)['value']
    if freeze(limit)!=ZERO:raise Unsupported('Хвостовая оценка не стремится к нулю')
    later='b' if outer!='b' else 'j'
    return dict(variable=outer,later_index=later,first_tail_term=source(u),tail_bound=envelope,valid_from=1,
                **({'unit_waves':phases,'majorant':term} if phases else {}),
                quantifiers=f'for every epsilon>0 there is N such that for all {later}>={outer}>=N, |S_{later}-S_{outer}|<epsilon'),{'converges':True,'criterion':'Cauchy'}


def printed_prefix_limit(task,outer,expression):
    """Bind positive integer indices, fixed reals and the literal contraction bounds."""
    from finite_sums import prefix_occurrences
    hypotheses=task.get('assumptions')
    if not isinstance(hypotheses,list) or hypotheses[:1]!=[outer+' is a positive integer']:
        raise Unsupported('Не подтверждена исходная область натурального индекса')
    if len(hypotheses)<2 or not isinstance(hypotheses[1],str):
        raise Unsupported('Не указана независимость параметров от индекса')
    name=r'[A-Za-z_][A-Za-z_0-9]*'
    declaration=re.fullmatch(rf'({name}(?:\s*,\s*{name})*) (is a fixed real number|are fixed real numbers)',hypotheses[1])
    if not declaration:raise Unsupported('Не установлены фиксированные вещественные параметры')
    params=re.split(r'\s*,\s*',declaration[1])
    if (len(params)==1)!=(declaration[2]=='is a fixed real number'):
        raise Unsupported('Не установлена декларация параметров')
    params,conds=unit_parameter_scope(outer,params,hypotheses[2:])
    if 'source_statement' in task:
        # The omitted terms must form a complete additive block. Expanding a
        # bare occurrence under subtraction, multiplication or division can change its meaning.
        rendered=expression
        for begin,end,index,lower,endpoint,offset,term in reversed(list(prefix_occurrences(expression))):
            raw=m.parse(term,index,[outer,*params])
            if not (raw[0]=='rpow' and raw[1][0]=='s' and raw[1][1] in params and raw[2]==('v',index)
                    and endpoint==outer and lower==1 and offset==0):
                raise Unsupported('Многоточие исходного текста не связано с границами и слагаемым')
            p=raw[1][1]
            leading=re.search(r'\(\s*\d+\s*\+\s*$',expression[:begin])
            if not leading or not re.match(r'\s*\)',expression[end:]):
                raise Unsupported('Не проверены скобки печатной суммы с многоточием')
            rendered=rendered[:begin]+p+'+...+'+p+'^'+outer+rendered[end:]
        suffix=','.join('|'+p+'|<1' for p in params)
        statement=re.sub(r'\s+','',task['source_statement']).replace('…','...').removesuffix('.')
        if statement!='Найтиlim'+re.sub(r'\s+','',rendered)+','+suffix:
            raise Unsupported('Печатная формула или ограничения расходятся со структурированной целью')
    return params,conds


def finite_prefix_limit_input(task):
    """Read the source expression and its quantified fixed-parameter conditions."""
    kind=task.get('kind',task.get('task_type','limit'))
    target={'point':'+inf','side':'positive_infinity'}
    params,conds=[],[]
    if 'goal' in task:
        fields={'id','task_type','kind','goal','assumptions','source_number','source_edition','source_pdf_pages','source_statement',
                'source_exercise_number','source_subpart','transcription_notes','program_status','main_pass_status','deferred_reason'}
        goal=task['goal'];outer=goal['variable'];expression=goal['expression']
        if (set(task)-fields or task.get('transcription_notes') or kind!='finite_sum_sequence_limit' or
                any(task[k]!=kind for k in ('kind','task_type') if k in task)):
            raise Unsupported('Не разобраны фиксированные параметры, условия или требуемый метод составного предела')
        if set(goal)=={'variable','expression','approach'} and goal['approach']=='positive_integer_index_to_infinity':
            params,conds=printed_prefix_limit(task,outer,expression)
        else:
            original='Найти предел при '+outer+'->infinity: '+expression
            assumptions=task.get('assumptions')
            if (set(goal)!={'variable','expression','variable_domain','fixed_parameters','goal'}
                    or goal['variable_domain']!='positive_integers' or not isinstance(assumptions,list)
                    or not assumptions or assumptions[0] not in (outer+' positive integer',outer+' is a positive integer')
                    or goal['goal']!='complete scalar sequence limit of the printed finite sums'):
                raise Unsupported('Не установлено соответствие печатного предела, области индексов и составного выражения')
            params,conds=unit_parameter_scope(outer,goal['fixed_parameters'],assumptions[1:])
            texts={original+'.'}
            if params:texts.add(original+', '+','.join('|'+p+'|<1' for p in params)+'.')
            if task.get('source_statement') not in texts:
                raise Unsupported('Текст предела расходится с формулой или ограничениями параметров')
    else:
        if (set(task)-{'id','kind','variable','expression','variable_domain','parameters','approach','stated_conditions'} or
                kind!='limit' or task.get('variable_domain')!='positive_integers' or task.get('approach')!=target):
            raise Unsupported('Требуется предел на исходных натуральных индексах с разобранными условиями и методом')
        outer=task['variable'];expression=task['expression']
        params,conds=unit_parameter_scope(outer,task.get('parameters',[]),task.get('stated_conditions',[]))
    return outer,expression,params,conds


def finite_sum_context(task,library,request):
    """Rewrite proved prefixes at their original occurrences, preserving the outer obligation."""
    from finite_sums import prefix_occurrences,replace_prefixes
    if not library.data.get('finite_sum_context_substitution'):
        raise Unsupported('В библиотеке не подключена подстановка доказанной формулы суммы')
    kind=task.get('kind',task.get('task_type','limit'))
    coverage=dict(valid_from=1)
    if kind in ('proof','prove'):
        lhs,rhs=task['goal']['proposition'].split('=')
        occurrences=list(prefix_occurrences(lhs))
        if len(occurrences)!=1 or lhs.strip()!=lhs[occurrences[0][0]:occurrences[0][1]]:
            raise Unsupported('Для индукции требуется явная полная сумма в левой части')
        outer=occurrences[0][4]
        if task.get('assumptions')!=[outer+' is a positive integer']:
            raise Unsupported('Область вспомогательной формулы не совпадает с исходной')
        printed=None
        if 'source_statement' in task:
            statement=re.fullmatch(r'(Методом математической индукции доказать|Доказать|Prove)\s*:?\s+([^=]+)=([^=]+?)\.?',task['source_statement'].strip(),re.I)
            if not statement:raise Unsupported('Не установлены печатное равенство и требование к методу')
            direct=re.sub(r'\s+','',statement[2]+'='+statement[3])==re.sub(r'\s+','',lhs+'='+rhs)
            if not direct:printed=statement[3]
        rewritten,facts=replace_prefixes(rhs,outer,request,printed)
        child={**task,'goal':{**task['goal'],'proposition':lhs+'='+rewritten}}
        if 'source_statement' in task:
            child['source_statement']=statement[1]+' '+(lhs if direct else statement[2])+'='+rewritten
        result=request('prove the rewritten identity with the original method',child)
    else:
        target={'point':'+inf','side':'positive_infinity'}
        outer,expression,params,conds=finite_prefix_limit_input(task)
        if params and not library.data.get('parametrized_integer_powers'):
            raise Unsupported('Не подключены целочисленные степени фиксированных параметров')
        divisor_scope='eventually' if library.data.get('scoped_sequence_nonzero') else None
        rewritten,facts=replace_prefixes(expression,outer,request,parameters=params,conditions=conds,
                                         divisor_scope=divisor_scope) if params else replace_prefixes(expression,outer,request)
        child=dict(kind='limit',variable=outer,expression=rewritten,variable_domain='positive_integers',approach=target)
        if params:
            child.update(kind='contracting_power_expression_limit',parameters=params,stated_conditions=conds)
        result=request('limit of the expression with proved sums substituted',child)
        if params and divisor_scope:
            coverage={'domain_scope':result['compilation']['domain_scope'],'sum_identities_valid_from':1}
            if coverage['domain_scope']=='all_indices':coverage['valid_from']=1
    if not facts:raise Unsupported('Не обнаружена подстановка конечной суммы')
    return dict(variable=outer,substitutions=facts,rewritten_goal=child,**coverage),result['value']


def finite_sum_formula(task, library, request):
    from finite_sums import generated_sum_branches
    from polynomial import NotRational, Undefined
    if not library.data.get('finite_sum_formula'):
        raise Unsupported('Не подключено построение формулы конечной суммы')
    if (set(task)-{'kind','id','summand','index','variable','lower','upper_offset','parameters','stated_conditions'}
            or type(task.get('lower')) is not int or type(task.get('upper_offset',0)) is not int):
        raise Unsupported('Не установлены исходные границы конечной суммы')
    index, outer=task['index'],task['variable']
    params,conds=unit_parameter_scope(outer,task.get('parameters',[]),task.get('stated_conditions',[]))
    m.context({'variable':index,'parameters':[outer,*params]})
    if params and not library.data.get('parametrized_integer_powers'):
        raise Unsupported('Не подключена формула суммы с фиксированными параметрами')
    try:
        args=task['summand'],index,outer,task['lower'],task.get('upper_offset',0)
        evidence,branches=generated_sum_branches(*args,parameters=params,conditions=conds) if params else generated_sum_branches(*args)
    except (NotRational,Undefined) as exc:
        raise Unsupported('Не доказано разностное тождество на исходной области суммы') from exc
    if 'identity_task' in evidence:
        request('finite sum identity discovered from the summand',evidence['identity_task'])
    if [label for label,_ in branches] not in (['all'],['even','odd']):
        raise Unsupported('Не установлено покрытие всех достаточно больших натуральных индексов')
    at_index={'all':outer,'even':'2*'+outer,'odd':'2*'+outer+'+1'}
    return evidence,dict(valid_from=evidence['valid_from'],branches=[
        {'indices':label,'at_index':at_index[label],'expression':source(expr)} for label,expr in branches])


def contracting_expression_limit(task,library,request):
    """Apply finite-limit arithmetic after checking the original and limiting divisors."""
    fields={'id','kind','expression','variable','variable_domain','approach','parameters','stated_conditions'}
    if (not library.data.get('parametrized_integer_powers') or set(task)-fields
            or task.get('variable_domain')!='positive_integers'
            or task.get('approach',{'point':'+inf','side':'positive_infinity'})!={'point':'+inf','side':'positive_infinity'}):
        raise Unsupported('Требуется выражение на исходной области натуральных индексов с установленными параметрами')
    variable=task['variable'];params,conditions=unit_parameter_scope(variable,task['parameters'],task['stated_conditions'])
    expression=m.parse(task['expression'],variable,params);n=('v',variable)
    common=dict(variable=variable,variable_domain='positive_integers')
    proved={};steps=[]
    eventual=False;scoped=library.data.get('scoped_sequence_nonzero')
    def nonzero(expr,role,scope):
        nonlocal eventual
        if (role,expr) not in proved:
            goal=dict(kind='contracting_expression_nonzero',expression=source(expr),**common,**project_parameter_context(expr,params,conditions))
            if scoped:goal['scope']=scope
            proof=request(role,goal)
            if proof['value']!={'nonzero':True}:raise Unsupported('Не подтверждено ненулевое значение')
            if proof['compilation'].get('strategy')=='nonzero_limit':eventual=True
            proved[role,expr]=True
    def endpoint(e):
        op=e[0]
        if op in ('s','q'):return e
        if op=='rpow' and e[1][0]=='s' and e[1][1] in params:
            exponent=e[2];shift=ZERO
            if exponent!=n:
                if exponent[0]!='add' or n not in exponent[1:]:
                    raise Unsupported('Для предела степени требуется исходный целый показатель n+d')
                shift=exponent[2] if exponent[1]==n else exponent[1]
            if shift[0]!='q' or shift[2]!=1:raise Unsupported('Сдвиг показателя должен быть целым')
            if ('power',e) not in proved:
                goal=dict(kind='contracting_integer_power_limit',base=e[1][1],offset=shift[1],**common,**project_parameter_context(e,params,conditions))
                proved['power',e]=freeze(request('limit of the signed integer power',goal)['value'])
            return proved['power',e]
        if op not in ('add','mul','div','pow'):
            raise Unsupported('Для оставшейся операции не доказан переход к пределу последовательности')
        left=endpoint(e[1])
        if op=='pow':
            right=e[2]
            if right<=0:denominator,limit=e[1],left
        else:
            right=endpoint(e[2])
            if op=='div':denominator,limit=e[2],right
        if op=='div' or op=='pow' and right<=0:
            nonzero(denominator,'eventually nonzero original divisor' if scoped else 'nonzero divisor at every original index','eventually')
            nonzero(limit,'nonzero limiting divisor','all_indices')
        value=m.simplify((op,left,right))
        steps.append(dict(operation=op,expression=source(e),limit=source(value)))
        return value
    result=endpoint(expression)
    coverage={'domain_scope':'eventually'} if eventual else dict(valid_from=1,domain_scope='all_indices')
    return dict(scope='pointwise for fixed real parameters',limit_operations=steps,**coverage),result


def finite_sum_bound(task, library, saved):
    from finite_sums import propose_sum_bound, verify_sum_bound
    from polynomial import NotRational, Undefined
    if 'bound' not in library.data.get('finite_sum_limit_strategies',()):
        raise Unsupported('Нет правила оценки частичных сумм')
    if (set(task)!={'kind','summand','index','variable','lower','upper_offset'} or
            any(not isinstance(task[k],str) for k in ('summand','index','variable')) or
            any(type(task[k]) is not int for k in ('lower','upper_offset'))):
        raise Unsupported('Не распознаны границы или дополнительные требования к оценке')
    m.context({'variable':task['index'],'parameters':[task['variable']]})
    args=(task['summand'],task['index'],task['variable'],task['lower'],task['upper_offset'])
    try:
        witness=propose_sum_bound(*args) if saved is None else saved['witness']
        facts,bounds=verify_sum_bound(*args,witness)
    except (NotRational,Undefined) as exc:
        raise Unsupported('Не подтверждена рациональная оценка на исходной области') from exc
    return {'witness':witness,'facts':facts},bounds


def sum_limit_input(task):
    """Extract the sum and its affine outer expression, retaining uncancelled denominators."""
    from finite_sums import rational_on_tail
    from polynomial import NotRational, Undefined
    domain = {'point':'+inf','side':'positive_infinity'}
    if task.get('kind')=='sequence_expression_limit':
        from quadrature import riemann_weight,uniform_sum_source
        n,params,conditions=uniform_sum_source(task)
        if params or conditions:raise Unsupported('This exact-prefix strategy does not transport parameter assumptions')
        expression=riemann_weight(task['expression'],n,params,as_prefix=True)
        return sum_limit_input(dict(kind='limit',variable=n,expression=expression,variable_domain='positive_integers',approach=domain))
    if 'goal' in task:
        fields = {'id','task_type','kind','goal','assumptions','source_number','source_edition',
                  'source_pdf_pages','source_pdf_page','source_statement','transcription_notes','program_status'}
        goal = task['goal']
        if (set(task)-fields or task.get('transcription_notes') or not isinstance(goal,dict)
                or set(goal)!={'expression','variable','approach'} or goal['approach']!='positive_integer_index_to_infinity'
                or any(task[k]!='finite_sum_or_product_sequence_limit' for k in ('kind','task_type') if k in task)):
            raise Unsupported('Не распознаны все исходные требования к пределу суммы')
        outer, expression = goal['variable'], goal['expression']
        if not isinstance(outer,str) or task.get('assumptions')!=[outer+' is a positive integer']:
            raise Unsupported('Не установлена область натурального индекса')
        if 'source_statement' in task:
            statement = task['source_statement']
            tokens=r'[A-Za-z_А-Яа-яЁё][\w]*|\d+(?:\.\d+)?|[^\s]'
            printed='Найти lim('+outer+'→∞) '+expression if isinstance(expression,str) else ''
            if (not isinstance(statement,str) or not printed or
                    re.findall(tokens,statement.strip().removesuffix('.'))!=re.findall(tokens,printed)):
                raise Unsupported('Текст и формула исходного условия расходятся')
    else:
        if (set(task)-{'kind','id','variable','expression','variable_domain','approach','parameters'}
                or task.get('kind','limit')!='limit' or task.get('variable_domain')!='positive_integers'
                or task.get('approach')!=domain or task.get('parameters')):
            raise Unsupported('Ожидается предел последовательности на всех натуральных индексах')
        outer, expression = task['variable'], task['expression']
    if not isinstance(expression,str) or len(expression)>4000 or not isinstance(outer,str):
        raise Unsupported('Неверная запись суммы или её индекса')
    m.context({'variable':outer})
    from finite_sums import prefix_occurrences
    occurrences=list(prefix_occurrences(expression))
    if len(occurrences)!=1:raise Unsupported('Требуется одно вхождение конечной суммы')
    begin,end,index,lower,endpoint,offset,summand=occurrences[0]
    if endpoint!=outer or 1+offset<lower-1:
        raise Unsupported('Границы суммы не согласованы с исходной областью')
    marker='__prefix'
    while marker in expression or marker==outer:marker+='_'
    # Parentheses keep original token boundaries around the replaced subexpression.
    surrounding=m.parse(expression[:begin]+'('+marker+')'+expression[end:],outer,[marker])
    absolute=surrounding[0]=='abs'
    affine=surrounding[1] if absolute else surrounding
    node=affine;symbol=('s',marker)
    while node!=symbol:
        if node[0] not in ('add','mul','div'):
            raise Unsupported('Не доказан перенос предела через внешнюю операцию')
        left=m.contains(node[1],symbol)
        if node[0]=='div' and not left:raise Unsupported('Сумма входит в знаменатель')
        node=node[1] if left else node[2]
    at_zero=m.substitute(affine,{symbol:ZERO});at_one=m.substitute(affine,{symbol:ONE})
    try:
        for raw in (at_zero,at_one):rational_on_tail(raw,outer,1)
    except (NotRational,Undefined) as exc:
        raise Unsupported('Не подтверждена исходная область внешнего множителя') from exc
    center=m.simplify(at_zero);scale=m.add(m.simplify(at_one),m.neg(center))
    question=prefix_question(summand,index,outer,lower,offset)
    return question,outer,absolute,center,scale


def sum_limit_strategies(task,library):
    from polynomial import rf
    enabled=library.data.get('finite_sum_limit_strategies',['exact'])
    mesh=(('riemann',) if task.get('kind')=='sequence_expression_limit' and library.data.get('finite_riemann_integral_limit') else ())
    if mesh and task.get('parameters') and library.data.get('abstract_riemann_profiles'):
        mesh+=('abstract_riemann_profile',)
    try:_,outer,_,_,weight=sum_limit_input(task)
    except Unsupported:
        if mesh:return mesh
        raise
    p,d=rf(weight,outer)
    # A shrinking outside factor can turn even a coarse bound into an exact limit.
    order=('bound','exact') if len(p)<len(d) else ('exact','bound')
    return tuple(s for s in order if s in enabled)+mesh


def finite_sum_limit(task,library,request,strategy):
    if strategy=='abstract_riemann_profile' and library.data.get('abstract_riemann_profiles'):
        from finite_sums import abstract_riemann_profile
        return abstract_riemann_profile(task)
    if strategy=='riemann' and task.get('kind')=='sequence_expression_limit' and task.get('method_requirement') in (None,'any'):
        from quadrature import uniform_sum_source
        n,_,_=uniform_sum_source(task)
        child=request('recover and integrate a continuous mesh kernel',dict(task,method_requirement='definite_integral'))
        return dict(outer=n,strategy=strategy,endpoints=[]),freeze(child['value'])
    if not library.data.get('finite_sum_limit') or strategy not in library.data.get('finite_sum_limit_strategies',['exact']):
        raise Unsupported('Способ получения предела суммы не подключён')
    question,outer,absolute,center,scale=sum_limit_input(task)
    if strategy=='exact':
        plan,value=prefix_limit(question,outer,absolute,request,center,scale)
    elif strategy=='bound':
        goal={**question,'kind':'finite_sum_bound'}
        bounds=request('bounds on the original finite sum',goal)['value']
        endpoints=[]
        for key in ('lower','upper'):
            bound=m.parse(bounds[key],question['variable'])
            renamed=m.substitute(bound,{('v',question['variable']):('v',outer)})
            expr=m.add(center,m.mul(scale,renamed))
            child=dict(kind='limit',variable=outer,variable_domain='positive_integers',expression=source(expr),
                       approach={'point':'+inf','side':'positive_infinity'})
            ans=request('limit at the '+key+' bound',child)
            endpoints.append(dict(indices=key,expression=source(expr),limit=freeze(ans['value'])))
        value=endpoints[0]['limit']
        if value!=endpoints[1]['limit']:
            raise Unsupported('Полученные границы имеют разные пределы и не определяют искомый предел')
        if absolute:value='+inf' if value in ('+inf','-inf') else m.simplify(('abs',value))
        plan=dict(endpoints=endpoints,valid_from=bounds['valid_from'])
    else:raise Unsupported('Неизвестный способ получения предела суммы')
    return dict(plan,outer=outer,absolute=absolute,strategy=strategy,scale=source(scale),center=source(center)),value


def prefix_limit(question,outer,absolute,request,center=ZERO,scale=ONE):
    """Transport the original endpoint operation over a proved prefix on the same integer tail."""
    formula=request('closed form of the finite partial sum',question)['value']
    endpoints=[]
    for branch in formula['branches']:
        label=branch['indices']
        expr=m.substitute(m.parse(branch['expression'],question['variable']),{('v',question['variable']):('v',outer)})
        idx=m.substitute(m.parse(branch['at_index'],question['variable']),{('v',question['variable']):('v',outer)})
        repl={('v',outer):idx}
        expr=m.add(m.substitute(center,repl),m.mul(m.substitute(scale,repl),expr))
        if absolute:expr=m.simplify(('abs',expr))
        child=dict(kind='limit',variable=outer,variable_domain='positive_integers',
                   approach={'point':'+inf','side':'positive_infinity'},expression=source(expr))
        result=request('upper endpoint on integer indices: '+label,child)
        endpoints.append({'indices':label,'expression':source(expr),'limit':freeze(result['value'])})
    a,b=endpoints[0]['limit'],endpoints[-1]['limit']
    if a==b:value=a
    elif all(x in ('+inf','-inf') or isinstance(x,tuple) and x[0]=='q' for x in (a,b)):
        value={'limit_status':'DOES_NOT_EXIST'}
    else:raise Unsupported('Не установлено, равны ли пределы подпоследовательностей')
    return dict(valid_from=formula['valid_from'],endpoints=endpoints),value


ADDITIVE_MODEL_GOALS={'solid_sections','source_spatial_moment','source_planar_composition',
                      'improper_space_integrals','source_geometric_application','source_geometric_domains',
                      'source_global_extrema','source_integral_transform','source_surface_field',
                      'source_parameter_integral','source_endpoint_limit','interval_integral_proof',
                      'ordinary_series_proof','source_series_algebra','power_series_boundary','derivative_proof',
                      'improper_integral'}
ADDITIVE_ORDER_CHARTS=('source_additions_numeric_first','source_additions_numeric_last')
ADDITIVE_FIELDS={'source_formula','formula','region','surfaces','equations','boundaries','integrand','conditions',
                 'stated_conditions','substitution','density','function','weight','claim','claims','curve',
                 'term','expression','primitive','left','right','source_expression'}


def ordered_source_additions(text, *, constants_first):
    """Order intact additive terms inside scalar equations and relation fields."""
    if not isinstance(text,str) or '+' not in text or not 0<len(text)<2000:
        return text
    if (not re.fullmatch(r'[A-Za-z_0-9α-ωΑ-Ωπ²³⁴.,+*/^()=<>!−\-\s;]+',text)
            or re.search(r'[\w²³⁴]\s+[\w²³⁴]|\b(?:int|sum|prod|inf)(?:_|\b)',text)):
        return text

    def key(part):
        literal=part.strip(' (')
        number=bool(re.match(r'-?\d',literal))
        return (number!=constants_first,literal.casefold(),literal)

    def align(terms):
        if len(terms)==1:return terms[0]
        if any(not t.strip() for t in terms):raise ValueError('Empty additive operand')
        ordered=sorted(terms,key=key)
        if ordered==terms:return '+'.join(terms)
        return '+'.join('('+t.strip()+')' if i and t.lstrip().startswith(('-', '−')) else t.strip()
                        for i,t in enumerate(ordered))

    def scan(at, nested=False):
        terms=[];clauses=[];part=[]
        while at<len(text):
            c=text[at]
            if c=='(':
                operand,at=scan(at+1,True);part.append('('+operand+')')
                continue
            if c==')':
                if not nested:raise ValueError('Unmatched closing parenthesis')
                break
            if c in ',;<>=' or c=='!' and text[at+1:at+2]=='=':
                # Comparators and argument separators have fixed order.
                clauses.extend((align([*terms,''.join(part)]),c));terms=[];part=[]
            elif c=='+' and re.search(r'[^\s+*/^\-−]\s*$', ''.join(part)):
                terms.append(''.join(part));part=[]
            else:part.append(c)
            at+=1
        if nested and at==len(text):raise ValueError('Unmatched opening parenthesis')
        return ''.join([*clauses,align([*terms,''.join(part)])]),at+int(nested)
    try:return scan(0)[0]
    except ValueError:return text


def additive_source_candidate(task,chart):
    if chart not in ADDITIVE_ORDER_CHARTS:raise Unsupported('Unknown source additive order')
    first=chart==ADDITIVE_ORDER_CHARTS[0]
    def rewrite(v):
        if isinstance(v,list):return [rewrite(z) for z in v]
        return ordered_source_additions(v,constants_first=first)
    updated={k:rewrite(v) if k in ADDITIVE_FIELDS else v for k,v in task.items()}
    if updated==task:raise Unsupported('The source additions are already in this order')
    return updated


def additive_order_options(task,kind):
    if kind not in ADDITIVE_MODEL_GOALS:return ()
    seen=[];charts=[]
    for chart in ADDITIVE_ORDER_CHARTS:
        try:changed=additive_source_candidate(task,chart)
        except Unsupported:continue
        if changed not in seen:
            seen.append(changed);charts.append(chart)
    return tuple(charts)



def compose_goal(task,library,request,chart=None,*,saved=None):
    kind=composed_kind(task)
    if chart in ADDITIVE_ORDER_CHARTS:
        if kind not in ADDITIVE_MODEL_GOALS:raise Unsupported('The additive input rule is unavailable for this goal')
        normalized=additive_source_candidate(task,chart)
        if composed_kind(normalized)!=kind:raise Unsupported('The rewrite changes the mathematical goal kind')
        child=request('математически равносильный порядок слагаемых',normalized)
        if child.get('schema')!=COMPOSED_GOALS[kind][0] or 'compilation' not in child:
            raise Unsupported('The normalized mathematical model must prove the same goal')
        return {**child['compilation'],'source_addition_order':chart,
                'source_addition_basis':'method.commutative_source_expression_order'},child['value']
    if kind=='elementary_proof':
        from elementary_proofs import elementary_proof
        return elementary_proof(task,library,request)
    if kind=='source_integral_transform':
        from quadrature import source_integral_transform
        return source_integral_transform(task,library,request)
    if kind=='source_surface_field':
        from surface_fields import source_surface_field
        return source_surface_field(task,library,request)
    if kind=='source_spatial_moment':
        from plane_domains import source_spatial_moment
        return source_spatial_moment(task,library,request)
    if kind=='source_geometric_domains':
        from geometric_domains import source_geometric_domains
        return source_geometric_domains(task,library,request)
    if kind=='source_geometric_application':
        from planar_integrals import source_geometric_application
        return source_geometric_application(task,library,request)
    if kind=='source_definite_trace':
        from quadrature import source_definite_trace
        return source_definite_trace(task,library,request)
    if kind=='source_endpoint_limit':
        from quadrature import source_endpoint_limit
        return source_endpoint_limit(task,library,request)
    if kind=='source_planar_composition':
        from planar_integrals import source_planar_composition
        return source_planar_composition(task,library,request)
    if kind=='functional_primitive':
        from integrals import primitive_from_function
        return primitive_from_function(task,library,request)
    if kind=='defined_riemann_integral':
        from quadrature import defined_riemann_integral
        return defined_riemann_integral(task,library)
    if kind=='indefinite_integral_recurrence':
        from integrals import trig_primitive_recurrence
        return trig_primitive_recurrence(task,library)
    if kind=='real_function_proof':
        from real_functions import real_function_goal
        return real_function_goal(task,library,request)
    if kind=='derivative_proof':
        from derivative_proofs import derivative_proof
        return derivative_proof(task,library,request)
    if kind=='source_uniform_functional':
        from uniform import (absolute_numeric_tail,abstract_uniform_theorem,concentration_goal,regularity_of_series,uniform_source_witness,
                             uniform_exp_taylor,uniform_sequence_abstract)
        from uniform import functional_transport_goal,functional_transport_routing
        if library.data.get('coefficient_and_limit_transport') and functional_transport_routing(task,task['kind']):
            try:return functional_transport_goal(task,library,request)
            except Unsupported:pass
        target=task['kind']
        if target in ('parameter_sequence_classification','sequence_integral_interchange'):
            return concentration_goal(task,library)
        if target=='uniform_sequence_theorem':return uniform_sequence_abstract(task,library)
        if target in ('functional_series_theorem','function_sequence_example','series_proposition'):
            return abstract_uniform_theorem(task,library)
        if target=='functional_series_example':return uniform_source_witness(task,library,request)
        if target in ('functional_series_regularity','series_operation_justification'):return regularity_of_series(task,library)
        if not library.data.get('positive_uniform_error_bounds'):raise Unsupported('No uniform error theorem is available')
        return (uniform_exp_taylor if target=='uniform_taylor_error' else absolute_numeric_tail)(task)
    if kind=='abstract_series_theorem':
        from finite_sums import abstract_series_theorem
        return abstract_series_theorem(task,library)
    if kind=='ordinary_series_proof':
        from ordinary_series import ordinary_goal
        return ordinary_goal(task,library,request)
    if kind in ('explicit_cauchy_series','certified_series_prefix'):
        from finite_sums import cauchy_series_certificate,sufficient_series_prefix
        return (cauchy_series_certificate if kind=='explicit_cauchy_series' else sufficient_series_prefix)(task,library)
    if kind=='source_series_algebra':
        if (library.data.get('sequence_source_scope') and task.get('kind',task.get('task_type')) in
                ('finite_sum_or_product_sequence_limit','characterize_convergence_by_envelope_algebra')):
            from finite_sums import sequence_source_scope
            return sequence_source_scope(task)
        from finite_sums import (algebraic_series_goal,cauchy_product_identity,differential_series_identity,uniform_polynomial_sums,
                                 transformed_power_series,source_power_series_calculus)
        from finite_sums import coefficient_transport_goal,coefficient_transport_routing
        if library.data.get('coefficient_and_limit_transport') and coefficient_transport_routing(task,task['kind']):
            try:return coefficient_transport_goal(task,library,request)
            except Unsupported:pass
        rule={'rational_series_radius':algebraic_series_goal,'formal_reciprocal_expansion':algebraic_series_goal,
              'series_identity_proof':cauchy_product_identity,'series_ode_identity':differential_series_identity,
              'uniform_partial_sums':uniform_polynomial_sums}.get(task['kind'])
        if rule:return rule(task,library)
        return (transformed_power_series if task['kind']=='infinite_power_series_expansion' and 'additional_series' not in task
                else source_power_series_calculus)(task,library,request)
    if kind=='fourier_coefficient_relation':
        from quadrature import fourier_coefficient_action
        return fourier_coefficient_action(task,library)
    if kind=='interval_integral_proof':
        from planar_integrals import interval_proof
        return interval_proof(task,library,request)
    if kind=='source_vector_calculus':
        from cartesian_fields import vector_calculus
        from planar_integrals import curve_chart_goal,source_curve_integrals
        if curve_chart_goal(task):return source_curve_integrals(task,library,request)
        return vector_calculus(task,library,request)
    if kind=='scalar_source_proof':
        from scalar_proofs import scalar_proof
        return scalar_proof(task,library,request)
    if kind=='multivariate_operator_proof':
        from cartesian_fields import multivariate_operator_proof
        return multivariate_operator_proof(task,library,request)
    if kind in ('polynomial_interpolation','bernstein_approximation','stirling_application','product_and_approximation_claim'):
        from finite_sums import interpolation_polynomial,bernstein_polynomial,stirling_factorials,products_and_approximation
        constructor={'polynomial_interpolation':interpolation_polynomial,'bernstein_approximation':bernstein_polynomial,
                     'stirling_application':stirling_factorials,'product_and_approximation_claim':products_and_approximation}[kind]
        return constructor(task,library)
    if kind=='applied_extremum':
        from graphs import applied_extremum
        return applied_extremum(task,library)
    if kind=='local_geometry':
        from cartesian_fields import local_geometry
        return local_geometry(task,library,request)
    if kind=='certified_numeric_approximation':
        from quadrature import certified_numeric_approximation
        return certified_numeric_approximation(task,library,saved)
    if kind=='approximate_equation_roots':
        from graphs import approximate_equation_roots
        return approximate_equation_roots(task,library,request)
    if kind=='parameter_improper_evaluation':
        from quadrature import evaluate_parameter_integral
        return evaluate_parameter_integral(task,library,request)
    if kind=='fourier_integral_representation':
        from quadrature import fourier_integral_representation
        return fourier_integral_representation(task,library,saved)
    if kind=='power_series_boundary':
        from finite_sums import power_series_boundary
        return power_series_boundary(task,library,request)
    if kind=='solve_functional_equation':
        from uniform import functional_characterization
        return functional_characterization(task,library,saved)
    if kind=='complex_power_series_disk':
        from uniform import complex_series_disk
        return complex_series_disk(task,library)
    if kind=='fourier_expansion':
        from uniform import fourier_transport_goal
        if library.data.get('coefficient_and_limit_transport'):
            try:return fourier_transport_goal(task,library)
            except Unsupported:pass
        from quadrature import fourier_expansion
        return fourier_expansion(task,library,saved)
    if kind=='function_sign_sets':return function_sign_sets(task,library,request)
    if kind=='rectangular_grid_sums':
        from planar_integrals import rectangular_grid_sums
        return rectangular_grid_sums(task,library,saved)
    if kind=='plane_measure':
        from planar_integrals import plane_measure
        return plane_measure(task,library,request,chart,saved)
    if kind=='higher_derivative':return ordinary_differentiation(task,library,request)
    if kind=='successive_composition':return successive_composition(task,library,request)
    if kind=='order_certificate':
        from finite_sums import order_certificate
        return order_certificate(task,library)
    if kind in ('derivative_signs','printed_inequality'):
        from graphs import derivative_signs,printed_inequality
        import polynomial as poly, intervals as line
        try:return (derivative_signs if kind=='derivative_signs' else printed_inequality)(task,library,request)
        except (poly.NotRational,poly.Undefined,poly.ResourceBound,line.Unsupported) as exc:
            raise Unsupported(str(exc) or 'The original sign conditions need a further exact partition') from exc
    if kind=='plane_geometry':
        from plane_geometry import plane_geometry
        return plane_geometry(task,library,request)
    if kind=='exact_ordinary_order':return exact_ordinary_order(task,library,request)
    if kind=='measurement_uncertainty':return measurement_uncertainty(task,library)
    if kind=='curve_contacts':
        from cartesian_fields import curve_contacts
        return curve_contacts(task,library,request)
    if kind=='symbolic_order':return symbolic_order(task,library,request)
    if kind=='infinite_power_series_expansion':return analytic_power_series(task,library,request)
    if kind=='sided_derivatives':return sided_derivatives(task,library,request)
    if kind=='continuous_least_squares':
        from quadrature import continuous_least_squares
        return continuous_least_squares(task,library,request)
    if kind=='source_parameter_integral':
        from quadrature import parameter_catalogue_proof
        return parameter_catalogue_proof(task,library,request)
    if kind=='improper_space_integrals':
        from quadrature import improper_space_proof
        return improper_space_proof(task,library)
    if kind=='source_global_extrema':
        from level_sets import source_global_extrema
        return source_global_extrema(task,library)
    if kind=='finite_interval_integral':
        from quadrature import finite_interval_value
        return finite_interval_value(task,library,request)
    if kind=='continuous_riemann_limit':
        from quadrature import uniform_sum_limit
        return uniform_sum_limit(task,library,request,saved)
    if kind in ('finite_product_limit','finite_product_identity'):
        from finite_sums import finite_product
        return finite_product(task,library,request,identity=kind=='finite_product_identity',saved=saved)
    if kind in ('sequence_expression_nonzero','sequence_expression_limit'):
        from finite_sums import sequence_expression_goal
        return sequence_expression_goal(task,library,request)
    if kind=='sequence_term_at':
        from finite_sums import sequence_term_at
        return sequence_term_at(task,library,request)
    if kind in ('contracting_integer_power_limit','contracting_expression_nonzero'):
        from finite_sums import geometric_endpoint
        return geometric_endpoint(task,library,request)
    if kind=='contracting_power_expression_limit':return contracting_expression_limit(task,library,request)
    if kind in ('sequence_liminf_limsup','sequence_range_and_envelopes'):
        if chart=='exact_integer_phase' or saved is not None and 'family_reduction' in saved:
            from elementary_proofs import cluster_packet
            plan,value=cluster_packet(task,library)
            return dict(family_reduction=plan),value
        from finite_sums import sequence_envelopes
        return sequence_envelopes(task,library,request)
    if kind=='discrete_global_extremum':
        from finite_sums import discrete_extremum
        return discrete_extremum(task,library)
    if kind=='real_root_count_isolation':
        from graphs import isolate_equation
        return isolate_equation(task,library)
    if kind=='partial_sum_convergence':return partial_sum_convergence(task,library,request)
    if kind=='finite_sum_context':return finite_sum_context(task,library,request)
    if kind=='finite_sum_or_product_sequence_limit':return finite_sum_limit(task,library,request,chart)
    if chart is not None and chart not in integral_charts(task,library):
        raise Unsupported('The change of variable is not admitted for this integral')
    if kind=='finite_sum_bound':return finite_sum_bound(task,library,saved)
    if kind=='finite_sum_formula':return finite_sum_formula(task,library,request)
    if kind=='compute_limit':
        old=saved is not None and 'family_reduction' not in saved
        goal=task.get('goal',{});expr=goal.get('expression','') if isinstance(goal,dict) else ''
        extension=isinstance(goal,dict) and ('goal' in goal or isinstance(expr,str) and
                    re.search(r'\b(?:root_|root4\(|log_)|sin\([^()]+\)\^.+/sqrt\(',expr))
        if (library.data.get('scalar_family_transitions') and not old and not task.get('source_method') and
                not task.get('method_requirement') and (extension or saved is not None)):
            from scalar_families import extended_nested_limit
            from polynomial import ResourceBound
            try:plan,value=extended_nested_limit(task,library)
            except (Unsupported,ResourceBound,ArithmeticError,TypeError,ValueError):
                if saved is not None:raise
            else:return dict(family_reduction=plan),value
        return structured_limit(task,library,request,saved)
    if kind=='source_asymptotic_proof':
        from limit_proofs import source_limit_proof
        return source_limit_proof(task,library,request)
    if kind=='find_leading_term_and_order':return relative_leading_term(task,library,request)
    if kind in ('discontinuity_classification','piecewise_continuity'):
        if library.data.get('scalar_family_transitions') and (saved is None or 'family_reduction' in saved):
            from scalar_families import oscillation_and_continuity
            try:plan,value=oscillation_and_continuity(task,kind,library)
            except (Unsupported,ArithmeticError,TypeError,ValueError):
                if saved is not None:raise
            else:return dict(family_reduction=plan),value
        return classify_continuity(task,library,request)
    if kind=='pointwise_limit_continuity':
        from graphs import pointwise_phase_limit
        return pointwise_phase_limit(task,library)
    if kind=='integral_substitution_validity':
        from quadrature import substitution_validity
        if not library.data.get('proposed_substitution_validity'):raise Unsupported('Substitution validity is not admitted')
        return substitution_validity(*proposed_substitution_input(task),request)
    if kind=='infinite_rational_product':
        from finite_sums import classified_product
        return classified_product(task,library,request,saved)
    if kind=='function_increment':return function_increment(task,library,request)
    if kind=='linear_approximation':
        from quadrature import linear_approximation
        return linear_approximation(task,library,request,saved)
    if kind=='root_linearization':
        from quadrature import root_linearization
        return root_linearization(task,library,request,saved)
    if kind=='uniform_continuity':
        from uniform import continuity_goal
        return continuity_goal(task,library,request,chart,saved)
    if kind in ('quantifier_continuity','epsilon_delta_proof'):
        from uniform import neighborhood_goal
        return neighborhood_goal(task,library)
    if kind=='composite_function_differentiation':return composite_differentiation(task,library,request)
    if kind=='sampled_field_taylor':return sampled_field_taylor(task,library)
    if kind in ('integrate_by_series','power_series_quadrature'):
        from finite_sums import termwise_integral_sum,power_series_quadrature
        return termwise_integral_sum(task,library,request) if kind=='integrate_by_series' else power_series_quadrature(task,library)
    if kind=='series_numeric_approximation':
        from finite_sums import series_numeric_bounds
        return series_numeric_bounds(task,library,saved)
    if kind=='series_sum':
        from polynomial import NotRational,Undefined
        if library.data.get('generating_series_operators'):
            from finite_sums import generating_series_sum
            started=False
            def checked_request(*args):
                nonlocal started
                started=True
                return request(*args)
            try:return generating_series_sum(task,library,checked_request)
            except (Unsupported,NotRational,Undefined) as exc:
                if started:raise Unsupported(str(exc)) from exc
        try:return rational_series_sum(task,library,request,saved)
        except (NotRational,Undefined) as exc:raise Unsupported(str(exc) or 'No rational antidifference for this term') from exc
    if kind=='parametric_curve_derivatives':return parametric_curve_derivatives(task,library,request)
    if kind=='inverse_definition_derivative':return inverse_definition_derivative(task,library)
    if kind=='elementary_taylor_limit':
        from limit_proofs import elementary_taylor_limit
        return elementary_taylor_limit(task,library)
    if kind=='implicit_graph_derivatives_and_values':
        from cartesian_fields import implicit_graph_values
        return implicit_graph_values(task,library,request)
    if kind=='differentiate_floor_expression':return integer_step_derivative(task,library,request)
    if kind=='multivariate_taylor':return multivariate_taylor(task,library,request)
    if kind=='improper_integral':
        from quadrature import improper_integral
        return improper_integral(task,library,request)
    if kind=='implicit_derivative':return implicit_derivative(task,library,request)
    if kind in ('oriented_boundary_integral','integral_reduction_family'):
        from quadrature import oriented_boundary_integral,indexed_moment
        return (oriented_boundary_integral if kind=='oriented_boundary_integral' else indexed_moment)(task,library,request)
    if kind in ('uniform_sequence_convergence','uniform_series_convergence'):
        from uniform import (uniform_sequence,uniform_series_majorant,uniform_periodic_tail,uniform_telescoping_series,
                             elementary_uniform_error,general_uniform_series,weierstrass_tail_envelopes,UNIFORM_TAIL_THEOREMS)
        from polynomial import NotRational,Undefined
        try:
            if kind=='uniform_series_convergence':
                theorem=(saved or {}).get('theorem')
                if theorem=='method.weierstrass_tail_envelopes':return weierstrass_tail_envelopes(task,library)
                if theorem in UNIFORM_TAIL_THEOREMS:
                    return general_uniform_series(task,library,saved)
                try:
                    if task.get('requested_output')==['convergence_character','proof']:
                        return uniform_telescoping_series(task,library,request,saved)
                    if task.get('requested_output')==['uniform_convergence_classification','proof'] or (
                            saved or {}).get('theorem')=='method.uniform_periodic_summation_by_parts':
                        return uniform_periodic_tail(task,library,saved)
                    try:return uniform_series_majorant(task,library)
                    except Unsupported:
                        if task.get('method_requirement') or not library.data.get('uniform_periodic_tail'):raise
                        return uniform_periodic_tail(task,library,saved)
                except (Unsupported,NotRational,Undefined):
                    if saved is not None or not library.data.get('general_uniform_series_tails'):raise
                    if task.get('method_requirement')=='weierstrass_majorant':return weierstrass_tail_envelopes(task,library)
                    if task.get('method_requirement'):raise
                    return general_uniform_series(task,library)
            if (saved or {}).get('method')=='elementary_uniform_error':return elementary_uniform_error(task,library)
            try:return uniform_sequence(task,library,request)
            except (Unsupported,NotRational,Undefined,TypeError):
                if saved is not None or not library.data.get('elementary_uniform_errors'):raise
                return elementary_uniform_error(task,library)
        except (NotRational,Undefined) as exc:raise Unsupported(str(exc) or 'Another uniform-convergence argument is required') from exc
    if kind=='exact_form':
        from integrals import exact_form
        return exact_form(task,library,request)
    if kind=='line_integral':
        from quadrature import line_integral
        return line_integral(task,library,request)
    if kind=='area_from_line_integral':
        from planar_integrals import boundary_area
        return boundary_area(task,library,request,saved)
    if kind=='rational_primitive_algebraic_part':
        from integrals import rational_algebraic_part
        return rational_algebraic_part(task,library)
    if kind=='rational_primitive_criterion':
        from integrals import rational_primitive_criterion
        return rational_primitive_criterion(task,library)
    if kind=='quadratic_radical_primitive_proof':
        from integrals import quadratic_radical_primitive_proof
        return quadratic_radical_primitive_proof(task,library)
    if kind=='partial_fraction_symmetry':
        from integrals import partial_fraction_symmetry
        return partial_fraction_symmetry(task,library)
    if kind=='linear_primitive':
        if chart:
            from source_primitives import CHARTS as SOURCE_PRIMITIVE_CHARTS,chart_options,primitive_chart
            if chart in SOURCE_PRIMITIVE_CHARTS:
                if chart not in library.data.get('source_primitive_charts',()) or chart not in chart_options(task):
                    raise Unsupported('The exact source coordinate is not permitted for this integral')
                return primitive_chart(task,chart,request)
            if library.data.get('primitive_foundation_transitions'):
                from integrals import FOUNDATION_CHARTS,foundation_options,foundation_transition
                if chart in FOUNDATION_CHARTS:
                    if chart not in foundation_options(task):raise Unsupported('Foundation transition violates the original method')
                    return foundation_transition(task,library,request,chart)
            from integrals import ELEMENTARY_CHARTS,elementary_chart_options,elementary_primitive_transition
            if chart in ELEMENTARY_CHARTS:
                if not library.data.get('elementary_primitive_transitions') or chart not in elementary_chart_options(task):
                    raise Unsupported('The prescribed method does not admit this primitive transition')
                if chart in ('regular_piecewise','algebraic_lift') and not library.data.get('composition_primitive_skills'):
                    raise Unsupported('The primitive composition transition is unavailable')
                return elementary_primitive_transition(task,request,chart)
            from radical_primitives import CHARTS,radical_chart_options,radical_coordinate_primitive
            if chart in CHARTS:
                if not library.data.get('real_radical_coordinates') or chart not in radical_chart_options(task):
                    raise Unsupported('The library or the assigned method does not admit this primitive transition')
                return radical_coordinate_primitive(task,request,chart)
            from integrals import rational_coordinate_primitive
            return rational_coordinate_primitive(task,request,chart)
        from integrals import linear_primitive
        return linear_primitive(task,library,request)
    if kind=='level_sets':
        from level_sets import level_sets
        from polynomial import NotRational,Undefined
        try:return level_sets(task,library,request)
        except (NotRational,Undefined) as exc:raise Unsupported(str(exc) or 'An exact level classification is unavailable') from exc
    if kind=='spatial_reduction':
        from plane_domains import spatial_reduction
        return spatial_reduction(task,library,request)
    if kind=='cartesian_flux':
        from cartesian_fields import cartesian_flux
        return cartesian_flux(task,library,request)
    if kind=='solid_sections':
        from plane_domains import solid_sections
        return solid_sections(task,library,request,saved=saved)
    if kind=='bound_curve_integral':
        from quadrature import bound_curve_integral
        return bound_curve_integral(task,library,request,saved)
    if kind=='greens_boundary_integral':
        from quadrature import green_source_integral
        return green_source_integral(task,library,request,chart)
    if kind=='curve_metric':
        from plane_domains import curve_metric
        return curve_metric(task,library,request)
    if kind=='curve_curvature_radius':
        from planar_integrals import plane_curve_radius
        return plane_curve_radius(task,library,request)
    if kind=='surface_area':
        from planar_integrals import revolution_patch
        return revolution_patch(task,library,request)
    if kind=='bounded_section_measure':
        from plane_domains import section_measure
        return section_measure(task,library,request)
    if kind=='geometric_moments':
        from planar_integrals import source_measure_moments
        return source_measure_moments(task,library,request)
    if kind in ('planar_domain','cartesian_slices','reverse_iterated_integral'):
        from plane_domains import planar_domain
        from quadrature import cartesian_slices
        from polynomial import NotRational,Undefined
        try:return planar_domain(task,library,request) if kind=='planar_domain' else cartesian_slices(task,library)
        except (NotRational,Undefined) as exc:raise Unsupported(str(exc) or 'No exact planar certificate') from exc
    if kind in ('classify_extrema','real_function_domain','restricted_function_image','real_function_domain_and_range','function_bounds'):
        from graphs import extrema_plan,natural_domain,function_image,function_bounds,image_by_branches
        from polynomial import NotRational,Undefined
        build={'classify_extrema':extrema_plan,'real_function_domain':natural_domain,'function_bounds':function_bounds}.get(kind,function_image)
        try:
            if chart=='images_of_monotonicity_cells' and kind=='restricted_function_image':return image_by_branches(task,library,request)
            return build(task,library,request)
        except (NotRational,Undefined) as exc:raise Unsupported(str(exc) or 'A complete rational sign partition is unavailable') from exc
    if kind=='variable_endpoint_integral_derivative':
        from quadrature import endpoint_derivatives
        return endpoint_derivatives(task,library,request)
    if kind in ('definite_integral_sign','compare_definite_integrals','mean_function_value'):
        from quadrature import finite_integral_order,finite_integral_mean
        return (finite_integral_mean if kind=='mean_function_value' else finite_integral_order)(task,library,request)
    if kind=='weighted_mean_integral_estimate':
        from quadrature import weighted_mean_estimate
        return weighted_mean_estimate(task,library,request)
    if kind=='ellipsoid_moment':
        from quadrature import ellipsoid_moment
        return ellipsoid_moment(task,library)
    if task['kind']=='iterated_integral':
        from quadrature import iterated_integral
        return iterated_integral(task,library,request,chart)
    if task['kind']=='definite_quadrature':
        from quadrature import quadrature
        return quadrature(task,library,request)
    if task['kind']=='continuous_extension':
        fields={'kind','id','source','variable','expression','parameters','parameter_conditions','point','source_neighborhood','requested_output'}
        if (not library.data.get('finite_continuous_extensions') or set(task)-fields or
            task.get('requested_output')!=['continuous_extension_value'] or task.get('source_neighborhood') not in ('both','left','right')):
            raise Unsupported('Unknown continuous-extension source domain or obligation')
        child={k:task[k] for k in ('variable','expression','parameters','parameter_conditions') if k in task}
        child.update(kind='limit',approach={'point':task['point'],'side':task['source_neighborhood']})
        ctx=m.context(child);point=ctx['point']
        if point in ('+inf','-inf') or not m.constant_defined(point,ctx):
            raise Unsupported('A real finite point of extension is required')
        proof=request('limit_in_source_domain',child,('SOLVED','DOES_NOT_EXIST'))
        plan={'point':point,'source_neighborhood':ctx['side']}
        if proof['status']=='DOES_NOT_EXIST':
            return plan,{'exists':False,'unequal_limits':[s['value'] for s in proof['sides']]}
        value=freeze(proof['value'])
        if value in ('+inf','-inf'):return plan,{'exists':False,'infinite_limit':value}
        if not m.constant_defined(value,ctx):raise Unsupported('Finite real limit has not been established')
        return plan,{'exists':True,'assigned_value':value}
    if kind in ('potential_from_differential','exact_differential_endpoints'):
        from cartesian_fields import exact_form
        return exact_form(task,library,request,chart)
    if kind=='differential_coordinate_change':
        from cartesian_fields import transform_coordinates
        return transform_coordinates(task,library,request)
    if kind=='implicit_differential_identity':
        from cartesian_fields import differential_invariants
        return differential_invariants(task,library,request)
    if kind=='implicitly_coupled_system':
        from cartesian_fields import implicit_system
        return implicit_system(task,library,request)
    if kind in ('formal_differential_identity','eliminate_arbitrary_functions'):
        from cartesian_fields import field_composition
        return field_composition(task,library,request)
    if kind in ('multivariable_limit','multivariate_continuity'):
        from cartesian_fields import joint_limit
        return joint_limit(task,library,request)
    if kind=='discontinuity_set':
        from cartesian_fields import discontinuity_locus
        return discontinuity_locus(task,library)
    if kind=='compare_ordered_partials':
        from verify import same_value
        origin=task['source'];pair=origin.get('required_equality')
        if (set(origin)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','printed_group_heading','required_equality','derivative_sequence_convention'}
                or origin.get('derivative_sequence_convention','Left to right in the executable; both orders must be independently established on their common domain.')!='Left to right in the executable; both orders must be independently established on their common domain.'):
            raise Unsupported('Не разобраны дополнительные вопросы о частных производных')
        heading=re.fullmatch(r'Проверить равенство ∂²(\w+)/∂([a-z])∂([a-z]) = ∂²\1/∂([a-z])∂([a-z])',origin.get('printed_group_heading',''))
        if (not heading or not isinstance(pair,(list,tuple)) or len(pair)!=2 or not all(isinstance(p,(list,tuple)) for p in pair)
                or {tuple(p) for p in pair}!={(heading[3],heading[2]),(heading[5],heading[4])}
                or len(set(map(tuple,pair)))!=2):raise Unsupported('Сохранённые порядки дифференцирования не воспроизводят исходное равенство')
        child={k:v for k,v in task.items() if k!='source'}
        result=request('обе упорядоченные производные на исходной области',child)
        computed={tuple(i):freeze(v) for i,v in result['partial_values']}
        if any(tuple(p) not in computed for p in pair):raise Unsupported('Одна из двух производных ещё не доказана')
        left,right=(computed[tuple(p)] for p in pair)
        if not same_value(left,right):raise Unsupported('Формулы упорядоченных производных не равны')
        return dict(original_domain=result['compilation']['natural_domain'],ordered_equality=pair,independent_values=[left,right],
                    applied_methods=['method.coordinate_section_derivatives']),dict(equal=True,common_value=left,ordered_values=result['value'])
    if kind=='euler_integral_evaluation':
        from quadrature import euler_integral
        return euler_integral(task,library)
    if kind in ('multivariate_extrema','constrained_extrema'):
        from level_sets import quadratic_extrema
        return quadratic_extrema(task,library,request)
    if kind=='first_and_second_total_differentials':
        from cartesian_fields import total_differentials
        return total_differentials(task,library,request)
    if kind=='tangent_geometry':return tangent_geometry(task,library,request)
    if task['kind']=='scalar_field_geometry':return scalar_field_geometry(task,library,request)
    return differential_operator(task,library,request)


def scalar_field_geometry(task,library,request):
    """Apply the differential of a real scalar field at smooth points in Euclidean coordinates."""
    from verify import same_value
    fields={'kind','id','schema','source','transcription','function','variables','parameters','stated_conditions','points','requests','level'}
    if set(task)-fields or library.data.get('task_compilers',{}).get('scalar_field_geometry')!='euclidean_differential':
        raise Unsupported('Unknown field goal or omitted source obligation')
    base=compile_partial_bundle({'kind':'partial_derivatives',**{k:task[k] for k in ('function','variables','parameters','stated_conditions') if k in task}})
    coords=base['variables'];params=base['parameters'];points=task['points'];items=task['requests']
    if not isinstance(points,dict) or not points or not all(isinstance(k,str) for k in points) or not isinstance(items,(list,tuple)) or not items:
        raise Unsupported('Expected coordinates, named points and geometric requests')
    raw=m.parse(task['function'],None,[*coords,*params]); names=list(params)
    for p in points.values():
        if isinstance(p,dict):
            if (set(p)!={'on_level'} or 'level' not in task or not isinstance(p['on_level'],(list,tuple)) or len(p['on_level'])!=len(coords)
                    or not all(isinstance(v,str) for v in p['on_level'])):
                raise Unsupported('An arbitrary level point needs independent coordinates and a source level')
            names.extend(p['on_level'])
    dummy='__field'
    while dummy in [*coords,*names]:dummy+='_'
    m.context({'variable':dummy,'parameters':[*coords,*names]})
    conditions=base['stated_conditions'];m.context({'variable':dummy,'parameters':params,'parameter_conditions':conditions})
    ctx=m.context({'variable':dummy,'parameters':names,'parameter_conditions':conditions})
    def scalar(x):
        v=m.parse(str(x),None,names)
        if not m.constant_defined(v,ctx):raise Unsupported('Undefined real coordinate, direction or level')
        return m.simplify(v)
    def vector(values):
        if not isinstance(values,(list,tuple)) or len(values)!=len(coords):raise Unsupported('Vector dimension mismatch')
        return tuple(map(scalar,values))
    def tidy(e):
        # After a domain check, source round-tripping folds powers with newly integral exponents.
        return m.simplify(m.parse(source(m.simplify(e)),None,names))
    def norm(a):return m.simplify(('sqrt',m.dot(a,a)))
    def unit(a):
        length=norm(a)
        if not m.nonzero(length,ctx):raise Unsupported('A unit direction needs a proved nonzero norm')
        return tuple(m.div(x,length) for x in a)
    level=scalar(task['level']) if 'level' in task else None
    evaluated={};values=[]
    def derivative(role,expr,v,p):
        child=request(role,{'kind':'derivative_at','function':source(expr),'variable':v,'point':source(p),
                            'parameters':names,'stated_conditions':conditions})
        return tidy(freeze(child['value']))
    def gradient(label):
        if label in evaluated:return evaluated[label]['gradient']
        p=points[label];generic=isinstance(p,dict);pt=vector(p['on_level'] if generic else p)
        sub=dict(zip((('s',v) for v in coords),pt));at=m.substitute(raw,sub)
        if not m.constant_defined(at,ctx) or not all(known_guard((r,m.substitute(e,sub)),ctx) for r,e in domain_conditions(raw,True)):
            raise Unsupported('Smoothness on an open neighborhood of the source point is unresolved')
        value=tidy(at)
        if level is not None and not generic and not same_value(value,level):raise Unsupported('The point does not satisfy the source level equation')
        grad=tuple(derivative(label+'/'+v,m.substitute(raw,{k:a for k,a in sub.items() if k!=('s',v)}),v,pt[i]) for i,v in enumerate(coords))
        evaluated[label]={'point':pt,'field_value':value,'on_source_level':generic,'gradient':grad}
        return grad
    for item in items:
        op=item['op'];label=item['at'];keys={'op','at'}
        if op=='directional_derivative':keys.add('direction')
        if op=='gradient_angle':keys.add('other')
        if set(item)!=keys:raise Unsupported('Changed geometric output or direction')
        grad=gradient(label);rec=evaluated[label];pt=rec['point']
        if op=='gradient':val=grad
        elif op=='gradient_norm':val=norm(grad)
        elif op=='gradient_direction':val=unit(grad)
        elif op=='gradient_angle':val=('acos',m.dot(unit(grad),unit(gradient(item['other']))))
        elif op=='directional_derivative':
            d=item['direction']
            if isinstance(d,dict):
                if set(d)!={'curve','parameter','at'} or not isinstance(d['curve'],(list,tuple)) or len(d['curve'])!=len(coords):raise Unsupported('Invalid directed parametric tangent')
                t=d['parameter'];a=scalar(d['at']);m.context({'variable':t,'parameters':[*coords,*names]})
                curve=[m.parse(s,t,names) for s in d['curve']]
                position=[m.substitute(e,{('v',t):a}) for e in curve]
                if not all(m.constant_defined(v,ctx) and same_value(tidy(v),p) for v,p in zip(position,pt)):raise Unsupported('The curve misses the stated point')
                direction=tuple(derivative(label+'/curve/'+v,e,t,a) for v,e in zip(coords,curve))
            else:direction=vector(d)
            val=m.dot(grad,unit(direction))
        elif op=='tangent_plane_and_normal':
            if len(coords)!=3 or level is None:raise Unsupported('A surface in three dimensions and its level are required')
            constant=m.dot(grad,pt);regular=any(m.nonzero(v,ctx) for v in grad)
            if rec['on_source_level'] and rec['field_value']!=ZERO:
                # A certified Euler identity <grad F,p> = k F(p) proves regularity at a nonzero level.
                degree=m.simplify(m.div(constant,rec['field_value']))
                if m.num(degree) is not None and same_value(constant,m.mul(degree,rec['field_value'])):
                    constant=m.mul(degree,level);regular=regular or m.nonzero(constant,ctx)
            if not regular:raise Unsupported('A regular level point has not been proved')
            val={'normal':grad,'through':pt,'plane_constant':constant}
        else:raise Unsupported('Unknown geometric quantity')
        values.append(val)
    if set(points)!=set(evaluated):raise Unsupported('Some declared source points have no geometric request')
    return {'variables':coords,'field':raw,'level':level,'points':evaluated,'smooth_guards':domain_conditions(raw,True)},tuple(values)


def parametric_curve_derivatives(task,library,request):
    """Differentiate a local graph through its regular horizontal coordinate."""
    from verify import same_value
    if 'point' in task:
        if not library.data.get('parametric_corner_quotient'):raise Unsupported('Нет проверки разностного отношения в угловой точке')
        return parametric_corner(task,request)
    fields={'kind','id','source','coordinates','parameter','orders','parameters','stated_conditions','requested_output'}
    t=task['parameter'];params=task.get('parameters',[]);orders=task['orders'];xy=task['coordinates']
    cap=library.data.get('partial_bundle_contract',{}).get('selected_path_limits',{}).get('length',0)
    if (not library.data.get('parametric_graph_derivatives') or set(task)-fields or task['requested_output']!=['derivatives_as_functions_of_parameter']
        or not isinstance(params,(tuple,list)) or not all(isinstance(p,str) for p in params)
        or not isinstance(xy,(tuple,list)) or len(xy)!=2 or not isinstance(orders,(tuple,list)) or not orders
        or any(type(n)!=int or not 1<=n<=cap for n in orders) or len(set(orders))!=len(orders)):
        raise Unsupported('Uncovered parameterization, derivative orders or requested results')
    conditions=task.get('stated_conditions',[]);names=[t,*params];dummy='__curve'
    while dummy in names:dummy+='_'
    raw=tuple(m.parse(s,None,names) for s in xy)
    domain=tuple(dict.fromkeys(g for e in raw for g in domain_conditions(e)))
    source_conditions=[*conditions,*(guard_source(g) for g in entailed_domain_guards(domain))]
    ctx=m.context(dict(variable=dummy,parameters=names,parameter_conditions=source_conditions))
    def derivative(role,f,conditions):
        sub=dict(kind='partial_derivatives',function=source(f),variables=[t],parameters=params,
                 stated_conditions=conditions,requested_output=['first_partial_derivatives'])
        return freeze(request(role,sub)['value'][0])
    dx=derivative('horizontal velocity',raw[0],source_conditions)
    plan=dict(coordinates=raw,natural_domain=domain,horizontal_velocity=dx)
    if dx==ZERO:return plan,dict(regular_domain='empty',reason='locally constant horizontal coordinate')
    dy=derivative('vertical velocity',raw[1],source_conditions)
    if library.data.get('parametric_polynomial_pullback') and not domain:
        # Solve the coefficient equations of Y(t) = P(X(t)). A strictly monotone
        # monomial horizontal chart includes its stationary center in the graph.
        p,d=m.rational_form(raw[0]);r,s=m.rational_form(raw[1]);atom=('s',t)
        if d==s=={():1} and len(p)==1:
            mon,coefficient=next(iter(p.items()))
            if len(mon)==1 and mon[0][0]==atom and mon[0][1]%2 and mon[0][1]>=3 and coefficient:
                degree=mon[0][1]
                if all(not k or len(k)==1 and k[0][0]==atom and k[0][1]%degree==0 for k in r):
                    powers={k[0][1]//degree if k else 0:c for k,c in r.items()}
                    coeffs=[powers.get(i,0)/coefficient**i for i in range(max(powers,default=0)+1)]
                    result=[]
                    for order in orders:
                        c=list(coeffs)
                        for _ in range(order):c=[i*v for i,v in enumerate(c) if i] or [0]
                        result.append(m.dot(list(map(q,c)),[m.power(raw[0],i) for i in range(len(c))]))
                    plan.update(polynomial_in_horizontal_coordinate=[q(v) for v in coeffs],odd_chart_degree=degree,
                                vertical_velocity=dy,applied_methods=['method.parametric_polynomial_pullback'])
                    return plan,dict(regular_domain=domain,ordered_values=tuple(result),zero_horizontal_velocity='polynomial_extension')
    def strip_nonzero(e):
        top,_=m.rational_form(e)
        factors={a:k for a,k in m.common_mon(top).items() if m.nonzero(a,ctx)}
        return m.poly_expr({tuple((a,k-factors.get(a,0)) for a,k in mon if k!=factors.get(a,0)):c for mon,c in top.items()})
    def rank_pair(u,v):
        for expr in (u,v,m.add(u,v),m.dot((u,v),(u,v))):
            if known_guard(('nonzero',expr),ctx):return expr
        p,r=[m.trig_reduce(m.rational_form(m.power(e,2))[0],complete=True) for e in (u,v)]
        mon=next((z for z in p if z and z in r),None)
        if mon:
            scale=-p[mon]/r[mon];w=m.poly_expr(m.addp(p,{z:scale*c for z,c in r.items()}))
            if known_guard(('nonzero',w),ctx):return w
    u,v=map(strip_nonzero,(dx,dy))
    rank=rank_pair(u,v);stationary='nonzero_vertical_velocity';fold=[]
    if rank is None:
        for name in params:
            atom=('s',name)
            if m.nonzero(atom,ctx) or not m.common_mon(m.rational_form(dx)[0]).get(atom):continue
            if m.simplify(m.substitute(dx,{atom:ZERO}))==ZERO:
                child=request('nonzero parameter '+name,{**task,'stated_conditions':[*conditions,name+'!=0']})
                return plan,dict(split_parameter=name,nonzero=child['value'],zero={'regular_domain':'empty','reason':'locally constant horizontal coordinate'})
        ddx=derivative('horizontal acceleration at possible stationary parameters',dx,source_conditions)
        if (w:=rank_pair(u,strip_nonzero(ddx))) is not None:
            stationary='one_sided_branches_at_a_strict_coordinate_extremum';rank=w
        elif any(v!=ZERO and m.constant_defined(r:=m.div(ddx,v),ctx) and same_value(ddx,m.mul(r,v)) for v in (dx,dy)):
            ddy=derivative('vertical acceleration at possible stationary parameters',dy,source_conditions)
            rank=next((e for e in (ddy,m.add(ddy,dx),m.add(ddy,dy),m.add(ddy,m.neg(dx)),m.add(ddy,m.neg(dy))) if known_guard(('nonzero',e),ctx)),None)
            plan['vertical_acceleration']=ddy;stationary='vertical_displacement_of_lower_order_than_horizontal'
        if rank is None:raise Unsupported('Simultaneous stationary parameter values need a separate local graph argument')
        plan['horizontal_acceleration']=ddx
    regular=('nonzero',dx);scope=source_conditions+[guard_source(g) for g in entailed_domain_guards([regular,('nonzero',u)])]
    ctx_regular=m.context(dict(variable=dummy,parameters=names,parameter_conditions=scope))
    result={}
    for j in range(1,max(orders)+1):
        d=dy if j==1 else derivative('parameter derivative of order '+str(j-1)+' graph derivative',z,scope)
        z=m.div(d,dx)
        if stationary=='one_sided_branches_at_a_strict_coordinate_extremum':
            if fold and fold[-1] is None:fold.append(None)
            elif m.constant_defined(z,ctx) and all(known_guard(g,ctx) for g in domain_conditions(z,True)):fold.append(z)
            elif m.constant_defined(d,ctx) and rank_pair(u,strip_nonzero(d)) is not None:fold.append(None)
            else:raise Unsupported('One-sided derivatives at a turning point remain unclassified')
        if not all(known_guard(g,ctx_regular) for g in domain_conditions(z)):
            z=('div',d,dx)
        if j in orders:result[j]=z
    plan.update(vertical_velocity=dy,normalized_velocity=(u,v),nonzero_rank_witness=rank)
    return plan,dict(regular_domain=(*domain,regular),ordered_values=tuple(result[j] for j in orders),
                     zero_horizontal_velocity=stationary,**({'one_sided_at_turn':tuple(fold[j-1] for j in orders)} if fold else {}))


def parametric_corner(task,request):
    """Use the graph difference quotient on both sides of a piecewise affine chart."""
    from polynomial import rf,NotRational,pdiv
    from operations import expression_positions
    from verify import same_value
    fields={'kind','id','source','coordinates','parameter','point','orders','requested_output'}
    origin=task.get('source',{})
    output=['derivative_at_parameter_point','prove_regular_parameter_rule_inapplicable']
    printed='Show differentiability at t=0 despite failure of the usual parametric quotient formula.'
    if (set(task)-fields or task.get('orders')!=[1] or task.get('requested_output')!=output
            or set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','page_png_sha256','literal_requirement'}
            or origin.get('literal_requirement') not in (None,printed)
            or origin.get('literal_requirement')==printed and (task['parameter']!='t' or str(task['point'])!='0')):
        raise Unsupported('The source point, derivative order or proof obligation was changed')
    t=task['parameter'];v=('v',t);ctx=m.context(dict(variable=t))
    horizontal,vertical=(m.parse(z,t) for z in task['coordinates'])
    point=m.parse(str(task['point']),None)
    at=lambda e:m.substitute(e,{v:point})
    a,b=map(at,(horizontal,vertical))
    if not all(m.constant_defined(z,ctx) for z in (point,a,b)):raise Unsupported('Undefined parameter point on the original curve')
    atom_slopes={};axes=[horizontal,vertical]
    def affine(e):
        try:p,d=rf(e,t)
        except NotRational as exc:raise Unsupported('Need an affine real argument') from exc
        if len(p)>2 or len(d)!=1 or domain_conditions(e):raise Unsupported('Need an affine real argument')
        return p[1]/d[0] if len(p)==2 else 0
    for _,node in (pair for axis in axes for pair in expression_positions(axis)):
        if node[0]!='abs':continue
        atom_slopes[node]=affine(node[1])
    branches=[];values=[]
    quotient=('div',('add',vertical,('mul',q(-1),b)),('add',horizontal,('mul',q(-1),a)))
    for orientation,side in ((-1,'left'),(1,'right')):
        substitutions={}
        for node,slope in atom_slopes.items():
            s=m.sign(at(node[1]),ctx)
            if s is None:raise Unsupported('Unknown sign of an affine argument at the source point')
            if not s:s=orientation*((slope>0)-(slope<0))
            substitutions[node]=m.mul(q(s),node[1])
        branch=m.substitute(horizontal,substitutions)
        slope=affine(branch)
        if not slope or not same_value(at(branch),a):
            raise Unsupported('Need two continuous affine horizontal branches with nonzero slopes')
        local=m.substitute(quotient,substitutions)
        try:coeff,den=rf(local,t)
        except NotRational:coeff=den=()
        base=m.num(point)
        if base is not None and len(den)==2 and not real_intervals.peval(den,base) and not domain_conditions(m.substitute(vertical,substitutions)):
            polynomial,remainder=pdiv(coeff,den)
            if any(remainder):raise Unsupported('The ordinate has not been shown continuous at the join')
            value=q(real_intervals.peval(polynomial,base))
        else:
            proof=request('graph difference quotient from '+side,dict(kind='limit',variable=t,
                          expression=source(local),approach=dict(point=source(point),side=side)))
            value=freeze(proof['value'])
        if isinstance(value,str):raise Unsupported('The graph slope must be finite')
        branches.append((side,branch,q(slope),local));values.append(value)
    sl,sr=(m.num(z[2]) for z in branches)
    if sl*sr<=0 or sl==sr or not same_value(*values):
        raise Unsupported('The graph chart must be monotone with different velocities and matching graph quotients')
    return dict(original_coordinates=(horizontal,vertical),parameter=t,parameter_point=point,graph_point=(a,b),
                horizontal_branches=branches,difference_quotient=quotient,applied_methods=['method.parametric_corner_quotient']),dict(
                derivative_at_parameter_point=values[0],regular_parameter_rule_inapplicable=True)


def integer_step_derivative(task,library,request):
    """Differentiate a step factor on its smooth intervals, then match the zero jets at all jumps."""
    from polynomial import rf,NotRational
    from verify import same_value
    fields={'kind','id','schema','source','transcription','function','variable','parameters','stated_conditions',
            'method_requirement','requested_output','required_functions'}
    output=['finite_derivative','natural_domain_and_boundary_notes']
    origin=task.get('source',{})
    if (not library.data.get('integer_step_jet') or set(task)-fields or task.get('parameters') or task.get('stated_conditions')
            or task.get('requested_output')!=output or task.get('method_requirement')!='table_and_rules'
            or task.get('required_functions',['floor'])!=['floor']
            or set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256'}):
        raise Unsupported('Unresolved step-function source conditions')
    x=task['variable'];raw=m.parse(task['function'],x,extra_functions={'floor'})
    if raw[0]!='mul' or sum(e[0]=='floor' for e in raw[1:])!=1:
        raise Unsupported('One affine integer-part factor must multiply the smooth envelope')
    step,envelope=raw[1:] if raw[1][0]=='floor' else raw[:0:-1]
    try:p,d=rf(step[1],x)
    except NotRational as exc:raise Unsupported('The integer levels need a continuous affine chart') from exc
    if len(p)!=2 or len(d)!=1 or domain_conditions(step[1]):raise Unsupported('The integer levels need a continuous affine chart')
    if envelope[0]!='pow' or envelope[2]<2 or envelope[1][0]!='sin':
        raise Unsupported('The smooth envelope needs at least a double zero at each integer level')
    phase=envelope[1][1];affine=tuple(q(c/d[0]) for c in p)
    period=m.mul(m.PI,step[1]);ratio=m.num(m.simplify(m.div(phase,period)))
    if (not ratio or ratio.denominator!=1 or domain_conditions(phase)
            or not same_value(phase,m.mul(q(ratio),period))):
        raise Unsupported('The zeros of the envelope are not bound to all the integer levels')
    child=request('derivative of the smooth envelope',dict(kind='differentiate',function=source(envelope),variable=x,method_requirement='table_and_rules'))
    derivative=('mul',step,freeze(child['value']))
    return dict(original_expression=raw,affine_chart=affine,integer_phase_multiple=int(ratio),vanishing_order=envelope[2],
                applied_methods=['method.integer_step_jet']),dict(derivative=derivative,natural_domain='real_line',
                  on_integer_levels=ZERO,elsewhere=derivative)

def tangent_geometry(task,library,request):
    """Regular images and transverse level sets in three-dimensional Euclidean space."""
    from verify import same_value
    fields={'kind','id','schema','source','transcription','coordinates','parameters','stated_conditions','parametrization','point','level_sets','requested_output'}
    xyz=task['coordinates'];params=task.get('parameters',[]);conditions=task.get('stated_conditions',[]);chart=task.get('parametrization')
    if (set(task)-fields or not isinstance(xyz,(list,tuple)) or len(xyz)!=3 or ('level_sets' in task)==('parametrization' in task)
            or library.data.get('task_compilers',{}).get('tangent_geometry')!='regular_image_or_level_intersection'):
        raise Unsupported('Expected one real three-dimensional tangent problem')
    if not isinstance(params,(list,tuple)) or not all(isinstance(p,str) for p in [*xyz,*params]):
        raise Unsupported('Expected real coordinate and constant names')
    dummy='__tangent'
    while dummy in [*xyz,*params]:dummy+='_'
    m.context({'variable':dummy,'parameters':[*xyz,*params]})
    ctx=m.context({'variable':dummy,'parameters':params,'parameter_conditions':conditions})
    def field(role,f,variables,point,extra):
        spec={'kind':'scalar_field_geometry','function':f,'variables':variables,'points':{'P':point},'parameters':params,
              'stated_conditions':conditions,'requests':[{'op':'gradient','at':'P'}],**extra}
        return request(role,spec)['compilation']['points']['P']
    def cross(a,b):
        return tuple(m.add(m.mul(a[i],b[j]),m.neg(m.mul(a[j],b[i]))) for i,j in ((1,2),(2,0),(0,1)))
    if chart is not None:
        if (not isinstance(chart,dict) or set(chart)!={'variables','map','at'} or not isinstance(chart['map'],(list,tuple)) or len(chart['map'])!=3
                or not isinstance(chart['variables'],(list,tuple)) or len(chart['variables']) not in (1,2)):
            raise Unsupported('Expected a curve or a surface chart')
        variables=chart['variables'];dimension=len(variables);raw=[m.parse(f,None,[*params,*variables]) for f in chart['map']]
        components=[field('coordinate/'+v,f,variables,chart['at'],{}) for v,f in zip(xyz,chart['map'])]
        p=tuple(freeze(c['field_value']) for c in components);rows=tuple(zip(*(freeze(c['gradient']) for c in components)))
        v=rows[0] if dimension==1 else cross(*rows)
        if 'point' in task:
            given=task['point']
            if not isinstance(given,(list,tuple)) or len(given)!=3:raise Unsupported('Invalid stated chart point')
            exact=[m.parse(str(s),None,params) for s in given]
            if not all(m.constant_defined(s,ctx) and same_value(s,x) for s,x in zip(exact,p)):raise Unsupported('Chart misses the given point')
    else:
        ls=task['level_sets']
        if not isinstance(ls,(list,tuple)) or len(ls)!=2 or any(set(s)!={'function','level'} for s in ls):
            raise Unsupported('A space curve requires two explicit transverse level equations')
        components=[field('level/'+str(i+1),s['function'],xyz,task['point'],{'level':s['level']}) for i,s in enumerate(ls)]
        p=freeze(components[0]['point']);rows=tuple(freeze(c['gradient']) for c in components);v=cross(*rows);dimension=1
    output='tangent_line_and_normal_plane' if dimension==1 else 'tangent_plane_and_normal_line'
    if task['requested_output']!=[output]:raise Unsupported('Uncovered tangent obligation')
    norm2=m.dot(v,v);regular={'line_direction':v,'through':p,'plane_constant':m.dot(v,p)}
    plan={'dimension':dimension,'derivative_vectors':rows,'squared_rank_witness':norm2,'point':p}
    if m.nonzero(norm2,ctx) or any(m.nonzero(c,ctx) for c in v):return plan,regular
    if chart is not None and dimension==1 and norm2[0]=='pow' and norm2[1][0]=='s' and norm2[2]>0:
        # The zero branch is complete only if the local image itself collapses to a point.
        symbol=norm2[1];zero={symbol:ZERO}
        if all(m.constant_defined(m.simplify(m.substitute(e,zero)),ctx) for e in raw):
            return plan,{'split_parameter':symbol[1],'nonzero':regular,'zero':{'constant_image':tuple(m.simplify(m.substitute(e,zero)) for e in raw)}}
    raise Unsupported('Rank is not established on the whole source domain; singular chart or level intersection needs a separate argument')


def implicit_derivative(task,library,request):
    """In each differentiated composition F(x,z(x)), isolate its top derivative F_z D^I z."""
    from collections import Counter
    from functools import lru_cache
    from itertools import product
    from verify import same_value
    if 'source_formula' in task and library.data.get('printed_implicit_graph'):
        from cartesian_fields import implicit_graph_request
        indexed=implicit_graph_request(task)
        plan,values=implicit_derivative(indexed,library,request)
        plan['requested_paths']=list(zip(task['requested_output'],indexed['requested_partials']))
        return plan,values
    fields={'kind','id','source','relation','independent','dependent','parameters','stated_conditions','graph_conditions','point','scope','requested_partials','differential_orders','requested_output'}
    xs=task['independent'];z=task['dependent'];pars=task.get('parameters',[]);conds=task.get('stated_conditions',[])
    paths=task.get('requested_partials',[]);orders=task.get('differential_orders',[]);at='point' in task
    if (set(task)-fields or library.data.get('task_compilers',{}).get(task['kind'])!='differentiate_on_regular_graph'
            or not all(isinstance(v,(list,tuple)) for v in (xs,pars,conds,paths,orders)) or not xs or bool(paths)==bool(orders)
            or not all(isinstance(s,str) for s in [*xs,z,*pars,*conds]) or ('scope' in task)==at
            or not at and task['scope']!='regular_graph' or task['requested_output']!=(['total_differentials'] if orders else ['specified_implicit_derivatives'])):
        raise Unsupported('Expected one implicit scalar graph and explicit requested partials')
    limit=library.data['partial_bundle_contract']['selected_path_limits']
    if orders and (any(type(o) is not int or not 1<=o<=limit['length'] for o in orders) or sum(len(xs)**o for o in orders)>limit['count']):
        raise Unsupported('Requested total differential exceeds the recorded partial bundle size')
    if len(paths)>limit['count'] or any(not isinstance(p,(list,tuple)) or not 1<=len(p)<=limit['length'] or any(x not in xs for x in p) for p in paths):
        raise Unsupported('Unknown partial index, independent variable or derivative order')
    names=[*xs,z,*pars];dummy='__graph'
    while dummy in names:dummy+='_'
    def context(symbols,guards):return m.context({'variable':dummy,'parameters':symbols,'parameter_conditions':guards})
    fixed=context(pars,conds)
    f=m.parse(task['relation'],None,names)
    guards=domain_conditions(f,True)
    for condition in task.get('graph_conditions',[]):
        match=re.fullmatch(r'(.+?)(!=|>)0',condition)
        if not match:raise Unsupported('A local graph condition must describe an open set')
        e=m.parse(match[1],None,names);guards.extend(domain_conditions(e));guards.append(('positive' if match[2]=='>' else 'nonzero',e))
    admitted=list(conds)+[guard_source(g) for g in entailed_domain_guards(guards)]
    whole=context(names,admitted)
    subs={}
    if at:
        pt=task['point']
        if not isinstance(pt,dict) or set(pt)!=set([*xs,z]):raise Unsupported('A point needs all graph coordinates')
        subs={('s',v):m.parse(str(a),None,pars) for v,a in pt.items()}
        if not all(m.constant_defined(a,fixed) for a in subs.values()) or not all(known_guard((r,m.substitute(g,subs)),fixed) for r,g in guards):
            raise Unsupported('The original relation is not defined and smooth at this point')
        if not same_value(m.substitute(f,subs),ZERO):raise Unsupported('The point does not satisfy the original equation')
    @lru_cache(None)
    def ambient(path):
        if not path:return f
        v=path[-1];expr=ambient(path[:-1])
        if not m.variable_in(m.substitute(expr,{('s',v):('v',v)}),v):return ZERO
        child=request('partial/'+'/'.join(path),{'kind':'differentiate','function':source(expr),'variable':v,
                      'parameters':[w for w in names if w!=v],'stated_conditions':list(admitted),'method_requirement':'table_and_rules'})
        value=m.substitute(freeze(child['value']),{('v',v):('s',v)})
        if not all(known_guard((r,m.substitute(g,subs)),fixed) if at else known_guard((r,g),whole) for r,g in domain_conditions(value)):
            raise Unsupported('An ambient partial has an extra domain restriction on the source graph')
        return value
    pivot=ambient((z,))
    def local(value):return m.simplify(m.substitute(value,subs)) if at else value
    pivot_value=local(pivot)
    if same_value(pivot_value,ZERO) or at and not m.nonzero(pivot_value,fixed):
        raise Unsupported('The dependent derivative is not proved nonzero on the selected branch')
    admitted.append(guard_source(('nonzero',pivot)));whole=context(names,admitted)
    def insert(items,item):return tuple(sorted((*items,item)))
    @lru_cache(None)
    def composition(path):
        # Each key denotes one partial of F times a product of partials of z.
        if not path:return {((),()):1}
        terms=Counter();direction=path[-1]
        for (index,factors),count in composition(path[:-1]).items():
            terms[insert(index,direction),factors]+=count
            terms[insert(index,z),insert(factors,(direction,))]+=count
            for i,factor in enumerate(factors):
                others=factors[:i]+factors[i+1:]
                terms[index,insert(others,insert(factor,direction))]+=count
        return terms
    @lru_cache(None)
    def along(path):
        rest=ZERO
        for (index,factors),count in composition(path).items():
            if index==(z,) and factors==(path,):continue
            coeff=local(ambient(index))
            if coeff==ZERO:continue
            term=m.mul(q(count),coeff)
            for factor in factors:term=m.mul(term,along(factor))
            rest=m.add(rest,term)
        return m.simplify(m.div(m.neg(rest),pivot_value))
    increments={}
    if orders:
        for x in xs:
            name='d'+x
            while name in names or name in increments.values():name+='_'
            increments[x]=name
        values=[]
        for order in orders:
            total=ZERO
            for p in product(xs,repeat=order):
                term=along(tuple(sorted(p)))
                for v in p:term=m.mul(term,('s',increments[v]))
                total=m.add(total,term)
            values.append(total)
    else:values=[along(tuple(sorted(p))) for p in paths]
    return {'relation':f,'pivot':pivot,'smooth_guards':guards,'regular_graph_condition':('nonzero',pivot),
            'differential_increments':increments,
            'scope':'verified source point' if at else 'formula conditional on the original regular graph'},tuple(values)


def successive_composition(task,library,request):
    """Substitute the Taylor polynomials of arbitrary curves and identify the requested derivative coefficients."""
    from math import factorial
    if not library.data.get('successive_taylor_composition'):raise Unsupported('Successive Taylor composition is not admitted')
    fields={'kind','id','source','variables','parameters','stated_conditions','requested_output'}
    origin=task.get('source',{})
    if set(origin)-{'exercise','pdf_page','printed_page','pdf_sha256','page_png_sha256','literal_requirement'}:
        raise Unsupported('Unbound source condition in the composition')
    literal=origin.get('literal_requirement','').replace('φ','phi').replace('ψ','psi')
    xs=task.get('variables');pars=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    outputs=task.get('requested_output')
    if (not isinstance(xs,(list,tuple)) or len(xs)!=1 or not isinstance(pars,(list,tuple))
            or not all(isinstance(s,str) for s in [*xs,*pars]) or not isinstance(conditions,list)):
        raise Unsupported('One independent real coordinate is required')
    x,=xs
    t='__step'
    args=list(pars); meanings={};conditions=list(conditions);degree=2
    def symbol(name,meaning):
        if name in args or name in (x,t):raise Unsupported('Taylor symbols must be distinct on the source domain')
        args.append(name);meanings[name]=meaning
        return ('s',name)
    def jet(name,degree,meaning,differential,include_value=True):
        result=('s',name) if include_value else ZERO
        for k in range(1,degree+1):
            prefix='d' if k==1 else f'd{k}'
            label=prefix+name if differential else f'{name}_{k}'
            term=symbol(label,dict(function=meaning,order=k,differential=differential))
            result=m.add(result,m.mul(m.div(term,q(factorial(k))),m.power(('v',t),k)))
        return result
    if 'outer_expression' in task:
        fields.update({'outer_expression','inner_arguments','inner_regularities','inner_function','order'})
        outer=task['outer_expression'];inputs=task.get('inner_arguments')
        regularity=task.get('inner_regularities',{})
        if 'inner_function' in task:
            mfun=re.fullmatch(r'([A-Za-z_]\w*)\('+re.escape(x)+r'\)',task['inner_function'])
            if (inputs is not None or not mfun or regularity or outputs!=['successive_differential']
                    or type(task.get('order'))!=int):
                raise Unsupported('Unbound formal inner function or differential order')
            name=mfun[1];inputs={name:task['inner_function']};degree=task['order']
            texts=[f'Find the indicated successive differential with {name} an arbitrary sufficiently differentiable function of {x}.']
        elif not isinstance(inputs,dict) or not inputs or outputs not in (['second_derivative'],['second_differential'],['second_differential_in_dx_and_d2x']):
            raise Unsupported('Unknown order or dependent functions')
        else:
            texts=[]
            label=' и '.join(inputs)
            rhs=' для y='+outer
            if outputs==['second_derivative']:
                signature=' и '.join(f'{u}={f}' for u,f in inputs.items())
                suffix=' при '+' и '.join(conditions) if conditions else ''
                texts=[f'Пусть {signature} дважды дифференцируемы. Найти y″'+rhs+suffix+'.']
            elif outputs==['second_differential']:
                prefix=f'Пусть {label} — дважды дифференцируемые функции переменной {x}. Найти d²y'+rhs
                texts=[prefix+'.',prefix+' ('+' и '.join(conditions)+').',prefix+' ('+' и '.join(pars)+' постоянные).']
            elif len(inputs)==1:
                u,=inputs
                texts=[f'Найти d²y для y={outer}, когда {u} — промежуточный аргумент.',
                       f'Найти d²y для y=e^{u}, когда {u} — промежуточный аргумент.' if outer==f'exp({u})' else '']
        if set(task)-fields or not 1<=degree<=32 or literal and literal not in texts:
            raise Unsupported('Printed request and typed composition are inconsistent')
        inner={}
        for u,f in inputs.items():
            call=re.fullmatch(r'([A-Za-z_]\w*)\('+re.escape(x)+r'\)',f)
            if not call or not re.fullmatch(r'[A-Za-z_]\w*',u) or (regularity and regularity.get(call[1],0)<degree):
                raise Unsupported('An inner derivative is not available through the requested order')
            inner[u]=call[1]
        if ('inner_regularities' in task or outputs in (['second_derivative'],['second_differential'])) and set(regularity)!=set(inner.values()):
            raise Unsupported('Unresolved inner regularity assumption')
        differential=outputs!=['second_derivative'];orders=[degree]
        for u in inner:symbol(u,dict(function=inputs[u],order=0))
        raw=m.parse(outer,None,args);domain=domain_conditions(raw)
        ctx=m.context(dict(variable=t,parameters=args,parameter_conditions=conditions+[guard_source(g) for g in entailed_domain_guards(domain)]))
        if not all(known_guard(g,ctx) for g in domain_conditions(raw,smooth=True)):
            raise Unsupported('The outer function can be nonsmooth at an admissible inner value')
        if any(q0[0]=='rpow' and q0[1][0]=='s' and q0[1][1] in inner and q0[2][0]=='s' and q0[2][1] in pars
               and not known_guard(('positive',q0[1]),m.context(dict(variable=t,parameters=args,parameter_conditions=conditions)))
               for _,q0 in expression_positions(raw)):
            raise Unsupported('Exceptional real parameter powers require separate domain cases')
        ray=m.substitute(raw,{('s',u):jet(u,degree,inputs[u],differential) for u in inner})
    else:
        fields.update({'outer_function','outer_differentiability_order','inner_arguments'})
        outer=task.get('outer_function');arguments=task.get('inner_arguments',[])
        if (set(task)-fields or not isinstance(outer,str) or not re.fullmatch(r'[A-Za-z_]\w*',outer)
                or outputs!=['second_derivative','third_derivative'] or len(arguments)!=1 or task.get('outer_differentiability_order')!=3):
            raise Unsupported('Unbound regularity or requested order of the outer function')
        degree=3;orders=[2,3];differential=False
        arg=arguments[0];call=re.fullmatch(r'([A-Za-z_]\w*)\('+re.escape(x)+r'\)',arg)
        abstract=call and call[1] not in m.FUNCTIONS|set(m.ALIASES)
        expected=f'Пусть {outer} трижды дифференцируема. Найти y″ и y‴ для y={outer}({arg}).'
        if abstract:expected+=f' {call[1]} дифференцируема достаточное число раз.'
        if literal and literal!=expected:raise Unsupported('Printed composition or regularity differs from the goal')
        args.append(x)
        if abstract:
            if conditions!=[call[1]+' is sufficiently differentiable']:raise Unsupported('The required inner derivatives are not given')
            conditions=[];domain=[]
            delta=jet(call[1],degree,arg,False,False)
        else:
            raw=m.parse(arg,None,args);domain=domain_conditions(raw)
            ctx=m.context(dict(variable=t,parameters=args,parameter_conditions=conditions+[guard_source(g) for g in entailed_domain_guards(domain)]))
            if not all(known_guard(g,ctx) for g in domain_conditions(raw,smooth=True)):raise Unsupported('The inner function has unresolved boundary derivatives')
            shifted=m.substitute(raw,{('s',x):m.add(('s',x),('v',t))})
            delta=('add',shifted,('mul',q(-1),raw))
        ray=ZERO
        for k in range(1,degree+1):
            fk=symbol(f'{outer}_{k}',dict(function=outer,at=arg,order=k))
            ray=m.add(ray,m.mul(m.div(fk,q(factorial(k))),m.power(delta,k)))
    guards=conditions+[guard_source(g) for g in entailed_domain_guards(domain)]
    child=dict(kind='finite_expansion',expression=source(ray),variable=t,parameters=args,parameter_conditions=guards,
               approach={'point':'0','side':'both'},degree=degree,requested_output=['finite_power_expansion'])
    expansion=request('Taylor coefficients along an arbitrary inner curve',child)['value']
    return dict(order=degree,requested_orders=orders,independent_variable=x,symbols=meanings,natural_domain=domain,
                stated_conditions=conditions,differential=differential),tuple(m.mul(q(factorial(k)),freeze(expansion[k])) for k in orders)


def composite_differentiation(task, library, request):
    from itertools import product
    keys = {'id','source','kind','outer_function','variables','inner_arguments','requested_output'}
    if set(task)-keys or library.data.get('task_compilers',{}).get(task['kind'])!='ordered_outer_chain_rule':
        raise Unsupported('Unknown formal-composition fields or obligations')
    xs, arguments, output = task['variables'], task['inner_arguments'], task['requested_output']
    if (not isinstance(xs, (list, tuple)) or not xs or not isinstance(arguments, (list, tuple))
            or not arguments or not all(isinstance(s, str) for s in [*xs, *arguments])
            or not isinstance(output, (list, tuple)) or len(output) != 1
            or not isinstance(task['outer_function'], str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', task['outer_function'])):
        raise Unsupported('Expected a named outer field, coordinate list, inner arguments and one output type')
    output = output[0]
    path = None
    if isinstance(output,dict) and set(output)=={'ordered_partial'}:
        path = output['ordered_partial']
    elif output=='mixed_xy':
        path = ('x','y')
    elif output not in ('gradient_hessian','laplacian','d1_d2'):
        raise Unsupported('This first-and-second chain rule does not cover the original request')
    if path is not None and (not isinstance(path,(list,tuple)) or len(path)!=2 or any(x not in xs for x in path)):
        raise Unsupported('The ordered mixed partial references undefined coordinates')
    reserved = {*m.FUNCTIONS, *m.ALIASES, 'e', 'pi', 'min', 'max', 'lg'}
    if len(set(xs)) != len(xs) or set(xs) & reserved or task['outer_function'] in set(xs)|reserved:
        raise Unsupported('Coordinate or outer name collision')
    refs = {token[1] for expr in arguments for token in m.TOKEN.findall(expr) if token[1]}
    pars = sorted(refs - set(xs) - reserved)
    if task['outer_function'] in pars:raise Unsupported('A dependent outer function cannot be a fixed parameter')
    exprs = tuple(m.parse(a, None, [*xs,*pars]) for a in arguments)
    raw_guards = tuple(dict.fromkeys(g for expr in exprs for g in domain_conditions(expr)))
    guards = [guard_source(g) for g in entailed_domain_guards(raw_guards)]
    dummy = '__chain'
    while dummy in [*xs,*pars]:dummy += '_'
    ctx = m.context({'variable':dummy,'parameters':[*xs,*pars],'parameter_conditions':guards})
    if not all(known_guard(g, ctx) for expr in exprs for g in domain_conditions(expr, True)):
        raise Unsupported('Composition may have derivatives at a nonsmooth inner point; original boundary case remains open')

    grad, hess = [], []
    for i, arg in enumerate(arguments):
        child = request(f'inner[{i+1}]', dict(kind='partial_derivatives', function=arg, variables=xs,
                        parameters=pars, derivative_orders=[1,2], requested_output=['first_partial_derivatives','second_partial_derivatives']))
        partials = {tuple(path):freeze(val) for path,val in child['partial_values']}
        grad.append(tuple(partials[(x,)] for x in xs))
        hess.append(tuple(tuple(partials[(x,y)] for y in xs) for x in xs))

    # A form stores coefficients of ordered outer partials; every index refers to the same tuple of inner values.
    def coefficients(v, w=None):
        dv = [m.dot(row,v) for row in grad]
        if w is None:return {(i+1,):c for i,c in enumerate(dv)}
        dw = [m.dot(row,w) for row in grad]
        linear = {(i+1,):m.dot(v,[m.dot(row,w) for row in matrix]) for i,matrix in enumerate(hess)}
        quadratic = {(i+1,j+1):m.mul(a,b) for i,a in enumerate(dv) for j,b in enumerate(dw)}
        return {**linear, **quadratic}

    axes = [tuple(ONE if x==y else ZERO for y in xs) for x in xs]
    forms = {}
    increments = []
    if output == 'd1_d2':
        for x in xs:
            inc = 'd'+x
            while inc in [*xs,*pars,*increments,task['outer_function']]:inc += '_'
            increments.append(inc)
        vector = [('s',i) for i in increments]
        forms = {'d1':coefficients(vector), 'd2':coefficients(vector,vector)}
    elif output == 'gradient_hessian':
        for x,v in zip(xs,axes):forms['D '+x]=coefficients(v)
        for (x,v),(y,w) in product(zip(xs,axes),repeat=2):forms[f'D {x} {y}']=coefficients(v,w)
    elif path is not None:forms['D '+' '.join(path)]=coefficients(*(axes[xs.index(x)] for x in path))
    else:
        total = {}
        for v in axes:
            for path,c in coefficients(v,v).items():total[path]=m.add(total.get(path,ZERO),c)
        forms['laplacian']=total
    def packed(form):
        return [{'ordered_outer_partials':path,'coefficient':c} for path,c in sorted(form.items()) if c!=ZERO]
    return {'original_inner_domain':raw_guards,'outer_symbol':task['outer_function'],'outer_evaluation_arguments':exprs,
            'outer_differentiability_at_inner_image':{'required_for_paths':[(),*((i+1,) for i in range(len(arguments)))],
                                                       'scope':'twice Frechet differentiable at the image; the first outer differential is defined on a neighborhood of that image'},
            'mixed_order':'left-to-right; no exchange of mixed partials','increments':increments}, {name:packed(form) for name,form in forms.items()}


def sampled_field_taylor(task,library):
    """Taylor coefficients of a linear combination or compact angular mean of shifted smooth fields."""
    from fractions import Fraction
    from itertools import product
    from math import comb,factorial,prod
    fields={'kind','id','source','field','variables','increments','sampling','degree','regularity','requested_output'}
    xs=task['variables'];hs=task['increments'];field=task['field'];sampling=task['sampling'];degree=task.get('degree')
    regularity=task['regularity'];mode=task['requested_output'];finite=mode==['homogeneous_expansion_through_degree']
    if (library.data.get('task_compilers',{}).get(task['kind'])!='moments_of_translated_fields' or set(task)-fields or
        not isinstance(xs,(tuple,list)) or not isinstance(hs,(tuple,list)) or not xs or not hs or
        finite!=('degree' in task) or not finite and mode!=['all_taylor_coefficients'] or
        finite and (type(degree)!=int or degree<0) or regularity not in ('state_taylor_hypotheses','analytic_near_center')):
        raise Unsupported('Expected a Taylor coefficient request and its local regularity scope')
    m.context({'variable':field,'parameters':[*xs,*hs]})
    shifts=tuple(('s',h) for h in hs);dimension=len(xs);geometry=sampling['kind'];nodes=[]
    if geometry=='finite_linear_combination':
        if set(sampling)!={'kind','nodes'} or not sampling['nodes']:raise Unsupported('Missing shifts or extra measure conditions')
        for node in sampling['nodes']:
            matrix=node['offsets']
            if set(node)!={'weight','offsets'} or len(matrix)!=dimension or any(len(row)!=len(hs) for row in matrix):
                raise Unsupported('Each coordinate displacement must be linear in the declared increments')
            offset=[]
            for row in matrix:
                linear=ZERO
                for c,h in zip(row,shifts):linear=m.add(linear,m.mul(q(Fraction(str(c))),h))
                offset.append(linear)
            nodes.append((q(Fraction(str(node['weight']))),tuple(offset)))
        kernel={'method':'weighted_products','nodes':tuple(nodes)}
    else:
        circle=geometry=='uniform_circle'
        if (dimension!=2 or len(hs)!=1 or (not circle and geometry!='regular_polygon_vertices') or
                set(sampling)!=({'kind'} if circle else {'kind','vertices','first_direction'}) or
                not circle and (type(sampling['vertices'])!=int or sampling['vertices']<3 or sampling['first_direction']!=[1,0])):
            raise Unsupported('A normalized full circle or a regular polygon with its first radius along x is required')
        period=0 if circle else sampling['vertices']
        kernel={'method':'angular_frequency_average','frequency_multiple':period,'radius':shifts[0]}
    def coefficient(alpha):
        order=sum(alpha);denominator=prod(factorial(a) for a in alpha)
        if nodes:
            v=ZERO
            for weight,offset in nodes:
                term=weight
                for d,a in zip(offset,alpha):
                    if a:term=m.mul(term,m.power(d,a))
                v=m.add(v,term)
            return m.simplify(m.div(v,q(denominator)))
        p,r=alpha
        if r%2:return ZERO
        def survives(k):return k%period==0 if period else k==0
        moment=sum((-1)**j*comb(p,i)*comb(r,j) for i in range(p+1) for j in range(r+1) if survives(order-2*(i+j)))
        scale=q(Fraction((-1)**(r//2)*moment,2**order*denominator))
        return m.mul(scale,m.power(shifts[0],order)) if order else scale
    def indices(d,n):
        if d==1:yield (n,);return
        for j in range(n+1):
            for tail in indices(d-1,n-j):yield (j,*tail)
    result={'field':field,'variables':xs,'increments':hs,'coefficient_kernel':kernel}
    if finite:
        result['terms']=[{'orders':alpha,'coefficient':c} for j in range(degree+1) for alpha in indices(dimension,j)
                         if (c:=coefficient(alpha))!=ZERO]
        result.update(degree=degree,remainder='peano_in_increment_norm',requires_regular_derivatives=degree)
    elif nodes and len(hs)==dimension and all(z in (ZERO,h) for _,offset in nodes for h,z in zip(shifts,offset)):
        # Zero powers are one. The weight for a multi-index depends only on its positive coordinates.
        groups=[]
        for support in product((False,True),repeat=dimension):
            weight=sum(m.num(w) for w,ds in nodes if all(not positive or d!=ZERO for positive,d in zip(support,ds)))
            if weight:groups.append({'positive_coordinates':[x for x,s in zip(xs,support) if s],'weight':q(weight)})
        result['diagonal_support_weights']=groups
    elif geometry=='uniform_circle':
        result['circle_series']={'operator':'laplacian_power','factor':'radius^(2j)/(4^j*(j!)^2)','index':'j>=0'}
    if not finite:
        result['convergence']='convergent_for_analytic_field' if regularity=='analytic_near_center' else 'all_finite_jets_for_smooth_field; convergence_if_analytic'
    return {'geometry':geometry,'uniform_remainder':'bounded linear shifts; compact sampling directions'},result


def multivariate_taylor(task,library,request):
    """Use exact polynomial translation, or identify the multivariable Taylor jet on every line."""
    from math import factorial
    fields={'kind','id','source','expression','variables','center','increments','degree','parameters','stated_conditions','requested_output','requested_partials'}
    xs=task['variables'];inc=task['increments'];pars=task.get('parameters',[]);conds=task.get('stated_conditions',[])
    wants=task['requested_output'];at=task['center'];paths=task.get('requested_partials',[])
    finite=wants in (['finite_taylor_polynomial'],['finite_taylor_polynomial','specified_derivatives_at_center']);degree=task.get('degree')
    if (set(task)-fields or library.data.get('task_compilers',{}).get(task['kind'])!='translate_and_identify_homogeneous_terms'
            or not all(isinstance(z,(list,tuple)) for z in (xs,inc,pars,conds)) or not xs or len(xs)!=len(inc)
            or not all(isinstance(z,str) for z in [*xs,*inc,*pars,*conds]) or finite!=('degree' in task)
            or not isinstance(paths,(list,tuple)) or ('specified_derivatives_at_center' in wants)!=bool(paths)
            or finite and (type(degree) is not int or not 0<=degree<=24)
            or not finite and wants not in (['exact_shifted_polynomial'],['exact_increment'])):
        raise Unsupported('Unknown Taylor precision, variables, increments or requested output')
    dummy='__radial'
    while dummy in [*xs,*inc,*pars]:dummy+='_'
    def context(names):return m.context({'variable':dummy,'parameters':names,'parameter_conditions':conds})
    m.context({'variable':dummy,'parameters':[*xs,*inc,*pars]})
    fixed_names=[*pars,*xs] if at=='current_point' else list(pars)
    fixed=context(fixed_names);whole=context([*fixed_names,*inc])
    if at=='current_point':at={x:x for x in xs}
    if not isinstance(at,dict) or set(at)!=set(xs):raise Unsupported('The center must specify every original coordinate')
    center={('s',x):m.parse(str(at[x]),None,fixed_names) for x in xs}
    if not all(m.constant_defined(a,fixed) for a in center.values()):raise Unsupported('The center has an undefined coordinate')
    raw=m.parse(task['expression'],None,[*xs,*pars]);steps={('s',x):('s',h) for x,h in zip(xs,inc)}
    shifted=m.substitute(raw,{v:('add',a,steps[v]) for v,a in center.items()})
    guards=domain_conditions(raw,finite)
    local={v:a for v,a in center.items()} if finite else {v:('add',a,steps[v]) for v,a in center.items()}
    if not all(known_guard((r,m.substitute(e,local)),fixed if finite else whole) for r,e in guards):
        raise Unsupported('The original expression lacks the required smooth neighborhood or global domain')
    def homogeneous(expr):
        num,den=m.rational_form(expr);den=m.poly_expr(den);groups={}
        if not m.constant_defined(den,fixed) or not m.nonzero(den,fixed):raise Unsupported('Increment-dependent or vanishing denominator')
        for mon,c in num.items():
            d=0
            for atom,k in mon:
                if atom in steps.values():d+=k
                elif not m.constant_defined(atom,fixed):raise Unsupported('A coefficient is not polynomial in the coordinate increments')
            groups.setdefault(d,{})[mon]=c
        return {d:m.div(m.poly_expr(poly),den) for d,poly in groups.items()}
    point_value=m.simplify(m.substitute(raw,center))
    if finite:
        ray=m.substitute(raw,{v:('add',a,('mul',('v',dummy),steps[v])) for v,a in center.items()})
        proof=request('all directions',dict(kind='finite_expansion',expression=source(ray),variable=dummy,parameters=[*fixed_names,*inc],
                      parameter_conditions=conds,approach={'point':'0','side':'both'},degree=degree,requested_output=['finite_power_expansion']))
        terms=[freeze(c) for c in proof['value']]
        if len(terms)!=degree+1 or any(set(homogeneous(c))-{k} for k,c in enumerate(terms)):raise Unsupported('A radial coefficient is not homogeneous of its declared degree')
        remainder='peano_in_euclidean_norm'
    else:
        sections=homogeneous(m.add(shifted,m.neg(point_value)) if wants==['exact_increment'] else shifted)
        degree=max(sections,default=0);terms=[sections.get(k,ZERO) for k in range(degree+1)];remainder='identically_zero'
    answer={'homogeneous_terms':terms,'degree':degree,'remainder':remainder}
    if paths:
        derivatives=[];atoms=tuple(steps.values())
        for path in paths:
            if not isinstance(path,(tuple,list)) or not 1<=len(path)<=degree or any(v not in xs for v in path):
                raise Unsupported('The Taylor degree does not cover the requested partial')
            powers=tuple(path.count(x) for x in xs);num,den=m.rational_form(terms[len(path)])
            k=1
            for exponent in powers:k*=factorial(exponent)
            coeff={tuple((a,e) for a,e in mon if a not in atoms):k*c for mon,c in num.items()
                   if tuple(dict(mon).get(a,0) for a in atoms)==powers}
            derivatives.append(m.div(m.poly_expr(coeff),m.poly_expr(den)))
        answer['specified_derivatives_at_center']=derivatives
    return {'source_domain_guards':guards,'center':tuple(center.values()),'increments':inc,
            'basis':'multivariate Taylor theorem on a smooth open neighborhood and uniqueness along every direction' if finite else 'exact translation in the polynomial ring'},answer


def sided_derivatives(task,library,request):
    """Partition smooth branches, extend each from its own side, and compare with the assigned value."""
    from graphs import domain_partition
    from polynomial import NotRational,Undefined
    from verify import same_value
    line=real_intervals
    fields={'kind','id','source','schema','transcription','variable','function','branches','parameters','stated_conditions',
            'method_requirement','requested_output','off_point','point','assigned_value','reference','definition','off','at_zero'}
    kind=task['kind'];x=task.get('variable','x');v=('v',x);ctx=m.context(dict(variable=x))
    at=kind=='one_sided_derivative_investigation';general=kind=='generalized_one_sided_derivatives'
    no_slopes=kind=='continuity_and_no_one_sided_derivative'
    outputs={'differentiate':['finite_derivative','natural_domain_and_boundary_notes'],
             'investigate_differentiability':['complete_differentiability_domain','derivative_formula','boundary_and_one_sided_notes'],
             'one_sided_derivative_functions':['left_derivative_function','right_derivative_function','finite_infinite_and_domain_statuses'],
             'one_sided_derivative_investigation':['derivative_limit','ordinary_one_sided_derivatives','generalized_one_sided_derivatives']}
    origin=task.get('source',{})
    if (not library.data.get('one_sided_branch_derivatives') or set(task)-fields or task.get('parameters') or task.get('stated_conditions')
            or task.get('method_requirement','table_and_rules')!='table_and_rules' or task.get('requested_output')!=outputs.get(kind)
            or set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement','shared_instruction_page'}):
        raise Unsupported('Unresolved domain, method or one-sided source obligation')
    headings={'generalized_one_sided_derivatives':'Найти обобщённые производные в точках разрыва первого рода.',
              'global_one_sided_derivatives':'Определить левую и правую производные как функции x.',
              'continuity_and_no_one_sided_derivative':'Доказать непрерывность в 0 и отсутствие обеих односторонних производных.',
              'one_sided_derivative_investigation':'Установить предел f′, исследовать обычные и обобщённые односторонние производные и дать геометрическую иллюстрацию.'}
    if origin.get('literal_requirement') is not None and origin['literal_requirement']!=headings.get(kind):
        raise Unsupported('The printed instruction does not match the derivative request')
    if (general!=('definition' in task) or general and task['definition']!='quotients subtract the corresponding f(x0-0), f(x0+0) separately'
            or 'reference' in task and (not at or not task['reference'].endswith('generalized one-sided quotient subtracts the one-sided limit f(x0±0)'))):
        raise Unsupported('The ordinary and generalized source definitions must be distinguished')
    form=task.get('function');branches=task.get('branches')
    if no_slopes:
        if form is not None or branches is not None:raise Unsupported('Unbound extra branches')
        form=dict(off=task['off'],at='0',value=task['at_zero'])
    elif 'off' in task or 'at_zero' in task:raise Unsupported('Unused branch assignment')
    if at:
        if form is not None or branches is not None:raise Unsupported('Conflicting source function')
        text,sep,cond=task['off_point'].partition(',');point=str(task['point'])
        if not sep or cond.strip().replace(' ','')!=x+'!='+point:raise Unsupported('Unbound punctured branch')
        form=dict(off=text,at=point,value=task['assigned_value'])
    elif set(task)&{'point','assigned_value','off_point'}:raise Unsupported('Unused point assignment')
    if isinstance(form,dict):
        if set(form)!={'off','at','value'} or branches is not None:raise Unsupported('Ambiguous point assignment')
        branches=[dict(condition=x+'!='+str(form['at']),function=form['off']),dict(condition=x+'='+str(form['at']),function=str(form['value']))]
    elif branches is None and isinstance(form,str):branches=[dict(function=form)]
    elif form is not None:raise Unsupported('Conflicting global and piecewise expressions')
    if not isinstance(branches,list) or not branches:raise Unsupported('A complete source branch partition is required')
    def sample(e,y):return m.substitute(e,{v:q(y)})
    cuts=set()
    def rational_cut(t):
        z=line.read_quadratic_term(t)
        if z.b:raise Unsupported('An irrational cut needs an exact endpoint germ')
        return z.a
    def support(guards):
        # Every raw subexpression contributes its own domain. A sign known wherever
        # its operands are defined therefore adds no extra cut.
        active=[(r,e) for r,e in guards if not (m.sign(e,ctx)==1 or r=='nonzero' and m.sign(e,ctx)==-1)]
        try:partition,covered=domain_partition(x,active,simplify_guards=True)
        except (NotRational,Undefined) as exc:raise Unsupported('The zeros of a source or smoothness constraint are not isolated') from exc
        cuts.update(map(rational_cut,partition['cuts']));return covered
    def in_set(domain,y):
        z=line.Quadratic(y)
        return any((a<0 or a==0 and lc) and (b<0 or b==0 and rc) for l,r,lc,rc in domain[1]
                   for a,b in [(line.compare(line.read_endpoint(l),z),line.compare(z,line.read_endpoint(r)))])
    pieces=[]
    for branch in branches:
        if not isinstance(branch,dict) or set(branch)-{'function','condition'}:raise Unsupported('Unknown branch obligation')
        raw=m.parse(branch['function'],x)
        if any(e[0]=='rpow' for _,e in expression_positions(raw)):raise Unsupported('Real-power branches require original exponent classification')
        restrictions=[]
        if 'condition' in branch:
            tokens=re.split(r'(<=|>=|!=|=|<|>)',branch['condition'].replace(' ',''))
            if len(tokens) not in (3,5):raise Unsupported('Unparsed source interval')
            for a,op,b in zip(tokens[::2],tokens[1::2],tokens[2::2]):
                left,right=m.parse(a,x),m.parse(b,x)
                guards=domain_conditions(left)+domain_conditions(right)
                if guards:restrictions.append(support(guards))
                f=m.add(left,m.neg(right));cert=line.build_certificate(f,op,x)
                cuts.update(map(rational_cut,cert[4]));restrictions.append(cert[-1])
        domain=support(domain_conditions(raw));smooth=support(domain_conditions(raw,True))
        pieces.append((raw,restrictions,domain,smooth))
    def piece(y):
        active=[p for p in pieces if all(in_set(r,y) for r in p[1])]
        if len(active)>1:raise Unsupported('Overlapping source branch assignments')
        return active[0] if active and in_set(active[0][2],y) else None
    cuts=sorted(cuts)
    def split_abs(e,y):
        if e[0]=='abs':
            arg=split_abs(e[1],y);s=m.sign(sample(arg,y),ctx)
            if s not in (1,-1):raise Unsupported('The sign on a complete strict branch is unresolved')
            return arg if s==1 else m.neg(arg)
        return e[0],*(split_abs(a,y) if isinstance(a,tuple) else a for a in e[1:])
    def value_at(e,p):
        z=sample(e,p)
        if not m.constant_defined(z,ctx):return None
        z=m.simplify(z)
        # exp(-r) and 1/exp(r) are the same finite endpoint value for every real r.
        repl={u:m.div(ONE,('exp',m.neg(u[1]))) for _,u in expression_positions(z)
              if u[0]=='exp' and m.sign(u[1],ctx)==-1}
        return m.simplify(m.substitute(z,repl))
    def side_limit(e,p,side):
        z=value_at(e,p)
        if z is not None:return z
        return freeze(request(f'{side} limit at {p}',dict(kind='limit',expression=source(e),variable=x,
                            approach=dict(point=source(q(p)),side=side)))['value'])
    def separated_slopes(quotient,p,side):
        from finite_sums import periodic_phases
        n=('v','n');delta=m.add(v,m.neg(q(p)))
        for _,atom in expression_positions(quotient):
            if atom[0] not in ('sin','cos'):continue
            residue=m.simplify(m.mul(delta,atom[1]))
            sign=m.sign(residue,ctx)
            if m.variable_in(residue) or sign not in (-1,1):continue
            distance=m.div(m.mul(q(2*sign),residue),m.PI)
            shift=m.div(distance if side=='right' else m.neg(distance),n)
            path=m.add(q(p),shift);along=m.simplify(m.substitute(quotient,{v:path}))
            if not periodic_phases(along,'n'):continue
            goal=dict(kind='sequence_liminf_limsup',assumptions=['n is a positive integer'],
                      goal=dict(sequence=source(along),goals=['liminf','limsup']))
            bounds=request('distinct slopes along the '+side+' approach',goal)['value']
            from verify import different_value
            if different_value(bounds['liminf'],bounds['limsup'],ctx):
                return dict(path=path,positive_distance_numerator=distance,quotient=along,**bounds)
        raise Unsupported('Two unequal subsequential limits of the source quotient have not been proved')
    cells=[];expressions=[];cache={}
    for l,r in zip([None,*cuts],[*cuts,None]):
        y=(l+r)/2 if l is not None and r is not None else l+1 if l is not None else r-1 if r is not None else 0
        active=piece(y);entry=None
        if active:
            if not in_set(active[3],y):raise Unsupported('A full source interval lacks the required regularity')
            f=split_abs(active[0],y)
            if f not in cache:
                guards=entailed_domain_guards(domain_conditions(f,True))
                proof=request('ordinary derivative on smooth branch',dict(kind='differentiate',variable=x,function=source(f),
                              stated_conditions=[guard_source(g) for g in guards],method_requirement='table_and_rules'))
                cache[f]=m.simplify(freeze(proof['value']))
            entry=(f,cache[f])
        expressions.append(entry)
        cells.append(dict(left=str(l) if l is not None else '-inf',right=str(r) if r is not None else '+inf',
                          function=entry[0] if entry else None,derivative=entry[1] if entry else None))
    rows=[]
    for i,p in enumerate(cuts):
        if no_slopes and p!=0:continue
        if at and q(p)!=m.simplify(m.parse(str(task['point']),None)):continue
        live=piece(p);assigned=value_at(live[0],p) if live else None
        if live and assigned is None:raise Unsupported('Source endpoint value unresolved')
        sides={}
        for side,e in zip(('left','right'),expressions[i:i+2]):
            if e is None:continue
            if assigned is None and not (general or at):
                sides[side]=dict(ordinary=None);continue
            f,df=e;L=side_limit(f,p,side)
            if L in ('+inf','-inf'):raise Unsupported('A branch lacks a finite endpoint extension')
            if no_slopes:
                if assigned is None or not same_value(L,assigned):raise Unsupported('The source assignment is not continuous')
                quotient=m.simplify(m.div(m.add(f,m.neg(assigned)),m.add(v,m.neg(q(p)))))
                sides[side]=dict(branch_limit=L,ordinary='does_not_exist',witness=separated_slopes(quotient,p,side))
                continue
            slope=value_at(df,p)
            if at and slope is None:slope=side_limit(df,p,side)
            if slope is None:
                quotient=m.simplify(m.div(m.add(f,m.neg(L)),m.add(v,m.neg(q(p)))))
                slope=side_limit(quotient,p,side)
            ordinary=None
            if assigned is not None:
                if same_value(assigned,L):ordinary=slope
                else:
                    s=m.sign(m.add(L,m.neg(assigned)),ctx)
                    if s not in (-1,1):raise Unsupported('Comparison with the assigned value is unresolved')
                    ordinary='+inf' if (s>0)==(side=='right') else '-inf'
            sides[side]=dict(branch_limit=L,ordinary=ordinary,generalized=slope)
            if at:sides[side]['derivative_limit']=slope
        row=dict(point=q(p),value=assigned,sides=sides)
        if no_slopes:row['continuous']=len(sides)==2 and all(same_value(z['branch_limit'],assigned) for z in sides.values())
        if not general:
            slopes=[z['ordinary'] for z in sides.values()]
            if assigned is None:row['ordinary_derivative']='outside_domain'
            elif len(slopes)<2:row['ordinary_derivative']='no_two_sided_domain'
            elif any(z in ('+inf','-inf','does_not_exist') for z in slopes):row['ordinary_derivative']='no_finite_derivative'
            elif same_value(*slopes):row['ordinary_derivative']=slopes[0]
            else:
                from verify import different_value
                if not different_value(*slopes,ctx):raise Unsupported('The two ordinary derivatives have not been distinguished')
                row['ordinary_derivative']='different_one_sided_derivatives'
        if general:
            if len(sides)!=2:continue
            L,R=(sides[s]['branch_limit'] for s in ('left','right'))
            if same_value(L,R) and assigned is not None and same_value(L,assigned):continue
        rows.append(row)
    if (at or no_slopes) and (len(rows)!=1 or set(rows[0]['sides'])!={'left','right'}):raise Unsupported('Two adjacent differentiable branches are required')
    result=dict(cells=cells,cuts=rows)
    if at:
        left,right=(rows[0]['sides'][s]['derivative_limit'] for s in ('left','right'))
        if left!=right and not (isinstance(left,tuple) and isinstance(right,tuple) and same_value(left,right)):
            from verify import different_value
            if left not in ('+inf','-inf') and right not in ('+inf','-inf') and not different_value(left,right,ctx):raise Unsupported('Unresolved two-sided derivative limit')
            result['derivative_limit']='does_not_exist'
        else:result['derivative_limit']=left
    return dict(variable=x,source_branches=branches,smooth_cells='exact real partition',requested=kind),result


def power_series_headings(variable):
    return {'any':f'Разложить по неотрицательным целым степеням {variable} и найти соответствующий интервал сходимости.',
            'basic_expansions_I_to_V':f'Пользуясь основными разложениями I–V, написать разложение в степенной ряд относительно {variable}.',
            'algebra_of_power_series':'Производя соответствующие действия со степенными рядами, получить разложение.',
            'expand_derivative_then_integrate_termwise':'Разложить предварительно производную и получить ряд почленным интегрированием.'}


def analytic_power_series(task,library,request):
    """Prove a local identity of convergent series and give a finite formula for every coefficient."""
    laws=library.data.get('analytic_power_series')
    fields={'kind','id','source','function','series_variable','variable','center','requested_output','method_requirement',
            'derivative_order','source_hint'}
    if not laws or set(task)-fields or 'variable' in task and 'series_variable' in task:
        raise Unsupported('A source hint, extra quantity, constraint or change of variable needs its own proof')
    method=task.get('method_requirement','any')
    src=task.get('source',{})
    x=task.get('series_variable',task.get('variable','x'));text=task['function'];center=task.get('center','0')
    headings=power_series_headings(x)
    if not re.fullmatch(r'[A-Za-z_]\w*',x) or x=='n' or not re.fullmatch(r'-?[0-9]+',center):
        raise Unsupported('The requested series coordinate or center needs another transformation')
    outputs=task.get('requested_output',['all_coefficients'])
    order=task.get('derivative_order')
    if outputs==['all_coefficients','thousandth_derivative_at_zero'] and center=='0' and order is None:order=1000
    extra_output=order is not None and outputs in (['all_coefficients','derivative_at_center'],['all_coefficients','thousandth_derivative_at_zero'])
    if (outputs not in (['all_coefficients'],['all_coefficients','convergence_set']) and not extra_output
            or order is not None and (not extra_output or type(order) is not int or order<0)
            or 'thousandth_derivative_at_zero' in outputs and (order!=1000 or center!='0')):
        raise Unsupported('Another requested output remains')
    heading=headings.get(method)
    if (not heading or set(src)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'}
            or src and src.get('literal_requirement')!=heading+(f' Найти f^({order})({center}).' if extra_output else '')):
        raise Unsupported('The source method or the complete printed instruction was not established')
    names=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{x,'pi','e'})
    if 'n' in names:raise Unsupported('The coefficient index must be independent of fixed parameters')
    raw=m.parse(text,x,names);at=m.parse(center,None)
    ctx=m.context(dict(variable=x,parameters=names))
    guards=domain_conditions(raw)
    for relation,e in domain_conditions(raw,True):
        if not known_guard((relation,m.substitute(e,{('v',x):at})),ctx):
            raise Unsupported('The original expression is undefined or lacks its domain proof at the center')
    termwise=method=='expand_derivative_then_integrate_termwise'
    hint=task.get('source_hint');fractions=[]
    if method=='basic_expansions_I_to_V' and hint=='Применить формулы Эйлера.':hint=None
    if hint not in (None,'Разложить дробь на простейшие.'):
        raise Unsupported('The requested preliminary transformation remains unproved')
    if hint or (library.data.get('power_series_partial_fraction_discovery') and method=='basic_expansions_I_to_V'
                and raw[0]=='div' and not names):
        from polynomial import NotRational,Undefined
        try:
            p,d,poles=_linear_poles(raw,x)
            if len(p)>=len(d) or not hint and len({r for r,_,_ in poles})<2:
                raise Unsupported('No proper denominator with separated linear poles')
            fractions=[('div',q(w),('pow',m.add(('v',x),q(-root)),k))
                       for w,(root,k,_) in zip(_fraction_weights(p,poles),poles) if w]
            if not fractions:raise Unsupported('No verified simple fractions')
            rewritten=fractions[0]
            for part in fractions[1:]:rewritten=('add',rewritten,part)
            from verify import same_value
            if not same_value(raw,rewritten):raise Unsupported('The recombined rational expression differs from the source')
            text=source(rewritten)
        except (NotRational,Undefined,Unsupported) as exc:
            if hint:raise Unsupported('The prescribed rational decomposition is unavailable') from exc
            fractions=[]
    if termwise:
        child=request('differentiate the original function before expanding',dict(kind='differentiate',function=text,variable=x,
                      parameters=names,method_requirement='table_and_rules',stated_conditions=[guard_source(g) for g in domain_conditions(raw,True)]))
        text=source(freeze(child['value']))
    plan,value=taylor_coefficients(text,x,center,False,library,request,laws)
    root=value['root']
    if termwise:
        zero=m.simplify(m.substitute(raw,{('v',x):at}))
        value['coefficients'].append(dict(rule='antiderivative',operands=[root],zero=source(zero),positive_orders=laws['antiderivative']))
        root+=1
    def entire(e):
        if not m.contains(e,('v',x)):return m.constant_defined(e,ctx)
        if e[0]=='v':return True
        if e[0] in ('add','mul'):return all(entire(a) for a in e[1:])
        if e[0]=='pow':return e[2]>0 and entire(e[1])
        return e[0] in ('exp','sin','cos','sinh','cosh') and entire(e[1])
    global_series=entire(raw)
    needs_domain='convergence_set' in outputs or src.get('literal_requirement','').startswith(headings['any'])
    plan.update(method=method,natural_domain=guards,
                convergence_argument='entire_composition' if global_series else 'analytic_composition_on_a_neighborhood')
    value.update(root=root,formula=f'sum_{{k>=0}} C[{root}](k)*({x}-({center}))^k',
                 valid_on='all_real' if global_series else 'an_open_neighborhood_of_the_center')
    if needs_domain:
        if global_series:value['convergence_set']='all_real'
        else:
            from polynomial import rf,NotRational,Undefined
            try:p,d=rf(raw,x)
            except (NotRational,Undefined) as exc:
                raise Unsupported('Exact radius and endpoints of the requested convergence set still need a proof') from exc
            if len(p)!=1 or not p[0] or len(d)!=2 or not d[1]:
                raise Unsupported('There is no checked affine-denominator reduction for the requested convergence set')
            shifted=d[0]+d[1]*rational(at)
            if not shifted:raise Unsupported('The original center is an excluded pole')
            ratio=m.mul(q(-d[1]/shifted),m.add(('v',x),m.neg(at)))
            task_boundary=dict(kind='power_series_convergence_set',index='n',variable=x,start_index=0,
                               term='('+source(ratio)+')^n',requested_output=['radius','open_interval','both_endpoint_classifications'])
            value['convergence_set']=request('prove convergence including both endpoints of the geometric expansion',task_boundary)['value']
            value['valid_on']='certified_convergence_interval'
            plan['convergence_argument']='geometric_series_with_checked_endpoints'
            plan['geometric_factor']=ratio
    if fractions:plan['partial_fractions']=fractions
    if extra_output:
        from finite_sums import translated_coefficients
        from polynomial import rf,pm,NotRational,Undefined
        try:p,d=(translated_coefficients(a,rational(at)) for a in rf(raw,x))
        except (NotRational,Undefined) as exc:raise Unsupported('Exact high-order coefficient extraction needs a rational function') from exc
        if not d[0]:raise Unsupported('The denominator vanishes at the expansion center')
        # Q(z)Q(-z) is even. Select the required parity from P(z)Q(-z) and halve the coefficient index.
        k=order
        while k:
            reflected=tuple((-1)**j*c for j,c in enumerate(d))
            p=pm(p,reflected)[k%2::2] or (0,);d=pm(d,reflected)[::2];k//=2
        value['derivative_at_center']={'factorial_order':order,'multiplier':q(p[0]/d[0])}
    return plan,value


def symbolic_order(task,library,request):
    """Assemble finite coefficient sums, with a proved derivative cycle or first-derivative kernel."""
    basis=library.data.get('symbolic_taylor_coefficients')
    allowed={'kind','id','source','variable','function','point','order'}
    if not basis or set(task)-allowed or task.get('order') not in ('arbitrary positive integer n','n','n>=1'):
        raise Unsupported('Unbound order, method or further obligation')
    kind=task['kind'];x=task.get('variable','x');at=kind=='symbolic_order_point_derivative'
    origin=task.get('source',{});text=task['function']
    if set(origin)-{'exercise','pdf_page','printed_page','printed_subpart','pdf_sha256','literal_requirement','printed_occurrences'}:
        raise Unsupported('The printed hint or additional domain requirement must be treated separately')
    headings={'symbolic_order_derivative':('Найти производную n-го порядка.','Найти y^(n).'),
              'symbolic_order_differential':('Найти дифференциал n-го порядка.',),
              'symbolic_order_point_derivative':(f"Найти f^(n)({task.get('point')}).",)}
    occurrence=origin.get('printed_occurrences')
    if occurrence is not None and not re.fullmatch(r'The same exercise number and expression are printed twice on page [0-9]+ \([A-Za-z -]+\); one mathematical input\.',occurrence):
        raise Unsupported('An additional printed observation has not been bound')
    heading=origin.get('literal_requirement')
    if (at!=('point' in task) or origin and not heading or heading and heading not in headings[kind]
            and not (kind=='symbolic_order_derivative' and heading=='Найти n-ю производную арктангенса.' and text==f'atan({x})')):
        raise Unsupported('The source center, function or requested differential has changed')
    return taylor_coefficients(text,x,task.get('point'),kind=='symbolic_order_differential',library,request)


def taylor_coefficients(text,x,point,differential,library,request,expansion=None,*,fixed_real_powers=False):
    """Build an expression DAG of coefficient formulas at a fixed or generic real center."""
    basis=library.data['symbolic_taylor_coefficients'];at=point is not None
    params=sorted(set(re.findall(r'[A-Za-z_]\w*',text))-m.FUNCTIONS-set(m.ALIASES)-{x,'pi','e'})
    increment='d'+x
    if x=='n' or increment in params:raise Unsupported('Ambiguous order index or differential increment')
    dummy='__step'
    while dummy in [x,*params]:dummy+='_'
    names=[x,*params];m.context(dict(variable=dummy,parameters=names))
    raw=m.parse(text,None,names);center=m.parse(str(point),None,params) if at else ('s',x)
    positive=() if expansion else (('s','n'),)
    def domains(e,smooth=False):
        return domain_conditions(e,smooth,positive_integer_exponents=positive)
    replace={('s',x):center}
    domain=domains(raw)
    facts=() if at else entailed_domain_guards(domain)
    ctx=m.context(dict(variable=dummy,parameters=names,parameter_conditions=[guard_source(g) for g in facts]))
    def at_center(g):
        return g[0],m.substitute(g[1],replace)
    if any(not known_guard(at_center(g),ctx) and at_center(g) not in facts for g in (*domains(raw,True),*(domain if at else ()))):
        raise Unsupported('An original point or boundary lacks the required analytic neighborhood')
    rows=[];slots={};derivatives={}
    steps=library.data['partial_bundle_contract']['ordinary_kernel_leibniz']['kernel_steps']
    def kernel(op):
        if op not in derivatives:
            z=('v',dummy)
            guards=[guard_source(g) for g in domain_conditions((op,z),True)]
            p=request('first derivative of '+op,dict(kind='differentiate',variable=dummy,function=source((op,z)),
                        method_requirement='table_and_rules',stated_conditions=guards))
            derivatives[op]=m.simplify(freeze(p['value']))
        return derivatives[op]
    def node(e):
        if e in slots:return slots[e]
        tag=e[0];args=[];spec={};v0=m.substitute(e,replace);zero=source(m.simplify(v0) if expansion else v0)
        if e==('s',x):rule='coordinate'
        elif not m.contains(e,('s',x)):
            if not m.constant_defined(m.substitute(e,replace),ctx):raise Unsupported('Undefined fixed expression')
            rule='constant'
        elif tag in ('add','mul'):
            rule='addition' if tag=='add' else 'product';args=[node(w) for w in e[1:]]
        elif tag=='div':
            rule='product';args=[node(e[1]),node(('pow',e[2],-1))]
        elif tag in ('pow','rpow','sqrt','cbrt'):
            real=tag=='rpow' and fixed_real_powers and not m.contains(e[2],('s',x))
            if tag=='rpow' and not real and e[2]!=('s','n'):raise Unsupported('Real powers need a separate real-branch proof')
            exponent={'sqrt':'1/2','cbrt':'1/3','rpow':'n'}.get(tag,e[-1])
            if real:
                if not m.constant_defined(e[2],ctx) or not known_guard(('positive',m.substitute(e[1],replace)),ctx):
                    raise Unsupported('The analytic real power has no positive center or its exponent is undefined')
                exponent=source(e[2])
            integer=not real and (exponent=='n' or type(exponent)==int and exponent>=0)
            rule='nonnegative_integer_power' if integer else 'binomial_nonzero'
            spec['exponent']=str(exponent);args=[node(e[1])]
        elif expansion and tag in expansion['basic'] and m.simplify(m.substitute(e[1],replace))==ZERO:
            rule='elementary_maclaurin';args=[node(e[1])]
            spec['outer_coefficients']=expansion['basic'][tag]
        elif expansion and tag=='ln':
            rule='logarithmic_series';args=[node(e[1])]
        elif tag in steps:
            cycle=[];sign=1;state=tag
            while (state,sign) not in cycle:
                cycle.append((state,sign));target,factor=steps[state]
                if factor not in (-1,1) or m.simplify(m.add(kernel(state),m.neg(m.mul(q(factor),(target,('v',dummy))))))!=ZERO:
                    raise Unsupported('A derivative-cycle transition did not replay')
                state=target;sign*=factor
            if (state,sign)!=cycle[0]:raise Unsupported('The derivative cycle does not close')
            rule='derivative_cycle';args=[node(e[1])];spec['cycle']=cycle
        elif tag in ('atan','asin','ln'):
            derived=m.substitute(kernel(tag),{('v',dummy):e[1]})
            rule='integrated_chain';args=[node(e[1]),node(derived)]
        else:raise Unsupported('No coefficient identity on the source domain for '+tag)
        row=dict(zero=zero,rule=rule,operands=args,**spec)
        row['positive_orders']=expansion[rule] if expansion and rule in expansion else basis['steps'][rule]
        rows.append(row);slots[e]=len(rows)-1;return slots[e]
    root=node(raw)
    plan=dict(variable=x,center=source(center),fixed_parameters=params,natural_domain=domain,pointwise=at,
              order='n is a positive integer',coefficient_lemma='method.symbolic_taylor_coefficients')
    value=dict(coefficients=rows,root=root,formula=f'n! * C[{root}](n)'+(f' * ({increment})^n' if differential else ''),
               notation=basis['notation'])
    return plan,value


def exact_ordinary_order(task,library,request):
    """Differentiate affine kernels by their closed formulas and compose with Leibniz."""
    from functools import lru_cache
    from math import comb,prod
    from fractions import Fraction
    from integrals import affine
    from plane_geometry import reduce
    if not library.data.get('finite_affine_kernel_orders'):
        raise Unsupported('No finite-order kernel method on the current library')
    kind=task['kind'];origin=task.get('source',{})
    meta={'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256'}
    differential=kind=='differential_of_independent_variable'
    fields={'id','source','kind','function','stated_conditions','requested_output'}
    if kind=='partial_derivatives':
        if (set(task)-fields-{'variables','parameters','requested_partials'}
                or set(origin)-meta-{'printed_instruction','requested_ordinary_orders'}
                or origin.get('printed_instruction')!='В следующих примерах найти производные указанного порядка'
                or len(task['variables'])!=1 or task['requested_output']!=['specified_partial_derivatives']):
            raise Unsupported('The original ordinary derivative order or method is not bound')
        var,=task['variables'];parameters=task.get('parameters',[])
        orders=origin['requested_ordinary_orders']
        if task['requested_partials']!=[[var]*n for n in orders]:
            raise Unsupported('The selected order differs from the original instruction')
    else:
        allowed=meta|{'literal_requirement','printed_goal','requested_operator'}
        literal=origin.get('literal_requirement')
        if (set(task)-fields-{'variable','fixed_parameters','orders'} or set(origin)-allowed
                or literal not in (None,'Найти дифференциал указанной функции.')
                or literal and not differential):
            raise Unsupported('An additional order requirement remains')
        var=task['variable'];parameters=task.get('fixed_parameters',[])
        orders=task['orders']
        if task['requested_output']!=(['differentials'] if differential else ['derivatives']):
            raise Unsupported('An unknown derivative result was requested')
        if (literal and orders!=[1] or 'printed_goal' in origin and
                (not differential or len(orders)!=1 or origin.get('requested_operator')!='differential'
                 or origin['printed_goal']!=f'Treat {var} as independent; find d^{orders[0]} y.')):
            raise Unsupported('The typed order disagrees with the printed differential')
    if not orders or any(type(n)!=int or n<1 for n in orders) or len(set(orders))!=len(orders):
        raise Unsupported('The derivative orders must be positive integers')
    x=('v',var);raw=m.parse(task['function'],var,parameters)
    conditions=task.get('stated_conditions',[])
    facts=tuple(domain_conditions(raw))
    smooth=tuple(domain_conditions(raw,True))
    rules={}
    def product(a,b):
        if ZERO in (a,b):return ZERO
        if a==ONE:return b
        if b==ONE:return a
        return ('mul',a,b)
    def plus(a,b):
        return b if a==ZERO else a if b==ZERO else ('add',a,b)
    def kernel(node):
        tag=node[0];base=node[1] if len(node)>1 and isinstance(node[1],tuple) else None
        exponent={'sqrt':Fraction(1,2),'cbrt':Fraction(1,3)}.get(tag)
        if tag=='pow':exponent=Fraction(node[2])
        if tag=='div' and node[1]==ONE:
            base=node[2];exponent=Fraction(-1)
            if base[0] in ('sqrt','cbrt'):
                exponent/=2 if base[0]=='sqrt' else 3
                base=base[1]
        if exponent is None and tag not in ('exp','sin','cos'):return None
        try:a,_=affine(base,var)
        except Unsupported:return None
        return base,a,exponent
    @lru_cache(maxsize=None)
    def derivative(e,n):
        if not n:return e
        if not m.variable_in(e,var):return ZERO
        a=kernel(e)
        if a is not None:
            base,slope,k=a
            rules[e]=dict(kernel=e,affine_base=base,slope=slope,exponent=None if k is None else q(k))
            scale=q(m.num(slope)**n) if m.num(slope) is not None else ('pow',slope,n)
            if k is None:
                modes={'sin':(('sin',1),('cos',1),('sin',-1),('cos',-1)),
                       'cos':(('cos',1),('sin',-1),('cos',-1),('sin',1)),
                       'exp':(('exp',1),)*4}
                tag,sign=modes[e[0]][n%4]
                return product(product(q(sign),scale),(tag,base))
            weight=prod(k-j for j in range(n))
            if not weight:return ZERO
            remaining=int(k)-n
            factor=(base if remaining==1 else ONE if remaining==0 else ('pow',base,remaining)) if k.denominator==1 else (
                'div',e,base if n==1 else ('pow',base,n))
            return product(product(q(weight),scale),factor)
        op=e[0]
        if e==x:return ONE if n==1 else ZERO
        if op=='add':return plus(*(derivative(z,n) for z in e[1:]))
        if op=='div' and n==1:
            u,v=e[1:]
            dv=derivative(v,1);du=derivative(u,1)
            rules[e]=dict(quotient=e,denominator=v)
            return ('div',plus(product(du,v),product(q(-1),product(u,dv))),('pow',v,2))
        if op=='div' and e[1]!=ONE:
            return derivative(('mul',e[1],('div',ONE,e[2])),n)
        if op=='mul':
            left,right=e[1:];total=ZERO
            for j in range(n+1):
                u=derivative(left,j)
                if u==ZERO:continue
                v=derivative(right,n-j)
                if v!=ZERO:total=plus(total,product(q(comb(n,j)),product(u,v)))
            return total
        if n==1 and op in ('pow','sqrt','cbrt','ln','abs','sin','cos','exp','tan','asin','acos','atan'):
            u=e[1];inner=u[1] if op=='ln' and u[0]=='abs' else u
            du=derivative(inner,1)
            if op=='pow':
                power=e[2]
                factor=ZERO if not power else product(q(power),ONE if power==1 else ('pow',u,power-1))
            else:
                factor={'sqrt':('div',ONE,('mul',q(2),e)), 'cbrt':('div',ONE,('mul',q(3),('pow',e,2))),
                        'ln':('div',ONE,inner), 'abs':('div',e,u), 'sin':('cos',u), 'cos':('mul',q(-1),('sin',u)),
                        'exp':e,'tan':('div',ONE,('pow',('cos',u),2)),
                        'asin':('div',ONE,('sqrt',('add',ONE,('mul',q(-1),('pow',u,2))))),
                        'acos':('div',q(-1),('sqrt',('add',ONE,('mul',q(-1),('pow',u,2))))),
                        'atan':('div',ONE,('add',ONE,('pow',u,2)))}[op]
            rules[e]=dict(chain_kernel=e,local_factor=factor)
            return product(du,factor)
        raise Unsupported('The expression has no admitted affine kernel or product decomposition')
    ctx=m.context(dict(variable='__ordinary_scope',parameters=[var,*parameters],
        parameter_conditions=[*conditions,*(guard_source(g) for g in entailed_domain_guards(smooth))]))
    for r,e in facts:
        if not m.variable_in(e,var) and m.constant_defined(e,ctx):
            sign=m.sign(e,ctx)
            if sign==0 and r!='nonnegative' or sign==-1 and r!='nonzero':
                raise Unsupported('The original expression has no real domain under a fixed guard')
    values=tuple(derivative(raw,n) for n in orders)
    if max(orders)<=12:values=tuple(reduce(e) for e in values)
    scope=dict(derivative_conditions=conditions,retained_original_guards=smooth)
    increment='d'+var
    while increment in parameters:increment+='_'
    order_terms=tuple(values)
    if differential:
        order_terms=tuple(product(z,('s',increment) if k==1 else ('pow',('s',increment),k))
                          for k,z in zip(orders,values))
    return (dict(theorem='method.finite_affine_kernel_orders',original=raw,orders=orders,scope=scope,kernels=list(rules.values()),
                 argument='Для каждой аффинной основы вычисляется её постоянная производная. Степень даёт падающий факториал, гармоника — циклическую смену синуса и косинуса. Суммы дифференцируются почленно, произведения по формуле Лейбница. Для независимой переменной коэффициент дифференциала умножается на соответствующую степень её приращения.'),
            dict(derivatives=tuple(values),ordered_results=order_terms,orders=orders,variable=var,increment=increment if differential else None,
                 original_domain=facts,smooth_domain=smooth,stated_conditions=conditions))


def measurement_uncertainty(task,library):
    """Use a dimensionless input perturbation for both exact and first-order error."""
    from cartesian_fields import vector_source
    from plane_geometry import names
    if not library.data.get('relative_measurement_error'):
        raise Unsupported('The dimensionless perturbation method is unavailable')
    headings=(
        'Сторона квадрата 2,4 м ± 0,05 м; определить предельную абсолютную и относительную погрешности вычисления площади.',
        'С какой относительной погрешностью допустимо измерить радиус шара, чтобы его объём можно было определить с точностью до 1%?',
        'Для формулы маятника g=4π²l/T² определить влияние на g относительной погрешности δ измерения длины l; продолжение на с.108.',
        'Для формулы маятника g=4π²l/T² определить влияние на g относительной погрешности δ измерения периода T; продолжение на с.108.',
        'Определить абсолютную погрешность десятичного логарифма числа x>0 по его относительной погрешности δ.',
    )
    vector_source(task,{'formula','nominal','absolute_error','uncertain_variable','stated_conditions','source_pdf_pages',
                        'given_relative_error','requested_output'},headings)
    wanted=task['requested_output'];formula=task['formula'];parameters=names(formula)
    heading=task.get('source',{}).get('literal_requirement')
    if heading is not None:
        required={
            headings[0]:('x^2',['absolute_area_error','relative_area_error']),
            headings[1]:('4*pi*R^3/3',['admissible_relative_radius_error']),
            headings[2]:('4*pi^2*l/T^2',['relative_output_error']),
            headings[3]:('4*pi^2*l/T^2',['relative_output_error']),
            headings[4]:('ln(x)/ln(10)',['absolute_output_error']),
        }[heading]
        if (required!=(formula,wanted) or heading==headings[0] and (task.get('nominal')!={'x':'12/5'}
                or task.get('absolute_error')!={'x':'1/20'})
                or heading==headings[1] and task.get('given_relative_error')!={'volume':'1/100'}
                or heading in headings[2:4] and (task.get('given_relative_error')!='delta'
                    or task.get('uncertain_variable')!=('l' if heading==headings[2] else 'T'))
                or heading==headings[4] and (task.get('given_relative_error')!='delta' or task.get('stated_conditions')!=['x>0'])):
            raise Unsupported('The typed scaling law or error data disagree with the original measurements')
    coordinate=task.get('uncertain_variable') or (parameters[0] if len(parameters)==1 else None)
    if coordinate not in parameters:
        raise Unsupported('The variable under measurement is not bound')
    params=[p for p in parameters if p!=coordinate]
    x=('v',coordinate);s=('s',coordinate)
    stated=task.get('stated_conditions',[])
    if any(c not in {p+'>0' for p in parameters} for c in stated):
        raise Unsupported('An additional measured-domain restriction needs its own interval check')
    physical=[p+'>0' for p in params] if heading in headings[2:4] else []
    conditions=list(dict.fromkeys([*stated,coordinate+'>0',*physical]))
    ctx=m.context(dict(variable='__measurement',parameters=parameters,parameter_conditions=conditions))
    raw=m.parse(formula,coordinate,params)
    natural=domain_conditions(raw)
    if not all(known_guard((r,m.substitute(e,{x:s})),ctx) for r,e in natural):
        raise Unsupported('The whole positive perturbation interval must stay in the original domain')
    nominal=task.get('nominal')
    tol=task.get('given_relative_error')
    base=None
    if nominal is not None:
        if set(nominal)!=set(task.get('absolute_error',{})) or set(nominal)!={coordinate} or tol is not None:
            raise Unsupported('One exact absolute error and its nominal input are required')
        base,amount=[m.parse(t[coordinate],None) for t in (nominal,task['absolute_error'])]
        if not all(m.constant_defined(v,ctx) and m.sign(v,ctx)==1 for v in (base,amount,m.add(base,m.neg(amount)))):
            raise Unsupported('The measurement interval must remain positive')
        delta=m.div(amount,base)
    elif isinstance(tol,str):
        delta=('s',tol) if re.fullmatch(r'[A-Za-z_]\w*',tol) else m.parse(tol,None)
        if delta[0]=='s' and delta[1] in parameters:
            raise Unsupported('The error symbol cannot capture a formula parameter')
    else:
        delta=None
    if delta is not None and delta[0]!='s' and (not m.known_nonnegative(delta,ctx) or
                                                m.sign(m.add(ONE,m.neg(delta)),ctx)!=1):
        raise Unsupported('The perturbation radius must be nonnegative and smaller than one')
    one_minus=lambda e:m.add(ONE,m.neg(e))
    def bound(power,d):
        if not power:return ZERO
        endpoint=m.add(ONE,d) if power>0 else one_minus(d)
        return m.simplify(m.add(m.power(endpoint,power),m.neg(ONE)))
    result=dict(variable=coordinate,formula=raw,original_domain=natural,conditions=conditions)
    if wanted==['absolute_output_error']:
        if delta is None or raw[0]!='div' or raw[1]!=('ln',x) or m.variable_in(raw[2]) or not m.nonzero(raw[2],ctx):
            raise Unsupported('An absolute logarithmic scale change is required')
        k=m.div(ONE,m.simplify(('abs',raw[2])))
        result.update(exact_absolute_bound=m.mul(k,m.neg(('ln',one_minus(delta)))),
                      first_order_absolute_bound=m.mul(k,delta),perturbation_domain=('0<=relative_error<1',delta))
        argument='Подставляем положительное измерение x(1+h). Разность логарифмов даёт ln(1+h) с постоянным множителем. При |h|≤δ<1 её модуль наибольший при h=−δ, поскольку (1−δ)(1+δ)<1.'
    else:
        n,d=m.rational_form(raw)
        def degree(polynomial):
            values={dict(mon).get(x,0) for mon in polynomial}
            if len(values)!=1 or any(a!=x and m.variable_in(a,coordinate) for mon in polynomial for a,k in mon):
                raise Unsupported('The measured variable has no single homogeneous scaling order')
            return values.pop()
        power=degree(n)-degree(d)
        coeff=m.simplify(m.substitute(raw,{x:ONE}))
        if not m.nonzero(coeff,ctx):
            raise Unsupported('The nominal observable must be nonzero for relative error')
        result.update(scaling_exponent=power,nonzero_scale=coeff)
        if isinstance(tol,dict):
            if wanted!=['admissible_relative_radius_error'] or len(tol)!=1 or power<1:
                raise Unsupported('A positive power law and a single prescribed output tolerance are required')
            epsilon=m.parse(next(iter(tol.values())),None)
            if m.sign(epsilon,ctx)!=1 or m.sign(one_minus(epsilon),ctx)!=1:
                raise Unsupported('Output tolerance must lie between zero and one')
            rooted=('rpow',m.add(ONE,epsilon),q(1,power))
            result.update(exact_admissible_relative_error=m.add(rooted,q(-1)),
                         first_order_admissible_relative_error=m.div(epsilon,q(power)))
        elif delta is not None:
            result.update(exact_relative_bound_to_nominal=bound(power,delta),
                exact_relative_bound_to_true=bound(-power,delta),first_order_relative_bound=m.mul(q(abs(power)),delta),
                relative_perturbation_domain=('0<=relative_error<1',delta))
            if base is not None and wanted==['absolute_area_error','relative_area_error']:
                nominal_output=m.simplify(m.substitute(raw,{x:base}))
                magnitude=m.simplify(('abs',nominal_output))
                result.update(exact_absolute_bound=m.mul(magnitude,result['exact_relative_bound_to_nominal']),
                    first_order_absolute_bound=m.mul(magnitude,result['first_order_relative_bound']))
            elif base is not None or wanted!=['relative_output_error']:
                raise Unsupported('An unrecognized set of scaled errors was requested')
        else:
            raise Unsupported('An original tolerance has not been specified')
        argument='После подстановки измерения x(1+h) отношение к номиналу равно (1+h)^k. Монотонность переносит точную оценку на края интервала, а выпуклость степенной функции сравнивает крайние отклонения. Производная при h=0 даёт первый порядок, а обращение возрастающей степени — точный входной допуск.'
    return dict(theorem='method.measurement_error_scaling',source=raw,exact_scope=conditions,argument=argument),result


def ordinary_differentiation(task,library,request):
    """Interpret repeated ordinary differentiation, holding the independent increment fixed."""
    contract=library.data['partial_bundle_contract']
    origin=task.get('source',{})
    printed=task.get('kind')=='partial_derivatives'
    fields={'exercise','printed_page','pdf_page','pdf_sha256'}
    child={k:task[k] for k in ('function','parameters','stated_conditions','method_requirement') if k in task}
    if printed:
        plan=compile_partial_bundle(task,contract,expand_prefixes=False)
        xs=plan['variables'];orders=plan['orders']
        if (len(xs)!=1 or len(orders)!=1 or origin.get('requested_operator')!='differential'
                or set(origin)-fields-{'requested_operator','printed_goal'}
                or origin.get('printed_goal')!=f'Treat {xs[0]} as independent; find d^{orders[0]} y.'):
            raise Unsupported('The printed differential order or independence of the coordinate is unconfirmed')
        x,=xs;order,=orders
    else:
        x=task.get('variable');order=task.get('derivative_order')
        if (set(task)-set(child)-{'id','kind','schema','source','transcription','variable','derivative_order','requested_output'}
                or type(order)!=int or order!=2 or task.get('requested_output')!=['second_derivative','original_domain_and_derivative_existence_scope']
                or set(origin)-fields-{'printed_group_instruction','definition_ref','section_title'}
                or origin.get('printed_group_instruction',"Найти y'', если")!="Найти y'', если"):
            raise Unsupported('Unbound ordinary derivative order or additional source obligation')
    child.update(kind='partial_derivatives',variables=[x],requested_partials=[[x]*order],requested_output=['specified_partial_derivatives'])
    if not printed:plan=compile_partial_bundle(child,contract)
    proof=request('successive derivatives on the original domain',child)
    coefficient,=proof['value']
    result=dict(variable=x,order=order,natural_domain=plan['natural_domain'],stated_conditions=plan['stated_conditions'])
    if not printed:return result,coefficient
    increment='d'+x
    while increment in [x,*plan['parameters']]:increment+='_'
    result.update(independent_increment=increment,derivative=coefficient)
    return result,m.mul(freeze(coefficient),m.power(('s',increment),order))


def printed_ordinary_operator(task,base):
    """Bind the printed equation independently to its machine-readable derivative notation."""
    origin=task['source'];text=origin.get('printed_goal');typed=origin.get('requested_operator')
    if (set(origin)-{'exercise','pdf_page','printed_page','pdf_sha256','printed_goal','requested_operator'}
            or not isinstance(text,str) or not isinstance(typed,str) or len(base['variables'])!=1
            or not base['selected_paths'] or task.get('requested_output')!=['specified_partial_derivatives']):
        raise Unsupported('Не установлены полная исходная цель и порядки обыкновенных производных')
    claim=re.fullmatch(r'Prove\s+([^=]+?)\s*=\s*0(.*)',text.strip().removesuffix('.'))
    if not claim:raise Unsupported('Требуется печатное равенство дифференциального выражения нулю')
    expression,note=claim[1],claim[2].strip()
    x,=base['variables'];pars=base['parameters'];names=[x,*pars]
    aliases={}
    if note.startswith('('):
        definitions=re.fullmatch(r'\((.+?) any constants, including repeated values\)',note)
        if not definitions:raise Unsupported('Не разобрана область параметров печатного равенства')
        for entry in definitions[1].split(','):
            pair=re.fullmatch(r'([^\W\d]\w*)\s*=\s*(\w+)',entry.strip())
            if not pair or pair[2] not in pars or pair[1] in [*names,*aliases]:
                raise Unsupported('Неоднозначные обозначения параметров')
            aliases[pair[1]]=pair[2]
    elif note.startswith('for all '):
        quantifier=note.removeprefix('for all ')
        words='one two three four five six seven eight nine ten'.split()
        count=re.fullmatch(r'(\w+) constants?',quantifier)
        if count and (count[1].isdecimal() or count[1] in words):
            valid=(int(count[1]) if count[1].isdecimal() else 1+words.index(count[1]))==len(pars)
        else:valid=set(re.split(r'\s*,\s*',quantifier.removeprefix('arbitrary ')))==set(pars)
        if not valid:raise Unsupported('Список произвольных постоянных не соответствует исходной функции')
    elif note:
        from operations import expression_positions
        if (note!=f'. The original logarithm forces {x}>0'
                or ('positive',('s',x)) not in base['domain_guards']
                or not any(e==('ln',('s',x)) for _,e in expression_positions(m.parse(base['function'],None,names)))):
            raise Unsupported('Не обоснована печатная оговорка об исходной области')
    if (note.startswith('for all ') or aliases) and any(
            re.search(r'\b'+re.escape(p)+r'\b',c) for p in pars for c in base['stated_conditions']):
        raise Unsupported('Ограничение параметра противоречит требованию произвольных постоянных')

    orders=sorted({len(p) for p in base['selected_paths']})
    slots={'Y':0,**{'Y'+str(k):k for k in orders}}
    if any(s=='y' or re.fullmatch(r'Y\d*',s) for s in [*names,*aliases]):
        raise Unsupported('Обозначение поля совпало с переменной или параметром')
    expression=expression.replace('−','-').replace('″','′′').replace("'",'′')
    expression=re.sub(r'[⁰¹²³⁴⁵⁶⁷⁸⁹]+',lambda a:'^'+a[0].translate(
                         str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')),expression)
    symbols=sorted([*names,*aliases],key=len,reverse=True)
    token_pattern='|'.join(re.escape(s) for s in symbols)+r'|y(?:\^\(\d+\)|′+)?|\d+(?:\.\d+)?|[()+*/^-]'
    tokens=re.findall(token_pattern,expression)
    if ''.join(tokens)!=re.sub(r'\s+','',expression):raise Unsupported('Не разобраны все знаки печатного уравнения')
    cooked=[];previous_factor=False
    for token in tokens:
        if token not in symbols and token.startswith('y'):
            degree=token[3:-1] if token.startswith('y^(') else str(token.count('′'))
            token='Y'+degree if degree!='0' else 'Y'
            if token not in slots:raise Unsupported('Порядок производной расходится с исходной целью')
        factor=token in symbols or token in slots or token[0].isdigit()
        if previous_factor and (factor or token=='('):
            cooked.append('*')
        cooked.append(aliases.get(token,token))
        previous_factor=factor or token==')'
    if (m.parse(''.join(cooked),None,[*names,*slots])!=m.parse(typed,None,[*names,*slots])
            or set(re.findall(r'\bY[1-9]\d*\b',typed))!=set(slots)-{'Y'}):
        raise Unsupported('Печатное равенство расходится с оператором или запрошенными производными')
    def derivative(match):
        order=slots[match[0]]
        return ('D_'+x+'(')*order+'y'+')'*order
    return re.sub(r'\bY\d*\b',derivative,typed)


def differential_operator(task,library,request):
    """Apply scalar differential operators on the field's original domain."""
    from verify import same_value
    base_keys={'function','variables','parameters','stated_conditions','method_requirement'}
    fields=base_keys|{'kind','id','schema','source','transcription','field_symbol','operators','requests','requested_output'}
    if library.data.get('task_compilers',{}).get('differential_operator')!='coordinate_operator_composition':
        raise Unsupported('Coordinate operator composition is not admitted')
    printed=task.get('kind')=='partial_derivatives'
    if printed:
        base=compile_partial_bundle(task,library.data['partial_bundle_contract'])
        field='y';rules={'L':printed_ordinary_operator(task,base)}
        requests=[{'apply':['L'],'equals':'0'}];wanted=['verify_identities']
    else:
        if set(task)-fields or task.get('kind')!='differential_operator':
            raise Unsupported('Unknown differential operator source fields')
        base=compile_partial_bundle({'kind':'partial_derivatives',**{k:task[k] for k in base_keys if k in task}})
        field=task.get('field_symbol','u');rules=task.get('operators');requests=task.get('requests')
        wanted=task.get('requested_output',['operator_values'])
    coords=base['variables']; names=[*coords,*base['parameters']]
    if not isinstance(wanted,(list,tuple)) or not wanted or set(wanted)-{'operator_values','verify_identities'}:
        raise Unsupported('Unknown operator output requirement')
    if (not isinstance(field,str) or not isinstance(rules,dict) or not rules or
        any(not isinstance(k,str) or not isinstance(v,str) for k,v in rules.items()) or
        not isinstance(requests,(list,tuple)) or not requests):
        raise Unsupported('Expected nonempty operator definitions and requests')
    dummy='__operator_coordinate'
    while dummy in names or dummy==field:dummy+='_'
    m.context({'variable':dummy,'parameters':names+[field]})
    derivatives={'D_'+v:v for v in coords}
    if set(derivatives).intersection(names+[field]):raise Unsupported('Derivative name collision')
    definitions={k:m.parse(text,None,names+[field],derivatives) for k,text in rules.items()}
    raw=m.parse(base['function'],None,names)
    ctx=m.context({'variable':dummy,'parameters':names,'parameter_conditions':
                   [*base['stated_conditions'],*(guard_source(g) for g in base['domain_guards'])]})
    transitions={}; outputs=[]; values=[]
    def require_domain(expr):
        if not all(known_guard(g,ctx) for g in domain_conditions(expr)):
            raise Unsupported('Operator or claimed value has an unproved restriction on the original domain')
    def evaluate(e,operand):
        if e==('s',field):return operand
        op=e[0]
        if op in derivatives:
            arg=evaluate(e[1],operand);require_domain(arg)
            key=(derivatives[op],arg)
            if key not in transitions:
                index=(key[0],)
                t={**partial_child_task(base,index,{}),'function':source(arg)}
                child=request(op,t)
                transitions[key]=partial_component_value(base,index,child)
            return transitions[key]
        built=(op,*(evaluate(c,operand) if isinstance(c,tuple) else c for c in e[1:]))
        require_domain(built)
        return m.simplify(built)
    for item in requests:
        if not isinstance(item,dict) or set(item)-{'apply','equals'}:raise Unsupported('Unknown operator request')
        pipeline=item.get('apply')
        if not isinstance(pipeline,(list,tuple)) or not pipeline or any(k not in definitions for k in pipeline):
            raise Unsupported('Invalid operator composition')
        result=raw
        for k in pipeline:result=evaluate(definitions[k],result)
        require_domain(result)
        if 'equals' in item:
            rhs=m.parse(item['equals'],None,names);require_domain(rhs)
            if not same_value(result,rhs):raise Unsupported('The requested differential identity was not established')
        elif 'verify_identities' in wanted:raise Unsupported('A requested identity has no right-hand side')
        outputs.append({'apply':list(pipeline),'verified_identity':'equals' in item});values.append(result)
    plan={'field':raw,'variables':coords,'natural_domain':base['natural_domain'],'stated_conditions':base['stated_conditions'],
          'definitions':definitions,'applications':[(v,e,val) for (v,e),val in transitions.items()],'outputs':outputs}
    if printed:plan['printed_identity']=task['source']['printed_goal']
    return plan,tuple(values)


def compile_original_table(task):
    if task.get('kind')!='differentiate' or task.get('method_requirement')=='from_definition': raise Unsupported('Original-variable tables do not fulfill this goal or method')
    compilation=compile_derivative(task);ctx=m.context(compilation['compiled_limit_task'])
    if not compilation['point_defined']:raise Unsupported('Original source point domain unresolved')
    point=compilation['formula_scope']['quantified_symbol']
    ctx.update(domain='pointwise_real',variable=task.get('variable','x'),original_variable=task.get('variable','x'),
               point=('s',point),point_symbol=point,side='pointwise')
    return {'compilation':compilation,'context':ctx,'goal':('derivative',compilation['function_ast'])}


SERIES_POWERS = (q(0),q(2),q(1),q(3,2))


def phase_integer(e,n,guards):
    """Extract the parity in a(n)=(-1)^(e*n) R(n), retaining original rational divisors."""
    from polynomial import rf,pdiv
    if e[0]=='rpow' and m.simplify(e[1])==q(-1):
        guards.extend(domain_conditions(e[1])+domain_conditions(e[2]))
        p,d=rf(e[2],n);a,rest=pdiv(p,d)
        if any(rest) or len(a)>2 or any(c.denominator!=1 for c in a):
            raise Unsupported('Parity only follows from an integer affine exponent')
        return int(a[1])%2 if len(a)==2 else 0,q(-1 if int(a[0])%2 else 1)
    if e[0] in ('mul','div','add'):
        u,a=phase_integer(e[1],n,guards);v,b=phase_integer(e[2],n,guards)
        if e[0]=='add' and u!=v:raise Unsupported('Mixed periodic weights require separate finite sums')
        return (u if e[0]=='add' else (u+v)%2),(e[0],a,b)
    if e[0]=='pow':
        u,a=phase_integer(e[1],n,guards);return u*e[2]%2,('pow',a,e[2])
    return 0,e

def _fraction_weights(p,poles):
    """Verify a partial-fraction decomposition against its original common numerator."""
    from fractions import Fraction as F
    from polynomial import span_coefficients,pm,pa
    cols=[c for _,_,c in poles];weights=span_coefficients(p,cols)
    if weights is None:raise Unsupported('Unresolved rational poles')
    check=(F(0),)
    for w,c in zip(weights,cols):check=pa(check,pm((w,),c))
    if check!=p:raise Unsupported('Partial fraction identity failed')
    return weights


def rational_basis_sum(p,poles,phase,s,theory):
    """Keep one finite upper cutoff for all harmonic contributions before passing to the limit."""
    from fractions import Fraction as F
    weights=_fraction_weights(p,poles)
    def sign(j):return -1 if phase and j%2 else 1
    correction=F(0);reduced={};terms=[]
    for w,(root,k,_) in zip(weights,poles):
        if not w:continue
        offset=s-root;rho=offset%1 or F(1);shift=int(offset-rho)
        if rho not in (F(1),F(1,2)):raise Unsupported('No registered sum on this residue class')
        weight=w*sign(s+shift)
        low=min(0,shift);high=max(0,shift)
        correction+=weight*(1 if shift<0 else -1)*sum(F(sign(j))/(j+rho)**k for j in range(low,high))
        reduced[rho,k]=reduced.get((rho,k),0)+weight
        terms.append(dict(pole=str(root),order=k,weight=str(w),origin=str(rho),shift=shift))
    if not phase and sum(w for (rho,k),w in reduced.items() if k==1):
        raise Unsupported('The harmonic divergence survives at the common cutoff')
    value=q(correction);remainders=[]
    for (rho,k),w in reduced.items():
        if not w:continue
        rule=theory.get(f'{phase}:{rho}:{k}')
        if rule is None:raise Unsupported('A canonical series value is required')
        constant=m.parse(rule,None,[]);value=m.add(value,m.mul(q(w),constant))
        remainders.append(dict(origin=str(rho),order=k,coefficient=str(w),regular_part=constant))
    return dict(start=s,phase=phase,partial_fractions=terms,finite_endpoint_adjustment=str(correction),
                common_cutoff_residues=remainders),m.simplify(value)

def _rational_poles(raw,name,start,guards):
    from graphs import nonzero_on_integer_tail
    from polynomial import rf
    poles=_linear_poles(raw,name)
    for relation,w in guards:
        if relation!='nonzero':raise Unsupported('Additional domain proof for the original term is required')
        for factor in rf(w,name):nonzero_on_integer_tail(factor,start)
    return poles


def _linear_poles(raw,name):
    from integrals import denominator_factors
    from polynomial import rf,pgcd,pdiv
    p,d=rf(raw,name)
    g=pgcd(p,d);p,d=pdiv(p,g)[0],pdiv(d,g)[0]
    poles=[]
    for factor in denominator_factors(raw,d,name):
        if len(factor)!=2:continue
        root=-factor[0]/factor[1];multiplicity=0;rest=d
        while len(rest)>1:
            rest,remainder=pdiv(rest,factor)
            if any(remainder):break
            multiplicity+=1;poles.append((root,multiplicity,rest))
    return p,d,poles


def _rational_difference(p,d,poles,name,start):
    """Solve R(k)−R(k+1)=p(k)/d(k) exactly, checking the denominator on the integer tail."""
    from fractions import Fraction as F
    from graphs import nonzero_on_integer_tail
    from integrals import polynomial_expression
    from polynomial import pgcd,pa,pm,pp,pdiv,span_coefficients
    def shifted(poly,step):
        result=(F(0),)
        for c in reversed(poly):result=pa(pm(result,(F(step),F(1))),(c,))
        return result
    def difference(left,right):return pa(left,tuple(-v for v in right))
    b=pgcd(d,shifted(d,-1));orbits={}
    for root,multiplicity,_ in poles:
        orbits.setdefault(root%1,[]).append((root,multiplicity))
    for orbit in orbits.values():
        low=min(r for r,k in orbit);high=max(r for r,k in orbit);power=max(k for r,k in orbit)
        for j in range(1,int(high-low)+1):
            factor=pp((-low-j,F(1)),power);b=pm(b,pdiv(factor,pgcd(b,factor))[0])
    b1=shifted(b,1);columns=[]
    for i in range(len(b)-1):
        term=(F(0),)*i+(F(1),)
        columns.append(pm(d,difference(pm(term,b1),pm(shifted(term,1),b))))
    target=pm(p,pm(b,b1));a=span_coefficients(target,columns)
    if a is None:return None
    a=tuple(a) or (F(0),)
    if any(difference(pm(d,difference(pm(a,b1),pm(shifted(a,1),b))),target)):
        raise AssertionError('Invalid antidifference polynomial identity')
    g=pgcd(a,b);a,b=pdiv(a,g)[0],pdiv(b,g)[0];nonzero_on_integer_tail(b,start)
    return m.div(polynomial_expression(a,name),polynomial_expression(b,name))


def rational_sum_potential(raw,variable,start):
    """Find the forward-difference witness from the summand alone on k≥start."""
    p,d,poles=_rational_poles(raw,variable,start,domain_conditions(raw))
    potential=_rational_difference(p,d,poles,variable,start)
    if potential is None:raise Unsupported('No rational difference was found for the summand')
    return potential


def rational_series_sum(task,library,request,saved=None):
    """Recover R(n) from the exact rational identity a(n)=R(n)-R(n+1)."""
    from polynomial import NotRational
    fields={'kind','id','source','term','index','start_index','index_domain','parameters','stated_conditions','method_requirement','requested_output'}
    if isinstance(task.get('hint'),str):fields.add('hint')
    name=task['index'];start=task['start_index'];method=task.get('method_requirement')
    source_info=task.get('source',{})
    if not isinstance(source_info,dict) or set(source_info)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','page_png_sha256',
                                                        'literal_requirement','printed_instruction','explicit_required_method'}:
        raise Unsupported('Unbound series source requirement')
    explicit=source_info.get('explicit_required_method')
    if explicit is not None:
        if explicit not in ('telescoping','partial_fractions') or method not in (None,explicit):
            raise Unsupported('The source summation method has no matching proof plan')
        method=explicit
    direct=False
    for raw_requirement in (source_info[k] for k in ('literal_requirement','printed_instruction') if k in source_info):
        if not isinstance(raw_requirement,str):raise Unsupported('Invalid printed series requirement')
        optional=re.fullmatch(r'(.+?)[.;]\s*указание\s*:\s*([^.;!?]+)\.?',raw_requirement.strip(),re.I)
        if optional and not re.search(r'\b(?:необходимо|обязательно|требуется|также доказать)\b',optional[2],re.I):
            raw_requirement=optional[1]
        main=raw_requirement.strip().rstrip('.').casefold()
        goal,separator,prescribed=main.partition(' by ')
        if goal=='доказать непосредственно сходимость следующих рядов и найти их суммы':direct=True
        elif goal not in ('найти сумму ряда','найти сумму исходного ряда','доказать сходимость и найти сумму'):
            raise Unsupported('The printed series requirement needs an explicit proof')
        if separator:
            source_method={'telescoping':'telescoping','partial fractions':'partial_fractions'}.get(prescribed)
            if source_method is None or method not in (None,source_method):
                raise Unsupported('Не подтверждён метод суммирования из исходного условия: '+prescribed)
            method=source_method
    theory=library.data.get('rational_series_constants',{})
    if (set(task)-fields or library.data.get('task_compilers',{}).get(task['kind']) not in ('telescoping_antidifference','exact_rational_series') or type(start)!=int
            or task.get('index_domain','integers_from_start')!='integers_from_start' or method not in (None,'telescoping','partial_fractions') or method=='partial_fractions' and not theory
            or task.get('requested_output',['sum']) not in (['sum'],['convergence_and_sum'])):
        raise Unsupported('Additional series parameters, domain or summation obligations remain')
    if library.data.get('geometric_series_tail') and method is None and re.search(r'\b(sin|cos|periodic_sign|floor)\s*\(',task['term']):
        from finite_sums import geometric_series_certificate
        try:return geometric_series_certificate(task)
        except Unsupported:pass
    if library.data.get('translated_series_difference') and method in (None,'telescoping') and re.search(r'\b(sqrt|ln|cbrt)\s*\(',task['term']):
        from finite_sums import shifted_series_certificate
        try:return shifted_series_certificate(task,request)
        except Unsupported:pass
    if library.data.get('factorial_polynomial_series') and re.search(r'\bfactorial\s*\(',task['term']) and method is None and not direct:
        from finite_sums import factorial_weighted_sum
        return factorial_weighted_sum(task,saved)
    params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    m.context({'variable':name,'parameters':params});raw=m.parse(task['term'],name,params);n=('v',name)
    def endpoint_limit(expr,parameters=()):
        return freeze(request('limit of the upper partial-sum endpoint',{'kind':'limit','expression':source(expr),'variable':name,
                    'parameters':list(parameters),'variable_domain':'positive_integers','approach':{'point':'+inf','side':'positive_infinity'}})['value'])
    if params or conditions:
        if method=='partial_fractions' or len(params)!=1 or conditions!=[params[0]+' is a natural number']:
            raise Unsupported('The parametric shift must be a fixed positive integer')
        h=('s',params[0]);local=['__tail','__shift','__j']
        while set(local)&{name,*params}:local=[v+'_' for v in local]
        j=('s',local[2]);ctx=m.context({'variable':name,'parameters':local})
        cone={n:m.add(q(start),m.power(('s',local[0]),2)),h:m.add(ONE,m.power(('s',local[1]),2))}
        def lattice_nonzero(p):
            from math import gcd,lcm
            if any(atom not in (n,h) for mon in p for atom,k in mon):return False
            common=lcm(*(c.denominator for c in p.values()))
            g=gcd(*(int(common*c) for mon,c in p.items() if mon));constant=int(common*p.get((),0))
            return constant%g!=0 if g else constant!=0
        def defined(e):
            if m.constant_defined(m.substitute(e,cone),ctx):return True
            for relation,w in domain_conditions(e):
                if known_guard((relation,m.substitute(w,cone)),ctx):continue
                if relation!='nonzero' or not all(lattice_nonzero(p) for p in m.rational_form(w)):return False
            return True
        if not defined(raw):raise Unsupported('An original index or parameter restriction remains')
        def leading(p):
            degree=max((dict(mon).get(n,0) for mon in p),default=-1)
            return degree,m.poly_expr({tuple((a,k) for a,k in mon if a!=n):c for mon,c in p.items() if dict(mon).get(n,0)==degree})
        pending=[raw];seen=set()
        while pending:
            base=pending.pop();pending.extend(c for c in base[1:] if isinstance(c,tuple))
            if base in seen or not m.contains(base,n):continue
            seen.add(base)
            bp,bq=m.rational_form(base)
            if leading(bp)[0]!=1 or leading(bq)[0]!=0:continue
            kernel=m.div(ONE,base)
            if not defined(kernel):continue
            delta=m.add(kernel,m.neg(m.substitute(kernel,{n:m.add(n,h)})))
            if delta==ZERO:continue
            numerator,denominator=m.rational_form(('div',raw,delta));dp,lp=leading(numerator);dq,lq=leading(denominator)
            if dp!=dq or lq==ZERO:continue
            scale=m.div(lp,lq)
            if not defined(scale) or m.rational_form(m.add(raw,m.neg(m.mul(scale,delta))))[0]:continue
            tail=m.substitute(kernel,{n:m.add(m.add(n,ONE),j)})
            if endpoint_limit(tail,[*params,j[1]])!=ZERO:continue
            summand=m.substitute(kernel,{n:m.add(q(start),j)})
            plan={'term':raw,'start':start,'positive_integer_shift':h,'coefficient':scale,'kernel':kernel,'boundary_index':j,
                  'lower_block_summand':summand,'upper_block_summand':tail,'limit':ZERO}
            return plan,{'finite_sum':{'index':j[1],'from':0,'to':m.add(h,q(-1)),'summand':summand},'coefficient':scale}
        raise Unsupported('No proved difference of kernels over the declared integer shift')
    if library.data.get('linear_series_prefixes') and raw[0]=='add' and method is None:
        from finite_sums import sum_factors
        # Sum the components separately only when each geometric envelope contracts.
        try:contracting=all(abs(sum_factors(part,name,'__upper',start)[2])<1 for part in raw[1:])
        except (NotRational,Unsupported):contracting=False
        if contracting:
            children=[]
            for part in raw[1:]:
                child=dict(kind='series_sum',term=source(part),index=name,start_index=start,
                           source={'printed_instruction':'Доказать непосредственно сходимость следующих рядов и найти их суммы.'} if direct else {})
                val=freeze(request('finite sum and limit for the additive term',child)['value'])
                if not isinstance(val,tuple) or not m.constant_defined(val,m.context({'variable':name})):
                    raise Unsupported('A separate finite series sum is needed for each term')
                children.append(val)
            return dict(index=name,start=start,linear_limits=children),m.simplify(m.add(*children))
    extra=[];phase,r=phase_integer(raw,name,extra) if theory and method!='telescoping' else (0,raw)
    guards=extra+domain_conditions(r)
    upper='upper' if name!='upper' else 'bound'
    try:p,d,poles=_rational_poles(r,name,start,guards)
    except NotRational:
        if not library.data.get('finite_sum_formula') or method=='partial_fractions':raise
        question=prefix_question(task['term'],name,upper,start)
        plan,value=prefix_limit(question,name,False,request)
        if isinstance(value,(dict,str)):raise Unsupported('A convergent series requires a finite partial-sum limit')
        return {'index':name,'finite_prefix_limit':plan},value
    potential=None if phase or method=='partial_fractions' else _rational_difference(p,d,poles,name,start)
    if potential is None:
        if direct or not theory or method=='telescoping' or len(p)>=len(d):raise Unsupported('No proper rational sum in the selected method')
        return rational_basis_sum(p,poles,phase,start,theory)
    tail=m.substitute(potential,{n:m.add(n,ONE)})
    initial=m.simplify(m.substitute(potential,{n:q(start)}))
    partial=m.add(initial,m.neg(tail))
    if library.data.get('finite_sum_formula') and r==raw:
        # The common child receives only the summand and integer bounds. Its formula
        # supplies the endpoint-limit question; the series verifier also checks the binding.
        from finite_sums import rational_on_tail
        from polynomial import pm
        question=prefix_question(task['term'],name,upper,start)
        child=request('closed form of the finite partial sum',question)['value']
        branches=child['branches']
        if len(branches)!=1 or branches[0]['indices']!='all':
            raise Unsupported('A single rational prefix formula on the integer tail is required')
        prefix=m.substitute(m.parse(branches[0]['expression'],'N'),{('v','N'):n})
        left,ld=rational_on_tail(prefix,name,child['valid_from'])
        right,rd=rational_on_tail(partial,name,child['valid_from'])
        if pm(left,rd)!=pm(right,ld):
            raise Unsupported('The finite prefix does not match the recovered telescoping difference')
        value=endpoint_limit(prefix)
        if isinstance(value,str):raise Unsupported('The rational partial sums need a finite limit')
        return {'term':raw,'start':start,'original_domain_guards':guards,'antidifference':potential,'tail':tail,
                'finite_partial_sum':prefix,'partial_sum_limit':value,'limit':m.simplify(m.add(initial,m.neg(value)))},value
    limit=endpoint_limit(tail)
    if isinstance(limit,str):raise Unsupported('A finite terminal value is required')
    return {'term':raw,'start':start,'original_domain_guards':guards,'antidifference':potential,'tail':tail,
            'finite_partial_sum':partial,'limit':limit},m.simplify(m.add(initial,m.neg(limit)))


def series_outputs(task):
    wanted=task.get('requested_output',['convergence_classification'])
    printed=task.get('source',{})
    if not isinstance(wanted,(list,tuple)) or not all(isinstance(w,str) for w in wanted):
        raise Unsupported('Invalid requested series outputs')
    required=task.get('method_requirement')
    if not isinstance(printed,dict) or any(printed.get(k) not in (None,required)
            for k in ('explicit_imposed_method','explicit_required_method','method_requirement')):
        raise Unsupported('A printed criterion is missing from the series goal')
    return wanted


def series_candidates(task,library):
    wanted=series_outputs(task)
    methods=tuple(library.data.get('series_log_tests',()))
    required=task.get('method_requirement')
    if library.data.get('product_ratio_expansion') and re.search(r'\b(prod|factorial)\s*\(',str(task.get('term',''))):
        yield 'product_ratio_expansion'
    if library.data.get('exceptional_comparison') and re.search(r'\b(prod|piecewise)\s*\(',str(task.get('term',''))):
        yield 'exceptional_comparison'
    if library.data.get('periodic_integral_comparison') and re.search(r'\b(sin|cos|integral)\s*\(',str(task.get('term',''))):
        yield 'periodic_series'
    if (library.data.get('alternating_rational_series') and required in (None,'general_convergence_tests','leibniz_test')
            and re.search(r'\(\s*-\s*1\s*\)\s*(?:\^|\*\*)',str(task.get('term','')))):
        try:compile_series_comparison(task,'alternating_rational')
        except Unsupported:pass
        else:
            yield 'alternating_rational'
            return
    if re.search(r'\bfactorial\s*\(',str(task.get('term',''))):
        if library.data.get('integer_factorial_ratio') and required in ('ratio_test','general_convergence_tests','comparison_or_ratio_or_root'):yield 'factorial_ratio'
        return
    if required in ('ratio_test','root_test'):
        if required in methods:yield required
        return
    if set(wanted).intersection({'absolute_convergence','conditional_convergence'}):
        return  # The global classification goal handles absolute and ordinary convergence separately.
    if 'asymptotic_order' in (task.get('requested_output') or []):
        yield from SERIES_POWERS
        return
    term=compile_series_comparison(task,SERIES_POWERS[0])['term_ast']
    def variable_exponent(raw):
        return raw[0]=='rpow' and m.variable_in(raw[2]) or any(variable_exponent(c) for c in raw[1:] if isinstance(c,tuple))
    yield from (methods+SERIES_POWERS if variable_exponent(term) else SERIES_POWERS+methods)


def integer_term_ratio(term,n,start,samples):
    """Remove multiplicative integer factorials, constructing their exact consecutive ratio."""
    from integrals import affine
    factors=[]
    def shifted(e):return m.substitute(e,{n:('add',n,ONE)})
    def real_power(base,exponent):
        f=m.num(exponent)
        if base==ONE:return ONE
        if f is not None and f.denominator==1 and abs(f)>m.MAX_INTEGER_POWER:raise Unsupported('Consecutive integer power exceeds scalar grammar bound')
        if f is None and m.num(base) is not None and m.num(base)>0:return ('exp',m.mul(exponent,('ln',base)))
        return m.power(base,int(f)) if f is not None and f.denominator==1 else ('rpow',base,exponent)
    def contains_factorial(e):
        return e[0]=='factorial' or any(contains_factorial(c) for c in e[1:] if isinstance(c,tuple))
    def walk(e):
        op=e[0]
        if op=='factorial':
            if not all(m.constant_defined(m.substitute(e[1],{n:point}),context) for point,context in samples):
                raise Unsupported('Raw factorial argument has an unproved source domain')
            a,b=map(m.num,affine(e[1],n[1]))
            if a is None or b is None or a.denominator!=1 or b.denominator!=1 or a<0 or a*start+b<0:
                raise Unsupported('Factorial requires a nonnegative integer affine argument at every original index')
            product={():1}
            for j in range(1,int(a)+1):
                product=m.mulp(product,{((n,1),):a,():b+j})
            quotient=m.poly_expr(product)
            factors.append((e[1],int(a),int(b),quotient))
            return ONE,quotient
        if op in ('mul','div','pow'):
            l,ratio=walk(e[1])
            if op=='pow':return (op,l,e[2]),m.power(ratio,e[2])
            r,other=walk(e[2])
            return (op,l,r),(m.mul if op=='mul' else m.div)(ratio,other)
        if contains_factorial(e):raise Unsupported('Nonmultiplicative factorial requires a different discrete argument')
        if op=='rpow':
            base,p=e[1:];next_base=m.simplify(shifted(base));delta=m.add(shifted(p),m.neg(p))
            return e,m.mul(real_power(next_base,delta),real_power(m.div(next_base,base),p))
        return e,m.div(shifted(e),e) if m.variable_in(e) else ONE
    try:ordinary,ratio=walk(term)
    except ZeroDivisionError as exc:raise Unsupported('Consecutive ratio contains an undefined source factor') from exc
    if not factors:raise Unsupported('Missing discrete factorial')
    return ordinary,ratio,tuple(factors)


def alternating_rational_plan(raw,index,start):
    """Separate an integral alternating phase, keeping every original rational divisor."""
    from graphs import nonzero_on_integer_tail
    from polynomial import rf, NotRational, Undefined, quotient_derivative_numerator
    n=('v',index)
    def separate(e):
        if e[0]=='rpow' and e[1] in (q(-1),('mul',q(-1),ONE)):
            # Restrict the exponent to a polynomial syntax with integral coefficients.
            if domain_conditions(e[2]):raise Unsupported('The original phase has an unproved domain')
            p,d=rf(e[2],index)
            if d!=(1,) or len(p)>2 or any(c.denominator!=1 for c in p):
                raise Unsupported('An integral affine phase is required')
            return int(p[1])%2 if len(p)==2 else 0, q((-1)**(int(p[0])%2))
        if e[0] in ('mul','div'):
            left,a=separate(e[1]);right,b=separate(e[2])
            return left^right,(e[0],a,b)
        return 0,e
    try:
        alternate,amplitude=separate(raw)
        if not alternate:raise Unsupported('The sign must alternate between successive integer indices')
        guards=domain_conditions(amplitude)
        for relation,guard in guards:
            if relation!='nonzero':raise Unsupported('A nonrational domain guard remains')
            for p in rf(guard,index):nonzero_on_integer_tail(p,start)
        p,d=rf(amplitude,index)
        nonzero_on_integer_tail(d,start)
        h=quotient_derivative_numerator(p,d)
    except (NotRational,Undefined,ZeroDivisionError) as exc:
        raise Unsupported('A rational amplitude with defined coefficients is required') from exc
    # Beyond this Cauchy bound each nonzero polynomial has the sign of its leading coefficient.
    threshold=max([start]+[2+int(max((abs(c/poly[-1]) for c in poly[:-1]),default=0))
                           for poly in (p,d,h) if any(poly)])
    gap=len(d)-len(p) if any(p) else 0
    coefficient=p[-1]/d[-1]
    if gap>0 and h[-1]*coefficient>=0:raise Unsupported('Eventual decrease of the absolute amplitude was not established')
    scaled=amplitude if gap==0 else ('mul',('pow',n,gap),amplitude)
    child=dict(kind='limit',expression=source(scaled),variable=index,variable_domain='positive_integers',
               approach={'point':'+inf','side':'positive_infinity'})
    return dict(criterion='alternating_rational',index=index,start_index=start,term_ast=raw,
                amplitude=amplitude,degree_gap=gap,coefficient=q(coefficient),threshold=threshold,
                derivative_numerator=tuple(map(q,h)),domain_guards=guards,scaled_limit_task=child)


def compile_series_comparison(task,power):
    series_outputs(task)
    fields={'kind','term','index','start_index','index_domain','parameters','stated_conditions','method_requirement','requested_output','schema','id','source','transcription'}
    if not isinstance(task,dict) or set(task)-fields or task.get('kind')!='series_convergence':raise Unsupported('Unknown series source fields')
    power=freeze(power)
    log_test=power in ('root_test','ratio_test','factorial_ratio')
    alternating=power=='alternating_rational'
    if power=='exceptional_comparison':
        from finite_sums import exceptional_series_comparison
        return exceptional_series_comparison(task)
    if power=='product_ratio_expansion':
        from finite_sums import product_series_ratio
        if type(task.get('start_index')) is not int or task['start_index']<1 or task.get('index_domain','integers')!='integers':
            raise Unsupported('The positive integer range is required')
        return product_series_ratio(task)
    if not (power=='periodic_series' or alternating or log_test or power in SERIES_POWERS):raise Unsupported('Unadmitted comparison exponent')
    start=task.get('start_index');index=task.get('index')
    if type(start) is not int or start<1 or task.get('index_domain','integers')!='integers':raise Unsupported('Series start must be a literal positive integer')
    if power=='periodic_series':
        from quadrature import periodic_series_plan
        return periodic_series_plan(task)
    method='ratio_test' if power=='factorial_ratio' else power
    if alternating:
        outputs={'convergence_classification','absolute_convergence','conditional_convergence','justification'}
        required=task.get('requested_output',['convergence_classification'])
        if (task.get('method_requirement') not in (None,'general_convergence_tests','leibniz_test') or
                task.get('parameters') or task.get('stated_conditions') or not isinstance(required,(list,tuple)) or
                set(required)-outputs):raise Unsupported('Unsupported alternating series requirements')
        m.context({'variable':index})
        plan=alternating_rational_plan(m.parse(task['term'],index),index,start)
        if task.get('method_requirement')=='leibniz_test' and plan['degree_gap']<=0 and plan['coefficient']!=ZERO:
            raise Unsupported('The alternating convergence criterion needs a null amplitude')
        return plan
    if task.get('method_requirement') not in ('general_convergence_tests','comparison_or_ratio_or_root') and not (log_test and task.get('method_requirement')==method):raise Unsupported('Unimplemented series method')
    requested=task.get('requested_output',[])
    if not isinstance(requested,(list,tuple)) or set(requested)-{'convergence_classification','justification','asymptotic_order'}:raise Unsupported('Series sums/partial sums or unknown output are not admitted')
    params=task.get('parameters',[]);conditions=task.get('stated_conditions',[])
    if not isinstance(params,(list,tuple)) or any(not isinstance(p,str) and (not isinstance(p,dict) or set(p)-{'symbol','domain','independent_of'}) for p in params):raise Unsupported('Unknown series parameter conditions')
    if not isinstance(conditions,(list,tuple)) or not all(isinstance(c,str) for c in conditions):raise Unsupported('Invalid series source conditions')
    names=m.context({'variable':index,'parameters':params})['parameters'];n=('v',index)
    raw=m.parse(task['term'],index,names,('factorial',) if power=='factorial_ratio' else ())
    tail='__series_tail'
    while tail in names or tail==index:tail+='_'
    dummy='__series_dummy'
    while dummy in names+[index,tail]:dummy+='_'
    base=m.context({'variable':dummy,'parameters':names,'parameter_conditions':conditions})
    ctx=m.context({'variable':dummy,'parameters':names+[tail],'parameter_conditions':list(conditions)+[tail+'>0']})
    samples=((q(start),base),(('add',q(start),('s',tail)),ctx))
    factors=();e=raw
    if power=='factorial_ratio':e,ratio,factors=integer_term_ratio(raw,n,start,samples)
    initial,ray=(m.substitute(e,{n:point}) for point,_ in samples)
    def nonnegative(raw,context):
        return not m.variable_in(raw) and m.constant_defined(raw,context) and (m.sign(raw,context) in (0,1) or m.known_nonnegative(raw,context))
    signed=not (nonnegative(initial,base) and nonnegative(ray,ctx))
    if signed and (log_test or not all(m.constant_defined(expr,context) for expr,context in ((initial,base),(ray,ctx)))):
        raise Unsupported('The original term domain or logarithmic test positivity is unproved at some source indices')
    if log_test:
        def positive(raw):
            return all(m.sign(m.substitute(raw,{n:point}),context)==1 for point,context in samples)
        if not positive(e) or 'asymptotic_order' in requested:raise Unsupported('Logarithmic series test requires strict positivity and a classification goal')
        def logarithm(raw):
            op=raw[0]
            if op=='exp':return raw[1]
            if op=='rpow' or op=='pow' and positive(raw[1]):
                return ('mul',raw[2] if op=='rpow' else q(raw[2]),logarithm(raw[1]))
            if op in ('mul','div') and all(positive(v) for v in raw[1:]):
                right=logarithm(raw[2])
                return ('add',logarithm(raw[1]),right if op=='mul' else ('mul',q(-1),right))
            return ('ln',raw)
        loga=logarithm(e)
        scaled=('ln',ratio) if factors else m.simplify(('div',loga,n) if power=='root_test' else ('add',m.substitute(loga,{n:('add',n,ONE)}),('mul',q(-1),loga)))
    else:
        exponent=m.num(power);weight=('pow',n,int(exponent)) if exponent.denominator==1 else ('pow',('sqrt',n),exponent.numerator)
        scaled=('mul',weight,e)
    child={'kind':'limit','expression':source(scaled),'variable':index,'parameters':params,
           'parameter_conditions':list(conditions),'variable_domain':'positive_integers','approach':{'point':'+inf','side':'positive_infinity'}}
    return {**({'criterion':power} if log_test else {'power':freeze(power)}),**({'signed_comparison':True} if signed else {}),**({'integer_factorial_shifts':factors,'successive_ratio':ratio} if factors else {}),
            'term_ast':raw,'start_index':start,'index':index,'initial_term':initial,'initial_context':base,
            'tail_term':ray,'tail_context':ctx,'tail_parameter':tail,'scaled_limit_task':child,
            'order_requested':'asymptotic_order' in requested,'positivity_scope':
                'Factorials are positive only at proved nonnegative integer arguments for every integer N>=start; the remaining factor is checked at start and start+t for arbitrary t>0.' if factors else
                'N=start or N=start+t, arbitrary fixed real t>0; no running variable in either guard expression'}


def series_comparison_conclusion(plan,child):
    if child.get('status')!='SOLVED':raise Unsupported('Comparison limit is not completely proved')
    if plan.get('criterion')=='exceptional_comparison':
        from fractions import Fraction
        from quadrature import enclose
        value=freeze(child['value'])
        result=dict(criterion=plan['criterion'],classification='convergent',absolute_convergence=True,conditional_convergence=False)
        if plan['strategy']=='uniform_factor_bound':
            if value!=ONE:raise Unsupported('The polynomial multiplier changed the majorant ratio')
        elif plan['strategy']=='sparse_subseries':
            if not isinstance(value,tuple) or not m.constant_defined(value,m.context(dict(variable=plan['index']))):
                raise Unsupported('No finite bound for both scaled subseries')
        else:
            if not isinstance(value,tuple):raise Unsupported('The product multiplier has no finite limit')
            lo,hi=enclose(value,None)
            magnitude=max(abs(lo),abs(hi))
            if magnitude>=1:raise Unsupported('The limiting factor is not strictly inside the unit interval')
            rho=Fraction(1,2)
            while rho<=magnitude:rho=(1+rho)/2
            result['tail_factor_bound']=q(rho)
        return dict(status='SOLVED',value=result)
    if plan.get('criterion')=='product_ratio_expansion':
        from verify import same_value
        expected=q(1,3) if plan['index_dependent_powers'] or plan['root_factors'] else q(-1,2)
        if not same_value(child['value'],expected):raise Unsupported('The logarithmic remainder was not established')
        value=dict(criterion='product_ratio_expansion',classification=plan['classification'])
        if plan['classification']=='parameter_dependent':
            value.update(exponent=plan['log_coefficient'],convergent_if='exponent < -1',divergent_if='exponent >= -1')
        else:value['absolute_convergence']=plan['classification']=='convergent'
        if plan['terminating_if']:
            value=dict(classification='parameter_dependent',convergent_if_any_integer_root=plan['terminating_if'],otherwise=value)
        return dict(status='SOLVED',value=value)
    if plan.get('criterion')=='periodic_series':
        value=child['value']['convergence']
        if value not in ('convergent','divergent'):raise Unsupported('The amplitude integral is unresolved')
        absolute=value=='convergent' or plan.get('zero_sequence',False)
        conditional=not absolute and plan.get('zero_mean',False) and plan.get('tends_to_zero',False)
        return {'status':'SOLVED','value':dict(criterion='periodic_series',absolute_convergence=absolute,
                conditional_convergence=conditional,classification='convergent' if absolute or conditional else 'divergent')}
    if plan.get('criterion')=='alternating_rational':
        from verify import same_value
        if not same_value(freeze(child['value']),freeze(plan['coefficient'])):
            raise Unsupported('The power comparison did not give the leading coefficient')
        zero=freeze(plan['coefficient'])==ZERO
        absolute=zero or plan['degree_gap']>1
        conditional=not zero and plan['degree_gap']==1
        return {'status':'SOLVED','value':dict(criterion=plan['criterion'],absolute_convergence=absolute,
                conditional_convergence=conditional,classification='convergent' if absolute or conditional else 'divergent')}
    if 'criterion' in plan:
        value=freeze(child['value'])
        sign=1 if value=='+inf' else -1 if value=='-inf' else m.sign(value,plan['initial_context'])
        if sign not in (-1,1):raise Unsupported('The logarithmic criterion limit has no strict sign')
        return {'status':'SOLVED','value':{'classification':'convergent' if sign<0 else 'divergent','criterion':plan['criterion'],'log_limit':value}}
    value=freeze(child['value']);p=m.num(plan['power']);nonzero=False;classification=None
    if value in ('+inf','-inf') and p<=1:classification='divergent'
    elif value not in ('+inf','-inf') and m.constant_defined(value,plan['initial_context']):
        nonzero=m.sign(value,plan['initial_context']) in (-1,1)
        if p>1:classification='convergent'
        elif nonzero:classification='divergent'
    if classification is None:raise Unsupported('This scaled limit gives no admitted comparison conclusion')
    answer={'classification':classification,'comparison_power':plan['power'],'scaled_limit':value,'criterion':'positive p-series comparison; p=0 compares with the constant series'}
    if plan.get('signed_comparison'):
        answer['criterion']='finite scaled limit bounds the modulus; a nonzero signed or infinite limit gives a constant sign on a tail'
    if plan['order_requested']:answer['asymptotic_order']={'power':plan['power'],'equivalent_coefficient':value} if nonzero else None
    return {'status':'SERIES_ORDER_PENDING' if plan['order_requested'] and not nonzero else 'SOLVED','value':answer}


def structural_degree(e,coordinates,fixed_context):
    zero=m.num(ZERO);op=e[0]
    if op in ('q','pi'):return zero
    if op=='s':return m.num(ONE) if e[1] in coordinates else zero
    if op in ('add','mul','div'):
        a=structural_degree(e[1],coordinates,fixed_context);b=structural_degree(e[2],coordinates,fixed_context)
        if op=='add':
            if a!=b:raise Unsupported('Addition has unequal structural degrees')
            return a
        return a+b if op=='mul' else a-b
    if op=='pow':return structural_degree(e[1],coordinates,fixed_context)*e[2]
    if op in ('sqrt','cbrt'):return structural_degree(e[1],coordinates,fixed_context)/(2 if op=='sqrt' else 3)
    if op=='rpow':
        a=structural_degree(e[1],coordinates,fixed_context);b=structural_degree(e[2],coordinates,fixed_context)
        if a==b==0:return zero
        exponent=m.num(m.simplify(e[2])) if m.constant_defined(e[2],fixed_context) else None
        if b!=0 or exponent is None:raise Unsupported('Nonzero-degree base requires a numeric fixed exponent')
        return a*exponent
    if op in m.FUNCTIONS and structural_degree(e[1],coordinates,fixed_context)==0:return zero
    raise Unsupported('No admitted structural homogeneity rule')


def compile_euler_homogeneity(task):
    fields={'kind','function','variables','parameters','stated_conditions','method_requirement','requested_output','schema','id','source','transcription'}
    if not isinstance(task,dict) or set(task)-fields or task.get('kind')!='euler_homogeneity':raise Unsupported('Unknown Euler source fields')
    if task.get('method_requirement')!='partial_derivatives_and_scaling' or set(task.get('requested_output',[]))-{'homogeneity_degree','euler_identity'}:raise Unsupported('Unimplemented Euler method or output')
    child={k:task[k] for k in ('function','variables','parameters','stated_conditions') if k in task}
    child.update(kind='partial_derivatives',derivative_orders=[1],method_requirement='table_and_rules',requested_output=['first_partial_derivatives'])
    partial=compile_partial_bundle(child);variables=partial['variables'];names=list(variables)+partial['parameters'];dummy='__euler_dummy'
    while dummy in names:dummy+='_'
    fixed=m.context({'variable':dummy,'parameters':partial['parameters'],'parameter_conditions':list(partial['stated_conditions'])})
    common=m.parse(task['function'],None,names);degree=q(structural_degree(common,set(variables),fixed))
    guards=tuple((r,e,q(structural_degree(e,set(variables),fixed))) for r,e in partial['natural_domain'])
    ctx=m.context({'variable':dummy,'parameters':names,'parameter_conditions':list(partial['stated_conditions'])+[guard_source(g) for g in partial['domain_guards']]})
    if not all(known_guard((r,e),ctx) for r,e,_ in guards):raise Unsupported('Original domain boundary coverage remains unresolved')
    vectors=[(ZERO,)*len(variables),(ONE,)*len(variables),tuple(q(i+1) for i in range(len(variables)))]+[tuple(ONE if i==j else ZERO for i in range(len(variables))) for j in range(len(variables))]
    witness=next((v for v in vectors if m.constant_defined(m.substitute(common,{('s',name):x for name,x in zip(variables,v)}),fixed)),None)
    if witness is None:raise Unsupported('No proved nonempty original domain for every admitted parameter tuple')
    return {'degree':degree,'function_ast':common,'variables':variables,'natural_domain':partial['natural_domain'],
            'conic_guard_degrees':guards,'source_context':ctx,'nonempty_witness':witness,'partial_task':child,
            'scaling_scope':'For every positive real t and X in original D: tX is in D and f(tX)=t^degree*f(X)'}


def euler_conclusion(plan,child):
    from verify import same_value
    if child.get('status')!='SOLVED' or len(child.get('value',()))!=len(plan['variables']):raise Unsupported('First partial bundle is incomplete')
    lhs=ZERO
    for coordinate,partial in zip(plan['variables'],child['value']):lhs=('add',lhs,('mul',('s',coordinate),freeze(partial)))
    rhs=('mul',plan['degree'],plan['function_ast'])
    if not m.constant_defined(lhs,plan['source_context']) or not m.constant_defined(rhs,plan['source_context']):raise Unsupported('Raw Euler sides do not cover all original D')
    if not same_value(lhs,rhs):raise Unsupported('Exact Euler identity not established')
    return {'homogeneity_degree':plan['degree'],'euler_lhs':lhs,'euler_rhs':rhs,'original_domain':plan['natural_domain'],'scaling_scope':plan['scaling_scope']}
