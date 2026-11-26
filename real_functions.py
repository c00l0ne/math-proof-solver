"""Certificates constructed from real-function goals, with explicit domains and branches."""
import re
from fractions import Fraction as F
from math import ceil

import expressions as m
import intervals as line
import polynomial as poly
from model import ZERO, ONE, Unsupported, q

KINDS=frozenset({'composition_continuity','inverse_function_branches','parameter_curve_function','uniform_error_tolerance'})
STRUCTURED_FUNCTION_KINDS=frozenset({'inverse_function_and_domain','recover_function_by_substitution',
    'recover_function_on_inner_image','function_compositions','iterated_rational_composition',
    'composition_domain','iterate_function_formula'})
SOURCE_FIELDS={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page',
               'pdf_sha256','page_png_sha256','printed_hint'}
BASE={'kind','id','source','requested_output'}
NAME=r'[A-Za-z][A-Za-z0-9_]*'
PROOF=['proof']


def unsupported(message):
    raise Unsupported(message)


def fields(task,parameters,outputs,supported_hint=None):
    provenance=task.get('source',{})
    if (set(task)-BASE-set(parameters) or not isinstance(provenance,dict) or set(provenance)-SOURCE_FIELDS
            or task.get('requested_output',PROOF)!=outputs
            or provenance.get('printed_hint') not in (None,supported_hint)):
        unsupported('A source condition, output, or required method is not bound')


def nodes(e):
    yield e
    for a in e[1:]:
        if isinstance(a,tuple):yield from nodes(a)


def normal(text):
    for a,b in [('−','-'),('²','^2'),('³','^3'),('π','pi'),('sgn','sign'),('arctg','atan'),('arcsin','asin'),('arccos','acos')]:
        text=text.replace(a,b)
    text=re.sub(r'\bch\s+([a-z])\b',r'cosh(\1)',text)
    text=re.sub(r'\bsh\s+([a-z])\b',r'sinh(\1)',text)
    text=re.sub(r'\b(?:sin|cos|tan|cot|asin|acos|atan|sign)\s+([a-z])\b',
                lambda n:n[0].split()[0]+'('+n[1]+')',text)
    return re.sub(r'(?<=[0-9)])(?=[A-Za-z(])','*',text)


def source_view(task):
    text=task.get('statement')
    return text.strip().removesuffix('.') if isinstance(text,str) else ''


def routing(task,kind):
    if remaining_function_head(task,kind):return True
    if kind in KINDS|STRUCTURED_FUNCTION_KINDS:return True
    if kind!='proof_about_real_functions':return False
    if set(task)-BASE-{'statement'}:return False
    if match_interval_closure(task.get('statement')):return True
    text=source_view(task)
    return any(regex.fullmatch(text) for regex in ABSTRACT) or any(
        regex.fullmatch(text) for regex in (INVERSE_TEXT, MAPPED_CURVE, FUNCTION_EQUATION, DIFFERENCE,
                                           CLAMP_TEXT, COMPLEX_LAW, SIGN_LAW,*UNIFORM_TEXT))


def certificate(lib,rule,assumptions,conclusion,*steps,**evidence):
    if rule not in lib.data.get('real_function_transitions',()):
        unsupported('The needed real-function transition is absent')
    return dict(theorem='real_function.'+rule, assumptions=assumptions,
                argument=steps, **evidence), conclusion


def term(text,x):
    return m.parse(normal(text),x,extra_functions={'floor','sign'})


def affine_in(e,atom,variable):
    result=poly.rf(m.substitute(e,{atom:('v',variable)}),variable)
    p,d=result
    return (p[1]/d[0],p[0]/d[0]) if len(p)==2 and len(d)==1 else None


def step_compositions(task,lib):
    from graphs import domain_partition
    from tasks import domain_conditions
    from verify import same_value
    fields(task,{'f','g','variable'},['continuity_of_f_after_g','continuity_of_g_after_f'])
    x=task['variable'];v=('v',x);f,g=(term(task[k],x) for k in ('f','g'))
    results={}
    for key,outer,inner in (('f_after_g',f,g),('g_after_f',g,f)):
        raw=m.substitute(outer,{v:inner})
        if raw[0]=='sign':
            e=raw[1]
            guards=domain_conditions(e)
            if guards:unsupported('The sign composition has additional domain cuts')
            if same_value(e,m.add(ONE,m.add(v,m.neg(('floor',v))))):
                results[key]=dict(formula=ONE, continuous=True, source=raw, inner_range=(ONE,q(2),True,False))
                continue
            p,_=poly.rf(e,x)
            nonzero,full=domain_partition(x,(('nonzero',e),))
            positive,positive_set=domain_partition(x,(('positive',e),))
            if not any(p):
                results[key]=dict(formula=ZERO, continuous=True, source=raw)
                continue
            cuts=nonzero['cuts']
            if not cuts:
                value=m.sign(m.substitute(e,{v:ZERO}),{})
                if value not in (-1,1):unsupported('Unresolved sign on the linear component')
                results[key]=dict(formula=q(value), continuous=True, source=raw)
                continue
            signs=tuple(1 if positive_cell else -1 for positive_cell in positive['open_cells'])
            traces=tuple(dict(point=z,left=signs[i],right=signs[i+1],value=0,
                              classification='jump' if signs[i]!=signs[i+1] else 'removable')
                         for i,z in enumerate(cuts))
            results[key]=dict(source=raw,continuous=False,zero_traces=traces,nonzero_cells=full,
                              positive_cells=positive_set)
        elif inner==('sign',v):
            original=tuple(m.substitute(outer,{v:q(j)}) for j in (-1,0,1))
            def integer_floors(y):
                replacements={}
                for item in nodes(y):
                    if item[0]=='floor':
                        value=m.num(m.simplify(item[1]))
                        if value is None:unsupported('A floor value on the sign range is not resolved')
                        replacements[item]=q(value//1)
                return m.substitute(y,replacements)
            evaluated=tuple(map(integer_floors,original))
            if any(m.variable_in(y) or not m.constant_defined(y,{}) for y in evaluated):
                unsupported('The outer function must be defined at all three sign values')
            values=tuple(map(m.simplify,evaluated))
            left,at,right=values
            category='continuous' if left==at==right else 'removable' if left==right else 'jump'
            results[key]=dict(source=raw,continuous=category=='continuous',classification=category,
                              point=ZERO, traces=values)
        else:
            unsupported('A general step substitution or certified sign partition is required')
    return certificate(lib,'compose_by_sign_cells',dict(functions=(f,g),variable=x),results,
        'Pull the step boundaries back to the original input and evaluate all resulting cells.',
        'Compare both side values and the original point value at each boundary.')


def inverse_branches(task,lib,request):
    from tasks import domain_conditions
    fields(task,{'function','variable'},['all_maximal_continuous_inverse_branches'])
    x=task['variable'];v=('v',x);e=term(task['function'],x)
    if not re.fullmatch(NAME,x):unsupported('A named input variable is required')
    y='z' if x!='z' else 'w';u=('v',y)
    def branch(domain,image,formula,index=None):
        data=dict(domain=domain,image=image,inverse=formula)
        if index is not None:data['index']=index
        return data
    def bound(a,b,cl,cr):return (a,b,cl,cr)
    full=bound('-inf','+inf',False,False)
    trigs={g for g in nodes(e) if g[0] in ('sin','cos','tan')}
    if len(trigs)==1:
        atom,=trigs
        a,b=affine_in(e,atom,y) or (0,0)
        c,d=affine_in(atom[1],v,y) or (0,0)
        trig=atom[0]
        if not a or not c:unsupported('Both scalar maps of a trigonometric branch must be nondegenerate affine maps')
        expected=domain_conditions(atom)
        if any(g not in expected for g in domain_conditions(e)):
            unsupported('A source hole lies away from the trigonometric pole partition')
        k=('s','j' if x!='j' else 'k');p=m.mul(k,m.PI);half=m.mul(q(1,2),m.PI)
        mv=m.div(m.add(u,q(-b)),q(a))
        orient=lambda low,high,closed:bound(low,high,closed,closed) if c>0 else bound(high,low,closed,closed)
        if trig=='cos':
            # One branch on every successive pi interval. Reflection changes the index parity.
            edge=lambda base:m.div(m.add(base,q(-d)),q(c))
            stage=m.mul(q(2),p)
            result=tuple(branch(orient(edge(m.add(stage,l)),edge(m.add(stage,r)),True),
                bound(q(b-abs(a)),q(b+abs(a)),True,True),
                m.div(m.add(m.add(stage,m.mul(q(sign),('acos',mv))),q(-d)),q(c)),'all integers '+k[1])
                for l,r,sign in ((m.neg(m.PI),ZERO,-1),(ZERO,m.PI,1)))
        elif trig=='sin':
            edge=m.div(m.add(p,q(-d)),q(c));step=m.div(half,q(c))
            result=(branch(orient(m.add(edge,m.neg(step)),m.add(edge,step),True),
                bound(q(b-abs(a)),q(b+abs(a)),True,True),
                m.div(m.add(m.add(p,m.mul(('integer_parity_sign',k),('asin',mv))),q(-d)),q(c)),
                'all integers '+k[1]),)
        else:
            edge=m.div(m.add(p,q(-d)),q(c));step=m.div(half,q(c))
            result=(branch(orient(m.add(edge,m.neg(step)),m.add(edge,step),False),full,
                m.div(m.add(m.add(p,('atan',mv)),q(-d)),q(c)),'all integers '+k[1]),)
        return certificate(lib,'trigonometric_inverse_cells',dict(source=e,variable=x,guards=expected),
            dict(output_variable=y,branches=result),
            'The elementary trigonometric function is bijective on each indicated principal monotonicity interval.',
            'Translate those intervals by integer phases and undo the two nonzero affine maps.',
            'Adjacent turning points prevent enlarging a sine or cosine interval. Tangent poles exclude both ends.',
            affine_maps=((q(a),q(b)),(q(c),q(d))))
    p,d=poly.rf(e,x)
    if domain_conditions(e):
        from graphs import domain_partition
        _,domain=domain_partition(x,domain_conditions(e),simplify_guards=True)
        if tuple(domain[1])!=(full,):
            unsupported('The rational source has an extra hole and cannot use unbroken monotonicity intervals')
    if len(p)==3 and len(d)==1:
        a,b,c=(p[2]/d[0],p[1]/d[0],p[0]/d[0]);tip=-b/(2*a);height=c-b*b/(4*a)
        root=('sqrt',m.div(m.add(u,q(-height)),q(a)))
        image=bound(q(height),'+inf',True,False) if a>0 else bound('-inf',q(height),False,True)
        branches=(branch(bound('-inf',q(tip),False,True),image,m.add(q(tip),m.neg(root))),
                  branch(bound(q(tip),'+inf',True,False),image,m.add(q(tip),root)))
        rule='quadratic_inverse_cells'
        evidence=dict(completed_square=(q(a),q(tip),q(height)))
        argument=('Complete the square to obtain a nonnegative radial coordinate.',
                  'On each side of the vertex this coordinate has one sign and the inverse is continuous.',
                  'Enlarging either interval crosses the turning point and creates two preimages.')
    elif len(p)==2 and p[0]==0 and len(d)==3 and d[1]==0 and d[0]*d[2]>0:
        a=p[1]/d[0];scale=d[2]/d[0];tip=('sqrt',q(1/scale));height=m.mul(q(abs(a)/2),tip)
        tr=m.div(u,q(a))
        radical=('sqrt',m.add(ONE,m.neg(m.mul(q(4*scale),m.power(tr,2)))))
        inner=m.div(m.mul(q(2),tr),m.add(ONE,radical))
        outer=m.div(m.add(ONE,radical),m.mul(q(2*scale),tr))
        left=bound(m.neg(height),ZERO,True,False);right=bound(ZERO,height,False,True)
        branches=(branch(bound('-inf',m.neg(tip),False,True),left if a>0 else right,outer),
                  branch(bound(m.neg(tip),tip,True,True),bound(m.neg(height),height,True,True),inner),
                  branch(bound(tip,'+inf',True,False),right if a>0 else left,outer))
        rule='reciprocal_quadratic_inverse_cells'
        evidence=dict(coefficients=(q(a),q(scale)),derivative_numerator=m.mul(q(a),m.add(ONE,m.neg(m.mul(q(scale),m.power(v,2))))),
                      discriminant=radical)
        argument=('The denominator is positive, and the derivative changes sign only at the two displayed turning points.',
                  'The left and right unbounded ends tend to zero, which belongs only to the middle branch.',
                  'Solve the quadratic in the input and rationalize the smaller root to keep its value at zero.',
                  'Branches cannot cross a turning point without losing injectivity.')
    else:
        unsupported('No certified monotonicity partition and inverse formula for this source')
    return certificate(lib,rule,dict(source=e,variable=x,original_guards=domain_conditions(e)),
                       dict(output_variable=y,branches=branches),*argument,**evidence)


def structured_function_source(task,kind,notes=()):
    meta={'source_number','source_exercise_number','source_subpart','source_edition','source_pdf_page',
          'source_pdf_pages','program_status','main_pass_status','deferred_reason','transcription_notes'}
    if (set(task)-BASE-meta-{'task_type','goal','assumptions','source_statement'} or task.get('assumptions')
            or task.get('transcription_notes') not in (None,[],list(notes)) or not isinstance(task.get('goal'),dict)
            or any(task[k]!=kind for k in ('kind','task_type') if k in task)
            or set(task.get('source',{}))-SOURCE_FIELDS or task.get('source',{}).get('printed_hint')):
        unsupported('There is an additional source obligation outside the structured function goal')
    return task['goal']


def source_intervals(domain):
    from graphs import interval_terms
    if domain in ('real_numbers','R'):return [('-inf','+inf',False,False)]
    hole=re.fullmatch(r'R\s*\\\s*\{(.+)\}|x!=(.+)',domain)
    if hole:
        z=m.parse(next(c for c in hole.groups() if c is not None),None)
        if m.num(m.simplify(z)) is None:unsupported('The puncture is not a fixed rational point')
        return [('-inf',m.simplify(z),False,False),(m.simplify(z),'+inf',False,False)]
    half=re.fullmatch(r'x([<>])(=?)(.+)',domain)
    if half:
        op,included,z=half.groups();return [interval_terms(('[' if included else '(')+z+',inf)',{}) if op=='>'
                                    else interval_terms('(-inf,'+z+(']' if included else ')'),{})]
    return [interval_terms(domain,{})]


def principal_inverse_pieces(text,domain):
    """Invert elementary monotone pieces and compute their exact images."""
    from graphs import graph_curve
    from ray_proofs import compare_scalar
    from tasks import domain_conditions,known_guard
    from verify import same_value
    x,y=('v','x'),('v','y');full=('-inf','+inf',False,False);ctx=m.context(dict(variable='x'))
    def before(a,b):
        if a==b:return 0
        if a=='-inf' or b=='+inf':return -1
        if a=='+inf' or b=='-inf':return 1
        return compare_scalar(a,b)
    def branch(bounds,image,inverse,rule):return dict(source=bounds,image=image,inverse=inverse,rule=rule)
    def arrange(a,b,lc,rc,orientation):return (a,b,lc,rc) if orientation>0 else (b,a,rc,lc)
    if text.startswith('piecewise(') and text.endswith(')'):
        if domain not in ('R','real_numbers'):unsupported('A separate restriction of the piecewise source is unresolved')
        chunks=text[10:-1].split(';');constraints=[];parts=[]
        for chunk in chunks:
            m0=re.fullmatch(r'\s*(.+?)\s+if\s*(.+)\s*',chunk)
            if not m0:unsupported('A piece has no complete displayed condition')
            expr,relation=m0.groups();between=re.fullmatch(r'(.+?)<=x<=(.+)',relation)
            if between:relation='['+between[1]+','+between[2]+']'
            src=source_intervals(relation)
            if len(src)!=1:unsupported('Each piece needs one fully bound interval')
            constraints.append(src[0]);parts.extend(principal_inverse_pieces(expr,relation))
        if constraints[0][0]!='-inf' or constraints[-1][1]!='+inf' or any(
            a[1]!=b[0] or a[3]==b[2] for a,b in zip(constraints,constraints[1:])):
            unsupported('The listed pieces do not partition the original line')
        for i,a in enumerate(parts):
            for b in parts[i+1:]:
                l,r,lc,rc=a['image'];u,v,uc,vc=b['image']
                p=before(r,u);q0=before(v,l)
                if not (p<0 or q0<0 or p==0 and not (rc and uc) or q0==0 and not (vc and lc)):
                    unsupported('Two source branches have overlapping images, so there is no single inverse')
        return parts
    source=source_intervals(domain)
    original,sep,definition=text.partition('=');e=term(original,'x')
    if e in (('sinh',x),('tanh',x)) and source==[full]:
        p,n=('exp',x),('exp',m.neg(x));s=m.add(p,m.neg(n))
        denominator=q(2) if e[0]=='sinh' else m.add(p,n);model=m.div(s,denominator)
        if sep:
            raw=term(definition,'x')
            if not same_value(model,raw) or any(not known_guard((r,z),ctx) and not (r=='nonzero' and same_value(z,denominator))
                                              for r,z in domain_conditions(raw)):
                unsupported('The original exponential definition contains another formula or domain cut')
        if e[0]=='sinh':
            inverse=('ln',m.add(y,('sqrt',m.add(ONE,m.power(y,2)))));image=full;rule='positive_solution_of_exponential_quadratic'
        else:
            inverse=m.mul(q(1,2),('ln',m.div(m.add(ONE,y),m.add(ONE,m.neg(y)))));image=(q(-1),ONE,False,False);rule='positive_exponential_fraction'
        return [branch(full,image,inverse,rule)]
    if sep:unsupported('An unknown defining identity accompanies the source')
    if e[0]=='rpow':
        from integrals import affine
        b=m.num(m.simplify(e[1]));p,c=map(m.num,affine(e[2],'x'))
        if b is None or b<=0 or b==1 or not m.constant_defined(e[1],ctx) or not p or c is None or domain_conditions(e[2]):
            unsupported('A strictly monotone positive-base affine exponential is required')
        sense=1 if (b>1)==(p>0) else -1
        h=m.div(m.add(m.div(('ln',y),('ln',q(b))),q(-c)),q(p))
        def image_at(z):
            if isinstance(z,str):return '+inf' if (z=='+inf')==(sense>0) else ZERO
            power=p*m.num(z)+c
            return q(b**int(power)) if power.denominator==1 else ('rpow',q(b),q(power))
        return [branch(t,arrange(image_at(t[0]),image_at(t[1]),t[2],t[3],sense),h,'logarithmic_inverse') for t in source]
    root=e[0]=='sqrt';core=e[1] if root else e
    p,d=poly.rf(core,'x')
    if not root and max(len(p),len(d))<=2:
        def coefficients(poly):return (poly[1] if len(poly)>1 else F(0),poly[0])
        (A,B),(C,D)=coefficients(p),coefficients(d);det=A*D-B*C
        if not det:unsupported('A constant map has no inverse on an interval')
        if domain_conditions(e) and any(row['type']=='hole' for row in graph_curve(e,'x')['cuts']):
            unsupported('The raw fractional map has a further source hole')
        pole=q(-D/C) if C else None;answer=[];orientation=1 if det>0 else -1
        h=m.div(m.add(m.mul(q(D),y),q(-B)),m.add(q(A),m.mul(q(-C),y)))
        def image_at(z,left):
            if z==pole:return '-inf' if (det>0)==left else '+inf'
            if isinstance(z,str):return q(A/C) if C else '+inf' if (z=='+inf')==(det>0) else '-inf'
            return m.simplify(m.substitute(e,{x:z}))
        for a,b,lc,rc in source:
            if pole is not None and ((before(a,pole)<0<before(b,pole)) or a==pole and lc or b==pole and rc):
                unsupported('The original interval contains a genuine pole of the fractional map')
            answer.append(branch((a,b,lc,rc),arrange(image_at(a,True),image_at(b,False),lc,rc,orientation),h,
                                 'invert_nonzero_fractional_determinant'))
        return answer
    if len(p)==3 and len(d)==1 and not domain_conditions(core):
        A,B,C=(z/d[0] for z in reversed(p));vertex=q(-B/(2*A));height=q(C-B*B/(4*A))
        def image_at(z):
            value=('+inf' if A>0 else '-inf') if isinstance(z,str) else m.simplify(m.substitute(core,{x:z}))
            if root:
                if before(value,ZERO)<0:unsupported('The original restricted root is not real throughout its interval')
                return value if isinstance(value,str) else m.simplify(('sqrt',value))
            return value
        result=[]
        for a,b,lc,rc in source:
            side=-1 if before(b,vertex)<=0 else 1 if before(a,vertex)>=0 else 0
            if not side:unsupported('The requested branch crosses the turning point')
            square=m.div(m.add(m.power(y,2) if root else y,m.neg(height)),q(A))
            h=m.add(vertex,m.mul(q(side),('sqrt',square)))
            result.append(branch((a,b,lc,rc),arrange(image_at(a),image_at(b),lc,rc,side*A),h,
                                 'complete_square_and_choose_source_sign'))
        return result
    unsupported('The supplied map has no certified invertible elementary branch')


def structured_inverse(task,lib,kind):
    g=structured_function_source(task,kind)
    if (set(g)!={'expression','source_domain','goals'} or g['goals']!=['inverse relation/function','its exact real domain']
            or task.get('requested_output',['inverse_function','inverse_domain'])!=['inverse_function','inverse_domain']):
        unsupported('The inverse or its source domain is incomplete')
    text,domain=g['expression'],g['source_domain'];statement=f'Определить обратную функцию x=phi(y) и её область существования для y={text}, {domain}.'
    if task.get('source_statement',statement)!=statement:unsupported('The displayed inverse source and mathematical goal disagree')
    branches=principal_inverse_pieces(text,domain)
    return certificate(lib,'restricted_inverse_and_image',dict(original=text,domain=domain),dict(branches=branches),
        'Разбиваем исходную область на указанные интервалы. Устанавливаем строгую монотонность и покрытие каждого образа.',
        'Обращаем равенство в каждой исходной ветви и проверяем допустимый знак, полюсы и включение краёв.',
        'Образы различных ветвей не пересекаются. Объединяем их в точную область обратной функции.')


def recover_by_inner_image(task,lib,kind):
    from tasks import domain_conditions
    from verify import same_value
    g=structured_function_source(task,kind)
    if (set(g) not in ({'equation','variable_domain','goal'},{'equation','given_argument_domain','goal'})
            or task.get('requested_output',['function_and_image'])!=['function_and_image']):
        unsupported('The source must ask for a function on the actual inner image')
    eq=g['equation'];match=re.fullmatch(r'f\((.+)\)=(.+)',eq)
    if not match:unsupported('An explicit restriction f(g(x))=h(x) is required')
    inner,out=match.groups();domain=g.get('given_argument_domain',g.get('variable_domain'))
    if g['goal'] not in ('recover f on the actual inner image','recover f on the image of the restricted inner map',
                         'recover f on the image of '+inner):unsupported('An additional requested recovery remains')
    label='Найти f(x), если '+eq
    endings=('',', '+domain,' ('+domain+')')
    if task.get('source_statement',label+'.') not in {label+tail+'.' for tail in endings}:
        unsupported('The recovery statement has an additional source restriction')
    x,y=('v','x'),('v','y');outer=term(out,'x');G=term(inner,'x')
    rays=re.fullmatch(r'abs\(x\)>=(.+)',domain)
    if rays:
        k=m.num(m.simplify(m.parse(rays[1],None)))
        p,d=poly.rf(G,'x')
        if (k is None or k<=0 or len(p)!=3 or p[1] or len(d)!=2 or d[0]
                or p[2]/d[1]<=0 or p[0]/d[1]<=0 or k*k<p[0]/p[2]
                or any(r!='nonzero' or (e!=x and not (e[0]=='pow' and e[1]==x))
                       for r,e in domain_conditions(G)+domain_conditions(outer))):
            unsupported('The reciprocal map has unproved original rays')
        rest=m.simplify(m.add(outer,m.neg(m.power(G,2))));rr,dd=poly.rf(rest,'x')
        if len(rr)!=1 or len(dd)!=1:unsupported('The proposed shared quadratic in the inner value is not equivalent')
        u=q((p[2]*k+p[0]/k)/d[1]);answer=dict(formula=m.add(m.power(y,2),q(rr[0]/dd[0])),
                    image=(('-inf',m.neg(u),False,True),(u,'+inf',True,False)))
    else:
        if domain=='real_numbers' and not domain_conditions(G):domain='R'
        branches=principal_inverse_pieces(inner,domain);values=[]
        for b in branches:
            H=m.substitute(outer,{x:b['inverse']})
            if any(not (r=='nonzero' and G[0]=='div' and same_value(e,G[2])) and not (r=='nonnegative' and
                   e[0]=='add' and any(t==ONE for t in e[1:]) and any(t[0]=='pow' and t[2]==2 for t in e[1:]))
                   for r,e in domain_conditions(outer)):
                unsupported('An additional obligation of the original right-hand side remains')
            values.append(dict(image=b['image'],formula=m.simplify(H),inverse=b['inverse']))
        answer=dict(branches=values)
    return certificate(lib,'recover_function_on_verified_inner_image',dict(equation=eq,domain=domain),answer,
        'Определяем точный образ внутренней функции со всеми исходными исключениями.',
        'Выражаем правую часть через новую переменную, обращая подходящую ветвь или исключая старую переменную точным равенством.',
        'Функция определена условием на доказанном образе. Каждое значение вне этого образа исходное равенство оставляет свободным.')


def structured_compositions(task,lib,kind):
    from graphs import domain_partition
    from source_primitives import rational_kernel
    from tasks import domain_conditions
    spec=structured_function_source(task,kind);x=('v','x')
    queries=spec.get('requests')
    if not isinstance(queries,list) or not queries or len(set(queries))!=len(queries):unsupported('Explicit distinct compositions are required')
    if kind=='function_compositions':
        required=['all four formulas','their original domains'];names=spec.get('definitions')
        if (set(spec)!={'definitions','requests','goals'} or not isinstance(names,dict) or len(names)!=2
                or len(queries)!=4 or spec['goals']!=required):unsupported('Both original functions and four outputs are required')
    else:
        required=['expressions','original composition domains']
        definition=re.fullmatch(rf'({NAME})\(x\)=(.+)',spec.get('definition',''))
        if set(spec)!={'definition','requests','goals'} or not definition or spec['goals']!=required:
            unsupported('A single displayed function and its requested compositions are required')
        names={definition[1]:definition[2]}
    if any(not re.fullmatch(NAME,n) or n=='x' or not isinstance(v,str) for n,v in names.items()):
        unsupported('The function names or their expressions are incomplete')
    statement=task.get('source_statement')
    if statement is not None:
        a,_,b=re.sub(r'\s+','',statement).removesuffix('.').partition('если')
        if a.removesuffix(',')!='Найти'+','.join(queries) or b!=','.join(n+'(x)='+re.sub(r'\s+','',e) for n,e in names.items()):
            unsupported('The displayed expressions and composition requests disagree')
    if task.get('requested_output',required)!=required:unsupported('Additional composition output remains')
    def options(text):
        if text in ('sgn(x)','sign(x)'):
            return [(('negative',x),q(-1)),(('zero',x),ZERO),(('positive',x),ONE)]
        p=re.fullmatch(r'piecewise\((.+?) if x<=0;\s*(.+) if x>0\)',text)
        if p:return [(('nonpositive',x),term(p[1],'x')),(('positive',x),term(p[2],'x'))]
        result=term(text,'x')
        if any(x0[0] in ('floor','sign') for x0 in nodes(result)):unsupported('An undecomposed discontinuous function remains')
        return [(None,result)]
    functions={n:options(e) for n,e in names.items()};answers=[]
    for query in queries:
        tail=query;outer=[]
        while tail!='x':
            p=re.fullmatch(rf'({NAME})\((.*)\)',tail)
            if not p or p[1] not in functions:unsupported('A composition contains an unknown function or input')
            outer.append(p[1]);tail=p[2]
        if len(outer)<2:unsupported('The request does not compose two function applications')
        pieces=[((),x)]
        for name in reversed(outer):
            branches=[]
            for guards,inner in pieces:
                for condition,func in functions[name]:
                    bind={x:inner};raw=m.substitute(func,bind)
                    restrictions=tuple(domain_conditions(raw));extra=()
                    if any((c is not None and ((rel=='nonzero' and not c) or (rel=='positive' and c<=0)
                                                   or (rel=='nonnegative' and c<0)))
                           for rel,e in restrictions for c in (m.num(m.simplify(e)),)):
                        continue
                    if condition:
                        rel,expr=condition;check=m.substitute(expr,bind);c=m.num(m.simplify(check))
                        if c is not None:
                            if not {'negative':c<0,'zero':c==0,'positive':c>0,'nonpositive':c<=0}[rel]:continue
                        else:extra=((rel,check),)
                    clean=m.simplify(raw)
                    try:clean=rational_kernel(clean,'x')
                    except (poly.Undefined,poly.NotRational):pass
                    branches.append((tuple(dict.fromkeys(guards+extra+restrictions)),clean))
            pieces=branches
        region=[]
        for guards,form in pieces:
            def normalized(relation,e):
                if relation in ('negative','nonpositive'):return (('positive' if relation=='negative' else 'nonnegative',m.neg(e)),)
                if relation=='zero':return (('nonnegative',e),('nonnegative',m.neg(e)))
                return ((relation,e),)
            try:_,proof=domain_partition('x',[x0 for r,e in guards for x0 in normalized(r,e)],simplify_guards=True)
            except (Unsupported,line.Unsupported,poly.NotRational,poly.Undefined):proof=('and',guards)
            if proof==('real_set',()):continue
            region.append(dict(formula=form,original_domain=proof))
        answers.append(dict(request=query,branches=region))
    return certificate(lib,'compose_with_preimages_of_source_guards',dict(definitions=names,requests=queries),
        dict(compositions=answers),
        'Идём от внутреннего вызова к внешнему. На каждом шаге берём прообраз условий ветвей и естественной области следующей функции.',
        'Полюс сохраняется в условиях даже при последующем сокращении формулы. Проверяем все запрошенные композиции и объединение допустимых ветвей.')


def domain_preimage(task,lib):
    from graphs import interval_terms
    from integrals import affine
    from tasks import domain_conditions
    g=structured_function_source(task,'composition_domain',(
         'The source states f is defined for0<u<1; no values outside this declared interval are inferred.',))
    if (set(g)!={'outer_declared_domain','inner','variable','goal'} or g['variable']!='x'
            or g['goal']!='inverse image of the declared domain, with inner domain retained'
            or task.get('requested_output',['composition_domain'])!=['composition_domain']):
        unsupported('The declared inner map and full preimage goal are required')
    domain=g['outer_declared_domain'];text=g['inner'];a,b,left,right=interval_terms(domain,{})
    A,B=m.num(a),m.num(b)
    if A is None or B is None or A>=B or left or right:unsupported('An open bounded source interval with exact ordered endpoints is required')
    label=f'Функция f(u) определена при{A}<u<{B}. Найти область определения f({text}).'
    if task.get('source_statement',label)!=label:unsupported('The displayed function domain and inner map disagree')
    x=('v','x');e=term(text,'x');data=dict(outer_interval=(a,b),inner=e)
    if e[0]=='sin' and -1<=A<B<=1 and not domain_conditions(e[1]):
        m0,k=affine(e[1],'x');M=m.num(m0)
        if not M or m.num(k) is None:unsupported('A nondegenerate affine sine phase is required')
        L=m.simplify(('asin',a));U=m.simplify(('asin',b));period=m.mul(m.mul(q(2),m.PI),('s','k'))
        def preimage(pair):
            vals=[m.div(m.add(m.add(c,period),m.neg(k)),m0) for c in pair]
            return tuple(vals if M>0 else reversed(vals))+(False,False)
        answer=dict(index='integer k',intervals=[preimage((L,U)),preimage((m.add(m.PI,m.neg(U)),m.add(m.PI,m.neg(L))))])
        argument='В каждом периоде синус строго монотонен на двух главных ветвях. Обращаем концы на каждой ветви и переносим интервалы по ненулевой аффинной фазе.'
    elif e[0]=='ln' and not domain_conditions(e[1]):
        m0,k=affine(e[1],'x');M=m.num(m0)
        if not M or m.num(k) is None:unsupported('A nondegenerate affine logarithmic argument is required')
        ends=[m.div(m.add(m.simplify(('exp',u)),m.neg(k)),m0) for u in (a,b)]
        answer=dict(interval=tuple(ends if M>0 else reversed(ends))+(False,False))
        argument='Переходим к строгим экспоненциальным границам аргумента. Его положительность следует из нижней границы, затем обращаем аффинную карту.'
    elif (A,B)==(0,1) and e==('div',('floor',x),x):
        n=('s','j');answer=dict(index='integer j>=1',interval=(n,m.add(n,ONE),False,False))
        argument='При x<0 отношение целой части к x не меньше единицы, а при 0<x<1 оно нулевое. На положительных целочисленных интервалах с j≥1 оба нестрогих края исключаются.'
    else:unsupported('No monotone or integer-cell preimage for the original map')
    return certificate(lib,'preimage_of_an_outer_function_domain',data,answer,
        'Аргумент внешней функции должен принадлежать исходному открытому интервалу. Одновременно сохраняем собственную область внутренней функции.',argument)


def iterate_radial_map(task,lib):
    from tasks import domain_conditions,source
    g=structured_function_source(task,'iterate_function_formula')
    if (set(g)!={'definition','iteration','index_domain','variable_domain','goal'} or g['iteration']!='n successive compositions'
            or g['index_domain']!='positive_integers' or g['variable_domain']!='real_numbers' or g['goal']!='formula for all f_n(x)'
            or task.get('requested_output',['iteration_formula'])!=['iteration_formula']):
        unsupported('The original iterate needs a positive integer index and a complete real map')
    text=g['definition'];match=re.fullmatch(r'f\(x\)=(.+)',text)
    if not match:unsupported('The original iterated function is not given explicitly')
    label='Пусть f_n(x) есть n-кратная композиция f. Найти f_n(x), если '+text+'.'
    if task.get('source_statement',label)!=label:unsupported('The displayed iterative map and goal disagree')
    e=term(match[1],'x');x=('v','x')
    if e[0]!='div' or e[2][0]!='sqrt' or any(domain_conditions(z) for z in (e[1],e[2][1])):
        unsupported('A linear numerator and a globally positive quadratic root are required')
    (p,dp),(r,dr)=[poly.rf(z,'x') for z in (e[1],e[2][1])]
    if len(dp)!=1 or len(dr)!=1 or len(p)!=2 or p[0] or len(r)!=3 or r[1] or r[0]!=dr[0] or r[2]/dr[0]<0:
        unsupported('The map does not preserve the reciprocal-square coordinate on all nonzero inputs')
    A,B=p[1]/dp[0],r[2]/dr[0];a,b=map(lambda z:source(q(z)),(A,B))
    coordinate=m.power(x,-2)
    ans=dict(value_at_zero=ZERO,domain='real line',iterates=f'({a})^n*x/sqrt(1+({b})*x^2*sum_(j=0..n-1)({a})^(2*j))')
    return certificate(lib,'iterate_by_affine_reciprocal_square',dict(function=e,index='positive integer n'),ans,
        'При x≠0 пробуем обратный квадрат аргумента. Подстановка даёт аффинную рекурсию z_next=(z+B)/A². Знак очередной итерации определяется знаком A.',
        'Решаем аффинную рекурсию конечной геометрической суммой и восстанавливаем знак. Индукционный переход умножает прежнюю сумму на A² и добавляет единицу.',
        'В нуле все итерации равны нулю, а исходный радикал всегда положителен.',coordinate=coordinate,
        recurrence=(q(1/(A*A)),q(B/(A*A))),positive_original_radical=e[2][1])


INVERSE_TEXT=re.compile(r'Найти обратную (?:функцию )?для y=(.+?)(?:, (.*))?')
MAPPED_CURVE=re.compile(r'(?:Найти y\(x\) и область при x=(.+?), y=(.+?), (.+)|При x=(.+?), y=(.+?), (.+?), определить максимальные промежутки изменения (.+?) с однозначной y\(x\) и её формулу на каждом)')
FUNCTION_EQUATION=re.compile(r'Найти все непрерывные (?:на R функции, для которых (.+) при всех (.+)|(.+):R→R с (.+))')
CLAMP_TEXT=re.compile(r'При ('+NAME+r')>0 и непрерывной ('+NAME+r') доказать непрерывность (\2_\1), равной −\1 при \2<−\1, \2 при \|\2\|≤\1, \1 при \2>\1')
DIFFERENCE=re.compile(r'(?:Доказать Δ\[(.+)\]=(.+)|При Δ('+NAME+r')\(('+NAME+r')\)=\3\(\4\+Δ\4\)−\3\(\4\), Δ²\3=Δ\(Δ\3\), доказать, что непрерывная на R функция с Δ²\3\(\4\)≡0 линейна: \3\(\4\)=a\4\+b)')
ARITHMETIC_DISCONTINUITY=re.compile(
    rf'Обязательно ли ({NAME})\s*([+*])\s*({NAME}) разрывна в ({NAME}₀), если в этой точке '
    r'(?:\1 непрерывна и \3 разрывна|\1 и \3 разрывны)\? Построить соответствующие примеры',re.I)


def arithmetic_discontinuity(task,lib,match):
    f,op,g,point=match.groups()
    if f==g:unsupported('Continuity assumptions must refer to distinct freely chosen functions')
    both=bool(re.search(r' разрывны\b',match[0]));sum_goal=op=='+'
    H={'formula':'1 if h >= 0 else 0','traces':(0,1,1)}
    J={'formula':'1 if h >= 0 else -1','traces':(-1,1,1)}
    assert_discontinuous=(sum_goal and not both)
    common='All witness formulas use h=x-'+point+' and their left, point, right values are checked separately.'
    if both:
        choices=(('H','-H','0'),('H','H','2H')) if sum_goal else (('J','J','1'),('H','H','H'))
    elif sum_goal:
        choices=(('0','H','H'),)
    else:
        choices=(('h','H','max(h,0)'),('1','H','H'))
    samples={'H':H['traces'],'-H':(0,-1,-1),'2H':(0,2,2),'J':J['traces'],
             '1':(1,1,1),'0':(0,0,0),'h':(0,0,0),'max(h,0)':(0,0,0)}
    witnesses=[]
    for a,b,c in choices:
        u,v,w=(samples[z] for z in (a,b,c))
        value=tuple(l+r if sum_goal else l*r for l,r in zip(u,v))
        if value!=w or v[0]==v[2] or (u[0]!=u[2])!=both:
            unsupported('A witness does not satisfy all continuity assumptions')
        witnesses.append(dict(functions=(a,b),combined=c,traces=(u,v,w),continuous=w[0]==w[1]==w[2]))
    steps=(('If the sum were continuous, subtracting the given continuous summand would make the other summand continuous.',common)
           if assert_discontinuous else
           ('For multiplication, a continuous nonzero factor at the point has a continuous reciprocal.' if not sum_goal
            else 'The limits of two opposite jumps can cancel.',common))
    return certificate(lib,'continuity_under_arithmetic',dict(operation=op,functions=(f,g),
        point=point,continuous=(f,) if not both else (),discontinuous=(f,g) if both else (g,)),
        dict(necessarily_discontinuous=assert_discontinuous,witnesses=witnesses),
        *steps,witness_primitives={'H':H,'J':J})


def square_discontinuity(task,lib,match):
    return certificate(lib,'continuity_under_arithmetic',dict(domain='real line',operation='square'),
        dict(necessarily_discontinuous=False,witness='1 on rational inputs, -1 on irrational inputs',
             square=ONE,discontinuity_set='real line'),
        'Rational and irrational points approach every real point. The function has distinct traces along those two sets.',
        'Both possible input values have square 1, including the actual point value.')


def branch_reflection(task,lib,match):
    f,x,l,c,u,reflection,r=match.groups()
    if len({f,x,u})!=3 or F(c)-F(l)!=F(r)-F(c) or F(l)>=F(c) or F(reflection)!=2*F(c):
        unsupported('The two branches do not describe the same reflection chart')
    return certificate(lib,'compose_by_sign_cells',dict(functions=(f,'φ'),variable=x,domain=(q(F(l)),q(F(c)),False,False)),
        dict(formula=('v',x),continuous=True),
        'The direct branch maps the input into the first interval. The reflected branch maps it into the second interval.',
        'Reflecting twice about the same midpoint leaves the original input unchanged.')


def limit_shift(task,lib,match):
    f,left,T,x=match.groups()
    if len({f,T,x})!=3:unsupported('The shift, input sequence, and function must be independent')
    return certificate(lib,'bounded_shift_difference',dict(function=f,domain=(left,'+inf'),continuous=True,bounded=True,shift=T),
        dict(sequence=x,argument_limit='+inf',difference_limit=ZERO),
        'If the difference is bounded away from zero on the tail, it has a fixed sign by continuity.',
        'For a positive shift, telescoping the differences along equally spaced points violates boundedness.',
        'For a negative shift change the origin and reverse the difference. The zero shift has identically zero difference.',
        'Choose inputs successively farther out with difference of magnitude at most 1/n.')


def periodic_limit(task,lib,match):
    f,g=match.groups()
    if f==g:unsupported('The two function declarations need distinct names')
    return certificate(lib,'periodic_tail_identity',dict(periodic_functions=(f,g),difference_limit=ZERO),
        dict(equal_functions=(f,g),domain='real line'),
        'Use any positive period P of the first function. The P-shift difference of the second tends to zero.',
        'This shift difference still has every period Q of the second function. Along each x+nQ its value is constant.',
        'The difference is identically zero, so P is a common period.',
        'The original difference is now periodic with vanishing tail and the same argument shows equality.')


def monotone_trace(task,lib,match):
    mode='jump' if not match.groups() else 'intermediate_values'
    f,a,b=match.groups() if match.groups() else ('f',None,None)
    statements=('Left and right limits are the appropriate suprema or infima of the monotone values.',
                'Monotonicity places each actual value between the available one-sided traces.')
    if mode=='jump':
        answer=dict(discontinuity_kind='first kind',limits='finite on both available sides')
    else:
        if len({f,a,b})!=3:unsupported('The interval and function must be independently named')
        statements+=('Any unequal traces or value at an endpoint omit a nonempty interval of intermediate values.',)
        answer=dict(continuous_on=(a,b,True,True),function=f)
    return certificate(lib,'monotone_one_sided_traces',dict(function=f,interval=(a,b),
        shape='monotone',bounded=mode=='jump',covers_intermediate_values=mode!='jump'),answer,*statements)


def oscillating_sine(task,lib,match):
    f,x,a=match.groups()
    if len({f,x,a})!=3:unsupported('A moving argument and endpoint must be distinct')
    return certificate(lib,'oscillating_phase_intermediate_values',dict(function=f,variable=x,
        phase='1/('+x+'-'+a+')',value_at_endpoint=ZERO),
        dict(image_on_every_nontrivial_right_interval=(q(-1),ONE,True,True),continuous_at_endpoint=False),
        'On every punctured right interval the phase takes all sufficiently large positive values.',
        'Every sufficiently large full period of sine realizes the full closed range [-1,1].',
        'The repeated phases pi/2 and 3pi/2 modulo 2pi give incompatible limits at the endpoint.')


def strict_prefix(task,lib,match):
    f,a,b,lower,x,upper,delimiter=match.groups()
    if len({f,a,b,lower,x,upper})!=6:unsupported('The names of bounds, functions and moving coordinates must be distinct')
    if delimiter=='[':unsupported('At the included left endpoint the strict prefix is empty. A real value or a relative domain (a,b] must be specified.')
    return certificate(lib,'strict_prefix_left_trace',dict(function=f,bounded_on=(a,b,True,True),
          prefix=(a,x,True,False)),dict(left_continuous_functions=(lower,upper),domain=(a,b,False,True)),
        'For a left approach to x the strict prefixes increase by inclusion and exhaust the prefix at x.',
        'The corresponding infima and suprema form bounded monotone families.',
        'Every original argument below x is eventually included. Its value bounds the limiting extremum in the other direction.')


def intermediate_value_selection(task,lib,match):
    names=match.groups();f,a,b=names[:3]
    if len({f,a,b})!=3:unsupported('The source endpoints and function names must differ')
    if len(names)==3:
        return certificate(lib,'intermediate_value_selection',dict(function=f,continuous_on=(a,b,False,False),
            values='finite sample'),dict(attains='arithmetic mean',between='extreme sample inputs'),
            'The sample mean is trapped between its least and greatest sample values.',
            'Use the intermediate value theorem between the two input points attaining those values.')
    x,left,upper=names[3:]
    if a!=left or a!=upper:unsupported('Both limiting traces must concern the source endpoint')
    return certificate(lib,'intermediate_value_selection',dict(function=f,continuous_on=(a,b,False,False),
            cluster_threshold='between liminf and limsup',variable=x),dict(sequence_limit=a,values_limit='lambda'),
            'For a strict intermediate value each sufficiently small right neighborhood provides points on both sides of the target.',
            'Apply the intermediate value theorem between them to obtain an input with the target value.',
            'At a finite limiting trace use a sequence approaching that trace instead.')


ABSTRACT={
    ARITHMETIC_DISCONTINUITY:arithmetic_discontinuity,
    re.compile(r'Всегда ли квадрат разрывной функции разрывен\? Построить всюду разрывную функцию с непрерывным квадратом'):square_discontinuity,
    re.compile(rf'Исследовать ({NAME})\(φ\(({NAME})\)\) на ([0-9]+)<\2<([0-9]+): \1\(({NAME})\)=\5 при \3<\5≤\4, '
               r'\1\(\5\)=([0-9]+)−\5 при \4<\5<([0-9]+), φ\(\2\)=\2 на рациональных, φ\(\2\)=\6−\2 на иррациональных'):branch_reflection,
    re.compile(rf'Для непрерывной ограниченной ({NAME}) на \(({NAME}₀),\+∞\) и любого ({NAME}) доказать существование '
               r'(x)_n→\+∞ с \1\(\4_n\+\3\)−\1\(\4_n\)→0'):limit_shift,
    re.compile(r'Непрерывные периодические ([φϕ]) и ([ψ]) на R удовлетворяют \1\(x\)−\2\(x\)→0 при x→\+∞\. '
               r'Доказать \1\(x\)=\2\(x\)\. Общий период не дан'):periodic_limit,
    re.compile(r'Доказать, что все разрывы ограниченной монотонной функции — первого рода'):monotone_trace,
    re.compile(rf'Пусть ({NAME}) монотонна на \[({NAME}),({NAME})\] и принимает все значения между '
               r'\1\(\2\) и \1\(\3\)\. Доказать её непрерывность на \[\2,\3\]'):monotone_trace,
    re.compile(rf'Функция ({NAME})\(({NAME})\)=sin\(1/\(\2−({NAME})\)\) при \2≠\3, \1\(\3\)=0\. Доказать, что на каждом '
               r'\[\3,b\] принимает промежуточные значения между \1\(\3\) и \1\(b\), но не является непрерывной на \[\3,b\]'):oscillating_sine,
    re.compile(rf'Пусть ({NAME}) непрерывна на \(({NAME}),({NAME})\), x₁,…,xₙ∈\(\2,\3\)\. '
               r'Доказать существование ξ между ними, где \1\(ξ\) равно среднему арифметическому \1\(xᵢ\)'):intermediate_value_selection,
    re.compile(rf'Пусть ({NAME}) непрерывна на \(({NAME}),({NAME})\), l=liminf\(({NAME})→({NAME})\)\1\(\4\), '
               r'L=limsup\(\4→('+NAME+r')\)\1\(\4\)\. Для l≤λ≤L доказать существование \4ₙ→\2 с \1\(\4ₙ\)→λ'):intermediate_value_selection,
    re.compile(rf'Для ограниченной ({NAME}) на \[({NAME}),({NAME})\] доказать непрерывность слева '
               rf'({NAME})\(({NAME})\)=inf_\{{\2≤ξ<\5\}}\1\(ξ\), ({NAME})\(\5\)=sup_\{{\2≤ξ<\5\}}\1\(ξ\) на ([\[(])\2,\3\]'):strict_prefix,
}


def inverse_source(task,lib,match):
    from verify import same_value
    original,extras=match.groups()
    terms=re.fullmatch(rf'\(({NAME})x\+({NAME})\)/\(({NAME})x\+({NAME})\)',normal(original))
    if terms and extras:
        a,b,c,d=terms.groups()
        if len({a,b,c,d,'x','y'})!=6 or extras!=f'{a}{d}−{b}{c}≠0; выяснить, когда она совпадает с исходной':
            unsupported('The determinant restriction or original self-inverse question has changed')
        return certificate(lib,'projective_inverse',dict(matrix=((a,b),(c,d)),determinant_nonzero=True),
            dict(inverse=f'({d}*y-{b})/({a}-{c}*y)',original_hole=f'{c}≠0 ⇒ x≠-{d}/{c}',
                 image_hole=f'{c}≠0 ⇒ y≠{a}/{c}',self_inverse=(
                 f'{a}+{d}=0',f'{b}={c}=0 and {a}={d}≠0')),
            'Solve the linear equation for the original input and compare both denominator cuts.',
            'The original transformation composed with itself has the square of its coefficient matrix.',
            'By Cayley–Hamilton the square is scalar if and only if the trace vanishes or the original matrix is scalar.')
    if extras not in ('[x] — целая часть','где [x] — целая часть'):
        unsupported('The source has an additional inverse-function question')
    e=term(original.replace('[x]','floor(x)'),'x');v=('v','x')
    if not same_value(e,m.add(v,('floor',v))):unsupported('The floor fibers do not have the required affine form')
    return certificate(lib,'integer_cell_inverse',dict(source=e,original_domain='real line'),
        dict(inverse='y-floor(y/2)',image='union [2k,2k+1) for all integer k'),
        'Write the input as k+r with unique integer k and 0≤r<1.',
        'Its output is 2k+r, so k=floor(y/2) and the image intervals are disjoint.')


def equation_inverse(task,lib,match):
    if len(match.groups())==1:
        trig,=match.groups()
        return certificate(lib,'invert_strict_continuous_range',dict(equation=f'y−epsilon*{trig}(y)=x',
              epsilon=(ZERO,ONE,True,False),source_domain='real line'),
            dict(solution='unique continuous function on R',inverse_of=f'y−epsilon*{trig}(y)',
                 lipschitz='1/(1-epsilon)'),
            'The derivative is bounded below by 1−epsilon>0, so the map is strictly increasing.',
            'The bounded trigonometric correction leaves limits −∞ and +∞ on the two tails.',
            'The intermediate value theorem gives surjectivity and the inverse is Lipschitz by the derivative bound.')
    return certificate(lib,'invert_strict_continuous_range',dict(equation='cot(x)=k*x',
          source_domain=(ZERO,m.PI,False,False),parameter='any real k'),
        dict(solution='unique continuous function of k',inverse_of='cot(x)/x'),
        'Rearrange on the positive source interval to k=cot(x)/x.',
        'The derivative is −(x+sin(x)cos(x))/(x² sin²(x)).',
        'The numerator is the integral of 2cos²(t) from zero to x, which is strictly positive.',
        'The endpoint values of the rearranged map approach +∞ and −∞. Its continuous monotone inverse is defined on R.')


def inverse_structure(task,lib,match):
    flag=next((index for index,g in enumerate(match.groups()) if g),None)
    if flag==0:
        answer=dict(inverse='the original map',monotone=False)
        steps=('Both rational and irrational branches preserve their respective sets.',
               'The two successive applications of each branch give the identity, establishing bijectivity.',
               'On the positive half-line, two dense input sets have images with opposite signs. Both monotonic orientations fail.')
    elif flag==1:
        answer=dict(iff=('domain equals image','double composition equals identity on the domain'))
        steps=('The two requirements are necessary for equality of a map and its inverse.',
               'The double composition is the identity, giving injectivity and surjectivity onto that domain.')
    elif flag==2:
        answer=dict(inverse='sign(y)*sqrt(abs(y)-1) for |y|>1, 0 if y=0',
                    image='(-inf,-1) union {0} union (1,+inf)',continuous_on_image=True)
        steps=('The images of the negative and positive branches are disjoint open rays.',
               'Solve y=±(1+x²) on each original branch. The remaining 0 maps to 0.',
               'The inverse is continuous on each ray and on the relative image at the isolated point.')
    else:
        answer=dict(input_sequence_limit='a')
        steps=('If a subsequence stays a positive distance from a, choose a fixed intermediate point in the original interval.',
               'Strict monotonicity bounds the distance between its images and f(a) below by a positive constant.',
               'This contradicts convergence of the original sequence of images to f(a).')
    return certificate(lib,'inverse_fibers_and_image',dict(source_properties=match[0]),answer,*steps)


ANGLE_TEXT=tuple(map(re.compile,(
    r'Доказать arcsin ([a-z])\+arccos \1=π/2 на действительной области',
    r'Доказать arctg ([a-z])\+arctg\(1/\1\)=\(π/2\) sgn \1 для \1≠0',
    r'Доказать arctg ([a-z])\+arctg ([a-z])=arctg\(\(\1\+\2\)/\(1−\1\2\)\)\+επ, ε∈\{0,1,−1\}\. '
    r'Где при данном \1 возможен разрыв ε\? Определить области непрерывности ε на плоскости и его значение в каждой',
    r'Доказать arcsin ([a-z])\+arcsin ([a-z])=\(−1\)\^ε arcsin\(\1√\(1−\2²\)\+\2√\(1−\1²\)\)\+επ для \|\1\|,\|\2\|≤1, '
    r'где ε=0 при \1\2≤0 или \1²\+\2²≤1, и ε=sgn \1 при \1\2>0, \1²\+\2²>1',
    r'Доказать arccos ([a-z])\+arccos ([a-z])=\(−1\)\^ε arccos\(\1\2−√\(1−\1²\)√\(1−\2²\)\)\+2πε (?:при|для) \|\1\|,\|\2\|≤1, '
    r'где ε=0 при \1\+\2≥0 и ε=1 при \1\+\2<0',
)))


def principal_angles(task,lib,match):
    index=ANGLE_TEXT.index(match.re);variables=match.groups()
    if len(set(variables))!=len(variables):unsupported('The operands must have independent coordinates')
    x=variables[0];y=variables[-1]
    real=dict(variables=variables);square=real|dict(original_domain='both arguments in [-1,1]')
    if index==0:
        return certificate(lib,'principal_angle_ranges',square,dict(sum='pi/2'),
            'The complement of the principal arcsine angle lies in [0,pi] and has cosine equal to the argument.')
    if index==1:
        return certificate(lib,'principal_angle_ranges',real|dict(guard=f'{x}≠0'),dict(sum=f'pi*sign({x})/2'),
            'For a positive argument the two arctangent angles are acute and complementary.',
            'Oddness of the principal arctangent gives the negative branch.')
    if index==2:
        return certificate(lib,'principal_angle_ranges',real|dict(guard=f'{x}*{y}≠1'),
            dict(epsilon=((f'{x}*{y}<1',0),(f'{x}>0 and {x}*{y}>1',1),(f'{x}<0 and {x}*{y}>1',-1)),
                 boundary=f'{y}=1/{x} for {x}≠0',boundary_angle=f'pi*sign({x})/2',epsilon_undefined_on_boundary=True),
            'The cosine of the angle sum has the sign of 1−xy, and its sine gives the tangent addition formula.',
            'The sum lies between −pi and pi. A negative cosine requires the outer branch, with sign taken from the equal operand signs.',
            'The two noncentral components have opposite signs. The tangent expression has a pole at their boundary.')
    if index==3:
        return certificate(lib,'principal_angle_ranges',square,dict(epsilon=((f'{x}*{y}≤0 or {x}²+{y}²≤1',0),
              (f'{x}*{y}>0 and {x}²+{y}²>1',f'sign({x})')),identity=match[0].partition(' для ')[0]),
            'The sum of the principal arcsines lies in [−pi,pi]. Its cosine is sqrt(1−x²)sqrt(1−y²)−xy.',
            'If xy is positive, comparison of the nonnegative squares decides the cosine sign across the unit circle.',
            'Apply sine addition and reflect outside the principal angle range, keeping the sign of the original sum.')
    return certificate(lib,'principal_angle_ranges',square,
        dict(epsilon=((f'{x}+{y}≥0',0),(f'{x}+{y}<0',1)),identity=re.split(r' (?:при|для) \|',match[0])[0]),
        'The sum of the principal arccosines belongs to [0,2pi].',
        'Compare the second arccosine with arccos(-x)=pi−arccos(x) using strict decrease.',
        'Apply cosine addition and reflect the portion above pi into [0,pi].')


def parametric_curve(task,lib,request,match=None):
    from tasks import domain_conditions,source
    from verify import same_value
    if match is None:
        fields(task,{'parameter','x','y','parameter_interval'},['function_and_domain'])
        t,X,Y,interval=(task[k] for k in ('parameter','x','y','parameter_interval'))
    else:
        X,Y,interval,left,right,other,variable=match.groups()
        t='t' if variable is None else variable
        if left is not None:X,Y,interval=left,right,other
        if interval!='−∞<'+t+'<+∞':unsupported('The parameter interval is not fully bound')
        interval='(-inf,+inf)'
    u,v=term(X,t),term(Y,t);z=('v',t)
    if same_value(u,v) and set(domain_conditions(u))==set(domain_conditions(v)):
        image=request('exact image of the first coordinate',dict(kind='restricted_function_image',
            goal=dict(variable=t,expression=source(u),given_domain=interval,goal='exact image')))['value']
        return certificate(lib,'parametric_fiber_constancy',dict(parameter=t,interval=interval,coordinates=(u,v)),
            dict(function='y=x',image=image['image_intervals']),
            'Both coordinates agree on their common domain, so equal first coordinates imply equal second coordinates.',
            'The checked image of the first coordinate is exactly the domain of the resulting function.')
    if (u,v)==(('cosh',z),('sinh',z)) and interval=='(-inf,+inf)':
        return certificate(lib,'parametric_fiber_constancy',dict(parameter=t,interval=interval,coordinates=(u,v)),
            dict(branches=(('t≤0','y=−sqrt(x²−1)'),('t≥0','y=sqrt(x²−1)')),
                 image_intervals=((ONE,'+inf',True,False),)),
            'Hyperbolic cosine is strictly monotone on each indicated half-line, with minimum 1 and unbounded outer value.',
            'Use cosh²(t)−sinh²(t)=1 and use the sign of the second coordinate on each chart.',
            'An interval extending either half-line contains opposite nonzero parameters, which agree only in the first coordinate.')
    unsupported('The coordinate-fiber relationship or completeness of its branches is not proved')


def parametric_factor(task,lib,match):
    fiber='equal first coordinates imply equal second coordinates'
    mode=next(i for i,x in enumerate(match.groups()) if x)
    if mode==0:
        val=dict(iff=fiber,example=dict(equality='sin²(t)+cos²(t)=1',function='y=1−x',
                                        image='sin²((alpha,beta))'))
        arg=('Constancy on each fiber is necessary, since a function has one value at each input.',
             'Conversely, define the value at each image point by choosing any preimage. Fiber constancy makes the choice immaterial.',
             'The two example coordinates add to 1 for all allowed parameters.')
    elif mode==1:
        val=dict(iff=('both parametrizations define a function by fiber constancy',
                       'same first-coordinate image and same second coordinate on shared fibers'),
                 sufficient_when_inside_original_interval='the new parameters cover every first-coordinate fiber')
        arg=('Each point in the new graph is an original point when the reparametrization takes values in the original interval.',
             'Equality then reduces to covering all original first-coordinate values. A parameter from every first-coordinate fiber suffices.',
             'Without the image inclusion premise separately equate the second coordinates over the common first-coordinate image.')
    else:
        val=dict(iff=('first coordinate never attains either finite bound','fiber constancy'),unique=True,domain='(A,B)')
        arg=('For composition with a function defined on (A,B), every first coordinate must lie strictly inside (A,B).',
             'The intermediate value theorem fills all values strictly between the two extrema.',
             'Define the outer function on this image by choosing any preimage. Fiber constancy gives a unique value.')
    return certificate(lib,'parametric_fiber_constancy',dict(quantified_relation=match[0]),val,*arg)


def clamp_source(task,lib,request,match):
    c,f,_=match.groups()
    if c==f:unsupported('The bound must be independent of the function')
    lo,hi=[s for s in ('lower_bound','upper_bound','constant_lo','constant_hi') if s not in (c,f)][:2]
    formula=f'min({hi},max({lo},{f}))'
    functions=[f,lo,hi]
    request('continuity of the original function composed with the two clipping operations',
            dict(kind='prove_continuity',functions=functions,continuous_functions=functions,expressions=[formula]))
    return certificate(lib,'clipping_by_continuous_operations',dict(function=f,bound=c,positive_bound=True),
        dict(function=f'min({c},max(-{c},{f}))',continuous=True),
        'Both bounds are constant and thus continuous.',
        'Compare the function value with the two bounds. The clipping expression agrees with all three original cases, including equality.',
        'The child proof gives continuity of the resulting min and max operations.')


def difference_source(task,lib,request,match):
    from tasks import domain_conditions
    from verify import same_value
    original,wanted,f,x=match.groups()
    if original is None:
        t=f'{f}_centered'
        subgoal=dict(kind='solve_functional_equation',equation=f'{t}(s+v)={t}(s)+{t}(v)',
                     assumptions=[f'{t} continuous on R'],requested_output=['prove_characterization'])
        request('classification of the continuous additive centered function',subgoal)
        return certificate(lib,'translation_difference_equivalence',dict(function=f,domain='R',arbitrary_step=True),
            dict(all_solutions=f'{f}({x})=c*{x}+{f}(0)'),
            'Apply the second difference with endpoints u and v and step (v−u)/2.',
            'Subtract f(0), giving a function h with h(2x)=2h(x) and the midpoint identity.',
            'Their combination is the additive equation on all real pairs, classified by the checked subproof.',
            'Substituting an affine function gives zero second difference for every real step.')
    match=re.fullmatch(rf'({NAME})\(({NAME})\)([+*]?)({NAME})\(\2\)',original)
    if not match:unsupported('Both original operands must use the same variable')
    f,x,op,g=match.groups()
    if len({f,x,g})!=3:unsupported('The two function names and the input must be distinct')
    h='h' if {f,x,g}.isdisjoint({'h'}) else 'step_value'
    names=[f,g];v=('v',x);step=('s',h)
    target=m.parse(f'{f}({x}){op or "*"}{g}({x})',x,extra_functions=set(names))
    deriv=m.add(m.substitute(target,{v:m.add(v,step)}),m.neg(target))
    expected={name:f'({name}({x}+{h})-{name}({x}))' for name in names}
    formula=re.sub(r'Δ([A-Za-z]\w*)\('+re.escape(x)+r'\)',lambda a:expected.get(a[1],a[0]),wanted)
    formula=formula.replace('Δ'+x,h)
    formula=re.sub(r'\)(?=[A-Za-z(])',')*',formula)
    value=m.parse(formula,x,parameters=[h],extra_functions=set(names))
    if domain_conditions(value) or any(node[0]=='s' and node[1]!=h for node in nodes(value)):
        unsupported('The identity introduces an additional domain condition or an undeclared parameter')
    value=m.substitute(value,{node:(node[0],m.simplify(node[1])) for node in nodes(value) if node[0] in names})
    if not same_value(value,deriv):
        unsupported('The printed right-hand side does not equal the raw common-step increment')
    return certificate(lib,'translation_difference_equivalence',dict(functions=names,variable=x,step=h,
        original_values='each operand is defined at both endpoints'),dict(identity=wanted),
        'Expand both finite differences using the same shift. The two exact algebraic expressions agree.',
        printed_expansion=value,original_expansion=deriv)


COSINE_LAW=re.compile(rf'({NAME})\(({NAME})\+({NAME})\)\+\1\(\2−\3\)=2\1\(\2\)\1\(\3\)')
COMPLEX_LAW=re.compile(
    rf'Найти все непрерывные ограниченные ({NAME}),({NAME}) на R с \1\(({NAME})\+({NAME})\)=\1\(\3\)\1\(\4\)−\2\(\3\)\2\(\4\), '
    r'\2\(\3\+\4\)=\1\(\3\)\2\(\4\)\+\1\(\4\)\2\(\3\), \1\(0\)=1,\2\(0\)=0')
SIGN_LAW=re.compile(rf'Доказать, что разрывная функция ({NAME})\(([a-z])\)=sgn \2 удовлетворяет \1\(\2([a-z])\)=\1\(\2\)\1\(\3\)')


def functional_source(task,lib,request,match):
    if match.re==FUNCTION_EQUATION:
        law,vars_,name,cosine=match.groups()
        if law:
            product=re.fullmatch(rf'({NAME})\(([A-Za-z])([A-Za-z])\)=\1\(\2\)\1\(\3\)',law)
            if product is None:unsupported('The source is not a multiplicative law on all real pairs')
            f,x,y=product.groups()
            if len({f,x,y})!=3 or vars_!=f'{x},{y}':unsupported('The independent variables are not bound')
            child=dict(kind='solve_functional_equation',equation=f'{f}({x}*{y})={f}({x})*{f}({y})',
                       assumptions=[f'{f} continuous on (0,+inf)',f'{x},{y}>0','not identically zero'],
                       requested_output=['prove_characterization'])
            request('classification on positive input values of a nonzero multiplicative function',child)
            return certificate(lib,'extend_positive_homomorphism',dict(function=f,domain='R',law=law,continuous=True),
                dict(solutions=('identically 0','identically 1',f'abs({x})^r',f'sign({x})*abs({x})^r'),
                     nonconstant_parameters='r>0, value at origin 0'),
                'A nonzero solution has f(1)=1. Its restriction to positive inputs is nonzero by evaluating f(1).',
                'Use the checked positive-domain homomorphism classification.',
                'Since f(-1)²=1, the restriction determines the entire negative half-line with either sign.',
                'Continuity at zero allows the constant-one case or r>0. Direct multiplication checks all retained functions.')
        eq=COSINE_LAW.fullmatch(cosine)
        if not eq or name!=eq[1] or len(set(eq.groups()))!=3:
            unsupported('The continuous centered addition law is not bound')
        return certificate(lib,'centered_integral_regularization',dict(function=name,law=cosine,domain='R',continuous=True),
            dict(solutions=('identically 0','identically 1','cos(lambda*x)','cosh(lambda*x)'),parameter='lambda>0'),
            'The nonzero case has f(0)=1 and is even. Choose a small a with a nonzero integral of f on [0,a].',
            'Integrating the equation over [0,a] gives 2f(x) times that integral equal to the integral from x−a to x+a.',
            'The sliding integral first gives a continuous first derivative, then a continuous second derivative.',
            'Differentiate twice in the second variable at zero. This yields the constant-coefficient equation f″(x)=f″(0)f(x), with f(0)=1 and f′(0)=0.',
            'Solve the initial value problem by the sign of f″(0). Check the original law by sine and hyperbolic addition formulas.')
    if match.re==COMPLEX_LAW:
        f,g,x,y=match.groups()
        if len({f,g,x,y})!=4:unsupported('The two component functions and two inputs must be independent')
        return certificate(lib,'bounded_circle_homomorphism',dict(functions=(f,g),domain='R',bounded=True,
              continuous=True,origin=(ONE,ZERO),law='addition in the input and complex multiplication in the output'),
            dict(solutions=(f'{f}({x})=cos(k*{x})',f'{g}({x})=sin(k*{x})'),parameter='k in R'),
            'The pair has the complex product law. Its squared modulus M=f²+g² has M(x+y)=M(x)M(y).',
            'M(0)=1 implies no zeros, and boundedness of M(nx) and M(−nx) forces M(x)=1.',
            'Choose a continuous principal argument near 0. The small interval makes the argument uniquely additive on nearby inputs.',
            'A continuous local additive map is linear by rational subdivision, and the product law extends the angle formula everywhere.',
            'The sine and cosine pair satisfies both original equations and all stated hypotheses.')
    if len(set(match.groups()))!=3:unsupported('The two operands of multiplication must be independent')
    return certificate(lib,'extend_positive_homomorphism',dict(law=match[0],domain='R'),
        dict(multiplicative=True,discontinuous_at=ZERO),
        'For each of the three sign values the product sign equals the product of the signs, including zero.',
        'The left trace −1 and right trace +1 are unequal at zero.')


EXISTENCE_TEXT=tuple(map(re.compile,(
    r'Доказать существование единственной непрерывной y\(x\) на R для уравнения Кеплера y−ε (sin|cos) y=x, 0≤ε<1',
    r'Доказать, что для любого k∈R уравнение cot x=kx на 0<x<π имеет единственный непрерывный корень x\(k\)',
)))
INVERSE_STRUCTURE=re.compile(
    r'(?:(Может ли немонотонная на R функция иметь однозначную обратную\? Исследовать y=x на рациональных и −x на иррациональных)'
    r'|(В каком случае f и обратная f⁻¹ представляют одну и ту же функцию\?)'
    r'|(Доказать, что у разрывной y=\(1\+x²\)sgn x обратная функция непрерывна на своей области)'
    r'|(Для строго монотонной f на \[a,b\], если a≤x_n≤b и f\(x_n\)→f\(a\), доказать x_n→a))')
PARAMETRIC_FACTOR=re.compile(
    r'(?:(Для x=φ\(t\), y=ψ\(t\), α<t<β, дать необходимое и достаточное условие однозначности y\(x\)\. Рассмотреть x=sin²t, y=cos²t)'
    r'|(Когда x=φ\(t\),y=ψ\(t\), a<t<b и x=φ\(χ\(τ\)\),y=ψ\(χ\(τ\)\), α<τ<β, определяют одну и ту же функцию y\(x\)\?)'
    r'|(φ,ψ непрерывны на \(a,b\), A=inf φ, B=sup φ\. Когда существует однозначная f на \(A,B\), для которой ψ\(x\)=f\(φ\(x\)\) во всех a<x<b\?))')
ABSTRACT.update({**dict.fromkeys(ANGLE_TEXT,principal_angles),**dict.fromkeys(EXISTENCE_TEXT,equation_inverse),
                 INVERSE_STRUCTURE:inverse_structure,PARAMETRIC_FACTOR:parametric_factor})


UNIFORM_TEXT=tuple(map(re.compile,(
    r'Сформулировать с положительными кванторами на языке ε–δ, что функция непрерывна на данном множестве, но не равномерно непрерывна',
    rf'Доказать равномерную непрерывность непрерывной на \[({NAME}),\+∞\) функции с конечным пределом при \+∞',
    r'Доказать, что \|sin ([a-z])\|/\1 равномерно непрерывна по отдельности на \(−([0-9]+(?:/[0-9]+)?),0\) и \(0,\2\), но не на их объединении',
    rf'Если ({NAME}) равномерно непрерывна на \[({NAME}),({NAME})\] и на \[\3,({NAME})\], доказать равномерную непрерывность на \[\2,\4\]',
    r'На сколько равных частей достаточно разбить \[([0-9]+(?:[,.][0-9]+)?),([0-9]+(?:[,.][0-9]+)?)\], чтобы колебание ([a-z])² на каждой было меньше ([0-9]+(?:[,.][0-9]+)?)\?',
    rf'Доказать, что сумма и произведение ограниченного числа равномерно непрерывных на интервале \(({NAME}),({NAME})\) функций равномерно непрерывны на этом интервале',
    r'Доказать равномерную непрерывность ограниченной монотонной непрерывной функции на конечном или бесконечном интервале',
    rf'Доказать существование пределов на обоих концах ограниченного интервала \(({NAME}),({NAME})\) для равномерно непрерывной ({NAME})\. Верно ли это для бесконечного интервала\?',
    rf'Для непрерывной ({NAME}) на конечном открытом интервале доказать эквивалентность равномерной непрерывности и возможности непрерывного продолжения на \[({NAME}),({NAME})\]',
    rf'Для ω_({NAME})\(δ\)=sup\{{\|\1\(x₁\)−\1\(x₂\)\|: x₁,x₂∈\(({NAME}),({NAME})\), \|x₁−x₂\|≤δ\}} доказать, что равномерная непрерывность эквивалентна lim\(δ→0\)ω_\1\(δ\)=0',
)))


def uniform_tolerance(task,lib,request):
    from graphs import interval_terms
    from quadrature import enclose
    from tasks import source
    if task.get('quantity')=='square area':
        fields(task,{'quantity','side_range_cm','area_error_cm2'},['side_tolerance','numeric_value'])
        a,b=map(F,task['side_range_cm']);eps=F(task['area_error_cm2'])
        if not 0<a<b or not 0<eps<b*b-a*a:unsupported('Positive side lengths and a nontrivial error threshold are required')
        roots=(m.add(q(b),m.neg(('sqrt',q(b*b-eps)))),m.add(('sqrt',q(b*b+eps)),q(-b)))
        intervals=tuple(tuple(map(q,enclose(z,None))) for z in roots)
        return certificate(lib,'square_oscillation_bound',dict(side_range=(q(a),q(b)),strict_area_error=q(eps)),
            dict(both_lengths_in_range=roots[0],only_nominal_length_in_range=roots[1],numeric_enclosures=intervals,
                 use_strict_side_error=True),
            'Factor the area difference as the absolute side difference times the sum of the two sides.',
            'For separation d and both sides in the interval the maximum is (2b−d)d. If only the nominal side is in the interval it is (2b+d)d.',
            'Both upper envelopes increase up to the relevant tolerance. Solve each quadratic threshold exactly.')
    fields(task,{'quantity','domain','axis','width'},['sleeve_length'])
    if task.get('quantity')!='horizontal cylindrical sleeve sliding over y=cbrt(x)' or task.get('axis')!='parallel to Ox':
        unsupported('The geometry or curve required to build the oscillation is not bound')
    domain=interval_terms(task['domain'],m.context(dict(variable='x')))
    a,b,lc,rc=domain;A=None if isinstance(a,str) else m.num(a);B=None if isinstance(b,str) else m.num(b)
    if A is None or B is None or A!=-B or B<=0 or not lc or not rc:
        unsupported('A symmetric closed source interval is required for an attained sharp oscillation')
    width=task['width'];symbolic=width=='arbitrarily small epsilon';eps=('s','epsilon') if symbolic else q(F(width))
    length=('div',('pow',eps,3),q(4)) if symbolic else q(F(width)**3/4)
    if not symbolic and (F(width)<=0 or m.num(length)>B-A):
        unsupported('The width must define a nontrivial sliding sleeve inside the source interval')
    child=dict(kind='uniform_continuity',function='cbrt(x)',given_domain=task['domain'],variable='x',
               requested_output=['prove_power_bound_for_modulus'])
    request('uniform cube-root modulus on the entire original track',child)
    return certificate(lib,'sharp_cube_root_oscillation',dict(domain=domain,vertical_width=eps,
          width_small_enough=source(('pow',eps,3))+' <= '+source(q(4*(B-A))) if symbolic else True),
        dict(maximum_length=length,unit='horizontal axis unit',equality_attained_at='[-length/2, length/2]'),
        'The cube-root modulus is bounded by the cube root of four times the horizontal distance.',
        'On the centered interval the two cube roots have opposite signs and the difference attains the bound.',
        'The sleeve length cannot exceed the value for which this oscillation equals the prescribed width. If contact is forbidden use a smaller length.')


def uniform_source(task,lib,request,match):
    mode=UNIFORM_TEXT.index(match.re);params=match.groups()
    if mode==0:
        return certificate(lib,'uniform_continuity_quantifiers',dict(domain='D',meaning='positive quantifiers'),
            dict(pointwise='∀a∈D ∀ε>0 ∃δ>0 ∀x∈D: |x−a|<δ ⇒ |f(x)−f(a)|<ε',
                 failure_uniform='∃ε₀>0 ∀δ>0 ∃x,y∈D: |x−y|<δ and |f(x)−f(y)|≥ε₀'),
            'Write the pointwise definition with the center chosen before the radius.',
            'Negate the uniform definition by reversing the quantifiers and the strict value-distance inequality.')
    if mode in (1,3,6):
        if len(params)!=len(set(params)):unsupported('The named endpoints and function must differ')
        premise={1:'continuous on closed ray with a finite limit at its infinite end',
                 3:'uniform on two adjacent closed intervals',
                 6:'bounded monotone and continuous on a real interval'}[mode]
        steps=('Choose tail regions so every value is within ε/2 of the corresponding finite limit.',
               'On the remaining compact interval use uniform continuity. Enlarge the compact part so close crossing pairs are covered.')
        if mode==3:
            steps=('Use a common distance threshold for ε/2 on each interval.',
                   'For a crossing pair insert the shared endpoint. Both distances to it are smaller than the total distance.')
        if mode==6:
            steps=('The bounded monotone values have finite one-sided limits at each endpoint, including any infinite endpoint.',)+steps
        return certificate(lib,'glue_uniform_regions',dict(hypotheses=premise,source_parameters=params),
            dict(uniformly_continuous=True),*steps)
    if mode==2:
        x,radius=params;R=F(radius)
        if not 0<R<=3:unsupported('Signs of the sine branches must be checked throughout the source intervals')
        sides=((f'(-{radius},0)',f'-sin({x})/{x}'),(f'(0,{radius})',f'sin({x})/{x}'))
        for notation,function in sides:
            child=request('uniform continuity on '+notation,dict(kind='uniform_continuity',variable=x,function=function,
                given_domain=notation,requested_output=['uniform_continuity']))
            if not child['value'].get('uniform_continuity'):
                unsupported('A restricted branch lacks the required uniform continuity')
        return certificate(lib,'glue_uniform_regions',dict(variable=x,intervals=[row[0] for row in sides],formula=f'abs(sin({x}))/{x}'),
            dict(uniform_on_each=True,uniform_on_union=False,witness='arguments ±R/(n+1), image distance tends to 2'),
            'On the two source intervals sine has the sign of its argument. Apply the corresponding checkable formulas.',
            'Opposite points approaching zero approach output values −1 and 1, obstructing any uniform threshold across the components.')
    if mode==4:
        a,b,eps=map(lambda s:F(s.replace(',','.')),(*params[:2],params[3]))
        if not 0<=a<b or not eps>0:unsupported('A nonnegative bounded interval and positive error threshold are required')
        step=b-a
        def oscillation(n):
            d=step/n
            return (2*b-d)*d
        lo=0;hi=max(1,ceil(2*b*step/eps))
        while hi-lo>1:
            mid=(lo+hi)//2
            if oscillation(mid)<eps:hi=mid
            else:lo=mid
        if not oscillation(hi)<eps or lo and oscillation(lo)<eps:
            unsupported('Strict threshold and minimality were not checked')
        return certificate(lib,'square_oscillation_bound',dict(interval=(q(a),q(b)),strict_error=q(eps)),
            dict(parts=hi,maximum_oscillation=q(oscillation(hi)),previous_oscillation=q(oscillation(lo)) if lo else None),
            'For an increasing square at fixed width its oscillation is largest on the last subinterval.',
            'Solve the strict inequality by monotone integer search using exact arithmetic.')
    if mode==5:
        return certificate(lib,'bounded_interval_uniform_arithmetic',dict(endpoints=params,number_of_maps='finite',
              uniformly_continuous=True),dict(sum=True,product=True),
            'Subdivide the bounded interval into finitely many increments smaller than a threshold for ε=1. Chaining their differences bounds each function.',
            'For sums use the triangle inequality with the individual thresholds.',
            'For products telescope the difference of products and use the now established uniform bounds on all unchanged factors.')
    if mode in (7,8):
        steps=('Uniform continuity maps every sequence approaching a finite endpoint to a Cauchy sequence.',
               'Interleaving two such sequences proves all have one common finite limit by completeness.')
        if mode==7:
            child=dict(kind='uniform_continuity',variable='x',function='sin(x)',given_domain='(0,+inf)',
                       requested_output=['uniform_continuity'])
            proof=request('uniform continuity of a counterexample on the infinite ray',child)
            if not proof['value'].get('uniform_continuity'):
                unsupported('The proposed function must be uniformly continuous')
            val=dict(finite_endpoints=True,infinite_endpoint=False,counterexample='sin(x)')
            steps+=('The sine counterexample has subsequences of maximum and minimum values along the infinite endpoint.',)
        else:
            val=dict(equivalent=True,extension_unique=True)
            steps+=('Assign those limits to the two endpoints. Conversely apply the compact-interval theorem to a continuous extension.',)
        return certificate(lib,'uniform_endpoint_extension',dict(source_names=params,open_interval=True),val,*steps)
    return certificate(lib,'uniform_continuity_quantifiers',dict(source_names=params,distance_condition='≤δ'),
        dict(equivalent=True,right_limit_of_modulus=ZERO),
        'Uniform continuity at tolerance ε/2 bounds every difference at sufficiently small closed input-distance radius by ε/2, hence also its supremum.',
        'Conversely choose a positive radius with supremum below ε, then each pair inside the radius has difference below ε.')


def real_function_goal(task,lib,request):
    """Bind every source clause before invoking a reusable real-function transition."""
    try:
        kind=task.get('kind',task.get('task_type'))
        if remaining_function_head(task,kind) and lib.data.get('remaining_analysis_proofs'):
            return remaining_function_goal(task,lib)
        if kind=='inverse_function_and_domain':return structured_inverse(task,lib,kind)
        if kind in ('recover_function_by_substitution','recover_function_on_inner_image'):return recover_by_inner_image(task,lib,kind)
        if kind in ('function_compositions','iterated_rational_composition'):return structured_compositions(task,lib,kind)
        if kind=='composition_domain':return domain_preimage(task,lib)
        if kind=='iterate_function_formula':return iterate_radial_map(task,lib)
        if kind=='composition_continuity':return step_compositions(task,lib)
        if kind=='inverse_function_branches':return inverse_branches(task,lib,request)
        if kind=='parameter_curve_function':return parametric_curve(task,lib,request)
        if kind=='uniform_error_tolerance':return uniform_tolerance(task,lib,request)
        if kind=='proof_about_real_functions' and match_interval_closure(task.get('statement')):
            return abstract_interval_closure(task,lib)
        text=source_view(task)
        outputs=(['decision','examples'] if ARITHMETIC_DISCONTINUITY.fullmatch(text) else
                 ['decision','example'] if text.startswith('Всегда ли квадрат разрывной функции') else
                 ['classify_continuity'] if text.startswith('Исследовать ') else
                 ['proof','discontinuity_threshold','continuity_regions_and_values'] if ANGLE_TEXT[2].fullmatch(text) else
                 ['sufficient_number_of_subintervals'] if UNIFORM_TEXT[4].fullmatch(text) else PROOF)
        hint='Рассмотреть функцию F(x)=f²(x)+g²(x).' if COMPLEX_LAW.fullmatch(text) else None
        fields(task,{'statement'},outputs,hint)
        for regex,transition in ABSTRACT.items():
            match=regex.fullmatch(text)
            if match:return transition(task,lib,match)
        for regex,transition in ((MAPPED_CURVE,parametric_curve),(DIFFERENCE,difference_source),(CLAMP_TEXT,clamp_source),
                                 (FUNCTION_EQUATION,functional_source),(COMPLEX_LAW,functional_source),(SIGN_LAW,functional_source),
                                 *((r,uniform_source) for r in UNIFORM_TEXT)):
            match=regex.fullmatch(text)
            if match:return transition(task,lib,request,match)
        match=INVERSE_TEXT.fullmatch(text)
        if match:return inverse_source(task,lib,match)
    except (poly.NotRational,poly.Undefined) as exc:
        raise Unsupported('The bound expression lies outside the checked algebraic chart') from exc
    unsupported('No real-function grammar binds all clauses of this source')


INTERVAL_CLOSURE_FORMS={k:re.compile(text) for k,text in {
    'lower_derivative_root':r'Если (\w+) непрерывна на \[(\w+),\+∞\), \1′\((\w+)\)>(\w+)>0 при \3>\2 и \1\(\2\)<0, доказать единственность действительного корня \1=0 в \(\2,\2−\1\(\2\)/\4\)\.',
    'concave_root':r'(\w+) дважды дифференцируема на \[(\w+),\+∞\), \1\(\2\)=(\w+)>0, \1′\(\2\)<0, \1″\((\w+)\)≤0 при \4>\2\. Доказать существование единственного действительного корня на \(\2,\+∞\)\.',
    'derivative_envelope':r'Для монотонно возрастающей дифференцируемой (\w+) и \|(\w+)′\((\w+)\)\|≤\1′\(\3\) при \3≥(\w+) доказать \|\2\(\3\)−\2\(\4\)\|≤\1\(\3\)−\1\(\4\)\. Дать геометрическую интерпретацию\.',
    'pointwise_order':r'Функция возрастает в точке (\w+), если в некоторой окрестности знак (\w+)\((\w+)\)−\2\(\1\) совпадает со знаком \3−\1\. Доказать возрастание на конечном или бесконечном интервале, если это выполняется в каждой его точке\.',
    'strict_chord':r'Пусть (\w+)″\((\w+)\)([<>])0 при (\w+)<\2<(\w+)\. Доказать выпуклость (снизу|сверху) в смысле строгого сравнения \1\(λ₁x₁\+λ₂x₂\) с λ₁\1\(x₁\)\+λ₂\1\(x₂\) для двух точек интервала, λ₁,λ₂>0, λ₁\+λ₂=1\.',
    'bounded_convex':r'Доказать, что ограниченная выпуклая функция всюду непрерывна и имеет левую и правую производные\.',
    'parallel_secant':r'(\w+) дважды дифференцируема на \((\w+),(\w+)\), \1″\((\w+)\)≠0 для некоторого \4∈\(\2,\3\)\. Доказать существование x₁≠x₂ из \(\2,\3\), для которых \(\1\(x₂\)−\1\(x₁\)\)/\(x₂−x₁\)=\1′\(\4\)\.',
    'two_zero_end_limits':r'(\w+) дважды дифференцируема на \((\w+),\+∞\), \1\((\w+)\)→0 при \3→\2\+0 и при \3→\+∞\. Доказать существование (\w+)∈\(\2,\+∞\) с \1″\(\4\)=0\.',
    'quadratic_nonnegative':r'Исходя из Σ\(aₖx\+bₖ\)²≥0 при действительных x,aₖ,bₖ и k=1,\.\.\.,n, вывести \(Σaₖbₖ\)²≤\(Σaₖ²\)\(Σbₖ²\)\.',
    'quadratic_mean':r'Для положительных x₁,\.\.\.,xₙ доказать \(Σxₖ\)/n≤sqrt\(\(Σxₖ²\)/n\)\.',
    'geometric_mean_induction':r'Для положительных x₁,\.\.\.,xₙ доказать \(Πxₖ\)\^\(1/n\)≤\(Σxₖ\)/n\.(?: Указание: применить математическую индукцию\.)?',
    'power_mean':r'Для положительных (\w+),(\w+) среднее Δ_s=\(\(\1\^s\+\2\^s\)/2\)\^\(1/s\) при s≠0 и Δ_0=lim_\{s→0\}Δ_s\. (Доказать .+)\.',
    'nested_polygon_perimeters':r'При увеличении числа сторон n периметр p_n правильного вписанного в окружность многоугольника возрастает, периметр P_n правильного описанного убывает\. Пользуясь этим, доказать существование общего предела\.',
    'monotone_derivative_counterexample':r'Обязательно ли производная монотонной функции монотонна\? Рассмотреть (\w+)\((\w+)\)=(.+)\.',
    'pointwise_oscillatory_order':r'При (\w+)≠0 (\w+)\(\1\)=(.+), \2\(0\)=0\. Доказать, что функция возрастает в точке 0, но ни в каком интервале \(−ε,ε\), ε>0, не является возрастающей\.',
}.items()}


def match_interval_closure(statement):
    if not isinstance(statement,str):return None
    return next(((kind,hit.groups()) for kind,grammar in INTERVAL_CLOSURE_FORMS.items()
                 if (hit:=grammar.fullmatch(statement))),None)


def closure_certificate(lib,key,value,*argument,**data):
    closure_require(lib.data.get('abstract_interval_closures'),'Нет доказуемой композиции условий на интервале')
    return dict(theorem='real_function.'+key,argument=list(argument),**data),value


def closure_require(ok,reason):
    if not ok:raise Unsupported(reason)


def derivative_root_branches(kind,args,lib):
    closure_require(len(set(args))==len(args),'Точка, переменная и фиксированный порог должны быть связаны независимо')
    if kind=='lower_derivative_root':
        f,a,x,k=args;upper=f'{a}−{f}({a})/{k}'
        return closure_certificate(lib,'root_from_one_sided_affine_bound',
            dict(unique_root=True,interval=[a,upper],interval_open=True),
            'Положительный порог производной даёт строгое возрастание по Лагранжу. В исходном конце значение отрицательно.',
            f'Предлагаем правый конец {upper}, где аффинная нижняя граница равна нулю. Строгое условие на производную даёт положительное значение функции в этом конце.',
            'По теореме о промежуточном значении существует корень строго между концами. Монотонность даёт единственность.',
            function=f,variable=x,endpoint=a,strict_derivative_lower_bound=k,generated_abscissa=upper)
    f,a,A,x=args;upper=f'{a}−{A}/{f}′({a})'
    return closure_certificate(lib,'root_from_one_sided_affine_bound',
        dict(unique_root=True,interval=[a,upper],left_open=True,right_closed=True),
        'Знак второй производной даёт невозрастание первой. Сравнение с её правым значением в левом конце сохраняется на всём хвосте.',
        f'По Лагранжу функция не превосходит касательной в левом конце. Её нуль {upper} даёт конечный конец поиска, где функция неположительна.',
        'Непрерывность даёт корень между положительным началом и неположительным концом. Производная строго отрицательна, поэтому корень один.',
        function=f,variable=x,endpoint=a,affine_upper_slope=f'{f}′({a})',generated_abscissa=upper)


def prove_power_mean(args,lib):
    a,b,goal=args
    embedded=[f'{a}>0',f'{b}>0'];h=f'ln((exp(s*ln({a}))+exp(s*ln({b})))/2)'
    if goal==f'Доказать min({a},{b})≤Δ_s≤max({a},{b})':
        return closure_certificate(lib,'power_mean_order',
            dict(lower=f'min({a},{b})',upper=f'max({a},{b})'),
            'Сравнить среднее степеней с крайними степенями. При отрицательном показателе оба перехода через степени меняют направление, так что итоговый порядок сохраняется.',
            'Для нуля перейти к пределу в тех же замкнутых границах.',positive_inputs=embedded)
    if goal.removesuffix('. Указание: рассмотреть d(ln Δ_s)/ds')==f'Доказать строгое возрастание по s, если {a}≠{b}':
        return closure_certificate(lib,'strict_convex_secant_from_origin',dict(strictly_increasing=True,condition=f'{a}≠{b}'),
            'Положительный логарифмический аргумент позволяет представить ln Δ_s как h(s)/s, где h(0)=0.',
            'Вторая производная h равна произведению двух строго положительных весов на квадрат разности ln a−ln b. При a≠b первая производная строго возрастает.',
            'По Лагранжу h(s)/s равно h′ во внутренней точке отрезка между нулём и s. Поэтому s h′(s)−h(s)>0 на обеих сторонах нуля. Непрерывное продолжение соединяет строго возрастающие ветви.',
            positive_inputs=embedded,auxiliary=h)
    if goal==f'Доказать пределы Δ_s→min({a},{b}) при s→−∞ и Δ_s→max({a},{b}) при s→+∞':
        return closure_certificate(lib,'power_mean_extreme_base',
            dict(left_limit=f'min({a},{b})',right_limit=f'max({a},{b})'),
            'При положительном показателе вынести большее основание, при отрицательном меньшее. Нормированное среднее обеими сторонами лежит между 1/2 и 1.',
            'Логарифм нормированного множителя ограничен, поэтому после деления на s и экспоненты он стремится к единице.',positive_inputs=embedded)
    if goal=='Доказать что при s=0 получается среднее геометрическое':
        return closure_certificate(lib,'extend_logarithmic_secant_by_derivative',
            dict(at_zero=f'sqrt({a}*{b})'),
            'В нуле h(0)=0, а логарифм среднего равен разностному отношению h(s)/s.',
            'Его предел есть h′(0), равный (ln a+ln b)/2. Экспонента возвращает геометрическое среднее.',
            positive_inputs=embedded,auxiliary=h)
    raise Unsupported('Не связаны запрошенные свойства степенного среднего')


def concrete_order_closure(kind,args,task,lib):
    from derivative_proofs import table
    from integrals import affine
    from operations import expression_positions
    from tasks import domain_conditions, known_guard, source
    from verify import same_value
    if kind=='monotone_derivative_counterexample':
        f,x,text=args;raw=m.parse(re.sub(r'\bsin\s+(\w+)',r'sin(\1)',text),x);ctx=m.context(dict(variable=x))
        closure_require(all(known_guard(g,ctx) for g in domain_conditions(raw,True)),'Гладкость конкретной функции на всей прямой не установлена')
        derivative,tree=table(raw,x,lib);waves={e for _,e in expression_positions(derivative) if e[0]=='cos'}
        closure_require(len(waves)==1,'Нужен один ограниченный гармонический член производной')
        w,=waves;angle=w[1];s,t=affine(angle,x)
        p,d=m.rational_form(m.substitute(derivative,{w:('s','harmonicValue')}))
        marker=('s','harmonicValue');const=p.get((),0);coef=p.get(((marker,1),),0)
        closure_require(d=={():1} and set(p)<={() ,((marker,1),)} and const>=abs(coef)>0 and
                        m.num(s) is not None and m.num(s)>0 and m.num(t) is not None,
                        'Для монотонности нужны постоянный порог и ненулевой гармонический размах')
        points=[m.div(m.add(m.mul(q(i),m.PI),m.neg(t)),s) for i in range(3)]
        values=[q(const+coef),q(const-coef),q(const+coef)]
        return closure_certificate(lib,'bounded_derivative_with_oscillating_slope',
            dict(function_increases=True,derivative_monotone=False,witness=list(zip(points,values))),
            'Модуль косинуса не выше единицы, поэтому производная неотрицательна. Её нули возможны лишь в дискретных точках, и на каждом открытом промежутке есть участок строгого роста.',
            'Программа решает три уравнения фазы 0, π и 2π. Значения производной на этих возрастающих абсциссах попеременно отличаются, что исключает оба вида монотонности.',
            derivative=derivative,table_steps=tree)
    x,f,text=args;raw=m.parse(normal(text),x)
    z=('v',x);ctx=m.context(dict(variable=x))
    waves={e for _,e in expression_positions(raw) if e[0]=='sin'}
    closure_require(len(waves)==1 and all(g==('nonzero',z) or known_guard(g,ctx) for g in domain_conditions(raw)),
                'Вне нуля остаётся неопределённость или несколько гармонических ветвей')
    w,=waves;phase=w[1]
    closure_require(phase[0]=='div' and phase[2]==z and m.num(phase[1]) is not None
                and m.num(phase[1])>1 and same_value(raw,m.add(z,m.mul(m.power(z,2),w))),
                'Оценка касается линейного члена с квадратичной огибающей и обратной фазой')
    derivative,tree=table(raw,x,lib);a=phase[1]
    return closure_certificate(lib,'point_order_vs_nearby_slope',
        dict(increases_at_zero=True,monotone_in_any_neighborhood=False,
             witness_abscissas=f'{source(a)}/(2*pi*k), k positive integer'),
        'При 0<|x|<1 множитель 1+x sin(a/x) строго положителен. Приращение в нуле имеет знак x.',
        'Решаем фазовое уравнение a/x=2πk. В этих точках синус равен нулю, косинус равен единице, поэтому производная равна 1−a<0. Точки стремятся к нулю и исключают возрастание в любой окрестности.',
        derivative=derivative,table_steps=tree)


def abstract_interval_closure(task,lib):
    matched=match_interval_closure(task.get('statement'))
    closure_require(matched is not None,'Не разобрана исходная кванторная область сравнения')
    kind,args=matched
    needed={'derivative_envelope':['proof','geometric_interpretation'],
            'bounded_convex':['continuity','both_one_sided_derivatives'],
            'nested_polygon_perimeters':['both_monotonicity_proofs','common_limit_proof'],
            'monotone_derivative_counterexample':['decision','specified_example'],
            'pointwise_oscillatory_order':['local_increase','absence_of_increasing_neighborhood']}
    fields(task,{'statement'},needed.get(kind,['proof']))
    if kind in ('lower_derivative_root','concave_root'):return derivative_root_branches(kind,args,lib)
    if kind=='power_mean':return prove_power_mean(args,lib)
    if kind in ('monotone_derivative_counterexample','pointwise_oscillatory_order'):return concrete_order_closure(kind,args,task,lib)
    if kind=='derivative_envelope':
        p,f,x,a=args
        return closure_certificate(lib,'two_signed_derivative_comparisons',
            dict(bound=f'|{f}({x})−{f}({a})|≤{p}({x})−{p}({a})',
                 geometric_region=f'between {f}({a}) ± ({p}({x})−{p}({a}))'),
            'Поставить две промежуточные цели о возрастании φ+f и φ−f. Обе производные неотрицательны по модульной гипотезе.',
            'Сравнить значения обеих функций с исходной точкой и пересечь оценки. Геометрически график заключён между двумя перенесёнными графиками огибающих.',
            signed_auxiliaries=[f'{p}+{f}',f'{p}−{f}'],initial_point=a)
    if kind=='pointwise_order':
        return closure_certificate(lib,'first_violation_cut_for_pointwise_order',dict(strictly_increasing=True),
            'Для x<y предположить f(y)≤f(x). Локальный знак приращений справа от x исключает нарушения в начальной части отрезка.',
            'Предложить нижнюю грань c непустого множества нарушений. Если c принадлежит ему, слева от c лежат более ранние нарушения. Если нет, локальный рост справа от c исключает нарушения вблизи c. Оба вывода противоречат построению грани.')
    if kind=='strict_chord':
        f,x,sign,a,b,side=args
        closure_require((sign,side) in (('>','снизу'),('<','сверху')),'Знак второй производной не соответствует выпуклости')
        return closure_certificate(lib,'secant_slope_order',
            dict(chord_inequality='below' if sign=='>' else 'above',strict_for_distinct_points=True,equal_for_coincident_points=True),
            'Предложить внутреннюю точку z=λ₁x₁+λ₂x₂. При x₁≠x₂ оба отрезка ненулевые. Лагранж представляет левый и правый секущие наклоны значениями производной в двух упорядоченных точках.',
            'Знак второй производной устанавливает строгий порядок этих наклонов. Умножение на положительные длины даёт сравнение с хордой. При совпадении исходных точек получается равенство.',
            function=f,domain=[a,b],weights='positive and sum to one',intermediate='z=λ₁x₁+λ₂x₂')
    if kind=='bounded_convex':
        return closure_certificate(lib,'secant_slope_order',
            dict(continuous_at_every_interior_point=True,finite_left_and_right_derivatives=True,
             endpoint_counterexample='f(0)=1, f(x)=x^2 for 0<x<=1'),
            'Из выпуклости следуют упорядоченные секущие наклоны для трёх точек. Для каждой внутренней точки выбираем две окружающие точки и получаем конечные верхнюю и нижнюю оценки близких наклонов.',
            'Конечные оценки дают непрерывность. Односторонние наклоны монотонны и ограничены, значит имеют конечные пределы. В замкнутом конце непрерывность требует дополнительного условия.',
            original_scope='interior of the interval of convexity')
    if kind=='parallel_secant':
        f,a,b,xi=args
        return closure_certificate(lib,'common_level_after_affine_subtraction',
            dict(distinct_secant_points_exist=True,slope=f'{f}′({xi})'),
            'Вычесть касательное направление. Производная вспомогательной функции в ξ равна нулю, а её вторая производная там ненулевая.',
            'Разностное отношение первой производной сопоставляет её знак со знаком смещения в достаточно малой окрестности. Поэтому в ξ есть строгий локальный экстремум.',
            'Выбрать общий уровень между экстремальным значением и двумя близкими крайними значениями. Непрерывность даёт по точке на каждой стороне. Равенство значений после вычитания касательной возвращает требуемый наклон.',
            auxiliary=f'{f}(x)−{f}′({xi})*x',relative_scope=[a,b])
    if kind=='two_zero_end_limits':
        f,a,x,z=args
        return closure_certificate(lib,'affine_bound_conflicts_with_two_end_limits',dict(second_derivative_zero_exists=True),
            'Если функция тождественно нулевая, доказательство закончено. Иначе изменить знак при необходимости и выбрать положительное внутреннее значение.',
            'Из двух нулевых пределов выбрать меньшие значения слева и справа. По Лагранжу существуют положительный и затем отрицательный наклоны производной.',
            'Если вторая производная нигде не нулевая, свойство Дарбу фиксирует её знак. Положительный знак противоречит порядку полученных наклонов. Отрицательный знак ограничивает производную сверху отрицательной константой справа, откуда по Лагранжу функция стремится к минус бесконечности.',
            function=f,variable=x,open_left_endpoint=a,witness=z)
    if kind=='quadratic_nonnegative':
        return closure_certificate(lib,'positive_quadratic_minimum',
            dict(inequality='(sum(a_k*b_k))^2<=sum(a_k^2)*sum(b_k^2)'),
            'Собрать квадратный трёхчлен A x²+2B x+C из исходной суммы квадратов. При A>0 предложить точку x=−B/A и подставить её в неотрицательность.',
            'Если A=0, все коэффициенты при x равны нулю. Отдельная нулевая ветвь даёт B=0 и подтверждает равенство.',
            generated_test_point='-B/A when A>0')
    if kind=='quadratic_mean':
        return closure_certificate(lib,'positive_quadratic_minimum',
            dict(inequality='sum(x_k)/n<=sqrt(sum(x_k^2)/n)'),
            'Подставить в неравенство для суммы квадратов векторы (x_k) и (1). Положительность чисел позволяет извлечь квадратный корень с сохранением порядка.',
            paired_vectors=['(x_k)','(1)'])
    if kind=='geometric_mean_induction':
        return closure_certificate(lib,'preserve_average_while_saturating_one_coordinate',
            dict(inequality='product(x_k)^(1/n)<=sum(x_k)/n',method='induction'),
            'Для одного числа равенство. На следующем шаге, если не все числа равны своему среднему A, выбрать пару u≤A≤v.',
            'Заменить пару на A и u+v−A. Второе число положительно, сумма та же. Произведение пары выросло на (A−u)(v−A)≥0.',
            'После отделения множителя A оставшиеся n чисел имеют среднее A. Индукция ограничивает их произведение величиной A^n и завершает исходный шаг.')
    closure_require(kind=='nested_polygon_perimeters','Не установлен общий переход для этой постановки')
    return closure_certificate(lib,'monotone_normalized_polygon_profiles',
        dict(inscribed_strictly_increases=True,circumscribed_strictly_decreases=True,common_limit='2*pi*R'),
        'По половине центрального угла u=π/n и радиусу R получаем периметры 2πR·sin(u)/u и 2πR·tan(u)/u. Угол убывает при n≥3.',
        'Для первого отношения sin u−u cos u>0, его производная от нулевой границы равна u sin u>0. Для второго u sec²u−tan u>0 по той же проверке положительной производной.',
        'Отношения имеют противоположную монотонность по углу. Оба стремятся к единице при уменьшении угла к нулю.',
        auxiliary_angle='pi/n',first_index=3,radius='R>0')


MONOTONE_NORM=(
    r'Доказать \((?P<x>\w+)\^(?P<a>α)\+(?P<y>\w+)\^\2\)\^\(1/\2\)>\(\1\^(?P<b>β)\+\3\^\4\)\^\(1/\4\) при \1,\3>0 и 0<\2<\4\.'
)
CHORD_GOALS={
 'strict_power':r'Доказать и выяснить геометрический смысл: \((\w+)ⁿ\+(\w+)ⁿ\)/2>\(\(\1\+\2\)/2\)ⁿ при \1,\2>0, \1≠\2, n>1\.',
 'strict_exp':r'Доказать и выяснить геометрический смысл: \(eˣ\+eʸ\)/2>e\^\(\(x\+y\)/2\) при x≠y\.',
 'printed_entropy':r'Доказать и выяснить геометрический смысл: (\w+) ln \1\+(\w+) ln \2>\(\1\+\2\)ln\(\(\1\+\2\)/2\) при \1,\2>0\.',
 'weak_abstract':r'Для (\w+)″≥0 на \[(\w+),(\w+)\] доказать \1\(\((\w+)\+(\w+)\)/2\)≤\(\1\(\4\)\+\1\(\5\)\)/2 для любых \4,\5∈\[\2,\3\]\.',
}
EXP_TANGENCY=r'Доказать e\^(\w+)>1\+\1 при \1≠(x₀|\w+)\. Дать геометрическую интерпретацию\.'
AP_GP='У положительных арифметической и геометрической прогрессий одинаковы число членов и соответствующие крайние члены. Доказать, что сумма арифметической прогрессии больше.'
RATIONAL_INFLECTION=r'Доказать, что на y=(.+) три точки перегиба лежат на одной прямой\.'
NORMAL_INFLECTION=r'Найти (\w+)>0, при котором кривая y=\1 exp\(−\1²(\w+)²\)/sqrt\(π\) имеет точки перегиба \2=±(σ|\w+)\.'
CYCLOID_CONCAVITY=r'Исследовать направление вогнутости циклоиды x=(\w+)\(t−sin t\), y=\1\(1−cos t\), \1>0\.'


def remaining_function_head(task,kind):
    if kind in ('rational_stationary_sign_claim','local_maximum_and_monotonicity'):return True
    if kind!='proof_about_real_functions' or not isinstance(task.get('statement'),str):return False
    text=task['statement']
    return text==AP_GP or any(re.fullmatch(p,text) for p in (MONOTONE_NORM,EXP_TANGENCY,
                       *CHORD_GOALS.values(),RATIONAL_INFLECTION,NORMAL_INFLECTION,CYCLOID_CONCAVITY))


def chord_checks(task,lib):
    text=task['statement']
    for key,p in CHORD_GOALS.items():
        hit=re.fullmatch(p,text)
        if hit:break
    else:unsupported('Midpoint identity and domain do not match')
    geometry=key!='weak_abstract'
    fields(task,{'statement'},['proof','geometric_interpretation'] if geometry else ['proof'])
    descriptions={
        'strict_power':('positive half line','n>1','n(n−1)t^(n−2)>0'),
        'strict_exp':('R','distinct points','exp(t)>0'),
        'printed_entropy':('positive half line','distinct points for strictness','1/t>0'),
        'weak_abstract':(f'[{hit[2]},{hit[3]}]' if key=='weak_abstract' else '', 'f″≥0','nonnegative'),
    }
    domain,assumptions,second=descriptions[key]
    data=dict(weak_proof=True,strict_when_distinct=geometry,domain=domain)
    if geometry:data['geometric_interpretation']='The midpoint of the chord lies above the original graph at its midpoint abscissa whenever the abscissae differ.'
    if key=='printed_entropy':
        data.update(printed_claim_holds=False,counterexample=dict(x=ONE,y=ONE,left=ZERO,right=ZERO))
    elif key=='strict_power':require_distinct_chord_names(hit.groups())
    elif key=='weak_abstract':require_distinct_chord_names(hit.groups())
    return certificate(lib,'midpoint_comparison_from_ordered_slopes',dict(domain=domain,conditions=assumptions,
         second_derivative_sign=second),data,
         'Применить теорему Лагранжа на двух половинах с общей серединой. Знак второй производной упорядочивает наклоны равных по длине отрезков.',
         'Сложить неравенства приращений. Строгость следует при разных концах и строго возрастающей производной. В совпадающих концах обе части равны.')


def require_distinct_chord_names(names):
    if len(set(names))!=len(names):unsupported('Printed roles are required to be distinct')


def unnormalized_power_norm_order(task,lib,hit):
    fields(task,{'statement'},['proof'])
    require_distinct_chord_names(hit.groups())
    x,a,y,b=hit.groups()
    return certificate(lib,'strict_power_norm_order_via_unit_normalization',dict(positive_entries=[x,y],ordered_powers=[a,b]),
       dict(proven=True,normalization=f'({x}^{a}+{y}^{a})^(1/{a})'),
       'Разделить оба исходных положительных числа на их норму меньшей степени. Обе доли строго между нулём и единицей, а сумма их меньших степеней равна единице.',
       'Повышение показателя строго уменьшает каждое слагаемое. Взять положительный корень и вернуть первоначальный масштаб.')


def abstract_false_strictness(task,lib):
    text=task['statement']
    if text==AP_GP:
        fields(task,{'statement'},['proof'])
        return certificate(lib,'strict_comparison_requires_a_distinct_interior_term',dict(progression_terms_positive=True),
            dict(printed_claim_holds=False,counterexample=dict(arithmetic=[ONE,q(2)],geometric=[ONE,q(2)],both_sums=q(3)),
                 strict_if='at least three terms and distinct endpoints'),
            'Любые две положительные крайние точки задают одинаковую двухчленную арифметическую и геометрическую прогрессии. Поэтому заявленная строгая оценка не следует из исходного текста.',
            'Внутренние члены сравниваются взвешенным неравенством арифметического и геометрического средних. Для разных концов и наличия внутреннего члена сравнение строгое.')
    fields(task,{'statement'},['proof','geometric_interpretation'])
    hit=re.fullmatch(EXP_TANGENCY,text);t,z=hit.groups();require_distinct_chord_names((t,z))
    return certificate(lib,'strict_comparison_requires_a_distinct_interior_term',dict(function='exp',anchor=ZERO,excluded_symbol=z),
        dict(printed_claim_holds=False,counterexample=dict(argument=ZERO,excluded_point=ONE,left=ONE,right=ONE),
             corrected_domain=f'{t}!=0',geometric_interpretation='The tangent at the zero coordinate meets the exponential graph there alone.'),
        'Разность exp(x)−1−x в нуле равна нулю. Ее производная меняет знак с отрицательного на положительный, поэтому равенство возможно ровно при x=0.',
        'Печатное исключение произвольной переменной точки не исключает ноль. Подстановка ненулевой исключённой точки оставляет контрпример внутри исходного условия.')


def collinear_rational_inflections(task,lib,match):
    from verify import same_value
    from derivative_proofs import table
    from tasks import domain_conditions
    fields(task,{'statement'},['three_inflections','collinearity_proof'])
    x='x';u=('v',x);raw=term(match[1],x)
    if raw[0]!='div' or set(domain_conditions(raw))!={('nonzero',raw[2])}:unsupported('Need a linear numerator on a positive quadratic with the same original domain')
    p,pd=poly.rf(raw[1],x);d,dd=poly.rf(raw[2],x)
    if len(p)!=2 or len(d)!=3 or len(pd)!=1 or len(dd)!=1 or pd[0]<=0 or dd[0]<=0:unsupported('Unresolved rational degree')
    h=-d[1]/(2*d[2]);width=(d[0]-d[1]*d[1]/(4*d[2]))/d[2]
    a=p[1]*dd[0]/(pd[0]*d[2]);b=(p[0]+h*p[1])*dd[0]/(pd[0]*d[2])
    if a==0 or width<=0 or any(e[0]=='div' for e in nodes(raw[2])):unsupported('Need nonzero slope and positive translated quadratic on the source domain')
    shifted=m.add(u,q(-h));line=m.div(m.add(m.mul(q(a),shifted),q(3*b)),q(4*width))
    first,pr=table(raw,x,lib);second,pr2=table(first,x,lib)
    C=m.add(m.add(m.mul(q(a),m.power(shifted,3)),m.mul(q(3*b),m.power(shifted,2))),
            m.add(m.mul(q(-3*a*width),shifted),q(-b*width)))
    den=m.add(m.power(shifted,2),q(width))
    if not same_value(second,m.div(m.mul(q(2),C),m.power(den,3))) or not same_value(m.add(raw,m.neg(line)),m.div(m.neg(C),m.mul(q(4*width),den))):
        unsupported('Exact second derivative and chord residual do not share the same cubic')
    # Declared a!=0 and width>0 imply the discriminant is strictly positive.
    discr=108*width*(b*b+a*a*width)**2
    return certificate(lib,'inflection_coordinates_from_common_cubic_residual',dict(original_domain='R',quadratic_center=q(h)),
         dict(number_of_inflections=3,abscissae='three distinct real roots of the given cubic',cubic=C,collinearity_line=line),
         'Проделать точный сдвиг и выделить положительный квадратный знаменатель. Числитель второй производной и разность с найденной прямой имеют один кубический множитель.',
         'Положительный дискриминант даёт три простых действительных корня. В них знак второй производной меняется, а разность с прямой обращается в ноль.',
         discriminant=q(discr),table_steps=(*pr,*pr2))


def gaussian_inflection_parameter(task,lib,hit):
    fields(task,{'statement'},['parameter_condition','proof'])
    h,x,s=hit.groups();require_distinct_chord_names((h,x,s))
    return certificate(lib,'positive_envelope_exposes_inflection_equation',dict(positive_scale=h,symmetric_target=s),
        dict(nonzero_target_scale=f'1/(sqrt(2)*abs({s}))',zero_target='no positive scale',inflection_abscissae=f'±1/(sqrt(2)*{h})'),
        'Дважды продифференцировать гауссову функцию. Положительный множитель не влияет на знак, остаётся 2 h² x²−1.',
        'Оба простых симметричных нуля меняют знак. Приравнять их модуль требуемому, сохранив h>0, и исключить нулевую цель.')


def cycloid_arc_concavity(task,lib,hit):
    fields(task,{'statement'},['concavity_on_all_arcs','cusp_scope'])
    a=hit[1]
    return certificate(lib,'concavity_transport_along_regular_cycloidal_arcs',dict(scale=a,condition=a+'>0'),
        dict(regular_phase_cells='2*pi*k<t<2*pi*(k+1)',concavity='concave_down',
             second_derivative=f'-1/({a}*(1-cos(t))^2)',cusp_phase='t=2*pi*k',cusp_slopes=('negative infinity','positive infinity')),
        'На каждой фазовой ячейке горизонтальная скорость положительна. Выразить первый наклон через cot(t/2) и продифференцировать его по параметру с делением на горизонтальную скорость.',
        'На стыке обе скорости обращаются в ноль, но горизонтальное и вертикальное смещения имеют соответственно третий и второй порядки. Это определяет бесконечные противоположные наклоны в вершине.')


def stationary_oscillation_witness(task,lib):
    from tasks import domain_conditions
    from verify import same_value
    source=task.get('source',{})
    if (set(task)-BASE-{'branches'} or set(source)-SOURCE_FIELDS-{'literal_requirement','printed_instruction'} or
            source.get('literal_requirement') not in (None,'Decide whether a maximum forces monotonicity on each side in a small neighborhood, and analyze the printed example.') or
            source.get('printed_instruction') or task.get('requested_output') not in (None,['decision','counterexample'])):
        unsupported('An additional claim remains')
    branches=task['branches'];x='x';v=('v',x)
    if len(branches)!=2 or [b[0] for b in branches]!=['x!=0','x=0']:unsupported('Missing assigned center and punctured branches')
    e,center=(m.parse(normal(b[1]),x) for b in branches)
    u=m.simplify(m.add(center,m.neg(e)));z=m.div(u,m.power(v,2))
    wave=('sin',m.div(ONE,v));a=m.simplify(m.substitute(z,{wave:ZERO}));b=m.simplify(m.substitute(z,{wave:ONE}))
    b=m.simplify(m.add(b,m.neg(a)));A,B=map(m.num,(a,b))
    rebuilt=m.add(center,m.neg(m.mul(m.power(v,2),m.add(a,m.mul(b,wave)))))
    if A is None or B is None or not A>abs(B)>0 or not same_value(e,rebuilt) or (
            not m.constant_defined(center,{}) or set(domain_conditions(e))-set(domain_conditions(wave))):
        unsupported('The checked amplitude does not prove a strict maximum with unending changes of slope')
    return certificate(lib,'oscillatory_slope_at_strict_extremum',dict(original_center=center,amplitude=(a,b)),
        dict(strict_global_maximum_at_zero=True,monotone_on_no_one_sided_neighborhood=True,
             witness_points='x=1/(k*pi), k nonzero integers, k large in absolute value',derivative_at_witness='B*(-1)^k-2*A/(k*pi)'),
        'Положительная амплитуда ограничена снизу A−|B|>0. Это доказывает строгий максимум в нуле.',
        'Табличная производная на проколотой прямой в точках 1/(kπ) содержит знакопеременную постоянную компоненту и затухающий остаток. Обе чётности встречаются с каждой стороны.')


def remaining_function_goal(task,lib):
    if task['kind']=='rational_stationary_sign_claim':return stationary_rational_sign(task,lib)
    if task['kind']=='local_maximum_and_monotonicity':return stationary_oscillation_witness(task,lib)
    text=task.get('statement','')
    if text==AP_GP or re.fullmatch(EXP_TANGENCY,text):return abstract_false_strictness(task,lib)
    for p,fn in ((MONOTONE_NORM,unnormalized_power_norm_order),(RATIONAL_INFLECTION,collinear_rational_inflections),
                 (NORMAL_INFLECTION,gaussian_inflection_parameter),(CYCLOID_CONCAVITY,cycloid_arc_concavity)):
        hit=re.fullmatch(p,text)
        if hit:return fn(task,lib,hit)
    return chord_checks(task,lib)


def stationary_rational_sign(task,lib):
    meta=task.get('source',{})
    if (set(task)-BASE-{'given','claim'} or set(meta)-SOURCE_FIELDS-{'literal_requirement'} or
            meta.get('literal_requirement') not in (None,'Prove sgn(f″(x0))=sgn(P1′(x0)) under the printed hypotheses.')):
        unsupported('The full printed stationary-point claim is required')
    if task.get('given')!=['f(x)=P(x)/Q(x)','f-prime(x)=P1(x)/Q2(x)','P1(x0)=0','Q(x0) nonzero'] or (
            task.get('claim')!='sgn(f-second(x0))=sgn(P1-prime(x0))' or task.get('requested_output') not in (None,['proof'])):
        unsupported('The pivot, vanishing numerator and comparison must all be bound')
    return certificate(lib,'stationary_quotient_sign_requires_positive_denominator',dict(pivot_name='Q2',stationary_numerator='P1'),
         dict(printed_claim_holds=False,counterexample=dict(f='-x^2',P='-x^2',Q=ONE,
                P1='2*x',Q2=q(-1),at=ZERO,second_derivative=q(-2),numerator_derivative=q(2)),
              if_pivot_is_original_square='At a stationary point f″=P1′/Q^2, so the claimed signs agree.'),
         'При нулевом числителе правило частного даёт f″(x₀)=P₁′(x₀)/Q₂(x₀). Знак знаменателя нельзя вывести из ненулевости исходного Q.',
         'Если Q₂ является отдельным полиномом, выбранный отрицательный постоянный знаменатель меняет знак. Если имеется в виду Q в квадрате, знаменатель строго положителен и равенство знаков следует.')
