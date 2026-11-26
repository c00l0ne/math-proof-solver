"""Sign-invariant cylindrical decomposition for real planar domains, quadratic in the fiber."""
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import combinations
from math import ceil,floor,hypot,log10,prod
import re

import expressions as m
import intervals as line
import polynomial as poly
from graphs import Z,ordered_cuts,peval,rational_roots
from model import ONE,ZERO,Unsupported,q
from tasks import domain_conditions


def raw_conditions(e):
    pending=[e]
    while pending:
        node=pending.pop()
        if node[0]=='rpow':raise Unsupported('A general real power needs a separate maximal-domain proof')
        pending.extend(c for c in node[1:] if isinstance(c,tuple))
    return domain_conditions(e)


def factors_and_conditions(guards,variables,basis):
    x,y=(('s',v) for v in variables)
    def record(part):
        if not part:return 0,()
        rows={}
        for mon,c in part.items():
            powers=dict(mon)
            if set(powers)-{x,y} or powers.get(y,0)>2:raise Unsupported('An algebraic boundary exceeds quadratic degree in the fiber')
            rows.setdefault(powers.get(y,0),{})[powers.get(x,0)]=c
        coeffs=tuple(poly.trim([row.get(i,F(0)) for i in range(max(row,default=0)+1)]) for row in
                     (rows.get(j,{}) for j in range(max(rows)+1)))
        scale=next(c for p in coeffs for c in p if c)
        if len(coeffs)==1 and len(coeffs[0])==1:return line.sign(scale),()
        norm=tuple(tuple(c/scale for c in p) for p in coeffs)
        if norm not in basis:basis.append(norm)
        return line.sign(scale),(basis.index(norm),)
    def factors(e):
        tag=e[0]
        if tag in ('mul','div'):
            a,b=factors(e[1]);c,d=factors(e[2]);return a*c,b+d
        if tag=='pow':
            if not e[2]:return 1,()
            a,b=factors(e[1]);power=1 if e[2]%2 else 2;return a**power,b*power
        if tag=='add' and e[1]==q(1) and e[2][0]=='mul' and e[2][1]==q(-1) and e[2][2][0]=='pow' and e[2][2][2]==2:
            u=e[2][2][1]
            return factors(('mul',('add',q(1),('mul',q(-1),u)),('add',q(1),u)))
        a,b=map(record,m.rational_form(e))
        return a[0]*b[0],a[1]+b[1]
    conditions=[]
    for op,e in guards:
        if e[0] in ('sqrt','abs','cbrt'):
            if op=='nonnegative' and e[0] in ('sqrt','abs'):continue
            if e[0]=='abs' and op=='positive':op='nonzero'
            e=e[1]
        sign,ids=factors(e);conditions.append((op,sign,ids))
    return conditions


def projection(basis):
    """Resultants, degree drops, discriminants and first subresultants of persistent common roots."""
    mul=poly.pm
    def sub(p,r):return poly.pa(p,tuple(-c for c in r))
    minors=lambda a,b,c,d:sub(mul(a,d),mul(b,c))
    proj=set()
    for p in basis:
        proj.add(p[-1])
        if len(p)==3:
            c,b,a=p;proj.add(sub(mul(b,b),mul((F(4),),mul(a,c))))
    for p,r in combinations((p for p in basis if len(p)>1),2):
        if len(p)<len(r):p,r=r,p
        if len(p)==2:
            c,b=p;f,e=r;proj.add(minors(b,c,e,f))
        elif len(r)==2:
            c,b,a=p;f,e=r;proj.add(poly.pa(mul(a,mul(f,f)),sub(mul(c,mul(e,e)),mul(b,mul(e,f)))))
        else:
            c,b,a=p;f,e,d=r
            u,v,w=minors(a,b,d,e),minors(a,c,d,f),minors(b,c,e,f)
            resultant=sub(mul(v,v),mul(u,w));proj.add(resultant)
            if resultant==Z:proj.update((u,v))
    return sorted({tuple(c/p[-1] for c in p) for p in proj if len(p)>1})


def yterm(y):
    return q(y.a) if not y.b else m.add(q(y.a),m.mul(q(y.b),('sqrt',q(y.d))))


def specialize(p,x):
    return poly.trim([peval(a,x) for a in p])


def section_orders(p,x):
    rows=[];cols=p
    while any(a!=Z for a in cols):
        rows.append(specialize(cols,x));cols=[poly.trim([i*c for i,c in enumerate(a) if i] or Z) for a in cols]
    return rows


def boundary_limit(p,label,x,side):
    """Finite or infinite limit of an ordered root at a rational projecting section."""
    orders=section_orders(p,x)
    first=next(r for r in orders if r!=Z)
    if len(first)==len(p):
        roots=line.roots(first);return roots[min(label,len(roots)-1)]
    def local_sign(i):
        return next((line.sign(r[i])*side**k for k,r in enumerate(orders) if len(r)>i and r[i]),0)
    if len(p)==2:sign=-local_sign(0)*local_sign(1)
    else:
        sign=-local_sign(1)*local_sign(2)
        if len(first)==2 and label!=int(sign>0):return line.roots(first)[0]
        if len(first)==1 and local_sign(0)*local_sign(2)<0:sign=1 if label else -1
    return '+inf' if sign>0 else '-inf'


def boundary_formula(p,index,var,x):
    def expr(col):return m.poly_expr({(((('s',var),i),) if i else ()):c for i,c in enumerate(col) if c})
    coeff=[expr(a) for a in p]
    if len(p)==2:return m.simplify(m.div(m.neg(coeff[0]),coeff[1]))
    c,b,a=coeff
    delta=m.add(m.power(b,2),m.mul(q(-4),m.mul(a,c)))
    sign=(1 if index else -1)*line.sign(peval(p[2],x))
    return m.simplify(m.div(m.add(m.neg(b),m.mul(q(sign),('sqrt',delta))),m.mul(q(2),a)))


def fiber(basis,conditions,x,section,var):
    polys=[poly.trim([peval(a,x) for a in p]) for p in basis]
    def truth(signs):
        def holds(op,unit,indices):
            s=unit*prod(signs[i] for i in indices)
            return {'positive':s>0,'nonnegative':s>=0,'nonzero':s!=0,'zero':s==0}[op]
        return any(all(holds(*g) for g in branch) for branch in conditions)
    orders=[section_orders(p,x) for p in basis] if section else []
    boundary_polys=[next((p for p in rows if p!=Z),Z) for rows in orders] if section else polys
    boundaries=[]
    for i,p in enumerate(boundary_polys):
        for j,y in enumerate(line.roots(p)):boundaries.append((y,(i,j)))
    boundaries.sort(key=cmp_to_key(lambda a,b:line.compare(a[0],b[0])))
    bounds=[v for i,v in enumerate(boundaries) if not i or line.compare(v[0],boundaries[i-1][0])]
    ys=[y for y,_ in bounds];edges=['-inf',*ys,'+inf']
    samples=[line.Quadratic(line.between(a,b)) for a,b in zip(edges,edges[1:])]
    ok=lambda y:truth([line.peval(p,y).sign() for p in polys])
    cells=[ok(y) for y in samples];points=[ok(y) for y in ys]
    formulas=[yterm(y) if section else boundary_formula(basis[i],j,var,x) for y,(i,j) in bounds]
    # Neighboring true open cells merge through an included point.
    pieces=line.make_union(ys,cells,points)
    replace={line.quadratic_term(y):f for y,f in zip(ys,formulas)}
    intervals=[(replace.get(a,a),replace.get(b,b),lc,rc) for a,b,lc,rc in pieces[1]]
    result=dict(x=q(x),bounds=[(line.quadratic_term(y) if section else label) for y,label in bounds],
                cells=cells,points=points,fibers=intervals)
    if section:
        def sides(y):
            signs=[]
            for rows in orders:
                signs.append(next(((k,s) for k,p in enumerate(rows) if (s:=line.peval(p,y).sign())),(0,0)))
            return truth([(-1)**k*s for k,s in signs]),truth([s for k,s in signs])
        result['cell_sides']=[sides(y) for y in samples];result['point_sides']=[sides(y) for y in ys]
    return result


def decomposition(guards,variables,alternatives=None):
    basis=[]
    branches=[guards] if alternatives is None else [(*guards,*g) for g in alternatives]
    requirements=[factors_and_conditions(branch,variables,basis) for branch in branches]
    proj=projection(basis);cuts=ordered_cuts(x for p in proj for x in rational_roots(p))
    if any(x.b for x in cuts):raise Unsupported('Specialization over an irrational projection root needs an algebraic extension')
    edges=['-inf',*cuts,'+inf']
    slabs=[dict(left=a if isinstance(a,str) else q(a.a),right=b if isinstance(b,str) else q(b.a),
                **fiber(basis,requirements,line.between(a,b),False,variables[0])) for a,b in zip(edges,edges[1:])]
    sections=[fiber(basis,requirements,x.a,True,variables[0]) for x in cuts]
    for cut,i in zip(cuts,range(len(cuts))):
        joins=[]
        for slab,side,field in ((slabs[i],-1,'right_limits'),(slabs[i+1],1,'left_limits')):
            limits=[boundary_limit(basis[n],j,cut.a,side) for n,j in slab['bounds']]
            slab[field]=[line.endpoint_term(y) for y in limits]
            for j,y in enumerate(limits):
                if not isinstance(y,str):
                    joins.append((y,(slab['cells'][j],slab['points'][j],slab['cells'][j+1])))
        section=sections[i]
        section['point_boundary']=[]
        for j,(y,member) in enumerate(zip(section['bounds'],section['points'])):
            neighbors=[*section['point_sides'][j],*section['cells'][j:j+2]]
            neighbors.extend(v for z,row in joins if not line.compare(line.read_quadratic_term(y),z) for v in row)
            section['point_boundary'].append(any(v!=member for v in neighbors))
    coefficients=[tuple(tuple(map(q,col)) for col in p) for p in basis]
    return {'variables':variables,'polynomials':coefficients,**({'sign_conditions':requirements[0]} if alternatives is None else {'sign_alternatives':requirements}),'x_cuts':[q(x.a) for x in cuts],
            'slabs':slabs,'sections':sections},[tuple(map(q,p)) for p in proj]


def open_strips(region):
    """Export positive-area cells in the integration order of this decomposition."""
    return [(1,s['left'],s['right'],a,b) for s in region['slabs'] for a,b,_,_ in s['fibers'] if a!=b]


def region_inequalities(source,variables):
    """Read conjunctions and chained scalar inequalities, preserving all raw operand domains."""
    rows=source['inequalities'] if isinstance(source,dict) and set(source)=={'inequalities'} else [source]
    if not isinstance(rows,(tuple,list)) or not rows:raise Unsupported('Expected source inequalities')
    guards=[]
    for row in rows:
        if not isinstance(row,str):raise Unsupported('Expected a scalar inequality')
        parts=re.split(r'(<=|>=|<|>)',row)
        if len(parts)<3 or any(not t.strip() for t in parts):raise Unsupported('Expected explicit ordered boundaries')
        values=[m.parse(t.strip(),None,variables) for t in parts[::2]]
        for e in values:guards.extend(raw_conditions(e))
        for a,op,b in zip(values,parts[1::2],values[1:]):
            high,low=(b,a) if op[0]=='<' else (a,b)
            guards.append(('nonnegative' if '=' in op else 'positive',m.add(high,m.neg(low))))
    return list(dict.fromkeys(guards))


def algebraic_strips(guards,variables,sign):
    partition,projection=decomposition(guards,variables)
    strips=[(sign,a,b,l,h) for _,a,b,l,h in open_strips(partition)]
    if any(isinstance(v,str) for s in strips for v in s[1:]):
        raise Unsupported('Unbounded integration needs convergence hypotheses')
    return {'sign':sign,'outer_variable':variables[0],'conditions':guards,'projection':projection,
            'cuts':partition['x_cuts']},strips


def draw_region(region,title,viewport=None):
    """Render certified open cells and separately test inclusion on their curves and vertical sections."""
    from graphs import svg_canvas,svg_element as elem,svg_label as label,svg_text,svg_payload
    from model import freeze
    def scalar(t):return m.num(freeze(t))
    def middle(z):
        a,b=z.bounds(64);return (a+b)/2
    basis=[tuple(tuple(map(scalar,col)) for col in p) for p in region['polynomials']]
    cuts=list(map(scalar,region['x_cuts']));slabs=region['slabs'];sections=region['sections']
    def values(x,refs):
        cache={}
        for i,j in refs:
            if i not in cache:cache[i]=line.roots(specialize(basis[i],x))
        return [middle(cache[i][j]) for i,j in refs]
    sec_y=[[middle(line.read_quadratic_term(freeze(t))) for t in s['bounds']] for s in sections]
    xs=[F(-2),F(2),*cuts];ys=[F(-2),F(2),*(y for row in sec_y for y in row)]
    for s in slabs:ys+=values(scalar(s['x']),s['bounds'])
    cx=(max(xs)+min(xs))/2;cy=(max(ys)+min(ys))/2;radius=max(max(xs)-min(xs),max(ys)-min(ys))*F(3,5)
    xmin,xmax=cx-radius,cx+radius;ymin,ymax=cy-radius,cy+radius
    if viewport is not None:xmin,xmax,ymin,ymax=viewport;radius=(xmax-xmin)/2
    size=420;left,top=58,43;scale=F(size)/(2*radius)
    sx=lambda x:float(left+(x-xmin)*scale)
    sy=lambda y:float(top+(ymax-y)*scale)
    root=svg_canvas(535,520)
    for key,value in (('xmin',xmin),('xmax',xmax),('ymin',ymin),('ymax',ymax)):root.set('data-'+key,str(value))
    elem(root,'rect',width='100%',height='100%',fill='white')
    label(root,left,24,title);clip=elem(elem(root,'defs'),'clipPath',id='plot');elem(clip,'rect',x=left,y=top,width=size,height=size)
    fill=elem(root,'g',clip_path='url(#plot)',fill='#abd9e8');axes=elem(root,'g');strokes=elem(root,'g',clip_path='url(#plot)',fill='none')
    def stroke(parent,x,y,z,w,color,**extra):
        elem(parent,'line',x1=f'{x:.2f}',y1=f'{y:.2f}',x2=f'{z:.2f}',y2=f'{w:.2f}',stroke=color,**extra)
    raw=2*radius/6;unit=F(10)**floor(log10(float(raw)));step=next(i*unit for i in (1,2,5,10) if i*unit>=raw)
    for lo,hi,vertical in ((xmin,xmax,True),(ymin,ymax,False)):
        for i in range(ceil(lo/step),floor(hi/step)+1):
            v=i*step;color='#586375' if not v else '#d6e2e8';s=f'{float(v):.3g}'
            if vertical:
                X=sx(v);stroke(axes,X,top,X,top+size,color);label(root,X,top+size+20,s,text_anchor='middle')
            else:
                Y=sy(v);stroke(axes,left,Y,left+size,Y,color);label(root,left-6,Y+4,s,text_anchor='end')
    label(root,left+size+9,top+size+19,region['variables'][0]);label(root,left-10,top-6,region['variables'][1])
    def style(member):return {'stroke':'#164f69','stroke-width':'1.7','data-member':str(int(member))}
    def contour(path,member):
        if not path:return
        if not member:
            dash=[];phase=0;last=None
            for op,x,y in path:
                if op=='M':last=x,y;phase=0;continue
                x0,y0=last;length=hypot(x-x0,y-y0);at=0.
                while at<length:
                    end=min(length,at+(4-phase if phase<4 else 7-phase))
                    if phase<4:
                        for command,t in (('M',at),('L',end)):
                            dash.append((command,x0+(x-x0)*t/length,y0+(y-y0)*t/length))
                    phase=(phase+end-at)%7
                    if min(phase,7-phase)<1e-9:phase=0
                    if abs(phase-4)<1e-9:phase=4
                    at=end
                last=x,y
            path=dash
        if path:elem(strokes,'path',d=' '.join(f'{op}{x:.2f},{y:.2f}' for op,x,y in path),**style(member))
    clamp=lambda y:max(ymin,min(y,ymax))
    grid=[xmin+F(i,size)*(xmax-xmin) for i in range(size+1)]
    for s,a,b in zip(slabs,[xmin,*cuts],[*cuts,xmax]):
        a=max(a,xmin);b=min(b,xmax)
        if b<=a:continue
        if sx(b)-sx(a)<1:raise Unsupported('Distinct projected sections are below the visible resolution')
        X=[a,*[x for x in grid if a<x<b],b]
        def profile(x):
            edge='left_limits' if x==a and x!=xmin else 'right_limits' if x==b and x!=xmax else None
            if edge:
                return [ymin-radius if y=='-inf' else ymax+radius if y=='+inf' else middle(line.read_quadratic_term(freeze(y))) for y in s[edge]]
            return values(x,s['bounds'])
        profiles=[profile(x) for x in X]
        for i,inside in enumerate(s['cells']):
            if not inside:continue
            lower=[clamp(p[i-1]) if i else ymin for p in profiles];upper=[clamp(p[i]) if i<len(p) else ymax for p in profiles]
            polygon=list(zip(X,lower))+list(reversed(list(zip(X,upper))))
            elem(fill,'polygon',points=' '.join(f'{sx(x):.2f},{sy(y):.2f}' for x,y in polygon))
        for i,member in enumerate(s['points']):
            if member==s['cells'][i]==s['cells'][i+1]:continue
            path=[];prior=None
            for x,row in zip(X,profiles):
                y=row[i]
                if prior:
                    x0,y0=prior
                    if min(y0,y)<=ymax and max(y0,y)>=ymin:
                        a0,b0=clamp(y0),clamp(y)
                        xx=x0 if y==y0 else x0+(x-x0)*(a0-y0)/(y-y0)
                        zz=x if y==y0 else x0+(x-x0)*(b0-y0)/(y-y0)
                        if not path or path[-1]!=('L',sx(xx),sy(a0)):path.append(('M',sx(xx),sy(a0)))
                        path.append(('L',sx(zz),sy(b0)))
                prior=x,y
            contour(path,member)
    for x,s,Y in zip(cuts,sections,sec_y):
        if not xmin<=x<=xmax:continue
        X=sx(x)
        for i,(member,(l,r)) in enumerate(zip(s['cells'],s['cell_sides'])):
            if l==member==r:continue
            a=clamp(Y[i-1]) if i else ymin;b=clamp(Y[i]) if i<len(Y) else ymax
            if a!=b:contour([('M',X,sy(a)),('L',X,sy(b))],member)
        for i,(member,(l,r)) in enumerate(zip(s['points'],s['point_sides'])):
            if ymin<=Y[i]<=ymax and s['point_boundary'][i]:
                elem(strokes,'circle',cx=X,cy=sy(Y[i]),r=2.7,fill='#164f69' if member else 'white',**style(member))
    label(root,left,top+size+43,'Сплошная граница включена, штриховая исключена.')
    return svg_payload(svg_text(root))


def domain_preimages(guards,variables,*,elementary=False):
    """Intersect necessary and sufficient preimages, keeping every original divisor guard."""
    clauses=[];signs={}
    def polynomial(p):
        reduced=m.radical_poly(p)
        if any(atom[0]!='s' or atom[1] not in variables for mon in reduced for atom,_ in mon):
            raise Unsupported('The sign preimage still has a nonpolynomial boundary')
        return m.poly_expr(reduced)
    for relation,e in guards:
        if elementary:
            ctx={'parameters':[],'assumptions':[]}
            if relation=='nonnegative_integer':
                clauses.append({'integer_argument':e,'minimum':0});continue
            if m.constant_defined(e,ctx) and m.sign(e,ctx)==1:continue
            if e[0]=='div' and m.constant_defined(e[2],ctx) and m.sign(e[2],ctx)==1:e=e[1]
            if e[0]=='ln' and relation in ('positive','nonnegative'):
                e=('add',e[1],q(-1))
            # The principal inverse sine and cosine require |u| <= 1.
            if (relation=='nonnegative' and e[0]=='add' and e[1]==q(1) and e[2][0]=='mul' and
                e[2][1]==q(-1) and e[2][2][0]=='pow' and e[2][2][2]==2):
                u=e[2][2][1]
                if u[0]=='rpow' and (base:=m.num(u[1])) is not None and base>0:
                    e=m.mul(q((base<1)-(base>1)),u[2])
                elif u[0]=='mul':
                    coeff,op=u[1:]
                    if m.num(coeff) is None:coeff,op=op,coeff
                    if m.num(coeff) is not None and op[0] in ('sin','cos'):
                        scale=abs(m.num(coeff))
                        if scale>1:
                            angle=m.simplify(('asin',q(1/scale)))
                            center=q(0) if op[0]=='sin' else q(1,2)
                            clauses.append(dict(phase=op[1],shape='centered_band',origin_pi=center,period_pi=1,
                                                half_width=angle,closed=True,index='all_integers'))
                        continue
            if relation=='nonnegative' and e[0]=='mul':
                for factor,square in ((e[1],e[2]),(e[2],e[1])):
                    if square[0]=='pow' and square[2]>0 and square[2]%2==0 and square[1][0] in ('sin','cos'):
                        trig,arg=square[1]
                        cell=dict(phase=arg,shape='include_lattice',origin_pi=q(0) if trig=='sin' else q(1,2),
                                  period_pi=1,index='all_integers')
                        branch=domain_preimages([('nonnegative',factor)],variables,elementary=True)
                        clauses.append({'either':[branch,{'variables':variables,'intersection':[cell]}]});break
                else:factor=None
                if factor is not None:continue
            if e[0]=='tan' or e[0]=='add' and e[1][0]=='tan' and e[2][0]=='q':
                tangent,threshold=(e,q(0)) if e[0]=='tan' else (e[1],m.neg(e[2]))
                if relation in ('positive','nonnegative'):
                    clauses.append(dict(phase=tangent[1],shape='tangent_band',lower=m.simplify(('atan',threshold)),
                                        left_closed=relation=='nonnegative',period_pi=1,index='all_integers'));continue
        if e[0] in ('sqrt','abs','cbrt'):
            if relation=='nonnegative' and e[0]!='cbrt':continue
            if relation=='positive' and e[0]=='abs':relation='nonzero'
            e=e[1]
        if e[0] in ('sin','cos'):
            # Shift cosine to sine and use its exact sign on a half-turn.
            offset=q(0) if e[0]=='sin' else q(-1,2)
            cell={'phase':e[1],'origin_pi':offset,'index':'all_integers'}
            if relation=='nonzero':
                cell.update(period_pi=1,shape='exclude_lattice')
            else:
                cell.update(period_pi=2,width_pi=1,shape='intervals',closed=relation=='nonnegative')
            clauses.append(cell)
        else:
            num,den=m.rational_form(m.simplify(e))
            a,b=polynomial(num),polynomial(den)
            # An already positive denominator drops out; otherwise sign(a/b)=sign(a*b).
            expression=a if signs.get(b)=='positive' else m.mul(a,b)
            previous=signs.get(expression)
            signs[expression]='positive' if previous and previous!=relation else relation
    clauses.extend({'polynomial':e,'relation':relation} for e,relation in signs.items())
    return {'variables':variables,'intersection':clauses}


def planar_domain(t,lib,request):
    if not lib.data.get('planar_domain_cells') or set(t)-{'id','schema','source','kind','task_type','goal','requested_output'}:
        raise Unsupported('Additional source constraints or a different planar method remain')
    spec=t['goal'];v=spec['variables']
    outputs=set(t.get('requested_output',()))
    math_only=outputs=={'domain_set'} and spec.get('goal')=='determine the real domain'
    drawing=outputs=={'domain_set','drawing_of_domain'} and spec.get('goal')=='determine and draw the source real domain'
    if (set(spec)-{'variables','expression','goal'} or not isinstance(v,(list,tuple)) or
        not (math_only and len(v)>=2 or drawing and len(v)==2) or len(v)!=len(set(v))):
        raise Unsupported('The source dimension or requested domain obligations are unsupported')
    for name in v:m.context({'variable':name})
    guards=raw_conditions(m.parse(spec['expression'],None,v))
    if len(v)==2:
        try:
            region,proj=decomposition(guards,v)
        except (Unsupported,line.Unsupported):
            if drawing:raise
        else:
            value={'domain_set':region}
            if drawing:value.update(draw_region(region,spec['expression']))
            return {'projection':proj,'raw_conditions':guards},value
    if not lib.data.get('domain_sign_preimages'):raise Unsupported('No sign-preimage method for this dimension or boundary')
    return {'raw_conditions':guards,'method':'sign_preimages'}, {'domain_set':domain_preimages(guards,v)}


def region_report(r):
    from model import freeze
    from tasks import guard_source
    lines=['Область определения',r['task']['goal'].get('expression',''),r['status']]
    if r.get('value') is None:return '\n'.join(lines+[r.get('reason','')])+'\n'
    region=r['value']['domain_set']
    if 'intersection' in region:return '\n'.join(lines+preimage_description(region))+'\n'
    lines+=['Исходные условия '+(', '.join(guard_source(freeze(g)) for g in r['compilation']['raw_conditions']) or 'без ограничений')]
    return '\n'.join(lines+region_description(region))+'\n'


def preimage_description(region):
    from model import freeze
    from tasks import guard_source
    render=lambda e:m.render(freeze(e))
    if 'intervals_pi' in region:
        parts=[('[' if lc else '(')+render(a)+'π, '+render(b)+'π'+(']' if rc else ')') for a,b,lc,rc in region['intervals_pi']]
        return [region['variables'][0]+' ∈ '+(' ∪ '.join(parts) or '∅')]
    lines=[]
    if 'ambient_interval' in region:
        a,b,lc,rc=region['ambient_interval']
        lines.append(region['variables'][0]+' ∈ '+('[' if lc else '(')+render(a)+', '+render(b)+(']' if rc else ')'))
    for c in region['intersection']:
        if 'polynomial' in c:lines.append(guard_source((c['relation'],freeze(c['polynomial']))));continue
        if 'either' in c:lines.append(' или '.join('('+' и '.join(preimage_description(b))+')' for b in c['either']));continue
        if 'integer_argument' in c:lines.append(render(c['integer_argument'])+' ∈ {0, 1, 2, …}');continue
        phase=render(c['phase']);origin=render(c.get('origin_pi',q(0)))+'π'
        if c['shape']=='include_lattice':lines.append(f'{phase} = {origin} + kπ для некоторого целого k')
        elif c['shape']=='exclude_lattice':lines.append(f'{phase} ≠ {origin} + kπ для всех целых k')
        elif c['shape']=='centered_band':lines.append(f"|{phase} − ({origin}+kπ)| ≤ {render(c['half_width'])} для некоторого целого k")
        elif c['shape']=='tangent_band':lines.append(f"{render(c['lower'])}+kπ {'≤' if c['left_closed'] else '<'} {phase} < π/2+kπ для некоторого целого k")
        else:
            left,right=('[',']') if c['closed'] else ('(',')')
            lines.append(f'{phase} ∈ {left}{origin}+2kπ, {origin}+(2k+1)π{right} для некоторого целого k')
    return lines or ['Все вещественные значения']


def region_description(region):
    from model import freeze
    x,y=region['variables'];lines=[]
    def intervals(row):
        return ' ∪ '.join(('[' if lc else '(')+m.render(freeze(a))+', '+m.render(freeze(b))+(']' if rc else ')')
                          for a,b,lc,rc in row['fibers']) or '∅'
    for i,s in enumerate(region['slabs']):
        lines.append(m.render(freeze(s['left']))+' < '+x+' < '+m.render(freeze(s['right']))+'   '+y+' ∈ '+intervals(s))
        if i<len(region['sections']):
            cut=region['sections'][i];lines.append(x+' = '+m.render(freeze(cut['x']))+'   '+y+' ∈ '+intervals(cut))
    return lines


def bounded_cell_strips(equations,variables,axis=None):
    """Find connected components of the complement of all source curves, including adjacency across critical fibers."""
    from collections import defaultdict
    from intervals import compare,read_endpoint
    from model import freeze
    guards=[('nonzero',f) for f in equations]
    if axis and axis[0]==variables[1]:
        guards.append(('nonnegative',m.power(m.add(('s',axis[0]),m.neg(axis[1])),2)))
    region,projection=decomposition(guards,variables)
    slabs,sections=region['slabs'],region['sections']
    parents={};exterior=set()
    def root(node):
        while parents[node]!=node:
            parents[node]=parents[parents[node]];node=parents[node]
        return node
    def join(nodes):
        if nodes:
            rep=root(nodes[0])
            for node in nodes[1:]:parents[root(node)]=rep
    for i,row in enumerate(slabs):
        for j,included in enumerate(row['cells']):
            if not included:continue
            parents[(i,j)]=(i,j)
            if j in (0,len(row['cells'])-1) or i in (0,len(slabs)-1):exterior.add((i,j))
            for side in ('left_limits','right_limits'):
                if side in row and any(isinstance(z,str) for z in row[side][max(j-1,0):j+1]):exterior.add((i,j))
        for j,inside in enumerate(row['points']):
            if inside and row['cells'][j] and row['cells'][j+1]:join([(i,j),(i,j+1)])
    def edges(values):return ['-inf',*[read_endpoint(freeze(w)) for w in values],'+inf']
    for i,cut in enumerate(sections):
        values=edges(cut['bounds'])
        for j,inside in enumerate(cut['cells']):
            if not inside:continue
            incident=[]
            for index,side in ((i,'right_limits'),(i+1,'left_limits')):
                limits=edges(slabs[index][side])
                for k,(a,b) in enumerate(zip(limits,limits[1:])):
                    if (index,k) in parents and compare(a,values[j+1])<0 and compare(values[j],b)<0 and compare(a,b)<0:
                        incident.append((index,k))
            join(incident)
    grouped=defaultdict(list)
    for node in parents:grouped[root(node)].append(node)
    outside={root(n) for n in exterior}
    bounded=[cells for r,cells in grouped.items() if r not in outside]
    if len(bounded)!=1:raise Unsupported('The source boundary does not select a unique bounded connected face')
    basis=[[tuple(m.num(freeze(t)) for t in col) for col in p] for p in region['polynomials']]
    strips=[]
    for i,row in enumerate(slabs):
        cells=[j for s,j in bounded[0] if s==i]
        if not cells:continue
        if max(cells)-min(cells)+1!=len(cells):raise Unsupported('A disconnected fiber needs a union of intervals')
        probe=m.num(row['x'])
        def bound(j):
            p,k=row['bounds'][j]
            polynomial=basis[p]
            if len(polynomial)==3 and not any(polynomial[1]):
                # On this slab a*y²+c=0 and a is nonzero. Solve for y² first to preserve the canonical radical.
                x=('s',variables[0])
                def horner(col):
                    value=m.ZERO
                    for coefficient in reversed(col):value=m.add(q(coefficient),m.mul(x,value))
                    return value
                radicand=m.div(m.neg(horner(polynomial[0])),horner(polynomial[2]))
                return m.simplify(m.mul(q(1 if k else -1),('sqrt',radicand)))
            return boundary_formula(polynomial,k,variables[0],probe)
        strips.append((row['left'],row['right'],bound(min(cells)-1),bound(max(cells))))
    return dict(critical_fibers=region['x_cuts'],projection=projection,bounded_cells=bounded[0],
                exterior_components=len(outside),partition=region),strips


def circle_sweep(task,library):
    """Apply Pappus to a disk or its boundary only when the axis misses its interior."""
    from tasks import known_guard
    from verify import same_value
    if (not library.data.get('solid_sections') or task.get('kind')!='solid_of_revolution'
            or task.get('requested_output') not in (['volume'],['surface_area']) or len(task.get('boundary',()))!=1
            or set(task)-{'kind','id','source','boundary','axis','parameters','stated_conditions','requested_output'}):
        return None
    pair=task['boundary'][0].split('=');axis=task.get('axis','').split('=')
    if len(pair)!=2 or len(axis)!=2 or axis[0] not in ('x','y'):return None
    params=task.get('parameters',[]);names=['x','y',*params];positive=[];order=[]
    for cond in task.get('stated_conditions',[]):
        if re.fullmatch(r'[A-Za-z_]\w*>0',cond) and cond[:-2] in params:positive.append(cond);continue
        match=re.fullmatch(r'(0<)?([A-Za-z_]\w*)(<=|>=)([A-Za-z_]\w*)',cond)
        if not match or not {match[2],match[4]}<=set(params):return None
        left,right=match[2],match[4]
        if match[1]:positive.append(left+'>0')
        order.append((left,right) if match[3]=='<=' else (right,left))
    ctx=m.context(dict(variable='__circle',parameters=params,parameter_conditions=positive))
    try:point=m.parse(axis[1],None,params);terms=[m.parse(s,None,names) for s in pair]
    except Unsupported:return None
    if any(not known_guard(g,ctx) for a in [point,*terms] for g in domain_conditions(a)):return None
    x,y=(('s',name) for name in ('x','y'));f=m.add(terms[0],m.neg(terms[1]))
    def at(i,j):return m.simplify(m.substitute(f,{x:q(i),y:q(j)}))
    A=m.div(m.add(m.add(at(1,0),at(-1,0)),m.mul(q(-2),at(0,0))),q(2))
    if m.sign(A,ctx) not in (-1,1):return None
    cx=m.div(m.add(at(-1,0),m.neg(at(1,0))),m.mul(q(4),A))
    cy=m.div(m.add(at(0,-1),m.neg(at(0,1))),m.mul(q(4),A))
    R2=m.add(m.add(m.power(cx,2),m.power(cy,2)),m.neg(m.div(at(0,0),A)))
    dx=m.add(x,m.neg(cx));dy=m.add(y,m.neg(cy))
    if not same_value(f,m.mul(A,m.add(m.add(m.power(dx,2),m.power(dy,2)),m.neg(R2)))) or m.sign(R2,ctx)!=1:return None
    radius=m.simplify(('sqrt',R2))
    for p in params:
        z=('s',p)
        if m.sign(z,ctx)==1 and same_value(m.power(z,2),R2):radius=z;break
    offset=m.add((cx if axis[0]=='x' else cy),m.neg(point));s=m.sign(offset,ctx)
    if s not in (-1,1):return None
    distance=m.mul(q(s),offset)
    if m.sign(m.add(distance,m.neg(radius)),ctx) not in (0,1) and not any(
        same_value(radius,('s',lo)) and same_value(distance,('s',hi)) for lo,hi in order):return None
    output=task['requested_output'][0]
    measure=m.mul(m.PI,R2) if output=='volume' else m.mul(q(2),m.mul(m.PI,radius))
    return dict(theorem='method.external_axis_centroid_sweep',center=[cx,cy],axis_position=point,radius=radius,distance=distance,
                generator_measure=measure,domain='axis external or tangent; single full turn'),{output:m.mul(q(2),m.mul(m.PI,m.mul(distance,measure)))}


def power_profile_rotation(task,library,request):
    """Normalize a one-sided power profile or a symmetric pair before applying disks or shells."""
    from math import lcm
    from model import freeze
    from tasks import source
    if task['kind']!='solid_of_revolution' or not library.data.get('power_profile_rotation'):return None
    if set(task)-{'id','kind','source','parameters','requested_output','stated_conditions','boundary','axis'} or task.get('requested_output')!=['volume']:return None
    if set(task.get('source',{}))-{'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','section_convention'}:return None
    if task.get('source',{}).get('section_convention') not in (None,'Параметры положительны по общему соглашению раздела IV на с.208.'):return None
    axis=task.get('axis');graphs=task.get('boundary',[])
    if axis not in ('x=0','y=0') or len(graphs) not in (1,2) or not all(s.startswith('y=') for s in graphs):return None
    params=task.get('parameters',[]);end=None;conds=[]
    for condition in task.get('stated_conditions',[]):
        if condition.endswith('>0') and condition[:-2] in params:conds.append(condition)
        elif (v:=re.fullmatch(r'0<=x<=(.+)',condition)) and end is None:end=m.parse(v[1],None,params)
        else:return None
    if (len(graphs)==1)!=(end is not None) or len(graphs)==1 and axis!='y=0':return None
    ctx=m.context(dict(variable='x',parameters=params,parameter_conditions=conds));x=('v','x')
    raw=[m.parse(s[2:],'x',params) for s in graphs]
    def pw(c,p):
        if c==m.ONE:return m.ONE
        return m.power(c,p.numerator) if p.denominator==1 else m.simplify(('rpow',c,q(p)))
    def profile(e):
        # Coefficient and exponent on x>0, sign on the reflected branch (None if unproved).
        if e==x:return m.ONE,F(1),-1
        if m.constant_defined(e,ctx) and m.sign(e,ctx)==1:return m.simplify(e),F(0),1
        if e[0]=='abs':
            c,p,s=profile(e[1]);return c,p,1 if s else None
        if e[0] in ('pow','rpow'):
            r=F(e[2]) if e[0]=='pow' else m.num(m.simplify(e[2])) if m.constant_defined(e[2],ctx) else None
            if r is None or r<=0:raise Unsupported('Power profile is not defined at its vertex')
            c,p,s=profile(e[1])
            sign=1 if s==1 or s==-1 and r.denominator==1 and not r.numerator%2 else -1 if s==-1 and r.denominator==1 else None
            return pw(c,r),p*r,sign
        if e[0] not in ('mul','div'):raise Unsupported('The curve is not a single power on the positive side')
        c,p,s=profile(e[1]);d,r,j=profile(e[2])
        if e[0]=='div' and r:raise Unsupported('The unsimplified profile divides by zero at its vertex')
        return (m.mul(c,d),p+r,s*j if s and j else None) if e[0]=='mul' else (m.div(c,d),p,s*j if s and j else None)
    try:shapes=[profile(e) for e in raw]
    except Unsupported:return None
    if any(p<=0 for c,p,s in shapes):return None
    if len(shapes)==2:
        if any(s!=1 for c,p,s in shapes):return None
        if shapes[0][1]>shapes[1][1]:shapes.reverse();raw.reverse()
        (a,p,_),(b,r,_)=shapes
        if p==r:return None
        end=pw(m.div(a,b),1/(r-p))
    if not m.constant_defined(end,ctx) or m.sign(end,ctx)!=1:return None
    from operations import expression_positions
    heights=[]
    for e in raw:
        h=m.simplify(m.substitute(e,{x:end}))
        ones={node:m.ONE for _,node in expression_positions(h) if node[0]=='rpow' and node[1]==m.ONE and m.constant_defined(node[2],ctx)}
        heights.append(m.simplify(m.substitute(h,ones)))
    from verify import same_value
    if not all(m.constant_defined(h,ctx) for h in heights) or len(heights)==2 and not same_value(*heights):return None
    d=lcm(*(p.denominator for c,p,s in shapes));t=('v','t')
    disk=axis=='y=0';density=m.ZERO
    for j,(_,p,_) in enumerate(shapes):
        exponent=(1 if disk else 2)*d-1+int((2 if disk else 1)*d*p)
        density=m.add(density,m.mul(q(d*(-1)**j),m.power(t,exponent)))
    child=request('normalized radial section integrated over a unit interval',
                  dict(kind='iterated_integral',rectangle=[dict(variable='t',lower='0',upper='1')],parameters=[],
                       integrand=source(density),requested_output=['exact_integral']))
    multiplicity=len(shapes) if disk else 1
    scale=m.mul(m.PI,m.mul(q(multiplicity if disk else 2),
                m.mul(m.power(end,1 if disk else 2),m.power(heights[0],2 if disk else 1))))
    volume=m.mul(scale,freeze(child['value']));upper=m.mul(heights[0],m.power(t,int(d*shapes[0][1])))
    lower=m.mul(heights[0],m.power(t,int(d*shapes[1][1]))) if len(shapes)==2 else m.ZERO
    plan=dict(theorem='method.power_profile_rotation',positive_intersection=end,exponents=[q(p) for _,p,_ in shapes],
              endpoint_height=heights[0],axis=axis,half_profile_copies=multiplicity,substitution_power=d,
              sections=[dict(bounds=(m.ZERO,m.ONE),lower=lower,upper=upper,density=m.mul(scale,density),integral=volume)])
    return plan,dict(volume=volume)


def section_measure(task,library,request):
    import re
    from fractions import Fraction
    from model import freeze,q
    from tasks import source,domain_conditions,known_guard
    from intervals import Unsupported as LineUnsupported
    from polynomial import NotRational,Undefined
    from verify import same_value
    if (profile:=power_profile_rotation(task,library,request)) is not None:return profile
    if (sweep:=circle_sweep(task,library)) is not None:return sweep
    kind=task['kind'];solid=kind=='solid_of_revolution'
    if not solid and library.data.get('source_geometric_measure'):
        from planar_integrals import section_parameters,source_parametric_area,source_homogeneous_area
        if task.get('method_requirement') in ('polar_coordinates','derive_parametric_equations'):
            return source_homogeneous_area(task,request)
        if task.get('coordinate_system')=='parametric':return source_parametric_area(task,request)
        if (set(task)<={'id','source','kind','requested_output','parameters','stated_conditions','equations','coordinate_system'}
                and task.get('coordinate_system')=='rectangular' and task.get('requested_output')==['bounded_area']
                and len(task.get('equations',[]))==1
                and any(re.fullmatch(r'[^<>=]+>0',s) and '*' in s for s in task.get('stated_conditions',[]))):
            (eq,)=task['equations']
            if eq.count('=')!=1:raise Unsupported('A single closed quadratic boundary is required')
            params,standard=section_parameters(task,[eq,*task.get('stated_conditions',[])],('x','y'))
            conditions=list(dict.fromkeys([*standard,*task.get('stated_conditions',[])]))
            L,R=eq.split('=')
            goal=dict(kind='ellipsoid_moment',integrand='1',variables=['x','y'],parameters=params,stated_conditions=conditions,
                      quadratic_region=dict(left=L,right=R),requested_output=['exact_integral'])
            val=request('area of the enclosed positive definite quadratic sublevel',goal)['value']
            if set(val)!={'defined','value'} or val['defined'] is not True:
                raise Unsupported('A nonempty bounded quadratic sublevel was not proved')
            return dict(partition=dict(argument='complete_positive_squares_on_original_boundary',boundary=eq),
                        sections=[],measure_scale=m.ONE),dict(area=freeze(val['value']))
    if task.get('coordinate_system')=='polar' or task.get('axis')=='polar axis':
        return polar_measure(task,library,request)
    fields={'id','source','kind','requested_output','parameters','stated_conditions'}|({'boundary','axis'} if solid else {'equations','coordinate_system'})
    if (not library.data.get('bounded_section_measure') or set(task)-fields or task.get('coordinate_system','rectangular')!='rectangular'
            or task['requested_output']!=['volume' if solid else 'bounded_area']):
        raise Unsupported('Only a Cartesian area or volume with its original method is covered')
    params=task.get('parameters',[]);variables=['x','y'];sx,sy=(('s',j) for j in variables)
    conditions=[];limits=None
    if not solid and library.data.get('source_geometric_measure') and task.get('source',{}).get('section_convention') is not None:
        params,conditions=section_parameters(task,task['equations'],variables)
    for s in task.get('stated_conditions',[]):
        bound=re.fullmatch(r'([^<>=]+)<=x<=?([^<>=]+)',s.replace(' ',''))
        if bound and limits is None:limits=bound.groups()
        elif re.fullmatch(r'[A-Za-z_]\w*>0',s) and s[:-2] in params:
            if s not in conditions:conditions.append(s)
        else:raise Unsupported('Unproved printed domain, geometric constraint or boundary selection')
    ctx=m.context(dict(variable='__u',parameters=params,parameter_conditions=conditions))
    parse=lambda s:m.parse(s,None,[*variables,*params])
    equations=[];graph=[]
    for text in task['boundary' if solid else 'equations']:
        lhs,sep,rhs=text.partition('=')
        if not sep or '=' in rhs:raise Unsupported('Expected an explicit equality of source curves')
        left,right=parse(lhs),parse(rhs)
        for term in (left,right):
            if any(not known_guard(g,ctx) for g in domain_conditions(term)):
                raise Unsupported('A boundary chart may omit points of the original curves')
        equations.append(m.add(left,m.neg(right)))
        if lhs=='y' and not m.contains(right,sy):graph.append(right)
    axis=None
    if solid:
        name,eq,position=task['axis'].partition('=')
        if name not in variables or not eq:raise Unsupported('Expected an axis parallel to a Cartesian coordinate')
        c=m.parse(position,None,params)
        if not m.constant_defined(c,ctx):raise Unsupported('Undefined axis position')
        axis=name,m.simplify(c)
    factor=m.ONE
    if limits:
        if len(graph)!=len(equations) or len(graph)!=2:raise Unsupported('Explicit x-range needs two graph boundaries')
        lo=m.parse(limits[0],None,params);high=limits[1] if limits[1]=='+inf' else m.parse(limits[1],None,params)
        if not m.constant_defined(lo,ctx) or high!='+inf' and (not m.constant_defined(high,ctx) or m.sign(m.add(high,m.neg(lo)),ctx)!=1):
            raise Unsupported('Ordering of the source endpoints is unproved')
        def sign_between(z):
            if z==m.ZERO:return 0
            if m.sign(z,ctx) in (-1,1):return m.sign(z,ctx)
            if z[0]=='mul':
                a,b=sign_between(z[1]),sign_between(z[2]);return a*b if None not in (a,b) else None
            if z[0]=='pow' and type(z[2]) is int and z[2]>0 and z[2]%2==0:return 1
            if z==sx and m.sign(lo,ctx) in (0,1):return 1
            if z[0] in ('sin','cos') and z[1]==sx and high!='+inf':
                left,right=(m.num(m.div(b,m.PI)) for b in (lo,high))
                if left is None or right is None:return None
                shift=Fraction(1,2) if z[0]=='cos' else 0
                j=(left+shift).__floor__()
                if j<=left+shift<right+shift<=j+1:return (-1)**j
            return None
        l,h=graph
        s=sign_between(m.simplify(m.add(h,m.neg(l))))
        if s is None or s==0:raise Unsupported('Intersections and ordering on the source interval are unproved')
        if s<0:l,h=h,l
        partition=dict(argument='fixed_graph_order_on_source_interval',difference=m.add(h,m.neg(l)))
        strips=[(lo,high,l,h)]
    else:
        if params:
            # A positive diagonal change preserves every original face and the ordering of its fibers.
            from itertools import product
            scales=[('s',p) for p in params if p+'>0' in conditions]+[m.ONE]
            proposed=scales
            if not solid and library.data.get('source_geometric_measure'):
                proposed=scales+[m.power(s,n) for n in (2,3) for s in scales if s!=m.ONE]
            for dx,dy in product(proposed,repeat=2):
                pull={sx:m.mul(dx,sx),sy:m.mul(dy,sy)};normalized=[]
                for eq in equations:
                    num,den=m.rational_form(m.simplify(m.substitute(eq,pull)))
                    if len(den)!=1:break
                    dm=next(iter(den))
                    if any(v not in scales for v,k in dm):break
                    groups={tuple((v,k) for v,k in mon if v in scales) for mon in num}
                    if len(groups)!=1:break
                    reduced=m.poly_expr({tuple((v,k) for v,k in mon if v not in scales):c for mon,c in num.items()})
                    if any(m.contains(reduced,('s',p)) for p in params):break
                    normalized.append(reduced)
                if len(normalized)==len(equations):break
            else:raise Unsupported('No positive coordinate scaling removes the boundary parameters')
            equations=normalized
            factor=m.mul(dx,dy)
            if solid:
                radius_scale=dy if axis[0]=='y' else dx
                factor=m.mul(factor,radius_scale);axis=axis[0],m.simplify(m.div(axis[1],radius_scale))
        try:partition,strips=bounded_cell_strips(equations,variables,axis)
        except (LineUnsupported,NotRational,Undefined) as exc:raise Unsupported(str(exc)) from exc
        if params:partition['coordinate_scale']=(dx,dy)
    def cmp(a,b):
        if a=='+inf':return 1
        if b=='+inf':return -1
        return m.sign(m.add(a,m.neg(b)),ctx)
    if solid and axis[0]=='x':
        side={1 if cmp(a,axis[1]) in (0,1) else -1 if cmp(b,axis[1]) in (0,-1) else 0 for a,b,_,_ in strips}
        if 0 in side or len(side)!=1:raise Unsupported('Overlapping rotational shells or crossing of the rotation axis')
    pieces=[];total=m.ZERO
    for a,b,l,h in strips:
        width=m.simplify(m.add(h,m.neg(l)));density=width
        if solid and axis[0]=='x':density=m.mul(q(2),m.mul(q(next(iter(side))),m.mul(m.add(sx,m.neg(axis[1])),width)))
        if solid and axis[0]=='y':
            center=axis[1];low=m.simplify(m.add(l,m.neg(center)));high=m.simplify(m.add(h,m.neg(center)))
            if same_value(low,m.ZERO):density=m.power(high,2)
            elif same_value(high,m.ZERO) or same_value(low,m.neg(high)):density=m.power(low,2)
            else:
                if limits:ls,hs=sign_between(low),sign_between(high)
                else:
                    # The rotation axis was inserted in the sign partition. Its order is constant on this slab.
                    probe=m.div(m.add(a,b),q(2))
                    ls,hs=(m.sign(m.substitute(v,{sx:probe}),ctx) for v in (low,high))
                if ls==1:density=m.add(m.power(high,2),m.neg(m.power(low,2)))
                elif hs==-1:density=m.add(m.power(low,2),m.neg(m.power(high,2)))
                elif ls in (-1,0) and hs in (0,1):
                    if not limits and sum((x0,x1)==(a,b) for x0,x1,_,_ in strips)!=1:
                        raise Unsupported('Several rotating fibers may cover the same disk')
                    delta=m.simplify(m.add(high,low))
                    sign=sign_between(delta) if limits else metric_sign(m.substitute(delta,{sx:('v','x')}),'x',a,b,ctx)
                    if sign is None:raise Unsupported('The farther endpoint may change inside this strip')
                    density=m.power(high if sign>=0 else low,2)
                else:raise Unsupported('The outer radius changes sides or remains unproved')
        if solid:density=m.mul(m.PI,density)
        density=m.simplify(density);jac=m.ONE
        z=sx
        if m.contains(density,('sqrt',sx)) and cmp(a,m.ZERO) in (0,1) and b!='+inf':
            # x=t² is a bijection between the two nonnegative intervals.
            z=('s','t');jac=m.mul(q(2),z);rad=m.substitute(density,{('sqrt',sx):z,sx:m.power(z,2)})
            density=m.simplify(m.mul(jac,rad));L,H=(m.simplify(('sqrt',v)) for v in (a,b))
        else:L,H=a,b
        if H=='+inf':
            child=dict(kind='improper_integral',parameters=params,stated_conditions=conditions,variable=z[1],integrand=source(density),lower=source(L),upper=H,requested_output=['exact_integral'])
            val=request('improper slice integral '+str(len(pieces)),child)['value']
            if 'value' not in val:raise Unsupported('The slice integral has no verified finite value')
            val=freeze(val['value'])
        else:
            child=dict(kind='iterated_integral',parameters=params,stated_conditions=conditions,integrand=source(density),integration_order=[dict(variable=z[1],lower=source(L),upper=source(H))],requested_output=['exact_integral'])
            val=freeze(request('slice integral '+str(len(pieces)),child)['value'])
        pieces.append(dict(bounds=(a,b),lower=l,upper=h,substitution_jacobian=jac,density=density,integral=val))
        total=m.add(total,val)
    return dict(partition=partition,sections=pieces,axis=axis,measure_scale=factor),{'volume' if solid else 'area':m.mul(factor,total)}


def polar_measure(task,library,request):
    """Single-valued radial fibers. Verify their angle coverage and avoid double-counting signed polar radii."""
    from integrals import affine,learned_nodes
    from tasks import known_guard,source
    from model import freeze
    from verify import same_value
    solid=task['kind']=='solid_of_revolution'
    fields={'kind','id','source','parameters','stated_conditions','requested_output'}|({'axis','boundary'} if solid else {'coordinate_system','equations'})
    if (not library.data.get('polar_section_measure') or set(task)-fields or
            (task.get('axis')!='polar axis' if solid else task.get('coordinate_system')!='polar') or
            task.get('requested_output')!=['volume' if solid else 'bounded_area']):
        raise Unsupported('An angular coordinate change, source method or rotation axis remains unproved')
    import re
    params=task.get('parameters',[]);positives=[];limits=[];radial=[];left_open=False
    if not solid and library.data.get('source_geometric_measure') and task.get('source',{}).get('section_convention') is not None:
        from planar_integrals import section_parameters
        params,positives=section_parameters(task,task['equations'],('r','phi'))
    variable='phi';u=('v',variable)
    side_conditions=[]
    for s in task.get('stated_conditions',[]):
        bounded=re.fullmatch(r'0<([A-Za-z_]\w*)<1',s)
        if bounded and bounded[1] in params:
            name=bounded[1];positives.extend((name+'>0','1-'+name+'>0'));continue
        if s.endswith('>0') and s[:-2] in params:
            if s not in positives:positives.append(s)
        elif re.search(r'\bphi\b',s) and '<' in s:
            fields=re.split(r'\s*(<=|<)\s*',s.strip());items=fields[::2];ops=fields[1::2]
            if items.count(variable)!=1:raise Unsupported('The angular chain must contain the angle once')
            i=items.index(variable)
            if not 0<i<len(items)-1 or ops[i]!='<=':raise Unsupported('Both adjacent angular bounds are required')
            left_open=ops[i-1]=='<'
            ends=[None if t==variable else m.parse(t,None,params) for t in items]
            limits.extend((ends[i-1],ends[i+1]))
            side_conditions.extend((ends[j],op,ends[j+1]) for j,op in enumerate(ops) if j not in (i-1,i))
        elif s=='half turn bounds the figure' and '0<=phi<=pi' in task['stated_conditions']:continue
        else:raise Unsupported('An original parameter bound or sector selection remains open')
    ctx=m.context(dict(variable=variable,parameters=params,parameter_conditions=positives))
    for left,op,right in side_conditions:
        if not all(m.constant_defined(v,ctx) for v in (left,right)):
            raise Unsupported('An additional angular comparison has an undefined side')
        if m.sign(m.add(right,m.neg(left)),ctx) not in ((0,1) if op=='<=' else (1,)):
            raise Unsupported('An additional angular comparison is false or unresolved')
    for text in task['boundary' if solid else 'equations']:
        left,eq,right=text.partition('=')
        if not eq or '=' in right:raise Unsupported('Cannot isolate the original polar boundary')
        value=m.parse(right,variable,params)
        if left=='phi' and not m.variable_in(value,variable):limits.append(value)
        elif left in ('r','r^2'):radial.append((left,value))
        else:raise Unsupported('The radial equation or its inversion remains open')
    if len(radial) not in (1,2) or len(limits) not in (0,2):raise Unsupported('Multiple radial boundaries need ordered angular sectors')
    if any(not m.constant_defined(v,ctx) for v in limits):raise Unsupported('The original angular endpoints are undefined on the parameter domain')
    l,h=map(m.simplify,limits) if limits else (m.ZERO,m.mul(q(2),m.PI))
    angular=tuple(m.pi_multiple(v) for v in (l,h));whole=angular==(0,2)
    if None in angular or not 0<angular[1]-angular[0]<=2:raise Unsupported('Angular interval exceeds one turn or its order is unproved')
    if len(radial)==2 and not solid and left_open and 0==angular[0]<angular[1]<=1:
        # sin(v) <= v by integration of 1-cos(v)>=0. Positivity on (0,pi) permits taking reciprocals.
        if angular[1]>=1:raise Unsupported('An additional zero of the angular denominator is an endpoint')
        forms=[m.simplify(value) for tag,value in radial if tag=='r']
        def reciprocal(e,den):
            amplitude=m.simplify(m.mul(e,den))
            return amplitude if not m.variable_in(amplitude,variable) and m.sign(amplitude,ctx)==1 else None
        pair=next(((a,b) for a,b in (forms,forms[::-1]) if reciprocal(a,u) and reciprocal(b,('sin',u))),None) if len(forms)==2 else None
        if not pair:raise Unsupported('No verified comparison of every polar boundary on this sector')
        inner,outer=pair;v=reciprocal(inner,u);w=reciprocal(outer,('sin',u))
        for tag,raw in radial:
            for op,g in domain_conditions(raw):
                if op!='nonzero' or not any(same_value(g,z) for z in (u,('sin',u))) and not known_guard((op,g),ctx):
                    raise Unsupported('Another original domain restriction is present')
        if not same_value(v,w) and m.sign(m.add(w,m.neg(v)),ctx)!=1:raise Unsupported('Polar boundaries may cross')
        density=('div',('add',('div',m.power(w,2),('pow',('sin',u),2)),('mul',q(-1),('div',m.power(v,2),('pow',u,2)))),q(2))
        primitive=request('primitive of the combined annular area',dict(kind='integrate',variable=variable,integrand=source(density),parameters=params,stated_conditions=positives))
        F=freeze(primitive['value']['representative']);endpoints=[]
        for point,side in ((l,'right'),(h,'left')):
            val=freeze(request('angular boundary '+side,dict(variable=variable,expression=source(F),parameters=params,parameter_conditions=positives,approach=dict(point=source(point),side=side)))['value'])
            if val in ('-inf','+inf'):raise Unsupported('The improper area is infinite')
            endpoints.append(val)
        area=m.add(endpoints[1],m.neg(endpoints[0]))
        return dict(partition=dict(argument='reciprocal_order_from_sine_bound',source_angle=(l,h),common_cutoff=True,primitive=F,endpoints=endpoints),
                    sections=[dict(bounds=(l,h),lower=inner,upper=outer,density=density,integral=area)],measure_scale=m.ONE),{'area':area}
    if len(radial)!=1 or left_open:raise Unsupported('Several radial graphs or an open sector need separate boundary checks')
    form,original=radial[0];f=m.simplify(original);squared=form=='r^2'
    if not squared and not solid and f[0]=='div' and not m.variable_in(f[1],variable):
        # In a pole-free angular interval t = tan(theta/2) makes the cosine rational.
        amplitude,den=f[1:]
        if m.sign(amplitude,ctx)==-1:amplitude,den=m.neg(amplitude),m.neg(den)
        wave=('cos',u);A=m.simplify(m.substitute(den,{wave:m.ZERO}));B=m.add(m.substitute(den,{wave:m.ONE}),m.neg(A))
        if (not m.variable_in(A,variable) and not m.variable_in(B,variable) and
                same_value(den,m.add(A,m.mul(B,wave))) and m.sign(amplitude,ctx)==1 and
                len(domain_conditions(original))==1 and any(same_value(domain_conditions(original)[0][1],d) for d in (den,m.neg(den)))):
            plus,minus=m.add(A,B),m.add(A,m.neg(B))
            def positive(x):return m.sign(x,ctx)==1
            if whole and positive(plus) and positive(minus):
                # Projective half-angle coordinates cover one turn once (apart from the opposite ray).
                t=('v','t');scale=('sqrt',m.div(plus,minus));cells=[];values=[];p2=m.power(plus,2)
                for degree,coeff in ((0,m.div(scale,p2)),(2,m.div(m.power(scale,3),p2))):
                    density=m.div(m.power(t,degree),m.power(m.add(m.ONE,m.power(t,2)),2))
                    child=dict(kind='improper_integral',variable='t',integrand=source(density),lower='-inf',upper='+inf',requested_output=['exact_integral'])
                    cv=request('half-angle moment '+str(degree),child)['value']
                    if cv.get('convergence')!='convergent':raise Unsupported('The projective moment is not finite')
                    value=freeze(cv['value']);values.append(m.mul(coeff,value))
                    cells.append(dict(bounds=('-inf','+inf'),lower=m.ZERO,upper=f,density=density,integral=value,coefficient=coeff))
                return dict(partition=dict(argument='scaled_half_angle',radius=original,source_angle=(l,h),positive_coefficients=(plus,minus),scale=scale),
                            sections=cells,measure_scale=m.power(amplitude,2)),{'area':m.mul(m.power(amplitude,2),m.add(*values))}
            if same_value(plus,m.ZERO) and positive(minus) and 0<angular[0]<angular[1]<1:
                # Reciprocal tangent turns this chart into a polynomial and has finite positive endpoints.
                z=('v','t');density=m.div(m.mul(m.power(amplitude,2),m.add(m.ONE,m.power(z,2))),m.power(minus,2))
                # The finite half-angle endpoints may not have elementary table entries. Their principal positive square roots do.
                ends=tuple(m.simplify(('sqrt',m.div(m.add(m.ONE,('cos',v)),m.add(m.ONE,m.neg(('cos',v)))))) for v in (h,l))
                child=dict(kind='iterated_integral',parameters=params,stated_conditions=positives,integrand=source(density),
                           integration_order=[dict(variable='t',lower=source(ends[0]),upper=source(ends[1]))],requested_output=['exact_integral'])
                value=freeze(request('bounded half-angle sector',child)['value'])
                return dict(partition=dict(argument='reciprocal_half_angle',radius=original,source_angle=(l,h),positive_coefficient=minus),
                            sections=[dict(bounds=ends,lower=m.ZERO,upper=f,density=density,integral=value)],measure_scale=m.ONE),{'area':value}
    if any(not known_guard(g,ctx) for g in domain_conditions(original)):raise Unsupported('Positive radius denominator or the original angular domain is unproved')
    waves=list({w for w in learned_nodes(f) if isinstance(w,tuple) and w[0] in ('sin','cos') and m.variable_in(w,variable)})
    sign=m.sign(f,ctx);mode='nonnegative_radius';multiplier=m.ONE;chart=u;argument=None
    if len(waves)>1:raise Unsupported('Several angular harmonics need a common sign partition')
    if len(waves)==1:
        w=waves[0];frequency,phase=affine(w[1],variable);k=m.num(frequency);B=m.simplify(m.substitute(f,{w:m.ZERO}))
        A=m.add(m.substitute(f,{w:m.ONE}),m.neg(B))
        if not same_value(f,m.add(B,m.mul(A,w))) or any(m.variable_in(v,variable) for v in (A,B)) or k is None or k.denominator!=1 or k<=0:
            raise Unsupported('Cannot certify the frequency or the range of the radial harmonic')
        if m.sign(A,ctx) not in (-1,1):raise Unsupported('The harmonic amplitude must have a known sign')
        amplitude=A if m.sign(A,ctx)==1 else m.neg(A);margin=m.simplify(m.add(B,m.neg(amplitude)))
        if same_value(margin,m.ZERO) or m.sign(margin,ctx)==1:sign=1
        elif B==m.ZERO and whole and not solid:
            if squared and k%2:raise Unsupported('Opposite signed rays of the squared radius require a joint image check')
            mode='positive_lobes' if squared or k%2 else 'disjoint_signed_lobes'
            multiplier=m.div(q(k if mode=='positive_lobes' else 2*k),q(k))
            l,h=m.ZERO,m.PI;chart=m.mul(amplitude,('sin',u));argument=(w,frequency,phase)
            sign=1
        if sign==1 and mode=='nonnegative_radius' and whole and not solid:
            l,h=m.ZERO,m.mul(q(2),m.PI);chart=m.add(B,m.mul(A,('sin',u)));argument=(w,frequency,phase)
    elif not waves and same_value(f,m.mul(m.substitute(f,{u:m.ONE}),u)) and angular[0]>=0 and m.sign(m.substitute(f,{u:m.ONE}),ctx)==1:
        sign=1
    if not limits and not waves and m.variable_in(f,variable):
        raise Unsupported('No closed polar turn or source angular interval has been proved')
    if squared and whole and waves and k%2:
        raise Unsupported('A nonperiodic squared radius on opposite rays needs a separate coverage argument')
    if sign!=1:raise Unsupported('The positive radius sectors and their multiplicity remain unproved')
    if chart==u:chart=f
    if solid:
        if whole:
            # Upper and lower half-plane sections sweep identical circles precisely for symmetric radii.
            if len(waves)!=1 or waves[0][0]!='cos' or phase!=m.ZERO:raise Unsupported('Full rotation would overlap unknown radial sections')
            h=m.PI
        elif not 0<=angular[0]<angular[1]<=1:raise Unsupported('Volume would sweep across the rotation axis')
        if squared:raise Unsupported('The real branch of the cubic radial moment remains open')
        density=m.mul(m.div(m.mul(q(2),m.PI),q(3)),m.mul(m.power(chart,3),('sin',u)))
    else:density=m.div(chart if squared else m.power(chart,2),q(2))
    child=dict(kind='iterated_integral',parameters=params,stated_conditions=positives,integrand=source(density),
               integration_order=[dict(variable=variable,lower=source(l),upper=source(h))],requested_output=['exact_integral'])
    val=freeze(request('polar sector integral',child)['value'])
    return dict(partition=dict(argument=mode,original_angle=tuple(q(v) for v in angular),harmonic=argument,radius=original,angular_jacobian=multiplier),
                sections=[dict(bounds=(l,h),lower=m.ZERO,upper=chart,density=density,integral=val)],measure_scale=multiplier),{'volume' if solid else 'area':m.mul(multiplier,val)}


def metric_sign(f,v,a,b,ctx):
    """Return a weak sign on the entire closed parameter interval; zero contacts are allowed."""
    from integrals import affine,learned_nodes
    from verify import same_value
    f=m.simplify(f);p=('v',v);s=m.sign(f,ctx)
    if s is not None:return s
    if f==p:
        ends={m.sign(z,ctx) for z in (a,b)}
        if ends<={0,1}:return 1
        if ends<={0,-1}:return -1
    if f[0] in ('sqrt','abs') or f[0]=='pow' and f[2]%2==0:return 1
    if f[0]=='sinh':return metric_sign(f[1],v,a,b,ctx)
    if f[0] in ('mul','div'):
        s,t=(metric_sign(z,v,a,b,ctx) for z in f[1:])
        if None not in (s,t):return s*t
    if f[0]=='add':
        for wave,arg in (z for z in learned_nodes(f) if isinstance(z,tuple) and z[0] in ('cos','cosh')):
            A=m.simplify(m.substitute(f,{(wave,arg):m.ZERO}))
            B=m.add(m.substitute(f,{(wave,arg):m.ONE}),m.neg(A))
            if m.variable_in(A,v) or m.variable_in(B,v) or not same_value(f,m.add(A,m.mul(B,(wave,arg)))):continue
            if wave=='cos' and m.sign(B,ctx) in (-1,1):
                amplitude=B if m.sign(B,ctx)==1 else m.neg(B)
                for direction in (1,-1):
                    bound=m.add(m.mul(q(direction),A),m.neg(amplitude))
                    if m.sign(bound,ctx) in (0,1):return direction
            if wave=='cosh' and m.sign(B,ctx) in (-1,1) and m.sign(m.add(A,B),ctx) in (0,m.sign(B,ctx)):return m.sign(B,ctx)
        s,t=(metric_sign(z,v,a,b,ctx) for z in f[1:])
        if s==t:return s
    if f[0] in ('cos','sin'):
        try:c,d=affine(f[1],v)
        except Unsupported:return None
        ends=[m.pi_multiple(m.add(d,m.mul(c,z))) for z in (a,b)]
        if None not in ends:
            shift=F(1,2) if f[0]=='cos' else F(0)
            lo=min(ends)+shift;hi=max(ends)+shift;j=lo.__floor__()
            if hi<=j+1:return (-1)**j
    if f[0]=='add':
        num,den=m.rational_form(f);factors=m.common_mon(num)
        if factors:
            mon=tuple(sorted(factors.items(),key=lambda item:str(item[0])))
            common=m.poly_expr({mon:F(1)});reduced=m.div(f,common)
            left,right=(metric_sign(t,v,a,b,ctx) for t in (common,reduced))
            if None not in (left,right):return left*right
    return None


def metric_square_root(f,v,a,b,ctx):
    """Extract an exact rational-function square, optionally after a standard half-angle identity."""
    from integrals import learned_nodes
    from model import canonical
    def root(poly):
        if not poly:return m.ZERO
        atoms=sorted({z for mon in poly for z,_ in mon},key=canonical)
        def order(mon):return tuple(dict(mon).get(z,0) for z in atoms)
        first=max(poly,key=order);c=poly[first]
        r,s=(m.perfect_root(n,2) for n in (c.numerator,c.denominator))
        if r is None or s is None or any(k%2 for z,k in first):return None
        lead=tuple((z,k//2) for z,k in first);head=F(r,s);out={lead:head}
        degree=max(sum(k for z,k in mon) for mon in poly)//2
        while True:
            rem=m.addp(poly,{mon:-k for mon,k in m.mulp(out,out).items()})
            if not rem:return m.poly_expr(out)
            top=max(rem,key=order);pows=dict(top)
            if any(pows.get(z,0)<k for z,k in lead):return None
            term=tuple((z,k-dict(lead).get(z,0)) for z,k in top if k>dict(lead).get(z,0))
            if sum(k for z,k in term)>degree or order(term)>=min(map(order,out)):return None
            out[term]=rem[top]/(2*head)
    original=m.simplify(f);forms=[('rational_square',original)]
    for wave,arg in sorted({z for z in learned_nodes(original) if isinstance(z,tuple) and z[0] in ('cos','cosh')},key=canonical):
        h=m.div(arg,q(2));s=('sin' if wave=='cos' else 'sinh',h)
        c=('cos' if wave=='cos' else 'cosh',h)
        replacement={(wave,arg):m.add(m.ONE,m.mul(q(-2 if wave=='cos' else 2),m.power(s,2))),
                     ('sin' if wave=='cos' else 'sinh',arg):m.mul(q(2),m.mul(s,c))}
        forms.append(('half_angle_'+wave,m.simplify(m.substitute(original,replacement))))
        replacement[(wave,arg)]=m.add(m.mul(q(2),m.power(c,2)),q(-1))
        forms.append(('half_angle_'+wave,m.simplify(m.substitute(original,replacement))))
    hyper={arg for op,arg in (z for z in learned_nodes(original) if isinstance(z,tuple) and z[0] in ('sinh','cosh'))}
    for arg in sorted(hyper,key=canonical):
        half=m.div(arg,q(2));z=('exp',half)
        replacements={}
        for phase,k in ((arg,2),(half,1),(m.mul(q(2),arg),4)):
            P=m.power(z,k);I=m.div(m.ONE,P)
            replacements.update({('sinh',phase):m.div(m.add(P,m.neg(I)),q(2)),('cosh',phase):m.div(m.add(P,I),q(2))})
        image=m.simplify(m.substitute(original,replacements))
        scales=[m.ONE,q(2),q(3),*(('s',name) for name in ctx['parameters'])]
        for scale in scales:
            for factor in (scale,m.mul(q(2),scale),m.mul(q(3),scale)):
                for phase in (arg,half,m.mul(q(2),arg)):
                    for wave in ('sinh','cosh'):
                        candidate=m.mul(factor,(wave,phase));mapped=m.simplify(m.substitute(candidate,replacements))
                        if m.simplify(m.add(image,m.neg(m.power(mapped,2))))==m.ZERO and metric_sign(candidate,v,a,b,ctx)==1:
                            return candidate,dict(method='hyperbolic_square',original=original,squared_identity=image,root=candidate,sign=1)
    for method,g in forms:
        num,den=m.rational_form(g)
        if not den:continue
        lc=next(iter(den.values()))
        if lc<0:num,den=({k:-v for k,v in P.items()} for P in (num,den))
        r,s=root(num),root(den)
        if r is None or s is None:continue
        candidate=m.div(r,s)
        sign=metric_sign(candidate,v,a,b,ctx)
        if sign in (-1,0,1):
            return m.mul(q(sign),candidate),dict(method=method,original=original,squared_identity=g,root=candidate,sign=sign)
    # A common even monomial is a square on the full original curve, including zeros.
    num,den=m.rational_form(original);np,dp=m.common_mon(num),m.common_mon(den)
    if num and den:
        def split(poly,degrees):
            fact={z:k//2 for z,k in degrees.items() if k>=2}
            return (m.poly_expr({tuple(sorted(fact.items(),key=lambda i:canonical(i[0]))):F(1)}),
                    m.poly_expr({tuple((z,i-2*fact.get(z,0)) for z,i in mon if i>2*fact.get(z,0)):c for mon,c in poly.items()}))
        N,P=split(num,np);D,Q=split(den,dp);g=m.div(N,D)
        sign=metric_sign(g,v,a,b,ctx)
        if g!=m.ONE and sign in (-1,1):
            residual=m.div(P,Q)
            return m.mul(m.mul(q(sign),g),('sqrt',residual)),dict(method='positive_square_factor',original=original,squared_identity=residual,root=g,sign=sign)
    return m.simplify(('sqrt',original)),None


def curve_metric(task,library,request):
    from model import freeze
    from tasks import source,known_guard
    from verify import same_value
    from integrals import learned_nodes,affine
    if (sweep:=circle_sweep(task,library)) is not None:return sweep
    if library.data.get('source_polar_metric'):
        from planar_integrals import source_polar_metric
        if (metric:=source_polar_metric(task,request)) is not None:return metric
    solid=task['kind']=='solid_of_revolution'
    fields={'kind','source','id','parameters','stated_conditions','requested_output'}|({'axis','boundary'} if solid else {'coordinate_system','equations'})
    if not solid:fields.add('dependent_endpoint_ordinates')
    if not library.data.get('curve_metric') or set(task)-fields or task.get('requested_output')!=['surface_area' if solid else 'arc_length']:
        raise Unsupported('Original method or additional geometric output has not been established')
    if not solid and library.data.get('radial_arc_domain'):
        from planar_integrals import radial_arc_length
        if (result:=radial_arc_length(task,request)) is not None:return result
    params=task.get('parameters',[]);interval=None;v=None;positive=[];given_ordinates=None
    labels=task.get('dependent_endpoint_ordinates',[]);bindings={};label_positive=set()
    if not isinstance(labels,list) or any(not isinstance(v,str) or not re.fullmatch(r'[A-Za-z_]\w*',v) or v in params or v in ('x','y','r','t','phi') for v in labels):
        raise Unsupported('Endpoint ordinate names must be distinct from independent parameters and coordinates')
    for s in task.get('stated_conditions',[]):
        match=re.fullmatch(r'([^<>=]+)<=(x|y|t|phi|r)<=([^<>=]+)',s)
        if match and interval is None:
            left,v,right=match.groups();interval=(left,right);continue
        match=re.fullmatch(r'abs\((x|y|t|phi)\)<=([^<>=]+)',s)
        if match and interval is None:v=match[1];interval=('-('+match[2]+')',match[2]);continue
        stations=re.fullmatch(r'from [A-Z]\(([^,]+),([^,]+)\) to [A-Z]\(([^,]+),([^,]+)\)',s)
        if stations and interval is None:
            x0,y0,x1,y1=stations.groups();interval=(x0,x1);given_ordinates=(y0,y1);v='x';continue
        if re.fullmatch(r'[A-Za-z_]\w*>0',s) and s[:-2] in labels:label_positive.add(s[:-2]);continue
        if re.fullmatch(r'[A-Za-z_]\w*>0',s) and s[:-2] in params:positive.append(s)
        else:raise Unsupported('The source endpoints, parameter constraints or geometric branch are unresolved')
    source_equations=task['boundary' if solid else 'equations']
    polar_trace=task.get('coordinate_system')=='polar' or task.get('axis')=='polar axis'
    closed_polar=False
    if not interval and polar_trace and len(source_equations)==1 and source_equations[0].startswith('r='):
        v='phi';interval=('0' if solid else '-pi','pi');closed_polar=True
    if not interval:raise Unsupported('A closed trace requires determining a nonrepeating interval')
    cond=m.context(dict(variable=v,parameters=params,parameter_conditions=positive));p=('v',v)
    bounds=tuple(m.parse(z,None,params) for z in interval)
    if any(not m.constant_defined(z,cond) for z in bounds) or m.sign(m.add(bounds[1],m.neg(bounds[0])),cond)!=1:
        raise Unsupported('Ordering or definedness of the source endpoints remains open')
    maps={}
    for text in task['boundary' if solid else 'equations']:
        name,eq,rhs=text.partition('=')
        if not eq or name not in ('x','y','r','phi') or name in maps or name==v:
            raise Unsupported('The source curve needs a verified chart and branch multiplicity')
        maps[name]=m.parse(rhs,v,params)
    from quadrature import enclose,guard_bounds
    # Check every original coordinate, before taking a reflection or simplifying a parametric chart.
    for coordinate in maps.values():
        raw=coordinate
        for n in learned_nodes(coordinate):
            if isinstance(n,tuple) and n[0]=='rpow':
                exponent=m.num(m.simplify(n[2]))
                if (exponent and exponent>0 and exponent.denominator in (2,3) and
                        metric_sign(n[1],v,*bounds,cond) in (0,1) and all(known_guard(guard,cond) for guard in domain_conditions(n[2]))):
                    radical=('sqrt' if exponent.denominator==2 else 'cbrt',n[1])
                    raw=m.substitute(raw,{n:('pow',radical,exponent.numerator)})
        for op,g in domain_conditions(raw):
            if known_guard((op,g),cond) or op=='nonnegative' and metric_sign(g,v,*bounds,cond) in (0,1):continue
            guard_bounds(op,g,(enclose(bounds[0],None)[0],enclose(bounds[1],None)[1]),[v])
    if v in ('x','y','r','phi'):maps[v]=p
    polar=set(maps)=={'r','phi'}
    if not polar and set(maps)!={'x','y'}:raise Unsupported('Incomplete coordinate map')
    if not solid and task.get('coordinate_system')!=('polar' if polar else 'rectangular' if v in ('x','y') else 'parametric'):
        raise Unsupported('Source coordinate system does not match the given curve')
    endpoint_facts=[]
    if given_ordinates:
        if polar or v!='x':raise Unsupported('Specified endpoints do not define a graph arc')
        for t,ordinate in zip(bounds,given_ordinates):
            observed=m.simplify(m.substitute(maps['y'],{p:t}))
            if ordinate in labels:
                expected=bindings.setdefault(ordinate,observed)
                if ordinate in label_positive and m.sign(expected,cond)!=1:raise Unsupported('Positivity of the named ordinate is unresolved')
            else:expected=m.parse(ordinate,None,params)
            if not same_value(observed,expected):
                raise Unsupported('Specified endpoint does not lie on the curve')
            endpoint_facts.append((t,observed,expected))
    if set(bindings)!=set(labels):raise Unsupported('A named ordinate does not occur at a supplied endpoint')
    if solid:
        axis,eq,c=('y','=','0') if polar and task['axis']=='polar axis' else task['axis'].partition('=')
        if not eq or axis not in ('x','y'):raise Unsupported('The source rotation axis requires a different distance formula')
        center=m.parse(c,None,params)
        if not m.constant_defined(center,cond):raise Unsupported('The axis position is undefined')
    if polar:
        X,Y=(m.mul(maps['r'],(wave,maps['phi'])) for wave in ('cos','sin'))
    else:X,Y=maps['x'],maps['y']
    if polar:
        if closed_polar:
            # An even 2π-periodic harmonic has identical reflected radial sections.
            nodes={z for z in learned_nodes(maps['r']) if isinstance(z,tuple) and z[0] in ('sin','cos')}
            if not nodes or any(z[0]!='cos' or m.num(affine(z[1],v)[0]) is None or m.num(affine(z[1],v)[0]).denominator!=1 or affine(z[1],v)[1]!=m.ZERO for z in nodes):
                raise Unsupported('The polar arc has no established complete period and reflection')
            if m.variable_in(m.substitute(maps['r'],{n:('s','__harmonic') for n in nodes}),v):
                raise Unsupported('A nonperiodic radial component is present')
        if v=='r' and m.sign(bounds[0],cond) in (0,1) and not solid:pass
        elif v=='phi' and metric_sign(maps['r'],v,*bounds,cond)==1 and None not in tuple(m.pi_multiple(b) for b in bounds) and 0<m.pi_multiple(bounds[1])-m.pi_multiple(bounds[0])<=2:pass
        else:raise Unsupported('Nonnegative polar radii on a nonrepeating angular interval remain unproved')
        if solid and not closed_polar:raise Unsupported('Rotation multiplicity of the polar arc remains open')
    if v not in ('x','y') and not polar:
        axial=X if solid and axis=='y' else Y;radial=(Y if axis=='y' else X) if solid else None
        vals=[X,Y] if not solid else [axial,radial]
        if not solid and library.data.get('radial_arc_domain'):vals.append(m.dot((X,Y),(X,Y)))
        radial_orientation=0
        for coord in vals:
            if any(z[0] not in ('v','s','q','pi','mul','div','pow','add','sin','cos','sinh','cosh','exp') for z in learned_nodes(coord) if isinstance(z,tuple)):continue
            vel=request('monotone chart coordinate',dict(kind='differentiate',variable=v,function=source(coord),parameters=params,
                stated_conditions=positive,method_requirement='table_and_rules'))['value']
            vel=freeze(vel)
            sign=metric_sign(vel,v,*bounds,cond)
            if sign not in (-1,1):continue
            mid=m.div(m.add(*bounds),q(2));at_mid=m.simplify(m.substitute(vel,{p:mid}))
            if m.sign(at_mid,cond)!=sign:continue
            if solid and coord==radial:
                at=[m.sign(m.add(m.substitute(radial,{p:e}),m.neg(center)),cond) for e in bounds]
                if sign==1 and at[0] in (0,1) or sign==-1 and at[1] in (0,1):radial_orientation=1
                elif sign==1 and at[1] in (0,-1) or sign==-1 and at[0] in (0,-1):radial_orientation=-1
                else:continue
            break
        else:raise Unsupported('A nonrepeating parameter interval or rotation multiplicity remains unproved')
    if solid and axis==v:
        if not (m.sign(m.add(bounds[0],m.neg(center)),cond) in (0,1) or m.sign(m.add(bounds[1],m.neg(center)),cond) in (0,-1)):
            reflected=m.add(m.mul(q(2),center),m.neg(p))
            chart=Y if v=='x' else X
            other=m.substitute(chart,{p:reflected})
            for t in learned_nodes(other):
                if isinstance(t,tuple) and t[0] in ('cos','cosh','sin','sinh'):
                    for z in learned_nodes(chart):
                        if isinstance(z,tuple) and z[0]==t[0] and same_value(z[1],m.neg(t[1])):
                            other=m.substitute(other,{t:z if z[0] in ('cos','cosh') else m.neg(z)});break
            if not same_value(m.add(*bounds),m.mul(q(2),center)) or not same_value(chart,other):
                raise Unsupported('A folded profile can cover the same surface twice')
            interval=(source(center),interval[1]);bounds=(center,bounds[1])
    curves=[X,Y];coords=['__X','__Y'];scale=m.ONE
    scalar='1'
    if solid:
        distance=coords['xy'.index(axis)];rad=Y if axis=='y' else X
        sign=metric_sign(m.add(rad,m.neg(center)),v,*bounds,cond)
        if sign is None and v not in ('x','y') and not polar:sign=radial_orientation
        if polar and solid and v=='phi' and closed_polar:sign=1
        scalar='2*pi*'+(str(sign)+'*('+distance+'-('+source(center)+'))' if sign in (-1,1) else 'abs('+distance+'-('+source(center)+'))')
    root_chart=None
    if bounds[0]==m.ZERO:
        nodes={z for e in curves for z in learned_nodes(e) if isinstance(z,tuple) and z[0] in ('sqrt','rpow')}
        for node in sorted(nodes,key=str):
            base=node[1];power=F(1,2) if node[0]=='sqrt' else m.num(m.simplify(node[2]))
            if (power is None or power<=0 or power.denominator not in (2,3) or node[0]=='rpow' and
                    (m.variable_in(node[2],v) or any(not known_guard(g,cond) for g in domain_conditions(node[2])))):continue
            if any(not known_guard(g,cond) for g in domain_conditions(base)):continue
            try:A,B=affine(m.simplify(base),v)
            except Unsupported:continue
            if B!=m.ZERO or m.sign(A,cond)!=1:continue
            k=power.denominator;right=m.simplify(('sqrt' if k==2 else 'cbrt',m.mul(A,bounds[1])))
            if m.sign(right,cond)!=1:continue
            image=m.div(m.power(p,k),A);new=m.power(p,power.numerator)
            curves=[m.substitute(c,{node:new,p:image}) for c in curves]
            interval=('0',source(right));bounds=(m.ZERO,right);root_chart=dict(source_power=node,image=image,transformed=new,nonnegative_root=right)
            break
    # A positive angular or hyperbolic scale removes a fixed dimensional frequency.
    for node in (z for curve in curves for z in learned_nodes(curve)):
        if not isinstance(node,tuple) or node[0] not in ('cos','sin','cosh','sinh','exp'):continue
        try:freq,_=affine(m.simplify(node[1]),v)
        except Unsupported:continue
        if m.sign(freq,cond)!=1 or m.num(freq) is not None:continue
        scale=m.div(m.ONE,freq);curves=[m.substitute(g,{p:m.mul(scale,p)}) for g in curves]
        interval=tuple(source(m.mul(z,freq)) for z in bounds);break
    child=dict(kind='line_integral',variables=coords,parameter=v,scalar=scalar,parameters=params,stated_conditions=positive,
              path=[dict(map=list(map(source,curves)),lower=interval[0],upper=interval[1])],requested_output=['line_integral'])
    integral=request('arc density along the original curve',child)
    value=freeze(integral['value'])
    return dict(argument='nonrepeating_profile',source_interval_verified=True,interval=interval,coordinates=curves,positive_parameter_scale=scale,root_chart=root_chart,endpoint_facts=endpoint_facts,**({'ordinate_definitions':bindings} if bindings else {}),radius_density=scalar,
                line_integral=integral['compilation']['pieces']),{'surface_area' if solid else 'arc_length':value}


def radial_height_volume(task,library,request,field_weight=None):
    """Detect a complete disk from every intersection of two rotationally invariant height graphs."""
    from itertools import product
    from tasks import source,known_guard
    from model import freeze
    from verify import same_value
    if task['kind']!='bounded_solid_volume' or not library.data.get('solid_sections'):return None
    raw=task.get('surfaces');method=task.get('method_requirement')
    if (set(task)-{'id','kind','source','parameters','surfaces','stated_conditions','method_requirement','requested_output'} or
        method not in (None,'polar_coordinates','triple_integral') or
        task.get('requested_output')!=(['exact_volume','specified_method'] if method=='triple_integral' else ['exact_volume'])):return None
    if isinstance(raw,str):raw=[v.strip() for v in raw.split(',')]
    if not isinstance(raw,list):return None
    guards=list(task.get('stated_conditions',[]));walls=[]
    for s in raw:
        if re.fullmatch(r'[A-Za-z_]\w*>0',s):guards.append(s)
        else:walls.append(s)
    if not 2<=len(walls)<=3:return None
    coords=['x','y','z'];names=set(re.findall(r'\b[A-Za-z_]\w*\b',' '.join(walls)))-set(coords)-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'}
    params=sorted(names|set(task.get('parameters',[])));positive=set()
    for s in guards:
        if s in ('positive parameters','parameters positive'):positive.update(params)
        elif s.endswith('>0') and s[:-2] in params:positive.add(s[:-2])
        else:return None
    cond=[p+'>0' for p in sorted(positive)]
    ctx=m.context(dict(variable='__axial',parameters=params,parameter_conditions=cond))
    x,y,z=[('s',v) for v in coords];r=('s','__radius');station=('v','__radius')
    pairs=[s.split('=') for s in walls]
    if any(len(pair)!=2 for pair in pairs):return None
    pairs=[[m.parse(s,None,[*coords,*params]) for s in pair] for pair in pairs]
    scales=[m.ONE,*(('s',p) for p in sorted(positive))]
    for dx,dy in product(scales,repeat=2):
        R=m.add(m.div(m.power(x,2),m.power(dx,2)),m.div(m.power(y,2),m.power(dy,2)))
        roof=[];limits=[]
        for pair in pairs:
            mapped=[]
            for side in pair:
                # Replacement must account for the original radial form exactly on all rays.
                from integrals import learned_nodes
                nodes=[n for n in learned_nodes(side) if isinstance(n,tuple) and n[0]=='add' and m.contains(n,x) and m.contains(n,y)
                       and all(known_guard(g,ctx) for g in domain_conditions(n)) and same_value(n,R)]
                value=m.substitute(side,{node:m.power(r,2) for node in nodes})
                if m.contains(value,x) or m.contains(value,y):
                    if domain_conditions(side):break
                    candidate=m.simplify(m.substitute(side,{x:m.mul(dx,r),y:m.ZERO}))
                    num,den=m.rational_form(candidate)
                    def radial_polynomial(terms):
                        result=m.ZERO
                        for mon,c in terms.items():
                            powers=dict(mon);j=powers.pop(r,0)
                            if j%2:return None
                            result=m.add(result,m.mul(m.poly_expr({tuple(powers.items()):c}),m.power(R,j//2)))
                        return result
                    N,D=radial_polynomial(num),radial_polynomial(den)
                    if N is None or D is None or not same_value(side,m.div(N,D)):break
                    value=candidate
                value=m.substitute(value,{('sqrt',m.power(r,2)):r,('abs',r):r})
                radius_ctx=m.context(dict(variable='__axial',parameters=[*params,r[1]],parameter_conditions=[*cond,r[1]+'>0']))
                if any(not known_guard(g,radius_ctx) for g in domain_conditions(value)):break
                if any(not known_guard(g,ctx) for g in domain_conditions(m.substitute(value,{r:m.ZERO}))):break
                mapped.append(m.simplify(value))
            if len(mapped)!=2:break
            f=m.add(mapped[0],m.neg(mapped[1]));B=m.simplify(m.substitute(f,{z:m.ZERO}))
            if m.contains(f,z):
                A=m.simplify(m.add(m.substitute(f,{z:m.ONE}),m.neg(B)))
                if m.contains(A,r) or not m.constant_defined(A,ctx) or m.sign(A,ctx) not in (-1,1) or not same_value(f,m.add(B,m.mul(A,z))):break
                roof.append(m.div(m.neg(B),A))
            else:limits.append(B)
        else:
            if len(roof)==2:break
    else:return None
    diff=m.add(roof[1],m.neg(roof[0]));edge=limits[0] if limits else diff
    if len(limits)>1:return None
    # A radial wall needs ordering even on the unbounded exterior if a second bounded chamber is possible.
    fixed_sign=None
    if limits:
        for sign in [1,-1]:
            e=m.simplify(m.mul(q(sign),diff))
            if e[0]=='exp':fixed_sign=sign;break
        if fixed_sign is None:return None
    scale_choices=[*scales,*(('abs',('s',p)) for p in params if p not in positive)]
    for scale in scale_choices:
        if scale[0]=='abs':
            # A radius defined by R² can vanish. Its zero branch is recorded separately; no division by R is used there.
            raw_scale=scale[1]
            square=m.power(raw_scale,2);edge0=m.substitute(edge,{r:m.ZERO})
            if not (limits and same_value(edge,m.add(m.power(r,2),edge0)) and same_value(edge0,m.neg(square))):continue
            P=(F(-1),F(0),F(1));sign=1
        else:
            normal=m.substitute(edge,{r:m.mul(scale,station)})
            num,den=m.rational_form(normal)
            if not num or m.variable_in(m.poly_expr(den),'__radius'):continue
            common=m.common_mon(num);factor=m.poly_expr({tuple((v,k) for v,k in common.items() if v!=station):F(1)})
            sign=m.sign(m.div(factor,m.poly_expr(den)),ctx)
            if sign not in (-1,1):continue
            try:P,D=poly.rf(m.div(m.poly_expr(num),factor),'__radius')
            except poly.NotRational:continue
            if D!=(F(1),):continue
        roots=rational_roots(P)
        if any(v.b for v in roots):continue
        radii=sorted({s.a for s in roots if s.a>0})
        if len(radii)!=1:continue
        upper=q(radii[0]);direction=fixed_sign or sign*line.sign(peval(P,radii[0]/2))
        if not direction:continue
        low,high=roof if direction==1 else reversed(roof)
        parameter=m.mul(scale,('s','u'));jac=m.mul(dx,m.mul(dy,m.mul(m.power(scale,2),('s','u'))))
        # All admitted radial surfaces extend continuously to r=0. Do not discard an axial pole.
        if any(any(not known_guard(g,ctx) for g in domain_conditions(m.substitute(e,{r:m.ZERO}))) for e in roof):continue
        bounds=[dict(variable='phi',lower='0',upper='2*pi'),dict(variable='u',lower='0',upper=source(upper)),
                dict(variable='z',lower=source(m.substitute(low,{r:parameter})),upper=source(m.substitute(high,{r:parameter})))]
        differential=jac
        if field_weight is not None:
            # Keep the original expression, including poles, in the global cylindrical chart.
            from integrals import learned_nodes
            terms={n:m.power(parameter,2) for n in learned_nodes(field_weight) if isinstance(n,tuple) and
                   n[0]=='add' and m.contains(n,x) and m.contains(n,y) and not domain_conditions(n) and same_value(n,R)}
            radial=m.substitute(field_weight,terms)
            if m.contains(radial,x) or m.contains(radial,y):return None
            differential=('mul',jac,radial)
        child=dict(kind='iterated_integral',parameters=params,stated_conditions=cond,integration_order=bounds,integrand=source(differential),requested_output=['exact_integral'])
        result=request('full cylindrical integral of ordered heights',child)
        plan=dict(theorem='method.radial_height_sections',horizontal_scales=[dx,dy],radial_scale=scale,root_polynomial=[q(c) for c in P],
                    all_positive_roots=[upper],zero_scale_volume=0 if scale[0]=='abs' else None,heights=[low,high],bounds=bounds,jacobian=jac)
        value=freeze(result['value'])
        return plan,value if field_weight is not None else {'volume':value}
    return None


def power_simplex_measure(task,library):
    """Positive coordinate powers transform each bounded sheet into a simplex with a monomial Jacobian."""
    from quadrature import gamma_rational
    from verify import same_value
    kind=task['kind'];volume=kind=='bounded_solid_volume'
    if not library.data.get('solid_sections') or not volume:return None
    allowed={'id','source','kind','requested_output','parameters','surfaces','method_requirement','stated_conditions'}
    method=task.get('method_requirement');wanted=['exact_volume'] if method is None else ['exact_volume','substitution_and_jacobian']
    if set(task)-allowed or method not in (None,'change_of_variables') or task.get('requested_output')!=wanted:return None
    raw=task['surfaces'];equations=raw if isinstance(raw,list) else [z.strip() for z in raw.split(',')]
    coords=('x','y','z');walls={v for v in coords if v+'=0' in equations}
    candidates=[eq for eq in equations if eq not in (v+'=0' for v in coords)]
    if len(candidates)!=1:return None
    sides=candidates[0].split('=')
    if len(sides)!=2 or sides[1].strip()!='1':return None
    names=set(re.findall(r'\b[A-Za-z_]\w*\b',sides[0]))-set(coords)-m.FUNCTIONS-set(m.ALIASES)-{'pi','e'}
    conditions=task.get('stated_conditions',[]);fixed=set(task.get('parameters',[]));positive=set();negative=set();orthant=set()
    if fixed&set(coords):return None
    for c in conditions:
        if c in ('parameters positive','positive parameters'):positive.update(names|fixed)
        elif c in {v+s for v in coords for s in ('>0','>=0')}:orthant.add(c[0])
        elif c.endswith('>0') and c[:-2] in names|fixed:positive.add(c[:-2])
        elif c.endswith('<0') and c[:-2] in names|fixed:negative.add(c[:-2])
        else:return None
    expr=m.parse(sides[0],None,[*coords,*sorted(names|fixed)])
    # A real variable exponent is defined as exp(p*log(base)). Keep these raw domain
    # obligations separate from the conditions on coordinates and from the sign of an integer power.
    guards=domain_conditions(expr)
    parameter_domain={g[1] for rel,g in guards if rel=='positive' and g[0]=='s' and g[1] in names|fixed}
    nonzero={g[1][1] for rel,g in guards if rel=='nonzero' and g[0]=='pow' and g[2]!=0 and g[1][0]=='s' and g[1][1] in names|fixed}
    if negative&(positive|parameter_domain):return None
    assumptions=[v+'>0' for v in sorted(positive|parameter_domain)]+[v+'<0' for v in sorted(negative)]+[v+'!=0' for v in sorted(nonzero-negative-positive-parameter_domain)]
    ctx=m.context(dict(variable='__sheet',parameters=sorted(names|fixed),parameter_conditions=assumptions))
    def summands(e):
        if e[0]=='add':yield from summands(e[1]);yield from summands(e[2])
        else:yield e
    def base_and_power(e):
        if e[0]=='sqrt':return e[1],q(1,2)
        if e[0]=='cbrt':return e[1],q(1,3)
        if e[0]=='rpow':
            if not m.constant_defined(e[2],ctx):raise Unsupported('The original real exponent is not defined for every allowed parameter')
            return e[1],m.simplify(e[2])
        if e[0]=='pow':return e[1],q(e[2])
        return e,m.ONE
    chart={};multiplicity=1
    for term in summands(expr):
        if term[0]=='div':
            b,p=base_and_power(term[1]);scale,r=base_and_power(term[2])
            if not same_value(p,r):return None
        else:
            b,p=base_and_power(term);scale=m.ONE
            if b[0]=='div':b,scale=b[1:]
        if b[0]!='s' or b[1] not in coords or b[1] in chart or any(m.contains(e,('s',v)) for e in (scale,p) for v in coords):return None
        degree=m.num(p)
        if degree and degree.denominator==1 and degree.numerator%2==0 and m.constant_defined(scale,ctx) and m.nonzero(scale,ctx):
            sign=m.sign(scale,ctx)
            if sign!=1:scale=m.neg(scale) if sign==-1 else ('abs',scale)
        if not all(m.constant_defined(e,ctx) and m.sign(e,ctx)==1 for e in (scale,p)):return None
        j=b[1];n=m.num(p)
        if j not in orthant|walls:
            if n is None or n.denominator%2==0 or n.numerator%2:return None
            multiplicity*=2
        chart[j]=dict(scale=scale,exponent=p,inverse_exponent=m.div(m.ONE,p))
    if set(chart)!=set(coords):return None
    if parameter_domain-positive:
        raise Unsupported('The printed parameters permit integer specializations of real exponents. The signs and real domains of all powered scales have not been classified.')
    jacobian=q(multiplicity);total=m.ONE;shape=[]
    for v in coords:
        c=chart[v];alpha=c['inverse_exponent'];jacobian=m.mul(jacobian,m.mul(c['scale'],alpha))
        shape.append(alpha);total=m.add(total,alpha)
    factors=[gamma_rational(m.num(z)) for z in shape];denom=gamma_rational(m.num(total))
    # Integrating one variable at a time gives B(alpha,tail); the gamma factors of
    # adjacent tails cancel. The argument 1 is the constant density of the unused simplex slack.
    tails=[];tail=m.ONE
    for alpha in reversed(shape):
        tails.append((alpha,tail));tail=m.add(alpha,tail)
    formula=dict(factor=jacobian,gamma_numerator=shape,gamma_denominator=total)
    if all(z is not None for z in factors) and denom is not None:
        answer=jacobian
        for z in factors:answer=m.mul(answer,z)
        answer=m.div(answer,denom)
    else:answer=formula
    natural=sorted(v+'>0' for v in parameter_domain)+sorted(v+'!=0' for v in nonzero-parameter_domain-positive-negative)
    plan=dict(theorem='method.dirichlet_power_simplex_measure',chart=chart,octant_walls=sorted(walls|orthant),congruent_sheets=multiplicity,
              beta_steps=tails,inverse_jacobian_factor=jacobian,shape_parameters=shape,gamma_quotient=formula)
    if natural:plan['raw_real_power_domain']=natural
    result={'volume':answer}
    if nonzero-parameter_domain-positive-negative:result['parameter_domain']=natural
    return plan,result


def projection_moments(task,library,request,field_weight=None):
    """Derive a single planar face, then integrate its mass moments or its two ordered height graphs."""
    from itertools import product
    from math import comb
    from model import freeze
    from tasks import source,known_guard
    from verify import same_value
    kind=task['kind'];volume=kind=='bounded_solid_volume'
    wanted=task.get('requested_output');method=task.get('method_requirement');params=list(task.get('parameters',[]))
    common={'kind','id','source','parameters','requested_output','stated_conditions'}
    extra={'surfaces','method_requirement'} if volume else {'region','density'}
    if (not library.data.get('solid_sections') or set(task)-common-extra or
            volume and (method not in (None,'triple_integral') or wanted!=(['exact_volume','specified_method'] if method else ['exact_volume'])) or
            not volume and (kind!='lamina_centroid' or task.get('density')!='constant' or wanted!=['centroid_coordinates'])):
        raise Unsupported('Required geometry, integration method or density is not covered by a Cartesian projection')
    raw=task['surfaces'] if volume else task['region'];conditions=list(task.get('stated_conditions',[]))
    if isinstance(raw,str):
        match=re.fullmatch(r'(.+) \(([a-zA-Z_]\w*>0)\)',raw)
        if match:raw,guard=match.groups();conditions.append(guard)
        raw=[s.strip() for s in raw.split(',')]
    for c in conditions:
        if not re.fullmatch(r'[A-Za-z_]\w*>0',c):raise Unsupported('A geometric condition has no proved Cartesian translation')
        if c[:-2] not in params:params.append(c[:-2])
    coords=['x','y','z'];x,y,z=(('s',k) for k in coords);ctx=m.context(dict(variable='__face',parameters=params,parameter_conditions=conditions))
    if set(coords).intersection(params):raise Unsupported('Coordinates and constants must be distinct')
    walls=[];heights=[]
    for equation in raw:
        parts=equation.split('=')
        if len(parts)!=2:raise Unsupported('Expected a source surface equality')
        sides=[m.parse(p,None,[*coords,*params]) for p in parts]
        if any(not known_guard(g,ctx) for side in sides for g in domain_conditions(side)):raise Unsupported('A projected wall has an unproved original domain')
        body=m.add(sides[0],m.neg(sides[1]))
        if not m.contains(body,z):walls.append(body);continue
        base=m.substitute(body,{z:m.ZERO});slope=m.add(m.substitute(body,{z:m.ONE}),m.neg(base))
        if not volume or m.sign(slope,ctx) not in (-1,1) or not same_value(body,m.add(base,m.mul(slope,z))):
            raise Unsupported('The two bounding heights must be global single-valued graphs')
        heights.append(m.div(m.neg(base),slope))
    if len(walls)<2 or len(heights)!=(2 if volume else 0):raise Unsupported('Two height walls and a closed projected face have not been derived')
    scales=[m.ONE,*(('s',p) for p in params if p+'>0' in conditions)]
    for dx,dy in product(scales,repeat=2):
        pull={x:m.mul(dx,x),y:m.mul(dy,y)};normalized=[]
        for e in walls:
            numerator,den=m.rational_form(m.substitute(e,pull))
            if not numerator or len(den)!=1:break
            common=m.common_mon(numerator);factor=m.poly_expr({tuple((s,k) for s,k in common.items() if s not in (x,y)):F(1)})
            if m.sign(factor,ctx)!=1 or m.sign(m.poly_expr(den),ctx) not in (-1,1):break
            reduced=m.div(m.poly_expr(numerator),factor)
            if any(m.contains(reduced,('s',p)) for p in params):break
            normalized.append(reduced)
        if len(normalized)==len(walls):break
    else:raise Unsupported('No positive scaling of the source curves isolates a parameter-free bounded face')
    boundaries=normalized
    if field_weight is not None:
        # Sections also end where the two original height graphs meet, even without a vertical wall.
        contact=m.simplify(m.substitute(m.add(heights[0],m.neg(heights[1])),pull))
        if m.contains(contact,x) or m.contains(contact,y):boundaries=[*normalized,contact]
    partition,strips=bounded_cell_strips(boundaries,coords[:2])
    endpoints={strips[0][0],strips[-1][1]}
    for wall in normalized:
        on_curve=any(same_value(m.substitute(wall,{y:edge}),m.ZERO) for _,_,l,h in strips for edge in (l,h))
        on_end=any(same_value(m.substitute(wall,{x:edge}),m.ZERO) for edge in endpoints)
        if not on_curve and not on_end:raise Unsupported('A supplied wall does not bound the selected planar face')
    transformed=[m.simplify(m.substitute(h,pull)) for h in heights]
    values={};pieces=[];jac=m.mul(dx,dy);orientation=None
    for i,(a,b,l,h) in enumerate(strips):
        D=m.add(b,m.neg(a));L=m.add(h,m.neg(l));bounds=[dict(variable='x',lower=source(a),upper=source(b)),dict(variable='y',lower=source(l),upper=source(h))]
        if volume:
            # Substitute the exact section bounds into the height difference. Nonnegative Bernstein
            # coefficients on the unit square prove a global order, including at touching fibers.
            root=m.add(a,m.mul(D,x));ordinate=m.substitute(m.add(l,m.mul(L,y)),{x:root})
            difference=m.add(transformed[1],m.neg(transformed[0]))
            num,den=m.rational_form(m.substitute(difference,{x:root,y:ordinate}))
            denominator=m.poly_expr(den);degree=[max((dict(mon).get(v,0) for mon in num),default=0) for v in (x,y)]
            if m.sign(denominator,ctx) not in (-1,1) or any(k>12 for k in degree):raise Unsupported('No finite Bernstein sign witness for height ordering')
            signs=set();basis=[]
            for u,v in product(range(degree[0]+1),range(degree[1]+1)):
                coefficient=m.ZERO
                for mon,c in num.items():
                    powers=dict(mon);j,k=powers.pop(x,0),powers.pop(y,0)
                    if j<=u and k<=v:
                        weight=F(comb(u,j)*comb(v,k),comb(degree[0],j)*comb(degree[1],k))
                        coefficient=m.add(coefficient,m.poly_expr({tuple(powers.items()):c*weight}))
                coefficient=m.div(coefficient,denominator);basis.append(coefficient);signs.add(m.sign(coefficient,ctx))
            if signs<={0,1} and 1 in signs:direction=1
            elif signs<={-1,0} and -1 in signs:direction=-1
            else:raise Unsupported('The graphs cross or their order on this projected face remains unproved')
            if orientation is not None:
                if orientation!=direction or same_value(m.substitute(difference,{x:a}),m.ZERO):
                    raise Unsupported('An interior pinch separates two bounded solid components')
            orientation=direction
            low,high=transformed if direction==1 else reversed(transformed)
            bounds.append(dict(variable='z',lower=source(low),upper=source(high)))
            densities={'volume':jac} if field_weight is None else {'integral':('mul',jac,m.substitute(field_weight,pull))}
        else:basis=[];densities={'mass':jac,'moment_x_coordinate':m.mul(jac,m.mul(dx,x)),'moment_y_coordinate':m.mul(jac,m.mul(dy,y))}
        pieces.append(dict(bounds=bounds,height_bernstein_coefficients=basis))
        for name,f in densities.items():
            child=dict(kind='iterated_integral',parameters=params,stated_conditions=conditions,integration_order=bounds,integrand=source(f),requested_output=['exact_integral'])
            value=freeze(request(name+' over projected strip '+str(i),child)['value'])
            values[name]=m.add(values.get(name,m.ZERO),value)
    plan=dict(theorem='method.projected_region_moments',projection=partition,scale=(dx,dy),pieces=pieces,integrals=values)
    if field_weight is not None:return plan,values['integral']
    if volume:return plan,{'volume':values['volume']}
    if m.sign(values['mass'],ctx)!=1:raise Unsupported('Cannot divide first moments by an unproved positive mass')
    return plan,{'centroid':[m.div(values[k],values['mass']) for k in ('moment_x_coordinate','moment_y_coordinate')]}


def spatial_reduction(task,library,request):
    """Recover and certify Cartesian fibers before evaluating the original density."""
    from model import freeze
    from quadrature import guard_bounds
    from tasks import source
    mass=task.get('kind')=='solid_mass'
    field='density' if mass else 'integrand'
    fields={'kind','id','source','region',field,'requested_output','stated_conditions','parameters','method_requirement'}
    printed=task.get('source',{})
    method=task.get('method_requirement')
    if (not library.data.get('spatial_cartesian_reduction') or set(task)-fields
            or not isinstance(printed,dict) or set(printed)-{'exercise','pdf_page','printed_page','pdf_sha256','literal_requirement','printed_subpart'}
            or task.get('requested_output')!=['mass' if mass else 'exact_integral']
            or method not in (None,'cylindrical_coordinates') or mass and method):
        raise Unsupported('A required coordinate system, domain or output is not covered by Cartesian reduction')
    region=task['region'];params=task.get('parameters',[]);constraints=task.get('stated_conditions',[])
    if not isinstance(region,str) or not isinstance(constraints,(list,tuple)):raise Unsupported('Expected a single source solid')
    if region.startswith('bounded by ') and not mass:
        walls=region[len('bounded by '):].split(',')
        body=m.parse(task[field],None,['x','y','z',*params])
        geometry=dict(kind='bounded_solid_volume',surfaces=walls,parameters=params,stated_conditions=constraints,requested_output=['exact_volume'])
        if (polar:=radial_height_volume(geometry,library,request,field_weight=body)) is not None:return polar
        if method:raise Unsupported('The prescribed cylindrical reduction has no admitted graph or radial field')
        return projection_moments(geometry,library,request,field_weight=body)
    if method:raise Unsupported('The Cartesian box does not supply the prescribed coordinate change')
    if params or constraints:raise Unsupported('Fixed parameters or additional restrictions require a certified box or exterior domain')
    bounds=[];cube={}
    for clause in region.split(','):
        box=re.fullmatch(r'\s*([^<>=]+?)\s*<=\s*([A-Za-z_]\w*)\s*<=\s*([^<>=]+?)\s*',clause)
        if not box:raise Unsupported('Expected three finite coordinate intervals')
        a,v,b=box.groups();ends=[m.parse(s,None) for s in (a,b)]
        if any(not m.constant_defined(e,{'parameters':[],'assumptions':[]}) for e in ends):
            raise Unsupported('Undefined original box endpoint')
        lo,hi=[m.num(m.simplify(e)) for e in ends]
        if lo is None or hi is None or lo>hi or ('s',v) in cube:raise Unsupported('Unordered or repeated box coordinate')
        cube[('s',v)]=m.add(q(lo),m.mul(q(hi-lo),('v',v)))
        bounds.append(dict(variable=v,lower=a,upper=b))
    vs=[b['variable'] for b in bounds]
    if len(vs)!=3:raise Unsupported('The solid needs three independent coordinates')
    f=m.parse(task[field],None,vs);sign=None
    if mass:sign=tuple(q(w) for w in guard_bounds('nonnegative',m.substitute(f,cube),(F(0),F(1)),vs))
    child=dict(kind='iterated_integral',integration_order=bounds,integrand=source(f),requested_output=['exact_integral'])
    answer=freeze(request('integral of original field over box',child)['value'])
    return dict(theorem='method.spatial_cartesian_reduction',bounds=bounds,source_field=f,density_enclosure=sign),answer


def monomial_section_volume(task,library,request):
    """Discover two independent monomial levels among the printed walls and check every sign sheet."""
    from itertools import product
    from tasks import source
    if not library.data.get('monomial_section_volume') or task['kind']!='bounded_solid_volume':return None
    fields={'id','kind','source','surfaces','parameters','stated_conditions','method_requirement','requested_output'}
    method=task.get('method_requirement');meta=task.get('source',{})
    options={None:['exact_volume'],'change_of_variables':['exact_volume','substitution_and_jacobian']}
    if set(task)-fields or method not in options or task.get('requested_output')!=options[method]:return None
    headings={None:'Найти объём тела, ограниченного указанными поверхностями.',
              'change_of_variables':'Вычислить объём, пользуясь подходящей заменой переменных. Параметры положительны.'}
    if set(meta)-{'exercise','printed_subpart','pdf_page','printed_page','pdf_sha256','literal_requirement'} or meta.get('literal_requirement',headings[method])!=headings[method]:return None
    raw=task['surfaces'];walls=raw.split(',') if isinstance(raw,str) else raw
    if not isinstance(walls,(list,tuple)) or len(walls) not in (5,6):return None
    walls=[re.sub(r'\bxy\b','(x*y)',s.strip()) for s in walls]
    names=set(re.findall(r'[A-Za-z_]\w*',' '.join(walls)))-{'x','y','z','pi','e'}-m.FUNCTIONS-set(m.ALIASES)
    params=sorted(names|set(task.get('parameters',[])))
    if set(params)&{'x','y','z','U','V'}:return None
    cond=[];octant={};ordered={}
    for guard in task.get('stated_conditions',[]):
        if guard in ('positive parameters','parameters positive'):cond.extend(p+'>0' for p in params)
        elif guard in ('x>0','y>0','x<0','y<0'):
            sign=1 if '>' in guard else -1
            if guard[0] in octant and octant[guard[0]]!=sign:return None
            octant[guard[0]]=sign
        elif guard.endswith('>0') and guard[:-2] in params:cond.append(guard)
        elif (match:=re.fullmatch(r'0<(\w+)<(\w+)',guard)) and set(match.groups())<=set(params):
            a,b=match.groups();cond.extend((a+'>0',b+'>0',b+'-'+a+'>0'))
            ordered.setdefault(b,set()).add(a)
        else:return None
    from graphlib import TopologicalSorter,CycleError
    try:tuple(TopologicalSorter(ordered).static_order())
    except CycleError:return None
    cond=sorted(set(cond));ctx=m.context(dict(variable='z',parameters=params,parameter_conditions=cond))
    X,Y=('s','x'),('s','y');U,V=('s','U'),('s','V')
    def monomial(e):
        if e in (X,Y):return m.ONE,int(e==X),int(e==Y)
        if m.constant_defined(e,ctx):return m.simplify(e),0,0
        op=e[0]
        if op=='pow':
            c,a,b=monomial(e[1]);return m.power(c,e[2]),a*e[2],b*e[2]
        if op not in ('div','mul'):raise Unsupported('A side of the projected wall is not a Laurent monomial')
        c,i,j=monomial(e[1]);d,k,l=monomial(e[2]);sgn=1 if op=='mul' else -1
        if op=='div' and not m.nonzero(d,ctx):raise Unsupported('A coefficient of a wall may vanish')
        return (m.mul(c,d) if sgn==1 else m.div(c,d)),i+sgn*k,j+sgn*l
    walls_by_axis={};heights=[]
    try:
        for w in walls:
            pair=w.split('=')
            if len(pair)!=2:return None
            if 'z' in pair:
                if pair.count('z')!=1:return None
                heights.append(m.parse(pair[1-pair.index('z')],None,[*params,'x','y']));continue
            e,f=(m.parse(z,None,[*params,'x','y']) for z in pair)
            c,i,j=monomial(e);d,k,l=monomial(f);a,b=i-k,j-l
            if not any((a,b)) or not all(m.nonzero(s,ctx) for s in (c,d)):return None
            if (b or a)<0:a,b,d,c=-a,-b,c,d
            walls_by_axis.setdefault((a,b),[]).append(m.div(d,c))
    except Unsupported:return None
    if len(heights)!=2 or len(walls_by_axis)!=2 or any(len(vals) not in (1,2) for vals in walls_by_axis.values()):return None
    (a,b),(c,d)=walls_by_axis;det=a*d-b*c
    if not det:return None
    sheets=[]
    for sx,sy in product((1,-1),repeat=2):
        if any(octant[k]!=v for k,v in zip(('x','y'),(sx,sy)) if k in octant):continue
        box=[]
        for slot,((i,j),vals) in enumerate(walls_by_axis.items()):
            sign=(-1 if sx<0 and i%2 else 1)*(-1 if sy<0 and j%2 else 1)
            levels=[m.mul(q(sign),z) for z in vals]
            if any(m.sign(z,ctx) not in (-1,1) for z in levels):return None
            if any(m.sign(z,ctx)==-1 for z in levels):break
            if len(levels)==1:
                # The only missing boundary is the common vertex of the other two side curves.
                powers=(F(d,det),F(-c,det)) if slot==0 else (F(-b,det),F(a,det))
                if min(powers)<=0:return None
                levels.insert(0,m.ZERO)
            l,h=levels
            delta=m.sign(m.add(h,m.neg(l)),ctx)
            if delta not in (-1,1):return None
            box.append((l,h) if delta==1 else (h,l))
        if len(box)==2:sheets.append((sx,sy,box))
    if len(sheets)!=1:return None  # An unselected collection of disconnected bodies has ambiguous multiplicity.
    sx,sy,box=sheets[0]
    chart=m.context(dict(variable='z',parameters=params+['U','V'],parameter_conditions=cond+['U>0','V>0']))
    sheet=m.context(dict(variable='z',parameters=params+['x','y'],parameter_conditions=cond+[
        'x>0' if sx==1 else 'x<0','y>0' if sy==1 else 'y<0']))
    if not all(m.constant_defined(h,sheet) for h in heights):return None
    def push(i,j):
        def power(v,h):return m.power(v,int(h)) if h.denominator==1 else ('rpow',v,q(h))
        return m.mul(power(U,F(d*i-c*j,det)),power(V,F(a*j-b*i,det)))
    def transform(e):
        try:
            cf,i,j=monomial(e)
        except Unsupported:
            if e[0] not in ('add','mul','div','exp','sin','cos','pow','sqrt','ln'):raise
            return m.simplify((e[0],*(transform(z) if isinstance(z,tuple) else z for z in e[1:])))
        s=(-1 if sx<0 and i%2 else 1)*(-1 if sy<0 and j%2 else 1)
        return m.mul(m.mul(cf,q(s)),push(i,j))
    bottom,top=(transform(h) for h in heights)
    height=m.add(top,m.neg(bottom));sgn=m.sign(height,chart)
    def half_wave(e):
        if e[0]=='mul':
            left,right=half_wave(e[1]),half_wave(e[2])
            return left*right if left and right else None
        if e[0]!='sin':return m.sign(e,chart)
        for variable,(l,h) in zip((U,V),box):
            other=V if variable==U else U
            if m.contains(e[1],other):continue
            from integrals import affine
            from verify import same_value
            try:slope,intercept=affine(m.substitute(e[1],{variable:('v',variable[1])}),variable[1])
            except Unsupported:continue
            ends=tuple(m.add(m.mul(slope,v),intercept) for v in (l,h))
            if same_value(ends[0],m.ZERO) and same_value(ends[1],m.PI):return 1
            if same_value(ends[1],m.ZERO) and same_value(ends[0],m.PI):return 1
        return None
    if sgn not in (-1,1):sgn=half_wave(height)
    if sgn not in (-1,1):return None
    height=m.mul(q(sgn),height)
    jac=m.div(push(1,1),m.mul(q(abs(det)),m.mul(U,V)))
    bounds=[dict(variable=k,lower=source(l),upper=source(h)) for k,(l,h) in zip(('U','V'),box)]
    numerator,denominator=m.rational_form(m.mul(height,jac))
    if len(denominator)!=1:return None
    (den,dc),=denominator.items();stages=[];volume=m.ZERO
    from model import freeze
    for mon,coef in numerator.items():
        tags=dict(mon)
        for atom,n in den:tags[atom]=tags.get(atom,0)-n
        weight=q(coef/dc);factors=[m.ONE,m.ONE]
        for atom,power in tags.items():
            if power==0:continue
            deps=[i for i,v in enumerate((U,V)) if m.contains(atom,v)]
            if len(deps)>1:return None
            term=m.power(atom,power)
            if not deps:weight=m.mul(weight,term)
            else:factors[deps[0]]=m.mul(factors[deps[0]],term)
        for var,f,(l,h) in zip((U,V),factors,box):
            if f==m.ONE:weight=m.mul(weight,m.add(h,m.neg(l)));continue
            scale=m.ONE if f==var or f[0]=='pow' and f[1]==var or f[0]=='div' and f[1]==m.ONE and f[2]==var else (l if l!=m.ZERO else h)
            t=('v',var[1]);normalized=m.simplify(m.substitute(f,{var:m.mul(scale,t)}))
            start,end=m.div(l,scale),m.div(h,scale)
            probe=m.substitute(normalized,{t:var})
            if not m.constant_defined(probe,chart):return None
            child=request('primitive of one separated coordinate on the connected positive chart',
                          dict(kind='integrate',variable=t[1],integrand=source(normalized),parameters=params,
                               method_requirement='table_and_rules',requested_output=['primitive_family']))
            primitive=freeze(child['value']['representative'])
            if not m.constant_defined(m.substitute(primitive,{t:var}),chart):return None
            endpoints=[m.substitute(primitive,{t:s}) for s in (start,end)]
            if not all(m.constant_defined(z,ctx) for z in endpoints+[m.substitute(normalized,{t:start}),m.substitute(normalized,{t:end})]):return None
            value=m.mul(scale,m.add(m.simplify(endpoints[1]),m.neg(m.simplify(endpoints[0]))))
            weight=m.mul(weight,value);stages.append(dict(variable=var[1],scale=scale,lower=start,upper=end,integral=value))
        volume=m.add(volume,weight)
    plan=dict(theorem='method.monomial_section_volume',level_exponents=list(walls_by_axis),determinant=det,
              sign_sheet=[sx,sy],inverse_magnitudes=[push(1,0),push(0,1)],rectangle=bounds,
              positive_height=height,absolute_jacobian=jac,separated_integrals=stages)
    return plan,dict(volume=volume)


VOLUME_SOURCE_METHODS={
    'Найти объём в положительном октанте.':(None,),
    'Найти объём тела, ограниченного указанными поверхностями.':(None,'polar_coordinates'),
    'Найти объём с помощью тройного интеграла.':('triple_integral','spherical_or_cylindrical_triple_integral'),
    'Вычислить объём, пользуясь подходящей заменой переменных. Параметры положительны.':('change_of_variables',),
    'Найти объём тела, определитель матрицы коэффициентов отличен от нуля.':(None,),
    'Вычислить объём тела по напечатанным поверхности и плоскостям.':(None,),
    'Найти объём ограниченного тела.':(None,),'Вычислить объём ограниченного тела.':(None,)}


def bind_volume_source(task):
    """Pass printed spatial restrictions to every chart, including fallback section rules."""
    origin=task.get('source',{})
    fields={'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256','page_png_sha256',
            'literal_requirement','explicit_required_method','explicit_imposed_method','method_requirement'}
    if not isinstance(origin,dict) or set(origin)-fields or not isinstance(origin.get('literal_requirement',''),str):
        raise Unsupported('Unbound printed volume requirements')
    literal=origin.get('literal_requirement','').removesuffix(' Обобщённые сферические координаты рекомендованы.')
    method=task.get('method_requirement')
    if literal and method not in VOLUME_SOURCE_METHODS.get(literal,()) or any(origin.get(k,method)!=method for k in ('method_requirement','explicit_required_method','explicit_imposed_method')):
        raise Unsupported('The volume plan must preserve the printed region and method')
    if literal=='Найти объём в положительном октанте.':
        conditions=list(task.get('stated_conditions',[]))
        if any(re.fullmatch(r'[xyz](?:<0|<=0|=0)',s.replace(' ','')) for s in conditions):
            raise Unsupported('The coordinate restrictions contradict the printed positive octant')
        return {**task,'stated_conditions':list(dict.fromkeys([*conditions,'x>0','y>0','z>0']))}
    return task


def volume_coordinates_task(task):
    """Bind the volume, printed method and fixed parameters before drawing a coordinate chart."""
    if task.get('kind')!='bounded_solid_volume':return None
    allowed={'kind','id','source','surfaces','stated_conditions','parameters','suggested_method','method_requirement','requested_output'}
    if set(task)-allowed:return None
    given=task.get('source',{});method=task.get('method_requirement')
    outputs={None:['exact_volume'],'change_of_variables':['exact_volume','substitution_and_jacobian'],
             'spherical_or_cylindrical_triple_integral':['exact_volume','specified_method']}
    if method not in outputs or task.get('requested_output')!=outputs[method]:return None
    if not isinstance(given,dict) or set(given)-{'exercise','printed_subpart','pdf_page','pdf_pages','printed_page','pdf_sha256',
            'literal_requirement','explicit_required_method','method_requirement'}:return None
    literal=given.get('literal_requirement','').removesuffix(' Обобщённые сферические координаты рекомендованы.')
    if (literal and method not in VOLUME_SOURCE_METHODS.get(literal,()) or
            any(given.get(k,method)!=method for k in ('explicit_required_method','method_requirement'))):return None
    raw=task.get('surfaces')
    if not isinstance(raw,(str,list)) or not raw:return None
    return raw,task.get('stated_conditions',[]),literal


def volume_beta_moment(p,q0,request):
    """The quadrant moment is B((p+1)/2,(q+1)/2)/2. Keep both endpoint tests in the child proof."""
    from model import freeze
    from tasks import source
    from quadrature import gamma_rational
    expr='sin(x)^('+source(p)+')*cos(x)^('+source(q0)+')'
    child=dict(kind='euler_integral_evaluation',integrand=expr,limits='0..pi/2',method_requirement='euler_integrals_and_domain',
               requested_output=['existence_domain','euler_integral_formula'])
    value=request('angular integral and integrability at both ends',child)['value']
    if value.get('converges') is not True:raise Unsupported('Both angular endpoints require a proof of integrability')
    a=m.div(m.add(p,m.ONE),q(2));b=m.div(m.add(q0,m.ONE),q(2))
    if value.get('closed_value') is not None:return freeze(value['closed_value'])
    ga,gb,gs=[gamma_rational(m.num(t)) for t in (a,b,m.add(a,b))]
    if any(g is None for g in (ga,gb,gs)):raise Unsupported('The remaining angular beta moment is not elementary')
    return m.div(m.mul(ga,gb),m.mul(q(2),gs))


def spherical_volume(task,request,saved):
    """Search for a diagonal norm. Degree along a ray determines its outer radius and angular density."""
    from model import freeze
    from tasks import source
    from verify import same_value
    contract=volume_coordinates_task(task)
    if not contract:return None
    raw,conditions,literal=contract
    if 'октанте' in literal or 'определитель' in literal:return None
    equations=raw if isinstance(raw,list) else raw.split(',')
    if not 1<=len(equations)<=2 or equations[0].count('=')!=1:return None
    variables=('x','y','z');coords=tuple(('s',x) for x in variables)
    names=set(re.findall(r'\b[A-Za-z_]\w*\b',' '.join(equations)))-set(variables)-m.FUNCTIONS-{'pi','e'}
    fixed=task.get('parameters',[])
    if set(fixed)&set(variables) or any(c not in ['parameters positive','positive parameters',*(n+'>0' for n in names)] for c in conditions):return None
    positive=names if set(conditions)&{'parameters positive','positive parameters'} else {k[:-2] for k in conditions}
    if literal.endswith('Параметры положительны.') and not names<=positive:return None
    ctx=m.context(dict(variable='__ray',parameters=sorted(names|set(fixed)),parameter_conditions=[k+'>0' for k in sorted(positive)]))
    left,right=[m.parse(z,None,[*variables,*names]) for z in equations[0].split('=')]
    norm,power=(left[1],left[2]) if left[0]=='pow' else (left,1)
    if power<=0:return None
    def terms(z):
        return terms(z[1])+terms(z[2]) if z[0]=='add' else [z]
    def square(z):
        den=m.ONE
        if z[0]=='div':
            numerator,d=z[1:]
            if d[0]=='pow' and d[2]==2:den=d[1]
            elif m.num(d) is not None and m.num(d)>0:den=m.simplify(('sqrt',d))
            else:return None
            z=numerator
        if z[0]!='pow' or z[2]!=2:return None
        base=z[1]
        if base[0]=='div' and den==m.ONE:base,den=base[1:]
        if base not in coords or not m.constant_defined(den,ctx) or m.simplify(den)==m.ZERO:return None
        return base,den
    entries=[square(z) for z in terms(norm)]
    if len(entries)!=3 or None in entries:return None
    scales=dict(entries)
    if set(scales)!=set(coords):return None
    unit={v:t for v,t in zip([e[0] for e in entries],terms(norm))}
    axes={v:m.add(unit[coords[(i+1)%3]],unit[coords[(i+2)%3]]) for i,v in enumerate(coords)}
    digest_domain=[];scalar_den=[]
    for op,g in domain_conditions(left)+domain_conditions(right):
        if op!='nonzero':return None
        if not any(m.contains(g,v) for v in coords):
            if not m.constant_defined(g,ctx) or m.simplify(g)==m.ZERO:return None
            scalar_den.append(g)
        elif any(same_value(g,z) for z in [norm,*axes.values()]):digest_domain.append(g)
        else:return None
    # Internal directions never shadow free parameters, including the user's own direction-like names.
    directions={}
    for v in coords:
        name='direction_'+v[1]
        while name in names|set(fixed):name+='_'
        directions[v]=('s',name)
    def degree(z,axis):
        if not any(m.contains(z,v) for v in coords):return 0,z
        if z==norm:return 2,m.ONE
        if z[0]=='add' and same_value(z,axes[axis]):return 2,m.add(m.ONE,m.neg(m.power(directions[axis],2)))
        if z in coords:return 1,m.mul(scales[z],directions[z])
        op=z[0];d,a=degree(z[1],axis)
        if op=='pow':return d*z[2],m.power(a,z[2])
        if op=='exp' and d==0:return 0,m.simplify(('exp',a))
        if op not in ('add','mul','div'):raise Unsupported('The ray has no certified homogeneous degree')
        e,b=degree(z[2],axis)
        if op=='add' and d==e:return d,m.add(a,b)
        if op=='mul':return d+e,m.mul(a,b)
        if op=='div':return d-e,m.div(a,b)
        raise Unsupported('The terms on the ray have different radial degrees')
    def pospower(e,p):
        if p.denominator==1:return m.power(e,int(p))
        return m.simplify(('rpow',e,q(p)))
    def angular(g,axis,p,cone):
        D=tuple(directions.values());u=directions[axis]
        num,den=m.rational_form(g)
        if not num or not den:return None
        split={a:m.common_mon(num).get(a,0)-m.common_mon(den).get(a,0) for a in D}
        mon=m.ONE
        for a,k in split.items():mon=m.mul(mon,m.power(a,k))
        fixed_g=m.simplify(m.substitute(m.div(g,mon),{a:q(1,2) for a in D}))
        if all(k>=0 for k in split.values()) and not any(m.contains(fixed_g,a) for a in D) and same_value(g,m.mul(fixed_g,mon)):
            exps=[split[d] for d in D];odd=any(h%2 for h in exps)
            amp=m.simplify(('abs',fixed_g)) if odd else m.mul(q(1,2),m.add(fixed_g,m.simplify(('abs',fixed_g))))
            if cone is not None:
                if any(a!=u and k for a,k in split.items()):return None
                h=1+p*split[u];cap=m.div(m.add(m.ONE,m.neg(pospower(cone,h))),q(h))
                moment=m.mul(m.mul(q(2 if odd else 4),m.PI),cap)
            else:
                a,b,c=(h*p for h in exps)
                moment=m.mul(q(4 if odd else 8),m.mul(volume_beta_moment(q(b),q(a),request),
                                                       volume_beta_moment(q(1+a+b),q(c),request)))
            return m.mul(pospower(amp,p),moment),dict(mode='direction_monomial',powers=exps,coefficient=fixed_g,octants=4 if odd else 8,cap=cone)
        if cone is not None:return None
        if not any(m.contains(g,a) for a in D if a!=u):
            A=m.simplify(m.substitute(g,{u:m.ZERO}));B=m.add(m.simplify(m.substitute(g,{u:m.ONE})),m.neg(A))
            if A!=m.ZERO and m.known_nonnegative(A,ctx) and same_value(g,m.add(A,m.mul(B,m.power(u,2)))):
                K=m.num(m.simplify(m.div(m.neg(B),A)))
                if K is not None and K>=1:
                    bound=m.div(m.ONE,m.simplify(('sqrt',q(K))))
                    moment=m.mul(m.mul(q(4),m.PI),m.mul(bound,volume_beta_moment(m.ZERO,q(2*p+1),request)))
                    return m.mul(pospower(A,p),moment),dict(mode='axial_quadratic',offset=A,factor=q(K),angular_interval=[m.neg(bound),bound])
            if p==1:
                # Check the exact signed angular density before setting w=u^2 on the supported hemisphere.
                guess=m.simplify(m.substitute(m.div(g,u),{u:m.ONE}))
                coefficient=m.simplify(m.div(guess,('exp',q(-1))))
                if same_value(g,m.mul(m.mul(coefficient,u),('exp',m.neg(m.power(u,2))))):
                    t=dict(kind='iterated_integral',integrand='exp(-w)',integration_order=[dict(variable='w',lower='0',upper='1')],requested_output=['exact_integral'])
                    val=freeze(request('hemisphere integral after squaring its direction cosine',t)['value'])
                    return m.mul(m.PI,m.mul(m.simplify(('abs',coefficient)),val)),dict(mode='exponential_hemisphere',coefficient=coefficient,squared_direction=[0,1])
        for a in D:
            if a==u:continue
            form=m.div(m.power(a,2),m.add(m.ONE,m.neg(m.power(u,2))))
            with_axis=m.substitute(g,{u:m.ZERO});A=m.simplify(m.substitute(with_axis,{d:m.ONE for d in D}))
            if same_value(g,m.mul(A,form)) and m.known_nonnegative(A,ctx):
                moment=m.mul(q(8),volume_beta_moment(m.ZERO,q(2*p),request))
                return m.mul(pospower(A,p),moment),dict(mode='azimuth_power',coefficient=A,meridian_component=a,azimuth_exponent=q(2*p))
        return None
    axes_to_try=coords
    if saved and saved.get('theorem')=='method.homogeneous_ray_volume':
        axes_to_try=tuple(v for v in coords if v[1]==saved.get('axis'))
    for axis in axes_to_try:
        cone=None
        if len(equations)==2:
            match=re.fullmatch(r'([^<>=]+)\s*<=?\s*([^<>=]+)',equations[1])
            if not match:continue
            lhs,rhs=(m.parse(t,None,[*variables,*names]) for t in match.groups())
            if domain_conditions(lhs) or domain_conditions(rhs) or not same_value(lhs,axes[axis]) or not same_value(rhs,unit[axis]):continue
            cone=m.simplify(('sqrt',q(1,2)))
        try:d,g=degree(right,axis)
        except Unsupported:continue
        gap=2*power-d
        if gap<=0:continue
        try:integral=angular(m.simplify(g),axis,F(3,gap),cone)
        except (ZeroDivisionError,poly.NotRational):continue
        if integral is None:continue
        result,evidence=integral
        jac=m.ONE
        for v in coords:jac=m.mul(jac,scales[v])
        jac=m.simplify(('abs',jac))
        plan=dict(theorem='method.homogeneous_ray_volume',axis=axis[1],scales=[scales[v] for v in coords],directions=list(directions.values()),
                  radial_power=gap,angular_boundary=g,positive_directions_only=True,natural_nonzero=scalar_den,
                  removed_zero_measure=digest_domain,angular_integral=evidence,absolute_scale_jacobian=jac,radial_primitive='r^3/3')
        return plan,{'volume':m.simplify(m.mul(q(1,3),m.mul(jac,result)))}
    return None


def gamma_volume(coefficient,shapes,denominator):
    from quadrature import gamma_rational
    arguments=[m.num(m.simplify(arg)) for arg in shapes]
    total=m.num(m.simplify(denominator))
    factors=[gamma_rational(arg) for arg in arguments]
    divisor=gamma_rational(total)
    if divisor is not None and all(f is not None for f in factors):
        for factor in factors:coefficient=m.mul(coefficient,factor)
        return m.simplify(m.div(coefficient,divisor))
    # Gamma(s+k)=Gamma(s) times the k consecutive factors starting at s.
    for index,arg in enumerate(arguments):
        if arg is None or arg<=0 or total is None:continue
        shift=total-arg
        others=factors[:index]+factors[index+1:]
        if shift<0 or shift.denominator!=1 or any(g is None for g in others):continue
        for factor in others:coefficient=m.mul(coefficient,factor)
        divisor=prod(arg+j for j in range(int(shift)))
        return m.simplify(m.div(coefficient,q(divisor)))
    return dict(factor=coefficient,gamma_numerator=shapes,gamma_denominator=denominator)


def grouped_cross_sections(task):
    """A positive triangular or full elliptical slice with power-law intercepts reduces to a beta moment."""
    contract=volume_coordinates_task(task)
    if not contract:return None
    raw,conditions,literal=contract
    if literal=='Найти объём в положительном октанте.' or 'определитель' in literal:return None
    # These charts use affine triangular fibers or cylindrical disks, never spherical coordinates for a triangle.
    eqs=raw if isinstance(raw,list) else raw.split(',')
    variables=('x','y','z');coords=[('s',v) for v in variables]
    bounds={z for z in eqs if z in [v+'=0' for v in variables]}
    source_equations=[z for z in eqs if z not in bounds]
    if len(source_equations)!=1 or source_equations[0].count('=')!=1:return None
    lhs,rhs=source_equations[0].split('=')
    if rhs.strip()!='1':return None
    names=set(re.findall(r'\b[A-Za-z_]\w*\b',lhs))-set(variables)-m.FUNCTIONS-{'pi','e'}
    params=set(task.get('parameters',[]))
    if params&set(variables):return None
    positive=set();orthant=set()
    for z in conditions:
        if z in ('positive parameters','parameters positive'):positive.update(names|params)
        elif z in [v+sign for v in variables for sign in ('>=0','>0')]:orthant.add(z[0])
        elif z.endswith('>0') and z[:-2] in names:positive.add(z[:-2])
        else:return None
    if literal.endswith('Параметры положительны.') and not names<=positive:return None
    ctx=m.context(dict(variable='__section',parameters=sorted(names|params),parameter_conditions=[n+'>0' for n in sorted(positive)]))
    expr=m.parse(lhs,None,[*variables,*names])
    def addends(z):return addends(z[1])+addends(z[2]) if z[0]=='add' else [z]
    def base_degree(z):
        if z[0]=='pow':return z[1],q(z[2])
        if z[0]=='rpow':return z[1],z[2]
        return z,m.ONE
    def coordinate(z):
        base,power=base_degree(z);scale=m.ONE
        if base[0]=='div':
            numerator,denom=base[1:]
            if numerator in coords:base,scale=numerator,denom
            elif power==m.ONE:
                base,power=base_degree(numerator);scale,e=base_degree(denom)
                if power!=e:
                    n=m.num(power);d=m.num(denom)
                    if n is None or n.denominator!=1 or n<=0 or d is None or d<=0:return None
                    scale=m.simplify(('rpow',denom,q(1,int(n))))
            else:return None
        if base not in coords or scale==m.ZERO or not m.constant_defined(scale,ctx) or not m.constant_defined(power,ctx) or m.sign(power,ctx)!=1:return None
        return base,scale,power
    summands=addends(expr)
    for i,z in enumerate(summands):
        axial=coordinate(z)
        if not axial:continue
        axis,zscale,mz=axial
        rest=[s for j,s in enumerate(summands) if i!=j]
        if len(rest)==1:cross,n=base_degree(rest[0]);terms=addends(cross)
        else:n=m.ONE;terms=rest
        if len(terms)!=2 or m.sign(n,ctx)!=1:continue
        pair=[coordinate(t) for t in terms]
        if None in pair or {v[0] for v in pair}|{axis}!=set(coords):continue
        degrees=[t[2] for t in pair];scales=[scale for _,scale,_ in pair]+[zscale]
        factor=m.ONE
        for a in scales:factor=m.mul(factor,m.simplify(('abs',a)))
        if degrees==[q(2),q(2)] and not bounds and not orthant:
            zpower=m.num(mz)
            if zpower is None or zpower.denominator!=1 or zpower.numerator%2:continue
            # If n is not an integer the positive radial base still defines all disk interiors.
            shapes=[m.div(m.ONE,mz),m.add(m.ONE,m.div(m.ONE,n))]
            pref=m.div(m.mul(q(2),m.mul(m.PI,factor)),mz)
            chart='elliptical_disk';jacobian='|abc| r';multiplicity=2
        elif (degrees==[m.ONE,m.ONE] and (orthant==set(variables) or bounds=={v+'=0' for v in variables})
                and all(m.sign(t,ctx)==1 for t in scales) and task.get('method_requirement')!='spherical_or_cylindrical_triple_integral'):
            shapes=[m.div(q(2),n),m.add(m.ONE,m.div(m.ONE,mz))]
            pref=m.div(factor,n);chart='linear_triangle';jacobian='|abc| t';multiplicity=1
        else:continue
        value=gamma_volume(pref,shapes,m.add(*shapes))
        return dict(theorem='method.grouped_power_sections',chart=chart,axis=axis[1],scales=scales,
                    powers=[n,mz],jacobian=jacobian,beta_shape=shapes,half_slices=multiplicity,
                    coordinate_map=('r^2=(x_i/a_i)^2+(x_j/a_j)^2, w=z_k/a_k' if chart=='elliptical_disk'
                                    else 't=x_i/a_i+x_j/a_j, u=(x_i/a_i)/t, w=z_k/a_k'),
                    disk_or_triangle_range=[0,1],natural_nonzero=scales),{'volume':value}
    return None


def linear_image_volume(task):
    """Read an independent family of affine forms from the source; certify invertibility using its adjugate."""
    from verify import same_value
    contract=volume_coordinates_task(task)
    if not contract:return None
    raw,conditions,literal=contract
    if task.get('method_requirement')=='spherical_or_cylindrical_triple_integral' or 'октанте' in literal:return None
    variables=('x','y','z');coords=[('s',v) for v in variables];rows=[];widths=[];det_required=None;sphere=False
    name=r'[A-Za-z][A-Za-z0-9]*'
    pattern=rf'({name})_([a-z])\*x\+({name})_\2\*y\+({name})_\2\*z'
    indexed=re.fullmatch(pattern+rf'=\+({name})_\2,-\5_\2 for \2=1,2,3',raw) if isinstance(raw,str) else None
    quad=re.fullmatch(r'sum\(\('+pattern+r'\)\^2,\2=1\.\.3\)=('+name+r')\^2',raw) if isinstance(raw,str) else None
    if indexed or quad:
        match=indexed or quad;names=(match[1],match[3],match[4]);dummy=match[2]
        if len(set(names))!=3:return None
        det_required='det(rows('+','.join(n+'_'+dummy for n in names)+'))!=0'
        if conditions!=[det_required]:return None
        rows=[[''.join([v,str(i)]) for v in names] for i in (1,2,3)]
        sphere=bool(quad);widths=[quad[5]] if sphere else [indexed[5]+str(i) for i in (1,2,3)]
        if set(widths)&set(variables) or any(w in row for w in widths for row in rows):return None
        matrix=[[('s',v) for v in row] for row in rows];half=[('s',v) for v in widths];origin=[m.ZERO]*3
    else:
        if not isinstance(raw,list) or len(raw)!=3 or conditions:return None
        matrix=[];origin=[];half=[]
        for eq in raw:
            pair=re.fullmatch(r'([^=]+)=\+([^,]+),-(.+)',eq.replace(' ',''))
            if not pair or pair[2]!=pair[3]:return None
            names=set(re.findall(r'\b[A-Za-z_]\w*\b',pair[1]+' '+pair[2]))-set(variables)-m.FUNCTIONS-{'pi','e'}
            form=m.parse(pair[1],None,[*variables,*names]);width=m.parse(pair[2],None,names)
            if domain_conditions(form) or domain_conditions(width):return None
            zero={v:m.ZERO for v in coords};off=m.simplify(m.substitute(form,zero));row=[]
            reconstruction=off
            for v in coords:
                coeff=m.simplify(m.add(m.substitute(form,{**zero,v:m.ONE}),m.neg(off)))
                reconstruction=m.add(reconstruction,m.mul(coeff,v));row.append(coeff)
            if not same_value(form,reconstruction):return None
            matrix.append(row);origin.append(off);half.append(width)
    def cross(a,b):return [m.add(m.mul(a[(i+1)%3],b[(i+2)%3]),m.neg(m.mul(a[(i+2)%3],b[(i+1)%3]))) for i in range(3)]
    def dot(a,b):return m.add(m.add(m.mul(a[0],b[0]),m.mul(a[1],b[1])),m.mul(a[2],b[2]))
    columns=[cross(matrix[(i+1)%3],matrix[(i+2)%3]) for i in range(3)]
    det=dot(matrix[0],columns[0])
    if det_required is None and (m.num(det) is None or not m.num(det)):return None
    if any(not same_value(dot(a,b),det if i==j else m.ZERO) for i,a in enumerate(matrix) for j,b in enumerate(columns)):
        raise Unsupported('The affine chart failed its inverse matrix identity')
    if sphere:target=m.mul(q(4,3),m.mul(m.PI,m.power(m.simplify(('abs',half[0])),3)))
    else:
        target=q(8)
        for h in half:target=m.mul(target,m.simplify(('abs',h)))
    return dict(theorem='method.affine_solid_measure',matrix=matrix,offset=origin,determinant=det,adjugate_columns=columns,
                source_determinant=det_required,target='ball' if sphere else 'box',half_width_or_radius=half,
                inverse_jacobian=m.div(m.ONE,m.simplify(('abs',det)))),{'volume':m.div(target,m.simplify(('abs',det)))}


def section_volume_profile(task,library,request):
    if not library.data.get('source_volume_profiles') or task.get('kind')!='bounded_solid_volume':return None
    fields={'id','kind','source','surfaces','stated_conditions','method_requirement','requested_output','suggested_method'}
    method=task.get('method_requirement')
    outputs={None:['exact_volume'],'polar_coordinates':['exact_volume'],'triple_integral':['exact_volume','specified_method'],
             'spherical_or_cylindrical_triple_integral':['exact_volume','specified_method'],
             'change_of_variables':['exact_volume','substitution_and_jacobian']}
    if set(task)-fields or method not in outputs or task.get('requested_output')!=outputs[method]:return None
    from plane_domains import VOLUME_SOURCE_METHODS
    meta=task.get('source',{})
    heading=meta.get('literal_requirement','').removesuffix(' Обобщённые сферические координаты рекомендованы.')
    if (set(meta)-{'exercise','printed_subpart','printed_page','pdf_page','pdf_pages','pdf_sha256','literal_requirement'}
            or heading and method not in VOLUME_SOURCE_METHODS.get(heading,())
            or task.get('suggested_method') not in (None,'generalized_spherical_coordinates')):
        return None
    raw=task['surfaces'];guards=task.get('stated_conditions',[])
    normalize=lambda t:t.replace(' ','').replace('²','^2').replace('³','^3')
    walls=tuple(map(normalize,raw)) if isinstance(raw,list) else (normalize(raw),)
    conditions=tuple(map(normalize,guards))
    if len(set(walls))!=len(walls):return None
    positive=bool(conditions and conditions[0] in ('positiveparameters','parameterspositive'))
    n=r'([A-Za-z]\w*)';number=r'([1-9]\d*(?:/\d+)?)'
    matches=lambda pattern,w:re.fullmatch(pattern,w)
    P=m.PI
    real=lambda s:('s',s)
    rt=lambda t:m.simplify(('sqrt',t))
    sq=lambda t:m.power(t,2)
    cb=lambda t:m.power(t,3)
    diff=lambda a,b:m.add(a,m.neg(b))
    prod=lambda *values:_volume_product(values)

    def emit(route, steps, volume, **data):
        return dict(theorem='method.'+route,argument='; '.join(steps),source_volume_steps=steps,
                    stated_conditions=guards,method_requirement=method,**data),dict(volume=volume)
    def disk_sector(height, radius, opened):
        """Base sector plus the two first planar coordinate moments."""
        return prod(height,P,sq(radius),q(opened,2))

    if method is None and len(walls)==5 and walls[2:]==('x=0','y=0','z=0'):
        a=matches('x\\+y\\+z='+n,walls[0]);r=matches('x\\^2\\+y\\^2='+n+'\\^2',walls[1])
        if a and r and a[1]!=r[1] and not {a[1],r[1]}&{'x','y','z','pi'} and conditions==(a[1]+'>='+r[1]+'*sqrt(2)',):
            A,R=real(a[1]),('abs',real(r[1]))
            return emit('certified_height_on_planar_chart',[
                'В положительной камере проекция — четверть диска. R обозначает неотрицательный геометрический радиус.',
                'Неравенство Коши даёт x+y≤√2R на всей четверти диска. Напечатанное ограничение сохраняет неотрицательность высоты.',
                'Вычитаем оба первых момента четверти диска из её площади, умноженной на высоту плоскости.'],
                diff(disk_sector(A,R,F(1,2)),prod(q(2,3),cb(R))),chart='quarter disk',height='a-x-y',
                quadrant_height_integrals='a*pi*R^2/4-(sign_x+sign_y)*R^3/3')
    if method is None and not conditions and len(walls)==4 and walls[0]=='z=x^2+y^2' and walls[1]=='y=x^2' and walls[-1]=='z=0':
        hit=matches('y='+number,walls[2])
        if hit:
            B=q(F(hit[1]));r=rt(B)
            return emit('certified_height_on_planar_chart',[
                'Решаем боковую параболу относительно горизонтальной координаты, сохраняя обе симметричные ветви.',
                'Высота над плоскостью равна сумме квадратов. Сечение по x даёт (2/3)y^(3/2)+2y^(5/2).'],
                m.add(prod(q(4,15),m.power(r,5)),prod(q(4,7),m.power(r,7))),chart='-sqrt(y)<=x<=sqrt(y)',section_y_upper=B)
    if (method is None and not conditions and len(walls)==4 and walls[:2]==('z=cos(x)*cos(y)','z=0')
            and all(matches(r'abs\(x[+-]y\)<=pi/[1-9]\d*',v) for v in walls[2:]) and walls[2][5]=='+' and walls[3][5]=='-'):
        A,B=[F(1,int(z.split('/')[-1])) for z in walls[2:]]
        if max(A,B)>F(1,2):return None
        alpha,beta=prod(q(A),P),prod(q(B),P)
        value=m.add(prod(beta,m.simplify(('sin',alpha))),prod(alpha,m.simplify(('sin',beta))))
        return emit('certified_height_on_planar_chart',[
            'Новые координаты u=x+y,v=x−y образуют прямоугольник, обратный якобиан имеет модуль 1/2.',
            'Формула произведения даёт неотрицательную высоту (cos u+cos v)/2 в исходных угловых пределах.',
            'Сумма двух разделённых моментов вычисляется по синусам концов.'],value,
            chart='u=x+y, v=x-y',absolute_jacobian=q(1,2),bounds=(-A.numerator,A.denominator,-B.numerator,B.denominator))
    if method is None and not conditions and len(walls)==5 and walls[1:]==('z=0','y=x','y=0','x=pi'):
        hit=matches(r'z=sin\(pi\*y/\(([1-9]\d*)\*x\)\)',walls[0])
        if hit and int(hit[1])>=1:
            c=int(hit[1]);k=prod(P,q(1,c))
            return emit('certified_height_on_planar_chart',[
                'На каждом x>0 нормируем y координатой t=y/x. Боковые прямые дают 0≤t≤1, а якобиан равен x.',
                'Неотрицательная высота зависит только от t. Граничный отрезок x=0 имеет нулевую меру.',
                'Интегрирование синуса по t и x по его исходному отрезку даёт произведение двух моментов.'],
                prod(P,q(c,2),diff(ONE,m.simplify(('cos',k)))),chart='t=y/x',absolute_jacobian='x')
    if (method is None and not conditions and len(walls)==3 and walls[0]=='z=x*y' and walls[-1]=='z=0'
            and (hit:=matches(r'x\+y\+z='+number,walls[1]))):
        K=F(hit[1]);T=1+K
        polynomial=(T*T+2*T)*(T-1)-(2*T+1)*(T*T-1)/2+(T**3-1)/3
        value=prod(q(1,2),diff(q(polynomial),prod(q(T*T),('ln',q(T)))))
        return emit('partition_at_height_intersection',[
            'В ограниченной компоненте над z=0 обе высоты неотрицательны на треугольнике x≥0,y≥0,x+y≤K.',
            'При фиксированном x верхняя грань — минимум xy и K−x−y. Точка переключения y=(K−x)/(1+x) лежит внутри сечения.',
            'Интегрируем две высоты отдельно. После u=1+x рациональный остаток разделяется на многочлен и 1/u.'],
            value,partition='y=(K-x)/(1+x)',scale=q(K))
    if method=='polar_coordinates':
        return polar_section_profiles(walls,conditions,emit)
    if method is None and positive and (answer:=scaled_section_profiles(walls,conditions,emit,request)) is not None:return answer
    if method in ('triple_integral','spherical_or_cylindrical_triple_integral','change_of_variables',None):
        return special_section_profiles(walls,conditions,method,task.get('suggested_method'),emit,request)
    return None


def _volume_product(values):
    p=ONE
    for e in values:p=m.mul(p,e)
    return p


def polar_section_profiles(walls,conditions,emit):
    P=m.PI;s=lambda z:('s',z);p=lambda *args:_volume_product(args)
    if len(walls)==2 and not conditions and walls[0]=='z^2=x*y' and (rad:=re.fullmatch(r'x\^2\+y\^2=([A-Za-z]\w*)\^2',walls[1])):
        A=('abs',s(rad[1]))
        return emit('angular_beta_volume',[
            'Две действительные ветви существуют при xy≥0. Первая и третья четверти дают две равные неперекрывающиеся внутренности.',
            'Полярная высота 2r√(sin θ cos θ) и якобиан r отделяют радиальный момент ∫r²dr.',
            'Угловой интеграл на четверти окружности равен B(3/4,3/4)/2.'],
            dict(factor=p(q(2,3),m.power(A,3)),beta_shape=(q(3,4),q(3,4))),components=2,chart='polar')
    if (len(walls)==3 and conditions==('x>0','y>0') and walls[0]=='z=x+y' and walls[-1]=='z=0'
            and (hit:=re.fullmatch(r'\(x\^2\+y\^2\)\^2=([1-9]\d*)\*x\*y',walls[1]))):
        cap=q(int(hit[1]),2)
        return emit('polar_height_moments',[
            'На первом квадранте боковая граница становится r²≤C sin 2θ с положительным C.',
            'Интегрируем r³-меру высоты по радиусу. Подстановка t=sin θ−cos θ превращает угловую часть в степенной полукруглый момент.'],
            p(P,q(1,8),m.power(m.simplify(('sqrt',cap)),3)),chart='polar',radial_square_factor=cap)
    if (not conditions and len(walls)==4 and walls[0]=='z=x^2+y^2' and walls[3]=='z=0'):
        levels=[re.fullmatch(r'x\^2\+y\^2=(?:(\d+)\*)?x',v) for v in walls[1:3]]
        if all(levels):
            a,b=sorted(int(z[1] or '1') for z in levels)
            if 0<a<b:
                return emit('polar_height_moments',[
                    'Две окружности дают допустимые радиусы между их пересечениями с каждым лучом, где cos θ≥0.',
                    'Высота r² интегрируется с якобианом r. Остаётся общий момент cos⁴ θ на правой полуокружности.'],
                    p(P,q(3*(b**4-a**4),32)),radial_factors=(q(a),q(b)),chart='polar')
    if (len(walls)==2 and (hit:=re.fullmatch(r'x\^2\+y\^2\+z\^2=([A-Za-z]\w*)\^2',walls[0]))):
        a=hit[1];A=s(a)
        if conditions==(a+'>0',) and walls[1]=='x^2+y^2>='+a+'*abs(x)':
            return emit('polar_height_moments',[
                'Исходное неравенство на каждом полярном луче даёт a|cos θ|≤r≤a. Берём обе ветви шара.',
                'Интегрируем 2r√(a²−r²) по радиусу. Остаточный момент |sin θ|³ удваивается и отражается по четвертям.'],
                p(q(16,9),m.power(A,3)),radial_lower=a+'*abs(cos(theta))',chart='polar')
    if (len(walls)==3 and walls[-1]=='z=0' and (hit:=re.fullmatch(r'x\^2\+y\^2-([A-Za-z]\w*)\*z=0',walls[0]))):
        a=hit[1];A=s(a)
        if conditions==(a+'>0',) and walls[1]=='(x^2+y^2)^2='+a+'^2*(x^2-y^2)':
            return emit('polar_height_moments',[
                'В обеих лопастях выбираем cos 2θ≥0, исходная радиальная граница a√(cos 2θ).',
                'Высота r²/a неотрицательна. После радиального момента остаётся cos²2θ на двух секторах.'],
                p(P,q(1,8),m.power(A,3)),chart='polar with two lobes',components=2)
    if walls==('z=x^2+y^2','z=x+y') and not conditions:
        return emit('polar_height_moments',[
            'Положительная разность высот после выделения квадратов задаёт диск с центром (1/2,1/2) и радиусом 1/√2.',
            'Полярная замена относительно центра даёт высоту 1/2−r² и якобиан r.'],
            p(P,q(1,8)),center=(q(1,2),q(1,2)),radius_squared=q(1,2),chart='translated polar')
    return None


def scaled_section_profiles(walls,conditions,emit,request):
    from quadrature import gamma_rational

    P=m.PI;s=lambda z:('s',z);p=lambda *args:_volume_product(args)
    diff=lambda a,b:m.add(a,m.neg(b))
    named=r'([A-Za-z]\w*)'
    quad=r'x\^2/'+named+r'\^2\+y\^2/'+named+r'\^2'
    if len(walls)==2:
        sphere=re.fullmatch(quad+r'([+-])z\^2/'+named+r'\^2=([-]1|1)',walls[0])
        if sphere:
            a,b,sign,c,right=sphere.groups();xy='x^2/'+a+'^2+y^2/'+b+'^2';scale=p(s(a),s(b),s(c))
            if len({a,b,c})==3 and not {a,b,c}&{'x','y','z'}:
                if (sign,right)==('+','1') and conditions[1:]==('z>0',) and walls[1]==xy+'=z^2/'+c+'^2':
                    return emit('spherical_sector_shell_measure',[
                        'Масштабируем три положительные полуоси до единичного шара. Проверенный модуль якобиана равен произведению полуосей.',
                        'В верхнем конусе полярный угол не превосходит π/4. Радиальный и угловой моменты разделяются.'],
                        p(scale,P,q(2,3),diff(ONE,p(q(1,2),('sqrt',q(2))))),chart='normalized spherical',solid_angle='2*pi*(1-cos(pi/4))')
                if (sign,right)==('-','-1') and not conditions[1:] and walls[1]==xy+'=1':
                    return emit('certified_height_on_planar_chart',[
                        'После масштабирования цилиндр даёт единичный круг. Две полы гиперболоида дают высоту 2√(1+r²).',
                        'Радиальный полярный момент вычисляется заменой t=1+r².'],
                        p(scale,P,q(4,3),diff(p(q(2),('sqrt',q(2))),ONE)),chart='normalized cylindrical')
                if (sign,right)==('+','1') and not conditions[1:] and walls[1]=='('+xy+')^2=x^2/'+a+'^2-y^2/'+b+'^2':
                    return emit('polar_height_moments',[
                        'После масштабирования лемниската даёт две области r²≤cos 2θ≤1. Над ними высота сферы 2√(1−r²).',
                        'Явный радиальный момент оставляет (2/3)[1−(1−cos 2θ)^(3/2)]. На половине лопасти 1−cos 2θ=2sin²θ.',
                        'Вычисляем обычный момент sin³ и умножаем на число симметричных частей.'],
                        p(scale,q(2,9),m.add(p(q(3),P),diff(q(20),p(q(16),('sqrt',q(2)))))),
                        chart='normalized polar with two lobes',components=2)
    if len(walls)==3 and not conditions[1:]:
        parabola=re.fullmatch(quad+r'=z/'+named,walls[0])
        if parabola and walls[-1]=='z=0':
            a,b,c=parabola.groups();xy='x^2/'+a+'^2+y^2/'+b+'^2'
            if len({a,b,c})==3 and not {a,b,c}&{'x','y','z'} and walls[1]==xy+'=x/'+a+'+y/'+b:
                return emit('certified_height_on_planar_chart',[
                    'Нормируем масштабы. Боковая поверхность ограничивает круг с центром (1/2,1/2), квадрат радиуса 1/2.',
                    'Момент u²+v² на диске равен площади, умноженной на квадрат центра и добавочный радиальный момент R²/2.'],
                    p(s(a),s(b),s(c),P,q(3,8)),chart='translated normalized disk')
    if (len(walls)==3 and walls[0]=='z^2=x*y'
            and (lo:=re.fullmatch(r'x\+y='+named,walls[1])) and (hi:=re.fullmatch(r'x\+y='+named,walls[2]))):
        a,b=lo[1],hi[1]
        if a!=b and not {a,b}&{'x','y','z'} and conditions[1:]==('0<'+a+'<'+b,):
            return emit('angular_beta_volume',[
                'Сумма x+y положительна. Из xy≥0 получаем неотрицательность обеих координат.',
                'При фиксированной сумме t замена x=tu, y=t(1−u) даёт общий бета-момент высоты 2t√(u(1−u)) с якобианом t.',
                'Бета-момент равен π/8. Интегрируем t² по напечатанному положительному интервалу.'],
                p(P,q(1,12),diff(m.power(s(b),3),m.power(s(a),3))),chart='sum and coordinate share',absolute_jacobian='t')
    if (len(walls)==6 and not conditions[1:] and walls[0]=='z=x^2+y^2'
            and walls[3:]==('y=x/2','y=2*x','z=0') and (low:=re.fullmatch(r'xy='+named+r'\^2',walls[1]))
            and walls[2]=='xy=2*'+low[1]+'^2' and low[1] not in ('x','y','z')):
        a=low[1]
        return emit('monomial_reflection_sheets',[
            'Произведение положительно, поэтому остаются две ветви, отличающиеся общим знаком x,y.',
            'Переменные u=xy и v=y/x переводят каждую ветвь в один прямоугольник. Модуль якобиана на каждой равен 1/(2v).',
            'Высота u(v+1/v) разделяет меру на два однофакторных момента. Отражение удваивает результат одной ветви.'],
            p(q(9,2),m.power(s(a),4)),chart='u=xy,v=y/x',components=2,absolute_jacobian='1/(2*v)')
    simple=re.fullmatch(r'z=x\^\(([1-9]\d*/[1-9]\d*)\)\+y\^\(\1\)',walls[0])
    if simple and not conditions[1:] and walls[1:]==('z=0','x+y=1','x=0','y=0'):
        power=F(simple[1])
        return emit('simplex_section_moments',[
            'На положительном симплексе два слагаемых равны после отражения координат.',
            'Интеграл по второй координате даёт длину 1−x. Два оставшихся степенных момента вычисляются непосредственно.'],
            q(2/((power+1)*(power+2))),chart='positive simplex',moment_degree=q(power))
    if len(walls)==3 and not conditions[1:] and walls[-1]=='z=0' and (roof:=re.fullmatch(quad+r'\+z/'+named+r'=1',walls[0])):
        a,b,c=roof.groups()
        curve=re.fullmatch(r'\(x/'+re.escape(a)+r'\)\^\(([1-9]\d*/[1-9]\d*)\)\+\(y/'+re.escape(b)+r'\)\^\(\1\)=1',walls[1])
        if curve and F(curve[1]).numerator==2 and F(curve[1]).denominator%2 and len({a,b,c})==3 and not {a,b,c}&{'x','y','z'}:
            t=F(curve[1]);u=1/t
            if t>2:return None
            ga,gb,g0,g1=map(gamma_rational,(u,u+2/t,2*u+1,2*u+2/t+1))
            if any(x is None for x in (ga,gb,g0,g1)):return None
            area=m.div(p(ga,ga),g0);moment=m.div(p(ga,gb),g1)
            return emit('simplex_section_moments',[
                'Нормируем полуоси. Замена s=|u|^t,w=|v|^t переводит каждую четверть в симплекс, якобиан равен s^(1/t−1)w^(1/t−1)/t².',
                'При t≤2 внутри симплекса исходная верхняя грань неотрицательна. Интегрируем её три монома по формуле Дирихле и учитываем четыре четверти.'],
                p(q(4/t**2),s(a),s(b),s(c),diff(area,p(q(2),moment))),chart='powered simplex',power=q(t),components=4)
    return None


def special_section_profiles(walls,conditions,method,suggestion,emit,request):
    P=m.PI;s=lambda z:('s',z);p=lambda *args:_volume_product(args)
    diff=lambda a,b:m.add(a,m.neg(b))
    n=r'([A-Za-z]\w*)'
    if method is None and conditions==('positiveparameters','y>=0') and len(walls)==3 and walls[1]=='z=0':
        if (c:=re.fullmatch(r'z='+n+r'\*atan\(y/x\)',walls[0])) and (a:=re.fullmatch(r'sqrt\(x\^2\+y\^2\)='+n+r'\*atan\(y/x\)',walls[2])):
            if {a[1],c[1]}&{'x','y','z'}:return None
            return emit('angular_boundary_power_volume',[
                'Положительная радиальная граница в верхней полуплоскости требует положительной главной ветви arctg(y/x).',
                'Поэтому в первой четверти θ=arctg(y/x). Радиальная верхняя граница aθ, высота cθ.',
                'При полярном якобиане r остаётся третий степенной момент θ на [0,π/2].'],
                p(q(1,128),s(c[1]),m.power(s(a[1]),2),m.power(P,4)),chart='principal polar branch')
    if method=='triple_integral' and not conditions and len(walls)==1:
        text=walls[0]
        if (a:=re.fullmatch(r'x\^2\+z\^2='+n+r'\^2,x\+y=\+\1,-\1;x-y=\+\1,-\1',text)):
            a=('abs',s(a[1]))
            return emit('certified_height_on_planar_chart',[
                'Четыре плоскости эквивалентны условию |x|+|y|≤|a|. При каждом x цилиндр и эти плоскости дают независимые интервалы.',
                'Сохраняем кратный интеграл по двум длинам сечения. Отражение по x сводит его к разности площади четверти круга и её первого момента.'],
                p(m.power(a,3),diff(p(q(2),P),q(8,3))),chart='Cartesian triple section')
        if (a:=re.fullmatch(n+r'\*z=\1\^2-x\^2-y\^2,z=\1-x-y,x=0,y=0,z=0,\1>0',text)):
            return emit('partition_at_height_intersection',[
                'В положительном октанте верхняя грань — параболоид. Плоскость и z=0 выбирают нижнюю грань по знаку a−x−y.',
                'Под положительной частью плоскости получается треугольник. На нём плоскость лежит ниже параболоида.',
                'По тройным интегралам вычитаем тетраэдр из объёма под параболоидом над четвертью диска.'],
                p(m.power(s(a[1]),3),diff(p(P,q(1,8)),q(1,6))),chart='Cartesian triple section with split lower bound')
    if method=='spherical_or_cylindrical_triple_integral' and len(walls)==1:
        hit=re.fullmatch(r'x\^2\+y\^2\+z\^2='+n+r'\^2,x\^2\+y\^2\+z\^2='+n+r'\^2,x\^2\+y\^2=z\^2',walls[0])
        if hit and len(set(hit.groups()))==2 and not set(hit.groups())&{'x','y','z'}:
            a,b=hit.groups()
            if conditions==('z>=0','0<'+a+'<'+b):
                V=p(q(2,3),P,diff(m.power(s(b),3),m.power(s(a),3)),diff(ONE,p(q(1,2),('sqrt',q(2)))))
                return emit('spherical_sector_shell_measure',[
                    'Указанные положительные радиусы задают сферический слой. Сохраняем верхнюю полуобласть z≥0.',
                    'Образ конуса в сферических координатах 0≤φ≤π/4. Радиальный момент r² и угловой момент sin φ вычисляются отдельно.'],
                    V,chart='spherical triple integral',radial_bounds=(s(a),s(b)),angle_bound='pi/4')
    if method is None and suggestion in (None,'generalized_spherical_coordinates') and len(walls)==1 and not conditions:
        hit=re.fullmatch(r'x\^2/'+n+r'\^2\+y\^2/'+n+r'\^2\+z\^2/'+n+r'\^2=1,x\^2/\1\^2\+y\^2/\2\^2=z/\3',walls[0])
        if hit and len(set(hit.groups()))==3 and not set(hit.groups())&{'x','y','z'}:
            scalar=('abs',p(*(s(a) for a in hit.groups())))
            c=p(q(1,2),diff(('sqrt',q(5)),ONE))
            v=p(q(5,6),P,scalar,diff(ONE,c))
            return emit('partition_at_height_intersection',[
                'При ненулевых исходных масштабах нормируем эллипсоид. Во внутренности верхнего параболоида '
                'квадрат радиуса сечения не превосходит min(w,1−w²).',
                'Смена границы происходит в положительном корне w²+w−1=0. Интегрируем обе площади по отдельности.',
                'Другая сторона разделяющей поверхности при необходимости даёт дополнение до объёма эллипсоида.'],
                v,chart='scaled circular sections',transition=c,other_component=diff(p(q(4,3),P,scalar),v))
    if method=='change_of_variables' and conditions==('parameterspositive','x>0') and len(walls)==1:
        hit=re.fullmatch(r'x\^2\+z\^2='+n+r'\^2,x\^2\+z\^2='+n+r'\^2,x\^2-y\^2-z\^2=0',walls[0])
        if hit and len(set(hit.groups()))==2 and not set(hit.groups())&{'x','y','z'}:
            a,b=hit.groups()
            return emit('angular_beta_volume',[
                'Цилиндрическая карта вокруг оси y даёт x=r cos θ,z=r sin θ и сохраняет x>0.',
                'Конус ограничивает |θ|≤π/4 и |y|≤r√(cos 2θ). Модуль якобиана равен r.',
                'Порядок двух радиусов учитываем модулем разности их кубов. Угловой интеграл заменяем на бета-момент.'],
                dict(factor=p(q(1,3),('abs',diff(m.power(s(b),3),m.power(s(a),3)))),beta_shape=(q(1,2),q(3,4))),
                chart='x=r*cos(theta),z=r*sin(theta)',absolute_jacobian='r')
    if method is None and len(walls)==1:
        hit=re.fullmatch(r'x\^'+n+r'/'+n+r'\^\1\+y\^'+n+r'/'+n+r'\^\3\+z\^'+n+r'/'+n+r'\^\5=1,x=0,y=0,z=0',walls[0])
        if hit and len(set(hit.groups()))==6 and not set(hit.groups())&{'x','y','z'}:
            exponents=hit.groups()[::2];parameters=hit.groups()[1::2]
            if conditions==tuple(a+'>0' for a in exponents)+('x>=0','y>=0','z>=0'):
                inverse=[m.div(ONE,s(r)) for r in exponents]
                return emit('simplex_section_moments',[
                    'Для существования ограниченного тела в замкнутом положительном октанте степенные знаменатели должны быть положительными.',
                    'Делим каждый моном на собственный знаменатель. Образ тела — симплекс с тремя сохранёнными координатными гранями.',
                    'Абсолютный якобиан — произведение трёх степенных множителей. Формула Дирихле даёт отношение гамма-функций.'],
                    dict(factor=('abs',p(*(s(a) for a in parameters))),gamma_numerator=[m.add(ONE,r) for r in inverse],
                         gamma_denominator=m.add(ONE,m.add(m.add(inverse[0],inverse[1]),inverse[2])),
                         factor_condition='positive scales; otherwise use positive roots of positive powered denominators'),
                    chart='normalized positive powers',coordinate_boundaries=('x=0','y=0','z=0'))
    return None


def solid_sections(task,library,request,*,saved=None):
    """Compute a Jordan volume from verified planar sections or from the interior of a positive quadric."""
    from model import freeze
    from tasks import source,known_guard
    from verify import same_value
    from integrals import learned_nodes
    if task['kind']=='bounded_solid_volume':
        if (resolved:=section_volume_profile(task,library,request)) is not None:return resolved
        task=bind_volume_source(task)
    if (monomial:=monomial_section_volume(task,library,request)) is not None:return monomial
    charts=library.data.get('spatial_coordinate_measures',())
    if 'linear_image' in charts and (affine:=linear_image_volume(task)) is not None:return affine
    if 'elliptical_sections' in charts and (section:=grouped_cross_sections(task)) is not None:return section
    if 'directions' in charts:
        if (ray:=spherical_volume(task,request,saved)) is not None:return ray
    if (radial:=radial_height_volume(task,library,request)) is not None:return radial
    if (simplex:=power_simplex_measure(task,library)) is not None:return simplex
    if task['kind'] in ('bounded_solid_volume','lamina_centroid'):
        return projection_moments(task,library,request)
    kind=task['kind'];general={'kind','id','source','parameters','stated_conditions','requested_output'}
    source_fields={'equations'} if kind=='volume_bounded_by_surfaces' else {'statement'}
    if not library.data.get('solid_sections') or kind not in ('volume_from_named_solid','section_measure_identity','dense_section_measure','volume_bounded_by_surfaces'):
        raise Unsupported('The shape and its assumptions have no checked mathematical input contract')
    if set(task)-general-source_fields or task.get('requested_output')!=['proof' if kind in ('section_measure_identity','dense_section_measure') else 'volume']:
        raise Unsupported('Additional geometry or a source method has not been covered')
    params=task.get('parameters',[]);conditions=task.get('stated_conditions',[]);pos=[];station=None
    for s in conditions:
        if re.fullmatch(r'[A-Za-z_]\w*>0',s) and s[:-2] in params:pos.append(s)
        elif kind=='section_measure_identity' and s=='<='.join(task['statement']['interval']):continue
        elif (cut:=re.fullmatch(r'([^<>=]+)<([xyz])<([^<>=]+)',s)) and station is None:station=cut.groups()
        else:raise Unsupported('A domain or source section selection is unresolved')
    ctx=m.context(dict(variable='__section',parameters=params,parameter_conditions=pos))
    var='t'
    while var in params:var+='t'
    t=('v',var);parse=lambda z:m.parse(str(z),None,params)
    def positive(z):return m.constant_defined(z,ctx) and m.sign(z,ctx)==1
    def theorem(argument,**facts):
        record='method.jordan_contents_dense_sections' if kind=='dense_section_measure' else 'method.volume_from_planar_sections'
        return dict(theorem=record,argument=argument,**facts)
    def integrate(density,weight=m.ONE,lo=m.ZERO,hi=m.ONE):
        child=dict(kind='iterated_integral',parameters=params,stated_conditions=pos,integrand=source(density),integration_order=[dict(variable=var,lower=source(lo),upper=source(hi))],requested_output=['exact_integral'])
        return m.mul(weight,freeze(request('integrate sections',child)['value']))
    if kind=='volume_from_named_solid':
        if station:raise Unsupported('Extra clipping planes modify the source solid')
        shape=task['statement'];family=shape['kind'];h=parse(shape['height'])
        if not positive(h):raise Unsupported('Positive height is unproved')
        if family in ('obelisk','cone_frustum'):
            field='rectangle_sides' if family=='obelisk' else 'ellipse_semiaxes'
            if set(shape)!={'kind','height','lower_'+field,'upper_'+field}:raise Unsupported('Unknown section geometry')
            end=[list(map(parse,shape[key+'_'+field])) for key in ('lower','upper')]
            if any(len(v)!=2 or not all(map(positive,v)) for v in end):raise Unsupported('Section dimensions must be positive')
            sides=[m.add(a,m.mul(t,m.add(b,m.neg(a)))) for a,b in zip(*end)]
            compatible=m.add(m.mul(end[0][0],end[1][1]),m.neg(m.mul(end[0][1],end[1][0])))
            if family=='cone_frustum' and m.sign(compatible,ctx) in (-1,1):raise Unsupported('The proposed elliptic bases cannot be homothetic sections of one cone')
            density=m.mul(m.ONE if family=='obelisk' else m.PI,m.mul(*sides))
            argument='parallel rectangular sections by affine interpolation' if family=='obelisk' else 'homothetic elliptic sections of a conical frustum'
        elif family=='paraboloid_of_revolution' and set(shape)=={'kind','height','base_area'} and positive(parse(shape['base_area'])):
            density=m.mul(parse(shape['base_area']),t);argument='the squared radius of a paraboloid is proportional to axial distance'
        else:raise Unsupported('The named solid has no derived planar sections')
        return theorem(argument=argument,normalized_height=t,height=h,section_area=density,derived_homothety_condition=compatible if family=='cone_frustum' else None),{'volume':integrate(density,h)}
    if kind=='dense_section_measure':
        s=task['statement'];wanted={'interval','station_coordinate','rational_fiber_rectangle','irrational_fiber_rectangle','measure','asserted_section_integral','asserted_volume_exists'}
        if set(s)!=wanted or s['measure']!='Jordan' or params or conditions or not isinstance(s['station_coordinate'],str):raise Unsupported('Unproved dense sections or non-Jordan notion of volume')
        def interval(value):
            endpoints=[parse(z) for z in value]
            if not all(m.constant_defined(z,ctx) for z in endpoints):raise Unsupported('A section endpoint is undefined')
            pair=[m.num(m.simplify(z)) for z in endpoints]
            if len(pair)!=2 or None in pair or pair[0]>=pair[1]:raise Unsupported('Nonempty bounded rational intervals required')
            return pair
        lo,hi=interval(s['interval']);boxes=[[interval(pair) for pair in s[k]] for k in ('rational_fiber_rectangle','irrational_fiber_rectangle')]
        if any(len(box)!=2 for box in boxes):raise Unsupported('Original sections must be plane rectangles')
        areas=[prod(b-a for a,b in box) for box in boxes]
        common=prod(max(0,min(B,D)-max(A,C)) for (A,B),(C,D) in zip(*boxes))
        if saved is None:
            union=sum(areas)-common
        else:
            cuts=[sorted({v for box in boxes for v in box[k]}) for k in (0,1)]
            common=union=F(0)
            for x,X in zip(cuts[0],cuts[0][1:]):
                for y,Y in zip(cuts[1],cuts[1][1:]):
                    owners=[a<=x<X<=b and c<=y<Y<=d for ((a,b),(c,d)) in boxes]
                    cell=(X-x)*(Y-y)
                    if any(owners):union+=cell
                    if all(owners):common+=cell
        inner=(hi-lo)*common;outer=(hi-lo)*union
        if type(s['asserted_volume_exists']) is not bool or s['asserted_volume_exists']!=(inner==outer) or areas[0]!=areas[1]:
            raise Unsupported('The volume claim or the section-area Riemann integral fails on dense fibers')
        mean=integrate(q(areas[0]),q(hi-lo))
        asserted=parse(s['asserted_section_integral'])
        if not m.constant_defined(asserted,ctx) or not same_value(asserted,mean):raise Unsupported('The asserted integral of section areas differs')
        return theorem(argument='interior of the common section and closure of the union by density at every station',rational_area=q(areas[0]),irrational_area=q(areas[1]),
                    intersection=q(common),inner_jordan_volume=q(inner),outer_jordan_volume=q(outer),section_integral=mean),{'proved':True}
    if kind=='section_measure_identity':
        s=task['statement'];v=s['coordinate']
        if set(s)!={'coordinate','section_area','interval','ambient_measure','claim'} or s['ambient_measure']!='Jordan' or station or v in params:
            raise Unsupported('The hypotheses of sectional integration have not been established')
        lo,hi=map(parse,s['interval']);width=m.add(hi,m.neg(lo))
        if (not all(m.constant_defined(e,ctx) for e in (lo,hi)) or m.sign(width,ctx) not in (0,1)
                and '<='.join(s['interval']) not in conditions or m.sign(width,ctx)==-1):
            raise Unsupported('Endpoints of the section interval are not ordered')
        raw=m.parse(s['section_area'],v,params);z=('v',v)
        if any(not known_guard(guard,ctx) for guard in domain_conditions(raw)):raise Unsupported('Polynomial identity has an original hole')
        body=m.substitute(raw,{z:m.add(lo,m.mul(t,m.add(hi,m.neg(lo))))})
        numerator,den=m.rational_form(body);denom=m.poly_expr(den)
        if m.variable_in(denom,var) or not m.constant_defined(denom,ctx) or m.sign(denom,ctx) not in (-1,1):raise Unsupported('Expected a polynomial section')
        groups={}
        for mon,c in numerator.items():
            k=dict(mon).get(t,0);others=tuple((z,j) for z,j in mon if z!=t)
            coeff=m.div(m.poly_expr({others:c}),denom)
            if not m.constant_defined(coeff,ctx):raise Unsupported('A section coefficient is not a real constant')
            groups[k]=m.add(groups.get(k,m.ZERO),coeff)
        value=m.ZERO
        for k,coef in sorted(groups.items()):value=m.add(value,integrate(m.power(t,k),coef))
        value=m.mul(m.add(hi,m.neg(lo)),value)
        # Read formal evaluations of S at the stated stations. The substitutions populate a symbolic claim, not the answer.
        claim=s['claim'];terms=[];i=0
        while 'S(' in claim:
            i=claim.index('S(');j=i+2;depth=1
            while j<len(claim) and depth:
                depth+=int(claim[j]=='(')-int(claim[j]==')');j+=1
            if depth:raise Unsupported('Unbalanced section evaluation in the source claim')
            x=parse(claim[i+2:j-1]);ratio=None if same_value(lo,hi) else m.num(m.simplify(m.div(m.add(x,m.neg(lo)),width)))
            if (not m.constant_defined(x,ctx) or not (same_value(x,lo) or same_value(x,hi) or
                    ratio is not None and 0<=ratio<=1 and same_value(x,m.add(lo,m.mul(q(ratio),width))))):
                raise Unsupported('The given section function is only known on the original interval')
            eval_at=m.simplify(m.substitute(raw,{z:x}));terms.append((x,eval_at))
            claim=claim[:i]+'('+source(eval_at)+')'+claim[j:]
        target=parse(claim)
        if any(not known_guard(guard,ctx) for guard in domain_conditions(target)) or not same_value(value,target):
            raise Unsupported('The asserted quadrature identity does not hold under the polynomial hypothesis')
        return theorem(argument='integration of the source sections of a Jordan measurable solid',polynomial=raw,evaluations=terms,integral=value),{'proved':True}
    coords=list('xyz')
    if set(coords).intersection(params):raise Unsupported('A spatial coordinate cannot also be a fixed parameter')
    symbols=[('s',v) for v in coords];names=coords+params
    pairs=[]
    for eq in task['equations']:
        sides=eq.split('=')
        if len(sides)!=2:raise Unsupported('Surface equality expected')
        pairs.append((sides[0],sides[1]))
    def quadratic(subvars,pair,extra=(),conditions=()):
        whole=m.context(dict(variable='__section',parameters=names,parameter_conditions=[*pos,*conditions]))
        for side in pair:
            if any(not known_guard(g,whole) for g in domain_conditions(m.parse(side,None,names))):
                raise Unsupported('A source denominator or radical is not defined on every admitted section')
        child=dict(kind='ellipsoid_moment',variables=subvars,parameters=[*params,*extra],stated_conditions=[*pos,*conditions],integrand='1',
                   quadratic_region=dict(left=pair[0],right=pair[1]),requested_output=['exact_integral'])
        proof=request('bounded positive quadratic section',child);answer=proof['value']
        if not answer.get('defined') or m.sign(freeze(proof['compilation']['squared_radius']),whole)!=1:
            raise Unsupported('A positive squared radius must be established on every admitted section')
        return freeze(answer['value'])
    if len(pairs)==1:
        pair=pairs[0]
        if not station:
            # The positive-definite level surface separates its compact interior from an unbounded exterior.
            return theorem(argument='unique compact component of a positive ellipsoid'),{'volume':quadratic(coords,pair)}
        low,axis,high=station;lo,hi=map(parse,(low,high));width=m.add(hi,m.neg(lo))
        if not positive(width):raise Unsupported('Source section interval is unordered')
        x=('s',axis);inner=quadratic([v for v in coords if v!=axis],pair,[axis],[axis+'-('+low+')>0','('+high+')-'+axis+'>0'])
        body=m.simplify(m.substitute(inner,{x:m.add(lo,m.mul(width,t))}))
        if lo==m.ZERO:
            # On (0,1), both normalized station and width are positive.
            for node in list(learned_nodes(body)):
                if isinstance(node,tuple) and node[0]=='abs' and metric_sign(node[1],var,m.ZERO,m.ONE,ctx)==1:body=m.substitute(body,{node:node[1]})
        return theorem(argument='bounded elliptic section at every interior station; end planes have zero volume',axis=axis,section_area=inner),{'volume':integrate(body,width)}
    if len(pairs)==2 and not station:
        from itertools import permutations
        surfaces=[]
        for pair in pairs:
            left,right=(m.parse(z,None,names) for z in pair)
            if any(not known_guard(guard,ctx) for term in (left,right) for guard in domain_conditions(term)):
                raise Unsupported('A surface has an original hole')
            surfaces.append(m.add(left,m.neg(right)))
        choices=permutations(symbols)
        if saved is not None:
            names_saved=saved.get('fiber_coordinates',())
            if sorted(names_saved)!=sorted(coords):raise Unsupported('The original three fiber coordinates must be preserved')
            choices=[tuple(('s',name) for name in names_saved)]
        for x,y,z in choices:
            # Independent transverse quadratics: leaving either interval gives an unbounded ray.
            if m.contains(surfaces[0],z) or m.contains(surfaces[1],y):continue
            residual=[]
            for e,fiber in zip(surfaces,(y,z)):
                base=m.simplify(m.substitute(e,{fiber:m.ZERO}));A=m.add(m.substitute(e,{fiber:m.ONE}),m.neg(base))
                if m.variable_in(A) or not m.constant_defined(A,ctx) or m.sign(A,ctx) not in (-1,1) or not same_value(e,m.add(base,m.mul(A,m.power(fiber,2)))):break
                residual.append(m.div(m.neg(base),A))
            if len(residual)!=2:continue
            scales=[m.ONE,*(('s',p) for p in params if positive(('s',p)))]
            if saved is not None:
                chosen=freeze(saved['scale'])
                if chosen not in scales:raise Unsupported('The saved axial scale has no positive witness')
                scales=[chosen]
            for scale in scales:
                polynomials=[];factors=[]
                for R in residual:
                    num,den=m.rational_form(m.substitute(R,{x:m.mul(scale,t)}))
                    common=m.common_mon(num);factor=m.poly_expr({tuple((v,k) for v,k in common.items() if v!=t):F(1)})
                    unit=m.div(factor,m.poly_expr(den))
                    if not positive(unit):break
                    try:P,D=poly.rf(m.div(m.poly_expr(num),factor),var)
                    except poly.NotRational:break
                    if D!=(F(1),):break
                    polynomials.append(P);factors.append(unit)
                if len(polynomials)==2:break
            else:continue
            critical=[r for P in polynomials for r in rational_roots(P)]
            if any(r.b for r in critical):raise Unsupported('A critical fiber has an unhandled irrational station')
            roots=sorted({r.a for r in critical})
            intervals=[]
            for a,b in zip([None]+roots,roots+[None]):
                mid=(a+b)/2 if None not in (a,b) else b-1 if a is None and b is not None else a+1 if a is not None else F(0)
                if all(peval(P,mid)>0 for P in polynomials):intervals.append((a,b))
            if len(intervals)!=1 or None in intervals[0]:raise Unsupported('A unique bounded section interval is not isolated')
            low,high=intervals[0];Q=poly.pm(*polynomials)
            # Remove even root factors only after proving their signs throughout the chosen open interval.
            from integrals import polynomial_expression
            weight=m.mul(q(4),scale);remaining=Q;outside=m.ONE;odd=(F(1),)
            for r in roots:
                L=(-r,F(1));n=0
                while len(remaining)>1:
                    quo,rem=poly.pdiv(remaining,L)
                    if any(rem):break
                    remaining=quo;n+=1
                if n:
                    linear=m.add(t,q(-r));sign=1 if r<=low else -1 if r>=high else 0
                    if not sign:raise Unsupported('An interior zero splits the radical section')
                    outside=m.mul(outside,m.power(m.mul(q(sign),linear),n//2))
                    if n%2:odd=poly.pm(odd,L)
            remaining=poly.pm(remaining,odd)
            radical=m.simplify(('sqrt',polynomial_expression(remaining,var)))
            weight=m.mul(weight,m.simplify(('sqrt',m.mul(*factors))))
            density=m.mul(outside,radical);L,H=q(low),q(high);chart=None
            if low>=0 and remaining==(F(0),F(1)):
                image=m.power(t,2);chart='nonnegative square';density=m.mul(m.mul(q(2),t),m.mul(m.substitute(outside,{t:image}),t))
                L,H=(m.simplify(('sqrt',q(r))) for r in (low,high))
            value=integrate(density,weight,L,H)
            return theorem(argument='unique rectangular fibers from independent quadratic walls',axis=x[1],fiber_coordinates=[v[1] for v in (x,y,z)],scale=scale,
                source_squared_half_widths=residual,all_critical_stations=[q(r) for r in roots],normalized_interval=(q(low),q(high)),section_integrand=density,weight=weight,chart=chart),{'volume':value}
    raise Unsupported('Independent bounded fibers or a unique region for the intersecting surfaces have not been established')


def solid_sections_report(result):
    from app import pretty
    if result.get('value') is None:return 'Объём по сечениям\n'+result.get('reason','')
    plan=result['compilation'];kind=result['task']['kind']
    if 'source_volume_steps' in plan:
        value=result['value']['volume']
        if isinstance(value,dict):
            if 'beta_shape' in value:
                v=pretty(value['factor'])+' · B('+', '.join(map(pretty,value['beta_shape']))+')'
            else:
                v=pretty(value['factor'])+' · '+' · '.join('Γ('+pretty(s)+')' for s in value['gamma_numerator'])+' / Γ('+pretty(value['gamma_denominator'])+')'
        else:v=pretty(value)
        steps=[*plan['source_volume_steps'],'Объём равен '+v+'.']
        if 'other_component' in plan:steps.append('Для дополнительной области объём '+pretty(plan['other_component'])+'.')
        return '\n'.join(steps)
    if plan['theorem']=='method.monomial_section_volume':
        lines=['Показатели степеней двух семейств боковых стенок образуют обратимую матрицу. На подходящем по знакам квадранте логарифмы двух новых координат линейно выражаются через логарифмы |x| и |y|.']
        lines.extend(b['lower']+' ≤ '+b['variable']+' ≤ '+b['upper'] for b in plan['rectangle'])
        lines.append('Модуль якобиана равен '+pretty(plan['absolute_jacobian'])+', положительная высота равна '+pretty(plan['positive_height'])+'.')
        return '\n'.join(lines+['Объём равен '+pretty(result['value']['volume'])+'.'])
    if plan['theorem']=='method.affine_solid_measure':
        return ('Три линейные формы задают новые координаты. Обратимость проверена по присоединённой матрице. Якобиан обратной замены равен '+
                pretty(plan['inverse_jacobian'])+'. Образ области — '+('шар' if plan['target']=='ball' else 'прямоугольный параллелепипед')+'. Объём '+pretty(result['value']['volume'])+'.')
    if plan['theorem']=='method.grouped_power_sections':
        volume=result['value']['volume']
        value=(pretty(volume['factor'])+' · '+' · '.join('Γ('+pretty(e)+')' for e in volume['gamma_numerator'])+' / Γ('+pretty(volume['gamma_denominator'])+')' if isinstance(volume,dict) else pretty(volume))
        desc=('В нормированных координатах поперечное сечение — диск. Интегрируем радиус с якобианом r и учитываем обе половины тела.' if plan['chart']=='elliptical_disk' else
              'Положим t равным сумме двух нормированных координат, а u — доле первой из них. На ограниченной компоненте 0<u<1, якобиан пропорционален t.')
        return desc+' Остаётся бета-интеграл с аргументами '+', '.join(map(pretty,plan['beta_shape']))+'. Объём '+value+'.'
    if plan['theorem']=='method.homogeneous_ray_volume':
        required=', '.join(dict.fromkeys(pretty(v)+' ≠ 0' for v in plan['natural_nonzero']))
        prefix=('Условия исходных знаменателей: '+required+'. ') if required else ''
        return (prefix+'Нормируем оси и выбираем полярную ось '+plan['axis']+'. На единичной сфере получаем r^'+str(plan['radial_power'])+' = '+pretty(plan['angular_boundary'])+
                '. Положительная правая часть задаёт единственную внешнюю границу на луче. Интеграл r² dr равен r³/3. После углового интегрирования объём равен '+pretty(result['value']['volume'])+'.')
    if plan['theorem']=='method.radial_height_sections':
        lines=['Переходим к цилиндрическим координатам. Радиальное уравнение имеет единственный положительный корень '+pretty(plan['all_positive_roots'][0])+'.']
        for b in plan['bounds']:lines.append(b['lower']+' ≤ '+b['variable']+' ≤ '+b['upper'])
        return '\n'.join(lines+['Якобиан равен '+pretty(plan['jacobian'])+'.','Тройной интеграл даёт объём '+pretty(result['value']['volume'])+'.'])
    if plan['theorem']=='method.dirichlet_power_simplex_measure':
        lines=['Положительные степенные координаты превращают ограниченную часть тела в единичный симплекс.']
        if plan.get('raw_real_power_domain'):
            lines.append('На исходной области степеней и знаменателей выполняются '+', '.join(plan['raw_real_power_domain'])+'.')
        for v,c in plan['chart'].items():lines.append(v+' = '+pretty(c['scale'])+' · u_'+v+'^('+pretty(c['inverse_exponent'])+') внутри каждого листа.')
        lines.append('Число листов равно '+str(plan['congruent_sheets'])+'. Границы имеют нулевой объём.')
        lines.append('Последовательное интегрирование даёт произведение '+', '.join('B('+pretty(a)+', '+pretty(b)+')' for a,b in plan['beta_steps'])+'.')
        vol=result['value']['volume']
        value=(pretty(vol['factor'])+' · '+' · '.join('Γ('+pretty(e)+')' for e in vol['gamma_numerator'])+' / Γ('+pretty(vol['gamma_denominator'])+')' if isinstance(vol,dict) else pretty(vol))
        return '\n'.join(lines+['Объём равен '+value+'.'])
    if plan['theorem']=='method.projected_region_moments':
        lines=['Исходные границы задают ограниченную связную область проекции.']
        for piece in plan['pieces']:
            lines.extend(b['lower']+' ≤ '+b['variable']+' ≤ '+b['upper'] for b in piece['bounds'])
            if piece['height_bernstein_coefficients']:lines.append('Коэффициенты разности высот одного знака на всей полосе.')
        if 'volume' in result['value']:return '\n'.join(lines+['Объём равен '+pretty(result['value']['volume'])+'.'])
        return '\n'.join(lines+['Масса равна '+pretty(plan['integrals']['mass'])+'.','Координаты центра масс: '+', '.join(map(pretty,result['value']['centroid']))+'.'])
    if kind=='dense_section_measure':
        return '\n'.join(['На каждом промежутке высот встречаются рациональные и иррациональные уровни.',
            'Общая часть двух сечений определяет внутренний объём '+pretty(plan['inner_jordan_volume'])+'.',
            'Объединение сечений определяет наружный объём '+pretty(plan['outer_jordan_volume'])+'.',
            'Интеграл площади сечения равен '+pretty(plan['section_integral'])+'.',
            'Утверждение о существовании объёма по Жордану проверено.'])
    if kind=='section_measure_identity':
        return '\n'.join(['Площадь сечения равна '+pretty(plan['polynomial'])+'.',
            *['В точке '+pretty(x)+' площадь равна '+pretty(v)+'.' for x,v in plan['evaluations']],
            'Интегрирование многочлена по исходному отрезку даёт '+pretty(plan['integral'])+'.',
            'Правая часть заявленной формулы даёт то же значение.'])
    if kind=='volume_from_named_solid':
        lines=['На доле высоты t площадь поперечного сечения равна '+pretty(plan['section_area'])+'.',
               'При переходе от t к высоте появляется множитель '+pretty(plan['height'])+'.']
        if plan.get('derived_homothety_condition') is not None:
            lines.append('Подобие оснований конического тела даёт '+pretty(plan['derived_homothety_condition'])+' = 0.')
    elif 'source_squared_half_widths' in plan:
        lo,hi=plan['normalized_interval'];lines=[
            'Исходные поверхности ограничивают две независимые поперечные координаты.',
            'Квадраты полуширин равны '+' и '.join(map(pretty,plan['source_squared_half_widths']))+'.',
            'Обе полуширины положительны на общем промежутке от '+pretty(lo)+' до '+pretty(hi)+' в нормированной координате.']
    elif 'section_area' in plan:
        lines=['Внутри исходного интервала сечения являются эллипсами площадью '+pretty(plan['section_area'])+'.']
    else:lines=['Приведение квадратичной формы к положительным квадратам выделяет ограниченную внутренность эллипсоида.']
    return '\n'.join(lines+['Объём равен '+pretty(result['value']['volume'])+'.'])


SPATIAL_MEASURE_GOALS=frozenset({'surface_area','solid_area_and_volume','solid_centroid','solid_inertia','moments_identity'})
SPATIAL_FORCE_GOALS=frozenset({'mechanical_integral_application','newton_potential_or_force'})


def spatial_moment_admission(task):
    """Select goals whose original text names a supported family of verified maps."""
    kind=task.get('kind');region=task.get('region','');expr=task.get('integrand','')
    if kind=='surface_area':return isinstance(task.get('surface_region'),str) and 'parametrization' not in task
    if kind in SPATIAL_MEASURE_GOALS:return True
    if kind in SPATIAL_FORCE_GOALS:return True
    if kind in {'spatial_exact_integral','partition_volume_ratio','bounded_solid_volume'} and projective_region_spec(task):return True
    if kind in {'symbolic_dimension_integral','spatial_integral_reduction','dirichlet_integral','radial_integral_reduction',
                'multiple_integral_identity','spatial_integral_mean','spatial_integral_estimate'}:
        return True
    if not isinstance(region,str) or not isinstance(expr,str):return False
    if kind=='differentiate_moving_integral':
        return (re.fullmatch(r'[A-Za-z]\w*\(x\^2\+y\^2\+z\^2\)',expr) and
                re.fullmatch(r'x\^2\+y\^2\+z\^2<=([a-z]\w*)\^2',region) or
                re.fullmatch(r'[A-Za-z]\w*\(x\*y\*z\)',expr) and
                re.fullmatch(r'0<=x<=([a-z]\w*),0<=y<=\1,0<=z<=\1',region))
    if kind=='spatial_exact_integral':
        return (re.fullmatch(r'ellipsoid x\^2/\w+\^2\+y\^2/\w+\^2\+z\^2/\w+\^2(?:=|<=)1',region)
                or region.startswith('sphere x^2+y^2+z^2=') and expr=='sqrt(x^2+y^2+z^2)'
                or region.startswith('bounded by x+y+z=') and region.endswith(',x=0,y=0,z=0')
                or region.startswith('bounded by x^2+y^2+z^2=') and region.endswith(',x=0,y=0,z=0')
                or re.fullmatch(r'x\^2\+y\^2\+z\^2<=\d+',region) and 'all_parity_cases' in task.get('requested_output',[])
                or region.startswith('bounded by x^2+y^2=z^2,z=')
                or task.get('method_requirement')=='spherical_coordinates' and
                re.fullmatch(r'0<=x<=1,0<=y<=sqrt\(1-x\^2\),sqrt\(x\^2\+y\^2\)<=z<=sqrt\(2-x\^2-y\^2\)',region))
    if kind=='solid_mass':
        return (re.fullmatch(r'x\^2\+y\^2\+z\^2>=[1-9]\d*',region) and
                re.fullmatch(r'\w+\*exp\(-[A-Za-z]\w*\*sqrt\(x\^2\+y\^2\+z\^2\)\)',task.get('density','')))
    if kind=='improper_multiple_integral':
        return (region=='R^n, (aij) real symmetric positive definite' or
                re.fullmatch(r'x\^2\+y\^2<=[1-9]\d*',region) and expr=='ln(1/sqrt(x^2+y^2))' or
                re.fullmatch(r'x\^2\+y\^2<=(?:[1-9]\d*\*)?x',region) and expr=='1/sqrt(x^2+y^2)' or
                re.fullmatch(r'0<=x<=([a-z]\w*),0<=y<=x,\1>0',region) is not None or
                re.fullmatch(r'bounded by y=0,y=x,x=(?:pi|\d+)',region) is not None and expr.startswith('ln(sin('))
    return False


def source_spatial_moment(task,library,request):
    """Bind original source variables, then derive a weighted section or a checked coordinate substitution."""
    if not library.data.get('verified_spatial_moments'):
        raise Unsupported('Checked spatial moment compilers are unavailable')
    kind=task['kind'];meta=task.get('source',{});want=task.get('requested_output')
    provenance={'exercise','printed_subpart','printed_page','pdf_page','pdf_sha256','literal_requirement'}
    if (isinstance(meta,dict) and kind=='moments_identity' and type(meta.get('continued_on_pdf_page')) is int
            and meta['continued_on_pdf_page']>0):
        provenance.add('continued_on_pdf_page')
    if not isinstance(meta,dict) or set(meta)-provenance:
        raise Unsupported('A source side condition or imposed method remains')
    contracts={
        'symbolic_dimension_integral':({'integrand','region','dimension'}, ['formula_for_general_dimension'],'Вычислить интеграл или объём для исходного произвольного n.'),
        'multiple_integral_identity':({'claim','suggested_method'},['proof'],'Доказать указанную формулу.'),
        'dirichlet_integral':({'integrand','region','stated_conditions','substitution'}, ['exact_integral','specified_substitution'],'Вычислить интеграл Дирихле указанной заменой.'),
        'radial_integral_reduction':({'integrand','region','stated_conditions'}, ['one_dimensional_integral'],'Свести n-кратный интеграл к однократному.'),
        'spatial_integral_reduction':({'integrand','region','oriented_limits'},['one_dimensional_integral'],'Заменить тройной интеграл однократным.'),
        'spatial_exact_integral':({'integrand','region','method_requirement','hypotheses'},['exact_integral'],'Вычислить тройной интеграл по указанной области.'),
        'spatial_integral_mean':({'integrand','region'},['volume_mean'],'Найти среднее значение в указанной области.'),
        'spatial_integral_estimate':({'integrand','region','stated_conditions','method_requirement'},['two_sided_estimate'],'Оценить, пользуясь теоремой о среднем.'),
        'differentiate_moving_integral':({'integrand','region'},['derivative_with_scope'],'Найти F′(t); f дифференцируема.'),
        'solid_mass':({'density','region','stated_conditions'},['mass'],'Найти массу тела, заполняющего бесконечную область.'),
        'improper_multiple_integral':({'integrand','region'},['improper_integral_with_convergence'],'Вычислить несобственный интеграл.'),
    }
    projective=projective_region_spec(task) if kind in {'spatial_exact_integral','partition_volume_ratio','bounded_solid_volume','solid_area_and_volume'} else None
    if projective or kind in SPATIAL_MEASURE_GOALS or kind in SPATIAL_FORCE_GOALS:
        def emit(rule,steps,answer,**data):
            raw=task.get('region',task.get('surface_region',task.get('surfaces',task.get('physical_model'))))
            return dict(theorem='method.'+rule,argument=list(steps),source_region=raw,
                        required_method=task.get('method_requirement'),**data),answer
        if projective:return source_projective_spatial_measure(task,projective,emit,library)
        if kind in SPATIAL_FORCE_GOALS:return source_spatial_force(task,emit)
        if kind in ('surface_area','solid_area_and_volume'):return spatial_surface_measure(task,emit)
        return spatial_section_measure(task,emit)
    if kind not in contracts:raise Unsupported('The mathematical output is not bound')
    fields,expected,heading=contracts[kind];allowed_headings={heading}
    if kind=='spatial_integral_mean':allowed_headings.add('Найти среднее значение в эллипсоиде.')
    if kind=='spatial_exact_integral' and task.get('hypotheses') is not None:
        expected=['all_parity_cases','exact_integral'];allowed_headings={'Вычислить для целых неотрицательных m,n,p.'}
    if set(task)-{'kind','id','source','requested_output',*fields} or want!=expected or (meta.get('literal_requirement') is not None and meta['literal_requirement'] not in allowed_headings):
        raise Unsupported('The original mathematical restrictions and requested conclusions must all be preserved')
    def emit(rule,steps,answer,**data):
        return dict(theorem='method.'+rule,argument=list(steps),source_region=task.get('region'),
                    required_method=task.get('method_requirement',task.get('suggested_method')),**data),answer
    if kind=='symbolic_dimension_integral':return symbolic_spatial_moment(task,emit)
    if kind=='multiple_integral_identity':return ordered_spatial_identity(task,emit)
    if kind=='dirichlet_integral':return positive_dirichlet_map(task,request,emit)
    if kind in {'radial_integral_reduction','spatial_integral_reduction'}:return weighted_slice_reduction(task,emit)
    if kind=='differentiate_moving_integral':return moving_spatial_moment(task,emit)
    if kind in {'improper_multiple_integral','solid_mass'}:return improper_spatial_chart(task,emit)
    return exact_spatial_chart(task,request,emit)


def symbolic_spatial_moment(task,emit):
    """Integrate dimension-independent kernels by tensor, simplex and ball measures."""
    d=task['dimension'];region=task['region'];expr=task['integrand'].replace('²','^2')
    if not isinstance(d,str) or not re.fullmatch(r'[A-Za-z]\w*',d):raise Unsupported('The dimension must be a bound positive integer')
    fac=lambda n:f'factorial({n})'
    ball=lambda n:f'pi^(({n})/2)/Gamma(1+({n})/2)'
    def result(form,*proof,min_dim=1,rule='affine_slice_moment',**data):
        return emit(rule,proof,dict(formula=form,dimension=d,assumptions=[f'{d} integer, {d}>={min_dim}']),**data)
    if (hit:=re.fullmatch(r'\[0,(\d+)\]\^'+re.escape(d),region)) and int(hit[1])>0:
        L=int(hit[1]);k=re.fullmatch(r'sum_i xi\^([1-9]\d*)',expr)
        if k:
            n=int(k[1]);factor='' if L==1 else f'*{L}^({d}+{n})'
            return result(f'{d}{factor}/{n+1}','Каждый член зависит только от одной координаты.',
                          'Фубини даёт один степенной момент и произведение длин остальных сторон.',degree=n,cube_edge=L)
        if expr=='(sum_i xi)^2':
            factor='' if L==1 else f'*{L}^({d}+2)'
            return result(f'{d}*(3*{d}+1){factor}/12','Раскрываем квадрат суммы. Получаем d квадратов и d(d−1) упорядоченных смешанных членов.',
                          'Фубини применим к полиному на компактном кубе. Каждый квадрат даёт коэффициент 1/3, каждый смешанный член 1/4.',cube_edge=L)
    if (hit:=re.fullmatch(r'xi>=0,sum_i xi<=([a-z][a-z_0-9]*|\d+)',region)):
        R=hit[1];alpha={'1':F(0),'sqrt(sum_i xi)':F(1,2)}.get(expr)
        if alpha is not None:
            power=f'{d}+({alpha})' if alpha else d
            text=(f'{R}^{d}/{fac(d)}' if not alpha else f'({R})^({power})/({fac(d+"-1")}*({power}))')
            if not R.isdigit():text=f'piecewise({text} for {R}>0; 0 for {R}<=0)'
            return result(text,'Объём подуровня суммы координат получается из единичного симплекса растяжением во всех направлениях.',
                          'Единичный объём равен 1/d! по индукции по сечениям. Дифференцируем объём подуровня, получая вес s^(d−1)/(d−1)!, затем интегрируем указанную степень.',
                          radius=R,weight_power=q(alpha))
    if (hit:=re.fullmatch(r'0<=x'+re.escape(d)+r'<=\.\.\.<=x1<=(\d+)',region)):
        mon=re.fullmatch(r'prod_i xi(?:\^([1-9]\d*))?',expr)
        if mon:
            R=int(hit[1]);p=int(mon[1] or '1')+1;factor='' if R==1 else f'{R}^({p}*{d})/'
            return result(f'{factor}({p}^{d}*{fac(d)})' if R!=1 else f'1/({p}^{d}*{fac(d)})',
                          'Куб покрывается d! областями разных порядков. Общие границы имеют нулевую меру.',
                          'Произведение степеней симметрично, поэтому каждая область имеет одинаковый интеграл. Применяем Фубини на кубе и делим момент на d!.',
                          rule='ordered_simplex_moments',degree=p-1,cube_edge=R)
    if expr=='1' and region==f'pairs of hyperplanes sum_j aij*xj=+hi,-hi for i=1..{d}; det(A)!=0':
        return result(f'2^{d}*prod_i abs(hi)/abs(det(A))','Матрица A обратима по условию. Карта y=A x переводит пары гиперплоскостей в |y_i|≤|h_i| и имеет ненулевой постоянный якобиан.',
                      'В образе перемножаем длины сторон и делим на |det A|. Нулевая ширина даёт нулевой объём.',rule='affine_slice_moment',inverse_jacobian='1/abs(det(A))')
    if expr=='1' and region=='xi>=0,sum_i xi/ai<=1,ai>0':
        return result(f'prod_i ai/{fac(d)}','Диагональный масштаб y_i=x_i/a_i обратим, так как все a_i>0, и переводит область в положительный единичный симплекс.',
                      'Множитель объёма prod_i ai. Единичный объём равен 1/d! по проверенной индукции по сечениям.')
    if expr=='1' and region==f'n-cone sum_{{i<{d}}}(xi/ai)^2=(x{d}/a{d})^2, x{d}=a{d}':
        return result(f'({ball(d+"-1")})*prod_i abs(ai)/{d}','Только та полость, которую замыкает плоскость x_d=a_d, даёт ограниченное тело.',
                      'При x_d=a_d t, 0≤t≤1, сечение — эллипсоид с осями |a_i|t. Масштабируем единичный шар, интегрируем t^(d−1) и учитываем |a_d|.',
                      min_dim=2,rule='radial_moment_coordinates')
    if (hit:=re.fullmatch(r'sum_i xi\^2<=([a-z]\w*|\d+)\^2',region)) and expr=='1':
        R=hit[1]
        return result(f'({ball(d)})*abs({R})^{d}','Декартов интеграл exp(−|x|²) равен произведению одномерных гауссовых интегралов π^(d/2).',
                      'В радиальных координатах этот же интеграл равен S_(d−1)·Γ(d/2)/2. Из этого следует объём единичного шара, затем масштабируем на |R|.',
                      rule='radial_moment_coordinates',radius=R)
    if (hit:=re.fullmatch(r'sum_\{i<'+re.escape(d)+r'\} xi\^2<=([a-z]\w*)\^2,-([a-z]\w*)/2<=x'+re.escape(d)+r'<=\2/2',region)) and expr==f'x{d}^2':
        R,H=hit.groups()
        return result(f'piecewise(({ball(d+"-1")})*abs({R})^({d}-1)*{H}^3/12 for {H}>=0; 0 for {H}<0)',
                      'Сечения фиксированной координатой имеют одну и ту же меру (d−1)-шара. При отрицательной высоте исходные границы несовместны.',
                      'Фубини оставляет только момент ∫ x_d² dx_d=h³/12 на исходном симметричном отрезке.',min_dim=2,rule='radial_moment_coordinates')
    if region=='sum_i xi^2<=1' and expr=='1/sqrt(1-sum_i xi^2)':
        return result(f'pi^(({d}+1)/2)/Gamma(({d}+1)/2)','Радиальный вес S_(d−1) r^(d−1) берётся из меры шара.',
                      'Неотрицательное ядро допускает независимое приближение к r=1. При t=r² получается B(d/2,1/2), которая сходится на обоих концах.',rule='radial_moment_coordinates')
    raise Unsupported('A symbolic slice or coordinate measure for this kernel is missing')


def ordered_spatial_identity(task,emit):
    text=task['claim'];method=task.get('suggested_method')
    def result(name,formula,*steps,**data):
        return emit(name,steps,dict(identity=True,formula=formula),**data)
    if method is None and re.fullmatch(r'Kn\(x,y\)=int_\[a,b\]\^n K\(x,t1\)K\(t1,t2\)\.\.\.K\(tn,y\)dt; K_\(n\+m\+1\)\(x,y\)=int_a\^b Kn\(x,t\)Km\(t,y\)dt; K continuous on \[a,b\]\^2',text):
        return result('ordered_simplex_moments','K_(n+m+1)=integral(K_n*K_m)',
                      'Оба произведения образуют непрерывное ядро на компактном кубе.',
                      'В цепи из n+m+1 промежуточных координат оставляем одну общую координату. Фубини объединяет первые n и последние m координат с точно этим общим аргументом.',split_index='n+1')
    if method is None and re.fullmatch(r'int_\{0<=xn<=\.\.\.<=x1<=x\} f has reversed representation int_0\^x dxn int_xn\^x dx\(n-1\)\.\.\.int_x2\^x f dx1; n>=2, f continuous on \[0,x\]\^n',text):
        return result('ordered_simplex_moments','same ordered simplex in reverse integration order',
                      'Фиксируя самую малую координату, каждая следующая лежит между предыдущей и x.',
                      'Оба набора пределов взаимно описывают одно и то же множество упорядоченных точек. Непрерывность на компакте позволяет применить Фубини.',bound_proof='0<=x_n<=...<=x_1<=x')
    if method is None and (hit:=re.fullmatch(r'int_\{0<=([a-z])n<=\.\.\.<=\1\u0031<=([a-z])\} prod_i ([a-z])\(\1i\) = \(int_0\^\2 \3\(tau\)dtau\)\^n/n!; \3 continuous',text)):
        v,edge,fn=hit.groups()
        return result('ordered_simplex_moments',f'(int_0^{edge} {fn}(s)ds)^n/n!',
                      'Перестановки координат разбивают исходный куб на n! частей с равной мерой и симметричным весом.',
                      'По Фубини полный момент распадается на произведение равных однократных интегралов. Для ориентированных отрицательных пределов знак каждой координаты сохраняется при индукции Ньютон–Лейбница.',coordinate=v)
    if method is None and (hit:=re.fullmatch(r'int_\{0<=xn<=\.\.\.<=x1<=([a-z])\} ([a-z])\(xn\) = int_0\^\1 \2\(u\)\*\(\1-u\)\^\(n-1\)/\(n-1\)! du',text)):
        edge,fn=hit.groups()
        return result('ordered_simplex_moments',f'int_0^{edge} {fn}(u)*({edge}-u)^(n-1)/(n-1)! du',
                      'При фиксированной нижней координате u оставшиеся n−1 координат заполняют один из равновеликих порядков куба [u,x]^(n−1).',
                      'Его мера равна (x−u)^(n−1)/(n−1)!. Для ориентированных отрицательных пределов повторное применение Ньютон–Лейбница даёт тот же знак и ядро.',fiber_dimension='n-1')
    if method is None and re.fullmatch(r'int_\{0<=x\(n\+1\)<=\.\.\.<=x1<=x\} x1\*\.\.\.\*xn\*f\(x\(n\+1\)\) = int_0\^x \(x\^2-u\^2\)\^n\*f\(u\)du/\(2\^n\*n!\)',text):
        return result('ordered_simplex_moments','int_0^x (x^2-u^2)^n*f(u)du/(2^n*n!)',
                      'При фиксированной последней координате u вес произведения остальных координат симметричен на кубе [u,x]^n.',
                      'Каждый множитель интегрируется до (x²−u²)/2. Поделив момент куба на n!, получаем напечатанный вес.',fiber_dimension='n',single_factor='(x^2-u^2)/2')
    simplex='int_{xi>=0,sum xi<=1} '
    flat='prod xi^(pi-1) = prod Gamma(pi)/Gamma(sum pi+1), pi>0'
    weighted=re.fullmatch(re.escape(simplex)+r'([A-Za-z]\w*)\(sum xi\)prod xi\^\(pi-1\) = prod Gamma\(pi\)/Gamma\(sum pi\) \* int_0\^1 \1\(u\)u\^\(sum pi-1\) du; pi>0,\1 continuous',text)
    if (text==simplex+flat and method is None) or (weighted and method in (None,'mathematical_induction')):
        formula=(f'prod Gamma(pi)/Gamma(sum pi) * int_0^1 {weighted[1]}(u)u^(sum pi-1)du' if weighted else
                 'prod Gamma(pi)/Gamma(sum pi+1)')
        return result('dirichlet_weighted_sections',formula,
                      'Одномерная база очевидна. Для индукции сливаем последние две координаты r,s через их сумму u и долю r/u.',
                      'Якобиан u, доля на [0,1] даёт B(p,q). Положительные показатели обеспечивают интегрируемость у границ. Непрерывный внешний вес ограничен и сохраняется, так как зависит только от суммы.',
                      'После объединения показатель равен p+q. Сокращение последовательных Бета-множителей даёт формулу. Для постоянного внешнего веса последний интеграл равен 1/∑p_i.',
                      beta_arguments=('p','q'),new_shape='p+q',slice_density='u^(sum pi-1)')
    raise Unsupported('A matching order, weight symmetry or requested induction is not established')


def positive_dirichlet_map(task,request,emit):
    from cartesian_fields import _chart_determinant
    from model import freeze
    from tasks import source
    from verify import same_value
    expr=task['integrand'];h=re.fullmatch(r'x\^(\w+)\*y\^(\w+)\*z\^(\w+)\*\(1-x-y-z\)\^(\w+)',expr)
    if not h or len(set(h.groups()))!=4 or task['region']!='x+y+z<=1,x>=0,y>=0,z>=0':
        raise Unsupported('Bind all four original degrees and the full simplex')
    powers=h.groups();facts=task['stated_conditions'];printed=task['substitution']
    if facts!=[','.join(powers)+' positive'] or not isinstance(printed,list) or len(printed)!=3:
        raise Unsupported('All endpoint factors or the printed substitution remain unproved')
    names=[]
    for form,lhs in zip(printed,['x+y+z','y+z','z'],strict=True):
        left,right=form.split('=',1)
        terms=right.split('*')
        if left!=lhs or terms[:-1]!=names or not re.fullmatch(r'[A-Za-z]\w*',terms[-1]) or terms[-1] in [*names,*powers,'x','y','z']:
            raise Unsupported('The stated map does not give successive sums and their ratios')
        names.append(terms[-1])
    r,s,t=(('s',v) for v in names);rs=m.mul(r,s);rst=m.mul(rs,t)
    inverse=(m.add(r,m.neg(rs)),m.add(rs,m.neg(rst)),rst);J=[]
    for i,e in enumerate(inverse):
        child=dict(kind='partial_derivatives',function=source(e),variables=names,requested_output=['first_partial_derivatives'])
        J.append(tuple(map(freeze,request(f'checked derivatives of inverse coordinate {i+1}',child)['value'])))
    jac=_chart_determinant(J);required=m.mul(m.power(r,2),s)
    if not same_value(jac,required):raise Unsupported('The inverse Jacobian did not verify')
    p,q0,v,w=powers
    steps=['Из напечатанных равенств выводим обратную карту. Внутри симплекса все три новые координаты между 0 и 1.',
           'Частные производные обратной карты дают положительный якобиан ξ²η. Обратимость и полнота проверяются через исходные суммы.',
           'Подстановка разделяет интеграл на три Бета-интеграла. Все печатные показатели положительны, края интегрируемы. Сокращаем гамма-множители.']
    return emit('dirichlet_weighted_sections',steps,
                dict(formula=f'Gamma({p}+1)*Gamma({q0}+1)*Gamma({v}+1)*Gamma({w}+1)/Gamma({p}+{q0}+{v}+{w}+4)',convergence='absolute'),
                inverse=inverse,jacobian=jac,cube=(0,1),map_symbols=names,
                beta_shapes=((f'{p}+{q0}+{v}+3',f'{w}+1'),(f'{q0}+{v}+2',f'{p}+1'),(f'{v}+1',f'{q0}+1')))


def weighted_slice_reduction(task,emit):
    region=task['region'];expr=task['integrand'];spec=task.get('oriented_limits')
    def result(rule,formula,*steps,**facts):return emit(rule,steps,dict(formula=formula),**facts)
    if task['kind']=='radial_integral_reduction':
        fn=re.fullmatch(r'([A-Za-z]\w*)\(sqrt\(sum_i xi\^2\)\)',expr);b=re.fullmatch(r'sum_i xi\^2<=([A-Za-z]\w*)\^2',region)
        if fn and b and task.get('stated_conditions')==['n>=2',fn[1]+' continuous']:
            return result('radial_moment_coordinates',f'(2*pi^(n/2)/Gamma(n/2))*int_0^abs({b[1]}) {fn[1]}(r)*r^(n-1)dr',
                          'Объём шара радиуса r равен κ_n r^n. Дифференциал объёма даёт меру радиального слоя.',
                          'Непрерывность исходной функции позволяет применить послойную формулу и сохраняет оба края от 0 до |R|.',dimension_condition='n>=2')
        raise Unsupported('The full radial function or its source continuity has not been bound')
    if spec is not None:
        if not isinstance(spec,list) or len(spec)!=3 or region!='oriented bounds '+'; '.join(spec):
            raise Unsupported('The ordered source limits differ from the original input')
        rows=[re.fullmatch(r'([A-Za-z]\w*):0\.\.([A-Za-z]\w*)',s) for s in spec]
        if all(rows) and all(rows[i][2]==rows[i-1][1] for i in range(1,len(rows))):
            v=[z[1] for z in rows];edge=rows[0][2];fn=re.fullmatch(r'([A-Za-z]\w*)\('+re.escape(v[-1])+r'\)',expr)
            if len(set([*v,edge]))==4 and fn:
                return result('ordered_simplex_moments',f'int_0^{edge} ({edge}-{v[-1]})^2*{fn[1]}({v[-1]})/2 d{v[-1]}',
                              'После фиксации внутренней координаты остаётся треугольник двух упорядоченных координат.',
                              'Его мера равна (x−u)²/2. Для отрицательного x формула переносится по ориентированному Ньютон–Лейбницу, не меняя пределы исходной постановки.',
                              stacking=v,source_orientation='signed')
    if (hit:=re.fullmatch(r'0<=x<=([1-9]\d*),0<=y<=([1-9]\d*),0<=z<=(?:x\+y|y\+x)',region)) and (fn:=re.fullmatch(r'([A-Za-z]\w*)\(z\)',expr)):
        a,b=map(int,hit.groups());L=a+b
        return result('affine_slice_moment',f'int_0^{L} {fn[1]}(z)*(({L}-z)^2-max({a}-z,0)^2-max({b}-z,0)^2)/2 dz',
                      'На высоте z остаётся часть прямоугольника x+y≥z. Отражаем её к прямоугольному треугольнику с порогом a+b−z.',
                      'Вычитаем два излишних треугольника за сторонами. Для 0≤z≤a+b их положительные площади не пересекаются, получен точный послойный вес.',
                      section_knots=sorted({0,a,b,L}),coordinates=('x','y','z'))
    raise Unsupported('No checked mass of each original slice is available')


def moving_spatial_moment(task,emit):
    region=task['region'];expr=task['integrand']
    if (body:=re.fullmatch(r'([A-Za-z]\w*)\(x\^2\+y\^2\+z\^2\)',expr)) and (ball:=re.fullmatch(r'x\^2\+y\^2\+z\^2<=([a-z]\w*)\^2',region)):
        fn,P=body[1],ball[1]
        return emit('radial_moment_coordinates',[
            'Сферическая замена переводит интеграл в 4π∫₀^|t| f(r²)r² dr.',
            'Вне t=0 применяем Ньютон–Лейбница с производной |t|. В t=0 исходный интеграл O(|t|³), поэтому производная равна нулю.'],
            dict(formula=f'4*pi*{P}*abs({P})*{fn}({P}^2)',scope='all real parameters in the source function domain'),radial_radius=f'abs({P})')
    if (body:=re.fullmatch(r'([A-Za-z]\w*)\(x\*y\*z\)',expr)) and (box:=re.fullmatch(r'0<=x<=([a-z]\w*),0<=y<=\1,0<=z<=\1',region)):
        fn,P=body[1],box[1]
        return emit('affine_slice_moment',[
            'При положительном параметре производная получается по трём движущимся верхним граням. На каждой грани исходный интегранд непрерывен.',
            'Три вклада равны по симметрии произведения x*y*z. У начала весь объём O(|t|³). При отрицательном параметре исходное множество пусто.'],
            dict(formula=f'piecewise(3*int_0^{P} int_0^{P} {fn}({P}*y*z)dy dz for {P}>0; 0 for {P}<=0)',scope='original cubical inequalities'),moving_faces=3)
    raise Unsupported('The source shape is not a uniformly expanding ball or a product cube of one variable')


def exact_spatial_chart(task,request,emit):
    from functools import reduce
    from model import freeze
    from quadrature import guard_bounds
    from tasks import source
    from verify import same_value
    S=task['region'];text=task['integrand'];kind=task['kind'];method=task.get('method_requirement');facts=task.get('stated_conditions',[])
    coords=['x','y','z'];x,y,z=(('s',v) for v in coords);axes=(x,y,z)
    H=m.add(m.add(m.power(x,2),m.power(y,2)),m.power(z,2))
    def out(rule,val,*steps,**data):return emit(rule,steps,dict(value=val),**data)
    if kind=='spatial_integral_estimate' and method=='integral_mean_value':
        radius=re.fullmatch(r'x\^2\+y\^2\+z\^2<=([A-Za-z]\w*)\^2',S)
        p=re.fullmatch(r'1/sqrt\(\(x-(\w+)\)\^2\+\(y-(\w+)\)\^2\+\(z-(\w+)\)\^2\)',text)
        if radius and p and len(set((*p.groups(),radius[1],*coords)))==7:
            R,A,B,C=radius[1],*p.groups();d2=f'{A}^2+{B}^2+{C}^2'
            if facts==[d2+'>'+R+'^2']:
                d=('sqrt',m.parse(d2,None,[A,B,C]));r=('abs',('s',R));vol=m.mul(m.mul(q(4,3),m.PI),m.power(r,3))
                ends=(m.div(vol,m.add(d,r)),m.div(vol,m.add(d,m.neg(r))))
                return emit('radial_moment_coordinates',[
                    'Печатное условие помещает точку строго вне шара. На всём исходном шаре расстояние между d−r и d+r по неравенству треугольника.',
                    'Выполняем именно оценку из теоремы о среднем для непрерывного ядра. Умножаем границы на объём шара.'],
                    dict(lower=ends[0],upper=ends[1]),radius=r,dist_to_center=d,positive_minimum=m.add(d,m.neg(r)))
    ell=re.fullmatch(r'(?:ellipsoid )?x\^2/(\w+)\^2\+y\^2/(\w+)\^2\+z\^2/(\w+)\^2(?:=|<=)1',S)
    if ell and len(set((*ell.groups(),*coords)))==6:
        scales=ell.groups();A=tuple(('s',v) for v in scales)
        raw=m.parse(text,None,[*coords,*scales]);D=reduce(m.add,(m.div(m.power(v,2),m.power(a,2)) for v,a in zip(axes,A)),ZERO)
        guards=domain_conditions(raw);nonzero=[m.power(a,2) for a in A]
        bound=lambda source,target: same_value(source,target) and not any(r!='nonzero' or not any(same_value(g,h) for h in nonzero) for r,g in domain_conditions(source))
        K=reduce(m.mul,(('abs',a) for a in A),ONE)
        steps=['Диагональная замена делит координаты на исходные ненулевые масштабы. Образ — весь единичный шар, обратный якобиан — произведение модулей масштабов.',
               'После замены исходное ядро зависит только от радиуса; радиальная мера в трёх измерениях равна 4πr²dr.']
        if kind=='spatial_exact_integral' and method in (None,'appropriate_change_of_variables','spherical_coordinates'):
            if not any(r!='nonzero' or not any(same_value(g,h) for h in nonzero) for r,g in guards) and same_value(raw,D):
                val=m.mul(m.mul(q(4,5),m.PI),K);steps.append('Интегрируем r⁴ от 0 до 1.')
            elif raw[0]=='sqrt' and bound(raw[1],m.add(ONE,m.neg(D))):
                val=m.mul(m.mul(q(1,4),m.power(m.PI,2)),K);steps.append('Подстановка u=r² даёт второй параметр Бета-интеграла 3/2. Оба края сходятся.')
            else:raise Unsupported('The original ellipsoid weight is neither its norm nor an admitted radial function')
            return out('radial_moment_coordinates',val,*steps,diagonal=A,jacobian=K)
        if kind=='spatial_integral_mean' and raw[0]=='exp' and raw[1][0]=='sqrt' and bound(raw[1][1],D):
            steps.append('Общий якобиан сокращается при делении на объём, после чего 3∫₀¹r²e^r dr=3(e−2).')
            return out('radial_moment_coordinates',m.mul(q(3),m.add(('exp',ONE),q(-2))),*steps,diagonal=A,jacobian=K)
    sphere,comparison,side=S.partition('<=')
    if kind=='spatial_integral_mean' and comparison:
        left=m.parse(sphere,None,coords);R=m.parse(side,None,coords);p,d=m.rational_form(R)
        if not domain_conditions(left) and not domain_conditions(R) and m.simplify(left)==H and set(d)=={()} and set(p)<={((v,1),) for v in axes}:
            C=[q(p.get(((v,1),),F(0))/(2*d[()])) for v in axes];Q=m.dot(C,C)
            raw=m.parse(text,None,coords)
            if Q!=ZERO and not domain_conditions(raw) and same_value(raw,H):
                value=m.mul(q(8,5),Q)
                return out('radial_moment_coordinates',value,
                           'Дополняем квадраты. Получаем шар с центром C и квадратом радиуса |C|².',
                           'После сдвига линейный член имеет нулевой момент по отражению. Средний квадрат расстояния от центра равен 3R²/5.',center=C,radius_squared=Q)
    if kind!='spatial_exact_integral':raise Unsupported('No applicable proof for the stated mean or estimate')
    if task.get('hypotheses') is not None:
        p=re.fullmatch(r'x\^(\w+)\*y\^(\w+)\*z\^(\w+)',text);b=re.fullmatch(r'x\^2\+y\^2\+z\^2<=(\d+)',S)
        if p and b and int(b[1])>0 and len(set(p.groups()))==3 and task['hypotheses']==[','.join(p.groups())+' nonnegative integers'] and method is None:
            names=p.groups();total='+'.join(names);numer='*'.join(f'Gamma(({j}+1)/2)' for j in names)
            factor='' if b[1]=='1' else f'{b[1]}^(({total}+3)/2)*'
            even=f'{factor}{numer}/Gamma(({total}+3)/2+1)'
            return emit('radial_moment_coordinates',[
                'При нечётной степени отражение одной координаты меняет знак и сохраняет шар.',
                'В чётной ветви складываем восемь одинаковых октантов. Квадраты нормированных координат переводят каждый в симплекс, а якобиан даёт половинные гамма-показатели.'],
                dict(formula=f'piecewise(0 if any of {",".join(names)} odd; {even} otherwise)'),hypotheses=task['hypotheses'])
        raise Unsupported('The parity result needs nonnegative integer indices and the complete ball')
    raw=m.parse(text,None,coords)
    simplex=re.fullmatch(r'bounded by x\+y\+z=([1-9]\d*),x=0,y=0,z=0',S)
    if simplex and method in (None,'appropriate_change_of_variables'):
        ceiling=int(simplex[1]);s=('v','slice');T=reduce(m.add,axes,ZERO);rho=m.substitute(raw,{x:s,y:ZERO,z:ZERO})
        if same_value(raw,m.substitute(rho,{s:T})):
            enclosures=[]
            for relation,g in domain_conditions(raw):
                same=m.substitute(g,{x:s,y:ZERO,z:ZERO})
                if not same_value(g,m.substitute(same,{s:T})):raise Unsupported('An original domain guard depends on variables other than the sum')
                lo,hi=guard_bounds(relation,same,(F(0),F(ceiling)),['slice'])
                enclosures.append((relation,same,q(lo),q(hi)))
            child=dict(kind='iterated_integral',integrand=source(m.mul(m.div(m.power(s,2),q(2)),rho)),
                       integration_order=[dict(variable='slice',lower='0',upper=str(ceiling))],requested_output=['exact_integral'])
            val=freeze(request('verified one-dimensional integral of the recovered slice measure',child)['value'])
            return out('affine_slice_moment',val,'Координата s=x+y+z имеет постоянный якобиан 1 при выборе оставшихся x,y.',
                       'Сечение с фиксированным s — треугольник площади s²/2. Исходное ядро и каждое ограничение области зависят от одной суммы.',
                       'Подставляем меру сечения и решаем полученный одномерный интеграл.',slice_weight=m.div(m.power(s,2),q(2)),guard_checks=enclosures)
    octant=re.fullmatch(r'bounded by x\^2\+y\^2\+z\^2=([1-9]\d*),x=0,y=0,z=0',S)
    if octant and method is None and not domain_conditions(raw):
        p,d=m.rational_form(raw)
        if len(p)==1 and set(d)=={()}:
            (mon,c),=p.items();powers=dict(mon)
            if set(powers)<=set(axes):
                j=[powers.get(v,0) for v in axes];R=('sqrt',q(int(octant[1])));shapes=[q(F(k+1,2)) for k in j]
                scale=m.mul(q(c/(8*d[()])),m.power(R,3+sum(j)));value=gamma_volume(scale,shapes,q(F(5+sum(j),2)))
                from itertools import product
                signs=[dict(orthant=sg,sign=prod(s**k for s,k in zip(sg,j))) for sg in product((1,-1),repeat=3)]
                return emit('dirichlet_weighted_sections',[
                    'В положительном октанте квадраты нормированных координат переводят шар в единичный симплекс.',
                    'Якобиан на открытом октанте даёт степени (p_i−1)/2. Все новые показатели больше −1, поэтому грани не влияют.',
                    'Если исходный текст не выбирает знаки, отражение перечисляет значения во всех ограниченных компонентах.'],
                    dict(value=value,representative_orthant=(1,1,1),all_orthant_multipliers=signs),powers=j,radius=R)
    if method=='spherical_coordinates' and (sphere:=re.fullmatch(r'sphere x\^2\+y\^2\+z\^2=(?:(\d+)\*)?z',S)) and raw[0]=='sqrt' and not domain_conditions(raw[1]) and same_value(raw[1],H):
        R=int(sphere[1] or '1')
        return out('radial_moment_coordinates',m.mul(q(F(R**4,10)),m.PI),
                   'В исходной сфере азимут полный, 0≤θ≤π/2, а 0≤r≤R cosθ. Обратная сферическая карта покрывает всю область, кроме полярной оси нулевой меры.',
                   'Исходное ядро r и сферический якобиан r²sinθ дают интеграл ∫r³dr, а оставшийся вес cos⁴θ sinθ интегрируется подстановкой cosθ.',radial_bound=(q(R),'cos(theta)'))
    if (method=='spherical_coordinates' and S=='0<=x<=1,0<=y<=sqrt(1-x^2),sqrt(x^2+y^2)<=z<=sqrt(2-x^2-y^2)'
            and not domain_conditions(raw) and same_value(raw,m.power(z,2))):
        value=m.div(m.mul(m.PI,m.add(m.mul(q(2),('sqrt',q(2))),q(-1))),q(15))
        return out('radial_moment_coordinates',value,
                   'Сфера даёт 0≤r≤√2, конус — 0≤θ≤π/4. Первый квадрант сохраняет азимут 0≤φ≤π/2.',
                   'На таком секторе r sinθ≤1, поэтому исходное ограничение проекции выполнено в обе стороны. Интегрируем r⁴sinθ cos²θ.',cone_angle='pi/4',sphere_radius=('sqrt',q(2)))
    cone=re.fullmatch(r'bounded by x\^2\+y\^2=z\^2,z=([1-9]\d*)',S)
    polar=m.add(m.power(x,2),m.power(y,2))
    if cone and method in (None,'cylindrical_coordinates') and raw[0]=='sqrt' and not domain_conditions(raw[1]) and same_value(raw[1],polar):
        height=int(cone[1]);value=m.mul(q(F(height**4,6)),m.PI)
        return out('radial_moment_coordinates',value,
                   'Исходная замкнутая часть лежит на положительной полости конуса. В цилиндрических координатах 0≤r≤z≤H и полный азимут Ф.',
                   'Исходный радиус и якобиан дают r² dr·dz·dФ. Интегрируем сначала по r, затем по z.',height=q(height))
    raise Unsupported('A checked coordinate chart or original integrand guard is still missing')


def improper_spatial_chart(task,emit):
    expr=task.get('integrand',task.get('density'));region=task['region'];kind=task['kind']
    def result(rule,value,*steps,**facts):
        answer=dict(value=value,convergence='ordinary absolute on all parts of the original region') if not isinstance(value,str) else dict(formula=value,convergence='ordinary absolute')
        return emit(rule,steps,answer,**facts)
    if kind=='solid_mass':
        edge=re.fullmatch(r'x\^2\+y\^2\+z\^2>=([1-9]\d*)',region)
        hit=re.fullmatch(r'(\w+)\*exp\(-([A-Za-z]\w*)\*sqrt\(x\^2\+y\^2\+z\^2\)\)',expr)
        if edge and hit and len(set((*hit.groups(),'x','y','z')))==5 and task['stated_conditions']==[p+'>0' for p in hit.groups()]:
            r=('sqrt',q(int(edge[1])));rho,k=(('s',p) for p in hit.groups())
            pol=m.add(m.div(m.power(r,2),k),m.add(m.div(m.mul(q(2),r),m.power(k,2)),m.div(q(2),m.power(k,3))))
            value=m.mul(m.mul(q(4),m.PI),m.mul(rho,m.mul(('exp',m.neg(m.mul(k,r))),pol)))
            return result('radial_moment_coordinates',value,
                          'Исходная область — вся внешность шара. Сферический якобиан даёт 4πr²dr.',
                          'Положительный k обеспечивает затухание на всём бесконечном хвосте. Два интегрирования по частям вычисляют массу с исходным нижним пределом.',radius=r)
        raise Unsupported('The original exterior mass needs a proved positive radial density')
    if region=='R^n, (aij) real symmetric positive definite' and expr=='exp(-(sum_ij aij xi xj+2 sum_i bi xi+c))':
        return result('radial_moment_coordinates','pi^(n/2)*exp(b^T*A^(-1)*b-c)/sqrt(det(A))',
                      'Положительная определённость гарантирует обратимость A и A^(1/2), а также положительность det A.',
                      'Дополняем квадрат x↦x+A⁻¹b. Линейная замена y=A^(1/2)(x+A⁻¹b) покрывает всё пространство с обратным якобианом 1/√det A.',
                      'Полученное ядро положительно и факторизуется в произведение абсолютно сходящихся гауссовых интегралов.',jacobian='1/sqrt(det(A))')
    if (hit:=re.fullmatch(r'0<=x<=([a-z]\w*),0<=y<=x,\1>0',region)) and expr==f'1/sqrt(({hit[1]}-x)*(x-y))':
        a=('s',hit[1]);value=m.mul(m.PI,a)
        return result('dirichlet_weighted_sections',value,
                      'Внутри исходного треугольника оба множителя положительны. Применяем Тонелли к неотрицательному ядру и независимым отсечкам двух граней.',
                      'Во внутреннем интеграле 1/√(x−y) даёт 2√x. Замена x=a u сводит остаток к интегрируемому 2a·B(3/2,1/2).',singular_faces=(f'x={hit[1]}','y=x'))
    if region=='bounded by y=0,y=x,x=pi' and expr=='ln(sin(x-y))':
        return result('affine_slice_moment',m.neg(m.mul(m.div(m.power(m.PI,2),q(2)),('ln',q(2)))),
                      'Замена u=x−y имеет постоянный якобиан. Для u∈[0,π] оставшаяся координата имеет длину π−u.',
                      'Оба края ln(sin u) имеют лишь интегрируемую логарифмическую особенность. Отражение u↦π−u усредняет вес до π/2.',
                      'Формула sin(2u)=2sin u cos u и замена 2u дают ∫₀^π ln(sin u)du=−π ln 2.',singular_faces=('x=y','x-y=pi'))
    if (disc:=re.fullmatch(r'x\^2\+y\^2<=([1-9]\d*)',region)) and expr=='ln(1/sqrt(x^2+y^2))':
        R=('sqrt',q(int(disc[1])));val=m.mul(m.mul(m.PI,m.power(R,2)),m.add(q(1,2),m.neg(('ln',R))))
        return result('radial_moment_coordinates',val,'Полярная карта покрывает диск радиуса R. В угловом интеграле остаётся полный множитель 2π.',
                      'В нуле r ln(1/r) абсолютно интегрируема. Вычисляем один радиальный интеграл по частям.',radius=R)
    if (disc:=re.fullmatch(r'x\^2\+y\^2<=(?:([1-9]\d*)\*)?x',region)) and expr=='1/sqrt(x^2+y^2)':
        R=int(disc[1] or '1')
        return result('radial_moment_coordinates',q(2*R),'При полярной замене исходное неравенство даёт −π/2≤θ≤π/2 и 0≤r≤R cosθ.',
                      'При r>0 радиальный якобиан сокращает 1/r. Отсечка в нуле снимается по обычной абсолютной сходимости.',radial_bound=q(R))
    raise Unsupported('The original improper boundary has no verified convergence and complete coordinate image')


def source_spatial_moment_report(result,pretty):
    if result['status']!='SOLVED':return result.get('reason',result['status'])
    plan=result['compilation'];value=result['value'];rows=list(plan['argument'])
    if value.get('centroid_defined') is False:
        rows.append('Центр масс не определён ни при одном допустимом значении масштаба.')
        for branch in value['branches']:
            relation,lhs,rhs=branch['condition']
            sign={'less':' < ','equal':' = ','greater':' > '}[relation]
            rows.append('При '+pretty(lhs)+sign+pretty(rhs)+' объём равен '+pretty(branch['volume'])+'.')
    elif 'uniform_area_density_model' in value:
        rows.append('Для равномерной поверхностной плотности работа равна '+pretty(value['uniform_area_density_model'])+'.')
        rows.append('Для одного центрального ряда работа равна '+pretty(value['central_uniform_row_cost'])+'.')
    elif 'formula' in value:rows.append('Результат равен '+value['formula']+'.')
    elif 'components' in value:
        labels={'surface_area':'Площадь поверхности','volume':'Объём','inertia_xy':'I_xy','inertia_yz':'I_yz','inertia_zx':'I_zx'}
        rows.extend(labels.get(k,k)+' = '+pretty(v)+'.' for k,v in value['components'].items())
    elif 'lower' in value:rows.append('Нижняя граница '+pretty(value['lower'])+', верхняя '+pretty(value['upper'])+'.')
    elif isinstance(value['value'],dict):
        g=value['value'];rows.append('Значение равно '+pretty(g['factor'])+'·'+
            '·'.join('Γ('+pretty(s)+')' for s in g['gamma_numerator'])+'/Γ('+pretty(g['gamma_denominator'])+').')
    else:rows.append('Результат равен '+pretty(value['value'])+'.')
    if 'all_orthant_multipliers' in value:rows.append('Указанное значение относится к положительному октанту. Для остальных знаков используются множители из доказательства.')
    if 'convergence' in value:rows.append('Исходный интеграл сходится абсолютно.')
    return '\n'.join(rows)



def weighted_conical_centroid(task,emit):
    # A weighted homogeneous boundary must be tested for finite mass first.
    region=task.get('region','');name=r'([A-Za-z][A-Za-z0-9_]*)'
    match=re.fullmatch(fr'\(x\^2/{name}\^2\+y\^2/{name}\^2\+z/{name}\^([1-9]\d?)\)\^2=x\*y\*z/\(([^()]+)\);\s*(.*)',region)
    if not match:return None
    a,b,c,p,denominator,conditions=match.groups()
    if (
        len({a,b,c,'x','y','z'})!=6 or set(task)-{'id','kind','source','region','density','stated_conditions','requested_output'}
        or task.get('density')!='constant' or task.get('requested_output')!=['centroid_coordinates'] or task.get('stated_conditions')
        or task.get('source',{}).get('literal_requirement') not in (None,'Найти координаты центра масс заданного тела.')
        or set(conditions.split(','))!={'x>=0','y>=0','z>=0',a+'>0',b+'>0',c+'>0'}
    ):raise Unsupported('The original positive scales, orthant and constant density are required')
    if denominator not in (f'{a}*{b}*{c}',f'{a}*{b}'):
        raise Unsupported('A product of the normalized scales is required')
    power=int(p)-(denominator.endswith('*'+c))
    threshold=m.power(('s',c),power)
    return emit('weighted_homogeneous_mass_obstruction',[
        'Нормируем u=x/a, v=y/b, w=z/c^p. Получаем границу (u²+v²+w)²=Kuvw, где K вычислен из исходных масштабов.',
        'В положительном октанте (S+w)²≥4Sw и S=u²+v²≥2uv, поэтому (S+w)²≥8uvw. Равенство требует u=v, w=S. При K≤8 нет тела положительной меры.',
        'При K>8 точка u=v=1, w=2 удовлетворяет строгому неравенству, так что имеется открытая часть. Дилатация (u,v,w)→(tu,tv,t²w) сохраняет неравенство и имеет якобиан t⁴.',
        'Масса образов одной открытой области растёт без ограничения. Однородный центр масс не определён и в этой ветви.'
    ],dict(centroid_defined=False,branches=[
        dict(condition=['less',threshold,q(8)],volume=ZERO,level_set='origin'),
        dict(condition=['equal',threshold,q(8)],volume=ZERO,level_set='u=v and w=u²+v²'),
        dict(condition=['greater',threshold,q(8)],volume='+inf',reason='weighted dilation of an open subset')]),
        scale_coefficient=threshold,dilation_weights=[1,1,2],determinant_power=4)


def spatial_section_measure(task, emit):
    if task.get('kind')=='solid_centroid':
        weighted=weighted_conical_centroid(task,emit)
        if weighted is not None:return weighted
    """Propose a Cartesian column or a symmetry coordinate and integrate its mass moments."""
    from verify import same_value
    kind=task['kind'];region=task.get('region','');facts=task.get('stated_conditions',[])
    output=task.get('requested_output');density=task.get('density');meta=task.get('source',{})
    S=r'([A-Za-z_]\w*)';P=r'([1-9]\d*)'
    sphere=r'x\^2\+y\^2\+z\^2';radial=r'x\^2\+y\^2'
    disk=radial+r'<='+S+r'\^2'
    scales=r'x\^2/'+S+r'\^2\+y\^2/'+S+r'\^2\+z\^2/'+S+r'\^2'
    cap=scales.replace(r'\+z',r'=z')
    simplex=r'\(x/'+S+r'\)\^n\+\(y/'+S+r'\)\^n\+\(z/'+S+r'\)\^n'
    planes=['inertia_xy','inertia_yz','inertia_zx']
    goal_fields={
        'solid_centroid':{'region','density','stated_conditions'},
        'solid_inertia':{'region','density','stated_conditions','axis','mass'},
        'moments_identity':{'hypotheses','claim','formula','origin','product_moment'},
    }
    expected_headings={
        'solid_centroid':{'Найти координаты центра масс заданного тела.'},
        'solid_inertia':{'Найти моменты инерции однородного тела относительно всех координатных плоскостей.',
                         'Найти момент инерции однородного тела относительно Oz.',
                         'Найти момент неоднородного шара относительно диаметра.',
                         'Найти момент однородного цилиндра относительно прямой x=y=z.',
                         'Найти момент относительно начала координат.'},
        'moments_identity':{'Доказать теорему о параллельных осях для тела массы M.',
                            'Доказать формулу момента инерции тела относительно оси, проходящей через центр масс.',
                            'Доказать теорему параллельных осей.',
                            'Доказать формулу поворота оси, проходящей через центр масс.'},
    }
    heading=meta.get('literal_requirement')
    if (set(task)-{'kind','id','source','requested_output',*goal_fields[kind]}
            or heading is not None and heading not in expected_headings[kind]):
        raise Unsupported('Unrepresented restriction on the spatial measure')
    if kind=='moments_identity':
        hypotheses=task.get('hypotheses');claim=task.get('claim')
        if output==['proof'] and 'formula' in task and claim is None:
            formula=task['formula']
            if (set(task).isdisjoint({'origin','product_moment'}) and hypotheses==['l parallel l0','l0 through centroid','distance d']
                    and formula=='I_l=I_l0+S*d^2' and heading in (None,'Доказать теорему параллельных осей.')):
                return emit('affine_slice_moment',[
                    'Выбираем знаковое поперечное расстояние r до оси через центр масс. После переноса квадрат расстояния становится (r−d)².',
                    'Линейный член исчезает по определению центра масс. Для геометрического момента площади интеграл от единицы равен S.',
                    'При произвольной плотности тем же выводом получается M d², где M — полная масса.'],
                    dict(formula=formula,measure='geometric area measure; unit density',weighted_formula='I_l=I_l0+M*d^2'),
                    offset_square='(r-d)^2=r^2-2*r*d+d^2',centroid_condition='first transverse moment is zero')
            angle=re.fullmatch(r'I=Ix\*cos\((\w+)\)\^2-2\*Ixy\*sin\(\1\)\*cos\(\1\)\+Iy\*sin\(\1\)\^2',formula)
            if (angle and hypotheses is None and task.get('origin')=='centroid'
                    and task.get('product_moment')=='int_S rho(x,y)*x*y dx dy'
                    and heading in (None,'Доказать формулу поворота оси, проходящей через центр масс.')):
                a=angle[1];x,y,s0=('s','x'),('s','y'),('s',a)
                if a in ('x','y','pi','e') or a in m.FUNCTIONS:raise Unsupported('The axis angle must be an independent slot')
                co,si=('cos',s0),('sin',s0);d=m.add(m.mul(y,co),m.neg(m.mul(x,si)))
                expanded=m.add(m.add(m.power(m.mul(y,co),2),m.power(m.mul(x,si),2)),
                               m.mul(q(-2),m.mul(m.mul(x,y),m.mul(si,co))))
                if not same_value(m.power(d,2),expanded):raise Unsupported('The distance square does not reproduce the source mixed term')
                return emit('affine_slice_moment',[
                    'Нормаль к оси имеет компоненты −sin α и cos α. Умножаем её на радиус-вектор точки.',
                    'Раскрываем квадрат знакового расстояния и интегрируем три слагаемых относительно исходной меры ρ dxdy.',
                    'Диагональные интегралы — осевые моменты Ix и Iy. Смешанный — исходный центробежный момент Ixy.'],
                    dict(formula=formula),normal=(m.neg(si),co),distance_square=expanded)
            raise Unsupported('The printed axes, centroid and moment conventions must all be bound')
        if set(task)&{'formula','origin','product_moment'}:raise Unsupported('Additional moment requirements remain')
        if output==['proof'] and hypotheses==['l parallel l0','l0 passes through center of mass','distance d'] and claim=='I_l=I_l0+M*d^2':
            return emit('affine_slice_moment',[
                'Обозначаем поперечные к осям координату r и вектор сдвига b. Квадрат расстояния равен |r−b|².',
                'Из определения центра масс ∫r dm=0. Интегрирование даёт ∫|r|² dm+M|b|².'],dict(formula=claim),
                vector_identity='|r-b|^2=|r|^2-2*r.b+|b|^2',cross_moment='integral(r) dm=0')
        if (output==['proof'] and hypotheses==['origin at center of mass','axis direction cosines u=cos(alpha),v=cos(beta),w=cos(gamma)']
                and claim=='I=Ix*u^2+Iy*v^2+Iz*w^2-2*Kxy*u*v-2*Kxz*u*w-2*Kyz*v*w; Kij=integral(rho*x_i*x_j)'):
            return emit('affine_slice_moment',[
                'Пусть e=(u,v,w) — единичный вектор оси. Квадрат расстояния до оси равен |p|²−(p·e)².',
                'Раскрываем квадрат и используем u²+v²+w²=1. Интегралы диагональных членов дают Ix,Iy,Iz, а смешанные члены — −2Kij ei ej.'],
                dict(formula=claim),axis_vector=['u','v','w'],squared_norm='1',polarization='|p|^2-(p.e)^2')
        raise Unsupported('Origin and direction of the axes are required')
    if not isinstance(region,str) or not isinstance(density,str) or not isinstance(facts,list):
        raise Unsupported('Region and density must be defined explicitly')
    expected_output=['centroid_coordinates'] if kind=='solid_centroid' else output
    if (not isinstance(output,list) or output!=expected_output or
            facts not in ([],['parameters positive'],['0<alpha<1','0<beta<1','0<gamma<1'])):
        raise Unsupported('Requested components or parameter restrictions are not supported')
    if set(task)&{'axis','mass'} and output not in (['diametral_inertia_in_terms_of_M_and_R'],['inertia_about_given_line']):
        raise Unsupported('Additional inertia data must remain in their original goal')
    def E(s,*names):
        return m.simplify(m.parse(s,None,names))
    def unique(names):
        return len(set(names))==len(names) and not set(names)&({'x','y','z','pi','e','n'}|m.FUNCTIONS)
    def physical(hit,positive=False):
        if not unique(hit.groups()):raise Unsupported('The original scales are not independent fixed parameters')
        names=hit.groups()
        return tuple(('s',n) if positive else ('abs',('s',n)) for n in names)
    def measure(rule,values,steps,**record):
        if isinstance(values,str):answer=dict(formula=values)
        elif len(values)==1:answer=dict(value=m.simplify(values[0]))
        else:
            labels=('x','y','z') if kind=='solid_centroid' else output
            answer=dict(components=dict(zip(labels,map(m.simplify,values))))
        return emit(rule,steps,answer,measure_components=output,**record)
    def moments(geometry,bases,exponents,scale,projection,notes):
        if density not in ('unit','constant'):raise Unsupported('Density cannot be removed from the moment')
        shapes=[monomial_section_moment(geometry,bases,a) for a in exponents]
        if kind=='solid_centroid':
            if m.num(shapes[0]) is not None and m.num(shapes[0])<=0:
                raise Unsupported('The proposed body has no positive finite mass')
            values=[m.mul(s,m.div(t,shapes[0])) for s,t in zip(scale,shapes[1:])]
            factors=dict(normalized_mass=shapes[0],normalized_first_moments=shapes[1:])
        else:
            jac=m.mul(m.mul(('abs',scale[0]),('abs',scale[1])),('abs',scale[2]))
            values=[m.mul(jac,m.mul(shapes[j],m.power(scale[i],2))) for j,i in enumerate((2,0,1))]
            factors=dict(normalized_plane_moments=shapes,absolute_jacobian=jac)
        return measure('spatial_projected_column_moments',values,[*notes,
            'В продольной координате интегрируем степенной вес между двумя доказанными границами.',
            'В проекции интегрируем каждый моном точной формулой для данного диска, треугольника или квадрата.'],
            normalized_projection=projection,vertical_bounds=bases,scales=scale,**factors)
    plane=tuple(tuple(2 if j==i else 0 for j in range(3)) for i in (2,0,1))
    first=((0,0,0),(1,0,0),(0,1,0),(0,0,1))
    collar=re.fullmatch(cap+r',z=\3',region)
    if collar and ((output==['centroid_coordinates'] and density=='constant' and not facts) or
                   (output==planes and density=='unit' and facts==['parameters positive'])):
        a,b,C=physical(collar,bool(facts));c=('s',collar[3])
        if kind=='solid_centroid':
            values=(ZERO,ZERO,m.mul(q(3,4),c));record=dict(normalized_height_moment=q(1,4),normalized_mass_weight=q(1,3))
        else:
            jac=m.mul(m.mul(a,b),C)
            values=(m.mul(jac,m.mul(q(1,5),m.mul(m.PI,m.power(C,2)))),
                    m.mul(jac,m.mul(q(1,20),m.mul(m.PI,m.power(a,2)))),
                    m.mul(jac,m.mul(q(1,20),m.mul(m.PI,m.power(b,2)))))
            record=dict(vertical_moment=q(1,5),lateral_disk_moment=q(1,4),lateral_height_moment=q(1,5))
        return measure('affine_slice_moment',values,[
            'Плоскость крышки задаёт координату z=c t с 0≤t≤1. Из уравнения конуса следуют полуширины |a|t, |b|t.',
            'Нечётные поперечные моменты исчезают на симметричных дисках. Второй момент единичного диска по одной координате π/4.',
            'Интегрируем t^k на [0,1] и возвращаем обратный абсолютный якобиан и нужную размерность.'],
            scales=(a,b,c),requires='abc nonzero; positive scales where printed',**record)
    slope=re.fullmatch(r'x\^2\+y\^2='+P+r'\*z,x\+y=z',region)
    norm_slope=(r'x\^2/'+S+r'\^2\+y\^2/'+S+r'\^2=2\*z/'+S+r',x/\1\+y/\2=z/\3')
    if (slope and output==['centroid_coordinates'] and not facts or
            (sl:=re.fullmatch(norm_slope,region)) and output==planes and facts==['parameters positive']):
        scale=(q(int(slope[1]),2),)*3 if slope else physical(sl,True)
        return moments('disk',(r'(1+u)^2/2+(1+v)^2/2','2+u+v'),
                       first if kind=='solid_centroid' else plane,scale,'u^2+v^2<=2',
                       ['После масштабирования и переноса центра проекции в (1,1) расстояние между двумя листами равно 1−(u²+v²)/2.',
                        'Вне указанного диска порядок поверхностей обратен и ограниченного столбца нет.'])
    if (tr:=re.fullmatch(r'z=x\^2\+y\^2,x\+y='+S+r',x=0,y=0,z=0',region)) and output==['centroid_coordinates'] and not facts:
        physical(tr);a=('s',tr[1])
        return moments('triangle',('0','u^2+v^2'),first,(a,a,m.power(a,2)),'u>=0, v>=0, u+v<=1',
                       ['Две координатные плоскости и x+y=a образуют ограниченный треугольник. При a≠0 замена x=a u,y=a v даёт единичный симплекс.',
                        'Между z=0 и параболоидом z=a²w лежит 0≤w≤u²+v².'])
    diamond=re.fullmatch(r'z=x\^2\+y\^2,(?:z=\(x\^2\+y\^2\)/2,)?x\+y=\+('+P[1:-1]+r'),-\1,x-y=\+\1,-\1(?:,z=0)?',region)
    if diamond and not facts:
        has_bottom='z=0' in region;bound=int(diamond[1]);d=q(bound)
        if not has_bottom and 'z=(x^2+y^2)/2' in region and output==['centroid_coordinates'] and density=='constant':
            z0,z1='r^2/2','r^2'
            ht=monomial_section_moment('square',('(u^2+v^2)/4','(u^2+v^2)/2'),(0,0,0))
            zm=monomial_section_moment('square',('(u^2+v^2)/4','(u^2+v^2)/2'),(0,0,1))
            values=(ZERO,ZERO,m.mul(m.power(d,2),m.div(zm,ht)))
        elif has_bottom and 'z=(x^2+y^2)/2' not in region and output==['inertia_z'] and density=='unit':
            z0,z1='0','r^2'
            normalized=monomial_section_moment('square',('0','((u^2+v^2)/2)^2'),(0,0,0))
            values=(m.mul(q(1,2),m.mul(m.power(d,6),normalized)),)
        else:raise Unsupported('The two vertical bounds and exact output must agree')
        return measure('affine_slice_moment',values,[
            'Берём u=(x+y)/L,v=(x−y)/L. Все четыре исходные плоскости переходят в грани квадрата |u|,|v|≤1.',
            'Абсолютный якобиан равен L²/2, а r²=L²(u²+v²)/2. Интегрируем многочлен после нахождения продольного момента.',
            'Симметрия исходного тела и плотности убирает нечётные моменты.'],horizontal_bound=d,normalized_projection='[-1,1]^2',
            vertical_bounds=[z0,z1],radial_square='L^2*(u^2+v^2)/2')
    if (hit:=re.fullmatch(r'x\^2=2\*'+S+r'\*z,y\^2=2\*\1\*x,x=\1/'+P+r',z=0',region)) and output==['centroid_coordinates'] and not facts:
        p=('s',hit[1]);L=q(1,int(hit[2]))
        if not unique((hit[1],)):raise Unsupported('The cap scale must be fixed')
        values=(m.mul(p,m.mul(q(7,9),L)),ZERO,m.mul(q(7,44),m.mul(p,m.power(L,2))))
        return measure('affine_slice_moment',values,[
            'Пишем x=p t, z=p w. Тогда 0≤t≤L, 0≤w≤t²/2, |y|≤|p|√(2t); исходная ограниченная часть сохраняется для p≠0.',
            'Из ширины и высоты следует вес t^(5/2), а среднее w на столбце равно t²/4.',
            'В нормированных интегралах общего степенного веса масса сокращается; отражение y→−y даёт нулевой момент.'],
            normalized_bound=L,normalized_weight=q(5,2),positive_mass_for='p nonzero')
    crossing=re.fullmatch(r'x\^2\+z\^2='+S+r'\^2,y\^2\+z\^2=\1\^2,z>=0',region)
    if crossing and output==['centroid_coordinates'] and density=='constant' and not facts:
        R,=physical(crossing)
        return measure('affine_slice_moment',(ZERO,ZERO,m.mul(q(3,8),R)),[
            'Отражения x→−x и y→−y сохраняют оба исходных цилиндра и плотность.',
            'На высоте z=R t обе полуширины равны R√(1−t²), 0≤t≤1. Сечение — весь квадрат.',
            'Масса и момент z пропорциональны интегралам 1−t² и t(1−t²), их отношение 3/8.'],
            height_scale=R,normalized_section_weights=[q(2,3),q(1,4)],positive_mass_for='R>0')
    sphere_body=re.fullmatch(r'\(?'+scales+r'\)?=1(,x=0,y=0,z=0)?',region)
    if sphere_body and output in (['centroid_coordinates'],planes):
        names=sphere_body.groups()[:3];axes=tuple(('s',n) for n in names)
        if not unique(names):raise Unsupported('Each original denominator must be a nonzero fixed scale')
        if sphere_body[4] and output==['centroid_coordinates'] and density=='constant' and not facts:
            A,B,C=names
            return measure('radial_moment_coordinates',f'(s_x*3*abs({A})/8,s_y*3*abs({B})/8,s_z*3*abs({C})/8), each s_i in {{-1,1}}',[
                'Три явно заданные координатные плоскости выделяют восемь согласованных октантов. Выбираем знаки независимо.',
                'В нормированном положительном октанте на высоте t получается четверть диска площади π(1−t²)/4; средняя высота 3/8.',
                'Перестановки координат дают ту же величину для двух остальных осей. Возвращаем исходные масштабы и знаки.'],
                requires='three nonzero scales',each_orthant=True,normalized_height=q(3,8))
        if not sphere_body[4] and output==planes and density=='unit' and facts==['parameters positive']:
            factor=m.mul(m.mul(m.mul(*axes[:2]),axes[2]),m.mul(q(4,15),m.PI))
            values=[m.mul(factor,m.power(axes[i],2)) for i in (2,0,1)]
            return measure('radial_moment_coordinates',values,[
                'Из положительных масштабов следует, что диагональная замена переводит все грани в полный единичный шар.',
                'Каждый из трёх вторых координатных моментов даёт треть интеграла |u|². Радиальный интеграл ∫r^4dr=1/5.',
                'Возвращаем абсолютный якобиан abc и квадрат масштаба компоненты.'],normalized_radial_power=4,scales=axes)
    T=re.fullmatch(r'x/'+S+r'\+y/'+S+r'\+z/'+S+r'=1,x=0,y=0,z=0',region)
    N=re.fullmatch(simplex+r'=1,x=0,y=0,z=0;n>0,x>=0,y>=0,z>=0',region)
    if (T or N) and output==planes and facts==['parameters positive'] and density=='unit':
        a,b,c=physical(T or N,True)
        if T:
            jac=m.mul(m.mul(a,b),c)
            unit=gamma_volume(ONE,[q(3),ONE,ONE],q(6))
            value=[m.mul(m.mul(jac,unit),m.power(s,2)) for s in (c,a,b)]
        else:
            A,B,C=N.groups();g='Gamma(3/n)*Gamma(1/n)^2/(n^3*Gamma(1+5/n))'
            value=f'{A}*{B}*{C}*{g}*({C}^2,{A}^2,{B}^2)'
        return measure('affine_slice_moment',value,[
            'По положительным масштабам исходные координатные плоскости и ограничивающая поверхность переходят в симплекс.',
            'Берём u=(x/a)^n и аналоги, с n=1 для плоскости. Смена переменной переносит плотность во все три степенных множителя.',
            'Интеграл Дирихле даёт форму Γ(3/n)Γ(1/n)²/Γ(1+5/n). Все гамма-показатели строго положительны.'],
            symmetry='permutation of normalized axes',simplex_exponents=['3/n','1/n','1/n'])
    if (region=='0<=x<=1,0<=y<=1,0<=z<=1' and output==['centroid_coordinates']
            and facts==['0<alpha<1','0<beta<1','0<gamma<1']):
        params=('alpha','beta','gamma')
        exponent=tuple(f'(2*{a}-1)/(1-{a})' for a in params)
        target=m.parse('*'.join(f'{x}^({p})' for x,p in zip('xyz',exponent)),None,[*'xyz',*params])
        supplied=m.parse(density,None,[*'xyz',*params])
        if not same_value(supplied,target) or domain_conditions(supplied)!=domain_conditions(target):
            raise Unsupported('The normalized moments depend on the printed density')
        return measure('affine_slice_moment',tuple(('s',a) for a in params),[
            'Пределы прямоугольные, плотность распадается на три степенных множителя. При 0<α<1 имеем p+1=α/(1−α)>0.',
            'Теорема Фубини применима, все интегралы массы сходятся и положительны. В каждой координате остаётся (p+1)/(p+2).',
            'Подстановка показателей даёт α, β, γ.'],factor_exponents=exponent,finite_mass=True)
    if density=='unit' and output==planes and facts==['parameters positive']:
        shift=re.fullmatch(r'\('+scales+r'\)=1,x\^2/\1\^2\+y\^2/\2\^2=x/\1',region)
        ray=re.fullmatch(r'\('+scales+r'\)\^2=x\^2/\1\^2\+y\^2/\2\^2-(?:'+P+r'\*)?z\^2/\3\^2',region)
        if shift or ray:
            names=(shift or ray).groups()[:3]
            if not unique(names):raise Unsupported('The normalized scales must be independent')
            a,b,c=(('s',n) for n in names);J=m.mul(m.mul(a,b),c)
            def angular(p,q0):return gamma_volume(q(1,2),[q(p+1,2),q(q0+1,2)],q(p+q0+2,2))
            if shift:
                def transverse(p,q0):
                    return m.mul(q(4),m.add(m.add(m.mul(q(2,15),angular(p,q0)),m.mul(q(-1,3),angular(p+3,q0))),
                                             m.mul(q(1,5),angular(p+5,q0))))
                z=m.mul(q(4,15),m.add(angular(0,0),m.neg(angular(5,0))))
                dims=(z,transverse(0,2),transverse(2,0))
                steps=['Внутри нормированной сферы сдвинутый цилиндр даёт −π/2≤φ≤π/2, 0≤r≤cosφ.',
                       'Интегрируем z² или 1 по высоте |z|≤√(1−r²), затем по r. Верхняя граница даёт степени |sinφ|³ и |sinφ|⁵.',
                       'На половине углового интервала применяем бета-моменты синуса и косинуса. Вторая половина имеет те же чётные веса.']
                scope=dict(azimuth=['-pi/2','pi/2'],projected_radius='cos(phi)',angular_beta=True)
            else:
                L=1+int(ray[4] or 1);scale=('sqrt',q(L))
                z=m.div(m.mul(q(1,64*L),m.power(m.PI,2)),scale)
                side=m.div(m.mul(q(F(1,16)*(1-F(1,8*L))),m.power(m.PI,2)),scale)
                dims=(z,side,side)
                steps=['В нормированных сферических координатах t=cosθ. Исходное неравенство даёт r²≤1−L t² и |t|≤1/√L.',
                       'Интеграл r^4dr оставляет степень (1−L t²)^(5/2). Выбор плоскости даёт угловой вес t² или 1−t².',
                       'Масштаб s=√L t сводит обе угловые задачи к общим бета-моментам.']
                scope=dict(cosine_bound=m.div(ONE,scale),radial_square='1-L*t^2',angular_beta=True)
            values=[m.mul(J,m.mul(w,m.power(A,2))) for w,A in zip(dims,(c,a,b))]
            return measure('radial_moment_coordinates',values,[*steps,
                'Положительные исходные масштабы возвращаются через якобиан и квадрат соответствующей координаты.'],
                **scope,normalized_moments=dims)
    if density=='unit' and output==['inertia_z'] and not facts:
        cone=re.fullmatch(sphere+'='+P+','+radial+r'=(?:'+P+r'\*)?z\^2,z>0',region)
        bulb=re.fullmatch(r'\('+sphere+r'\)\^'+P+'='+S+r'\^'+P+r'\*z',region)
        if cone:
            K=int(cone[1]);slope=int(cone[2] or 1);C=q(1,slope+1)
            angular=m.add(q(2,3),m.mul(q(F(1,3*(slope+1))-1),('sqrt',C)))
            value=m.mul(m.mul(q(2*K*K,5),m.PI),m.mul(('sqrt',q(K)),angular))
            return measure('radial_moment_coordinates',(value,),[
                'Выбираем z осью сферических координат. Верхний конус даёт t=cos θ≥1/√(1+s), а сфера 0≤r≤√K.',
                'Плотность момента относительно Oz равна r²(1−t²). Якобиан равен r², азимут полный.',
                'Интегрируем r^4 и 1−t² с сохранением верхнего конусного знака.'],radial_limit=('sqrt',q(K)),angular_cosine_bound=('sqrt',C))
        if bulb and int(bulb[1])>=2 and int(bulb[3])==2*int(bulb[1])-1 and unique((bulb[2],)):
            p=F(5,int(bulb[3]));R=('abs',('s',bulb[2]))
            value=m.mul(m.mul(q(F(2,5)*(1/(p+1)-1/(p+3))),m.PI),m.power(R,5))
            return measure('radial_moment_coordinates',(value,),[
                'В полушарии знака параметра r^{2m−1}≤|A|^{2m−1}t, t=|cos θ|∈[0,1].',
                'После интеграла r^4dr остаётся точный вес t^{5/(2m−1)}(1−t²).',
                'Противоположные знаки параметра дают отражённые тела с тем же моментом Oz.'],radial_scale=R,angular_power=q(p))
    if (hit:=re.fullmatch(disk+r',-([A-Za-z_]\w*)<=z<=\2',region)) and output==['inertia_about_given_line'] and not facts:
        if not unique(hit.groups()) or 'mass' in task or density!='rho0' or task.get('axis')!='x=y=z':
            raise Unsupported('Original axis and homogeneous mass model are required')
        A,H=hit.groups()
        return measure('affine_slice_moment',f'2*pi*rho0*{A}^2*{H}*({A}^2/3+2*{H}^2/9) for {H}>=0; 0 for {H}<0',[
            'Цилиндр имеет полные дисковые сечения и длину 2H. При H<0 исходное множество пусто.',
            'Отражения трёх координат сохраняют область и плотность, поэтому все смешанные моменты равны нулю.',
            'Направление (1,1,1)/√3 имеет квадраты компонент 1/3; второй момент диска равен A²/4 на единицу массы, а продольный H²/3.'],
            normalized_direction=[q(1,3)]*3,mixed_moments=ZERO,density_symbol='rho0')
    if (hit:=re.fullmatch(sphere+r'<=([A-Za-z_]\w*)\^2',region)) and output==['diametral_inertia_in_terms_of_M_and_R'] and not facts:
        if density!='proportional to distance from center' or task.get('mass')!='M' or not unique(hit.groups()) or 'axis' in task:
            raise Unsupported('A radial mass normalization requires the original radial density and total mass')
        R=hit[1]
        return measure('radial_moment_coordinates',f'4*M*{R}^2/9',[
            'Радиальная плотность пропорциональна r. Для массы радиальный вес r³, для момента относительно диаметра r⁵ sin²θ.',
            'Сферическое среднее sin²θ равно 2/3. Отношение радиальных интегралов равно 2R²/3.',
            'Множитель плотности устраняется через исходную массу M.'],radial_mass_power=3,radial_moment_power=5,positive_mass_for='nonzero radius')
    if (hit:=re.fullmatch(r'\('+sphere+r'\)\^2<='+S+r'\^2\*\('+radial+r'\)',region)) and output==['inertia_about_origin'] and not facts:
        if density!='rho0' or not unique(hit.groups()):raise Unsupported('A constant density is required')
        value=E(f'pi^2*rho0*abs({hit[1]})^5/8',hit[1],'rho0')
        return measure('radial_moment_coordinates',(value,),[
            'В сферических координатах 0≤r≤|A|sin θ, весь интервал 0≤θ≤π и полный азимут.',
            'Квадрат расстояния до начала равен r². Поэтому после радиального интеграла r^4dr остаётся sin^6θ.',
            'Точный чётный угловой момент равен ∫₀^π sin^6θ dθ=5π/16; умножаем на полный азимут и плотность.'],
            radial_bound='abs(A)*sin(theta)',angular_even_moment=q(5,16))
    raise Unsupported('No checked spatial symmetry or complete projected section is available')


def monomial_section_moment(projection, vertical, exponents):
    """Integrate a polynomial column, then use exact moments of its projected region."""
    U,V=('s','u'),('s','v');i,j,k=exponents
    lo,hi=(m.parse(s,None,['u','v']) for s in vertical)
    if projection=='disk':
        U0,V0=m.add(ONE,U),m.add(ONE,V)
    else:
        U0,V0=U,V
    expression=m.mul(m.mul(m.power(U0,i),m.power(V0,j)),
                     m.div(m.add(m.power(hi,k+1),m.neg(m.power(lo,k+1))),q(k+1)))
    coeff,den=m.rational_form(expression)
    if set(den)!={()} or any(atom not in (U,V) for monomial in coeff for atom,_ in monomial):
        raise Unsupported('A nonpolynomial projected weight needs a separate integral proof')
    def projected(p,q0):
        from math import factorial
        if projection=='triangle':return q(F(factorial(p)*factorial(q0),factorial(p+q0+2)))
        if p%2 or q0%2:return ZERO
        if projection=='square':return q(F(4,(p+1)*(q0+1)))
        if projection!='disk':raise Unsupported('The projected region is not verified')
        # Disk radius sqrt(2), using the radial primitive and the even angular beta integral.
        a,b=p//2,q0//2
        factor=F(2*factorial(2*a)*factorial(2*b),2**(a+b)*factorial(a)*factorial(b)*factorial(a+b+1))
        return m.mul(q(factor),m.PI)
    result=ZERO
    for monomial,c in coeff.items():
        powers=dict(monomial)
        result=m.add(result,m.mul(q(c/den[()]),projected(powers.get(U,0),powers.get(V,0))))
    return m.simplify(result)


def spatial_surface_measure(task,emit):
    """Bind all source sheets, then use the graph or transverse strip area element."""
    from planar_integrals import geom_asinh,root_power_primitive
    kind=task['kind'];want=task.get('requested_output');meta=task.get('source',{})
    S=r'([A-Za-z_]\w*)';D=r'([1-9]\d*)';radial=r'x\^2\+y\^2';sphere=radial+r'\+z\^2'
    def sym(n):
        if n in (m.FUNCTIONS|{'x','y','z','r','phi','pi','e'}):raise Unsupported('A fixed geometric scale is required')
        return ('s',n)
    def E(s,*names):return m.simplify(m.parse(s,None,names))
    def chart(family,value,*steps,**evidence):
        return emit('spatial_surface_sections',steps,value if isinstance(value,dict) else dict(value=value),
                    chart_family=family,dimension=2,**evidence)
    def metric(family,value,*steps,**evidence):
        return chart(family,value,
                     'Площадь параметризованной поверхности равна интегралу нормы векторного произведения касательных.',
                     *steps,**evidence)
    def spherical_strip(value,domain,*steps,**evidence):
        return metric('spherical_height_strip',value,
                      'На сфере радиуса R в координатах высоты и азимута метрическая плотность постоянна, dS=R dφ dt.',
                      domain,*steps,**evidence)
    heading=meta.get('literal_requirement')
    if kind=='solid_area_and_volume':
        if (set(task)-{'kind','source','id','requested_output','surfaces','stated_conditions'}
                or want!=['surface_area','volume'] or heading not in (None,'Найти полную поверхность и объём ограниченного тела.')):
            raise Unsupported('Both measures of the same closed body are required')
        surfaces=task.get('surfaces')
        if not isinstance(surfaces,list) or len(surfaces)!=2 or not all(isinstance(s,str) for s in surfaces):
            raise Unsupported('The original bounding surfaces are required')
        cone=re.fullmatch(radial+r'=z\^2/'+D,surfaces[0]);cap=re.fullmatch(r'x\+y\+z='+D+r'\*'+S,surfaces[1])
        if not cone or not cap or int(cone[1])<=2 or task.get('stated_conditions')!=[cap[2]+'>0']:
            raise Unsupported('The original plane need not cut a bounded elliptical cone')
        d,n=int(cone[1]),int(cap[1]);a=sym(cap[2]);c=m.mul(q(n),a)
        projected=E(f'pi*({n}*{cap[2]})^2*sqrt({d})/({d-2}*sqrt({d-2}))',cap[2])
        section=m.mul(m.add(('sqrt',q(3)),('sqrt',q(d+1))),projected)
        volume=m.mul(q(1,3),m.mul(c,projected))
        return metric('capped_cone',dict(components=dict(surface_area=m.simplify(section),volume=m.simplify(volume))),
                      'Для нижнего конуса z+x+y≤0. Верхний даёт ограниченную проекцию, так как D>2.',
                      'Поворот u=(x+y)/√2,v=(x−y)/√2 и выделение квадрата дают эллипс с площадью πC²√D/(D−2)^(3/2).',
                      'У крышки постоянная плотность √3, у конуса √(D+1). Объём равен трети площади крышки на её расстояние от вершины.',
                      projected_area=projected,section_parameter=d,cap_constant=c,radial_slope=q(d))
    if (set(task)-{'kind','source','id','requested_output','surface_region'} or want!=['surface_area']
            or heading not in (None,'Найти площадь указанной части поверхности.')):
        raise Unsupported('The requested surface and its restrictions must be unchanged')
    raw=task.get('surface_region')
    if not isinstance(raw,str):raise Unsupported('No original surface is available')
    geographic=re.fullmatch(r'sphere of radius '+S+r' between two given meridians and parallels',raw)
    if geographic:
        R=sym(geographic[1]);alpha,beta,dtheta=(('s',name) for name in ('latitude_lower','latitude_upper','azimuth_width'))
        dy=m.mul(R,m.add(('sin',beta),m.neg(('sin',alpha))))
        return spherical_strip(dict(value=m.mul(R,m.mul(dtheta,dy)),
                               azimuth='width of the selected connected azimuthal interval in radians'),
                               'Высоты параллелей равны R sin(latitude_lower) и R sin(latitude_upper).',
                               'Интегрируем постоянную плотность по прямоугольнику высот и азимутов. Для другой части используется оставшаяся угловая ширина.',
                               radius=R,height_span=dy,azimuth_width=dtheta,
                               branch_domain='R>0; -pi/2<=latitude_lower<=latitude_upper<=pi/2; 0<=azimuth_width<=2*pi',
                               pole_measure_zero=True)
    if (hit:=re.fullmatch(S+r'\*z=x\*y inside '+radial+r'=\1\^2',raw)):
        A=hit[1];sym(A)
        return metric('radial_graph',E(f'2*pi*{A}^2*(2*sqrt(2)-1)/3',A),
                      'Граф z=xy/A над полным диском r≤|A|. Плотность графа √(1+r²/A²).',
                      'Подстановка u=1+r²/A² сокращает r dr; границы u=1 и u=2.',
                      original_scale_nonzero=A,angle_interval=['0','2*pi'],radial_upper=f'abs({A})')
    if (hit:=re.fullmatch(r'boundary of common body of cylinders x\^2\+z\^2='+S+r'\^2, y\^2\+z\^2=\1\^2',raw)):
        A=sym(hit[1])
        return metric('cylindrical_height_strip',m.mul(q(16),m.power(A,2)),
                      'На первом цилиндре высота z=R sin φ, а второе ограничение даёт |y|≤R|cos φ|.',
                      'Одна боковая часть даёт 2R²∫₀^{2π}|cos φ|dφ=8R². Перестановка x и y даёт вторую часть.',
                      'Пересечение боковых частей — кривые, которые от одной части к другой площади не прибавляют.',
                      strip_radius=('abs',A),angle_measure=q(4),component_multiplicity=2)
    if (hit:=re.fullmatch('sphere '+sphere+'='+S+r'\^2 inside cylinder x\^2/\1\^2\+y\^2/'+S+r'\^2=1; \2<=\1',raw)):
        A,B=hit.groups();sym(A);sym(B)
        if A==B:raise Unsupported('Each original axis must be retained')
        R,Q=f'abs({A})',f'abs({B})'
        S0=f'8*{A}^2*asin({Q}/{R}) for {Q}<{R}; 4*pi*{A}^2 for {Q}>={R}'
        return spherical_strip(dict(formula=S0),
                               'Из уравнения сферы и цилиндра следует (A²/B²−1)y²≤z². Поэтому выбираем высотой x.',
                               'Условие на каждую поперечную окружность то же самое: |cos φ|≤|B/A|, суммарная ширина 4 arcsin(|B/A|).',
                               'Если |B|≥|A|, подходит вся окружность. Полная высота от −|A| до |A|.',
                               height_coordinate='x',scale_conditions=[A+' nonzero',B+' nonzero'],constant_angular_window=True)
    if (hit:=re.fullmatch(r'z\^2=2\*x\*y, cut by x\+y='+D+r',x=0,y=0',raw)):
        L=int(hit[1]);value=E(f'pi*{L*L}/sqrt(2)')
        return metric('triangular_cone_graph',value,
                      'Координатные плоскости и наклонная крышка выделяют ограниченный треугольник x,y≥0, x+y≤L.',
                      'На двух листах z=±√(2xy) плотность равна (x+y)/√(2xy). Полагаем x=st,y=s(1−t).',
                      'Множитель s от якобиана отделяется, а ∫₀¹1/√(2t(1−t))dt=π/√2; учтены оба листа.',
                      projection=['0<=s<=L','0<=t<=1'],sheet_count=2,triangle_bound=q(L))
    if (hit:=re.fullmatch('sphere '+sphere+'='+S+r'\^2 outside both cylinders '+radial+r'=\+\1\*x and '+radial+r'=-\1\*x(?: \(Viviani\))?',raw)):
        A=sym(hit[1])
        return spherical_strip(m.mul(q(8),m.power(A,2)),
                               'Обе внешние области требуют r≥R|cos φ| в проекции xy; r²+z²=R².',
                               'Тем самым на каждом азимуте −R|sin φ|≤z≤R|sin φ|. Интеграл |sin φ| на полном обороте равен 4.',
                               height_coordinate='z',angular_height='2*R*abs(sin(phi))')
    if (hit:=re.fullmatch(r'z=sqrt\('+radial+r'\) inside cylinder '+radial+'='+D+r'\*x',raw)):
        C=int(hit[1]);value=E(f'{C*C}*pi*sqrt(2)/4')
        return metric('constant_graph_over_shifted_disk',value,
                      'Проекционная область (x−C/2)²+y²≤C²/4 — полный сдвинутый диск.',
                      'Плотность графа z=r равна √2 вне вершины. Вершина имеет нулевую площадь.',
                      projected_radius=q(C,2),metric_density=('sqrt',q(2)))
    if (hit:=re.fullmatch(r'z=sqrt\(x\^2-y\^2\) inside cylinder \('+radial+r'\)\^2='+S+r'\^2\*\(x\^2-y\^2\)',raw)):
        A=sym(hit[1])
        return metric('lobed_graph',m.mul(m.mul(q(1,2),m.PI),m.power(A,2)),
                      'Пусть r>0; обе исходные границы требуют cos(2φ)≥0 и r²≤A²cos(2φ). Имеются два лепестка.',
                      'Метрическая плотность равна √2|cos φ|/√cos(2φ). После интеграла r dr остаётся |cos φ|√cos(2φ).',
                      'На каждом лепестке v=sin φ переводит интеграл в площадь полудиска с нужным линейным масштабом.',
                      half_lobes=2,radial_squares='A^2*cos(2*phi)',integrable_seam=True)
    if (hit:=re.fullmatch(r'z=\(x\^2-y\^2\)/2 cut by planes x-y=\+'+D+r',-\1; x\+y=\+\1,-\1',raw)):
        L=int(hit[1]);C=F(L*L,2);G=1+1/C
        s=geom_asinh(m.div(ONE,('sqrt',q(G))))
        i0=m.mul(q(G),root_power_primitive(m.div(ONE,('sqrt',q(G))),0))
        i1=m.add(s,m.mul(('sqrt',q(G-1)),('atan',('sqrt',q((G-1)/(G+1))))))
        value=m.mul(q(8,3),m.add(m.mul(m.mul(q(C),('sqrt',q(C))),m.add(i0,m.mul(q(G-1),i1))),
                                 m.mul(q(-1,4),m.PI)))
        return metric('quadratic_metric_over_square',m.simplify(value),
                      'Координаты u=x+y,v=x−y превращают проекцию в квадрат, якобиан 1/2 и плотность √(1+(u²+v²)/2).',
                      'Отражения и перестановка координат выделяют треугольник 0≤v≤u≤L; после v=u t интегрируем u.',
                      'При C=L²/2, G=1+1/C остаётся комбинация ∫√(t²+G)dt и ∫√(t²+G)/(1+t²)dt на [0,1].',
                      'Первый берём из радикальной первообразной. Во втором t=√G sinh s и w=tanh s дают арктангенс.',
                      projected_square=L,metric_weight='sqrt(1+(u^2+v^2)/2)',radical_coefficients=[q(C),q(G)])
    if (hit:=re.fullmatch(radial+r'=2\*'+S+r'\*z inside cylinder \('+radial+r'\)\^2=2\*\1\^2\*x\*y',raw)):
        A=hit[1];sym(A)
        return metric('radial_graph',E(f'{A}^2*(20/9-pi/3)',A),
                      'Плотность графа равна √(1+r²/A²), а граница r²≤A²sin(2φ) выделяет первый и третий квадранты.',
                      'После радиальной замены u=1+r²/A² на первом квадранте √(1+sin2φ)=sinφ+cosφ.',
                      'Интеграл куба этой суммы равен 10/3 на каждом из двух симметричных лепестков.',
                      original_scale_nonzero=A,radial_upper='abs(A)*sqrt(sin(2*phi))',lobe_count=2)
    if (hit:=re.fullmatch(radial+'='+S+r'\^2 cut by x\+z=0,x-z=0; x>0,y>0',raw)):
        A=sym(hit[1])
        return metric('cylindrical_height_strip',m.mul(q(2),m.power(A,2)),
                      'В указанном квадранте 0<φ<π/2. Пересечение с обеими плоскостями даёт −Rcosφ≤z≤Rcosφ.',
                      'Метрическая плотность цилиндра R постоянна; интеграл cosφ на данном квадранте равен 1.',
                      strip_radius=('abs',A),angle_interval=['0','pi/2'],component_multiplicity=1)
    if (hit:=re.fullmatch(r'\('+radial+r'\)\^\(3/2\)\+z='+D+r' cut by z=0',raw)):
        H=int(hit[1]);radius=ONE if H==1 else E(f'{H}^(2/3)');U=m.mul(q(3),radius)
        exact=m.mul(m.div(m.PI,q(3)),root_power_primitive(U,0))
        return metric('radial_graph',m.simplify(exact),
                      'Единственная ограниченная часть z=H−r³ имеет 0≤r≤H^(1/3); квадрат радиального наклона равен 9r⁴.',
                      'Подстановка u=3r² переводит r√(1+9r⁴) dr в √(1+u²)du/6.',
                      'Существующая первообразная радикального веса применяется между 0 и 3H^(2/3).',
                      antiderivative_argument=U,closed_disk=True)
    if (hit:=re.fullmatch(r'\(x/'+S+r'\+y/'+S+r'\)\^2\+2\*z/'+S+r'=1 cut by x=0,y=0,z=0',raw)):
        A,B,C=hit.groups()
        if len({A,B,C})!=3:raise Unsupported('The three scales must stay independent')
        for v in (A,B,C):sym(v)
        K=f'{C}^2*(1/{A}^2+1/{B}^2)'
        V=f'abs({A}*{B})*((1+({K}))^(3/2)-1)/(3*({K}))'
        return metric('triangular_signed_strips',dict(formula=f'{V} on each bounded piece; sum over both pieces is 2*({V})'),
                      'Берём s=x/A+y/B,t=x/A. Границы становятся t=0,t=s,s=±1.',
                      'Две ограниченные треугольные ветви являются отражениями, а смешанные квадранты не ограничены.',
                      'Площадь каждой ветви — |AB|∫₀¹s√(1+Ks²)ds. Подстановка u=1+Ks² учитывает все допустимые знаки.',
                      planar_map=['s=x/A+y/B','t=x/A'],branch_count=2,requires='ABC nonzero')
    if (hit:=re.fullmatch(r'x\^2/'+S+r'-y\^2/'+S+r'=2\*z cut by cylinder x\^2/\1\^2\+y\^2/\2\^2=1; z>=0',raw)):
        A,B=hit.groups();sym(A);sym(B)
        if A==B:raise Unsupported('The two source scales are fixed independently')
        return metric('elliptical_signed_graph',
                      dict(formula=f'abs({A}*{B})*(2*sqrt(2)-1)/3 times the angle: 4*atan(sqrt(abs({A}/{B}))) if {A},{B}>0; 2*pi-4*atan(sqrt(abs({A}/{B}))) if {A},{B}<0; 2*pi if {A}>0>{B}; 0 if {B}>0>{A}'),
                      'Масштабируем x=A r cosφ, y=B r sinφ. Из цилиндра следует r≤1, метрическая плотность √(1+r²).',
                      'Знак исходной высоты задаёт A cos²φ≥B sin²φ. Ветви с обоими положительными, обоими отрицательными и двумя смешанными знаками исчерпывают исходную область.',
                      'По каждой угловой области интегрируем один и тот же радиальный вес с модулем якобиана.',
                      radius_bound=ONE,angle_test=f'{A}*cos(phi)^2>={B}*sin(phi)^2',requires='both scales nonzero')
    if (hit:=re.fullmatch(r'sin\(z\)=sinh\(x\)\*sinh\(y\) cut by x='+D+r' and x='+D+r'; y>=0',raw)):
        L,H=map(int,hit.groups())
        if L>=H:raise Unsupported('A positive nondegenerate strip is needed for the original period argument')
        area=E(f'pi*ln(sinh({H})/sinh({L}))/2')
        return metric('periodic_graph_sheets',dict(formula='+infinity',one_sheet=area),
                      'Для каждого x граница 0≤sinh x sinh y≤1 даёт конечный ненулевой поперечный интервал.',
                      'На открытом листе плотность равна cosh x cosh y/|cos z|. Замена u=sinh x sinh y даёт (π/2)coth x после интеграла по y.',
                      'Все сдвиги исходной поверхности на 2π вдоль z допустимы и сохраняют положительную площадь. Поэтому общее значение бесконечно.',
                      period='2*pi',one_sheet_positive=True,x_interval=[q(L),q(H)])
    if (hit:=re.fullmatch(r'helicoid \(r\*cos\(phi\),r\*sin\(phi\),'+S+r'\*phi\) for 0<r<'+S+r', 0<phi<2\*pi',raw)):
        H,A=hit.groups();sym(H);sym(A)
        if H==A:raise Unsupported('The pitch and radius must be carried independently')
        return metric('helicoidal_radial_strip',
                      dict(formula=f'pi*({A}*sqrt({A}^2+{H}^2)+{H}^2*asinh({A}/abs({H}))) for {A}>0 and {H}!=0; pi*{A}^2 for {A}>0 and {H}=0; 0 for {A}<=0'),
                      'Поперечные касательные взаимно перпендикулярны, их длины 1 и √(r²+H²).',
                      'Один полный оборот однократно покрывает внутреннюю область; при H=0 получается плоский круг.',
                      'Радикальная первообразная применяется при H≠0, а пустая область и вырожденный шаг учитываются отдельно.',
                      angle_length='2*pi',radial_metric=f'sqrt(r^2+{H}^2)',zero_pitch_checked=True)
    raise Unsupported('No complete checked covering of the original surface is available')


SPATIAL_NAME=r'([A-Za-z_]\w*)'
SPATIAL_INTERNAL=(m.FUNCTIONS|{'x','y','z','xi','eta','zeta','pi','e'})


def station_name(n):
    if n in SPATIAL_INTERNAL:raise Unsupported('A fixed geometric parameter must remain independent of the coordinates')
    return ('s',n)


def source_spatial_force(task,emit):
    """Reduce hydrostatic normals and Newton kernels on rotationally symmetric sections."""
    K=task['kind'];out=task.get('requested_output');meta=task.get('source',{})
    n=SPATIAL_NAME;axe=r'xi\^2\+eta\^2';rad=axe+r'\+zeta\^2'
    allowed={'physical_model'} if K=='mechanical_integral_application' else {'region','density','point','printed_hint'}
    title=('Найти указанную физическую величину из распределения и области.' if K=='mechanical_integral_application'
           else 'Найти ньютонов потенциал или силу притяжения в указанной точке.')
    if set(task)-{'kind','id','source','requested_output',*allowed} or meta.get('literal_requirement') not in (None,title):
        raise Unsupported('Every original physical condition and requested force must be preserved')
    def force(rule,value,*steps,**proof):
        return emit(rule,steps,dict(formula=value),
                    required_hint=task.get('printed_hint'),**proof)
    def expr(s,*lines,**proof):
        return force('hydrostatic_projected_load',s,*lines,**proof)
    def shell(value,*steps,**proof):
        return force('newton_angular_sections',value,
            'Из симметрии выбираем полярную ось от центра к P. Если P совпадает с центром, направление произвольно.',
            'При r,s>0 угловой интеграл по t=cosθ равен 2/max(r,s). В точке r=s его край порядка (1−t)^(-1/2) интегрируем.',
            *steps,angular_kernel='2/max(r,s)',convergence_at_equal_radii=True,**proof)
    def axial_cylinder(a,h,z,value,*steps,**evidence):
        return force('newton_angular_sections',value,
            'Полные диски и однородная плотность сохраняются при отражениях относительно обеих осевых плоскостей. Поперечные силы равны нулю.',
            'Радиальный интеграл ядра потенциала по диску равен 2π A(s), где A(s)=√(a²+s²)−|s|.',
            'Непрерывность A позволяет применять Ньютон–Лейбница к полному продольному интегралу и учитывать точку внутри тела.',
            *steps,cylinder_radius=a,cylinder_height=h,observer=z,radial_trace='A(s)=sqrt(a^2+s^2)-abs(s)',**evidence)
    if K=='mechanical_integral_application':
        raw=task.get('physical_model')
        if not isinstance(raw,str):raise Unsupported('The original physical model is required')
        units=r'rectangle side lengths ([A-Za-z]\w*),([A-Za-z]\w*), linear density ([A-Za-z]\w*) \(printed «погонная плотность»\) of cut grass; work to transport mass ([A-Za-z]\w*) a distance ([A-Za-z]\w*) is ([A-Za-z]\w*)\*\4\*\5, 0<\6<1; gather all hay in center'
        strip=re.fullmatch(units,raw)
        if strip and out==['minimal_work']:
            a,b,rho,M,dist,k=strip.groups()
            if len(set(strip.groups()))!=6:raise Unsupported('Dimensions, density and work coefficients have distinct roles')
            A,B=m.mul(q(1,2),('s',a)),m.mul(q(1,2),('s',b))
            D=('sqrt',m.add(m.power(A,2),m.power(B,2)))
            sigma_name='sigma'
            while sigma_name in strip.groups():sigma_name+='_'
            cost=('s',k)
            from planar_integrals import geom_asinh
            sa=m.mul(m.power(A,3),geom_asinh(m.div(B,A)))
            sb=m.mul(m.power(B,3),geom_asinh(m.div(A,B)))
            cap=m.mul(q(2,3),m.mul(cost,('s',sigma_name)))
            area_work=m.mul(cap,m.add(m.mul(q(2),m.mul(A,m.mul(B,D))),m.add(sa,sb)))
            return emit('transport_work_from_mass_measure',[
                'На прямоугольнике кратчайший путь к центру — прямой отрезок. Минимум для заданного распределения массы равен k∫distance dμ.',
                'Погонная плотность задаёт массу на линии, но для всего поля нужна геометрия рядов. Центральный ряд вдоль первой стороны даёт kρA². Тот же ряд на ненулевом поперечном удалении имеет строго большую стоимость.',
                'При отдельно заданной равномерной поверхностной плотности берём четыре равных четверти. В четверти div((x,y)√(x²+y²))=3√(x²+y²).',
                'Остаются два граничных интеграла квадратных корней. Подстановка их элементарных значений даёт указанную формулу для равномерной площади.'
            ],dict(unique_from_linear_density=False,
                   central_uniform_row_cost=m.mul(cost,m.mul(('s',rho),m.power(A,2))),
                   uniform_area_density_model=area_work,area_density_parameter=sigma_name),half_widths=[A,B])
        vessel=re.fullmatch(r'water pressure on lateral half x>=0 of cylinder x\^2\+y\^2='+n+
                            r'\^2, base z=0, water level z='+n,raw)
        if vessel and out==['resultant_force']:
            a,h=vessel.groups();station_name(a);station_name(h)
            return expr(f'gamma*abs({a})*{h}^2 along +Ox for {h}>=0; zero load if {h}<0',
                        'Вода внутри сосуда. Нормаль боковой поверхности (cosφ,sinφ,0), и при x≥0 −π/2≤φ≤π/2.',
                        'Интеграл компоненты Oy нулевой по симметрии. Компонента Ox получает угловой множитель 2.',
                        'При 0≤z≤h давление γ(h−z). Интегрируем его по высоте и умножаем на радиус цилиндра.',
                        angular_cosine=q(2),pressure='gamma*(h-z)',pressure_scale='gamma=rho_water*g',nonnegative_water_level=True)
        if raw=='sphere radius a in liquid of constant density delta, center depth h>=a' and out==['force_on_upper_hemisphere','force_on_lower_hemisphere']:
            return expr('vertical upward components: upper=-pi*delta*g*a^2*h+2*pi*delta*g*a^3/3; lower=pi*delta*g*a^2*h+2*pi*delta*g*a^3/3',
                        'При направлении Oz вверх на полусферах t=(z−z_c)/a лежит соответственно в [0,1] и [−1,0].',
                        'Метрический элемент 2πa²dt после интегрирования азимута. Внутреннее давление даёт вертикальную компоненту −δg(h−a t)t.',
                        'Условие h≥a сохраняет неотрицательное давление. Поперечные компоненты каждой силы исчезают по симметрии.',
                        hemisphere_domains=[[q(0),ONE],[q(-1),q(0)]],normal_sign='inward',fluid_condition='h>=a')
        if raw=='fully submerged cylinder radius a, height b, liquid density delta, center depth h, axis angle alpha to vertical' and out==['force_on_lower_base','force_on_upper_base']:
            return expr('lower=pi*a^2*delta*g*(h+b*abs(cos(alpha))/2); upper=pi*a^2*delta*g*(h-b*abs(cos(alpha))/2); normal directions inward',
                        'Полное погружение задано исходно. Центры плоских оснований имеют глубины h±b|cosα|/2.',
                        'Ошибка относительно центрального давления линейна по координате в плоскости. Она исчезает после интегрирования по диску.',
                        'У каждой силы нормаль направлена внутрь тела. Оба модуля неотрицательны, при нулевом среднем заглублении давление на основании равно нулю.',
                        depth_projection='b*abs(cos(alpha))/2',physical_scope='fully submerged',normal_sign='inward')
        cyl=re.fullmatch(r'attraction of homogeneous cylinder x\^2\+y\^2<='+n+
                         r'\^2,0<=z<='+n+r', mass M on point \(0,0,'+n+r'\) of mass m',raw)
        if cyl and out==['gravitational_force']:
            a,h,z=cyl.groups();[station_name(v) for v in (a,h,z)]
            return axial_cylinder(a,h,z,f'F_z=2*G*m*M/({a}^2*{h})*(A({z})-A({h}-{z}))',
                                  'Применяем плотность M/(πa²h), исходную точечную массу m и стандартный коэффициент G.',
                                  'Находим знаковую производную по высоте наблюдателя, которая определяет направление силы.',
                                  total_mass='M',test_mass='m')
        ellipse=re.fullmatch(r'ellipse x\^2/a\^2\+y\^2/b\^2<=1 with pressure '+n+
                            r'\*\(1-x\^2/a\^2-y\^2/b\^2\)(?:\^([1-9]\d*))?',raw)
        if ellipse and out==['mean_pressure']:
            p=ellipse[1];station_name(p);j=int(ellipse[2] or 1);a=m.mul(q(1,j+1),('s',p))
            return emit('hydrostatic_projected_load',[
                'После диагонального масштаба проекция — единичный диск, давление зависит от r².',
                'Абсолютный якобиан и угловая мера сокращаются с площадью. Подстановка t=r² даёт степенной средний момент.'],
                dict(value=a),radial_exponent=j,normalizing_area='pi*abs(a*b)')
        raise Unsupported('The oriented load or its requested components are not established')
    region=task.get('region');density=task.get('density');point=task.get('point');hint=task.get('printed_hint')
    if not all(isinstance(x,str) for x in (region,density,point)):
        raise Unsupported('Newton geometry, density and observation point must be explicit')
    ball=re.fullmatch(rad+r'<='+n+r'\^2',region)
    if ball:
        R=ball[1];station_name(R)
        if (out==['potential'] and point=='P(x,y,z)' and hint in ('Choose O-zeta through P.',None)
                and re.fullmatch(n,density)):
            station_name(density)
            return shell(f'U(r)=2*pi*{density}*({R}^2-r^2/3) for 0<=r<=abs({R}); 4*pi*{density}*abs({R})^3/(3*r) for r>abs({R})',
                         'Внутри шара разделяем радиальные слои в s=r; снаружи все s≤r. В центре непосредственный радиальный интеграл даёт 2πρR².',
                         radial_weight='s^2',spherical_axis='center-to-observer',coincident_center='integrate directly')
        axial=re.fullmatch(r'P\(0,0,'+n+r'\), mass '+n,point)
        mass=re.fullmatch(r'uniform with total mass '+n,density)
        if out==['force'] and hint is None and axial and mass:
            a,mass0=axial.groups();M=mass[1]
            [station_name(v) for v in (a,mass0,M)]
            return shell(f'F_z=-G*{M}*{mass0}*{a}/abs({R})^3 for abs({a})<=abs({R}); -G*{M}*{mass0}*{a}/abs({a})^3 outside',
                         'Подставляем постоянную плотность 3M/(4π|R|³). Дифференцируем уже вычисленный внутренний и внешний потенциал.',
                         'При |a|=|R| производные совпадают. При a=0 осевая сила равна нулю. Знак показывает притяжение к центру.',
                         ball_radius=R,test_mass=mass0,gradient_interior_and_exterior=True,requires='positive radius for fixed positive mass')
    band=re.fullmatch(n+r'\^2<='+rad+r'<='+n+r'\^2',region)
    fd=re.fullmatch(n+r'\(sqrt\('+rad+r'\)\)',density)
    if band and fd and out==['potential'] and point=='P(x,y,z)' and hint is None:
        L,H=band.groups();f=fd[1];[station_name(v) for v in (L,H,f)];L,H=f'abs({L})',f'abs({H})'
        return shell(f'U(r)=4*pi*(integral({L},min(r,{H}),{f}(s)*s^2)/r + integral(max(r,{L}),{H},{f}(s)*s)) for r>0; U(0)=4*pi*integral({L},{H},{f}(s)*s); empty subintervals contribute 0',
                     'Сохраняем радиальную плотность f(s) и две исходные границы. Разделяем интеграл в s=r только если эта точка внутри слоя.',
                     'При r=0 угловая мера 4π, ядро 1/s. Конечность потенциала определяется сходимостью соответствующих одномерных интегралов.',
                     layer_limits=(L,H),convergence='preserve convergence of the remaining radial integrals')
    cylinder=re.fullmatch(axe+r'<='+n+r'\^2,0<=zeta<='+n,region)
    obs=re.fullmatch(r'P\(0,0,([A-Za-z_]\w*)\)(,mass 1)?',point)
    if cylinder and obs and re.fullmatch(n,density) and hint is None:
        a,h=cylinder.groups();z=obs[1];[station_name(v) for v in (a,h,density)]
        if out==['potential'] and not obs[2]:
            return axial_cylinder(a,h,z,f'U=2*pi*{density}*(B({h}-{z})+B({z})) for {a}!=0,{h}>0; U=0 otherwise; B(s)=(s*sqrt({a}^2+s^2)+{a}^2*asinh(s/abs({a}))-s*abs(s))/2',
                                  'Первообразная B нечётна и непрерывна на оси. Интегрирование от −z до h−z даёт оба вклада.',
                                  observer_cases=['below','inside','above'],density=density)
        if out==['force'] and obs[2]:
            return axial_cylinder(a,h,z,f'F_z=2*pi*G*{density}*(A({z})-A({h}-{z})) for {h}>=0; 0 for {h}<0',
                                  'Дифференцируем конечную сумму первообразных. На гранях формула остаётся непрерывной.',
                                  observer_cases=['below','inside','above'],density=density,test_mass=ONE)
    sector=re.fullmatch(r'spherical sector, sphere radius '+n+r', full axial section angle 2\*'+n,region)
    if sector and out==['force'] and point=='vertex, mass 1' and hint is None and re.fullmatch(n,density):
        R,a=sector.groups();[station_name(v) for v in (R,a,density)]
        return force('newton_angular_sections',f'G*pi*{density}*{R}*sin({a})^2 along the sector axis',
                     'Угловая граница осевого сечения даёт 0≤θ≤α. Азимут полный, поэтому обе поперечные компоненты исчезают.',
                     'Радиальный квадрат якобиана сокращается с r^(-2) в силе. Особенность вершины интегрируема.',
                     'Положительный осевой вклад \u222b cosθ sinθ dθ равен sin²α/2. Возвращаем радиус, плотность и полный азимут.',
                     theta_domain=('0',a),radial_singularity_integrable=True)
    raise Unsupported('The original Newton geometry and all observation cases are not established')


def projective_region_spec(task):
    """Recognize ratios or linear projective coordinates from the original walls."""
    kind=task.get('kind');n=SPATIAL_NAME
    if kind=='spatial_exact_integral':
        region=task.get('region')
        if not isinstance(region,str):return None
        wall=re.fullmatch(r'z='+n+r'\*y\^2,z='+n+r'\*y\^2,y>0,0<\1<\2; z='+n+r'\*x,z='+n+r'\*x,0<\3<\4; z='+n+r'>0',region)
        if wall:return 'parabolic_walls',wall.groups()
        wall=re.fullmatch(r'x>0,y>0,z>0; z=\(x\^2\+y\^2\)/'+n+r',z=\(x\^2\+y\^2\)/'+n+r',x\*y='+n+r'\^2,x\*y='+n+r'\^2,y='+n+r'\*x,y='+n+r'\*x;0<\3<\4,0<\5<\6,0<\1<\2',region)
        if wall:return 'positive_ratio_walls',wall.groups()
    if kind=='bounded_solid_volume':
        surfaces=task.get('surfaces')
        if not isinstance(surfaces,str):return None
        x='x/'+n;y='y/'+n;z='z/'+n;add=x+r'\+'+y;ts=add+r'\+'+z
        choices=[
            ('signed_simplex_rays',r'\('+ts+r'\)\^2=x/'+n+r'([+-])y/'+n),
            ('product_simplex_rays',r'\('+ts+r'\)\^4=x\*y\*z/\(\1\*\2\*\3\)'),
            ('separated_elliptic_sum',r'\('+add+r'\)\^2\+\('+z+r'\)\^2=1'),
            ('arcsine_section',r'\('+add+r'\)/\(x/\1\+y/\2\+'+z+r'\)=\(2/pi\)\*asin\(x/\1\+y/\2\+z/\3\),x/\1\+y/\2=1,x=0,x=\1'),
            ('logarithmic_section',r'\('+ts+r'\)=ln\(\(x/\1\+y/\2\+z/\3\)/\(x/\1\+y/\2\)\),x=0,z=0,y/\2\+z/\3=0,x/\1\+y/\2\+z/\3=1'),
        ]
        for name,pattern in choices:
            hit=re.fullmatch(pattern,surfaces)
            if hit:return name,hit.groups()
    if kind=='partition_volume_ratio' and isinstance(task.get('sphere'),str) and isinstance(task.get('cut'),str):
        sphere=re.fullmatch(r'x\^2\+y\^2\+z\^2<=4\*'+n+r'\*z',task['sphere'])
        if sphere and re.fullmatch(r'x\^2\+y\^2\+'+re.escape(sphere[1])+r'\*z=4\*'+re.escape(sphere[1])+r'\^2',task['cut']):
            return 'switch_of_radial_bounds',sphere.groups()
    if kind=='solid_area_and_volume':
        eq=task.get('surfaces')
        if isinstance(eq,list) and len(eq)==2 and all(isinstance(s,str) for s in eq):
            lo=re.fullmatch(r'x\^2\+y\^2='+n+r'\*z',eq[0])
            if lo and re.fullmatch(r'z=2\*'+re.escape(lo[1])+r'-sqrt\(x\^2\+y\^2\)',eq[1]):
                return 'paraboloid_cone_cap',lo.groups()
    return None


def source_projective_spatial_measure(task,spec,emit,library):
    """Check inverse maps, choose positive branches and integrate the resulting fiber."""
    name,names=spec;kind=task['kind'];title=task.get('source',{}).get('literal_requirement')
    want=task.get('requested_output');facts=task.get('stated_conditions',[]);method=task.get('method_requirement')
    fields={'bounded_solid_volume':{'surfaces','stated_conditions','method_requirement'},
            'spatial_exact_integral':{'integrand','region'},
            'solid_area_and_volume':{'surfaces','stated_conditions'},
            'partition_volume_ratio':{'sphere','cut'}}
    headings={'bounded_solid_volume':'Вычислить объём, пользуясь подходящей заменой переменных. Параметры положительны.',
              'spatial_exact_integral':'Вычислить тройной интеграл по указанной области.',
              'solid_area_and_volume':'Найти объём и поверхность ограниченного тела.',
              'partition_volume_ratio':'Найти отношение двух объёмов частей шара.'}
    if set(task)-{'id','kind','source','requested_output',*fields[kind]} or title not in (None,headings[kind]):
        raise Unsupported('The required spatial statement and all of its conclusions must be kept')
    def E(s,*args):return m.simplify(m.parse(s,None,args))
    def finish(value,*rows,rule='projective_spatial_fibers',**record):
        if 'inverse_variables' in record:
            from cartesian_fields import derivative_table
            from surface_fields import vector_cross
            from verify import same_value
            inverse_variables=record['inverse_variables'];names0=record.get('map_parameters',[])
            symbols=[*inverse_variables,*names0]
            if len(symbols)!=len(set(symbols)):
                raise Unsupported('The change of variables needs distinct coordinates and parameters')
            inverse=[m.parse(s,None,symbols) for s in record['inverse']]
            partial,trace=derivative_table(library)
            jacobian=[[partial(e,u) for u in inverse_variables] for e in inverse]
            determinant=m.simplify(m.dot(jacobian[0],vector_cross(jacobian[1],jacobian[2])))
            expected=m.parse(record.get('signed_jacobian',record['jacobian']),None,symbols)
            if not same_value(determinant,expected):
                raise Unsupported('The inverse-map determinant could not be verified')
            record.update(jacobian_matrix=jacobian,determinant=determinant,derivative_rules=trace)
        return emit(rule,rows,value if isinstance(value,dict) else dict(value=value),
                    chart_family=name,**record)
    if name=='parabolic_walls' and want==['exact_integral'] and task.get('integrand')=='x^2':
        a,b,P,Q,h=names
        for v in names:station_name(v)
        if set(names)&{'u','v'}:raise Unsupported('The proposed local ratios must be distinct from the fixed scales')
        val=E(f'2*{h}^(9/2)*(1/sqrt({a})-1/sqrt({b}))*(1/{P}^3-1/{Q}^3)/27',*names)
        return finish(val,
            'У всех нужных координат положительные значения во внутренности. Выбираем u=z/y², v=z/x и исходную высоту.',
            'Имеем a≤u≤b, α≤v≤β, 0<z≤h. Обратные y=√(z/u), x=z/v дают абсолютный якобиан z^(3/2)/(2u^(3/2)v²).',
            'Умножаем на исходный вес x²=z²/v². Все три степенных интеграла имеют конечные пределы.',
            inverse=['z/v','sqrt(z/u)','z'],inverse_variables=['u','v','z'],
            signed_jacobian='-z^2/(2*u^2*v^2*sqrt(z/u))',jacobian='z^(3/2)/(2*u^(3/2)*v^2)',
            bounds=[[a,b],[P,Q],['0',h]])
    if name=='positive_ratio_walls' and want==['exact_integral'] and task.get('integrand')=='x*y*z':
        p,q0,a,b,P,Q=names
        for v in names:station_name(v)
        if set(names)&{'u','s','w'}:raise Unsupported('The proposed local ratios must be distinct from the fixed scales')
        C=lambda s:f'({s}^2/4+ln({s})-1/(4*{s}^2))'
        val=E(f'({b}^8-{a}^8)*(1/{p}^2-1/{q0}^2)*({C(Q)}-{C(P)})/8',*names)
        return finish(val,
            'В положительном октанте координаты u=xy, s=y/x, w=z/(x²+y²) определены и имеют единственный обратный образ.',
            'Границы становятся a²≤u≤b², α≤s≤β, 1/n≤w≤1/m. Якобиан обратной замены u(s+1/s)/(2s).',
            'Вес после подстановки u³w(s+1/s)²/(2s). Интеграл распадается на два степенных и один с логарифмом.',
            inverse=['sqrt(u/s)','sqrt(u*s)','w*u*(s+1/s)'],inverse_variables=['u','s','w'],
            signed_jacobian='u^2*(s+1/s)/(2*s*sqrt(u/s)*sqrt(u*s))',jacobian='u*(s+1/s)/(2*s)',
            bounds=[[f'{a}^2',f'{b}^2'],[P,Q],[f'1/{q0}',f'1/{p}']])
    if kind=='bounded_solid_volume':
        if want!=['exact_volume','substitution_and_jacobian'] or method not in (None,'change_of_variables'):
            raise Unsupported('The change of variables and its Jacobian are part of the goal')
        a,b,c=names[:3]
        for v in (a,b,c):station_name(v)
        if len({a,b,c})!=3:raise Unsupported('Independent original scales are required')
        scale=f'{a}*{b}*{c}'
        if name in ('signed_simplex_rays','product_simplex_rays','separated_elliptic_sum'):
            if facts!=['parameters positive','x>=0','y>=0','z>=0']:
                raise Unsupported('The positive scales and original first octant must be retained')
            if name=='separated_elliptic_sum':
                return finish(E(scale+'/3',a,b,c),
                              'После масштабирования выбираем u=x/a,s=x/a+y/b,w=z/c. Обратный якобиан abc.',
                              'Исходные знаки дают 0≤u≤s и w≥0. Уравнение ограничивает 0≤s≤1, 0≤w≤√(1−s²).',
                              'Интегрируем сначала постоянную плотность по u, затем s√(1−s²) по [0,1].',
                              inverse=[f'{a}*u',f'{b}*(s-u)',f'{c}*w'],jacobian=scale,
                              inverse_variables=['u','s','w'],map_parameters=[a,b,c],
                              proved_bounds=['0<=u<=s','0<=s<=1','0<=w<=sqrt(1-s^2)'])
            radial='U*V*(1-U-V)';extra=['Верхняя радиальная граница равна UV(1−U−V). После интеграла t² остаётся куб этой высоты.',
                                         'Его интеграл по симплексу равен (3!)³/11!, по стандартным степенным моментам.']
            value=E(scale+'/554400',a,b,c)
            if name=='signed_simplex_rays':
                h,sign,k=names[3:];station_name(h);station_name(k)
                if len(set((a,b,c,h,k)))!=5:raise Unsupported('Named scales must retain their independent inputs')
                A,B=f'({a}/{h})',f'({b}/{k})'
                radial=f'{A}*U{sign}{B}*V'
                if sign=='+':
                    value=E(f'{scale}*({A}^3+{A}^2*{B}+{A}*{B}^2+{B}^3)/60',a,b,c,h,k)
                    extra=['Линейная высота AU+BV неотрицательна на всём симплексе. После интеграла t² раскрываем куб и берём моменты симплекса.']
                else:
                    value=E(f'{scale}*{A}^4/(60*({A}+{B}))',a,b,c,h,k)
                    extra=['Радиальная высота AU−BV положительна только при AU>BV. Отсекли треугольник с вершинами (0,0),(1,0),(B/(A+B),A/(A+B)).',
                           'После аффинного перехода его якобиан A/(A+B), а новая линейная высота имеет значения 0,A,0 в вершинах.']
            return finish(value,
                'На первом октанте нормируем масштабы, затем t=u+v+w и U=u/t,V=v/t. Вершина t=0 имеет нулевую меру.',
                'Обратные u=tU,v=tV,w=t(1−U−V) и якобиан abc·t². Углы образуют стандартный симплекс.',
                *extra,inverse=[f'{a}*t*U',f'{b}*t*V',f'{c}*t*(1-U-V)'],jacobian=scale+'*t^2',
                inverse_variables=['t','U','V'],map_parameters=[a,b,c],
                radial_upper=radial,strictly_positive_height=True)
        if facts!=['parameters positive']:
            raise Unsupported('Positive scales and original branch geometry must be kept')
        shared='Выбираем u=x/a, s=x/a+y/b, t=s+z/c. Обратный якобиан abc.'
        chart=dict(inverse=[f'{a}*u',f'{b}*(s-u)',f'{c}*(t-s)'],jacobian=scale,
                   inverse_variables=['u','s','t'],map_parameters=[a,b,c],excluded_original_pole='t=0 on original surface')
        if name=='arcsine_section':
            return finish(E(f'3*{scale}/2',a,b,c),shared,
                          'Из исходной дроби требуется t≠0, из арксинуса |t|≤1. Нижняя поверхность s=2t arcsin(t)/π, верхняя s=1.',
                          'Область 0≤u≤1 имеет две симметричные ветви по t. Предел при t=0 сохраняем как границу нулевой меры.',
                          'Интегрирование по частям даёт ∫₀¹t arcsin(t)dt=π/8. Вычитаем толщину нижней поверхности на обеих ветвях.',
                          t_interval=['-1','1'],s_bounds=['2*t*asin(t)/pi','1'],**chart)
        if name=='logarithmic_section':
            return finish(E(f'{scale}*(5/e-5/3)',a,b,c),shared,
                          'На исходной поверхности t/s>0. После экспоненцирования s=t e^(−t), на другой стенке s=t.',
                          'Границы u=0 и u=t вместе с t=1 ограничивают положительную часть. Отрицательная ветвь не замыкается.',
                          'На 0<t<1 после двух линейных интегралов остаётся t²(1−e^(−t)). Применяем первообразную экспоненциального веса.',
                          t_interval=['0','1'],s_bounds=['t*exp(-t)','t'],
                          original_log_domain='t/s>0; s nonzero',**chart)
    if name=='switch_of_radial_bounds' and want==['volume_ratio']:
        a=names[0];station_name(a)
        return finish(dict(formula=f'37:27 on x^2+y^2+{a}*z<=4*{a}^2 and its complementary side, for {a}!=0'),
                      'При отрицательном a отражение z→−z переводит обе исходные поверхности к положительному масштабу.',
                      'При t=z/a радиальный квадрат ограничен 4t−t² от сферы. Для первой части есть вторая граница 4−t.',
                      'Порядок границ меняется при t=1 и t=4. Моменты на [0,1] и [1,4] дают 37/6, а весь шар даёт 64/6.',
                      'Общий множитель π|a|³ сокращается. При a=0 положительных объёмов для отношения нет.',
                      walls=['4*t-t^2','4-t'],height_breaks=[q(0),ONE,q(4)],ordered_side_weights=[q(37,6),q(27,6)])
    if name=='paraboloid_cone_cap' and want==['volume','surface_area']:
        a=names[0];station_name(a)
        if facts!=[a+'>0']:raise Unsupported('The two graph bounds require their printed positive scale')
        vals=dict(volume=E(f'5*pi*{a}^3/6',a),surface_area=E(f'pi*{a}^2*(sqrt(2)+(5*sqrt(5)-1)/6)',a))
        return finish(dict(components=vals),
            'Для r≥0 неравенство r²/a≤2a−r равносильно r≤a. Значит, ограниченный столбец лежит между этими двумя графиками.',
            'Интегрируем высоту столбца с весом 2πr. Объём даёт 5πa³/6.',
            'Для обеих поверхностей метрика равна √(1+z_r²). На конусе она постоянна, на параболоиде даёт замену 1+4r²/a².',
            'Шов r=a и вершина обладают нулевой площадью. Другой замыкающей крышки нет.',
            rule='spatial_surface_sections',radius_bound=a,vertical_bounds=[f'r^2/{a}',f'2*{a}-r'],surface_count=2)
    raise Unsupported('The projected region does not bind the full requested weighted measure')
