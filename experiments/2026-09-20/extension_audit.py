"""Exact exterior-extension audit and exhaustive one-line cell search."""
from research import *
from functools import cmp_to_key

def angle_compare(u, v):
    x,y=u[:2];z,w=v[:2]
    hu=0 if y>0 or y==0 and x>0 else 1
    hv=0 if w>0 or w==0 and z>0 else 1
    if hu!=hv:return hu-hv
    cross=x*w-y*z
    return -1 if cross>0 else 1 if cross<0 else 0

def wedges(ar):
    out=[]
    for p,incident in ar['points'].items():
        rays=[]
        for i in incident:
            a,b,c=ar['lines'][i];d=(b,-a)
            axis=0 if b else 1
            if d[axis]<0:d=(-d[0],-d[1])
            rays.extend([(d[0],d[1],p==ar['rows'][i][-1],i),
                         (-d[0],-d[1],p==ar['rows'][i][0],i)])
        rays.sort(key=cmp_to_key(angle_compare))
        for u,v in zip(rays,rays[1:]+rays[:1]):
            if u[2] and v[2] and u[0]*v[1]-u[1]*v[0]>0:
                out.append(dict(p=p,u=u[:2],v=v[:2],lines=(u[3],v[3])))
    return out

def exterior_choices(ar):
    # w(x,y)=x-alpha*y, excluding finitely many parallel directions.
    breaks=sorted(set(-F(b,a) for a,b,c in ar['lines'] if a))
    alphas=[breaks[0]-1]+[(x+y)/2 for x,y in zip(breaks,breaks[1:])]+[breaks[-1]+1]
    ws=wedges(ar)
    out=[]
    for alpha in alphas:
        for sign in (-1,1):
            normal=(sign,-sign*alpha)
            dot=lambda p:normal[0]*p[0]+normal[1]*p[1]
            count=sum(dot(w['u'])>0 and dot(w['v'])>0 for w in ws)
            h=1+max(F(dot(p),p[2]) for p in ar['points'])
            line=primitive((*normal,h))
            out.append((count,line))
    return sorted(out,reverse=True)

def line_samples(ar):
    """One rational sample per open cell in (slope,intercept) space.

    Constraints x*s+b=y for every old vertex, and s=old slope.
    Every open cell is incident to a finite vertex since constraints span R^2.
    Around each vertex sample every local open angular sector exactly.
    """
    critical=list(set(primitive((p[0],p[2],p[1])) for p in ar['points']))
    critical+=list(set(primitive((1,0,F(-a,b))) for a,b,c in ar['lines'] if b))
    vertices=set(p for x,y in it.combinations(critical,2) if (p:=intersection(x,y)))
    seen=set()
    for sv,bv,z in sorted(vertices):
        s0,b0=F(sv,z),F(bv,z)
        vals=[a*s0+b*b0-c for a,b,c in critical]
        rays=[]
        for (a,b,c),val in zip(critical,vals):
            if val==0:rays.extend([(b,-a),(-b,a)])
        rays=sorted(set(rays),key=cmp_to_key(angle_compare))
        for r,q in zip(rays,rays[1:]+rays[:1]):
            d=(r[0]+q[0],r[1]+q[1])
            assert r[0]*q[1]-r[1]*q[0]>0
            eps=min([F(1)]+[abs(val)/(2*(abs(a*d[0]+b*d[1])+1))
                for (a,b,c),val in zip(critical,vals) if val])
            s,b=s0+eps*d[0],b0+eps*d[1]
            signs=tuple((a*s+bb*b-c)>0 for a,bb,c in critical)
            if signs in seen:continue
            seen.add(signs)
            assert all(a*s+bb*b-c!=0 for a,bb,c in critical)
            yield primitive((s,-1,-b))

def audit(lines):
    ar=arrangement(lines);old=set(ar['triangles']);n=len(lines)
    best_preserve=(-1,None);best_all=(-1,None);hist=Counter();cells=0
    for line in line_samples(ar):
        new=arrangement(lines+[line]);tri=set(new['triangles']);T=len(tri);cells+=1
        if T>best_all[0]:best_all=(T,line)
        if old<=tri:
            hist[T-len(old)]+=1
            if T>best_preserve[0]:best_preserve=(T,line)
    result=dict(n=n,old=len(old),cells=cells,
        max_preserving=best_preserve,max_unrestricted=best_all,
        preserving_gain_histogram=dict(sorted(hist.items())),
        wedges=len(wedges(ar)),max_exterior=exterior_choices(ar)[0])
    print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:] or ['5','7']):
        audit([(i,-1,-i*i) for i in range(n)])
