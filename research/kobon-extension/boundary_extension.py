"""Exact exterior extension with rational arithmetic. Lines use a*x+b*y=c."""
from exact_geometry import *
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

def cyclic_data(ar):
    rays=[]
    for i,(a,b,c) in enumerate(ar['lines']):
        rays.extend([(b,-a,i),(-b,a,i)])
    rays.sort(key=cmp_to_key(angle_compare))
    def idx(d):
        return next(i for i,r in enumerate(rays) if d[0]*r[1]==d[1]*r[0] and d[0]*r[0]+d[1]*r[1]>0)
    n=len(ar['lines']);B=[]
    for w in wedges(ar):
        i,j=idx(w['u']),idx(w['v'])
        assert j==(i+1)%(2*n),(i,j)
        B.append(i)
    profile=[sum((i-j)%(2*n)<n-1 for i in B) for j in range(2*n)]
    return B,profile

def check(ls):
    ar=arrangement(ls);n=len(ls);T=len(ar['triangles']);d=n*(n-2)-3*T
    assert len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
    B,profile=cyclic_data(ar);b=len(B)
    assert len(set(B))==b
    assert 3<=b<=n and b+d>=n,(n,T,d,b)
    assert sum(profile)==b*(n-1)
    assert max(profile)<=n//2
    count,line=exterior_choices(ar)[0]
    assert max(profile)==count
    new=arrangement(ls+[line]);assert len(new['triangles'])==T+count
    assert set(ar['triangles'])<=set(new['triangles'])
    assert all(len(s)==2 for s in new['points'].values())
    q=max(3,3*T-n*(n-3));gain=((n-1)*q+2*n-1)//(2*n)
    assert count>=gain
    return dict(n=n,T=T,d=d,b=b,guaranteed_gain=gain,actual_gain=count,
                wedge_starts=B,profile=profile,added_line=line)

