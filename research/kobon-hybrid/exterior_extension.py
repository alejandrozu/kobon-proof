"""Choose the best exterior line exactly; normal sectors are enumerated first."""
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
            rays.extend([(d[0],d[1],p==ar['rows'][i][-1]),
                         (-d[0],-d[1],p==ar['rows'][i][0])])
        rays.sort(key=cmp_to_key(angle_compare))
        for u,v in zip(rays,rays[1:]+rays[:1]):
            if u[2] and v[2] and u[0]*v[1]-u[1]*v[0]>0:
                out.append((u[:2],v[:2]))
    return out


def best_exterior(ar):
    # Counts depend only on the normal's angular sector. Form the expensive
    # offset from all old vertices only once, after selecting a best sector.
    breaks=sorted(set(-F(b,a) for a,b,c in ar['lines'] if a))
    alphas=[breaks[0]-1]+[(x+y)/2 for x,y in zip(breaks,breaks[1:])]+[breaks[-1]+1]
    ws=wedges(ar);choices=[]
    for alpha in alphas:
        for sign in (-1,1):
            x,y=sign*alpha.denominator,-sign*alpha.numerator
            count=sum(x*u[0]+y*u[1]>0 and x*v[0]+y*v[1]>0 for u,v in ws)
            choices.append((count,-(abs(x).bit_length()+abs(y).bit_length()),x,y))
    count,_,x,y=max(choices)
    height=1+max(F(x*p[0]+y*p[1],p[2]) for p in ar['points'])
    return count,primitive((x,y,height)),len(ws)
