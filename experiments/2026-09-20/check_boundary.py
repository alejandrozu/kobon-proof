from extension_audit import *
import random

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

if __name__=='__main__':
    rng=random.Random(20092026);checked=0
    for n in range(3,31):
        for trial in range(20):
            while True:
                ls=[(i,-1,rng.randrange(-100000,100001)) for i in range(n)]
                if all(len(s)==2 for s in arrangement(ls)['points'].values()):break
            check(ls);checked+=1
    print('PASS',checked,'simple rational arrangements; boundary charge, cyclic identity, bound, exact extension and preservation')
