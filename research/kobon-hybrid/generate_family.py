"""Generate and independently verify finite rational members of the new seed family.

The BBL doubling formula is credited to Bartholdi, Blanc, and Loisel (2007).
Exact rational interval midpoints propose the trigonometric coefficients.
Each saved finite arrangement is counted exactly by two independent methods.
Usage: python generate_family.py [maximum_doublings, default 4]
"""
from verify_seed import *
from exterior_extension import best_exterior
import sys


def write_certificate(dest,lines,count,description,t):
    ar=arrangement(lines)
    assert len(ar['triangles'])==count
    n=len(lines)
    assert len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
    data=dict(n=n,triangle_count=count,lines_frac=[[str(x) for x in line] for line in lines],
              construction=description,doubling_steps=t,declared_parallel_pairs=[],
              priority_status='Not established; validity is certified independently of priority')
    path=dest/f'n{n:03d}.json';path.write_text(json.dumps(data,indent=2))
    result=verify(path);result.update(adjacency_count=count,simple=True)
    return result,ar


def extend_and_verify(dest,ar,t):
    lines=ar['lines'];n=len(lines);count=len(ar['triangles'])
    gain,added,b=best_exterior(ar)
    d=n*(n-2)-3*count
    assert b+d>=n
    g=((n-1)*max(3,3*count-n*(n-3))+2*n-1)//(2*n)
    assert gain>=g
    extended=arrangement(lines+[added]);newcount=len(extended['triangles'])
    assert newcount==count+gain
    assert set(ar['triangles'])<=set(extended['triangles'])
    ext,_=write_certificate(dest,lines+[added],newcount,'BBL family followed by an optimal exterior extension',t)
    ext.update(gain=gain,guaranteed_gain=g,free_ray_wedges=b,preserves_old_triangles=True)
    print('FAMILY',n,count,'EXTENSION',n+1,newcount,'gain',gain,'wedges',b,flush=True)
    return ext


def refresh_even():
    dest=Path(__file__).parent/'certificates'
    records=json.loads((dest.parent/'finite-verification.json').read_text())
    for i,record in enumerate(records):
        n=record['n']
        if n%2:continue
        old=dest/f'n{n-1:03d}.json'
        data=json.loads(old.read_text())
        ar=arrangement(data['lines_frac'])
        assert len(ar['triangles'])==data['triangle_count']
        records[i]=extend_and_verify(dest,ar,data['doubling_steps'])
    (dest.parent/'finite-verification.json').write_text(json.dumps(records,indent=2))


def generate(maximum_t=4):
    dest=Path(__file__).parent/'certificates';dest.mkdir(exist_ok=True)
    epsilon=min(EPS,F(1,4*Q*2**maximum_t))
    aa=[x.midpoint() for x in grid(epsilon)]
    lines=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(aa,V)]
    slopes=[1/v for v in V]
    sigma=1 if V[Q//2-1]>V[Q//2] else -1
    q=Q;records=[]
    for t in range(maximum_t+1):
        count=(q*q-4)//3
        result,ar=write_certificate(dest,lines,count,'Certified 11-line seed plus BBL doubling',t)
        assert sum(0 in tri for tri in ar['triangles'])==q-1
        records.append(result)
        records.append(extend_and_verify(dest,ar,t))
        if t==maximum_t:break
        positive=[tan_pi(k,2*q).midpoint() for k in range(1,q,2)]
        bb=[-x for x in positive[::-1]]+positive
        minimum=min(abs(m) for m in slopes)
        mm=[sigma*minimum/F(q**10)*(2*b/(1+b*b)+1/(q**6*b)) for b in bb]
        lines += [primitive((m,-1,m*b)) for m,b in zip(mm,bb)]
        slopes += mm;q*=2
    (dest.parent/'finite-verification.json').write_text(json.dumps(records,indent=2))
    return records


if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='--refresh-even':refresh_even()
    else:generate(int(sys.argv[1]) if len(sys.argv)>1 else 4)
