"""Find tangent-grid realizations of published seeds, then verify BBL doubles.

LP/trigonometry propose rational lines. Exact counters certify each finite
arrangement. Success at finite orders does not itself prove an infinite family.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
from normalize_search import *
from mpmath import mp
import time


def find_seed(path,eps=1e-6,limit=0):
    ls=read_lines(path);ar=arrangement(ls);n=len(ls)-1
    counts=Counter(i for tri in ar['triangles'] for i in tri)
    ys=[i for i in range(n+1) if len(ar['rows'][i])==n and counts[i]==n-1]
    if limit:ys=ys[:limit]
    agrid=sorted([math.tan(k*math.pi/n) for k in range(-n//2+1,n//2) if k]+[-eps,eps])
    print('start grid search',path,'triangles',len(ar['triangles']),'Y candidates',len(ys),flush=True)
    reports=[]
    for y in ys:
        t=time.time();base=normalize(ls,y)
        res=constraints(base,agrid)
        margin=float(res.x[-1]) if res.success else 0
        report=dict(y=y,margin=margin,seconds=time.time()-t,status=res.message)
        reports.append(report)
        print('grid',len(ls),'Y',y,'margin',margin,'seconds',round(report['seconds'],2),flush=True)
        if margin>1e-9:
            out=dict(source=str(path),n=len(ls),triangle_count=len(ar['triangles']),y=y,eps=eps,
                     grid=agrid,v=res.x[:-1].tolist(),margin=margin,
                     original_normalized_a=[str(x[0]) for x in base],
                     original_normalized_v=[str(x[1]) for x in base])
            dest=Path(__file__).with_name(f'grid-seed-{n+1}-y{y}.json')
            dest.write_text(json.dumps(out,indent=2))
            print('FEASIBLE',dest,flush=True)
            return out
    Path(__file__).with_name(f'grid-report-{n+1}.json').write_text(json.dumps(reports,indent=2))
    return None


def double_finite(data,t=1,digits=70):
    mp.dps=digits
    n=data['n']-1
    aa=sorted([F(str(mp.tan(mp.mpf(k)*mp.pi/n))) for k in range(-n//2+1,n//2) if k]
              +[-F(str(data['eps'])),F(str(data['eps']))])
    vv=[F(str(x)) for x in data['v']]
    ls=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(aa,vv)]
    ar=arrangement(ls)
    assert len(ar['triangles'])==data['triangle_count'],(len(ar['triangles']),data['triangle_count'])
    assert all(len(v)==2 for v in ar['points'].values())
    slopes=[1/v for v in vv]
    # sigma is +1 if the two central exceptional lines meet above Y0.
    i,j=n//2-1,n//2
    p=intersection(ls[i+1],ls[j+1]);sigma=1 if p[1]>0 else -1
    for step in range(t):
        bb=[F(str(mp.tan(-mp.pi/2+(mp.mpf(j)-mp.mpf('0.5'))*mp.pi/n))) for j in range(1,n+1)]
        minimum=min(abs(x) for x in slopes)
        mm=[sigma*minimum/F(n**10)*(2*b/(1+b*b)+1/(n**6*b)) for b in bb]
        ls += [primitive((m,-1,m*b)) for m,b in zip(mm,bb)]
        slopes += mm
        count=len(arrangement(ls)['triangles'])
        expected=len(ar['triangles'])+n*n
        assert count==expected,(count,expected)
        n*=2;ar=arrangement(ls)
        out=dict(n=len(ls),triangle_count=count,lines_frac=[[str(x) for x in l] for l in ls],
                 source=data['source'],seed_y=data['y'],doubling_steps=step+1,
                 operation='LP tangent-grid realization followed by BBL doubling; finite rational certificate',
                 declared_parallel_pairs=[])
        dest=Path(__file__).with_name(f'doubled-{len(ls)}.json');dest.write_text(json.dumps(out,indent=2))
        print('EXACT DOUBLE',len(ls),count,'saved',dest,flush=True)
    return out


if __name__=='__main__':
    for s in sys.argv[1:]:
        result=find_seed(s)
        if result:double_finite(result)
