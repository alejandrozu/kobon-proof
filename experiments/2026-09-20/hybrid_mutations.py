"""Search realizable triangle flips by linear programming on a fixed BBL grid."""
from hybrid_doubling import *
from hybrid_search import save_result
import random,argparse


def matrix_data(aa,vv):
    n=len(aa);rows=[];lookup={}
    for i,j in it.combinations(range(n),2):
        sign=1 if vv[i]>vv[j] else -1
        row=np.zeros(n+1);row[i]=-sign;row[j]=sign;row[-1]=1
        lookup[(i,j)]=len(rows);rows.append(row)
    for i,j,k in it.combinations(range(n),3):
        d=(aa[j]-aa[k])*vv[i]+(aa[k]-aa[i])*vv[j]+(aa[i]-aa[j])*vv[k]
        assert d
        row=np.zeros(n+1);row[i]=float(aa[j]-aa[k]);row[j]=float(aa[k]-aa[i]);row[k]=float(aa[i]-aa[j])
        row/=max(abs(row));row*=(-1 if d>0 else 1);row[-1]=1
        lookup[(i,j,k)]=len(rows);rows.append(row)
    return np.array(rows),lookup


def run(path,seconds=90,seed=337):
    data=json.loads(Path(path).read_text());n=data['n']-1;mp.dps=75;eps=F(str(data['eps']))
    aa=sorted([F(str(mp.tan(mp.mpf(k)*mp.pi/n))) for k in range(-n//2+1,n//2) if k]+[-eps,eps])
    vv=[F(x) for x in data['v']];rng=random.Random(seed)
    make=lambda v:[(0,1,0)]+[primitive((1,-w,a)) for a,w in zip(aa,v)]
    ar=arrangement(make(vv));best=len(ar['triangles']);initial=best;bestv=vv.copy();score=best
    seen={tuple(sorted(ar['triangles']))};start=time.time();tested=0;accepted=0;last=start
    print('MUTATION START',n+1,best,flush=True)
    while time.time()-start<seconds:
        matrix,lookup=matrix_data(aa,vv)
        candidates=[tuple(i-1 for i in t) for t in ar['triangles'] if 0 not in t]
        order=sorted(range(n),key=lambda i:vv[i])
        candidates += [tuple(sorted((i,j))) for i,j in zip(order,order[1:])]
        rng.shuffle(candidates);options=[]
        for tri in candidates:
            ix=lookup[tri];mat=matrix.copy();mat[ix,:-1]*=-1
            obj=np.zeros(n+1);obj[-1]=-1
            res=linprog(obj,A_ub=mat,b_ub=np.zeros(len(mat)),bounds=[(-1,1)]*n+[(0,1)],method='highs')
            tested+=1
            if not res.success or res.x[-1]<1e-8:continue
            cand=[F(str(x)).limit_denominator(10**12) for x in res.x[:-1]]
            nar=arrangement(make(cand));newscore=len(nar['triangles'])
            if newscore<score:continue
            key=tuple(sorted(nar['triangles']))
            if key in seen:continue
            if len(nar['points'])!=n*(n+1)//2 or sum(0 in t for t in nar['triangles'])!=n-1:continue
            options.append((newscore,rng.random(),cand,nar,key))
            if newscore>best:break
            if time.time()-start>seconds:break
        if not options:break
        options.sort(key=lambda q:q[:2],reverse=True)
        score,_,vv,ar,key=options[0];seen.add(key);accepted+=1
        if score>best:
            best=score;bestv=vv.copy()
            out=data.copy();out.update(triangle_count=best,v=[str(v) for v in vv],
                                      operation='Compatible seed optimization by realizable triangle flips')
            Path(__file__).with_name(f'mutation-seed-{n+1}.json').write_text(json.dumps(out,indent=2))
            save_result(Path(__file__).with_name(f'mutation-lines-{n+1}.json'),ar['lines'],best,str(path),out['operation'],dict(tested=tested))
            print('MUTATION BEST',n+1,best,'tested',tested,'seconds',round(time.time()-start,2),flush=True)
        if time.time()-last>20:
            print('mutation progress',n+1,'best',best,'tested',tested,'accepted',accepted,'seconds',round(time.time()-start,2),flush=True);last=time.time()
    data.update(triangle_count=best,v=[str(v) for v in bestv])
    Path(__file__).with_name(f'mutation-seed-{n+1}.json').write_text(json.dumps(data,indent=2))
    report=dict(n=n+1,initial=initial,best=best,tested=tested,accepted=accepted,seconds=time.time()-start,seed=seed)
    Path(__file__).with_name(f'mutation-report-{n+1}.json').write_text(json.dumps(report,indent=2))
    print('MUTATION DONE',report,flush=True)
    double_finite(data,2)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('--seconds',type=int,default=90)
    p.add_argument('--seed',type=int,default=337);a=p.parse_args();run(a.path,a.seconds,a.seed)
