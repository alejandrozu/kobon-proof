"""Fit a published order type to a doubling-compatible grid with soft losses."""
from hybrid_doubling import *
from scipy.sparse import csr_matrix,hstack,vstack,eye
from hybrid_search import InsertionScore,save_result


def rows(base,aa):
    olda=[x[0] for x in base];oldv=[x[1] for x in base];n=len(base)
    soft=[];hard=[]
    for i,j in it.combinations(range(n),2):
        s=1 if oldv[i]>oldv[j] else -1
        q=np.zeros(n);q[i]=-s;q[j]=s;soft.append(q)
        if j==i+1:hard.append(q)
    for i,j,k in it.combinations(range(n),3):
        d=(olda[j]-olda[k])*oldv[i]+(olda[k]-olda[i])*oldv[j]+(olda[i]-olda[j])*oldv[k]
        if not d:continue
        q=np.zeros(n);q[i]=aa[j]-aa[k];q[j]=aa[k]-aa[i];q[k]=aa[i]-aa[j]
        q/=max(abs(q));q*=(-1 if d>0 else 1)
        soft.append(q)
        if j==i+1 or k==j+1:hard.append(q)
    return np.array(soft),np.array(hard)


def run(path,eps=.00001,limit=0):
    ls=read_lines(path);ar=arrangement(ls);n=len(ls)-1
    cnt=Counter(i for t in ar['triangles'] for i in t)
    ys=[i for i in range(n+1) if len(ar['rows'][i])==n and cnt[i]==n-1]
    if limit:ys=ys[:limit]
    mp.dps=75
    exacta=sorted([F(str(mp.tan(mp.mpf(k)*mp.pi/n))) for k in range(-n//2+1,n//2) if k]
                  +[-F(str(eps)),F(str(eps))])
    aa=list(map(float,exacta));best=-1;bestdata=None;history=[];start=time.time()
    for y in ys:
        soft,hard=rows(normalize(ls,y),aa)
        m=len(soft)
        mat=vstack([hstack([csr_matrix(soft),-eye(m)]),hstack([csr_matrix(hard),csr_matrix((len(hard),m))])]).tocsr()
        rhs=np.concatenate([np.full(m,-.001),np.full(len(hard),-.0001)])
        obj=np.concatenate([np.zeros(n),np.ones(m)])
        res=linprog(obj,A_ub=mat,b_ub=rhs,bounds=[(-1,1)]*n+[(0,None)]*m,method='highs')
        if not res.success:
            history.append(dict(y=y,success=False,status=res.message));continue
        # A mild, deterministic perturbation breaks accidental numerical ties.
        for variant in range(3):
            vv=[F(str(x)).limit_denominator(10**10)+F((i*31%17-8)*(variant+1),10**10)
                for i,x in enumerate(res.x[:n])]
            new=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(exacta,vv)]
            nar=arrangement(new);score=len(nar['triangles']);full=sum(0 in t for t in nar['triangles'])==n-1
            history.append(dict(y=y,variant=variant,score=score,saturated=full,soft_cost=res.fun))
            if not full:continue
            if score>best:
                best=score
                bestdata=dict(source=str(path),n=n+1,triangle_count=score,y=y,eps=eps,grid=aa,
                              v=[str(v) for v in vv],margin=.0001,
                              operation='Soft order-type fitting with the distinguished line fully saturated',
                              original_triangles=len(ar['triangles']))
                dest=Path(__file__).with_name(f'relaxed-seed-{n+1}.json')
                dest.write_text(json.dumps(bestdata,indent=2))
                save_result(Path(__file__).with_name(f'relaxed-lines-{n+1}.json'),new,score,str(path),bestdata['operation'],dict(y=y))
                print('RELAXED BEST',n+1,score,'Y',y,'cost',res.fun,'full',full,flush=True)
        if y%5==0:print('relaxed progress',n+1,y,'best',best,'seconds',round(time.time()-start,2),flush=True)
    Path(__file__).with_name(f'relaxed-report-{n+1}.json').write_text(json.dumps(history,indent=2))
    if bestdata:
        print('FINAL RELAXED',n+1,best,flush=True)
        double_finite(bestdata,2)


if __name__=='__main__':
    run(sys.argv[1],limit=int(sys.argv[2]) if len(sys.argv)>2 else 0)
