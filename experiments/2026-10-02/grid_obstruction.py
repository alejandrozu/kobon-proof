"""Extract small positive dependencies obstructing tangent-grid type fitting.

The first stage is floating discovery only. Exact certificates, if produced,
are verified separately and must distinguish rounded-grid from true-grid data.
"""
from free_chart_grid_fit import *


def rows_for(chi,I,shift,epsilon):
    n=len(chi)-1;q=n-1;ids,sg=free_signs(chi,I,shift)
    triples=list(it.combinations(range(q),3));bytriple=dict(zip(triples,sg));caps=[]
    for i in range(q-1):
        signs={int(bytriple[tuple(sorted((i,i+1,k)))])*(1 if k<i else -1)
               for k in range(q)if k not in(i,i+1)}
        if len(signs)!=1:return None
        caps.append(signs.pop())
    aa=np.array(sorted([math.tan(k*math.pi/q)for k in range(-q//2+1,q//2)if k]+[-epsilon,epsilon]))
    M=np.zeros((len(triples)+q-1,q));meta=[]
    for r,((i,j,k),s)in enumerate(zip(triples,sg)):
        M[r,i]=s*(aa[j]-aa[k]);M[r,j]=s*(aa[k]-aa[i]);M[r,k]=s*(aa[i]-aa[j]);meta.append(['triple',i,j,k,int(s)])
    for r,(i,s)in enumerate(enumerate(caps),len(triples)):
        M[r,i]=s;M[r,i+1]=-s;meta.append(['cap',i,i+1,s])
    return ids,aa,M,meta


def discover(source,out,epsilon):
    source=source.resolve();out=out.resolve();out.mkdir(parents=True,exist_ok=True)
    raw=[s for s in source.read_text().splitlines()if ')'in s];seen=set();records=[];sizes={};start=time.time()
    for ci,rawline in enumerate(raw):
        n,chi=from_word(rawline);q=n-1
        for I,shift in it.product(range(n),range(q)):
            rs=rows_for(chi,I,shift,epsilon)
            if rs is None:continue
            ids,aa,M,meta=rs;key=M.tobytes()
            if key in seen:continue
            seen.add(key);norm=np.max(abs(M),axis=1);mat=np.column_stack([-M/norm[:,None],np.ones(len(M))]);obj=np.zeros(q+1);obj[-1]=-1
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                opt=linprog(obj,A_ub=mat,b_ub=np.zeros(len(mat)),bounds=[(-1,1)]*q+[(0,1)],method='highs',options={'threads':1})
            assert opt.success
            ys=-opt.ineqlin.marginals/norm;active=np.flatnonzero(ys>1e-9);weights=ys[active]
            err=float(np.max(abs(weights@M[active])))if len(active)else None
            row=dict(class_index=ci,I=I,shift=shift,margin=float(opt.x[-1]),
                support=[meta[i]for i in active],weights=weights.tolist(),floating_residual=err)
            sizes[len(active)]=sizes.get(len(active),0)+1;records.append(row)
    report=dict(source=str(source.relative_to(ROOT)),epsilon=epsilon,records=records,
       support_histogram=sizes,seconds=time.time()-start,status='Floating support discovery only; not exact certificates')
    (out/'supports.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(cases=len(records),sizes=sizes,seconds=report['seconds'])),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--epsilon',type=float,default=.01)
    a=p.parse_args();discover(a.source,a.out,a.epsilon)
