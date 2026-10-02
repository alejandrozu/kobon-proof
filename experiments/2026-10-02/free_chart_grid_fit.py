"""Fit an original projective pseudoline type to a tangent grid.

Unlike word_grid_fit, retain every original support and leave the new infinity
line unconstrained. For each distinguished support, rotate its cyclic order of
the other supports through every gap. Reorient supports crossing the cut.
Only the projective triple signs are prescribed; reciprocal-slope order is free.
Floating LP diagnostics are not nonrealizability certificates.
"""
from word_grid_fit import *


def free_signs(chi, I, shift):
    n=len(chi)-1;J=n;K=next(k for k in range(n)if k!=I)
    d=int(chi[I,J,K]);ids=[k for k in range(n)if k!=I]
    A={k:int(chi[k,I,J])for k in ids}
    def comparison(l,m):return -d*int(chi[l,m,I])*A[l]*A[m]
    ids.sort(key=cmp_to_key(comparison))
    for k in ids[:shift]:A[k]*=-1
    ids=ids[shift:]+ids[:shift]
    return ids,np.array([int(chi[l,m,k])*A[l]*A[m]*A[k]
                        for l,m,k in it.combinations(ids,3)],dtype=np.int8)


def run_free(source,out,epsilon=0.01,seconds=600,max_classes=0,saturated=False):
    source=source.resolve();out=out.resolve();out.mkdir(parents=True,exist_ok=True)
    started=time.time()
    if source.suffix=='.json':
        lines=read_lines(source);n=len(lines);lr=[(a,b,-c)for a,b,c in lines]+[(0,0,1)];entries=[]
        for i,j,k in it.combinations(range(n+1),3):
            a,b,c=lr[i];d,f,g=lr[j];h,z,w=lr[k]
            det=a*(f*w-g*z)-b*(d*w-g*h)+c*(d*z-f*h);assert det
            entries.append(((i,j,k),1 if det>0 else -1))
        prepared=[(n,tensor(n+1,entries))];attribution='Projective type of the attributed saved coordinate witness'
    else:
        raw=[s for s in source.read_text().splitlines()if ')'in s]
        prepared=[from_word(s)for s in raw];attribution='Parpalak--Utkin2026 projective types, independent coordinate fitting'
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        attribution=attribution,
        epsilon=epsilon,saturated=saturated,records=[],wins=[],scope='Floating diagnostics, not an infeasibility theorem')
    seen=set();cache={};best=0.;tested=0;duplicates=0;unsaturable=0
    for ci,(n,chi)in enumerate(prepared[:max_classes or None]):
        q=n-1
        if q not in cache:
            aa=np.array(sorted([math.tan(k*math.pi/q)for k in range(-q//2+1,q//2)if k]+[-epsilon,epsilon]))
            triples=list(it.combinations(range(q),3));M=np.zeros((len(triples),q+1))
            for r,(i,j,k)in enumerate(triples):
                M[r,i]=aa[j]-aa[k];M[r,j]=aa[k]-aa[i];M[r,k]=aa[i]-aa[j]
            M/=np.max(abs(M),axis=1)[:,None];cache[q]=(aa,M,triples)
        aa,M,triples=cache[q];obj=np.zeros(q+1);obj[-1]=-1
        for I,shift in it.product(range(n),range(q)):
            if time.time()-started>seconds:break
            ids,sg=free_signs(chi,I,shift);key=sg.tobytes()
            if key in seen:duplicates+=1;continue
            seen.add(key);mat=-sg[:,None]*M;mat[:,-1]=1
            if saturated:
                bytriple=dict(zip(triples,sg));extra=[]
                for i in range(q-1):
                    signs={int(bytriple[tuple(sorted((i,i+1,k)))])*(1 if k<i else -1)
                           for k in range(q)if k not in(i,i+1)}
                    if len(signs)!=1:break
                    sign=signs.pop();row=np.zeros(q+1);row[i]=-sign;row[i+1]=sign;row[-1]=1;extra.append(row)
                if len(extra)!=q-1:unsaturable+=1;continue
                mat=np.vstack([mat,extra])
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                opt=linprog(obj,A_ub=mat,b_ub=np.zeros(len(mat)),bounds=[(-1,1)]*q+[(0,1)],
                    method='highs',options={'threads':1,'time_limit':5})
            margin=float(opt.x[-1])if opt.success else None;tested+=1
            if margin is not None:best=max(best,margin)
            row=dict(class_index=ci,I=I,shift=shift,margin=margin,status=int(opt.status))
            report['records'].append(row)
            if margin is not None and margin>1e-8:
                # A tiny deterministic generic perturbation avoids coincident
                # reciprocal slopes without changing any strict triple sign.
                vv=opt.x[:-1]+np.arange(q)*margin/(100*q)
                vv=[F(float(x)).limit_denominator(10**10)for x in vv]
                if vv[q//2-1]<vv[q//2]:vv=[-v for v in vv]
                vv=[v+2 for v in vv]
                eps=F(str(epsilon or 1e-7));intercepts=[F(float(x)).limit_denominator(10**12)for x in aa]
                intercepts[q//2-1]=-eps;intercepts[q//2]=eps
                lines=[(0,1,0)]+[primitive((1,-v,a))for a,v in zip(intercepts,vv)]
                ar=arrangement(lines);T=len(ar['triangles']);caps=sum(0 in t for t in ar['triangles'])
                path=out/f'n{n:03d}-class{ci:04d}-I{I:02d}-cut{shift:02d}.json'
                data=dict(n=n,triangle_count=T,lines_frac=[[str(x)for x in l]for l in lines],
                    reciprocal_slopes=[str(v)for v in vv],epsilon=str(eps),Y0_triangles=caps,
                    source=str(source.relative_to(ROOT)),source_class=ci,distinguished=I,cut=shift,
                    line_labels=ids,numerical_lp_margin=margin,
                    verification='Exact rational midpoint only; true-tangent interval verification pending')
                path.write_text(json.dumps(data,indent=2)+'\n');direct=verify(path)
                data['direct']=direct;path.write_text(json.dumps(data,indent=2)+'\n')
                report['wins'].append(str(path.relative_to(ROOT)))
                print(json.dumps(dict(event='feasible',n=n,T=T,caps=caps,**row)),flush=True)
            if tested%200==0:
                print(json.dumps(dict(event='progress',tested=tested,duplicates=duplicates,best=best,seconds=time.time()-started)),flush=True)
        if time.time()-started>seconds:break
    report.update(tested=tested,duplicates=duplicates,unsaturable=unsaturable,best_margin=best,seconds=time.time()-started)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(event='done',tested=tested,duplicates=duplicates,unsaturable=unsaturable,best=best,wins=len(report['wins']),seconds=report['seconds'])),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--epsilon',type=float,default=.01);p.add_argument('--seconds',type=float,default=600)
    p.add_argument('--max-classes',type=int,default=0)
    p.add_argument('--saturated',action='store_true')
    a=p.parse_args();run_free(a.source,a.out,a.epsilon,a.seconds,a.max_classes,a.saturated)
