"""Explore selected boundary faces of the normalized 19-line realization cone."""
from seed_search import *

def force_equalities(eq,v):
    n=len(v);a=[list(row) for row in eq];piv=[];r=0
    for c in range(n):
        j=next((j for j in range(r,len(a)) if a[j][c]),None)
        if j is None:continue
        a[r],a[j]=a[j],a[r];z=a[r][c];a[r]=[x/z for x in a[r]]
        for j in range(len(a)):
            if j!=r and a[j][c]:
                z=a[j][c];a[j]=[x-z*y for x,y in zip(a[j],a[r])]
        piv.append(c);r+=1
        if r==len(a):break
    vv=[F(float(x)).limit_denominator(10**12) for x in v]
    for row,c in zip(a,piv):vv[c]=-sum(row[j]*vv[j] for j in range(n) if j not in piv)
    return vv

def run(samples=1000):
    original=[primitive((F(m),-1,-F(b))) for m,b in list(csv.reader(open(Path(__file__).with_name('series18-lines.csv'))))[1:]]
    base=normalize(original,0);n=18
    aa=sorted([F(math.tan(k*math.pi/n)).limit_denominator(10**9) for k in range(-8,9) if k]+[-F(1,10**6),F(1,10**6)])
    olda=[x[0] for x in base];oldv=[x[1] for x in base]
    source_ar=arrangement([(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(olda,oldv)])
    candidates=[tuple(i-1 for i in tri) for tri in source_ar['triangles'] if 0 not in tri]
    raw=[];lookup={}
    for i,j in it.combinations(range(n),2):
        sign=-1 if oldv[i]>oldv[j] else 1
        q=[F(0)]*n;q[i]=sign;q[j]=-sign;raw.append(q)
    for i,j,k in it.combinations(range(n),3):
        d=(olda[j]-olda[k])*oldv[i]+(olda[k]-olda[i])*oldv[j]+(olda[i]-olda[j])*oldv[k]
        sign=-1 if d>0 else 1
        q=[F(0)]*n;q[i]=sign*(aa[j]-aa[k]);q[j]=sign*(aa[k]-aa[i]);q[k]=sign*(aa[i]-aa[j])
        lookup[(i,j,k)]=len(raw);raw.append(q)
    mat=np.array(raw,dtype=float);scale=np.max(abs(mat),axis=1);mat/=scale[:,None]
    obj=np.zeros(n+1);obj[-1]=-1
    jobs=[(x,) for x in candidates]+list(it.combinations(candidates,2))
    random.Random(42).shuffle(jobs)
    jobs=jobs[:samples]
    best=0;feasible=0;counts=Counter()
    for trial,chosen in enumerate(jobs):
        ids=[lookup[x] for x in chosen];eq=mat[ids];others=np.delete(mat,ids,axis=0)
        result=linprog(obj,A_ub=np.column_stack((others,np.ones(len(others)))),b_ub=np.zeros(len(others)),
                       A_eq=np.column_stack((eq,np.zeros(len(eq)))),b_eq=np.zeros(len(eq)),
                       bounds=[(-1,1)]*n+[(0,1)],method='highs')
        if not result.success or result.x[-1]<1e-8:continue
        vv=force_equalities([raw[i] for i in ids],result.x[:-1])
        if any(sum(x*y for x,y in zip(q,vv))>=0 for i,q in enumerate(raw) if i not in ids):continue
        feasible+=1
        ls=[(0,1,0)]+[primitive((1,-v,a)) for v,a in zip(vv,aa)];ar=arrangement(ls)
        T=len(ar['triangles']);counts[T]+=1
        if T<105:continue
        score,r=far_extensions(ar)
        if score>best:
            best=score;print('BEST',trial,'core',T,'even',score,'collapsed',chosen,flush=True)
            out=dict(n=20,triangle_count=score,lines_frac=[[str(x) for x in l] for l in ls+[r]],collapsed=chosen)
            Path(__file__).with_name('collapse-best.json').write_text(json.dumps(out,indent=2))
        if trial%100==0:print('progress',trial,'feasible',feasible,'counts',dict(counts),flush=True)
    print('DONE trials',len(jobs),'feasible',feasible,'best',best,'counts',dict(counts),flush=True)

if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 1000)
