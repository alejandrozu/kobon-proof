"""Search exact degenerations of the published 19-line iterative seed.
All prospective records are independently counted with rational arithmetic.
The tangent grid here is rationally approximated; it is not an infinite proof.
"""
import csv
import random
from functools import cmp_to_key
from normalize_search import *

def solve_exact(matrix, vector):
    a=[[F(x) for x in row]+[F(y)] for row,y in zip(matrix,vector)]
    n=len(a)
    for col in range(n):
        p=next((r for r in range(col,n) if a[r][col]),None)
        if p is None:return None
        a[col],a[p]=a[p],a[col]
        z=a[col][col];a[col]=[x/z for x in a[col]]
        for r in range(n):
            if r!=col and a[r][col]:
                z=a[r][col];a[r]=[x-z*y for x,y in zip(a[r],a[col])]
    return [row[-1] for row in a]

def unbounded_wedges(a):
    ls=a['lines'];rows=a['rows'];wedges=[]
    def compare(u,v):
        x,y=u[:2];z,w=v[:2]
        hu=0 if (y>0 or y==0 and x>0) else 1
        hv=0 if (w>0 or w==0 and z>0) else 1
        if hu!=hv:return hu-hv
        cross=x*w-y*z
        return -1 if cross>0 else 1 if cross<0 else 0
    for p,incident in a['points'].items():
        rays=[]
        for i in incident:
            A,B,C=ls[i];dx,dy=B,-A
            if (B and dx<0) or (not B and dy<0): dx,dy=-dx,-dy
            rays.append((dx,dy,p==rows[i][-1]))
            rays.append((-dx,-dy,p==rows[i][0]))
        rays.sort(key=cmp_to_key(compare))
        for r,s in zip(rays,rays[1:]+rays[:1]):
            if r[2] and s[2] and r[0]*s[1]-r[1]*s[0]>0:
                wedges.append((r[:2],s[:2]))
    return wedges

def far_extensions(a):
    ls=a['lines'];pts=a['points']; n=len(ls)
    # Projection x-alpha*y. Breakpoints occur at directions of the old lines.
    vv=sorted(set(-F(b,a) for a,b,c in ls if a))
    aa=[vv[0]-1]+[(v+w)/2 for v,w in zip(vv,vv[1:])]+[vv[-1]+1]
    best=len(a['triangles']);winner=None;wedges=unbounded_wedges(a)
    for alpha in aa:
        for sign in (1,-1):
            score=len(a['triangles'])+sum(sign*(r[0]-alpha*r[1])>0 and sign*(s[0]-alpha*s[1])>0 for r,s in wedges)
            if score>best:
                proj=[F(p[0],p[2])-alpha*F(p[1],p[2]) for p in pts]
                d=max(proj)+1 if sign>0 else min(proj)-1
                best=score;winner=primitive((1,-alpha,d))
    if winner is not None:
        assert len(arrangement(ls+[winner])['triangles'])==best
    return best,winner

def search(samples=100, seed=1):
    original=[primitive((F(m),-1,-F(b))) for m,b in list(csv.reader(open(Path(__file__).with_name('series18-lines.csv'))))[1:]]
    base=normalize(original,0);n=18
    aa=sorted([F(math.tan(k*math.pi/n)).limit_denominator(10**9) for k in range(-8,9) if k]+[-F(1,10**6),F(1,10**6)])
    olda=[x[0] for x in base];oldv=[x[1] for x in base]
    raw=[];rhs=[]
    order=sorted(range(n),key=lambda i:oldv[i])
    for i,j in zip(order,order[1:]):
        row=[F(0)]*n;row[i]=1;row[j]=-1;raw.append(row);rhs.append(-F(1,1000))
    for i,j,k in it.combinations(range(n),3):
        d=(olda[j]-olda[k])*oldv[i]+(olda[k]-olda[i])*oldv[j]+(olda[i]-olda[j])*oldv[k]
        s=-1 if d>0 else 1
        row=[F(0)]*n;row[i]=s*(aa[j]-aa[k]);row[j]=s*(aa[k]-aa[i]);row[k]=s*(aa[i]-aa[j])
        raw.append(row);rhs.append(F(0))
    for i in range(n):
        for sign in (-1,1):
            row=[F(0)]*n;row[i]=sign;raw.append(row);rhs.append(F(1))
    mat=np.array(raw,dtype=float);bb=np.array(rhs,dtype=float)
    scale=np.max(np.abs(mat),axis=1);mat=mat/scale[:,None];bb=bb/scale
    rng=np.random.default_rng(seed);best=0;seen=set();hist=Counter();checked=0
    for trial in range(samples):
        result=linprog(rng.normal(size=n),A_ub=mat,b_ub=bb,bounds=[(None,None)]*n,method='highs')
        if not result.success:continue
        active=np.flatnonzero(abs(mat@result.x-bb)<1e-7)
        key=tuple(active)
        if key in seen:continue
        seen.add(key)
        independent=[];rows=[]
        for ix in active:
            if np.linalg.matrix_rank(np.array(rows+[mat[ix].tolist()]),tol=1e-9)>len(rows):
                rows.append(mat[ix].tolist());independent.append(ix)
            if len(rows)==n:break
        if len(rows)<n:continue
        exact=solve_exact([raw[ix] for ix in independent],[rhs[ix] for ix in independent])
        if exact is None or any(sum(x*y for x,y in zip(row,exact))>bound for row,bound in zip(raw,rhs)):continue
        lines=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(aa,exact)]
        ar=arrangement(lines);T=len(ar['triangles']);hist[T]+=1;checked+=1
        if T<103:continue
        score,r=far_extensions(ar)
        if score>best:
            best=score
            mult=[sorted(x) for x in ar['points'].values() if len(x)>2]
            print('BEST trial',trial,'core',T,'even',score,'mult',mult,flush=True)
            out={'source':'LP degeneration of Parpalak-Utkin 19-line seed; rational approximation to tangent grid',
                 'n':20,'triangle_count':score,'lines_frac':[[str(x) for x in l] for l in lines+[r]],
                 'core_count':T,'a':[str(x) for x in aa],'v':[str(x) for x in exact]}
            Path(__file__).with_name('seed-search-best.json').write_text(json.dumps(out,indent=2))
        if trial%10==0: print('progress',trial,'exact checked',checked,'hist',dict(hist),flush=True)
    print('DONE exact checked',checked,'best',best,'core counts',dict(hist),flush=True)

if __name__=='__main__': search(int(sys.argv[1]) if len(sys.argv)>1 else 100)
