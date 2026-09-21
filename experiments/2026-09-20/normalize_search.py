"""Exploratory LP test of a fixed intersection grid. This is not a proof."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent/'vendor'))
import numpy as np
from scipy.optimize import linprog
from research import *

def normalize(lines, y):
    # Coordinate change X=x, Y=a_y*x+b_y*y-c_y; swap x,y if needed.
    if not lines[y][1]: lines=[(b,a,c) for a,b,c in lines]
    ay,by,cy=lines[y]
    result=[]
    for i,(a,b,c) in enumerate(lines):
        if i==y: continue
        A=F(a)-F(b*ay,by); B=F(b,by); C=F(c)-F(b*cy,by)
        assert A
        result.append((C/A,-B/A,i))
    return sorted(result)

def constraints(base, aa, epsilon=1e-4):
    olda=[v[0] for v in base]; oldv=[v[1] for v in base]; n=len(base)
    ub=[]; eq=[]
    for i,j in it.combinations(range(n),2):
        s=1 if oldv[i]>oldv[j] else -1
        q=np.zeros(n+1); q[i]=-s; q[j]=s; q[-1]=1
        ub.append(q)
    for i,j,k in it.combinations(range(n),3):
        d=(olda[j]-olda[k])*oldv[i]+(olda[k]-olda[i])*oldv[j]+(olda[i]-olda[j])*oldv[k]
        q=np.zeros(n+1);q[i]=aa[j]-aa[k];q[j]=aa[k]-aa[i];q[k]=aa[i]-aa[j]
        size=max(abs(q));q/=size
        if not d: eq.append(q)
        else:
            q *= -1 if d>0 else 1
            q[-1]=1
            ub.append(q)
    obj=np.zeros(n+1);obj[-1]=-1
    return linprog(obj,A_ub=ub,b_ub=np.zeros(len(ub)),
                   A_eq=eq or None,b_eq=np.zeros(len(eq)) if eq else None,
                   bounds=[(-1,1)]*n+[(0,1)],method='highs')

def run(path,r):
    ls=read_lines(path);a=arrangement(ls); n=len(ls)-2
    reduced=[l for i,l in enumerate(ls) if i!=r]
    ar=arrangement(reduced);cnt=Counter(i for t in ar['triangles'] for i in t)
    candidates=[(y if y<r else y+1) for y in range(n+1)
        if len(ar['rows'][y])==n and cnt[y]==n-1]
    print(path, 'removed',r,'candidate Ys',candidates,flush=True)
    for y in candidates:
        base=normalize(ls,y)
        ir=next(i for i,t in enumerate(base) if t[2]==r)
        other=[t for t in base if t[2]!=r]
        agrid=[math.tan(k*math.pi/n) for k in range(-n//2+1,n//2) if k]+[-1e-6,1e-6]
        agrid.sort()
        # Try an affine exterior line or interior one at several placements.
        if ir==0: options=[-agrid[-1]*q for q in (1.5,5,100,10000)]
        elif ir==n: options=[agrid[-1]*q for q in (1.5,5,100,10000)]
        else: options=[agrid[ir-1]*(1-q)+agrid[ir]*q for q in (.1,.5,.9)]
        best=0; bestdata=None
        for arval in options:
            aa=agrid.copy();aa.insert(ir,arval)
            res=constraints(base,aa)
            margin=res.x[-1] if res.success else 0
            if margin>best:
                best=margin;bestdata=(aa,res.x[:-1].tolist())
        print('Y',y,'R slot',ir,'margin',best,flush=True)
        if best>1e-9:
            out=dict(source=path,removed=r,Y=y,base_labels=[x[2] for x in base],a=bestdata[0],v=bestdata[1],margin=best)
            Path(__file__).with_name(f'lp-{len(ls)}-r{r}-y{y}.json').write_text(json.dumps(out,indent=2))

if __name__=='__main__': run(sys.argv[1],int(sys.argv[2]))
