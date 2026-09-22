"""Score oriented-matroid boundary contractions; realize useful ones by LP.

All candidate gains are combinatorial until exact rational reconstruction and
both direct recounts pass. Fixed normals make determinant conditions linear
in offsets. A floating LP rejection is not an exact infeasibility theorem.
"""
import argparse,collections,itertools,json,math,sys,time
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/general-bounds-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
sys.path.insert(0,str(Path(__file__).parent))
import numpy as np
from scipy.optimize import linprog
from exact_geometry import arrangement,read_lines,intersection,primitive
from check_pu_current import direct_count
OUT=ROOT/'research/six-hour-2026-09-21/general-bounds/collapses'

def det(a,b,c):return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])

class Census:
    def __init__(self,ls):
        self.ls=ls;self.n=n=len(ls);self.triples=list(itertools.combinations(range(n),3))
        self.det={t:det(*(ls[i]for i in t))for t in self.triples}
        assert all(self.det.values()),'This initial search expects a simple base'
        self.pos={};self.neg={}
        for i,j in itertools.combinations(range(n),2):
            p=intersection(ls[i],ls[j]);assert p
            x,y,w=p;P=N=0
            for k,(a,b,c)in enumerate(ls):
                ev=a*x+b*y-c*w
                if ev>0:P|=1<<k
                if ev<0:N|=1<<k
            self.pos[i,j]=P;self.neg[i,j]=N
        self.faces=set(t for t in self.triples if self.face(t,self.pos,self.neg))
    @staticmethod
    def face(t,P,N):
        i,j,k=t
        return not ((P[i,j]|P[i,k]|P[j,k])&(N[i,j]|N[i,k]|N[j,k]))
    def collapse(self,zeros):
        P=self.pos.copy();N=self.neg.copy();affected=set()
        for t in zeros:
            for pair in itertools.combinations(t,2):
                k=next(i for i in t if i not in pair);P[pair]&=~(1<<k);N[pair]&=~(1<<k)
                affected.update(tuple(sorted((*pair,k)))for k in range(self.n)if k not in pair)
        new={t for t in affected if t not in zeros and self.face(t,P,N)}
        return len(self.faces)+len(new)-len(self.faces&affected),self.faces.difference(affected)|new

def realize(census,zeros,timeout):
    n=census.n; ls=census.ls
    # Scaling each row by a positive normal factor keeps orientation signs.
    L=np.array([[float(F(x,max(abs(l[0]),abs(l[1]))))for x in l]for l in ls])
    A=[];Z=[]
    for t in census.triples:
        i,j,k=t; row=np.zeros(n+1)
        row[i]=L[j,0]*L[k,1]-L[j,1]*L[k,0]
        row[j]=L[k,0]*L[i,1]-L[k,1]*L[i,0]
        row[k]=L[i,0]*L[j,1]-L[i,1]*L[j,0]
        row/=max(abs(row[:-1]))
        if t in zeros:Z.append(row)
        else:
            row*=-(1 if census.det[t]>0 else -1);row[-1]=1;A.append(row)
    # Two affine translation gauges, plus fixed offset scale through bounded c.
    objective=np.zeros(n+1);objective[-1]=-1
    res=linprog(objective,A_ub=np.array(A),b_ub=np.zeros(len(A)),
        A_eq=np.array(Z),b_eq=np.zeros(len(Z)),bounds=[(-1,1)]*n+[(0,1)],
        method='highs',options={'time_limit':timeout})
    if not res.success or res.x[-1]<1e-9:return None,dict(status=int(res.status),message=res.message,margin=float(res.x[-1])if res.x is not None else None)
    info=dict(status=int(res.status),margin=float(res.x[-1]))
    # Reconstruct free offsets, then impose concurrent triples exactly.
    common=set.intersection(*map(set,zeros));Y=min(common)
    dependents=[min(set(t)-{Y})for t in zeros]
    if len(set(dependents))!=len(dependents):return None,dict(info,reason='overlapping dependent supports')
    for denom in [10**6,10**9,10**12]:
        rat=[(F(a),F(b),F(float(res.x[i])).limit_denominator(denom)*max(abs(a),abs(b)))for i,(a,b,c)in enumerate(ls)]
        for t,b in zip(zeros,dependents):
            a=next(i for i in t if i not in {Y,b})
            p=intersection(primitive(rat[Y]),primitive(rat[a]));assert p
            ab,bb,_=rat[b];rat[b]=(ab,bb,(ab*p[0]+bb*p[1])/p[2])
        ints=[primitive(l)for l in rat]
        # Primitive may reverse a row; compare with the original normalization.
        for i in range(n):
            if ints[i][0]*ls[i][0]+ints[i][1]*ls[i][1]<0:ints[i]=tuple(-v for v in ints[i])
        newdet={t:det(*(ints[i]for i in t))for t in census.triples}
        if all((not newdet[t])if t in zeros else(newdet[t]*census.det[t]>0)for t in census.triples):
            ar=arrangement(ints); data=dict(n=n,triangle_count=len(ar['triangles']),lines_frac=[[str(v)for v in l]for l in ints])
            assert set(direct_count(data))==set(ar['triangles'])
            data.update(triangles=sorted(ar['triangles']),collapsed_triples=sorted(zeros),lp_margin=info['margin'],reconstruction_denominator=denom)
            return data,info
    return None,dict(info,reason='exact reconstruction did not retain all required signs')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',default='research/finite-table/classical-044.json');ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--lp-seconds',type=float,default=10);args=ap.parse_args()
    OUT.mkdir(exist_ok=True);start=time.monotonic();ls=read_lines(ROOT/args.source);C=Census(ls);n=C.n
    best=len(C.faces);candidates=[];hist=collections.Counter()
    for t in C.faces:
        score,_=C.collapse({t});hist[f'single-{score-best}']+=1
        if score>best:candidates.append((score,(t,)))
    for y in range(n):
        faces=[t for t in C.faces if y in t]
        for a,b in itertools.combinations(faces,2):
            if set(a)&set(b)!={y}:continue
            score,_=C.collapse({a,b});hist[f'pair-{score-best}']+=1
            if score>best:candidates.append((score,(a,b)))
    candidates.sort(reverse=True);print('BASE',n,best,'BOUNDARY HISTOGRAM',dict(hist),'IMPROVING',len(candidates),flush=True)
    report=dict(n=n,source=args.source,base_triangles=best,boundary_histogram=dict(hist),candidates=len(candidates),attempts=[])
    for score,ts in candidates:
        if time.monotonic()-start>args.seconds:break
        data,info=realize(C,set(ts),args.lp_seconds);info.update(predicted=score,triples=ts);report['attempts'].append(info)
        if data:
            assert data['triangle_count']==score
            data['source']=args.source;data['construction']='Exact concurrent-face boundary of the source arrangement, fixed normals LP and rational reconstruction'
            path=OUT/f'n{n:03d}-T{score:05d}-{len(report["attempts"]):05d}.json';path.write_text(json.dumps(data,indent=2)+'\n')
            print('EXACT SUCCESS',str(path),flush=True)
        if len(report['attempts'])%10==0:print('ATTEMPTS',len(report['attempts']),'SECONDS',round(time.monotonic()-start,1),flush=True)
    report['seconds']=time.monotonic()-start
    (OUT/f'report-{n:03d}.json').write_text(json.dumps(report,indent=2)+'\n')
    print('DONE',report['seconds'],len(report['attempts']),flush=True)

if __name__=='__main__':main()
