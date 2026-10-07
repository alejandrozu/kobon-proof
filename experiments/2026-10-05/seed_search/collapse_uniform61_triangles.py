"""Exact topology and LP screen for concurrent surgeries of the uniform61 seed.

The three vertices of an empty triangle are merged into one actual triple
point. Strict distinguished-axis cap apices are excluded. Floating LP outputs
are rationally reconstructed in the exact concurrency kernel and recounted.
The existing simple BBL recurrence is not asserted for a concurrent result.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,sys,itertools as it,time,warnings,hashlib,argparse,math
ROOT=Path(__file__).resolve().parents[3]
for p in ['research/kobon-hybrid','experiments/2026-10-05/corpus']:
    sys.path.insert(0,str(ROOT/p))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement,primitive
from facet_walk61 import np,matrix,sparse,linprog
from raise_existing_core import exact_nullspace_round
from check_global_token_hypotheses import ledger

def collapsed_count(ar,Q):
    points=list(ar['points']);ids={p:i for i,p in enumerate(points)};cluster={ids[p] for p,s in ar['points'].items() if len(s&set(Q))==2};assert len(cluster)==math.comb(len(Q),2);hub=len(points);rows=[]
    for row in ar['rows']:
        rr=[hub if ids[p] in cluster else ids[p] for p in row];rows.append([v for j,v in enumerate(rr) if j==0 or rr[j-1]!=v])
    edges={};adj={v:set() for row in rows for v in row}
    for i,row in enumerate(rows):
        for a,b in zip(row,row[1:]):e=tuple(sorted((a,b)));assert e not in edges;edges[e]=i;adj[a].add(b);adj[b].add(a)
    triangles=[]
    for a in adj:
        for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
            if c not in adj[b]:continue
            labels=tuple(sorted(edges[tuple(sorted(e))] for e in [(a,b),(a,c),(b,c)]))
            if len(set(labels))==3:triangles.append(labels)
    return len(triangles),sum(0 in t for t in triangles)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=180);args=ap.parse_args();start=time.time()
    source=ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json';raw=json.loads(source.read_text());bounds=[(F(a)+F(b))/2 for a,b in zip(raw['lo'],raw['hi'])];roots=[bounds[p]*s for p,s in raw['labels'][1:]];slopes=list(map(F,raw['slopes'][1:]));h=[1/m for m in slopes];lines=[(F(0),F(1),F(0))]+[(F(1),-hh,a) for hh,a in zip(h,roots)];ar=arrangement(lines);assert len(ar['triangles'])==1190
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/collapse-uniform61';out.mkdir(parents=True,exist_ok=True);scores=[];hist=Counter()
    for Q in ar['triangles']:
        if 0 in Q:continue
        # Any adjacent-index pair is an apex of a distinguished axis cap.
        if any(abs(a-b)==1 for a,b in it.combinations(Q,2)):continue
        T,caps=collapsed_count(ar,Q);hist[T]+=1;rec=dict(Q=Q,T=T,caps=caps);scores.append(rec)
    A,triples,pairs=matrix(np.array(list(map(float,roots))));sg=np.sign(A@np.array(list(map(float,h))));assert all(sg!=0);records=[];wins=[]
    for score in sorted(scores,key=lambda r:r['T'],reverse=True):
        if time.time()-start>args.seconds:break
        if score['T']<=1190 or score['caps']!=59:continue
        Q=score['Q'];qq=tuple(i-1 for i in Q);row=triples[qq];strict=np.array([r for r in range(A.shape[0]) if r!=row]);M=sparse.hstack([-sparse.diags(sg[strict])@A[strict],np.ones((len(strict),1))],format='csr');E=sparse.hstack([A[row],sparse.csr_matrix((1,1))],format='csr');obj=np.zeros(61);obj[-1]=-1
        with warnings.catch_warnings():
            warnings.simplefilter('ignore');lp=linprog(obj,A_ub=M,b_ub=np.zeros(len(strict)),A_eq=E,b_eq=np.zeros(1),bounds=[(-1,1)]*60+[(0,1)],method='highs',options={'threads':1,'time_limit':10,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
        margin=float(lp.x[-1]) if lp.success else 0;rec=dict(score,margin=margin,status=int(lp.status),passed=False);records.append(rec)
        if margin<1e-9:continue
        i,j,k=qq;coef=[F(0)]*60;coef[i]=roots[j]-roots[k];coef[j]=roots[k]-roots[i];coef[k]=roots[i]-roots[j];hh=exact_nullspace_round([coef],lp.x[:-1]);hh=[x+2 for x in hh];candidate=[(F(0),F(1),F(0))]+[(F(1),-x,a) for x,a in zip(hh,roots)];actual=ledger(candidate);assert actual and actual['T']==score['T'] and actual['multiplicities']=={3:1};caps=sum(0 in t for t in arrangement(candidate)['triangles']);assert caps==59
        rec.update(passed=True,exact_ledger=actual);dst=out/f'Q{"_".join(map(str,Q))}-T{actual["T"]}.json';dst.write_text(json.dumps(dict(rec,source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_attribution='Point1190 and original affine type: Rohith; uniform refit and the present exact concurrent surgery are this research branch',roots=list(map(str,roots)),reciprocal_slopes=list(map(str,hh)),lines_frac=[[str(v) for v in l] for l in candidate],status_note='Exact rational concurrent point with strict59 axis caps; actual tangent-parametric certificate and nonsimple BBL transfer are unproved'),indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)));print(json.dumps(dict(event='candidate',**rec)),flush=True)
    report=dict(screened=len(scores),histogram=dict(hist),LPs=len(records),records=records,wins=wins,seconds=time.time()-start,scope='Only reachable empty-triangle collapses with all strict axis-cap apices untouched; no concurrent infinite family asserted')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(screened=len(scores),histogram=dict(hist),LPs=len(records),wins=len(wins),seconds=report['seconds'])),flush=True)
