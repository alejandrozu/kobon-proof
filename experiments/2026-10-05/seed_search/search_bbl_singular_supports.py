"""Exact support-line screen on a simple BBL backbone.

Candidate supports pass through two actual ordinary vertices. A fast exact
insertion counter follows the split consecutive edges; retained best points
are rechecked by the independent full arrangement implementation.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,itertools as it,time,argparse,math
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement,primitive,intersection
from check_global_token_hypotheses import ledger
from test_backbone_corridor_doubling import pencil

def support(p,q):return primitive((p[1]*q[2]-p[2]*q[1],p[2]*q[0]-p[0]*q[2],p[1]*q[0]-p[0]*q[1]))
def value(L,p):return L[0]*p[0]+L[1]*p[1]-L[2]*p[2]

class InsertionCounter:
    def __init__(self,lines):
        self.ar=arrangement(lines);self.lines=self.ar['lines'];self.pos=[{p:j for j,p in enumerate(row)} for row in self.ar['rows']];self.coordinates=[0 if l[1] else 1 for l in self.lines];self.vertices=list(self.ar['points']);self.pair={tuple(sorted(s)):p for p,s in self.ar['points'].items()};assert all(len(s)==2 for s in self.ar['points'].values())
    def count(self,C):
        if any(C[0]*b-C[1]*a==0 for a,b,c in self.lines):return None
        ps={};crossings=[]
        for i,l in enumerate(self.lines):
            p=intersection(C,l);crossings.append(p);ps.setdefault(p,set()).add(i)
        ax=0 if C[1] else 1;ordered=sorted(ps,key=lambda p:F(p[ax],p[2]));lost=0
        for tri in self.ar['triangle_vertices']:
            vs=[value(C,p) for p in tri]
            if min(vs)<0<max(vs):lost+=1
        def adjacent(i,p,r):
            row=self.ar['rows'][i];rank=self.pos[i][r];axis=self.coordinates[i];pr=p[axis]*r[2]-r[axis]*p[2]
            if not pr:return False
            if pr>0:return rank+1==len(row) or p[axis]*row[rank+1][2]<=row[rank+1][axis]*p[2]
            return rank==0 or p[axis]*row[rank-1][2]>=row[rank-1][axis]*p[2]
        fresh=[]
        for p,q in zip(ordered,ordered[1:]):
            for i,j in it.product(ps[p],ps[q]):
                if i==j:continue
                r=self.pair[tuple(sorted((i,j)))]
                if r in [p,q]:continue
                if adjacent(i,p,r) and adjacent(j,q,r):fresh.append(tuple(sorted((i,j))))
        return dict(T=len(self.ar['triangles'])-lost+len(fresh),lost=lost,new=len(fresh),core_count=sum(len(s)>1 for s in ps.values()),core_supports=[sorted(s) for s in ps.values() if len(s)>1],new_triangle_old_pairs=fresh)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,default=12);ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--seed');ap.add_argument('--initial-q',type=int,default=6);ap.add_argument('--suffix',default='');ap.add_argument('--single-core',action='store_true');args=ap.parse_args();start=time.time()
    seed=ROOT/args.seed if args.seed else ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-bbl/seed-axis7-root-10.json';raw=json.loads(seed.read_text());old=[tuple(map(F,l)) for i,l in enumerate(raw['lines_frac']) if i!=raw['corridor_index']];q=args.initial_q;step=0
    epsilon=F(raw.get('epsilon',raw.get('eps','1/10000')))
    while q<args.q:
        step+=1;delta=epsilon/F(10**step);kappa=delta*epsilon**2/F(10**(20*(step-1)));old=list(map(primitive,old+pencil(q,delta,kappa)));q*=2
    assert q==args.q;counter=InsertionCounter(old);vertices=counter.vertices;out=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/bbl-singular-support-q{q}{args.suffix}';out.mkdir(parents=True,exist_ok=True);seen=set(counter.lines);best=0;wins=[];hist={};tested=0;targets=q*q//3+q//2
    def candidates():
        if not args.single_core:
            for a,b in it.combinations(range(len(vertices)),2):yield a,b,support(vertices[a],vertices[b])
            return
        for a,p in enumerate(vertices):
            critical={support(p,r) for r in vertices if r!=p}
            critical=sorted(critical,key=lambda L:(L[0]==0,F(L[1],L[0]) if L[0] else F(0)))
            for b,(L,M) in enumerate(zip(critical,critical[1:])):yield a,b,primitive(tuple(l+m for l,m in zip(L,M)))
            yield a,len(critical)-1,primitive(tuple(l-m for l,m in zip(critical[-1],critical[0])))
    for a,b,C in candidates():
        if time.time()-start>args.seconds:break
        if C in seen:continue
        seen.add(C);r=counter.count(C)
        if r is None:continue
        tested+=1;hist[r['T']]=hist.get(r['T'],0)+1
        if r['T']>=best:
            if r['T']>best:best=r['T'];print(json.dumps(dict(event='best',q=q,tested=tested,pair=[a,b],**r)),flush=True)
            if r['T']>=targets:
                lines=old+[C];actual=ledger(lines);assert actual['T']==r['T'];dst=out/f'pair{a}_{b}-T{r["T"]}-core{r["core_count"]}.json';dst.write_text(json.dumps(dict(q=q,seed=str(seed.relative_to(ROOT)),pair_vertex_ids=[a,b] if not args.single_core else [a],pair_vertices=[vertices[a],vertices[b]] if not args.single_core else [vertices[a]],insertion=r,exact_ledger=actual,corridor_index=len(old),lines_frac=[[str(v) for v in l] for l in lines],status_note='Exact singular support; true tangent and scalable support criterion pending'),indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)))
    report=dict(q=q,backbone_T=len(counter.ar['triangles']),target=targets,best=best,tested=tested,possible_pairs=math.comb(len(vertices),2),unique_candidates=len(seen)-len(old),histogram=hist,wins=wins,seconds=time.time()-start,completed=time.time()-start<args.seconds,scope='All one-vertex normal sectors' if args.single_core else 'All ordinary-vertex pair support lines if completed; fixed rational BBL point only')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
