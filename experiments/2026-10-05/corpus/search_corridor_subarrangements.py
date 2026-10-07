"""Exact subset containment screens retaining a chosen two-core corridor.

Deleting old lines only removes/merges old vertices, so old exact row order
reconstructs every subset without floating geometry. The small14→8 stage is
exhaustive under the explicit core-pair/axis choices. Larger stages use bounded
greedy/random deletion and do not prove noncontainment.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import itertools as it,json,random,time,sys,argparse
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive

class Subsets:
    def __init__(self,source):
        raw=json.loads(source.read_text());self.lines=[tuple(map(F,l)) for l in raw['lines_frac']] if 'lines_frac' in raw else [(F(a),F(b),-F(c)) for a,b,c in raw['lines']];self.n=len(self.lines);ar=arrangement(self.lines);self.T=len(ar['triangles']);self.points=list(ar['points']);self.supports=[set(ar['points'][p]) for p in self.points];self.masks=[sum(1<<i for i in s) for s in self.supports];ids={p:i for i,p in enumerate(self.points)};self.rows=[[ids[p] for p in r] for r in ar['rows']];self.cores=[s for s in self.supports if len(s)>=3];self.source=source
    def score(self,S,axis):
        mask=sum(1<<i for i in S);multip=[(m&mask).bit_count() for m in self.masks];rows=[[v for v in self.rows[i] if multip[v]>=2] for i in sorted(S)];edges={};adj={v:set() for r in rows for v in r}
        for line,row in zip(sorted(S),rows):
            for a,b in zip(row,row[1:]):e=tuple(sorted((a,b)));edges[e]=line;adj[a].add(b);adj[b].add(a)
        T=0;V=0
        for a in adj:
            for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
                if c not in adj[b]:continue
                labels={edges[tuple(sorted(e))] for e in [(a,b),(a,c),(b,c)]}
                if len(labels)<3:continue
                T+=1;V+=axis in labels
        return T,V,sum(r>=3 for r in multip)
    def replay(self,S,axis):
        S=sorted(S);ar=arrangement([self.lines[i] for i in S]);T=len(ar['triangles']);inc=sum(S.index(axis) in t for t in ar['triangles'])
        assert (T,inc,sum(len(s)>=3 for s in ar['points'].values()))==self.score(S,axis)
        return dict(T=T,axis_index=S.index(axis),axis_triangles=inc,lines_frac=[[str(v) for v in self.lines[i]] for i in S],triangles=[list(t) for t in ar['triangles']],retained_source_lines=S,source=str(self.source.relative_to(ROOT)))

def axes(A):
    result=[];seen=set()
    for c,d in it.combinations(A.cores,2):
        for axis in c&d:
            mandatory=c|d;key=(axis,tuple(sorted(mandatory)))
            if key not in seen:seen.add(key);result.append((axis,mandatory))
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--restarts',type=int,default=30);args=ap.parse_args();start=time.time();deadline=start+args.seconds;rng=random.Random(125026)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/corridor-subarrangements';out.mkdir(parents=True,exist_ok=True);reports=[];wins=[]
    for i in range(1,16):
        source=ROOT/f'research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-{i:02d}.json';A=Subsets(source);tested=0;best=0;found=[]
        for axis,mandatory in axes(A):
            for choice in it.combinations([j for j in range(A.n) if j not in mandatory],8-len(mandatory)):
                S=mandatory|set(choice);T,V,q=A.score(S,axis);tested+=1;best=max(best,T)
                if T>=15:
                    p=out/f'M{i:02d}-n8-T{T}-axis{axis}-subset{"_".join(map(str,sorted(S)))}.json';p.write_text(json.dumps(A.replay(S,axis),indent=2)+'\n');found.append(str(p.relative_to(ROOT)));wins.append(str(p.relative_to(ROOT)))
        r=dict(source=str(source.relative_to(ROOT)),target=8,tested=tested,best=best,found=found,exhaustive_scope='All8-subsets containing each chosen corridor axis and both selected triple cores');reports.append(r);print(json.dumps(dict(event='small',source=i,tested=tested,best=best,wins=len(found))),flush=True)
    for n,target,desired in [(26,14,54),(50,26,204)]:
        source=ROOT/f'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-{n:03d}.json';A=Subsets(source);best=0;found=[];tests=0;traces=[]
        for axis,mandatory in axes(A):
          for restart in range(args.restarts):
            if time.time()>deadline:break
            S=set(range(n));trace=[]
            while len(S)>target:
                proposals=[]
                for removed in S-mandatory:
                    score=A.score(S-{removed},axis);tests+=1;proposals.append((score,removed))
                optimum=max(x[0][0] for x in proposals);eligible=[p for p in proposals if p[0][0]>=optimum-(1 if restart%3==2 else 0)];score,removed=rng.choice(eligible);S.remove(removed);trace.append(dict(removed=removed,n=len(S),T=score[0],axis_triangles=score[1]))
            T,V,q=A.score(S,axis);traces.append(dict(restart=restart,T=T,axis_triangles=V,trace=trace));best=max(best,T)
            print(json.dumps(dict(event='greedy',source_n=n,target=target,restart=restart,T=T,best=best,tests=tests,seconds=time.time()-start)),flush=True)
            if T>=desired:
                p=out/f'n{n}-to{target}-T{T}-restart{restart}.json';p.write_text(json.dumps(A.replay(S,axis),indent=2)+'\n');found.append(str(p.relative_to(ROOT)));wins.append(str(p.relative_to(ROOT)));break
        reports.append(dict(source=str(source.relative_to(ROOT)),target=target,desired=desired,best=best,tested=tests,found=found,traces=traces,scope='Bounded greedy/random deletion, not exhaustive noncontainment'))
    (out/'report.json').write_text(json.dumps(dict(reports=reports,wins=wins,seconds=time.time()-start,trust='Exact subset row order and independent full-coordinate replays of retained winners; only smallstage explicitly exhaustive'),indent=2)+'\n')

if __name__=='__main__':main()
