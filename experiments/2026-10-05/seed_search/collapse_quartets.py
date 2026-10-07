"""Targeted exact topology / LP search for an interior quadruple core.

Only quartet blocks with all three crossings contiguous on each participating
line can collapse while retaining every other chirotope sign. The merged graph
is scored first; positive LP outputs are reconstructed with exact rational
concurrency and recounted. No all-order or new-record claim comes from screening.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import sys,itertools as it,json,time,argparse,warnings
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
import numpy as np
from scipy.optimize import linprog
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=18);ap.add_argument('--min-count',type=int,default=90);args=ap.parse_args();start=time.time();n=args.n
    source=ROOT/f'research/finite-table/classical-{n:03d}.json';raw=json.loads(source.read_text());lines=[tuple(map(F,l)) for l in raw['lines_frac']];lines=[tuple(v/max(abs(a),abs(b)) for v in [a,b,c]) for a,b,c in lines]
    ar=arrangement(lines);T=len(ar['triangles']);assert len(ar['points'])==n*(n-1)//2
    points=list(ar['points']);point_id={p:i for i,p in enumerate(points)};pair_id={tuple(sorted(s)):point_id[p] for p,s in ar['points'].items()};rows=[[point_id[p] for p in r] for r in ar['rows']];positions=[{v:i for i,v in enumerate(r)} for r in rows]
    triple_labels=list(it.combinations(range(n),3));normals=np.array([[float(a),float(b)] for a,b,c in lines]);weights=[];signs=[]
    for i,j,k in triple_labels:
        a,b,c=lines[i];d,e,f=lines[j];g,h,z=lines[k]
        w=[-(d*h-e*g),a*h-b*g,-(a*e-b*d)];value=w[0]*c+w[1]*f+w[2]*z;assert value
        row=np.zeros(n);row[[i,j,k]]=list(map(float,w));weights.append(row);signs.append(1 if value>0 else -1)
    weights=np.array(weights);signs=np.array(signs);out=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/collapse-quartet{n}';out.mkdir(parents=True,exist_ok=True);records=[];wins=[];contiguous=0
    for Q in it.combinations(range(n),4):
        cluster={pair_id[p] for p in it.combinations(Q,2)}
        if any(max(vs)-min(vs)!=2 for i in Q for vs in [[positions[i][pair_id[tuple(sorted((i,j)))]] for j in Q if j!=i]]):continue
        contiguous+=1;hub=len(points);newrows=[[hub if v in cluster else v for v in r] for r in rows];newrows=[[v for j,v in enumerate(r) if not j or v!=r[j-1]] for r in newrows];edge_lines={};adj={v:set() for r in newrows for v in r}
        for i,r in enumerate(newrows):
            for a,b in zip(r,r[1:]):edge=tuple(sorted((a,b)));assert edge not in edge_lines;edge_lines[edge]=i;adj[a].add(b);adj[b].add(a)
        triangles=[];use=Counter()
        for a in adj:
            for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
                if c not in adj[b]:continue
                es=[tuple(sorted(e)) for e in [(a,b),(a,c),(b,c)]]
                if len({edge_lines[e] for e in es})<3:continue
                triangles.append((a,b,c));use.update(es)
        score=len(triangles);D1=sum(v==2 and hub in e for e,v in use.items());U=len(edge_lines)-len(use);Rc=sum(r[0]==hub or r[-1]==hub for r in newrows);C=sum(hub in e for e in edge_lines if use[e]<=1);gap=n-2*U-D1-Rc
        record=dict(quartet=Q,screen_T=score,D1=D1,U=U,C=C,Rc=Rc,first_token_gap=gap,passed=False);records.append(record)
        if score<args.min_count and gap<=2:continue
        outside=[i for i in range(n) if i not in Q];d=len(outside)+2;M=np.zeros((n,d))
        for pos,i in enumerate(outside):M[i,pos]=1
        for i in Q:M[i,-2:]=normals[i]
        kept=[r for r,t in enumerate(triple_labels) if not set(t)<=set(Q)];A=weights[kept]@M;sg=signs[kept];scale=np.max(np.abs(A),axis=1);assert all(scale>1e-12);A/=scale[:,None]
        matrix=np.column_stack([-sg[:,None]*A,np.ones(len(A))]);objective=np.zeros(d+1);objective[-1]=-1
        with warnings.catch_warnings():
            warnings.simplefilter('ignore');r=linprog(objective,A_ub=matrix,b_ub=np.zeros(len(A)),bounds=[(-1,1)]*d+[(0,1)],method='highs',options={'threads':1,'time_limit':10})
        margin=float(r.x[-1]) if r.success else None;record.update(lp_status=int(r.status),margin=margin)
        if not margin or margin<1e-9:continue
        values=[F(float(v)).limit_denominator(10**12) for v in r.x[:-1]];center=values[-2:];newc={i:values[j] for j,i in enumerate(outside)}
        for i in Q:newc[i]=lines[i][0]*center[0]+lines[i][1]*center[1]
        candidate=[primitive((a,b,newc[i])) for i,(a,b,c) in enumerate(lines)];actual=ledger(candidate);assert actual
        record.update(passed=True,exact_ledger=actual);proposal=dict(record,center=list(map(str,center)),source=str(source.relative_to(ROOT)),lines_frac=[[str(v) for v in l] for l in candidate],status='Exact rational one-quadruple point arrangement; external replay only, no new global theorem')
        path=out/f'T{actual["T"]}-Q{"_".join(map(str,Q))}.json';path.write_text(json.dumps(proposal,indent=2)+'\n');wins.append(str(path.relative_to(ROOT)))
        print(json.dumps(dict(event='candidate',Q=Q,margin=margin,ledger=actual)),flush=True)
    report=dict(n=n,source_T=T,contiguous_blocks=contiguous,tested=len(records),wins=wins,records=records,seconds=time.time()-start,scope='A single source affine type, quartet collapse preserving other orientation signs; no exhaustive geometry ceiling')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(source_T=T,contiguous=contiguous,wins=len(wins),max_T=max((r['screen_T'] for r in records),default=0),max_gap=max((r['first_token_gap'] for r in records),default=0),seconds=time.time()-start)),flush=True)

if __name__=='__main__':main()
