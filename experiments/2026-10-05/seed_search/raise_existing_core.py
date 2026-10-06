"""Collapse one added line into an existing triple while preserving other signs.

The topology is exactly scored first; rational LP outputs are recounted with
unchanged exact geometry. Higher-multiplicity token tests are distinct from
the triple-only conjectures. This is a bounded screen, not an upper theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import sys,itertools as it,json,time,argparse,warnings,hashlib
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'));sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
import numpy as np
from scipy.optimize import linprog
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger

def exact_nullspace_round(E,approx):
    d=len(approx);matrix=[r.copy() for r in E];pivots=[];row=0
    for col in range(d):
        pivot=next((j for j in range(row,len(matrix)) if matrix[j][col]),None)
        if pivot is None:continue
        matrix[row],matrix[pivot]=matrix[pivot],matrix[row];scale=matrix[row][col];matrix[row]=[x/scale for x in matrix[row]]
        for j in range(len(matrix)):
            if j==row:continue
            factor=matrix[j][col]
            if factor:matrix[j]=[a-factor*b for a,b in zip(matrix[j],matrix[row])]
        pivots.append(col);row+=1
    values=[F(float(v)).limit_denominator(10**12) for v in approx];free=[i for i in range(d) if i not in pivots]
    for j,col in enumerate(pivots):values[col]=-sum(matrix[j][i]*values[i] for i in free)
    assert all(sum(a*b for a,b in zip(r,values))==0 for r in E)
    return values

def run(source,out):
    raw=json.loads(source.read_text());lines=[tuple(map(F,l)) for l in raw['lines_frac']];n=len(lines);lines=[tuple(v/max(abs(a),abs(b)) for v in [a,b,c]) for a,b,c in lines]
    ar=arrangement(lines);T=len(ar['triangles']);points=list(ar['points']);supports=[set(ar['points'][p]) for p in points];point_id={p:i for i,p in enumerate(points)};rows=[[point_id[p] for p in r] for r in ar['rows']];positions=[{v:i for i,v in enumerate(r)} for r in rows]
    triple_labels=list(it.combinations(range(n),3));weights=[];weights_exact=[];signs=[];normals=np.array([[float(a),float(b)] for a,b,c in lines])
    for i,j,k in triple_labels:
        a,b,c=lines[i];d,e,f=lines[j];g,h,z=lines[k];w=[-(d*h-e*g),a*h-b*g,-(a*e-b*d)];value=w[0]*c+w[1]*f+w[2]*z
        row=np.zeros(n);row[[i,j,k]]=list(map(float,w));weights.append(row);weights_exact.append(w);signs.append((value>0)-(value<0))
    weights=np.array(weights);signs=np.array(signs);records=[];wins=[]
    candidates={tuple(sorted(s|{i})) for s in supports if len(s)==3 for i in range(n) if i not in s}
    for Q in sorted(candidates):
        Q=set(Q);cluster={v for v,s in enumerate(supports) if len(s&Q)>=2}
        if any(not supports[v]<=Q for v in cluster):continue
        if any(max(vs)-min(vs)!=len(vs)-1 for i in Q for vs in [[positions[i][v] for v in cluster if i in supports[v]]]):continue
        hub=len(points);newrows=[[hub if v in cluster else v for v in r] for r in rows];newrows=[[v for j,v in enumerate(r) if not j or v!=r[j-1]] for r in newrows];edge_lines={};adj={v:set() for r in newrows for v in r}
        cores={v for v,s in enumerate(supports) if len(s)>=3 and v not in cluster}|{hub}
        for i,r in enumerate(newrows):
            for a,b in zip(r,r[1:]):e=tuple(sorted((a,b)));assert e not in edge_lines;edge_lines[e]=i;adj[a].add(b);adj[b].add(a)
        triangles=[];use=Counter()
        for a in adj:
            for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
                if c not in adj[b]:continue
                es=[tuple(sorted(e)) for e in [(a,b),(a,c),(b,c)]]
                if len({edge_lines[e] for e in es})<3:continue
                triangles.append((a,b,c));use.update(es)
        score=len(triangles);D1=sum(u==2 and sum(v in cores for v in e)==1 for e,u in use.items());D2=sum(u==2 and all(v in cores for v in e) for e,u in use.items());U=len(edge_lines)-len(use);Rc=sum((r[0] in cores)+(r[-1] in cores) for r in newrows);C=sum(sum(v in cores for v in e) for e in edge_lines if use[e]<=1);gap=n-2*U-D1-Rc
        record=dict(quartet=sorted(Q),screen_T=score,D1=D1,D2=D2,U=U,C=C,Rc=Rc,first_token_gap=gap,passed=False);records.append(record)
        if gap<=2 and score<T:continue
        outside=[i for i in range(n) if i not in Q];d=len(outside)+2;M=np.zeros((n,d));MF=[[F(0) for _ in range(d)] for _ in range(n)]
        for pos,i in enumerate(outside):M[i,pos]=1;MF[i][pos]=F(1)
        for i in Q:M[i,-2:]=normals[i];MF[i][-2:]=lines[i][:2]
        strict=[r for r,t in enumerate(triple_labels) if not set(t)<=Q and signs[r]];equal=[r for r,t in enumerate(triple_labels) if not set(t)<=Q and not signs[r]]
        A=weights[strict]@M;sg=signs[strict];scale=np.max(np.abs(A),axis=1);assert all(scale>1e-12);A/=scale[:,None];matrix=np.column_stack([-sg[:,None]*A,np.ones(len(A))]);objective=np.zeros(d+1);objective[-1]=-1
        E=weights[equal]@M if equal else None;E=np.column_stack([E,np.zeros(len(E))]) if equal else None
        with warnings.catch_warnings():
            warnings.simplefilter('ignore');r=linprog(objective,A_ub=matrix,b_ub=np.zeros(len(A)),A_eq=E,b_eq=np.zeros(len(equal)) if equal else None,bounds=[(-1,1)]*d+[(0,1)],method='highs',options={'threads':1,'time_limit':10})
        margin=float(r.x[-1]) if r.success else None;record.update(lp_status=int(r.status),margin=margin)
        if not margin or margin<1e-9:continue
        EF=[[sum(weights_exact[tr][j]*MF[line][col] for j,line in enumerate(triple_labels[tr])) for col in range(d)] for tr in equal]
        values=exact_nullspace_round(EF,r.x[:-1]);center=values[-2:];newc={i:values[j] for j,i in enumerate(outside)}
        for i in Q:newc[i]=lines[i][0]*center[0]+lines[i][1]*center[1]
        candidate=[primitive((a,b,newc[i])) for i,(a,b,c) in enumerate(lines)];actual=ledger(candidate);assert actual
        assert actual['T']==score and n-2*actual['U']-actual['D1']-actual['Rc']==gap
        record.update(passed=True,exact_ledger=actual);proposal=dict(record,center=list(map(str,center)),source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_attribution='Andrea Maiorana (CC-BY4.0) or Parpalak--Utkin, as recorded in the retained source provenance; new exact core-collapse obstruction, no lower-bound record claimed',source_url='https://github.com/rufio72/kobon_triangles_k14/blob/e47c7cfd9661e54d29befb83118bf83d5f804028/sol11.json' if 'maiorana14' in source.parts else None,source_commit='e47c7cfd9661e54d29befb83118bf83d5f804028' if 'maiorana14' in source.parts else None,license='CC-BY4.0' if 'maiorana14' in source.parts else None,lines_frac=[[str(v) for v in l] for l in candidate],status='Exact rational quadruple arrangement with every remaining triple equality preserved by rational nullspace reconstruction')
        path=out/f's{source.stem}-T{actual["T"]}-Q{"_".join(map(str,sorted(Q)))}.json';path.write_text(json.dumps(proposal,indent=2)+'\n');wins.append(str(path.relative_to(ROOT)));print(json.dumps(dict(event='candidate',source=str(source.relative_to(ROOT)),Q=sorted(Q),margin=margin,actual=actual)),flush=True)
    return dict(source=str(source.relative_to(ROOT)),n=n,T=T,candidates=len(candidates),contiguous=len(records),records=records,wins=wins)

if __name__=='__main__':
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/raise-existing-cores';out.mkdir(parents=True,exist_ok=True);reports=[]
    sources=[ROOT/f'research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-{i:02d}.json' for i in range(1,16)]
    sources += [ROOT/f'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-{n:03d}.json' for n in [8,14,20,26,32,38,50]]
    for source in sources:
        if not source.exists():continue
        r=run(source,out);reports.append(r);print(json.dumps(dict(event='finish',source=str(source.relative_to(ROOT)),contiguous=r['contiguous'],wins=len(r['wins']),max_gap=max((x['first_token_gap'] for x in r['records']),default=0))),flush=True)
    (out/'report.json').write_text(json.dumps(dict(reports=reports,scope='Bounded exact topology and LP proposals, no numerical or upper-bound novelty inferred without exact ledger'),indent=2)+'\n')
