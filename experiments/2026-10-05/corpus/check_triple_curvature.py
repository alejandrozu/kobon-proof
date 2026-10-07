"""Exact bounded screen of two triple-only core-graph resource candidates.

No global theorem is concluded. Full rational lines are saved for any failure.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,time,random,itertools as it
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(Path(__file__).resolve().parent))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from check_global_token_hypotheses import ledger
from exact_geometry import arrangement,primitive

def components(lines):
    ar=arrangement(lines);cores={p for p,l in ar['points'].items() if len(l)==3};use={}
    for tri in ar['triangle_vertices']:
        for e in it.combinations(tri,2):
            key=frozenset(e);use[key]=use.get(key,0)+1
    adj={p:set() for p in cores}
    for e,u in use.items():
        if u==2 and e<=cores:
            a,b=tuple(e);adj[a].add(b);adj[b].add(a)
    seen=set();cc=0
    for v in adj:
        if v in seen:continue
        cc+=1;stack=[v]
        while stack:
            z=stack.pop()
            if z in seen:continue
            seen.add(z);stack.extend(adj[z]-seen)
    return dict(core_graph_components=cc,core_graph_isolates=sum(not a for a in adj.values()))

def main():
    start=time.time();base=ROOT/'research/openmath-seven-hour-2026-10-05/corpus';old=json.loads((base/'triple-ordinary-shared-sanity.json').read_text());records=[];bad=[];skipped=0
    def record(r,source,lines=None):
        r=dict(r,source=source,curvature_slack=6*r['q']+6-3*r['D1']-2*r['D2']-r['Rc'],strong_slack=6*r['q']-3*r['D1']-2*r['D2'],no_boundary_slack=r['C']-2*r['D1'])
        assert r['curvature_slack']==r['C']+6-2*r['D1']
        assert r['strong_slack']==r['C']+r['Rc']-2*r['D1']
        records.append(r)
        if min(r['curvature_slack'],r['strong_slack'])<0:
            if lines is None:
                raw=json.loads((ROOT/source).read_text());lines=raw.get('lines_frac') or [(a,b,-c) for a,b,c in raw['lines']]
            witness=dict(r,lines_frac=[[str(v) for v in l] for l in lines],**components(lines));bad.append(witness)
            print(json.dumps(dict(event='counterexample',**witness)),flush=True)
    for r in old['tested']:record(r,r['source'])
    rng=random.Random(260605)
    for trial in range(320):
        q=rng.randint(1,9);slopes=rng.sample(range(-200,201),3*q);lines=[]
        centers=rng.sample([(x,y) for x in range(-6,7) for y in range(-6,7)],q)
        for j,(x,y) in enumerate(centers):
            for m in slopes[3*j:3*j+3]:lines.append(primitive((m,-1,m*x-y)))
        r=ledger(lines)
        if r is None or any(int(m)>3 for m in r['multiplicities']):skipped+=1;continue
        r.update(components(lines));record(r,f'Exact3-pencil mixture, seed260605 trial{trial}',lines)
        if len(bad)>10:break
    # Purposeful disconnected full-triple stars: each copy is the line
    # arrangement of the six edges of a planar K4, transformed rationally.
    for copies in range(1,7):
        points=[];edges=[]
        for j in range(copies):
            t=F(j+1,101);dx=100000*j;dy=1234*j+1000*j*j
            shape=[(0,0),(0,1),(-1,-1),(1,0)]
            points.extend((F(x)-t*y+dx,t*x+F(y)+dy) for x,y in shape)
            edges.extend((4*j+a,4*j+b) for a,b in it.combinations(range(4),2))
        lines=[]
        for i,j in edges:
            x,y=points[i];u,v=points[j];a=v-y;b=x-u;lines.append(primitive((a,b,a*x+b*y)))
        r=ledger(lines)
        if r is None or any(int(m)>3 for m in r['multiplicities']):skipped+=1;continue
        r.update(components(lines));record(r,f'{copies} rationally separated K4 full-triple stars',lines)
    # Cubic core graphs include shared center-to-center candidates. The cycle
    # plus opposite matching is 3-regular, unlike independent pencil mixtures.
    for trial in range(240):
        q=2*rng.randint(2,10);points=rng.sample([(rng.randint(-10000,10000),rng.randint(-10000,10000)) for _ in range(3*q)],q)
        edges={tuple(sorted((i,(i+1)%q))) for i in range(q)}|{(i,i+q//2) for i in range(q//2)};lines=[]
        for i,j in sorted(edges):
            x,y=points[i];u,v=points[j];a=v-y;b=x-u;lines.append(primitive((a,b,a*x+b*y)))
        r=ledger(lines)
        if r is None or any(int(m)>3 for m in r['multiplicities']):skipped+=1;continue
        r.update(components(lines));record(r,f'Exact cubic center graph, seed260605 trial{trial}',lines)
        if len(bad)>10:break
    worst=min(records,key=lambda r:r['curvature_slack']);worst_strong=min(records,key=lambda r:r['strong_slack'])
    result=dict(scope='Pairwise nonparallel actual arrangements with maximum multiplicity3; exact finite screen only',candidates=['3D1+2D2+Rc<=6q+6','3D1+2D2<=6q'],tested=len(records),records=records,violations=bad,passed=not bad,worst_curvature=worst,worst_strong=worst_strong,worst_no_boundary=min(records,key=lambda r:r['no_boundary_slack']),random_skipped=skipped,seconds=time.time()-start)
    (base/'triple-curvature-sanity.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(tested=len(records),violations=len(bad),worst_curvature=worst,worst_strong=worst_strong,skipped=skipped,seconds=time.time()-start)),flush=True)

if __name__=='__main__':main()
