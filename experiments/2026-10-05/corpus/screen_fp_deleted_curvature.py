"""Exact incidence/row-order screens after deleting phase-zero FP lines.

The pair determinant and triple-concurrence identities are the same as the
existing FP audit. Every retained vertex has its original canonical support,
but its actual multiplicity is recomputed from the retained line set. Line-row
order uses exact sine-index signs; no coordinates or floating sorting are used.
"""
from pathlib import Path
from functools import cmp_to_key
from collections import Counter
import itertools as it,json,time,random,argparse
ROOT=Path(__file__).resolve().parents[3]

def vertex(n,i,j):
    k=(-i-j)%n
    return tuple(sorted({i,j,k})) if k not in [i,j] else tuple(sorted((i,j)))

class Arrangement:
    def __init__(self,n):
        self.n=n;self.vertices=sorted({vertex(n,i,j) for i,j in it.combinations(range(n),2)})
        self.masks=[sum(1<<i for i in v) for v in self.vertices];self.ids={p:i for i,p in enumerate(self.vertices)};self.rows=[]
        for i in range(n):
            def compare(p,q):
                if p==q:return 0
                j=min(x for x in p if x!=i);k=min(x for x in q if x!=i)
                assert (i+j+k)%n!=0
                sine=1 if ((i+j+k)//n)%2==0 else -1
                return (1 if k>j else -1)*sine
            row=sorted((p for p in self.vertices if i in p),key=cmp_to_key(compare))
            assert all(compare(p,q)<0 for p,q in it.combinations(row,2))
            self.rows.append([self.ids[p] for p in row])

    def ledger(self,S,detail=False):
        S=set(S);mask=sum(1<<i for i in S);n=len(S);mult=[(v&mask).bit_count() for v in self.masks];cores={i for i,r in enumerate(mult) if r==3}
        rows=[[v for v in self.rows[i] if mult[v]>=2] for i in sorted(S)];edges={};adj={v:set() for row in rows for v in row};Rc=0
        for i,row in zip(sorted(S),rows):
            Rc+=(row[0] in cores)+(row[-1] in cores)
            for a,b in zip(row,row[1:]):
                e=tuple(sorted((a,b)));assert e not in edges;edges[e]=i;adj[a].add(b);adj[b].add(a)
        triangles=[];use=Counter();at=Counter()
        for a in adj:
            for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
                if c not in adj[b]:continue
                es=[tuple(sorted(e)) for e in [(a,b),(a,c),(b,c)]];labels=[edges[e] for e in es]
                assert len(set(labels))==3
                triangles.append((a,b,c));use.update(es);at.update([a,b,c])
        assert max(use.values(),default=0)<=2
        D1=sum(u==2 and sum(v in cores for v in e)==1 for e,u in use.items());D2=sum(u==2 and all(v in cores for v in e) for e,u in use.items())
        assert all(u!=2 or any(v in cores for v in e) for e,u in use.items())
        C=sum(sum(v in cores for v in e) for e in edges if use[e]<=1);U=len(edges)-len(use);q=len(cores);T=len(triangles);delta=n*(n-2)-3*T
        assert delta==3*q+U-D1-D2
        assert 2*delta==2*U-D1+C+Rc
        result=dict(parent_order=self.n,n=n,retained=sorted(S),T=T,q=q,D1=D1,D2=D2,C=C,Rc=Rc,U=U,delta=delta,curvature_slack=C+6-2*D1,strong_slack=C+Rc-2*D1,no_boundary_slack=C-2*D1,ordinary_sector_profile=dict(Counter(at[v] for v in adj if v not in cores)),core_sector_profile=dict(Counter(at[v] for v in cores)))
        if detail:
            result.update(actual_vertex_supports={str(v):[i for i in self.vertices[v] if i in S] for v in adj},original_vertex_supports={str(v):self.vertices[v] for v in adj},ordered_rows=rows,triangle_vertices=triangles,edge_use=[dict(vertices=e,line=i,use=use[e]) for e,i in edges.items()])
        return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--random',type=int,default=80);args=ap.parse_args()
    start=time.time();deadline=start+args.seconds;rng=random.Random(60426);records=[];worst=None;worst_strong=None;worst_curv=None;violations=[];tests=0;rich_cases=0;max_ordinary=0;worst_rich=None;worst_first=None
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/fp-deletion-curvature';out.mkdir(parents=True,exist_ok=True)
    def test(A,S,source):
        nonlocal tests,worst,worst_strong,worst_curv,rich_cases,max_ordinary,worst_rich,worst_first
        r=A.ledger(S);r['source']=source;tests+=1
        r['first_token_gap']=r['n']-2*r['U']-r['D1']-r['Rc']
        if r['n']%2==0 and (worst_first is None or r['first_token_gap']>worst_first['first_token_gap']):worst_first=r
        fanmax=max(r['ordinary_sector_profile'],default=0);max_ordinary=max(max_ordinary,fanmax)
        if fanmax>=3:
            rich_cases+=1
            if worst_rich is None or r['no_boundary_slack']<worst_rich['no_boundary_slack']:worst_rich=r
        if worst is None or r['no_boundary_slack']<worst['no_boundary_slack']:
            worst=r;print(json.dumps(dict(event='minimum',**r)),flush=True)
            (out/'worst-no-boundary.json').write_text(json.dumps(A.ledger(S,True),indent=2)+'\n')
        if worst_strong is None or r['strong_slack']<worst_strong['strong_slack']:worst_strong=r
        if worst_curv is None or r['curvature_slack']<worst_curv['curvature_slack']:worst_curv=r
        if min(r['strong_slack'],r['curvature_slack'])<0:
            full=A.ledger(S,True);full['source']=source;violations.append(full)
            p=out/f'counterexample-parent{A.n}-order{len(S)}-{tests}.json';p.write_text(json.dumps(full,indent=2)+'\n')
            print(json.dumps(dict(event='counterexample',path=str(p.relative_to(ROOT)),**r)),flush=True)
        return r
    for n in [18,24,30,36,42,48,54,60]:
        if time.time()>deadline or violations:break
        A=Arrangement(n);test(A,range(n),'Full original FP')
        for i in range(n):
            test(A,[j for j in range(n) if j!=i],f'Single deletion{i}')
            if violations or time.time()>deadline:break
        for trial in range(args.random):
            if violations or time.time()>deadline:break
            size=rng.randint(max(6,n//2),n-2);test(A,rng.sample(range(n),size),f'Random subset seed60426 trial{trial}')
        records.append(dict(parent=n,tests_so_far=tests,seconds=time.time()-start))
    result=dict(passed=not violations,tests=tests,parents=records,worst_no_boundary=worst,worst_strong=worst_strong,worst_curvature=worst_curv,worst_even_first_token=worst_first,rich_ordinary_cases=rich_cases,max_ordinary_sectors=max_ordinary,worst_rich_ordinary=worst_rich,violations=violations,seconds=time.time()-start,trust='Exact FP incidence and sine-index row order, no floating geometry; no Lean general theorem or global numerical upper bound')
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['passed','tests','worst_no_boundary','worst_strong','worst_curvature','rich_ordinary_cases','max_ordinary_sectors','worst_rich_ordinary','seconds']}),flush=True)

if __name__=='__main__':main()
