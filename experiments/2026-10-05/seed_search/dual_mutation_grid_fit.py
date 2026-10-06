"""Use LP dual support to screen actual single-face mutations of a strong seed.

This is a bounded proposal generator, not a theorem of local optimality. An
actual triangle/parallel face mutation changes one chirotope sign; the resulting
graph is scored before fitting. No numerical candidate is counted as a result
without a separate exact geometry and whole-parameter certificate.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import itertools as it,json,sys,time,math,argparse,warnings,hashlib
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/seed_search'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-02'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from word_grid_fit import tensor,chart_signs
from facet_walk61 import np,matrix,sparse,linprog,mutation_score,parallel_score,solve
from fit_optimal31_projective_charts import dot,cross
from exact_geometry import arrangement,primitive

def graph(ar,n):
    pairs=list(it.combinations(range(n),2));pair_ids={p:i for i,p in enumerate(pairs)}
    point_ids={point:pair_ids[tuple(sorted(labels))] for point,labels in ar['points'].items()};assert len(point_ids)==len(pairs)
    rows=[[point_ids[p] for p in row] for row in ar['rows']];adj=[set() for p in pairs];edge_lines={}
    for i,row in enumerate(rows):
        for a,b in zip(row,row[1:]):adj[a].add(b);adj[b].add(a);edge_lines[tuple(sorted((a,b)))]=i
    triangles=[(tuple(labels),tuple(sorted(point_ids[p] for p in points))) for labels,points in zip(ar['triangles'],ar['triangle_vertices'])]
    return dict(n=n,pairs=pairs,pair_ids=pair_ids,rows=rows,adj=adj,edge_lines=edge_lines,triangles=triangles)

def triangle_labels(g,vertices):
    p,q,r=[set(g['pairs'][v]) for v in vertices]
    return tuple(sorted([next(iter(p&q)),next(iter(p&r)),next(iter(q&r))]))

def dual(A,sg):
    M=sparse.hstack([-sparse.diags(sg.astype(float))@A,np.ones((A.shape[0],1))],format='csr');o=np.zeros(A.shape[1]+1);o[-1]=-1
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        r=linprog(o,A_ub=M,b_ub=np.zeros(A.shape[0]),bounds=[(-1,1)]*A.shape[1]+[(0,1)],method='highs',options={'threads':1,'time_limit':10})
    return r

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=53);ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--min-count',type=int,default=898)
    args=ap.parse_args();start=time.time();deadline=start+args.seconds;n=args.n;q=n-1
    source=ROOT/f'work/openmath-rohith/kobon-triangles/submissions/n{n}/solution.json';raw=json.loads(source.read_text());lines=[primitive((F(a),F(b),-F(c))) for a,b,c in raw['lines']]
    ar=arrangement(lines);g=graph(ar,n);T=len(g['triangles']);inc=[sum(i in t for t in ar['triangles']) for i in range(n)];axes=[i for i,v in enumerate(inc) if v==n-2]
    hs=[(a,b,-c) for a,b,c in lines]+[(F(0),F(0),F(1))];entries=[]
    for i,j,k in it.combinations(range(n+1),3):
        v=dot(hs[i],cross(hs[j],hs[k]));assert v;entries.append(((i,j,k),1 if v>0 else -1))
    chi=tensor(n+1,entries);roots=np.array(sorted([math.tan(k*math.pi/q) for k in range(-q//2+1,q//2) if k]+[0.,0.]));A,_,_=matrix(roots)
    out=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/dual-mutation{n}';out.mkdir(parents=True,exist_ok=True)
    moves={}
    for labels,vertices in g['triangles']:
        s=mutation_score(g,labels)
        if s and T+s['delta']>=args.min_count:moves[tuple(labels)]=s
    for i,j in it.combinations(range(n),2):
        s=parallel_score(g,i,j)
        if s and T+s['delta']>=args.min_count:moves[(i,j,n)]=s
    for labels,s in moves.items():
        s['incidence_delta']=dict(Counter(i for v in s['created'] for i in triangle_labels(g,v))-Counter(i for v in s['lost'] for i in triangle_labels(g,v)))
        # Counter subtraction omits negative entries; retain them explicitly.
        lost=Counter(i for v in s['lost'] for i in triangle_labels(g,v));created=Counter(i for v in s['created'] for i in triangle_labels(g,v))
        s['incidence_delta']={i:created[i]-lost[i] for i in set(lost)|set(created)}
    reports=[];wins=[];tested=0
    for axis in axes:
        if time.time()>deadline:break
        ids,sg=chart_signs(chi,axis,n);pairs=list(it.combinations(ids,2));triples=list(it.combinations(ids,3));labels=[tuple(sorted(p+(n,))) for p in pairs]+[tuple(sorted(p)) for p in triples]
        initial=dual(A,sg);support=[]
        if initial.success:support=[r for r,v in enumerate(initial.ineqlin.marginals) if abs(v)>1e-8]
        record=dict(axis=axis,initial_margin=float(initial.x[-1]) if initial.success else None,dual_support=[dict(row=r,labels=labels[r],weight=float(-initial.ineqlin.marginals[r])) for r in support],fits=[])
        for row in support:
            labels_=labels[row];s=moves.get(labels_)
            if s is None or axis in labels_ or s['incidence_delta'].get(axis,0)!=0:continue
            mutated=sg.copy();mutated[row]*=-1;x,status=solve(A,mutated,10);tested+=1
            fit=dict(labels=labels_,T=T+s['delta'],passed=x is not None,status=status);record['fits'].append(fit)
            if x is not None:
                if x[q//2-1]<x[q//2]:x=-x
                vv=[F(float(v+2)).limit_denominator(10**12) for v in x];eps=F(1,10**8);rr=[F(float(v)).limit_denominator(10**15) for v in roots];rr[q//2-1]=-eps;rr[q//2]=eps
                candidate=[(F(0),F(1),F(0))]+[(F(1),-h,r) for h,r in zip(vv,rr)];actual=arrangement(candidate);count=len(actual['triangles']);caps=sum(0 in t for t in actual['triangles'])
                proposal=dict(n=n,triangle_screen=count,caps_screen=caps,reciprocal_slopes=list(map(str,vv)),source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_commit='f462d8e18aea2a458376c523c9b6c2980237071f',source_axis=axis,source_labels=ids,mutated_labels=labels_,epsilon=str(eps),lines_frac=[[str(v) for v in l] for l in candidate],status='Exact rational midpoint following floating grid LP; actual tangent and whole-interval verification pending')
                path=out/f'T{count}-axis{axis:03d}-row{row:05d}-proposal.json';path.write_text(json.dumps(proposal,indent=2)+'\n');fit['proposal']=str(path.relative_to(ROOT));wins.append(fit)
                print(json.dumps(dict(event='proposal',axis=axis,T=count,caps=caps,margin=status,mutated_labels=labels_)),flush=True)
        reports.append(record);print(json.dumps(dict(event='axis',axis=axis,support=len(support),fits=len(record['fits']),tested=tested,wins=len(wins),seconds=time.time()-start)),flush=True)
        (out/'report.json').write_text(json.dumps(dict(n=n,T=T,axes=axes,eligible_moves=len(moves),mutation_delta_counts=dict(Counter(s['delta'] for s in moves.values())),tested=tested,wins=wins,records=reports,seconds=time.time()-start,scope='Bounded dual-guided actual single-face mutations with a retained saturated axis; no local/global optimality theorem'),indent=2)+'\n')
    print(json.dumps(dict(eligible_moves=len(moves),tested=tested,wins=len(wins),seconds=time.time()-start)),flush=True)

if __name__=='__main__':main()
