"""Screen infinitesimal FP resolutions through a bipartite conflict graph.

At each old triple point, a generic resolution retains one alternating
sector class. An old triangle survives only if all of its triple corners
select their required class. Conflicts can be matched independently of the
additional straight-line realizability constraints on resolution signs.
This is a finite combinatorial experiment, not a Lean all-order theorem.
"""
from pathlib import Path
from collections import defaultdict,deque,Counter
import itertools as it,json
ROOT=Path(__file__).resolve().parents[3]


def parity(xs):return -1 if sum(xs[i]>xs[j] for i,j in it.combinations(range(3),2))%2 else 1
def sine_sign(n,total):return 0 if total%n==0 else 1 if (total//n)%2==0 else -1
def evaluation_sign(n,i,j,r):
    if r in [i,j]:return 0
    return (1 if r>j else -1)*(1 if r>i else -1)*sine_sign(n,i+j+r)


def maximum_matching(adjacency,left):
    pu={u:None for u in left};pv={v:None for vs in adjacency.values() for v in vs};matching=0
    while True:
        distance={u:0 for u in left if pu[u] is None};queue=deque(distance);found=False
        while queue:
            u=queue.popleft()
            for v in adjacency[u]:
                w=pv[v]
                if w is None:found=True
                elif w not in distance:distance[w]=distance[u]+1;queue.append(w)
        if not found:break
        def augment(u):
            for v in adjacency[u]:
                w=pv[v]
                if w is None or (distance.get(w)==distance[u]+1 and augment(w)):
                    pu[u]=v;pv[v]=u;return True
            distance[u]=-1;return False
        for u in left:
            if pu[u] is None and augment(u):matching+=1
    return matching


def audit(row):
    n=row["n"];ts=list(map(tuple,row["canonical_triangle_list"]));by_core=defaultdict(lambda:defaultdict(list));colours={};free=[]
    for t_id,(i,j,k) in enumerate(ts):
        choices=[]
        for a,b,other in [(i,j,k),(i,k,j),(j,k,i)]:
            r=(-a-b)%n
            if r in [a,b]:continue
            core=tuple(sorted((a,b,r)))
            desired=evaluation_sign(n,a,other,r)
            if not desired:desired=evaluation_sign(n,b,other,r)
            assert desired
            detsign=1 if a>b else -1
            preference=-desired*detsign*parity((a,b,r))
            # Normalize by the common infinitesimal cos(3theta) resolution.
            phase=1 if (sum(core)//n)%2==0 else -1
            bit=preference*phase;choices.append(bit);by_core[core][bit].append(t_id)
        if not choices:free.append(t_id)
        else:
            assert len(set(choices))==1,(n,(i,j,k),choices)
            colours[t_id]=choices[0]
    left=[t for t,c in colours.items() if c==1];right=[t for t,c in colours.items() if c==-1]
    adjacency={t:set() for t in left}
    for classes in by_core.values():
        for a in classes[1]:adjacency[a].update(classes[-1])
    matching=maximum_matching(adjacency,left)
    independent=len(ts)-matching
    upper=row["triple_points"]+independent
    G=n*(n-3)//3+1+n%2
    return dict(n=n,old_triangles=len(ts),cores=row["triple_points"],left=len(left),right=len(right),free=len(free),
                maximum_matching=matching,maximum_surviving_old_triangles=independent,
                resolution_upper_screen=upper,repository_G=G,excess=upper-G,
                graph_edges=sum(map(len,adjacency.values())))


if __name__=="__main__":
    rows=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/fp-shared-rule.json").read_text())["rows"]
    result=[audit(r) for r in rows if r["n"] in list(range(8,61))+[99,120,195]]
    out=ROOT/"research/openmath-seven-hour-2026-10-05/seed_search/fp-resolution-matching.json"
    out.write_text(json.dumps(dict(passed=True,scope="Finite resolution-sign conflict graph; no geometric completeness/all-n Lean theorem yet",results=result),indent=2)+"\n")
    print(json.dumps(dict(cases=len(result),excess_cases=[r for r in result if r["excess"]>0],selected=[r for r in result if r["n"] in [8,11,18,31,60,195]])))
