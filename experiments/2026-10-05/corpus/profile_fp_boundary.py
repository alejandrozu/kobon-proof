"""Exact endpoint/ray profiles of the concurrent FP obstruction family.

Vertex order on line i is certified combinatorially: for P_ij,P_ik,
sign(t_ij-t_ik)=sign(k-j)*sign(sin(pi*(i+j+k)/n)). This follows from
the existing exact determinant identity. No floating coordinates are used.
"""
from pathlib import Path
from functools import cmp_to_key
from collections import Counter,defaultdict
import itertools as it,json

ROOT=Path(__file__).resolve().parents[3]


def vertex(n,i,j):
    k=(-i-j)%n
    return tuple(sorted({i,j,k})) if k not in [i,j] else tuple(sorted((i,j)))


def profile(row):
    n=row["n"];triangles=row["canonical_triangle_list"]
    points={vertex(n,i,j) for i,j in it.combinations(range(n),2)}
    cores={p for p in points if len(p)==3}
    ordered=[]
    for i in range(n):
        def compare(p,q):
            if p==q:return 0
            j=min(x for x in p if x!=i);k=min(x for x in q if x!=i)
            assert (i+j+k)%n!=0
            sine_sign=1 if ((i+j+k)//n)%2==0 else -1
            return (1 if k>j else -1)*sine_sign
        vertices=sorted((p for p in points if i in p),key=cmp_to_key(compare))
        assert all(compare(p,q)<0 for p,q in it.combinations(vertices,2))
        ordered.append(vertices)
    all_edges={};uses=Counter();at_point=Counter()
    for i,vertices in enumerate(ordered):
        for p,q in zip(vertices,vertices[1:]):all_edges[tuple(sorted((p,q)))]=i
    for i,j,k in triangles:
        p,q,r=vertex(n,i,j),vertex(n,i,k),vertex(n,j,k)
        at_point.update([p,q,r])
        for edge in [tuple(sorted((p,q))),tuple(sorted((p,r))),tuple(sorted((q,r)))]:
            assert edge in all_edges
            uses[edge]+=1
    assert max(uses.values())==2
    ray_profiles=[];end_tokens=Counter();opposite_profiles=Counter();core_adj=defaultdict(set)
    for p in sorted(cores):
        counts=Counter();ordinary_axes=[];core_neighbors=[]
        for line in p:
            vertices=ordered[line];idx=vertices.index(p)
            for j in [idx-1,idx+1]:
                if not 0<=j<len(vertices):counts["unbounded"]+=1;continue
                q=vertices[j];edge=tuple(sorted((p,q)));use=uses[edge]
                if use==0:counts["unused"]+=1
                elif use==1:counts["single"]+=1
                elif len(q)==3:counts["core_shared"]+=1;core_adj[p].add(q);core_neighbors.append(q)
                else:counts["ordinary_shared"]+=1;ordinary_axes.append(line)
        assert sum(counts.values())==6
        ray_profiles.append(dict(core=p,triangle_sectors=at_point[p],ordinary_shared_axes=ordinary_axes,ordinary_caps_antipodal=len(ordinary_axes)==2 and ordinary_axes[0]==ordinary_axes[1],core_neighbors=core_neighbors,**counts))
        end_tokens.update(counts)
    for edge,use in uses.items():
        if use!=2 or sorted(map(len,edge))!=[2,3]:continue
        ordinary=next(p for p in edge if len(p)==2);core=next(p for p in edge if len(p)==3)
        line=all_edges[edge];vertices=ordered[line];idx=vertices.index(ordinary);idx_core=vertices.index(core)
        opposite=idx+1 if idx_core<idx else idx-1
        if not 0<=opposite<len(vertices):opposite_profiles["unbounded"]+=1
        else:opposite_profiles[f"bounded_use_{uses[tuple(sorted((ordinary,vertices[opposite])))]}"]+=1
    left=set(cores);components=[]
    while left:
        start=next(iter(left));component={start};todo=[start];left.remove(start)
        while todo:
            p=todo.pop()
            for q in core_adj[p]&left:left.remove(q);component.add(q);todo.append(q)
        components.append(len(component))
    d1=end_tokens["ordinary_shared"];d2=end_tokens["core_shared"]//2
    deficit=n*(n-2)-3*len(triangles)
    result=dict(n=n,q=len(cores),T=len(triangles),D1=d1,D2=d2,U=len(all_edges)-len(uses),
        deficit=deficit,core_graph_components=len(components),core_graph_component_sizes=sorted(components),
        core_graph_cyclomatic=d2-len(cores)+len(components),clean_lines=sum(not any(len(p)==3 for p in vertices) for vertices in ordered),
        core_ray_totals=dict(end_tokens),ordinary_opposite_ray_profiles=dict(opposite_profiles),
        ordinary_triangle_sector_profile=dict(Counter(at_point[p] for p in points if len(p)==2)),
        core_triangle_sector_profile=dict(Counter(at_point[p] for p in cores)),
        extremal_triple_fans=sum(p.get("ordinary_shared",0)==3 for p in ray_profiles),
        ray_profiles=ray_profiles,observed_balance=dict(two_deficit=2*deficit,
          single_plus_unbounded_minus_D1=end_tokens["single"]+end_tokens["unbounded"]-d1,
          D1_plus_unbounded=d1+end_tokens["unbounded"]))
    assert d1==row["ordinary_shared"] and d2==row["core_shared"]
    assert 2*deficit==result["observed_balance"]["single_plus_unbounded_minus_D1"]
    return result


if __name__=="__main__":
    data=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/fp-shared-rule.json").read_text())
    rows=[profile(r) for r in data["rows"] if r["n"] in [8,18,60]]
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/fp-boundary-profiles.json"
    out.write_text(json.dumps(dict(passed=True,trust="Exact sign-combinatorial endpoint audit; no Lean all-n ray-profile theorem",profiles=rows),indent=2)+"\n")
    print(json.dumps([{k:r[k] for k in ["n","q","T","D1","D2","U","deficit","core_graph_components","core_graph_cyclomatic","core_ray_totals","ordinary_opposite_ray_profiles","core_triangle_sector_profile","extremal_triple_fans","observed_balance"]} for r in rows]))
