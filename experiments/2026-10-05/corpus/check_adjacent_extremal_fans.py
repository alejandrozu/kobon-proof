"""Independent exact geometry audit of adjacent extremal higher-order fans."""
from pathlib import Path
from collections import Counter
import itertools as it,json,sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import arrangement

LINES=[(0,1,0),(5,1,0),(-5,1,0),(10,3,10),(10,-3,10),
       (-4,1,0),(9,2,0),(-6,1,-6),(6,1,6),(1,0,-2),(30,1,102)]


if __name__=="__main__":
    ar=arrangement(LINES)
    assert all(LINES[i][0]*LINES[j][1]!=LINES[i][1]*LINES[j][0] for i,j in it.combinations(range(len(LINES)),2))
    uses=Counter();incident=Counter()
    for triangle in ar["triangle_vertices"]:
        incident.update(triangle)
        uses.update(frozenset(e) for e in it.combinations(triangle,2))
    assert max(uses.values())<=2
    rows=[]
    for p,support in ar["points"].items():
        if len(support)<3:continue
        neighbors=[next(q for q in edge if q!=p) for edge,use in uses.items() if p in edge and use==2]
        ordinary=sum(len(ar["points"][q])==2 for q in neighbors)
        core=sum(len(ar["points"][q])>=3 for q in neighbors)
        rows.append(dict(point=list(p),multiplicity=len(support),support=sorted(support),
            triangular_sectors=incident[p],ordinary_shared=ordinary,core_shared=core,
            full=incident[p]==2*len(support),extremal=ordinary==2*len(support)-3))
    centers=[(0,0,1),(1,0,1)]
    selected=[next(r for r in rows if tuple(r["point"])==p) for p in centers]
    assert all(r["multiplicity"]==5 and r["full"] and r["ordinary_shared"]==7 for r in selected),selected
    assert uses[frozenset(centers)]==2
    result=dict(passed=True,n=11,line_convention="a*x+b*y=c",lines_frac=LINES,triangle_count=len(ar["triangles"]),
        triangles=sorted(ar["triangles"]),centers=selected,core_profiles=rows,shared_center_edge_triangles=2,
        conclusion="Adjacent full extremal fans can occur at multiplicity5; triple-only independence cannot be extended to all multiplicities",
        trust="Independent exact integer geometry; direct Lean witness is separate",attribution="New construction from the upper-bound research branch")
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/adjacent-extremal-fans-r5.json"
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ["passed","n","triangle_count","centers","shared_center_edge_triangles"]}))
