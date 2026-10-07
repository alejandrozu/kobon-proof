"""Exact profile of a five-sector triple with two antipodal ordinary caps."""
from pathlib import Path
from collections import Counter
import itertools as it,json,sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import arrangement

if __name__=="__main__":
    lines=[(0,1,0),(1,-1,0),(1,1,0),(1,0,1),(5,1,-5),(1,9,10)]
    ar=arrangement(lines);center=(0,0,1);uses=Counter();incident=Counter()
    for triangle in ar["triangle_vertices"]:
        incident.update(triangle);uses.update(frozenset(e) for e in it.combinations(triangle,2))
    assert all(lines[i][0]*lines[j][1]!=lines[i][1]*lines[j][0] for i,j in it.combinations(range(6),2))
    neighbors=[next(p for p in e if p!=center) for e,u in uses.items() if center in e and u==2]
    ordinary=[p for p in neighbors if len(ar["points"][p])==2]
    cores=[p for p in neighbors if len(ar["points"][p])>=3]
    assert incident[center]==5 and len(ordinary)==2 and len(cores)==2
    assert all(p[1]==0 for p in ordinary)
    result=dict(passed=True,n=6,lines_frac=lines,triangles=sorted(ar["triangles"]),triangle_count=len(ar["triangles"]),
                center=list(center),multiplicity=len(ar["points"][center]),triangular_sectors=incident[center],
                ordinary_shared=[list(p) for p in ordinary],core_shared=[list(p) for p in cores],
                ordinary_rays_antipodal=True,marked_core_rays=0,
                conclusion="A d1=2,d2=2 five-sector triple need not have a doubly-capped core ray",
                attribution="New local construction by upper-bound research branch",trust="Independent exact integer geometry; not a Lean witness yet")
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/antipodal-two-cap-five-sector.json"
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ["passed","n","triangle_count","triangular_sectors","ordinary_shared","core_shared","marked_core_rays"]}))
