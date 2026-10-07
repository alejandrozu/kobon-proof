"""Exact one-line deletion profiles of corpus simple perfect arrangements.

Discovery runs rebuilding every arrangement are unnecessary: delete the
removed line's vertices from the exact ordered rows and add the new edges.
Only new edges can create triangles.  This tests whether a deletion family
could improve G at powers of two; it proves only the supplied finite cases.
"""
from pathlib import Path
from collections import defaultdict
import itertools as it,json,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import arrangement,primitive


def run(path):
    started=time.time()
    data=json.loads(path.read_text())
    lines=[primitive((a,b,-c)) for a,b,c in data["lines"]]
    n=len(lines)
    ar=arrangement(lines)
    assert len(ar["points"])==n*(n-1)//2 and all(len(s)==2 for s in ar["points"].values())
    vertices={p:i for i,p in enumerate(ar["points"])}
    rows=[[vertices[p] for p in row] for row in ar["rows"]]
    supports={vertices[p]:s for p,s in ar["points"].items()}
    original=[set(t) for t in ar["triangles"]]
    result=[]
    for removed in range(n):
        edge_lines={};neighbors=defaultdict(set);new_edges=set()
        for i,row in enumerate(rows):
            if i==removed:continue
            remaining=[v for v in row if removed not in supports[v]]
            old_edges={frozenset((a,b)) for a,b in zip(row,row[1:])}
            for a,b in zip(remaining,remaining[1:]):
                edge=frozenset((a,b));edge_lines[edge]=i
                neighbors[a].add(b);neighbors[b].add(a)
                if edge not in old_edges:new_edges.add(edge)
        new_triangles=set()
        for edge in new_edges:
            a,b=edge
            for c in neighbors[a]&neighbors[b]:
                sides=(edge_lines[edge],edge_lines[frozenset((a,c))],edge_lines[frozenset((b,c))])
                if len(set(sides))==3:new_triangles.add(tuple(sorted(sides)))
        lost=sum(removed in t for t in original)
        count=len(original)-lost+len(new_triangles)
        result.append(dict(removed=removed,lost=lost,created=len(new_triangles),triangles=count,new_triangles=sorted(new_triangles)))
    return dict(source=str(path.relative_to(ROOT)),n=n,triangles=len(original),simple=True,
                best_remaining=max(r["triangles"] for r in result),profiles=result,seconds=time.time()-started)


if __name__=="__main__":
    base=ROOT/"work/openmath-rohith/kobon-triangles/doubled"
    rows=[run(base/name) for name in ["n49_767_b7_d4.json","n65_1365_b3_d4.json","n97_3071_b7_d4.json"]]
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/perfect-seed-deletions.json"
    out.write_text(json.dumps(dict(passed=True,trust="External exact finite deletion profiles; no infinite deletion theorem",results=rows),indent=2)+"\n")
    print(json.dumps([{k:r[k] for k in ["n","triangles","best_remaining","seconds"]} for r in rows]))
