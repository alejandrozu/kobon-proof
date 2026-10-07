"""Recount every projective chart of the actual31/299 source before BBL fits.

A change of infinity can change bounded triangles. We keep this exact count
and axis saturation explicit, and test298 as well as299 since either could
give a stronger constant-gap dyadic straight-line family.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,itertools as it,json,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"experiments/2026-10-02"))
sys.path.insert(0,str(ROOT/"experiments/2026-10-05/seed_search"))
from word_grid_fit import tensor,chart_signs
from facet_walk61 import np,matrix,solve
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import arrangement


def cross(u,v):return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def dot(u,v):return sum(a*b for a,b in zip(u,v))
def normalize(rows,I,J):
    c0=cross(rows[I],rows[J]);K=next(k for k,H in enumerate(rows) if dot(H,c0))
    c1=cross(rows[J],rows[K]);c2=cross(rows[K],rows[I]);base=[]
    for k,H in enumerate(rows):
        if k in [I,J]:continue
        A,B,C=dot(H,c0),dot(H,c1),dot(H,c2);assert A
        base.append((F(-C,A),F(-B,A),k))
    return sorted(base)


if __name__=="__main__":
    started=time.time();source=ROOT/"research/finite-table/classical-031.json";raw=json.loads(source.read_text())
    lines=[tuple(map(F,l)) for l in raw["lines_frac"]]
    rows=[(a,b,-c) for a,b,c in lines]+[(F(0),F(0),F(1))]
    entries=[]
    for i,j,k in it.combinations(range(32),3):
        value=dot(rows[i],cross(rows[j],rows[k]));assert value
        entries.append(((i,j,k),1 if value>0 else -1))
    chi=tensor(32,entries)
    bounds=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/tangent60/bounds.json").read_text())
    vals=[float((F(bounds[str(2*k)][0])+F(bounds[str(2*k)][1]))/2) for k in range(1,15)]
    roots=np.array([-v for v in reversed(vals)]+[0.,0.]+vals);A,_,_=matrix(roots)
    out=ROOT/"research/openmath-seven-hour-2026-10-05/seed_search/optimal31-projective-charts";out.mkdir(parents=True,exist_ok=True)
    charts=[];records=[];seen={};proposals=[]
    # Original infinity first, then the other exact projective labels.
    for infinity in [31]+list(range(31)):
        axis=next(i for i in range(32) if i!=infinity);base=normalize(rows,axis,infinity)
        newlines=[(F(0),F(1),F(0))]+[(F(1),-v,a) for a,v,k in base]
        ar=arrangement(newlines);assert len(ar["points"])==465 and all(len(s)==2 for s in ar["points"].values())
        count=len(ar["triangles"]);labels=[axis]+[k for a,v,k in base]
        incidences={label:sum(i in t for t in ar["triangles"]) for i,label in enumerate(labels)}
        axes=[label for label,value in incidences.items() if value==29]
        chart=dict(infinity=infinity,triangle_count=count,saturated_axes=axes,incidences=incidences,
            exact_chart_lines=[[str(x) for x in l] for l in newlines],chart_line_labels=labels)
        charts.append(chart);print(json.dumps({k:chart[k] for k in ["infinity","triangle_count","saturated_axes"]}),flush=True)
        if count<291:continue
        for axis in axes:
            ids,sg=chart_signs(chi,axis,infinity);key=hashlib.sha256(sg.tobytes()).hexdigest()
            if key in seen:
                records.append(dict(axis=axis,infinity=infinity,triangle_count=count,duplicate_of=seen[key]));continue
            seen[key]=[axis,infinity]
            candidate,status=solve(A,sg,10)
            record=dict(axis=axis,infinity=infinity,triangle_count=count,passed=candidate is not None,status=status,cell_hash=key)
            if candidate is not None:
                if candidate[14]<candidate[15]:candidate=-candidate
                proposal=dict(n=31,triangle_screen=count,caps_screen=29,
                    reciprocal_slopes=[str(F(float(v+2)).limit_denominator(10**12)) for v in candidate],
                    source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    axis=axis,infinity=infinity,source_labels=ids,
                    status="Floating LP proposal; exact true-tangent uniform verification required")
                path=out/f"T{count}-I{axis:02d}-J{infinity:02d}-proposal.json";path.write_text(json.dumps(proposal,indent=2)+"\n")
                record["proposal"]=str(path.relative_to(ROOT));proposals.append(record)
                print(json.dumps(dict(event="proposal",**record)),flush=True)
            records.append(record)
        report=dict(source=str(source.relative_to(ROOT)),charts=charts,records=records,proposals=proposals,
            unique_cells=len(seen),seconds=time.time()-started,scope="One actual projective32-line type; exact recharted bounded counts, floating grid-fit diagnostics")
        (out/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(charts=len(charts),unique_cells=len(seen),proposals=len(proposals),seconds=time.time()-started)),flush=True)
    (out/"report.json").write_text(json.dumps(dict(source=str(source.relative_to(ROOT)),charts=charts,records=records,
        proposals=proposals,unique_cells=len(seen),seconds=time.time()-started,
        scope="One actual projective32-line type; exact recharted bounded counts, floating grid-fit diagnostics"),indent=2)+"\n")
