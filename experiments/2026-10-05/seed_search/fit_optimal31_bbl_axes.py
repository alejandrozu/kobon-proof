"""Test the actual31/299 affine type on every saturated tangent-grid axis.

The original affine infinity is fixed. No arbitrary cyclic recharting or
unverified pseudoline straightening is counted as an optimal straight seed.
LP outcomes are proposals/diagnostics; exact uniform verification is separate.
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


if __name__=="__main__":
    started=time.time();source=ROOT/"research/finite-table/classical-031.json";raw=json.loads(source.read_text())
    lines=[tuple(map(F,l)) for l in raw["lines_frac"]];ar=arrangement(lines)
    assert len(ar["triangles"])==299 and len(ar["points"])==465 and all(len(s)==2 for s in ar["points"].values())
    incidences=[sum(i in t for t in ar["triangles"]) for i in range(31)];axes=[i for i,c in enumerate(incidences) if c==29]
    homogeneous=[(a,b,-c) for a,b,c in lines]+[(F(0),F(0),F(1))]
    entries=[]
    for i,j,k in it.combinations(range(32),3):
        a,b,c=homogeneous[i];d,e,f=homogeneous[j];g,h,z=homogeneous[k]
        value=a*(e*z-f*h)-b*(d*z-f*g)+c*(d*h-e*g);assert value
        entries.append(((i,j,k),1 if value>0 else -1))
    chi=tensor(32,entries)
    bounds=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/tangent60/bounds.json").read_text())
    vals=[float((F(bounds[str(2*k)][0])+F(bounds[str(2*k)][1]))/2) for k in range(1,15)]
    roots=np.array([-v for v in reversed(vals)]+[0.,0.]+vals);A,_,_=matrix(roots)
    out=ROOT/"research/openmath-seven-hour-2026-10-05/seed_search/optimal31-bbl-axes";out.mkdir(parents=True,exist_ok=True)
    records=[]
    for axis in axes:
        labels,signs=chart_signs(chi,axis,31)
        proposal,status=solve(A,signs,10)
        record=dict(axis=axis,source_axis_triangles=29,lp_passed=proposal is not None,status=status,source_labels=labels)
        if proposal is not None:
            if proposal[14]<proposal[15]:proposal=-proposal
            path=out/f"axis{axis:02d}-proposal.json"
            data=dict(n=31,triangle_screen=299,caps_screen=29,reciprocal_slopes=[str(F(float(v+2)).limit_denominator(10**12)) for v in proposal],
                source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_axis=axis,source_labels=labels,
                original_infinity_label=31,status="Floating LP proposal; exact true-tangent whole-interval verification pending")
            path.write_text(json.dumps(data,indent=2)+"\n");record["proposal"]=str(path.relative_to(ROOT))
        records.append(record);print(json.dumps(record),flush=True)
        (out/"report.json").write_text(json.dumps(dict(original_count=299,simple=True,saturated_axes=axes,incidences=incidences,
            records=records,scope="This one exact31/299 affine type, fixed original infinity; floating LP diagnostics only",seconds=time.time()-started),indent=2)+"\n")
    print(json.dumps(dict(axes=len(axes),proposals=sum(r["lp_passed"] for r in records),seconds=time.time()-started)),flush=True)
