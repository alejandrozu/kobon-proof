"""Fraction-only whole-interval verification of a new61 tangent-grid proposal.

The tangent bounds are exported from the compiled BBLTangent60Bounds module.
Screened triangle counts are never trusted.  The exact midpoint arrangement
is recounted, then every direction, simplicity and support interval is checked.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import argparse,hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import primitive,arrangement


def verify(source,out,minimum=1191):
    started=time.time();data=json.loads(source.read_text())
    if "reciprocal_slopes" in data:v=[F(s) for s in data["reciprocal_slopes"]]
    else:v=[1/F(s) for s in data["slopes"][1:]]
    q=len(v);n=q+1;d=q//2
    assert q in [30,60] and min(v)>0 and len(set(v))==q and v[d-1]>v[d]
    tangents=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/tangent60/bounds.json").read_text())
    ratio=60//q
    lo0=[F(tangents[str(ratio*k)][0]) for k in range(1,d)]
    hi0=[F(tangents[str(ratio*k)][1]) for k in range(1,d)]
    labels=[None]+[(k-1,-1) for k in range(d-1,0,-1)]+[(d-1,-1),(d-1,1)]+[(k-1,1) for k in range(1,d)]
    normals=[(F(0),F(1))]+[(F(1),-h) for h in v]
    @lru_cache(None)
    def det(i,j):
        a,b=normals[i];c,d=normals[j];return a*d-b*c
    assert all(det(i,j) for i,j in combinations(range(n),2))
    @lru_cache(None)
    def form(r,i,j,oriented=False):
        a,b=normals[r];c,d=normals[i];e,f=normals[j]
        coefficients={}
        for line,m in [(i,a*f-b*e),(j,-a*d+b*c),(r,-det(i,j))]:
            if labels[line]:
                pos,sgn=labels[line];coefficients[pos]=coefficients.get(pos,F(0))+m*sgn
        factor=det(i,j) if oriented else F(1)
        return tuple((pos,c*factor) for pos,c in sorted(coefficients.items()) if c)
    reports=[]
    for power in range(8,16):
        epsilon_upper=F(1,10**power);lo=lo0+[F(0)];hi=hi0+[epsilon_upper]
        midpoint=[(l+h)/2 for l,h in zip(lo,hi)]
        constants=[F(0)]+[sgn*midpoint[pos] for pos,sgn in labels[1:]]
        concrete=[primitive((*normal,c)) for normal,c in zip(normals,constants)]
        ar=arrangement(concrete);triangles=sorted(ar["triangles"]);caps=[t for t in triangles if 0 in t]
        if len(triangles)<minimum or len(caps)!=q-1:
            reports.append(dict(epsilon_upper=str(epsilon_upper),triangles=len(triangles),caps=len(caps),passed=False,reason="counts"))
            continue
        @lru_cache(None)
        def lower(f):return sum(c*(lo[pos] if c>=0 else hi[pos]) for pos,c in f)
        @lru_cache(None)
        def upper(f):return sum(c*(hi[pos] if c>=0 else lo[pos]) for pos,c in f)
        failure=None;simple=0;supports=0
        for i,j,k in combinations(range(n),3):
            f=form(k,i,j);simple+=1
            if not (lower(f)>0 or upper(f)<0 or (len(f)==1 and f[0][0]==d-1)):
                failure=dict(kind="simplicity",triple=[i,j,k]);break
        if failure is None:
            for i,j,k in triangles:
                for r in range(n):
                    fs=[form(r,a,b,True) for a,b in [(i,j),(i,k),(j,k)]];supports+=1
                    if not (all(lower(f)>=0 for f in fs) or all(upper(f)<=0 for f in fs)):
                        failure=dict(kind="triangle",triple=[i,j,k],line=r);break
                if failure:break
        report=dict(epsilon_upper=str(epsilon_upper),triangles=len(triangles),caps=len(caps),simple_checks=simple,triangle_support_checks=supports,passed=failure is None,failure=failure)
        reports.append(report);print(json.dumps(report),flush=True)
        if failure is None:
            assert len(ar["points"])==n*q//2
            result=dict(passed=True,n=n,triangle_count=len(triangles),distinguished=q-1,epsilon_max=str(epsilon_upper),
                reciprocal_slopes=[str(h) for h in v],slopes=["0"]+[str(1/h) for h in v],labels=labels,
                lo=[str(x) for x in lo],hi=[str(x) for x in hi],triangles=triangles,distinguished_triangles=caps,
                lines_frac=[[str(c) for c in line] for line in concrete],reports=reports,
                source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                tangent_proof="Kobon/BBLTangent60Bounds.lean",tangent_proof_sha256=hashlib.sha256((ROOT/"Kobon/BBLTangent60Bounds.lean").read_bytes()).hexdigest(),
                source_attribution="Rohith Poola61 affine seed; new LP/chirotope-cell mutation search",
                trust="Exact external rational-box certificate; full concrete Lean seed remains a separate verification step",seconds=time.time()-started)
            out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+"\n")
            return result
    result=dict(passed=False,source=str(source.relative_to(ROOT)),reports=reports,seconds=time.time()-started)
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+"\n")
    return result


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("source",type=Path);p.add_argument("--out",type=Path,required=True);p.add_argument("--minimum",type=int,default=1191)
    args=p.parse_args();r=verify(args.source.resolve(),args.out.resolve(),args.minimum)
    print(json.dumps({k:v for k,v in r.items() if k in ["passed","n","triangle_count","distinguished","epsilon_max","seconds"]}),flush=True)
