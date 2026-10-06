"""Test regular-direction/empty-cone limits for the actual31/299 affine type.

Two special lines have normals(1,eta),(-1,eta) and pass through the origin.
At eta=0 their normals coincide projectively. The LP handles zero constant
determinants by their leading eta coefficient, rather than incorrectly
requiring a fixed-slope positive margin at the limit.

Forge's original perfect-projective hypothesis is NOT assumed or concluded.
Any feasible result still needs exact interval checks and a new valid
quantitative iteration theorem before an infinite-family claim.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import itertools as it,json,sys,math,time,warnings,hashlib
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"work/construction-deps"))
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
import numpy as np
from scipy.optimize import linprog
from exact_geometry import arrangement,primitive


def determinant(u,v,w):
    a,b,c=u;d,e,f=v;g,h,z=w
    return a*(e*z-f*h)-b*(d*z-f*g)+c*(d*h-e*g)
def sign(x):return (x>0)-(x<0)


if __name__=="__main__":
    started=time.time();source=ROOT/"research/finite-table/classical-031.json";raw=json.loads(source.read_text())
    lines=[tuple(map(F,l)) for l in raw["lines_frac"]];ar=arrangement(lines);assert len(ar["triangles"])==299
    oriented=[]
    for label,(a,b,c) in enumerate(lines):
        scale=1 if b>0 or (b==0 and a>0) else -1
        row=(scale*a,scale*b,-scale*c)
        oriented.append((math.atan2(float(row[1]),float(row[0])),label,row))
    oriented.sort()
    assert all(oriented[i][2][0]*oriented[j][2][1]-oriented[i][2][1]*oriented[j][2][0]>0 for i,j in it.combinations(range(31),2))
    tb=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/tangent60/bounds.json").read_text())
    tan={k:(F(tb[str(2*k)][0])+F(tb[str(2*k)][1]))/2 for k in range(1,15)}
    aa={k:float(tan[15-k]) if k<15 else 0. if k==15 else -float(tan[k-15]) for k in range(1,30)}
    out=ROOT/"research/openmath-seven-hour-2026-10-05/seed_search/forge31-leading-fit";out.mkdir(parents=True,exist_ok=True)
    reports=[]
    for cut in range(31):
        selected=oriented[cut:]+oriented[:cut]
        rows=[row if i+cut<31 else tuple(-x for x in row) for i,(angle,label,row) in enumerate(selected)]
        labels=[label for angle,label,row in selected]
        inside=[]
        for r,s in it.combinations(range(1,30),2):
            a=sign(determinant(rows[0],rows[r],rows[s]));b=sign(determinant(rows[30],rows[r],rows[s]));assert a and b
            if a==b:inside.append((r,s,a))
        degrees=Counter(v for r,s,a in inside for v in [r,s])
        record=dict(cut=cut,source_labels=labels,inside_pairs=inside,inside_max_degree=max(degrees.values(),default=0))
        if max(degrees.values(),default=0)>1:
            record.update(passed=False,reason="Cone-axis pair graph is not a matching; simple regular intersections cannot all lie on the auxiliary axis")
            reports.append(record);continue
        parent={r:r for r in range(1,30)}
        for r,s,a in inside:parent[s]=r
        group_ids={g:i for i,g in enumerate(sorted(set(parent.values())))};groups={r:group_ids[parent[r]] for r in parent};d=len(group_ids)
        inequalities=[]
        def add(coefficients,orientation):
            vec=np.zeros(d)
            for line,value in coefficients.items():vec[groups[line]]+=orientation*value
            magnitude=max(abs(vec));assert magnitude>0
            inequalities.append(vec/magnitude)
        for i,j,k in it.combinations(range(1,30),3):
            s=sign(determinant(rows[i],rows[j],rows[k]));assert s
            add({i:aa[j]-aa[k],j:aa[k]-aa[i],k:aa[i]-aa[j]},s)
        inside_set={(r,s) for r,s,a in inside}
        for r,s in it.combinations(range(1,30),2):
            orientation=sign(determinant(rows[0],rows[r],rows[s]))
            if (r,s) in inside_set:add({r:aa[s],s:-aa[r]},orientation)
            else:add({r:-1.,s:1.},orientation)
        for r in range(1,30):add({r:-1.},sign(determinant(rows[0],rows[r],rows[30])))
        matrix=np.array(inequalities);ub=np.column_stack([-matrix,np.ones(len(matrix))]);objective=np.zeros(d+1);objective[-1]=-1
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            result=linprog(objective,A_ub=ub,b_ub=np.zeros(len(ub)),bounds=[(-1,1)]*d+[(0,1)],method="highs",options={"threads":1,"time_limit":10})
        margin=float(result.x[-1]) if result.success else None;record.update(lp_status=int(result.status),margin=margin,passed=bool(margin and margin>1e-9),groups=groups)
        if record["passed"]:
            constants={r:F(float(result.x[groups[r]])).limit_denominator(10**12) for r in range(1,30)}
            eta=F(1,10**6)
            normals=[(F(1),eta)]+[(tan[15-k] if k<15 else F(0) if k==15 else -tan[k-15],F(1)) for k in range(1,30)]+[(F(-1),eta)]
            concrete=[primitive((*normal,F(0) if i in [0,30] else -constants[i])) for i,normal in enumerate(normals)]
            test=arrangement(concrete);T=len(test["triangles"])
            record["exact_midpoint_count"]=T
            proposal=dict(n=31,triangle_count=T,eta=str(eta),constants=["0"]+[str(constants[r]) for r in range(1,30)]+["0"],
                lines_frac=[[str(c) for c in l] for l in concrete],source_labels=labels,inside_pairs=inside,
                source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                status="Floating leading-coefficient LP plus exact rational midpoint count; true-tangent uniform sign verification pending",
                iteration_scope="Original Forge p3-maximal hypothesis not satisfied automatically; no family claim")
            path=out/f"cut{cut:02d}-proposal.json";path.write_text(json.dumps(proposal,indent=2)+"\n");record["proposal"]=str(path.relative_to(ROOT))
            print(json.dumps(dict(event="proposal",cut=cut,margin=margin,T=T)),flush=True)
        reports.append(record)
    result=dict(source=str(source.relative_to(ROOT)),reports=reports,proposals=[r for r in reports if r.get("passed")],seconds=time.time()-started,
                scope="One actual31/299 affine type, fixed original infinity, regular-slope/collapsing-special-pair leading LP")
    (out/"report.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(cuts=31,matching_candidates=sum(r["inside_max_degree"]<=1 for r in reports),proposals=len(result["proposals"]),seconds=result["seconds"])))
