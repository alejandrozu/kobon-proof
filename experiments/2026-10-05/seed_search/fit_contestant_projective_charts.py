"""Exact rechart/recount followed by bounded epsilon-dependent grid LP probes.

Every positive numerical output remains a proposal. Fixed-epsilon feasibility
does not imply an arbitrarily-small parameter family; all negative outputs are
diagnostics, not exact infeasibility certificates.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,itertools as it,json,sys,time,math,argparse,warnings
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/seed_search'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-02'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from word_grid_fit import tensor,chart_signs
from facet_walk61 import np,matrix,sparse,linprog
from fit_optimal31_projective_charts import normalize,cross,dot
from exact_geometry import arrangement,primitive

def lp(A,sg,limit):
    M=sparse.hstack([-sparse.diags(sg.astype(float))@A,np.ones((A.shape[0],1))],format='csr')
    objective=np.zeros(A.shape[1]+1);objective[-1]=-1
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        r=linprog(objective,A_ub=M,b_ub=np.zeros(A.shape[0]),bounds=[(-1,1)]*A.shape[1]+[(0,1)],method='highs',options={'threads':1,'time_limit':limit,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
    margin=float(r.x[-1]) if r.success else None
    residual=float(np.min(sg*(A@r.x[:-1]))) if r.success else None
    passed=bool(r.success and margin>1e-9 and residual>1e-10)
    return (r.x[:-1] if passed else None),dict(lp_status=int(r.status),margin=margin,min_signed_residual=residual,passed=passed)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=53);ap.add_argument('--epsilons',nargs='+',type=float,default=[0.,0.001]);ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--max-charts',type=int,default=0)
    args=ap.parse_args();started=time.time();deadline=started+args.seconds;n=args.n;q=n-1
    source=ROOT/f'work/openmath-rohith/kobon-triangles/submissions/n{n}/solution.json';raw=json.loads(source.read_text());lines=[primitive((F(a),F(b),-F(c))) for a,b,c in raw['lines']]
    rows=[(a,b,-c) for a,b,c in lines]+[(F(0),F(0),F(1))];entries=[]
    for i,j,k in it.combinations(range(n+1),3):
        v=dot(rows[i],cross(rows[j],rows[k]));assert v
        entries.append(((i,j,k),1 if v>0 else -1))
    chi=tensor(n+1,entries)
    matrices={eps:matrix(np.array(sorted([math.tan(k*math.pi/q) for k in range(-q//2+1,q//2) if k]+[-eps,eps])))[0] for eps in args.epsilons}
    out=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/contestant{n}-projective-charts';out.mkdir(parents=True,exist_ok=True)
    charts=[];records=[];seen={};proposals=[]
    def save():
        report=dict(n=n,source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_commit='f462d8e18aea2a458376c523c9b6c2980237071f',charts=charts,records=records,proposals=proposals,unique_cells=len(seen),seconds=time.time()-started,scope='Exactly recounted affine cuts of one actual projective type, floating epsilon-grid fitting; no infeasibility or uniform-family theorem')
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    for infinity in ([n]+list(range(n)))[:args.max_charts or n+1]:
        if time.time()>deadline:break
        axis=next(i for i in range(n+1) if i!=infinity);base=normalize(rows,axis,infinity)
        newlines=[(F(0),F(1),F(0))]+[(F(1),-v,a) for a,v,k in base]
        ar=arrangement(newlines);assert len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
        count=len(ar['triangles']);labels=[axis]+[k for a,v,k in base]
        incidence={label:sum(i in t for t in ar['triangles']) for i,label in enumerate(labels)};axes=[label for label,v in incidence.items() if v==n-2]
        chart=dict(infinity=infinity,T=count,saturated_axes=axes,incidences=incidence);charts.append(chart)
        print(json.dumps(dict(event='chart',infinity=infinity,T=count,axes=len(axes),seconds=time.time()-started)),flush=True)
        if not axes:save();continue
        for axis in axes:
            if time.time()>deadline:break
            ids,sg=chart_signs(chi,axis,infinity);key=hashlib.sha256(sg.tobytes()).hexdigest()
            if key in seen:
                records.append(dict(axis=axis,infinity=infinity,T=count,duplicate_of=seen[key]));continue
            seen[key]=[axis,infinity]
            for epsilon,A in matrices.items():
                x,diagnostics=lp(A,sg,10);record=dict(axis=axis,infinity=infinity,T=count,epsilon=epsilon,cell_hash=key,**diagnostics)
                if x is not None:
                    if x[q//2-1]<x[q//2]:x=-x
                    proposal=dict(n=n,triangle_screen=count,caps_screen=n-2,epsilon=epsilon,reciprocal_slopes=[str(F(float(v+2)).limit_denominator(10**12)) for v in x],source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_commit='f462d8e18aea2a458376c523c9b6c2980237071f',axis=axis,infinity=infinity,source_labels=ids,status='Floating grid LP candidate; exact midpoint and true-tangent parameter proof pending')
                    path=out/f'T{count}-I{axis:03d}-J{infinity:03d}-eps{epsilon:g}.json';path.write_text(json.dumps(proposal,indent=2)+'\n');record['proposal']=str(path.relative_to(ROOT));proposals.append(record)
                    print(json.dumps(dict(event='proposal',**record)),flush=True)
                records.append(record)
        save()
    save();print(json.dumps(dict(charts=len(charts),cells=len(seen),positive=len(proposals),seconds=time.time()-started)),flush=True)

if __name__=='__main__':main()
