"""Rational-interval persistence certificate for the prior 19-line grid seed.

This verifies the existing Parpalak--Utkin positive control, not a new record.
The irrational tangent values are enclosed using the repository's Machin/Taylor
interval engine. Lean formalization of these interval calculations is separate.
"""
import itertools,json,sys,time
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import verify_seed as engine
from exact_geometry import primitive,arrangement
from verify_direct import verify

def run():
    start=time.monotonic();q=18;eps=F(1,1000)
    data=json.loads((ROOT/'experiments/2026-09-20/grid-seed-19-y0.json').read_text())
    # Six decimal places suffice; exact margin checking below is authoritative.
    vv=[-F(round(float(v)*10**6),10**6)for v in data['v']]
    assert len(set(vv))==q and all(vv)and vv[q//2-1]>0>vv[q//2]
    positive=[engine.tan_pi(k,q)for k in range(1,q//2)]
    def grid(e):return[-x for x in positive[::-1]]+[engine.I(-e),engine.I(e)]+positive
    grids=[grid(F(0)),grid(eps)];minimum=F(100);checks=[]
    for i,j,k in itertools.combinations(range(q),3):
        ds=[]
        for aa in grids:
            d=(aa[j]-aa[k])*vv[i]+(aa[k]-aa[i])*vv[j]+(aa[i]-aa[j])*vv[k]
            assert d.sign(),('unresolved',i,j,k,d.lo,d.hi)
            ds.append(d);minimum=min(minimum,abs(d.lo),abs(d.hi))
        assert ds[0].sign()==ds[1].sign(),('sign changes',i,j,k)
        checks.append(dict(triple=[i,j,k],sign=ds[0].sign()))
    aa=[x.midpoint()for x in grids[1]]
    ls=[(0,1,0)]+[primitive((1,-v,a))for a,v in zip(aa,vv)]
    ar=arrangement(ls);assert len(ar['triangles'])==107
    assert len(ar['points'])==171 and all(len(s)==2 for s in ar['points'].values())
    assert sum(0 in t for t in ar['triangles'])==17
    out=ROOT/'research/six-hour-2026-09-21/general-bounds';out.mkdir(parents=True,exist_ok=True)
    witness=out/'prior-seed19-rational.json'
    witness.write_text(json.dumps(dict(n=19,triangle_count=107,lines_frac=[[str(x)for x in l]for l in ls],
        source='Existing 2026-09-20 Parpalak--Utkin positive-control grid fit; no numerical novelty claim.',
        reciprocal_slopes=[str(v)for v in vv],epsilon=str(eps)),indent=2)+'\n')
    independent=verify(witness)
    report=dict(n=19,triangles=107,Y0_triangles=17,epsilon_interval='0<epsilon<=1/1000',
        reciprocal_slopes=[str(v)for v in vv],nonY_triples=len(checks),endpoint_interval_checks=2*len(checks),
        minimum_determinant_lower_bound=str(minimum),constant_distinct_reciprocal_slopes=True,
        tangent_bounds=[dict(k=k,lo=str(x.lo),hi=str(x.hi))for k,x in enumerate(positive,start=1)],
        determinant_signs=checks,independent_finite_verification=independent,
        seconds=time.monotonic()-start,
        status='Rigorous rational interval calculation; not Lean-verified. Whole interval follows because each determinant is affine in epsilon.',
        external_BBL_family='N=18*2^t+1, T=(324*4^t-1)/3=N(N-2)/3; prior construction and external BBL theorem, not a new numerical claim.')
    (out/'prior-seed19-interval.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k]for k in ('n','triangles','Y0_triangles','epsilon_interval','endpoint_interval_checks','seconds')}),flush=True)

if __name__=='__main__':run()
