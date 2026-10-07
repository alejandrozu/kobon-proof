"""Bounded actual-affine saturated-axis probes for contestant point types.

Every input is exactly recounted, then each actual saturated axis is tested
against the epsilon-zero regular tangent-intercept grid. Positive LP margins
are candidate proposals, not verified uniform seeds or new lower bounds.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools as it,sys,json,time,hashlib,math,argparse
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-10-02'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/seed_search'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from word_grid_fit import tensor,chart_signs
from facet_walk61 import np,matrix,solve
from exact_geometry import arrangement,primitive

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--orders',nargs='+',type=int,default=[53]);ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--epsilons',nargs='+',type=float,default=[0.]);ap.add_argument('--tag',default='contestant-general-axes')
    args=ap.parse_args();start=time.time();deadline=start+args.seconds
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search'/args.tag;out.mkdir(parents=True,exist_ok=True)
    records=[]
    for n in args.orders:
        source=ROOT/f'work/openmath-rohith/kobon-triangles/submissions/n{n}/solution.json'
        raw=json.loads(source.read_text());lines=[primitive((F(a),F(b),-F(c))) for a,b,c in raw['lines']]
        ar=arrangement(lines);T=len(ar['triangles']);simple=all(len(s)==2 for s in ar['points'].values()) and len(ar['points'])==n*(n-1)//2
        inc=[sum(i in t for t in ar['triangles']) for i in range(n)];axes=[i for i,v in enumerate(inc) if v==n-2]
        record=dict(n=n,T=T,simple=simple,odd_upper=n*(n-2)//3,source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_commit='f462d8e18aea2a458376c523c9b6c2980237071f',saturated_axes=axes,incidences=inc,fits=[])
        records.append(record);print(json.dumps(dict(event='input',n=n,T=T,simple=simple,axes=len(axes))),flush=True)
        if not simple:continue
        hs=[(a,b,-c) for a,b,c in lines]+[(F(0),F(0),F(1))];entries=[]
        for i,j,k in it.combinations(range(n+1),3):
            a,b,c=hs[i];d,e,f=hs[j];g,h,z=hs[k]
            v=a*(e*z-f*h)-b*(d*z-f*g)+c*(d*h-e*g);assert v
            entries.append(((i,j,k),1 if v>0 else -1))
        chi=tensor(n+1,entries);q=n-1
        cached=[(axis,*chart_signs(chi,axis,n)) for axis in axes]
        for epsilon in args.epsilons:
          roots=np.array(sorted([math.tan(k*math.pi/q) for k in range(-q//2+1,q//2) if k]+[-epsilon,epsilon]));A,_,_=matrix(roots)
          for axis,labels,signs in cached:
            if time.time()>deadline:break
            x,status=solve(A,signs,10)
            fit=dict(axis=axis,epsilon=epsilon,passed=x is not None,status=status);record['fits'].append(fit)
            if x is not None:
                if x[q//2-1]<x[q//2]:x=-x
                proposal=dict(n=n,triangle_screen=T,caps_screen=n-2,epsilon=epsilon,source_labels=labels,reciprocal_slopes=[str(F(float(v+2)).limit_denominator(10**12)) for v in x],source=record['source'],source_sha256=record['source_sha256'],source_axis=axis,original_infinity_label=n,source_commit=record['source_commit'],status='Floating positive-margin LP proposal; exact true-tangent whole-interval certificate pending')
                path=out/f'n{n:03d}-axis{axis:03d}-eps{epsilon:g}-proposal.json';path.write_text(json.dumps(proposal,indent=2)+'\n');fit['proposal']=str(path.relative_to(ROOT))
                print(json.dumps(dict(event='proposal',n=n,T=T,axis=axis,epsilon=epsilon,margin=status)),flush=True)
            report=dict(records=records,seconds=time.time()-start,scope='Fixed actual affine infinity, all tested actual saturated axes; numerical screen only')
            (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(dict(event='finish',n=n,tested=len(record['fits']),proposals=sum(f['passed'] for f in record['fits']),seconds=time.time()-start)),flush=True)
    (out/'report.json').write_text(json.dumps(dict(records=records,seconds=time.time()-start,scope='Exact point-input recount; floating fixed-infinity epsilon-zero regular-grid LP diagnostics'),indent=2)+'\n')

if __name__=='__main__':main()
