"""Finite LP test of contestant affine types on the arbitrarily-small grid.
Positive floating margins are proposals, never proofs. Exact interval verification
and actual tangent enclosures remain separate.
"""
from pathlib import Path
import sys,json,itertools as it,time,hashlib
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-10-02'))
from word_grid_fit import tensor,chart_signs,np,linprog,math,warnings
out=ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant-limit-fits'
out.mkdir(parents=True,exist_ok=True)
reports=[]
for rel in ['bases/base31_290_s30005.json','bases/n61_1190_base31.json']:
    p=ROOT/'work/openmath-rohith/kobon-triangles'/rel
    raw=json.loads(p.read_text());ll=raw['lines'];n=len(ll);q=n-1
    hs=[tuple(map(F,x)) for x in ll]+[(F(0),F(0),F(1))]
    entries=[]
    for i,j,k in it.combinations(range(n+1),3):
        a,b,c=hs[i];d,e,f=hs[j];g,h,z=hs[k]
        dd=a*(e*z-f*h)-b*(d*z-f*g)+c*(d*h-e*g)
        assert dd,(i,j,k)
        entries.append(((i,j,k),1 if dd>0 else -1))
    chi=tensor(n+1,entries);ids,sg=chart_signs(chi,0,n)
    pairs=list(it.combinations(range(q),2));triples=list(it.combinations(range(q),3))
    for eps in [0,1e-7,1e-4,0.01]:
        aa=np.array(sorted([math.tan(k*math.pi/q) for k in range(-q//2+1,q//2) if k]+[-eps,eps]))
        matrix=np.zeros((len(pairs)+len(triples),q+1))
        for row,(i,j) in enumerate(pairs):matrix[row,i]=1;matrix[row,j]=-1
        for row,(i,j,k) in enumerate(triples,len(pairs)):
            matrix[row,i]=aa[j]-aa[k];matrix[row,j]=aa[k]-aa[i];matrix[row,k]=aa[i]-aa[j]
        matrix/=np.max(abs(matrix),axis=1)[:,None]
        matrix=-sg[:,None]*matrix;matrix[:,-1]=1
        obj=np.zeros(q+1);obj[-1]=-1
        with warnings.catch_warnings():
            warnings.simplefilter('ignore')
            result=linprog(obj,A_ub=matrix,b_ub=np.zeros(len(matrix)),bounds=[(-1,1)]*q+[(0,1)],method='highs',options={'threads':1,'time_limit':20})
        margin=float(result.x[-1]) if result.success else None
        rec=dict(n=n,epsilon=eps,margin=margin,status=int(result.status),source=rel,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
        if margin and margin>1e-9:
            vv=[F(float(v)).limit_denominator(10**10) for v in result.x[:-1]]
            # Reflection, if necessary, puts the central triangle above y=0.
            if vv[q//2-1]<vv[q//2]:vv=[-v for v in vv]
            vv=[v+2 for v in vv]
            path=out/f'n{n:03d}-epsilon{eps:g}.json'
            path.write_text(json.dumps(dict(rec,source_labels=ids,reciprocal_slopes=[str(v) for v in vv],source_commit='f462d8e18aea2a458376c523c9b6c2980237071f',status_note='LP proposal; exact true-tangent interval validation pending'),indent=2)+'\n')
            rec['proposal']=str(path.relative_to(ROOT))
        reports.append(rec);print(rec,flush=True)
        (out/'report.json').write_text(json.dumps(reports,indent=2)+'\n')