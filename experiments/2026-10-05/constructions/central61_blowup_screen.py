"""Exact small-epsilon tests of rational central-slope blow-ups.
Finite samples discover limiting constructions; they are not uniform proofs.
All saved counts use exact adjacency on rational tangent-box midpoints.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,itertools,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import primitive,arrangement
raw=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-uniform-box.json').read_text())
slopes=list(map(F,raw['slopes']));labels=raw['labels'];lo=list(map(F,raw['lo']));hi=list(map(F,raw['hi']))
central=[i for i,lab in enumerate(labels) if lab and lab[0]==29]
report=dict(source='contestant61-uniform-box.json',central=central,scope='Exact finite samples only; uniform small-epsilon proof remains separate',cases=[])
for p,q in [(1,1),(1,0),(0,1),(2,2),(1,2),(2,1),(0,0),(-1,-1)]:
    rec=dict(p=p,q=q,samples=[])
    for e in [F(1,10**3),F(1,10**5),F(1,10**8),F(1,10**12)]:
        ss=slopes.copy();ss[central[0]]*= (F(1,100)/e)**p;ss[central[1]]*= (F(1,100)/e)**q
        pars=[(l+h)/2 for l,h in zip(lo,hi)];pars[-1]=e
        lines=[(0,1,0)]+[primitive((ss[i],-1,ss[i]*lab[1]*pars[lab[0]])) for i,lab in enumerate(labels[1:],1)]
        a=arrangement(lines);ts=sorted(a['triangles']);caps=sum(0 in t for t in ts)
        rr=dict(epsilon=str(e),triangles=len(ts),caps=caps,simple=len(a['points'])==1830)
        rec['samples'].append(rr);print(dict(p=p,q=q,**rr),flush=True)
        if len(ts)>=1190 and caps==59:
            file=ROOT/f'research/openmath-seven-hour-2026-10-05/constructions/central61-p{p}-q{q}-eps{e.denominator}.json'
            file.write_text(json.dumps(dict(n=61,triangle_count=len(ts),lines_frac=[[str(x) for x in l] for l in lines],triangles=ts,central_exponents=[p,q],epsilon=str(e),source='Rohith Poola fixed61 slopes after reflection and central blow-up',uniform_status='Not proved; exact point witness only'),indent=2)+'\n')
    report['cases'].append(rec)
    (ROOT/'research/openmath-seven-hour-2026-10-05/constructions/central61-blowup-screen.json').write_text(json.dumps(report,indent=2)+'\n')