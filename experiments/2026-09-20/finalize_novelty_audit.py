import json,sys,math,hashlib
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'outputs/kobon-extension'))
from exact_geometry import primitive,arrangement
from verify_direct import verify
dest=root/'outputs/kobon-own-results'
(dest/'comparison-certificates').mkdir(exist_ok=True)
checks=[]
for n in [44,99,195]:
    lines=[]
    for i in range(n):
        a=(2*i+1)*math.pi/n
        lines.append(primitive(tuple(F(str(v)) for v in (math.sin(a/2),math.cos(a/2),math.sin(3*a/2)))))
    ar=arrangement(lines)
    assert len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
    t=len(ar['triangles'])
    assert t==(n*(n-3)+2)//3
    p=dest/'comparison-certificates'/f'fp-{n}.json'
    p.write_text(json.dumps(dict(n=n,triangle_count=t,lines_frac=lines,
       attribution='Rational approximation to Furedi-Palasti Example 1. Reproduction of prior construction, not an original construction claim.')),encoding='utf-8')
    checks.append(verify(p))
(dest/'comparison_verification.json').write_text(json.dumps(checks,indent=2),encoding='utf-8')

p=dest/'inventory.json'; data=json.loads(p.read_text())
r=next(x for x in data['rows'] if x['n']==44)
r.update(kind='C',basis='Exact exterior extension of the published Parpalak-Utkin 43-line arrangement',
         certificate='certificates/n044.json',
         sha256=hashlib.sha256((dest/'certificates/n044.json').read_bytes()).hexdigest())
data['priority_audit']='novelty-audit.md'
p.write_text(json.dumps(data,indent=2),encoding='utf-8')
p=dest/'results.md'; text=p.read_text(); text=text.replace('| 44 | 608 | G |','| 44 | 608 | C |')
text+='\nAn exact 44-line certificate was added during the priority audit. See [novelty-audit.md](novelty-audit.md) for the distinction between old, dominated, and still-unresolved priority candidates.\n'
p.write_text(text,encoding='utf-8')
