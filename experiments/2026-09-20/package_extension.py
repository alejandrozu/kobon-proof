"""Assemble the focused, reproducible user-facing extension package."""
import json, shutil
from pathlib import Path
from research import *

root=Path(__file__).resolve().parents[2]
work=Path(__file__).resolve().parent
out=root/'outputs'/'kobon-extension'
(out/'certificates').mkdir(parents=True,exist_ok=True)
for name in ['BoundaryExtension.lean','RationalExamples.lean']:
    shutil.copyfile(work/name,out/name)
shutil.copyfile(work/'research.py',out/'exact_geometry.py')
shutil.copyfile(root/'outputs'/'kobon-research'/'verify_direct.py',out/'verify_direct.py')

boundary=(work/'extension_audit.py').read_text().split('def line_samples')[0]
boundary=boundary.replace('"""Exact exterior-extension audit and exhaustive one-line cell search."""',
    '"""Exact exterior extension with rational arithmetic. Lines use a*x+b*y=c."""')
boundary=boundary.replace('from research import *','from exact_geometry import *')
checks=(work/'check_boundary.py').read_text().split('def cyclic_data')[1].split("if __name__=='__main__':")[0]
boundary+='def cyclic_data'+checks
(out/'boundary_extension.py').write_text(boundary,encoding='utf8')

def cert(name,lines,expected,source):
    ar=arrangement(lines)
    assert len(ar['triangles'])==expected
    data=dict(n=len(lines),triangle_count=expected,source=source,
        lines_frac=[[str(x) for x in l] for l in ar['lines']])
    (out/'certificates'/f'{name}.json').write_text(json.dumps(data,indent=2),encoding='utf8')

small=json.loads((work/'small-both-parities.json').read_text())
for data in small:
    cert(f'chain_{data["n"]}',data['lines_frac'],data['T'],'Explicit example from the extension manuscript; not a record claim')
ls=[(i,-1,-i*i) for i in range(5)]
cert('alternation_5',ls,3,'Parabolic tangent arrangement used to test the original alternating-segment lemma')
cert('alternation_6',ls+[(1,-2,-200)],4,'Previous five lines plus y=x/2+100; gain one rather than two')
large=json.loads((work/'simple21-extension.json').read_text())
for n,T in [(19,107),(20,116),(21,126)]:
    cert(f'chain_{n}',large['lines_frac'][:n],T,
        'Parpalak-Utkin published 19-line seed, followed by the explicitly certified exterior and interior additions; https://github.com/parpalak/triangle-maximal-18-series')

(out/'lean-toolchain').write_text('leanprover/lean4:v4.31.0\n',encoding='utf8')
(out/'lakefile.toml').write_text('''name = "kobon_extension"
version = "0.1.0"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
''',encoding='utf8')
print('Created package at',out)
