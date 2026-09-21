import hashlib, json, zipfile
from pathlib import Path

root=Path(__file__).resolve().parents[2]
out=root/'outputs'/'kobon-extension'
report=json.loads((out/'verification.json').read_text())
assert report['all_checks_passed'] and report['deterministic_regression_cases']==560
for name in ['BoundaryExtension','RationalExamples']:
    log=(out/f'{name}.log').read_text(encoding='utf-8-sig')
    assert 'depends on axioms' in log
    assert not any(x in log for x in ['sorryAx','error:','error(','warning:'])
    code=(out/f'{name}.lean').read_text(encoding='utf-8-sig')
    assert 'sorry' not in code and '\naxiom ' not in code

for name in ['manuscript.md','claim_and_attribution.md','README.md']:
    text=(out/name).read_text(encoding='utf8')
    assert text.count(r'\[')==text.count(r'\]')
    for line in text.splitlines():
        assert line.count('$')%2==0,(name,line)
    assert r'/$2n$$' not in text and '(y=ix+i^2)' not in text

metadata=dict(date='2026-09-20',lean='4.31.0',
    mathlib='fabf563a7c95a166b8d7b6efca11c8b4dc9d911f',
    mathlib_checkout_clean=True,
    lean_compile_results={'BoundaryExtension.lean':0,'RationalExamples.lean':0},
    formalized_scope='Finite cyclic counting, numerical corollaries, parity equivalence, and explicit rational examples',
    not_formalized='The Euclidean boundary charging and exterior-addition reduction in manuscript Sections 2 and 3',
    full_uniform_gain_recurrence='Unproved in this package',
    priority='Not established',
    seed_source='https://github.com/parpalak/triangle-maximal-18-series/blob/master/data/n19/lines.csv',
    seed_input_sha256=hashlib.sha256((root/'work'/'kobon'/'series18-lines.csv').read_bytes()).hexdigest())
(out/'verification_scope.json').write_text(json.dumps(metadata,indent=2),encoding='utf8')
files=[p for p in out.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='manifest.json']
manifest={str(p.relative_to(out)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf8')
archive=root/'outputs'/'kobon-extension-2026-09-20.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for p in sorted(files+[out/'manifest.json']):
        z.write(p,p.relative_to(out))
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert len(z.namelist())==len(files)+1
print(json.dumps(dict(archive=str(archive),files=len(files)+1,bytes=archive.stat().st_size,
    manuscript_words=len((out/'manuscript.md').read_text().split()),checks='PASS'),indent=2))
