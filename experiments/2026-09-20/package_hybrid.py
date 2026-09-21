"""Audit metadata, hash deliverables, and create the portable research packet."""
from pathlib import Path
import hashlib,json,zipfile

workspace=Path(__file__).resolve().parents[2]
root=workspace/'outputs'/'kobon-hybrid'
records=json.loads((root/'finite-verification.json').read_text())
expected={11:32,12:37,21:132,22:142,41:532,42:552,81:2132,82:2172,161:8532,162:8612}
assert {r['n']:r['triangles'] for r in records}==expected
for r in records:
    assert r['pass_check'] and r['simple'] and r['adjacency_count']==r['triangles']
    data=json.loads((root/'certificates'/r['file']).read_text())
    assert data['n']==len(data['lines_frac'])==r['n']
    assert data['triangle_count']==r['triangles']
report=json.loads((root/'seed-verification.json').read_text())
assert report['endpoint_interval_checks']==240 and report['triangles']==32
files=sorted(p for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts
             and p.name!='manifest.json')
manifest=dict(date='2026-09-20',family='N=10*2^t+1, T=(100*4^t-4)/3',
              verified_finite_counts=expected,priority='Not established',
              files=[dict(path=p.relative_to(root).as_posix(),bytes=p.stat().st_size,
                          sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files])
(root/'manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
archive=root.parent/'kobon-hybrid-2026-09-20.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in files+[root/'manifest.json']:
        z.write(p,'kobon-hybrid/'+p.relative_to(root).as_posix())
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for entry in manifest['files']:
        assert hashlib.sha256(z.read('kobon-hybrid/'+entry['path'])).hexdigest()==entry['sha256']
print('PASS: all ten certificate records match their coordinates and verification reports.')
print('PASS:',len(files),'hashed files plus manifest; archive CRC and SHA-256 round trip.')
print(archive,'bytes',archive.stat().st_size)
