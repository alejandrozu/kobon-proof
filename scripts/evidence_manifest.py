"""Record/check hashes of stable project evidence, excluding run timestamps/logs."""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/'evidence/file-manifest.json'
DIRS=['Kobon','research','data','experiments','archive','scripts','evidence','.github']
EXCLUDED={'evidence/file-manifest.json'}
def records():
    paths=[p for directory in DIRS for p in (ROOT/directory).rglob('*') if p.is_file()]
    paths += [p for p in ROOT.iterdir() if p.is_file() and p.name!='.gitignore']
    paths += [ROOT/'verification/certificate-index.json',ROOT/'verification/build-targets.json']
    result={}
    for p in sorted(set(paths)):
        rel=p.relative_to(ROOT).as_posix()
        if rel in EXCLUDED or '__pycache__' in p.parts or p.suffix=='.pyc':continue
        result[rel]=dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
    return result
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    current=records()
    if args.check:
        old=json.loads(MANIFEST.read_text())['files']
        changed=sorted(k for k in old.keys()|current.keys() if old.get(k)!=current.get(k))
        assert not changed,'Evidence mismatch: '+', '.join(changed)
        print(f'PASS: {len(current)} evidence files match.')
    else:
        MANIFEST.parent.mkdir(exist_ok=True)
        MANIFEST.write_text(json.dumps(dict(algorithm='SHA-256',
          scope='Stable source/evidence files. Build logs and timestamped summaries are intentionally excluded; lean-summary hashes its checked sources separately.',
          files=current),indent=2)+'\n')
        print(f'Recorded {len(current)} evidence files.')
