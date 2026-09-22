"""Build every result and audit its axioms; keep complete logs and status.

Requires the pinned Lean/Lake toolchain on PATH. Bounded concurrency avoids
starting all large coordinate certificates at once. No search software needed.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, time

ROOT=Path(__file__).resolve().parents[1]

def source_tokens(txt):
    """Strip Lean strings and nested comments before the conservative scan."""
    out=[];i=0;depth=0;string=False
    while i<len(txt):
        if depth:
            if txt.startswith('/-',i):depth+=1;i+=2
            elif txt.startswith('-/',i):depth-=1;i+=2
            else:i+=1
        elif string:
            if txt[i]=='\\':i+=2
            elif txt[i]=='"':string=False;i+=1
            else:i+=1
        elif txt.startswith('/-',i):depth=1;i+=2;out.append(' ')
        elif txt.startswith('--',i):
            end=txt.find('\n',i);i=len(txt) if end<0 else end;out.append(' ')
        elif txt[i]=='"':string=True;i+=1;out.append(' ')
        else:out.append(txt[i]);i+=1
    return ''.join(out)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--jobs',type=int,default=2)
    args=parser.parse_args()
    assert args.jobs>=1
    for p in [ROOT/'Kobon.lean',*(ROOT/'Kobon').rglob('*.lean')]:
        txt=source_tokens(p.read_text(encoding='utf-8'))
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',txt),f'Unapproved source token: {p}'
    targets=json.loads((ROOT/'verification/build-targets.json').read_text())
    logs=ROOT/'verification/build-logs';logs.mkdir(exist_ok=True)
    env=dict(os.environ);env.setdefault('LEAN_NUM_THREADS','2')
    results=[]
    def build(target):
        start=time.monotonic()
        run=subprocess.run(['lake','build',target],cwd=ROOT,env=env,
            text=True,encoding='utf-8',errors='replace',capture_output=True)
        output=run.stdout+run.stderr
        log=logs/(target+'.log');log.write_text(output,encoding='utf-8')
        passed=run.returncode==0 and 'sorryAx' not in output
        result=dict(target=target,passed=passed,returncode=run.returncode,
                    seconds=round(time.monotonic()-start,3),log=log.relative_to(ROOT).as_posix())
        print(('PASS' if passed else 'FAIL'),target,result['seconds'],flush=True)
        return result
    core=[t for t in targets if 'Certificates.' not in t and t not in ('Kobon.AllN','Kobon.Universal','Kobon','Kobon.Audit')]
    for t in core:
        r=build(t);results.append(r)
        if not r['passed']:break
    if all(r['passed'] for r in results):
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures=[pool.submit(build,t) for t in targets if 'Certificates.' in t]
            for f in as_completed(futures):results.append(f.result())
    if all(r['passed'] for r in results):
        for t in ('Kobon.AllN','Kobon.Universal','Kobon','Kobon.Audit'):
            r=build(t);results.append(r)
            if not r['passed']:break
    sources={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
             for p in [ROOT/'Kobon.lean',*(ROOT/'Kobon').rglob('*.lean')]}
    summary=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),
        lean_toolchain=(ROOT/'lean-toolchain').read_text().strip(),
        complete=len(results)==len(targets) and all(r['passed'] for r in results),
        scope='Unconditional parity-sensitive all-natural-order construction, projective cap gains and finite-certificate envelope; actual triangle/sign-cell geometry; unconditional 49-seed numerical target; finite coordinate lower bounds, real parameterized seeds, geometric exterior addition from visible pairs; complete one-step BBL doubling from a saturated compatible tangent-grid seed for q=4r>=20; local fan geometry and explicitly conditional global upper-budget arithmetic. Universal quantitative successor extension and end-to-end infinite BBL iteration remain separate proof obligations.',
        native_evaluation='Finite certificate checks use native_decide and trust Lean native evaluation; audit explicitly allows and lists those generated axioms.',
        results=results,source_sha256=sources)
    (ROOT/'verification/lean-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return 0 if summary['complete'] else 1

if __name__=='__main__':raise SystemExit(main())
