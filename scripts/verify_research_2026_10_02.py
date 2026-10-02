"""Replay the session's exact computations using only standard Python.

Reports go under verification/, keeping the frozen research evidence intact.
This checker does not promote computer-assisted certificates to Lean theorems.
"""
from pathlib import Path
import hashlib, json, subprocess, sys, time

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/research-2026-10-02'
DATA=Path('research/three-hour-2026-10-02/constructions')

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    commands=[
        ('affine-grid21',[
            'experiments/2026-10-02/verify_affine_grid_obstruction.py',
            str(DATA/'primary-inputs/data/exhaustive/21.uniq-e.txt'),
            str(DATA/'grid21-obstruction/affine-exact/certificates.json'),
            str(DATA/'grid21-obstruction/affine-exact/coverage-repairs.json'),
            '--out',str(OUT/'affine-grid21.json')]),
        ('uniform-grid49',[
            'experiments/2026-10-02/verify_uniform_grid49.py',
            str(DATA/'affine-grid49-limit/n049-I27-limit-slopes.json'),
            '--out',str(OUT/'uniform-grid49')]),
        ('uniform-grid49-visibility',[
            'experiments/2026-10-02/verify_uniform_grid49_visibility.py',
            str(OUT/'uniform-grid49/uniform-seed.json'),
            '--out',str(OUT/'visibility-grid49.json')]),
        ('local-grid-robustness',[
            'research/three-hour-2026-10-02/bbl/verify_local_robustness.py',
            '--out',str(OUT/'local-robustness.json')]),
        ('lean-export-grid49',[
            'experiments/2026-10-02/audit_lean_grid49_export.py',
            '--out',str(OUT/'lean-export-grid49.json')]),
    ]
    results=[]
    checked_sources=[Path(__file__),*[ROOT/args[0] for _,args in commands]]
    source_hashes={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in checked_sources}
    for name,args in commands:
        start=time.monotonic()
        p=subprocess.run([sys.executable,'-B',*args],cwd=ROOT,
            text=True,encoding='utf-8',errors='replace',capture_output=True)
        (OUT/(name+'.log')).write_text(p.stdout+p.stderr,encoding='utf-8')
        if name=='uniform-grid49' and p.returncode==0:
            regenerated=json.loads((OUT/'uniform-grid49/uniform-seed.json').read_text())
            frozen=json.loads((ROOT/DATA/'uniform-grid49/uniform-seed.json').read_text())
            for data in (regenerated,frozen):
                data['source']=data['source'].replace('\\','/')
            assert regenerated==frozen, 'Regenerated49 seed differs from the frozen exact evidence'
        result={'check':name,'passed':p.returncode==0,'returncode':p.returncode,
                'seconds':round(time.monotonic()-start,3)}
        results.append(result)
        print(('PASS' if result['passed'] else 'FAIL'),name,result['seconds'],flush=True)
        if p.returncode:
            print((p.stdout+p.stderr)[-3000:]);break
    passed=len(results)==len(commands) and all(r['passed'] for r in results)
    assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h
               for p,h in source_hashes.items()), 'A research checker changed during verification'
    (OUT/'summary.json').write_text(json.dumps({'passed':passed,
        'scope':'Exact computer-assisted certificates; external classification completeness is attributed, not re-enumerated or Lean-proved.',
        'source_sha256':source_hashes,'results':results},indent=2)+'\n',encoding='utf-8')
    return 0 if passed else 1

if __name__=='__main__':raise SystemExit(main())
