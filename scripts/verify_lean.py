"""Build every result and audit its axioms; keep complete logs and status.

Requires the pinned Lean/Lake toolchain on PATH. Bounded concurrency avoids
starting all large coordinate certificates at once. No search software needed.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, time

ROOT=Path(__file__).resolve().parents[1]

AGGREGATES=('Kobon.AllN','Kobon.Universal','Kobon','Kobon.Audit')


def is_certificate(module):
    return module.startswith(('Kobon.Certificates.','Kobon.SimpleCertificates.'))


def module_path(module):
    return ROOT/(module.replace('.','/')+'.lean')

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


def local_import_dependencies(targets):
    """Read the transitive local import graph without running Lean or Lake."""
    dependencies={}
    visiting=set()

    def closure(module):
        if module in dependencies:return dependencies[module]
        assert module not in visiting, f'Cyclic local imports: {module}'
        visiting.add(module)
        path=module_path(module)
        assert path.is_file(), f'Missing local module: {module}'
        tokens=source_tokens(path.read_text(encoding='utf-8'))
        direct=[]
        for line in tokens.splitlines():
            match=re.match(r'^\s*import\s+(.+)$',line)
            if match:
                direct.extend(m for m in match.group(1).split()
                              if m=='Kobon' or m.startswith('Kobon.'))
        deps=set(direct)
        for dep in direct:deps.update(closure(dep))
        visiting.remove(module)
        dependencies[module]=deps
        return deps

    for target in targets:closure(target)
    return dependencies


def unbuilt_active_sources(paths, targets, dependencies):
    reachable=set(targets)
    for target in targets:reachable.update(dependencies[target])
    modules={'.'.join(p.relative_to(ROOT).with_suffix('').parts):p for p in paths}
    return sorted(module for module in modules if module not in reachable)


def build_phases(targets, dependencies=None):
    """Keep every finite-certificate consumer behind the bounded build phase.

    This follows transitive local imports, so a new module importing Universal,
    a comparison module, or Results cannot silently trigger a large certificate
    dependency build in the early sequential phase. The final root and axiom
    audit always run after every other requested target.
    """
    assert len(targets)==len(set(targets)), 'Duplicate build target'
    assert all(t in targets for t in AGGREGATES), 'Missing aggregate target'
    if dependencies is None:dependencies=local_import_dependencies(targets)
    terminal={'Kobon','Kobon.Audit'}
    certificates=[t for t in targets if is_certificate(t)]
    deferred={t for t in targets if t in AGGREGATES or
              any(is_certificate(d) or d in AGGREGATES for d in dependencies[t])}

    def ordered(modules):
        pending=set(modules);result=[]
        while pending:
            ready=[m for m in modules if m in pending and not (dependencies[m]&pending)]
            assert ready, f'No dependency-safe build order: {sorted(pending)}'
            for m in ready:pending.remove(m);result.append(m)
        return result

    core=ordered([t for t in targets if t not in deferred and not is_certificate(t)])
    late=ordered([t for t in targets if t in deferred and t not in terminal
                  and not is_certificate(t)])+['Kobon','Kobon.Audit']
    assert set(core+certificates+late)==set(targets)
    return core,certificates,late

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--jobs',type=int,default=2)
    args=parser.parse_args()
    assert args.jobs>=1
    active_sources=[ROOT/'Kobon.lean',*(ROOT/'Kobon').rglob('*.lean')]
    for p in active_sources:
        txt=source_tokens(p.read_text(encoding='utf-8'))
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',txt),f'Unapproved source token: {p}'
    targets=json.loads((ROOT/'verification/build-targets.json').read_text(encoding='utf-8'))
    dependencies=local_import_dependencies(targets)
    uncovered=unbuilt_active_sources(active_sources,targets,dependencies)
    assert not uncovered, ('Active Lean files are outside the verified import/build closure: '
        +', '.join(uncovered)+'. Move unfinished sources to research drafts or explicitly integrate them.')
    audited=dependencies['Kobon']|{'Kobon','Kobon.Audit'}
    unaudited=sorted('.'.join(p.relative_to(ROOT).with_suffix('').parts)
        for p in active_sources if '.'.join(p.relative_to(ROOT).with_suffix('').parts) not in audited)
    assert not unaudited, 'Active Lean files are outside the root axiom audit: '+', '.join(unaudited)
    initial_sources={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in active_sources}
    core,certificates,late=build_phases(targets,dependencies)
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
    for t in core:
        r=build(t);results.append(r)
        if not r['passed']:break
    if all(r['passed'] for r in results):
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures=[pool.submit(build,t) for t in certificates]
            for f in as_completed(futures):results.append(f.result())
    if all(r['passed'] for r in results):
        for t in late:
            r=build(t);results.append(r)
            if not r['passed']:break
    final_sources={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in [ROOT/'Kobon.lean',*(ROOT/'Kobon').rglob('*.lean')]}
    source_changes=sorted(p for p in initial_sources.keys()|final_sources.keys()
                          if initial_sources.get(p)!=final_sources.get(p))
    summary=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),
        lean_toolchain=(ROOT/'lean-toolchain').read_text().strip(),
        complete=len(results)==len(targets) and all(r['passed'] for r in results) and not source_changes,
        scope='Unconditional parity-sensitive all-natural-order construction and retained finite-certificate envelope; actual triangle/sign-cell geometry; unconditional 49-seed numerical target; complete finite-depth BBL iteration and full exterior visibility for the compatible 11-seed odd/even dyadic families, with a shrinking allowable parameter interval at each depth; an all-order envelope retaining these families and the previous release. Generic Forge-family formulas retain explicit seed premises. An exact real tangent-grid ten-sign obstruction is proved. Actual geometric vertex, elementary-edge, shared-side and multiple-point-core incidence identities are extracted for finite injective certificate families of pairwise nonparallel real lines. Actual even-order clean-line charging and the classical odd/even simple-arrangement upper bounds are proved, yielding actual one-triangle optimality windows for both eleven-seed families. Local fan theorems and conditional aggregate upper-budget arithmetic are distinguished from the remaining whole-arrangement fan extraction, matching, and summation obligations. The unrestricted quantitative one-line successor recurrence remains unproved.',
        native_evaluation='Finite certificate checks use native_decide and trust Lean native evaluation; audit explicitly allows and lists those generated axioms.',
        build_phases=dict(core=core,certificates=certificates,after_certificates=late),
        source_coverage='Every hashed active Lean source belongs to the requested build closure and the final root axiom audit. Complete also requires unchanged active source contents throughout the build.',
        source_changes_during_build=source_changes,
        results=results,source_sha256=initial_sources)
    (ROOT/'verification/lean-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return 0 if summary['complete'] else 1

if __name__=='__main__':raise SystemExit(main())
