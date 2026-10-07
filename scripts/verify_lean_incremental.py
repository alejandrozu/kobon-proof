"""Verify an extension of a complete, hash-pinned Lean release.

Unchanged sources whose entire local import closure is unchanged reuse the
named baseline verification. Every other active module is compiled directly,
in dependency order, and the final whole-project axiom audit is rerun. This
does not claim a clean rebuild of the reused baseline. The regular
verify_lean.py remains the clean Lake-build verifier used by CI.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
from pathlib import Path
import argparse, ctypes, hashlib, json, os, re, shutil, subprocess, time
from verify_lean import ROOT, module_path, source_tokens, local_import_dependencies, unbuilt_active_sources


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class CompilerGate:
    """Share the research session's two Windows compiler gates."""
    def __init__(self, slot):
        self.handle = None
        if os.name == 'nt':
            k = ctypes.WinDLL('kernel32', use_last_error=True)
            k.CreateMutexW.argtypes = (ctypes.c_void_p, ctypes.c_bool, ctypes.c_wchar_p)
            k.CreateMutexW.restype = ctypes.c_void_p
            k.WaitForSingleObject.argtypes = (ctypes.c_void_p, ctypes.c_uint32)
            k.WaitForSingleObject.restype = ctypes.c_uint32
            k.ReleaseMutex.argtypes = (ctypes.c_void_p,)
            k.CloseHandle.argtypes = (ctypes.c_void_p,)
            suffix = 'Ordinary' if slot == 0 else 'Outside'
            self.k = k
            self.handle = k.CreateMutexW(None, False, 'Local\\KobonOpenMath'+suffix+'Compiler20261005')
            if not self.handle:
                raise ctypes.WinError(ctypes.get_last_error())

    def __enter__(self):
        if self.handle:
            result = self.k.WaitForSingleObject(self.handle, 0xffffffff)
            if result not in (0, 0x80):
                raise RuntimeError(f'Compiler gate failed: {result}')
        return self

    def __exit__(self, *unused):
        if self.handle:
            self.k.ReleaseMutex(self.handle)
            self.k.CloseHandle(self.handle)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline', required=True)
    p.add_argument('--summary', default='verification/openmath-incremental-summary.json')
    p.add_argument('--lean', default=shutil.which('lean'))
    p.add_argument('--lean-path')
    p.add_argument('--jobs', type=int, choices=(1, 2), default=2)
    args = p.parse_args()
    assert args.lean, 'Pass the pinned Lean executable with --lean.'
    if args.baseline.startswith('git:'):
        ref = args.baseline[4:]
        assert re.fullmatch(r'[0-9a-f]{40}', ref), 'Use an exact baseline commit SHA.'
        raw = subprocess.check_output(['git', 'show', ref+':verification/lean-summary.json'], cwd=ROOT)
    else:
        raw = (ROOT/args.baseline).read_bytes()
    baseline = json.loads(raw)
    assert baseline['complete'], 'The reused baseline must be complete.'
    baseline_hash = hashlib.sha256(raw).hexdigest()
    summary_path = ROOT/args.summary
    prior = json.loads(summary_path.read_text(encoding='utf-8')) if summary_path.exists() else {}
    prior_results = {r['target']: r for r in prior.get('results', []) if r.get('passed')}
    active = [ROOT/'Kobon.lean', *sorted((ROOT/'Kobon').rglob('*.lean'))]
    hashes = {x.relative_to(ROOT).as_posix(): digest(x) for x in active}
    for x in active:
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source_tokens(x.read_text(encoding='utf-8'))), x
    modules = ['.'.join(x.relative_to(ROOT).with_suffix('').parts) for x in active]
    deps = local_import_dependencies(modules)
    targets = json.loads((ROOT/'verification/build-targets.json').read_text(encoding='utf-8'))
    assert not unbuilt_active_sources(active, targets, deps), 'An active source is outside the build closure.'
    audited = deps['Kobon']|{'Kobon', 'Kobon.Audit'}
    assert set(modules) <= audited, 'An active source is outside the root axiom audit.'
    baseline_sources = baseline['source_sha256']
    old_same = {m for m in modules if hashes[module_path(m).relative_to(ROOT).as_posix()] ==
                baseline_sources.get(module_path(m).relative_to(ROOT).as_posix())}
    out_root = ROOT/'.lake/build/lib/lean'
    logs = ROOT/'verification/build-logs/openmath-seven-hour-2026-10-05'
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['LEAN_NUM_THREADS'] = '1'
    if args.lean_path:
        env['LEAN_PATH'] = args.lean_path
    elif os.name == 'nt' and not env.get('LEAN_PATH'):
        trace = json.loads((out_root/'Kobon/BBLSeed49Data.trace').read_text(encoding='utf-8'))
        match = re.match(r'^\.> LEAN_PATH=(.*?) c:\\Users', trace['log'][0]['message'], re.I)
        assert match, 'Cannot recover the cached Lean import path; pass --lean-path.'
        env['LEAN_PATH'] = match.group(1)

    def fingerprint(m):
        data = sorted((d, hashes[module_path(d).relative_to(ROOT).as_posix()]) for d in deps[m]|{m})
        return hashlib.sha256(json.dumps(data).encode()).hexdigest()

    def output_path(m):
        return out_root/(m.replace('.', '/')+'.olean')

    results = {}
    for m in modules:
        fp = fingerprint(m)
        if m in old_same and deps[m] <= old_same and m not in ('Kobon', 'Kobon.Audit') and output_path(m).exists():
            results[m] = dict(target=m, passed=True, mode='baseline-reuse', baseline=args.baseline,
                              fingerprint=fp, source_sha256=hashes[module_path(m).relative_to(ROOT).as_posix()])
        elif prior_results.get(m, {}).get('fingerprint') == fp and output_path(m).exists() and m not in ('Kobon', 'Kobon.Audit'):
            results[m] = prior_results[m]

    def save(complete=False):
        data = dict(checked_at_utc=datetime.now(timezone.utc).isoformat(), complete=complete,
                    mode='incremental-hash-pinned-baseline-plus-direct-compilation',
                    baseline=args.baseline, baseline_sha256=baseline_hash,
                    lean_toolchain=(ROOT/'lean-toolchain').read_text().strip(),
                    scope='Every active source is covered by the build closure and root axiom audit. '
                          'Unchanged baseline source/import closures are reused; all remaining active sources are compiled. '
                          'The complete whole-project axiom audit is compiled again. This is not a clean baseline rebuild.',
                    native_evaluation='Finite native_decide certificate roots are explicitly separated by the root axiom audit.',
                    results=[results[m] for m in sorted(results)], source_sha256=hashes)
        summary_path.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')

    def build(m, slot):
        start = time.monotonic()
        out = output_path(m)
        out.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(m+'.log')
        with CompilerGate(slot), log.open('w', encoding='utf-8') as f:
            run = subprocess.run([args.lean, module_path(m).relative_to(ROOT).as_posix(), '-o', str(out)],
                                 cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT)
        content = log.read_text(encoding='utf-8', errors='replace')
        unchanged = all(digest(module_path(d)) == hashes[module_path(d).relative_to(ROOT).as_posix()]
                        for d in deps[m]|{m})
        passed = run.returncode == 0 and 'sorryAx' not in content and unchanged
        r = dict(target=m, passed=passed, mode='fresh-direct-compile', returncode=run.returncode,
                 seconds=round(time.monotonic()-start, 3), log=log.relative_to(ROOT).as_posix(),
                 fingerprint=fingerprint(m), source_sha256=hashes[module_path(m).relative_to(ROOT).as_posix()],
                 source_and_import_closure_unchanged_during_compile=unchanged)
        print(('PASS' if passed else 'FAIL'), m, r['seconds'], flush=True)
        return r

    pending = set(modules)-results.keys()
    running = {}
    slots = list(range(args.jobs))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            failed = {m for m, r in results.items() if not r['passed']}
            ready = sorted(m for m in pending if not (deps[m] & (pending|{v[0] for v in running.values()}|failed)))
            while slots and ready:
                m = ready.pop(0)
                slot = slots.pop(0)
                pending.remove(m)
                running[pool.submit(build, m, slot)] = (m, slot)
            if not running:
                if pending:
                    print('BLOCKED by failed imports:', ', '.join(sorted(pending)), flush=True)
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                m, slot = running.pop(future)
                results[m] = future.result()
                slots.append(slot)
                save()
    final_active = [ROOT/'Kobon.lean', *sorted((ROOT/'Kobon').rglob('*.lean'))]
    final = {x.relative_to(ROOT).as_posix(): digest(x) for x in final_active}
    complete = len(results) == len(modules) and all(r['passed'] for r in results.values()) and hashes == final
    save(complete)
    print('COMPLETE' if complete else 'INCOMPLETE', f'{len(results)}/{len(modules)} modules', flush=True)
    return 0 if complete else 1


if __name__ == '__main__':
    raise SystemExit(main())
