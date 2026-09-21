"""Generate simplicity checks, result aliases, an import root, and an axiom audit.

Only reads the certificate index; it does not regenerate coordinate data.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
records = json.loads((ROOT/'verification/certificate-index.json').read_text())
targets = []
for d in records:
    key = d['module'].split('.')[-1]
    if d['simple']:
        module = 'Kobon.SimpleCertificates.'+key
        p = ROOT/(module.replace('.', '/')+'.lean')
        p.parent.mkdir(exist_ok=True)
        p.write_text(f'''import Kobon.Simple
import {d['module']}

namespace {d['module']}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent {d['n']} (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound {d['n']} {d['triangles']} :=
  validate_simple_sound lines triangles {d['triangles']} checked no_concurrent

#print axioms simple_lower_bound
end {d['module']}
''', encoding='utf-8')
        d['simple_theorem'] = d['module']+'.simple_lower_bound'
        d['simple_module'] = module
        targets.append(module)
    else:
        targets.append(d['module'])

body = ''.join('import '+m+'\n' for m in targets)
body += '\nnamespace Kobon.Results\n\n'
table = json.loads((ROOT/'research/finite-table/index.json').read_text())
for row in table:
    n = row['n']
    for kind in ('classical', 'simple'):
        source = f'research/finite-table/{kind}-{n:03d}.json'
        d = next(d for d in records if source in d['sources'])
        T = row[kind+'_lower']
        prop = 'SimpleLowerBound' if kind == 'simple' else 'LowerBound'
        thm = d['simple_theorem'] if kind == 'simple' else d['theorem']
        body += f'theorem {kind}_{n:03d} : {prop} {n} {T} := {thm}\n'

old = json.loads((ROOT/'research/kobon-own-results/inventory.json').read_text())['rows']
for row in old:
    n,T = row['n'],row['lower_bound']
    d = max((d for d in records if d['n']==n),key=lambda d:d['triangles'])
    assert d['triangles']>=T
    body += f'theorem earlier_{n:03d} : LowerBound {n} {T} :=\n  {d["theorem"]}.mono (by decide)\n'
body += '\nend Kobon.Results\n'
(ROOT/'Kobon/Results.lean').write_text(body,encoding='utf-8')

core = ['Kobon.Geometry','Kobon.Simple','Kobon.Euclidean','Kobon.BoundaryExtension',
        'Kobon.RationalExamples','Kobon.Families','Kobon.AffineLemmas']
(ROOT/'Kobon.lean').write_text(''.join('import '+m+'\n' for m in core+['Kobon.Results']),encoding='utf-8')
(ROOT/'verification/certificate-index.json').write_text(json.dumps(records,indent=2)+'\n')
(ROOT/'verification/build-targets.json').write_text(json.dumps(core+targets+['Kobon','Kobon.Audit'],indent=2)+'\n')

audit = '''import Kobon
import Lean.Util.CollectAxioms

/-! Every theorem in the active project is checked for unapproved axioms.
Native evaluation is permitted and reported separately; sorryAx is not. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name info =>
    if name.toString.startsWith "Kobon" && info.isTheorem then names.push name else names
  for name in names do
    let axioms ← Lean.collectAxioms name
    let mut native := false
    for ax in axioms do
      if ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound then
        pure ()
      else if (ax.toString.splitOn "native_decide.ax_").length > 1 then
        native := true
      else
        throwError "Unapproved axiom {ax} in {name}"
    logInfo m!"AUDIT {name}: {if native then "native-evaluation" else "kernel"}; axioms={axioms}"
  logInfo m!"AUDIT_TOTAL {names.size}"
'''
(ROOT/'Kobon/Audit.lean').write_text(audit,encoding='utf-8')
print(f'Prepared {len(records)} certificates and {sum(d["simple"] for d in records)} simplicity checks.')
