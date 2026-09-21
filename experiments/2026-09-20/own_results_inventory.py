"""Inventory of outputs from our extensions; excludes unchanged literature seeds."""
import json, shutil, hashlib
from pathlib import Path

root=Path(__file__).resolve().parents[2]
rows=json.loads((root/'work/kobon/bounds_table.json').read_text())
dest=root/'outputs/kobon-own-results'
(dest/'certificates').mkdir(parents=True,exist_ok=True)

# These are generated outputs, not the downloaded record certificates or the
# unchanged Furedi-Palasti comparison seeds. Published inputs retain attribution.
specials={
 5:('outputs/kobon-extension/certificates/chain_5.json','Base example'),
 6:('outputs/kobon-extension/certificates/chain_6.json','Exact extension'),
 7:('outputs/kobon-extension/certificates/chain_7.json','Exact extension'),
 9:('work/kobon/fixed-cap-9.json','Additional line on Parpalak-Utkin family'),
 15:('work/kobon/fixed-cap-15.json','Additional line on Parpalak-Utkin family'),
 20:('outputs/kobon-extension/certificates/chain_20.json','Extension of Parpalak-Utkin 19-line input'),
 21:('work/kobon/far-21.json','Additional line on published 20-line input'),
 27:('work/kobon/far-27.json','Additional line on published 26-line input'),
 33:('work/kobon/far-33.json','Additional line on published 32-line input'),
 39:('work/kobon/far-39.json','Additional line on published 38-line input'),
 48:('work/kobon/deletion-50-2.json','Two deletions from published 50-line input'),
 51:('outputs/kobon-research/certificates/n051.json','Additional line on Parpalak-Utkin family'),
 99:('outputs/kobon-research/certificates/n099.json','Additional line on Parpalak-Utkin family'),
 195:('outputs/kobon-research/certificates/n195.json','Additional line on Parpalak-Utkin family'),
}
inventory=[]
for r in rows:
    n=r['n']
    entry=dict(n=n,lower_bound=r['extension_only'],kind='G',
        basis='Defect extension theorem',general_rule_output=r['extension_only'])
    if n==3:
        entry.update(lower_bound=1,kind='B',basis='Three-line base case')
    else:
        prev=next(q for q in rows if q['n']==n-1)
        entry['simple_input_n']=n-1
        entry['simple_input_bound']=prev['retained_simple_lower']
        entry['input_note']='Prior constructions or previously derived simple outputs; input is not claimed as original.'
    inventory.append(entry)
for n,(rel,basis) in specials.items():
    p=root/rel
    data=json.loads(p.read_text())
    count=data.get('triangle_count',data.get('triangles'))
    assert isinstance(count,int),(n,p,list(data))
    entry=next((x for x in inventory if x['n']==n),None)
    if entry is None:
        entry=dict(n=n,lower_bound=count,general_rule_output=None)
        inventory.append(entry)
    if count>=entry['lower_bound']:
        target=dest/'certificates'/f'n{n:03d}.json'
        shutil.copyfile(p,target)
        entry.update(lower_bound=count,kind='B/C' if n==5 else 'C',basis=basis,
                     certificate=str(target.relative_to(dest)),
                     source_file=rel,sha256=hashlib.sha256(target.read_bytes()).hexdigest())
inventory.sort(key=lambda x:x['n'])
out=dict(scope='Strongest outputs explicitly derived or constructed in this work for n=3..60, plus larger exact certificates. Not a priority or record claim.',
    exclusions=['Unchanged published record certificates','Unchanged Furedi-Palasti reproduction seeds','Unproved full-gain recurrence'],
    rows=inventory)
(dest/'inventory.json').write_text(json.dumps(out,indent=2),encoding='utf-8')

lines=['# Strongest outputs of our Kobon work',
 '', '20 September 2026. The range is 3–60, followed by the larger exact certificates.',
 '', 'These are outputs of our extension rule or our explicit construction steps. Published arrangements used as inputs retain their original attribution. Unchanged literature records and comparison-seed reproductions are excluded. This is not a claim that the numerical bounds are new records or were first discovered here.',
 '', '**G:** numerical consequence of the geometric defect theorem, using an available simple input. **C:** explicit exact certificate. **B:** elementary base example.',
 '', '| n | Strongest output: K(n) at least | Evidence |', '|---:|---:|:---|']
for r in inventory:
    lines.append(f"| {r['n']} | {r['lower_bound']} | {r['kind']} |")
lines.extend(['', 'The 39-line certificate gives 469, correcting the 468 retained in the earlier comparison. The stronger special outputs at 7, 9, 15, 21, 27, 33, 39, 48, and 51 lines were not all represented by the general-rule E column.',
 '', 'The explicit outputs at 9, 15, 21, 27, 33, 39, 48, 51, 99, and 195 lines permit triple intersections. They are classical Kobon bounds and cannot be fed into the simple-arrangement defect formula without a separate simplicity check.',
 '', 'The earlier infinite-family argument gives K(q+3) >= q^2/3 + q + 1 for q=6*2^t, t>=0, by adding a line to the Parpalak–Utkin even family. The proof argument is in ../kobon-research/proof_note.md; its finite members at 51, 99, and 195 are exact certificates.',
 '', 'The simple even corollaries and general extension theorem are in ../kobon-extension/manuscript.md. In particular, for q=6*2^t or q=18*2^t, the bound at q+2 is q^2/3 + q/2 - 1. The perfect BBL q=14*2^t family gives (q^2-1)/3 + q/2 at q+2. These are deductions from attributed input families; novelty is not established.',
 '', 'The general geometry is proved in ordinary mathematics in the manuscript; its Lean verification covers the finite counting core, not end-to-end Euclidean formalization.',
 '', 'The per-row input counts, certificate locations, and hashes are in inventory.json.'])
(dest/'results.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
for r in inventory:
 print(f"| {r['n']} | {r['lower_bound']} | {r['kind']} |")
