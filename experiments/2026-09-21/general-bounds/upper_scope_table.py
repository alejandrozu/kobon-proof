"""Reproduce a scope-separated upper-bound comparison, without importing it into Lean."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/six-hour-2026-09-21/general-bounds'
OEIS={3:1,4:2,5:5,6:7,7:11,8:16,9:21,10:25,11:32,12:38,
      13:47,14:54,15:65,16:72,17:85,18:94,19:107,20:117,21:133,
      22:144,23:161,24:173,25:191,26:205,27:225,28:239,29:261,
      30:276,31:299,32:316,33:341,34:358,35:385,36:404,37:431,
      38:451,41:533,42:555,43:587,45:645,46:669,49:767,50:794}

def clement_bader(n):
    return n*(n-2)//3-(n%6 in (0,2))

def blanc(n):
    r=n%6
    if r in (0,4):return n*(2*n-5)//6
    if r==1:return (n*(n-2)-2)//3
    if r==2:return (n*(2*n-5)-4)//6
    return n*(n-2)//3

rows=[]
for n in range(3,61):
    cb=clement_bader(n)
    row=dict(n=n,tamura=n*(n-2)//3,classical_clement_bader_reported=cb,
             simple_blanc=blanc(n),simple_bbl_2007=(n*(3*n-7)//9 if n%2==0 else None),
             oeis_reported_upper=OEIS.get(n))
    if n==11:row['separate_classical_exclusion_reported']='Savchuk 2025 excludes33; SAT run not replayed here.'
    if n in (10,12,14,16,20):row['audit_note']='OEIS reports exact value, but the inspected cited simple-arrangement bounds do not establish this unrestricted upper value.'
    rows.append(row)
OUT.mkdir(parents=True,exist_ok=True)
(OUT/'upper-scope-table.json').write_text(json.dumps(dict(
    accessed_utc='2026-09-22',
    note='Source-scope audit of reported external upper statements, not completed proof audits. The Clement--Bader local wording issue is documented separately. No claim this list exhausts all special-case upper proofs.',
    rows=rows),indent=2)+'\n')
text=['# Upper bounds with their hypotheses retained','',
      'This table separates the unrestricted classical envelope reported by Clément–Bader from bounds that require simplicity. It is an audit of cited source statements, not a new upper-bound proof or a complete literature census. The OEIS column is transcribed as displayed on 22 September 2026, including its older 8-line entry.', '',
      '| n | Tamura reported | Classical Clément–Bader reported | Simple Blanc | OEIS reported upper |',
      '|---:|---:|---:|---:|---:|']
for r in rows:
    text.append(f"| {r['n']} | {r['tamura']} | {r['classical_clement_bader_reported']} | {r['simple_blanc']} | {r['oeis_reported_upper'] if r['oeis_reported_upper'] is not None else '—'} |")
text+=['','The 11-line value has the separate Savchuk SAT exclusion described in the scope audit. A smaller OEIS entry does not by itself prove that entry wrong: it signals that a separate unrestricted proof must be located before that upper bound is used here. In particular, the two simple columns cannot certify a nonsimple witness as classically optimal.','']
(OUT/'upper-scope-table.md').write_text('\n'.join(text))
print(f'Wrote {len(rows)} scope-separated rows.')
