"""Reproducible comparison; no OEIS or other external edits."""
import json, sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'outputs'/'kobon-extension'))
from verify_direct import verify

baseline=json.loads(Path(__file__).with_name('table_baseline.json').read_text())
fp={r['n']:r['triangles'] for r in baseline}
seeds={3:1,5:5,7:11,9:21,11:32,12:37,13:47,15:65,17:85,
       19:107,21:133,23:161,25:191,27:225,29:261,31:299,33:341,
       35:385,37:431,41:533,43:587,45:645,49:767,57:1045}
oeis={3:(1,1),4:(2,2),5:(5,5),6:(7,7),7:(11,11),8:(15,16),9:(21,21),
      10:(25,25),11:(32,32),12:(38,38),13:(47,47),14:(54,54),15:(65,65),
      16:(72,72),17:(85,85),18:(93,94),19:(107,107),20:(117,117),21:(133,133),
      22:(143,144),23:(161,161),24:(172,173),25:(191,191),26:(204,205),
      27:(225,225),28:(238,239),29:(261,261),30:(275,276),31:(299,299),
      32:(315,316),33:(341,341),34:(357,358),35:(385,385),36:(402,404),
      37:(431,431),38:(450,451),41:(533,533),42:(553,555),43:(587,587),
      45:(645,645),46:(667,669),49:(767,767),50:(792,794)}
def g(n,t):
    a=(n-1)*max(3,3*t-n*(n-3))
    return (a+2*n-1)//(2*n)
simple={}
rows=[]
for n in range(3,61):
    ext=None if n==3 else simple[n-1]+g(n-1,simple[n-1])
    simple[n]=max(fp[n],seeds.get(n,0),ext or 0)
    old,ou=oeis.get(n,(None,None))
    cb=n*(n-2)//3-int(n%6 in (0,2))
    retained=max(old or 0,simple[n],817 if n==51 else 0)
    ub=min(cb,ou) if ou is not None else cb
    assert retained<=ub
    rows.append(dict(n=n,oeis_lower=old,oeis_reported_upper=ou,
        general_upper=cb,display_upper=ub,seed=seeds.get(n),
        furedi_palasti_rational_seed=fp[n],extension_only=ext,
        retained_simple_lower=simple[n],retained_classical_lower=retained,
        improves_existing_oeis=old is not None and retained>old))
    print(f"| {n} | {old if old is not None else '—'} | {retained} | {ub}{'*' if ou is None or ub!=ou else ''} | {ext if ext is not None else 'seed'} |")
assert not any(r['improves_existing_oeis'] for r in rows)
Path(__file__).with_name('bounds_table.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')

# Independent exact counts for every Furedi-Palasti seed selected in a gap.
checked=[]
certdir=Path(__file__).with_name('table-certificates')
certdir.mkdir(exist_ok=True)
for r in baseline:
    n=r['n']
    if n not in oeis and n not in seeds and simple[n]==r['triangles']:
        p=certdir/f'fp-{n}.json'
        p.write_text(json.dumps(dict(n=n,triangle_count=r['triangles'],lines_frac=r['lines'])),encoding='utf-8')
        checked.append(verify(p))
Path(__file__).with_name('table_baseline_verification.json').write_text(json.dumps(checked,indent=2),encoding='utf-8')
