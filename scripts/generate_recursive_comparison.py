"""Compare proved recursive families with the pre-session verified envelope.

Use --forge only after the unconditional 33-line seed bridge is Lean checked.
This is a release comparison, not an assertion of numerical first priority.
"""
from pathlib import Path
import argparse
import csv
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'research/three-hour-2026-10-02'


def baseline(n):
    return 0 if n < 3 else 1 if n == 3 else n * (n - 3) // 3 + 1 + n % 2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--forge', action='store_true')
    args = parser.parse_args()
    old = (ROOT / 'Kobon/AllN.lean').read_text(encoding='utf-8')
    section = old.split('def enhancement')[1].split('theorem enhancement_sound')[0]
    finite = {int(n): int(t) for n, t in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)', section)}
    families = [('eleven', 10, 4)]
    if args.forge:
        families.append(('forge', 32, 1))
    rows = []
    for name, base, defect in families:
        for t in range(10):
            q = base * 2 ** t
            odd = (q*q-defect)//3
            for parity, n, count in [('odd',q+1,odd),('even',q+2,odd+q//2)]:
                previous = max(baseline(n),finite.get(n,0))
                benchmark = n*(n-2)//3 if parity=='odd' else n*(2*n-5)//6
                rows.append(dict(family=name,depth=t,parity=parity,n=n,
                    constructed=count,baseline=baseline(n),previous_envelope=previous,
                    retained_envelope=max(previous,count),
                    release_gain=max(0,count-previous),
                    polynomial_benchmark=benchmark,
                    construction_polynomial_gap=benchmark-count))
    OUT.mkdir(parents=True,exist_ok=True)
    with (OUT/'family-comparison.csv').open('w',newline='',encoding='utf-8') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    (OUT/'family-comparison.json').write_text(json.dumps({
        'comparison_release':'8d9f20a6c8afcc0312c5f28f81050cb8fa2595c0',
        'scope':'Constructed counts versus the previous verified repository envelope. '
                'Polynomial benchmarks are arithmetic comparisons; no new upper theorem or priority claim.',
        'forge_unconditional_included':args.forge,'rows':rows},indent=2)+'\n',encoding='utf-8')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(11,4.2),layout='constrained')
    colors={'eleven':'#1c658c','forge':'#b45f06'}
    labels={'eleven':'11-line seed','forge':'33-line seed'}
    for ax,parity in zip(axes,['odd','even']):
        for name,_,_ in families:
            rs=[r for r in rows if r['family']==name and r['parity']==parity]
            ax.plot([r['n'] for r in rs],[r['polynomial_benchmark']-r['baseline'] for r in rs],
                    ':',color=colors[name],label=f'{labels[name]} orders: baseline')
            ax.plot([r['n'] for r in rs],[r['construction_polynomial_gap'] for r in rs],
                    'o-',markersize=4,color=colors[name],label=f'{labels[name]}: recursive family')
        ax.set_xscale('log',base=2);ax.set_yscale('symlog',linthresh=1)
        ax.set_xlabel('Number of lines n')
        ax.set_ylim(bottom=0)
        ax.set_ylabel('Gap to polynomial benchmark (triangles)')
        ax.set_title('Odd orders' if parity=='odd' else 'Even orders (simple benchmark)')
        ax.grid(alpha=.2);ax.legend(fontsize=8)
    fig.savefig(OUT/'recursive-gap-comparison.png',dpi=180)
    plt.close(fig)
    print(f'Wrote {len(rows)} comparison rows and the original arithmetic-gap figure.')


if __name__=='__main__':
    main()
