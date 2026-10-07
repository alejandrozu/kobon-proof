"""Exact formula data and a scientific plot for the verified61-line orbit.
Requires matplotlib. The upper curves concern simple arrangements only.
"""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/openmath-seven-hour-2026-10-05/figures'
OUT.mkdir(parents=True, exist_ok=True)
rows = []
for t in range(9):
    q = 60*2**t
    odd_n, even_n = q+1, q+2
    odd, even = 1200*4**t-10, 1200*4**t+30*2**t-11
    baseline = lambda n: n*(n-3)//3+1+n%2
    odd_u, even_u = odd_n*(odd_n-2)//3, even_n*(2*even_n-5)//6
    assert odd_u-odd == 9 and even_u-even == 10
    rows.append(dict(t=t, q=q, odd_n=odd_n, even_n=even_n,
                     odd_lower=odd, even_lower=even,
                     odd_baseline=baseline(odd_n), even_baseline=baseline(even_n),
                     odd_simple_upper=odd_u, even_simple_upper=even_u,
                     odd_family_gap=9, even_family_gap=10,
                     odd_baseline_gap=odd_u-baseline(odd_n),
                     even_baseline_gap=even_u-baseline(even_n)))
(OUT/'family61-formula-data.json').write_text(json.dumps(rows, indent=2)+'\n')
plt.rcParams.update({'font.size': 10, 'svg.fonttype': 'none'})
fig, axes = plt.subplots(1, 2, figsize=(9.2, 3.8), sharey=True, constrained_layout=True)
for ax, parity, color in zip(axes, ('odd', 'even'), ('#2563a8', '#b54c28')):
    ts = [r['t'] for r in rows]
    ax.semilogy(ts, [r[parity+'_baseline_gap'] for r in rows], 'o--',
                color='#777777', label='Quadratic baseline G')
    ax.semilogy(ts, [r[parity+'_family_gap'] for r in rows], 's-',
                color=color, label='Family from 61 lines')
    ax.set_title(('Odd: n = 60·2ᵗ + 1' if parity == 'odd' else 'Even: n = 60·2ᵗ + 2'))
    ax.set_xlabel('Iteration depth t')
    ax.set_xticks(ts)
    ax.grid(True, which='both', alpha=0.22)
    ax.legend(loc='upper left', fontsize=8)
axes[0].set_ylabel('Simple upper bound − certified lower bound')
fig.savefig(OUT/'family61-simple-gap.svg')
fig.savefig(OUT/'family61-simple-gap.png', dpi=180)
plt.close(fig)
print(OUT)
