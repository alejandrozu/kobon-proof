"""Generate new, original vector figures from the frozen October evidence.

Requires numpy and matplotlib. Geometry is intersected in exact rational
arithmetic before conversion to display coordinates. The 49-line figure is a
rational midpoint illustration, not a replacement for the interval proof.
"""
from pathlib import Path
from fractions import Fraction as F
import csv
import hashlib
import json
import shutil
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DATA = ROOT / 'research/three-hour-2026-10-02'
OUT = HERE / 'long/figures'
BLUE, ORANGE, TEAL = '#235d88', '#c76422', '#287c6a'
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':9,
    'axes.titlesize':10, 'axes.labelsize':9, 'legend.fontsize':8,
    'xtick.labelsize':8, 'ytick.labelsize':8, 'axes.spines.top':False,
    'axes.spines.right':False, 'axes.grid':True, 'grid.alpha':.18,
    'grid.linewidth':.5, 'pdf.fonttype':42, 'ps.fonttype':42,
    'savefig.bbox':'tight', 'mathtext.fontset':'dejavusans'})
manifest = []

def save(fig, name, sources, note, extra):
    OUT.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT / (name+'.pdf'), metadata={'Title':name,
        'Author':'Alejandro Zarzuelo Urdiales', 'CreationDate':None, 'ModDate':None})
    fig.savefig(OUT / (name+'.png'), dpi=170)
    plt.close(fig)
    for ext in ('pdf','png'):
        shutil.copy2(OUT / (name+'.'+ext), HERE / 'journal/figures' / (name+'.'+ext))
    manifest.append({'figure':name, 'note':note, 'details':extra,
        'sources':[{'path':p.relative_to(ROOT).as_posix(),
                    'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sources]})

source = DATA / 'family-comparison.csv'
rows = list(csv.DictReader(source.open(encoding='utf-8')))
assert len(rows)==20
for row in rows:
    for k in row:
        if k not in ('family','parity'): row[k]=int(row[k])
    q = 10*2**row['depth']
    expected=(q*q-4)//3+(q//2 if row['parity']=='even' else 0)
    assert row['constructed']==expected
    n=row['n']
    assert row['baseline']==n*(n-3)//3+1+n%2
    upper=n*(n-2)//3 if n%2 else n*(2*n-5)//6
    assert upper==row['polynomial_benchmark']==expected+1
    assert row['retained_envelope']-row['previous_envelope']==row['release_gain']

fig, axes=plt.subplots(1,2,figsize=(7.3,2.75),layout='constrained')
for parity,color,marker in [('odd',BLUE,'o'),('even',ORANGE,'s')]:
    rr=[r for r in rows if r['parity']==parity]
    depth=[r['depth'] for r in rr]
    axes[0].semilogy(depth,[r['polynomial_benchmark']-r['baseline'] for r in rr],
        marker=marker,color=color,label='Upper bound minus G: '+parity)
    axes[1].plot(depth,[r['release_gain'] for r in rr],marker=marker,color=color,label=parity)
axes[0].axhline(1,color=TEAL,ls='--',label='Upper bound minus family = 1')
axes[0].set(title='Verified family versus all-order baseline',xlabel='Iteration depth t',ylabel='Triangle gap (log scale)')
axes[0].legend(loc='upper left',fontsize=7)
axes[1].set(title='Improvement over previous repository envelope',xlabel='Iteration depth t',ylabel='Gain in certified triangles')
axes[1].legend(loc='upper left')
axes[1].annotate('321 / 322 lines',xy=(5,104),xytext=(2.5,490),fontsize=8,
    arrowprops={'arrowstyle':'->','color':'#666666'})
for ax in axes: ax.set_xticks(range(10))
save(fig,'recursive-envelope',[source],
    'The upper polynomials apply to simple arrangements. Comparison is to the previous verified repository envelope, not a global literature record.',
    {'orders':'q+1 and q+2, q=10*2^t', 'depths':list(range(10)),'rows':rows})

source = DATA / 'constructions/uniform-grid49/uniform-seed.json'
data=json.loads(source.read_text(encoding='utf-8'))
lines=[tuple(map(F,row)) for row in data['lines_frac']]
assert len(lines)==49 and len(data['triangles'])==767
def intersect(i,j):
    a,b,c=lines[i]; d,e,f=lines[j]
    det=a*e-b*d
    assert det
    return ((b*f-c*e)/det,(c*d-a*f)/det)

# A fixed invertible shear reveals the geometry of the nearly parallel seed.
def display(p):
    x,y=p
    return float(x-2*y),float(y)
polys=[]
colors=[]
for i,j,k in data['triangles']:
    polys.append([display(intersect(i,j)),display(intersect(j,k)),display(intersect(k,i))])
    colors.append(ORANGE if (i,j,k)==(0,24,25) else TEAL if 0 in (i,j,k) else BLUE)
vertices=np.array(polys).reshape(-1,2)
lo=vertices.min(axis=0); hi=vertices.max(axis=0)
fig,axes=plt.subplots(1,2,figsize=(7.3,3.5),layout='constrained')
for ax in axes:
    ax.add_collection(PolyCollection(polys,facecolors=colors,edgecolors='#183649',linewidths=.22,alpha=.75))
    ax.axhline(0,color='#222222',lw=.8)
    ax.set(xlabel='Sheared coordinate x − 2y',ylabel='y')
axes[0].set(xlim=(-5,5),ylim=(-6,6),title='Seed geometry: distinguished-line window')
axes[1].set(xlim=(-.6,.6),ylim=(-.6,.6),title='Central window and distinguished support')
axes[1].set_aspect('equal',adjustable='box')
save(fig,'uniform49',[source],
    'Rational midpoint epsilon=1/200; invertible shear x -> x-2y. Blue cells, teal distinguished caps, orange central triangle. Both panels are clipped windows; distant cells are outside the display. Exact external certificate; full Lean seed validity is pending.',
    {'triangles':767,'distinguished_caps':47,'epsilon':'1/200',
     'overall_bounds':[lo.tolist(),hi.tolist()], 'left_window':[-5,5,-6,6], 'center_window':[-.6,.6,-.6,.6]})

(HERE/'new-figure-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print('PASS: exact source identities verified; generated two new vector figures for both manuscripts.')
