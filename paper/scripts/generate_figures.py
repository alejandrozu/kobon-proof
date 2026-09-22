"""Reproduce the paper's vector figures, exact rendering data, and LaTeX tables.

Run from any directory with Python >=3.10, numpy and matplotlib. No network,
image generation, search, proof compilation, or modification of research data.
All geometry is counted in exact rational arithmetic before conversion to float
for rendering. Irrational family illustrations are explicitly rational proxies;
their plots are not the proofs of the corresponding real-family theorems.
"""
from __future__ import annotations
import csv
import hashlib
import itertools
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
FIG = PAPER / 'figures'
GEN = PAPER / 'generated'
for folder in (FIG, GEN):
    folder.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(ROOT / 'research/kobon-hybrid'))
from exact_geometry import arrangement, primitive, intersection

BLUE = '#235d88'
ORANGE = '#c76422'
TEAL = '#287c6a'
GREY = '#62686e'
PURPLE = '#7b5498'
plt.rcParams.update({
    'font.family': 'DejaVu Sans', 'font.size': 9,
    'axes.titlesize': 10, 'axes.labelsize': 9,
    'legend.fontsize': 8, 'xtick.labelsize': 8, 'ytick.labelsize': 8,
    'axes.spines.top': False, 'axes.spines.right': False,
    'axes.grid': True, 'grid.alpha': .17, 'grid.linewidth': .5,
    'lines.linewidth': 1.5, 'savefig.bbox': 'tight',
    'pdf.fonttype': 42, 'ps.fonttype': 42,
    'mathtext.fontset': 'dejavusans',
})

def read(rel):
    return json.loads((ROOT / rel).read_text(encoding='utf-8-sig'))

def sha(rel):
    return hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()

CATALOG = read('verification/certificate-index.json')
OEIS = {d['n']: d['explicit_lower'] for d in read('evidence/oeis-observations.json')['rows']}
UPPER = {d['n']: d for d in read('research/six-hour-2026-09-21/general-bounds/upper-scope-table.json')['rows']}
BEST = {}
for rec in CATALOG:
    n = rec['n']
    row = BEST.setdefault(n, {'classical': 0, 'simple': 0})
    row['classical'] = max(row['classical'], rec['triangles'])
    if rec['simple']:
        row['simple'] = max(row['simple'], rec['triangles'])

def B(n): return (n * max(n-3, 0) + 2)//3
def G(n): return 0 if n < 3 else 1 if n == 3 else n*(n-3)//3 + 1+n%2
def U(n): return n*(n-2)//3
def UBsimple(n): return n*(2*n-5)//6 if n%2 == 0 else U(n)

AUDIT = []
def save(fig, name, sources, caption, status, details=None):
    fig.savefig(FIG / f'{name}.pdf', metadata={
        'Title': name, 'Author': 'Alejandro Zarzuelo Urdiales',
        'Subject': 'Original rendering from documented Kobon research data',
        'CreationDate': None, 'ModDate': None})
    fig.savefig(FIG / f'{name}.png', dpi=160)
    plt.close(fig)
    AUDIT.append(dict(name=name, sources=[dict(path=s, sha256=sha(s)) for s in sources],
                      caption=caption, status=status, details=details or {}))

def plot_bounds():
    ns = np.arange(4, 121)
    fig, ax = plt.subplots(figsize=(7, 4.1), layout='constrained')
    ax.plot(ns, [U(int(n)) for n in ns], color=GREY, ls='--', label=r'$U_T(n)=\lfloor n(n-2)/3\rfloor$ (external benchmark)')
    ax.plot(ns, [B(int(n)) for n in ns], color=BLUE, label=r'$B(n)=\lceil n(n-3)/3\rceil$ (Füredi–Palásti)')
    ax.plot(ns, [G(int(n)) for n in ns], color=ORANGE, lw=1, label=r'$G(n)$ (formal affine refinement)')
    ax.set(xlabel='Number of lines $n$', ylabel='Triangular cells', title='Quadratic growth: the constant refinement is not visible at this scale')
    ax.legend(loc='upper left')
    save(fig, 'bounds-growth', ['Kobon/Universal.lean', 'Kobon/AllN.lean'],
         'The proved affine refinement G and the classical Füredi–Palásti formula B share the same leading and linear terms. The dashed Tamura polynomial is an external comparison bound, not a new upper theorem.', 'General proved lower formulas; attributed external upper benchmark.')

    fig, ax = plt.subplots(figsize=(6.5, 3.2), layout='constrained')
    gains = [1,1,0,2,0,1]
    ax.bar(range(6), gains, color=[ORANGE if v else '#d7dce0' for v in gains], width=.65)
    for i, v in enumerate(gains): ax.text(i, v+.08, str(v), ha='center', fontsize=12)
    ax.set(xticks=range(6), yticks=[0,1,2], ylim=(0,2.6), xlabel='$n$ modulo $6$', ylabel='$G(n)-B(n)$', title=r'Exact gain by residue class, for $n\geq4$')
    save(fig, 'residue-gains', ['Kobon/Universal.lean'],
         'Exact constant gain G(n)-B(n) in the six residue classes, as proved by Universal.baseline_improvement. The small order n=3 is handled separately.', 'General Lean theorem, standard axioms.')

    fig, axs = plt.subplots(1, 2, figsize=(7.4, 3.6), layout='constrained')
    ns = np.arange(4, 241)
    axs[0].plot(ns, [U(int(n))-B(int(n)) for n in ns], color=BLUE, lw=.9, label='$U_T-B$')
    axs[0].plot(ns, [U(int(n))-G(int(n)) for n in ns], color=ORANGE, lw=.9, label='$U_T-G$')
    axs[0].set(xlabel='$n$', ylabel='Absolute triangle gap', title='The remaining gap grows linearly')
    axs[0].legend()
    axs[1].plot(ns, [(G(int(n))-B(int(n)))/int(n)**2 for n in ns], color=ORANGE, lw=.8)
    axs[1].set(xlabel='$n$', ylabel='$(G-B)/n^2$', title='The normalized gain tends to zero')
    axs[1].ticklabel_format(axis='y', style='sci', scilimits=(0,0))
    save(fig, 'normalized-gap', ['Kobon/Universal.lean'],
         'Absolute distance to Tamura\'s polynomial and the improvement normalized by n squared. The refinement changes only constant terms; it neither closes the general linear gap nor changes asymptotic density.', 'Exact arithmetic comparison of proved formulas; no new upper claim.')

    ns = list(range(3,61))
    fig, axs = plt.subplots(2, 1, figsize=(7.3, 5.5), sharex=True, layout='constrained', gridspec_kw={'height_ratios':[2,1]})
    axs[0].plot(ns, [G(n) for n in ns], color=ORANGE, label='General $G(n)$')
    axs[0].plot(ns, [U(n) for n in ns], color=GREY, ls='--', label='Tamura polynomial')
    axs[0].scatter(ns, [BEST[n]['classical'] for n in ns], c=BLUE, s=15, label='Best saved classical certificate', zorder=3)
    ox = [n for n in ns if OEIS.get(n) is not None]
    axs[0].scatter(ox, [OEIS[n] for n in ox], marker='o', s=43, facecolors='none', edgecolors=TEAL, lw=.8, label='Explicit OEIS lower-table snapshot')
    axs[0].set(ylabel='Triangular cells', title='Saved finite envelope versus a formula valid at every order')
    axs[0].legend(loc='upper left', ncol=1)
    axs[1].bar(ns, [BEST[n]['classical']-G(n) for n in ns], color=BLUE, width=.7)
    axs[1].set(xlabel='Number of lines $n$', ylabel='Saved count $-G(n)$', xlim=(2,61))
    save(fig, 'finite-envelope', ['verification/certificate-index.json', 'evidence/oeis-observations.json', 'Kobon/Universal.lean'],
         'Best saved classical coordinate counts for 3–60, with the unconditional formula G and the explicit OEIS lower-table snapshot of 20 September 2026. Missing OEIS markers mean omitted entries, not unknown bounds or numerical novelty. Existing constructions retain their authors\' attribution.', 'Finite Lean certificates and proved formula; dated external table snapshot.')

def affine_float(p): return np.array([float(F(p[0],p[2])), float(F(p[1],p[2]))])

def draw_arrangement(ax, ar, title='', new=None, distinguished=None, viewport=None, radial=False):
    verts = np.array([[affine_float(p) for p in tri] for tri in ar['triangle_vertices']])
    flattened = verts.reshape((-1,2))
    lo, hi = flattened.min(axis=0), flattened.max(axis=0)
    if viewport is not None:
        lo,hi=np.array(viewport[0]),np.array(viewport[1])
    span = np.maximum(hi-lo, 1e-12)
    center = (hi+lo)/2
    scaled = (verts-center)/span
    colors = [ORANGE if new and tuple(t) in new else BLUE for t in ar['triangles']]
    ax.add_collection(PolyCollection(scaled, facecolors=colors, edgecolors='none', alpha=.35))
    # Rendering uses an invertible diagonal affine map. Exact cell enumeration
    # has already happened; the map improves legibility without changing cells.
    for idx, l in enumerate(ar['lines']):
        lf = np.array([float(F(v,max(map(abs,l)))) for v in l])
        aa, bb = lf[0]*span[0], lf[1]*span[1]
        cc = lf[2]-lf[0]*center[0]-lf[1]*center[1]
        candidates=[]
        if bb!=0:
            for x in (-.54,.54):
                y=(cc-aa*x)/bb
                if -.540001<=y<=.540001: candidates.append((x,y))
        if aa!=0:
            for y in (-.54,.54):
                x=(cc-bb*y)/aa
                if -.540001<=x<=.540001: candidates.append((x,y))
        if len(candidates)>=2:
            xy=np.array(candidates[:2])
            ax.plot(xy[:,0],xy[:,1],color=ORANGE if idx==distinguished else '#33424c',lw=1.4 if idx==distinguished else .48,alpha=.9)
    if radial:
        c=np.array([1.,1.])
        points=[np.array([0.,0.]),np.array([3.,0.]),np.array([0.,3.]),np.array([1.5,0.]),np.array([0.,1.5]),np.array([1.5,1.5])]
        for p in points:
            xy=(np.array([c,p])-center)/span
            ax.plot(xy[:,0],xy[:,1],color=ORANGE,lw=2.1)
        p=(c-center)/span
        ax.scatter([p[0]],[p[1]],s=35,color=ORANGE,zorder=5)
        ax.annotate('Triple point $(1,1)$',p,xytext=(.13,.35),fontsize=9,arrowprops={'arrowstyle':'-','lw':.8})
    ax.set(xlim=(-.55,.55),ylim=(-.55,.55),aspect='equal',title=title)
    ax.axis('off')
    return dict(center=center.tolist(), diagonal_scale=span.tolist())

def exact_plot(name, source, title, caption, distinguished=None, radial=False):
    data=read(source); ar=arrangement(data['lines_frac'])
    count=len(ar['triangles'])
    assert count==data['triangle_count'],(source,count,data['triangle_count'])
    if name.startswith('historical-'):
        fig,axs=plt.subplots(1,2,figsize=(7.5,4),layout='constrained',gridspec_kw={'width_ratios':[1,1.5]})
        tr=draw_arrangement(axs[0],ar,'All bounded cells',distinguished=distinguished)
        vp=np.array([affine_float(p) for p in ar['points']])
        bounds=np.quantile(vp,[.12,.88],axis=0)
        zoom=draw_arrangement(axs[1],ar,'Central region (cropped)',distinguished=distinguished,viewport=bounds)
        tr['zoom']=zoom
        fig.suptitle(title,fontsize=11)
        foot='Blue shading uses the exact triangle list; panels have separate affine scales'
    elif name=='seed-21':
        fig,axs=plt.subplots(1,3,figsize=(8.3,3.4),layout='constrained',gridspec_kw={'width_ratios':[.7,1.1,1.1]})
        tr=draw_arrangement(axs[0],ar,'Global scale',distinguished=distinguished)
        tr['macroscopic_zoom']=draw_arrangement(axs[1],ar,'Old seed region (cropped)',distinguished=distinguished,viewport=[[-4,-2],[4,6]])
        tr['pencil_zoom']=draw_arrangement(axs[2],ar,'New pencil region (cropped)',distinguished=distinguished,viewport=[[-4,-3e-10],[4,1e-10]])
        fig.suptitle(title,fontsize=11)
        foot='Three separate affine scales; pencil panel resolves heights of order $10^{-10}$'
    elif name=='seed-11':
        fig,axs=plt.subplots(1,2,figsize=(7.4,4),layout='constrained')
        tr=draw_arrangement(axs[0],ar,'All bounded cells',distinguished=distinguished)
        tr['zoom']=draw_arrangement(axs[1],ar,'Distinguished-line region (cropped)',distinguished=distinguished,viewport=[[-3.5,-2],[3.5,4]])
        fig.suptitle(title,fontsize=11)
        foot='Blue shading uses the exact triangle list; orange is the distinguished line'
    else:
        fig, ax=plt.subplots(figsize=(6.4,5.4),layout='constrained')
        tr=draw_arrangement(ax,ar,title,distinguished=distinguished,radial=radial)
        foot='All counted cells shaded; axes independently rescaled by an affine map'
    fig.text(.5,-.035,foot,ha='center',fontsize=8,color=GREY)
    triangles=[list(t) for t in ar['triangles']]
    (GEN/f'{name}-render-data.json').write_text(json.dumps(dict(source=source,source_sha256=sha(source),n=data['n'],triangle_count=count,triangles=triangles,render_affine_map=tr),indent=2)+'\n')
    save(fig,name,[source],caption,'Exact rational coordinate enumeration; finite certificate or local theorem as captioned.',dict(count=count,render_transform=tr))

def fp_rational(n, phase):
    # 15-decimal rational proposals, re-enumerated exactly. These are explicitly
    # illustrations and are not used to infer the real all-order theorem.
    scale=10**15
    return [primitive([round(scale*math.sin(t)),round(scale*math.cos(t)),round(scale*math.sin(3*t))])
            for t in [(i+phase)*math.pi/n for i in range(n)]]

def direct_triangle_set(lines):
    """Independent exact weak-side test, used for the new rendering proxies."""
    result=set()
    for i,j,k in itertools.combinations(range(len(lines)),3):
        vertices=[intersection(lines[a],lines[b]) for a,b in ((i,j),(i,k),(j,k))]
        if any(p is None for p in vertices):
            continue
        p=vertices[0];a,b,c=lines[k]
        if a*p[0]+b*p[1]-c*p[2]==0:
            continue
        for a,b,c in lines:
            values=[a*x+b*y-c*z for x,y,z in vertices]
            if min(values)<0<max(values):
                break
        else:
            result.add((i,j,k))
    return result

def phase_and_chart():
    fig,axs=plt.subplots(1,2,figsize=(7.4,3.9),layout='constrained')
    data=[]
    for ax,phase,label,expected in zip(axs,[.5,1/6],['$\\alpha=1/2$: 36 cells','$\\alpha=1/6$: 37 cells'],[36,37]):
        lines=fp_rational(12,phase);ar=arrangement(lines)
        assert len(ar['triangles'])==expected
        assert len(ar['points'])==66 and all(len(v)==2 for v in ar['points'].values())
        assert set(ar['triangles'])==direct_triangle_set(ar['lines'])
        draw_arrangement(ax,ar,label)
        data.append(dict(n=12,phase=str(phase),lines_frac=lines,triangle_count=expected,triangles=ar['triangles']))
    (GEN/'phase-family-proxies.json').write_text(json.dumps(data,indent=2)+'\n')
    save(fig,'phase-family',['Kobon/FurediPalasti.lean','Kobon/ShiftedFurediPalasti.lean'],
         'Twelve-line rational renderings of the Füredi–Palásti trigonometric family at phases one half and one sixth. Exact enumeration of these rational proxies gives 36 and 37 cells; the general irrational construction is proved separately in Lean. Independent affine axis rescaling is used in each panel.',
         'Exact finite illustrations of an attributed classical family and its formally proved phase refinement.',dict(proxy_file='paper/generated/phase-family-proxies.json'))

    n=9;lines=fp_rational(n,.5);old=arrangement(lines)
    ps=sorted(old['points'],key=lambda p:F(p[0],p[2]))
    h=(F(ps[1][0],ps[1][2])+F(ps[2][0],ps[2][2]))/2
    shifted=[primitive([h*a-c,h*b,c]) for a,b,c in lines]
    new=arrangement(shifted);extra=set(new['triangles'])-set(old['triangles'])
    assert len(old['triangles'])==18 and len(new['triangles'])==20 and len(extra)==2
    assert set(old['triangles'])<=set(new['triangles'])
    assert set(old['triangles'])==direct_triangle_set(old['lines'])
    assert set(new['triangles'])==direct_triangle_set(new['lines'])
    assert all(len(v)==2 for v in new['points'].values()) and len(new['points'])==36
    fig,axs=plt.subplots(1,2,figsize=(7.4,4),layout='constrained')
    draw_arrangement(axs[0],old,'Original chart: 18 cells')
    draw_arrangement(axs[1],new,'Two-cap chart: 20 cells',new=extra)
    fig.text(.5,.018,'Blue: retained support triples     Orange: two additional bounded cells',ha='center',fontsize=8)
    (GEN/'affine-chart-proxy.json').write_text(json.dumps(dict(n=n,original_lines=lines,chart_h=str(h),transformed_lines=shifted,old_count=18,new_count=20,added_triangles=sorted(extra)),indent=2)+'\n')
    save(fig,'affine-chart',['Kobon/FurediPalastiTwoCaps.lean','Kobon/Projective.lean'],
         'An exactly checked nine-line rational proxy of the two-cap change of affine chart. All eighteen old support triples remain triangular cells and two additional triples become bounded. This realizes G(9)=20, below the independently known optimum 21. Coordinates are rescaled separately in the two panels; this picture is not a metric comparison.',
         'Exact finite illustration; all-order geometric theorem separately formalized.',dict(proxy_file='paper/generated/affine-chart-proxy.json',added_triangles=sorted(extra)))

def diagnostics():
    source='experiments/2026-09-20/successor-49/chain.json'
    states=read(source)['states']
    fig,axs=plt.subplots(1,2,figsize=(7.5,3.6),layout='constrained')
    ns=[s['n'] for s in states]
    axs[0].plot(ns,[s['triangles'] for s in states],'-o',color=BLUE,label='Exact greedy exterior chain')
    axs[0].plot(ns,[(n-1)**2//4+191 for n in ns],'--',color=GREY,label='Proposed full-gain schedule')
    axs[0].set(xlabel='Current number of lines',ylabel='Triangle count',xticks=ns,title='One insertion route from 49:767')
    axs[0].legend(loc='upper left')
    axs[1].plot(ns,[s['maximum_exterior_gain'] for s in states],'-o',color=ORANGE,label='Maximum available exterior gain')
    axs[1].plot(ns,[s['requested_gain'] for s in states],'--',color=GREY,label='Requested next gain')
    axs[1].set(xlabel='Current number of lines',ylabel='Triangles added by the next line',xticks=ns,title='The boundary resource collapses')
    axs[1].legend(loc='lower left')
    save(fig,'successor-49-resource',[source],
         'Exact finite exterior-extension chain from the saved 49:767 seed, with the recorded lexicographic tie break. The available maximal gains fall from 24 to 23 and then 2. Failure of this route does not refute a recurrence for maxima or a method that reconstructs the arrangement.',
         'Exact finite experiment; not a universal obstruction or recurrence proof.')

    ts=list(range(7));qs=[10*2**t for t in ts];odd=[q+1 for q in qs];even=[q+2 for q in qs]
    counts=[(q*q-4)//3 for q in qs]
    fig,axs=plt.subplots(1,2,figsize=(7.5,3.9),layout='constrained')
    axs[0].plot(ts,[U(n)-G(n) for n in odd],color=ORANGE,label='$U_T-G$ at $n=q+1$')
    axs[0].plot(ts,[U(n)-B(n) for n in odd],color=GREY,ls=':',label='$U_T-B$ at $n=q+1$')
    axs[0].plot(ts,[U(n)-c for n,c in zip(odd,counts)],color=BLUE,ls='--',label='Odd manuscript family deficit')
    axs[0].set(yscale='log',xlabel=r'Doubling index $t$; $q=10\,2^t$',ylabel='Distance to $U_T$',title='Sparse odd family versus all-order formulas')
    axs[0].legend()
    ds=[UBsimple(n)-(c+q//2) for n,c,q in zip(even,counts,qs)]
    axs[1].plot(ts,ds,'--',color=TEAL,label='Stronger even target (invariant needed)')
    axs[1].plot(ts,[d+1 for d in ds],':',color=GREY,label='Weaker paper-supported even guarantee')
    axs[1].scatter(ts[:5],ds[:5],s=35,color=TEAL,label='Saved Lean finite witnesses')
    axs[1].scatter([5],[ds[5]],s=50,facecolors='none',edgecolors=TEAL,label='Two independent exact counters')
    axs[1].scatter([6],[ds[6]],marker='x',s=45,color=GREY,label='Second counter unfinished')
    axs[1].set(xlabel='Doubling index $t$; $n=q+2$',ylabel='Distance to even simple polynomial',ylim=(-.1,3.6),yticks=[0,1,2],title='Even companion: verification is not uniform')
    axs[1].legend(loc='upper left',fontsize=7)
    save(fig,'family-deficits',['research/kobon-hybrid/manuscript.md','research/six-hour-2026-09-21/hybrid-family/README.md','experiments/2026-09-21/hybrid-family/larger-members-verification.json'],
         'For q=10·2^t, the manuscript odd family has (q²−4)/3 triangles, one below Tamura\'s polynomial. The paper-supported weaker even guarantee adds q/2−1, leaving simple-polynomial gap two; the stronger target adds q/2 and requires the recorded boundary invariant, leaving gap one. Infinite iteration and the full invariant are not end-to-end Lean theorems. Filled even markers are saved finite Lean certificates through 162; 322 passed two exact counters; 642 lacks its second completed check. The BBL doubling method retains Bartholdi–Blanc–Loisel attribution.',
         'General formula comparison with explicit published-theorem/manuscript dependencies; finite verification levels separated.')

    ressource='research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json'
    rows=read(ressource);ns=[r['n'] for r in rows]
    fig,axs=plt.subplots(1,2,figsize=(7.7,3.9),layout='constrained')
    xs=np.arange(len(ns));width=.36
    axs[0].bar(xs-width/2,[r['source_T']-UBsimple(r['n']) for r in rows],width,color=BLUE,label='Published nonsimple witness')
    axs[0].bar(xs+width/2,[r['maximum']-UBsimple(r['n']) for r in rows],width,color=ORANGE,label='Best tested local simple resolution')
    axs[0].axhline(0,color=GREY,lw=.8)
    axs[0].set(xticks=xs,xticklabels=ns,xlabel='$n$',ylabel='Count minus Blanc even simple bound',title='Current gallery inputs retain external attribution')
    axs[0].legend(loc='lower left')
    ms='research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json';md=read(ms)
    vals=[r['triangles'] for r in md['resolutions']]
    axs[1].bar(range(4),vals,color=ORANGE,width=.65)
    axs[1].axhline(54,color=BLUE,label='Maiorana original: 54')
    axs[1].set(xticks=range(4),xticklabels=['− −','− +','+ −','+ +'],ylim=(50,54.6),xlabel='Two local resolution signs',ylabel='Triangular cells',title='A 14-line smoothing counterexample')
    for i,v in enumerate(vals):axs[1].text(i,v+.08,str(v),ha='center')
    axs[1].legend(loc='lower left')
    save(fig,'external-comparison',[ressource,ms,'research/six-hour-2026-09-21/general-bounds/upper-scope-table.json'],
         'Exact local-resolution checks of published nonsimple inputs. Left: Parpalak–Utkin gallery coordinates (the eight-line value has older discovery priority), compared with their best local simple resolutions and the simple-arrangement upper polynomial. Right: all four local resolutions of Andrea Maiorana\'s two-triple-point 14:54 example give 52,52,53,52. Neither a nondecreasing smoothing rule nor a loss-at-most-one rule holds for all these examples. This does not provide classical upper bounds.',
         'Independent exact finite computations on attributed external constructions.')

    names=['One-line local proposals (earlier)','Vertex-chord insertions (earlier)','Offset chambers: n=39','Joint chambers: n=39','Joint chambers: n=40','Joint chambers: n=48','Projective beam edges: n=39','Paired singular collapses: n=44']
    vals=[5867928,1274096,21488140,9712359,24634918,24427315,2122270,35352]
    fig,ax=plt.subplots(figsize=(7.7,4.2),layout='constrained')
    y=np.arange(len(vals));ax.barh(y,vals,color=BLUE,height=.65)
    for yy,v in zip(y,vals):ax.text(v*1.1,yy,f'{v:,}',va='center',fontsize=8)
    ax.set(yticks=y,yticklabels=names,xscale='log',xlim=(1e4,1.8e8),xlabel='Recorded proposals / chambers / candidate edges (log scale)',title='Negative searches: effort counts are not comparable coverage measures')
    ax.invert_yaxis()
    save(fig,'negative-searches',['research/six-hour-2026-09-21/RESEARCH_REVIEW.md','research/six-hour-2026-09-21/construction-search/README.md'],
         'Recorded sizes of selected unsuccessful searches. The units differ across methods; these bars measure recorded search effort, not exhaustive coverage or comparative algorithm quality. Floating search stages and exact finite verification are separate. No bar constitutes an upper bound or impossibility theorem.',
         'Bounded experimental outcomes; heterogeneous units explicitly distinguished.',dict(labels=names,counts=vals))

def esc(s):
    return str(s).replace('\\', '/').replace('&',r'\&').replace('%',r'\%').replace('_',r'\_').replace('#',r'\#')

def longtable(path, spec, header, rows, caption, label, intro=''):
    sep = 6 if path == 'finite-best-3-60.tex' else 4
    text=intro+'\n\\begingroup\n\\small\n'+f'\\setlength{{\\tabcolsep}}{{{sep}pt}}\n'
    text+=f'\\begin{{longtable}}{{{spec}}}\n\\caption{{{caption}}}\\label{{{label}}}\\\\\n\\toprule\n{header}\\\\\n\\midrule\n\\endfirsthead\n'
    text+=f'\\multicolumn{{{len(header.split(" & "))}}}{{l}}{{\\small\\itshape Continued from previous page}}\\\\\n\\toprule\n{header}\\\\\n\\midrule\n\\endhead\n\\midrule\n\\endfoot\n\\bottomrule\n\\endlastfoot\n'
    text+='\n'.join(' & '.join(map(str,row))+r' \\' for row in rows)
    text+='\n\\end{longtable}\n\\endgroup\n'
    (GEN/path).write_text(text,encoding='utf-8')

def source_code(paths):
    mapping=[('maiorana14','MA'),('parpalak-utkin-current','PU'),('six-hour-2026-09-21/certificates','SC'),('finite-table','FT'),('kobon-extension','EX'),('kobon-own-results','HI'),('kobon-hybrid','HY'),('kobon-research','KR')]
    codes=[]
    for p in paths:
        for token,c in mapping:
            if token in p:
                if c not in codes:codes.append(c)
                break
    return ','.join(codes) or 'OT'

def tables():
    rows=[]
    for n in range(3,61):
        up=UPPER[n]
        rows.append([n,G(n),BEST[n]['simple'],BEST[n]['classical'],OEIS.get(n) if OEIS.get(n) is not None else '--',up['simple_blanc'],up['tamura']])
    longtable('finite-best-3-60.tex','rrrrrrr',r'$n$ & $G(n)$ & Saved simple & Saved classical & OEIS lower & Blanc simple & $U_T$',rows,
              'Saved finite lower bounds, separated by arrangement class, and attributed comparison upper values. OEIS is the explicit table snapshot of 20 September 2026; a dash means omitted. The upper columns are external results, not upper theorems proved by this project.','exp:finite-table')
    with (GEN/'finite-best-3-60.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.writer(f);w.writerow(['n','G','saved_simple','saved_classical','explicit_OEIS_lower','Blanc_simple','Tamura']);w.writerows(rows)

    rows=[];manifest=[]
    for i,rec in enumerate(CATALOG,1):
        paths=rec['sources']; code=source_code(paths)
        rows.append([i,rec['n'],rec['triangles'],'S' if rec['simple'] else 'M',code,r'\texttt{'+rec['coordinate_sha256'][:12]+'}'])
        metadata_keys=('source','construction','priority_status','attribution','author','authors','license','upstream_commit','upstream_url','method','notes')
        metadata={p:{k:v for k,v in read(p).items() if k in metadata_keys} for p in paths}
        manifest.append(dict(id=i,n=rec['n'],triangles=rec['triangles'],simple=rec['simple'],source_codes=code,sources=paths,coordinate_sha256=rec['coordinate_sha256'],module=rec['module'],source_file_sha256={p:sha(p) for p in paths},source_metadata=metadata))
    intro=r'''\noindent The catalog contains '''+str(len(CATALOG))+r''' distinct promoted coordinate identities, not '''+str(len(CATALOG))+r''' new numerical records. S denotes a simple arrangement; M denotes a verified arrangement with multiple intersections. Every row has a classical lower-bound theorem; S rows also have simplicity certificates. The hash is a prefix of the canonical coordinate SHA-256 identity, not of the source file. Full source paths, source-file hashes, theorem modules, and complete identities are supplied in \texttt{paper/generated/certificate-catalog.json}.

\noindent Source codes identify repository collections, not discovery authors: FT, retained finite table (mixed published and derived sources); EX, exact extension; HI, historical work inventory; HY, compatible-seed/hybrid work; SC, current session (phase/chart or classical dyadic construction, distinguished in the JSON metadata); MA, Andrea Maiorana's external certificates; PU, Parpalak--Utkin gallery inputs; KR, earlier research collection; OT, other documented source. Published constructions retain their original attribution. Native-evaluation trust boundaries are discussed in the text.
'''
    longtable('certificate-catalog.tex','rrrrll',r'ID & $n$ & $T$ & Class & Collections & Coordinate identity',rows,
              'Complete promoted coordinate catalog. Repeated orders and counts can have distinct coordinate witnesses; no numerical priority follows from inclusion.','exp:catalog',intro)
    (GEN/'certificate-catalog.json').write_text(json.dumps(manifest,indent=2)+'\n')
    inv=read('research/kobon-own-results/inventory.json')['rows'];out=[]
    for r in inv:
        n=r['n'];kind=r['kind'].replace('G','E')
        out.append([n,r['lower_bound'],kind,G(n),BEST.get(n,{}).get('classical','--')])
    intro=r'''\noindent This is a historical numerical inventory, not a list of original discoveries. B means an elementary base case; C means an explicit coordinate construction in that inventory; E means the then-evaluated defect-extension consequence (called G in the historical file, renamed here to avoid confusion with the present function $G$). The numerical inequalities are now retained independently by the compiled \texttt{Results.earlier\_NNN} aliases. This does not formalize all premises of the former general defect argument or establish priority. The right columns display current, separately proved bounds.
'''
    longtable('historical-inventory.tex','rrcrr',r'$n$ & Earlier output & Historical basis & Current $G(n)$ & Best saved classical',out,
              'Earlier work inventory compared with the present unconditional formula and saved certificate envelope.','exp:historical',intro)

def audit():
    manifest=dict(generator='paper/scripts/generate_figures.py',figure_count=len(AUDIT),certificate_count=len(CATALOG),matplotlib_version=matplotlib.__version__,numpy_version=np.__version__,figures=AUDIT)
    (GEN/'figure-manifest.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    txt='# Figure provenance and claim audit\n\nAll PDFs are original vector renderings generated by `paper/scripts/generate_figures.py`. No borrowed figure or generative image is used. Each PDF has a PNG preview. Run with Python, NumPy and Matplotlib; source files are read-only. Geometric triangle sets are recomputed with exact rational adjacency before rendering. Converting coordinates to floating point occurs only after the exact combinatorics is fixed. SHA-256 source hashes and triangle-rendering data are in `paper/generated/`.\n\n'
    txt+='The manuscript author is Alejandro Zarzuelo Urdiales. Authorship of this rendering does not transfer mathematical discovery attribution from Füredi–Palásti, Bartholdi–Blanc–Loisel, Maiorana, Parpalak–Utkin, Tamura, Blanc, or the earlier sources retained in the catalog.\n\n'
    for f in AUDIT:
        txt+=f"## {f['name']}.pdf\n\n**Claim status:** {f['status']}\n\n**Caption:** {f['caption']}\n\n**Inputs:**\n\n"
        for s in f['sources']:txt+=f"- `{s['path']}` — SHA-256 `{s['sha256']}`\n"
        txt+='\n'
    txt+='## Tables\n\n- `finite-best-3-60.tex` / `.csv`: catalog maxima separated into simple and classical; dated OEIS snapshot; upper-scope table with its external attribution.\n- `certificate-catalog.tex` / `.json`: every promoted coordinate identity, collection codes, source paths, hashes, and theorem modules. Collection codes are not discovery attributions.\n- `historical-inventory.tex`: every row in the old own-results inventory, its historical evidence label, and comparison to current independently certified bounds.\n\n## Rendering checks\n\nAll figure PDFs are vector outputs (lines, polygons, text). Phase and chart illustrations use exported rational proxies and exact count assertions; they do not replace the all-order real proof. Arrangement panels use documented invertible diagonal affine rescaling, and therefore do not purport to preserve lengths, angles, or cross-panel metric scale. Search bars carry heterogeneous units and cannot justify nonexistence.\n'
    (PAPER/'figure_audit.md').write_text(txt,encoding='utf-8')

def main():
    plot_bounds()
    for n,t in [(28,238),(30,275),(34,357)]:
        exact_plot(f'historical-{n}',f'research/finite-table/classical-{n:03d}.json',f'{n} lines; {t} certified triangular cells',
                   f'Exact saved simple witness for {n}:{t}, independently certifying a lower value attributed to Alejandro Zarzuelo Urdiales in OEIS. The current witness is an exterior extension of a retained published odd-order input; it is not asserted to reproduce the precise March drawing. All {t} cells are shaded. Historical source attribution is preserved in the coordinate provenance.')
    phase_and_chart()
    diagnostics()
    exact_plot('shared-fan','research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json','A triangle and its three medians',
               'Six exact triangular cells formed by a triangle and its three medians. The central triple point is incident to six shared radial segments, highlighted in orange. This refutes a literal local count of at most two incident shared-side pairs, not the final Clément–Bader upper theorem. The local geometry is separately formalized in SharedFan.',radial=True)
    exact_plot('seed-11','research/kobon-hybrid/seed-11-rational.json','Compatible eleven-line seed: 32 cells',
               'Exact rational reference of the tangent-grid-compatible eleven-line seed. The orange line is the distinguished horizontal support. The known count 32 is not a numerical discovery claim; SeedFamily proves compatibility for a true trigonometric parameter family. BBL supplies the classical doubling framework.',distinguished=0)
    exact_plot('seed-21','experiments/2026-09-21/hybrid-family/seed21-reference.json','Compatible twenty-one-line reference: 132 cells',
               'Exact rational reference used in the verified twenty-one-line tangent-grid family. Its 132 cells are one below the separately retained 21:133 construction. The distinguished horizontal line is orange. Axis rescaling makes the very small pencil scale visible; it does not change incidence.',distinguished=0)
    tables();audit()
    print(json.dumps(dict(figures=len(AUDIT),catalog_records=len(CATALOG),outputs=str(PAPER)),indent=2))

if __name__=='__main__':main()
