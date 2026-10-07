"""Reproduce original October 7 scientific figures from exact proved formulas.

The portfolio panel evaluates the literal definitions in AllN, Universal,
RecursiveEnvelope and OpenMathConstructionEnvelope; it is not a SOTA table.
The coefficient panel compares two proved inequalities from the October run.
"""
from pathlib import Path
import hashlib,json,re,shutil
import sys
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
    'axes.titlesize':10,'legend.fontsize':8,'pdf.fonttype':42,
    'savefig.bbox':'tight','axes.spines.top':False,'axes.spines.right':False})
BLUE,ORANGE,TEAL='#235d88','#c76422','#287c6a'
manifest=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(fig,name,data,sources,note):
    out=HERE/'long/figures';out.mkdir(parents=True,exist_ok=True)
    for ext in ('pdf','png'):
        p=out/(name+'.'+ext)
        kwargs={'metadata':{'Author':'Alejandro Zarzuelo Urdiales','CreationDate':None,'ModDate':None}} if ext=='pdf' else {'dpi':180}
        fig.savefig(p,**kwargs)
        q=HERE/'journal/figures'/p.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
    plt.close(fig)
    record={'name':name,'note':note,'data':data,
        'source_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in sources},
        'pdf_sha256':sha(out/(name+'.pdf')),'png_sha256':sha(out/(name+'.png'))}
    manifest.append(record)

rows=[]
for t in range(9):
    q=60*2**t
    for parity,n,T in [('odd',q+1,1200*4**t-10),('even',q+2,1200*4**t+30*2**t-11)]:
        G=n*(n-3)//3+1+n%2
        upper=n*(n-2)//3 if n%2 else n*(2*n-5)//6
        gap=upper-T;assert gap==(9 if parity=='odd' else 10)
        rows.append(dict(t=t,n=n,parity=parity,family=T,baseline=G,simple_upper=upper,gap=gap))
fig,axes=plt.subplots(1,2,figsize=(7.4,2.7),layout='constrained')
for parity,color,mark in [('odd',BLUE,'o'),('even',ORANGE,'s')]:
    rr=[r for r in rows if r['parity']==parity]
    axes[0].semilogy([r['t'] for r in rr],[r['simple_upper']-r['baseline'] for r in rr],color=color,marker=mark,label='Simple upper minus G: '+parity)
    axes[0].axhline(rr[0]['gap'],color=color,ls='--',label='Simple upper minus family: '+parity)
    axes[1].plot([r['t'] for r in rr],[r['family']-r['baseline'] for r in rr],color=color,marker=mark,label=parity)
axes[0].set(xlabel='Doubling depth t',ylabel='Triangle gap (log scale)',title='Constant family gaps')
axes[1].set(xlabel='Doubling depth t',ylabel='Triangles gained over G',title='Exact improvement over the baseline')
for ax in axes:ax.legend(fontsize=7);ax.grid(alpha=.18)
save(fig,'new-family61-gaps',rows,[ROOT/'Kobon/OpenMathConstructionParetoFamily61.lean',ROOT/'Kobon/Universal.lean'],
    'Exact q=60*2^t family evaluations. Upper floors are for simple arrangements only; numerical priority is not asserted. The 62-line even family is weaker than G.')

source=ROOT/'Kobon/AllN.lean'
text=source.read_text(encoding='utf-8').split('def enhancement',1)[1].split('def bound',1)[0]
enh={int(n):int(T) for n,T in re.findall(r'^\s*\|\s*(\d+)\s*=>\s*(\d+)',text,re.M)}
def baseline(n):return 0 if n<3 else 1 if n==3 else n*(n-3)//3+1+n%2
def previous(n):
    H=max(baseline(n),(n*max(n-3,0)+2)//3,enh.get(n,0))
    for t in range(n+1):
        q=10*2**t
        if n==q+1:H=max(H,(q*q-4)//3)
        elif n==q+2:H=max(H,(q*q-4)//3+q//2)
    return H
def new(n):
    H=previous(n)
    for t in range(n+1):
        for q,T in [(32*2**t,(1024*4**t-1)//3),(36*2**t,432*4**t-1),(48*2**t,768*4**t-1),(60*2**t,1200*4**t-10)]:
            if n==q+1:H=max(H,T)
            elif n==q+2:H=max(H,T+q//2-(1 if q==60*2**t else 0))
    return H
portfolio=[dict(n=n,previous=previous(n),new=new(n)) for n in range(3,601)]
for r in portfolio:assert r['new']>=r['previous']
check={73:1727,74:1763,121:4790,122:4849,241:19190,242:19309,481:76790,482:77029}
for n,T in check.items():assert new(n)>=T
fig,axes=plt.subplots(1,2,figsize=(7.4,2.8),layout='constrained')
ns=[r['n'] for r in portfolio]
axes[0].plot(ns,[r['previous'] for r in portfolio],color=BLUE,lw=.9,label='3 October envelope')
axes[0].plot(ns,[r['new'] for r in portfolio],color=ORANGE,lw=.9,label='Completed portfolio')
axes[0].set(xlabel='Number of lines n',ylabel='Certified lower bound',title='Same quadratic scale')
rr=[r for r in portfolio if r['new']>r['previous']]
axes[1].vlines([r['n'] for r in rr],0,[r['new']-r['previous'] for r in rr],color=TEAL,lw=1.1)
axes[1].scatter([r['n'] for r in rr],[r['new']-r['previous'] for r in rr],color=TEAL,s=15)
axes[1].set(xlabel='Number of lines n',ylabel='Gain over 3 October envelope',title='Additional certified orders')
axes[0].legend(fontsize=7)
for ax in axes:ax.grid(alpha=.18)
save(fig,'new-family-orbits',portfolio,[source,ROOT/'Kobon/Universal.lean',ROOT/'Kobon/RecursiveEnvelope.lean',ROOT/'Kobon/OpenMathConstructionEnvelope.lean'],
    'Exact executable portfolio comparison for3<=n<=600. Retains all finite enhancements and earlier q10 families. Includes known numerical orbits newly formalized here; gains are not claims against worldwide best constructions.')

names=['A0','B15','E3','P21','N12','M22'];old=[-1,-1,0,0,0,0];latest=[0,-1,3,3,1,1]
fig,ax=plt.subplots(figsize=(7.1,2.8),layout='constrained')
x=list(range(len(names)))
ax.bar([v-.18 for v in x],old,width=.36,color=BLUE,label='Earlier half estimate in this run')
ax.bar([v+.18 for v in x],latest,width=.36,color=ORANGE,label='Final M22 estimate')
ax.set_xticks(x,names);ax.axhline(0,color='#444444',lw=.7)
ax.set(ylabel=r'Coefficient in bound for $2\delta-2U$',title='Eliminated source penalty and retained positive profiles')
ax.legend(fontsize=7);ax.grid(axis='y',alpha=.18)
save(fig,'new-upper-profile-coefficients',{'types':names,'earlier':old,'final':latest},[ROOT/'Kobon/UpperOpenMathHalfCurvature.lean',ROOT/'Kobon/UpperOpenMathM22Curvature.lean'],
    'Coefficient comparison of two proved all-triple global estimates within this run, after moving corrections to the right. This is an inequality illustration, not a claim that arbitrary count vectors are geometrically realizable.')

(HERE/'october-figure-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print('PASS: three original vector figures, exact data and source hashes.')
