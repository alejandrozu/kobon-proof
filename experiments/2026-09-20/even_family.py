"""Finite rational realizations approximating Parpalak--Utkin's even draft.

All actual output arrangements are counted exactly. Trig evaluations only
propose rational coefficients; they do not certify an infinite family.
Source: github.com/parpalak/kobon-even-draft/8-14-26-even-series.md
"""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent/'vendor'))
from mpmath import mp
from research import *

def rat(x): return F(str(x))

def build(t,dps=100):
    mp.dps=dps
    target=6*2**t;s=rat(mp.sqrt(3));eps=F(1,4*target)
    eta=3*s*target**6;delta=2*target**6
    a=[-s,-1/s,1/s,s,-eps,eps]
    # Preserve the two triple intersections exactly after approximating sqrt(3).
    qx=(2*eta/s-s)/(1+2*eta);qy=-(qx+s)/2
    slopes=[-F(1,2),-eta,eta,F(2,5),
            qy/(qx+eps),4*s/(s+9*eps)]
    n=6
    for step in range(t):
        mn=min(abs(x) for x in slopes)
        bb=[rat(mp.tan(-mp.pi/2+(F(j,1)-F(1,2))*mp.pi/n)) for j in range(1,n+1)]
        mm=[-mn/F(n**10)*(2*b/(1+b*b)+1/(n**6*b)) for b in bb]
        a+=bb;slopes+=mm;n*=2
    ls=[(0,1,0)]+[primitive((m,-1,m*x)) for m,x in zip(slopes,a)]
    ls.append((1,-1,delta))
    return ls

def main(t):
    from seed_search import far_extensions
    ls=build(t);ar=arrangement(ls);n=len(ls);score=len(ar['triangles'])
    want=(n*(2*n-5)+2)//6
    print('known family',n,'exact count',score,'expected',want,flush=True)
    mult=[sorted(x) for x in ar['points'].values() if len(x)>2]
    print('multiple vertices',mult,flush=True)
    def save(tag,lines,count):
        Path(__file__).with_name(tag+'.json').write_text(json.dumps(dict(n=len(lines),triangle_count=count,lines_frac=[[str(x) for x in l] for l in lines]),indent=2))
    save(f'pu-family-{n}',ls,score)
    if score!=want: return
    best,r=far_extensions(ar)
    print('far extension',n+1,'triangles',best,'gain',best-score,flush=True)
    save(f'pu-far-{n+1}',ls+[r],best)
    # A second distant line, opposite the distinguished R.
    delta=2*(n-2)**6
    for slope in (-1,1):
        extra=primitive((slope,-1,delta))
        if extra in ar['lines']:continue
        try:
            count=len(arrangement(ls+[extra])['triangles'])
            print('second cap slope',slope,'count',count,flush=True)
            save(f'pu-cap-{n+1}-{slope}',ls+[extra],count)
        except AssertionError:pass

if __name__=='__main__':main(int(sys.argv[1]))
