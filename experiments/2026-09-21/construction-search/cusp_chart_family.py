"""Test deltoid cusp-chord affine charts of rationalized FP arrangements.

Every saved witness is counted by exact adjacency and independently by the
open-interior sign test. Parameter scanning is numerical and heuristic.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,argparse,time,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/python-deps'))
sys.path.insert(0,str(ROOT/'experiments/2026-09-20'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import numpy as np
import mpmath as mp
from chart_search import projective_faces,transform as raw_transform
from research import arrangement,primitive,F
from hybrid_search import save_result
from verify_direct import verify

def transform(lines,h):
    # Normalize the chart scale so later numerical investigations remain well
    # conditioned. Scaling x,y has no effect on the exact triangle count.
    return raw_transform(lines,[F(h[0],h[2]),F(h[1],h[2]),F(1)])


def build(n,phase):
    mp.mp.dps=60
    pp=mp.mpf(phase.numerator)/phase.denominator
    lines=[]
    for i in range(n):
        theta=(i+pp)*mp.pi/n
        lines.append(primitive([F(str(mp.sin(theta))),F(str(mp.cos(theta))),F(str(mp.sin(3*theta)))]))
    return lines


def run(first,last,phases,outdir):
    dest=Path(outdir);dest.mkdir(exist_ok=True,parents=True);records=[]
    for n in range(first,last+1):
        if n<5:continue
        for phase in phases:
            start=time.time();lines=build(n,phase);ar=arrangement(lines)
            ps,faces=projective_faces(ar)
            xyz=np.array([[float(F(v,p[2])) for v in p] for p in ps])
            ix=np.array([[i for i,s in face] for face in faces])
            fs=np.array([[s for i,s in face] for face in faces],dtype=np.int8)
            best=len(ar['triangles']);initial=best;winner=None
            # Three cusp chords. Angular shifts shrink as n^-2, as do the
            # distances to the cusp chord; the grid includes the exact chord.
            params=[];hs=[]
            for cusp in range(3):
                for beta in np.linspace(-3,3,25):
                    angle=-mp.pi/3+cusp*2*mp.pi/3+beta*mp.pi/(n*n)
                    a,b=float(mp.cos(angle)),float(mp.sin(angle))
                    for gamma in np.linspace(-1,15,65):
                        c=1.5-gamma*float(mp.pi)**2/(n*n)
                        params.append((cusp,float(beta),float(gamma)))
                        hs.append((a,b,-c))
            hs=np.array(hs)
            for startix in range(0,len(hs),256):
                vals=hs[startix:startix+256]@xyz.T
                signs=np.sign(vals).astype(np.int8)
                sg=signs[:,ix]*fs
                scores=np.sum((sg[:,:,0]==sg[:,:,1])&(sg[:,:,1]==sg[:,:,2])&(sg[:,:,0]!=0),axis=1)
                order=np.argsort(scores)[::-1]
                for jj in order:
                    if scores[jj]<=best:break
                    j=startix+int(jj);h=hs[j]
                    hh=primitive([F(str(h[0])),F(str(h[1])),F(str(-h[2]))])
                    new=transform(lines,hh)
                    if any(a[0]*b[1]==a[1]*b[0] for a,b in itertools.combinations(new,2)):continue
                    nn=arrangement(new);score=len(nn['triangles'])
                    if score>best:
                        best=score;winner=(new,hh,params[j])
                if best==len(faces):break
            detail=dict(n=n,phase=str(phase),initial=initial,best=best,projective=len(faces),
                        parameters=winner[2] if winner else None,seconds=time.time()-start)
            if winner:
                out=dest/f'fp-{n:03d}-phase-{phase.numerator}-{phase.denominator}.json'
                save_result(out,winner[0],best,'Furedi-Palasti trigonometric line construction',
                            'Projective chart near a deltoid cusp chord',detail)
                verify(out)
                detail['certificate']=str(out.relative_to(ROOT)) if out.is_absolute() else str(out)
            records.append(detail)
            (dest/'cusp-family-report.json').write_text(json.dumps(records,indent=2))
            print(json.dumps(detail),flush=True)
    return records


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--first',type=int,default=5);p.add_argument('--last',type=int,default=60)
    p.add_argument('--phases',default='1/2,1/6,5/6');p.add_argument('--outdir',required=True);a=p.parse_args()
    run(a.first,a.last,[F(p) for p in a.phases.split(',')],a.outdir)
