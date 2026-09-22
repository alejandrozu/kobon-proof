"""Projective-chart search, numerical proposals followed by exact reconstruction.

This searches a new neighborhood compared with line replacement: all lines are
changed simultaneously by one projective transformation. The projective face
census is exact. Candidate ranking uses floating point and is not exhaustive.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys, json, time, argparse, itertools, math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-09-20'))
import numpy as np
from chart_search import projective_faces, through, transform as raw_transform
from research import arrangement, read_lines, primitive, F
from hybrid_search import save_result

def transform(lines,h):
    return raw_transform(lines,[F(h[0],h[2]),F(h[1],h[2]),F(1)])


def run(path,out,seconds=300,seed=221,maximum_pairs=0):
    rng=np.random.default_rng(seed);start=time.time()
    ar=arrangement(read_lines(path));points,faces=projective_faces(ar)
    coords=np.array([[float(F(v,max(abs(x) for x in p))) for v in p] for p in points])
    coords/=np.linalg.norm(coords,axis=1)[:,None]
    ix=np.array([[i for i,s in face] for face in faces])
    fs=np.array([[s for i,s in face] for face in faces],dtype=np.int8)
    initial=best=len(ar['triangles']);P=len(points);examined=verified=0;false_positive=0
    records=[];last=start
    print(json.dumps(dict(event='chart_start',n=len(ar['lines']),triangles=best,
                         projective_triangles=len(faces),vertices=P,seed=seed)),flush=True)
    if initial==len(faces):
        report=dict(n=len(ar['lines']),initial=initial,best=best,projective_triangles=len(faces),
                    exact_obstruction='Every projective triangle is already bounded in the initial chart.')
        Path(str(out)+'.report.json').write_text(json.dumps(report,indent=2));return report

    def check(u,v,perturb):
        nonlocal best,verified,false_positive
        verified+=1
        h=through(points[u],points[v])
        # The signed homogeneous convention of through is ax+by-cz=0.
        d=[F(str(float(x))).limit_denominator(10**7) for x in perturb]
        d[2]*=-1
        vals=[h[0]*x+h[1]*y-h[2]*z for x,y,z in points]
        dvs=[d[0]*x+d[1]*y-d[2]*z for x,y,z in points]
        eps=min([F(abs(a),2)/(abs(b)+1) for a,b in zip(vals,dvs) if a]+[F(1)])
        for multiplier in (1,-1):
            hh=primitive([a+multiplier*eps*b for a,b in zip(h,d)])
            if not hh[2]:continue
            ls=transform(ar['lines'],hh)
            if any(a[0]*b[1]==a[1]*b[0] for a,b in itertools.combinations(ls,2)):continue
            nar=arrangement(ls);score=len(nar['triangles'])
            if score>best:
                best=score
                detail=dict(pair=[u,v],chart=[str(x) for x in hh],projective_triangles=len(faces),
                            seconds=time.time()-start,seed=seed,proposals=examined)
                save_result(out,ls,best,str(path),'Projective transformation of all lines',detail)
                records.append(dict(triangles=best,**detail))
                print(json.dumps(dict(event='chart_improvement',n=len(ls),**records[-1])),flush=True)
                return
        false_positive+=1

    # A full pair list is cheap through about 100 lines; shuffle avoids a
    # pathological initial portion and preserves a reproducible stopping rule.
    pairs=np.array(list(itertools.combinations(range(P),2)),dtype=np.int32)
    rng.shuffle(pairs)
    if maximum_pairs:pairs=pairs[:maximum_pairs]
    for startix in range(0,len(pairs),128):
        if time.time()-start>=seconds or best==len(faces):break
        batch=pairs[startix:startix+128];p=coords[batch[:,0]];q=coords[batch[:,1]]
        h=np.cross(p,q);hn=np.linalg.norm(h,axis=1)
        valid=hn>1e-12
        batch=batch[valid];p=p[valid];q=q[valid];h=h[valid]/hn[valid,None]
        dots=h@coords.T
        sg=np.sign(dots).astype(np.int8);zeros=np.abs(dots)<1e-10
        pq=np.sum(p*q,axis=1);den=1-pq*pq
        for sa,sb in ((1,1),(1,-1),(-1,1),(-1,-1)):
            d=((sa-pq*sb)/den)[:,None]*p+((sb-pq*sa)/den)[:,None]*q
            ds=d@coords.T
            signs=np.where(zeros,np.sign(ds).astype(np.int8),sg)
            f=signs[:,ix]*fs[None,:,:]
            scores=np.sum((f[:,:,0]==f[:,:,1])&(f[:,:,1]==f[:,:,2])&(f[:,:,0]!=0),axis=1)
            examined+=len(batch)
            candidates=np.flatnonzero(scores>best)
            for j in candidates:
                if scores[j]>best:check(int(batch[j,0]),int(batch[j,1]),d[j])
        if time.time()-last>30:
            print(json.dumps(dict(event='chart_progress',n=len(ar['lines']),best=best,
                                 proposals=examined,verified=verified,seconds=time.time()-start)),flush=True)
            last=time.time()
    report=dict(n=len(ar['lines']),source=str(path),initial=initial,best=best,
                projective_triangles=len(faces),vertices=P,proposals=examined,exact_candidates=verified,
                false_positives=false_positive,seconds=time.time()-start,seed=seed,improvements=records,
                limitations='Floating candidate ranking is heuristic; no exhaustive optimality claim.')
    Path(str(out)+'.report.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(dict(event='chart_done',**report)),flush=True)
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('out')
    p.add_argument('--seconds',type=float,default=300);p.add_argument('--seed',type=int,default=221)
    p.add_argument('--pairs',type=int,default=0);a=p.parse_args()
    run(a.path,a.out,a.seconds,a.seed,a.pairs)
