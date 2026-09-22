"""Chart proposals for the NONSIMPLE phase-zero Furedi-Palasti arrangement.

Concurrency labels are exact modular triples. Trigonometric coordinates,
edge order, projective face lifts and chart ranking use floating point. This
script discovers conjectures; its output is not an exact coordinate proof.
"""
import argparse,collections,itertools,json,math,time
from pathlib import Path
import numpy as np
from cubic_chambers import base

def projective(n):
    theta=np.arange(n)*math.pi/n
    ls=np.column_stack((np.sin(theta),np.cos(theta),np.sin(3*theta)))
    vdict,affine,gap=base(n);keys=sorted(vdict);idx={k:i for i,k in enumerate(keys)}
    xyz=np.array([[*vdict[k],1]for k in keys]);xyz/=np.linalg.norm(xyz,axis=1)[:,None]
    edges={};neighbors=collections.defaultdict(set)
    for i in range(n):
        row={}
        for j in range(n):
            if i==j:continue
            v=tuple(sorted({i,j,(-i-j)%n}))
            row[idx[v]]=math.cos(theta[i]+2*theta[j])
        rr=sorted(row,key=row.get)
        for a,b in zip(rr,rr[1:]+rr[:1]):
            edge=frozenset((a,b));s=-1 if a==rr[-1] else 1
            assert edge not in edges or edges[edge]==(i,s),(n,edge)
            edges[edge]=(i,s);neighbors[a].add(b);neighbors[b].add(a)
    faces=[]
    for p,ad in neighbors.items():
        for q,r in itertools.combinations(sorted(x for x in ad if x>p),2):
            if frozenset((q,r))not in edges:continue
            e1=edges[frozenset((p,q))];e2=edges[frozenset((p,r))];e3=edges[frozenset((q,r))]
            if len({e1[0],e2[0],e3[0]})!=3:continue
            if e1[1]*e2[1]*e3[1]!=1:continue
            faces.append(((p,q,r),(1,e1[1],e2[1])))
    fi=np.array([f[0]for f in faces]);fs=np.array([f[1]for f in faces],dtype=np.int8)
    affine_count=int(np.count_nonzero((fs[:,0]==fs[:,1])&(fs[:,1]==fs[:,2])))
    assert affine_count==len(affine),(n,affine_count,len(affine))
    return xyz,fi,fs,keys,gap

def scan(n,maxpairs=0,seed=932):
    start=time.monotonic();xyz,fi,fs,keys,gap=projective(n)
    best=int(np.count_nonzero(np.all(fs==1,axis=1)));initial=best;history=[]
    besth=np.array([0.,0.,1.]);rng=np.random.default_rng(seed)
    pairs=np.array(list(itertools.combinations(range(len(xyz)),2)),dtype=np.int32)
    rng.shuffle(pairs)
    if maxpairs:pairs=pairs[:maxpairs]
    count=0
    for s in range(0,len(pairs),128):
        batch=pairs[s:s+128];p=xyz[batch[:,0]];q=xyz[batch[:,1]]
        hh=np.cross(p,q);norm=np.linalg.norm(hh,axis=1);valid=norm>1e-10
        batch=batch[valid];p=p[valid];q=q[valid];hh=hh[valid]/norm[valid,None]
        vals=hh@xyz.T;zero=np.abs(vals)<1e-9;sg=np.sign(vals).astype(np.int8)
        pq=np.sum(p*q,axis=1);den=1-pq*pq
        for sa,sb in ((1,1),(1,-1),(-1,1),(-1,-1)):
            d=((sa-pq*sb)/den)[:,None]*p+((sb-pq*sa)/den)[:,None]*q
            dv=d@xyz.T;signs=np.where(zero,np.sign(dv).astype(np.int8),sg)
            f=signs[:,fi]*fs[None,:,:]
            scores=np.sum((f[:,:,0]==f[:,:,1])&(f[:,:,1]==f[:,:,2])&(f[:,:,0]!=0),axis=1)
            count+=len(batch)
            for a in np.flatnonzero(scores>best):
                # A concrete perturbed chart, with every nonzero old sign stable.
                eps=min([abs(x)/(2*(abs(y)+1))for x,y,z in zip(vals[a],dv[a],zero[a])if not z]+[.01])
                h=hh[a]+eps*d[a]
                ff=np.sign(xyz@h)[fi]*fs
                score=int(np.sum((ff[:,0]==ff[:,1])&(ff[:,1]==ff[:,2])&(ff[:,0]!=0)))
                if score>best:
                    best=score;besth=h
                    history.append(dict(count=best,chart=h.tolist(),pair=[keys[i]for i in batch[a]],seconds=time.monotonic()-start))
    return dict(n=n,initial_affine=initial,projective_triangles=len(fi),best_float=best,
                chart=besth.tolist(),minimum_order_gap=gap,proposals=count,history=history,
                seconds=time.monotonic()-start,status='floating proposal, exact modular concurrency grouping; not a proof')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--ns',default='6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60')
    p.add_argument('--maxpairs',type=int,default=0);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True);records=[]
    for n in map(int,a.ns.split(',')):
        row=scan(n,a.maxpairs);records.append(row)
        (a.out/f'n{n:03d}.json').write_text(json.dumps(row,indent=2)+'\n')
        (a.out/'report.json').write_text(json.dumps(records,indent=2)+'\n')
        print(json.dumps(row),flush=True)
