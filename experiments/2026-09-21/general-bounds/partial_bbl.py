"""Exact-combinatorial deletion/partial-doubling search in retained BBL families.

Every crossing order is reconstructed from exact rational coordinates. Scoring
subsets only removes entries from those exact orders, so no numerical geometry
is involved. Saved best subsets are independently reconstructed and counted.
"""
import argparse,collections,json,sys,time
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from exact_geometry import arrangement,read_lines

def prepare(path):
    ar=arrangement(read_lines(path));n=len(ar['lines'])
    assert len(ar['points'])==n*(n-1)//2 and all(len(v)==2 for v in ar['points'].values())
    rows=np.array([[next(j for j in ar['points'][v]if j!=i)for v in row]for i,row in enumerate(ar['rows'])],dtype=np.int32)
    return ar,rows

def count(rows,keep):
    N=len(rows);ids=np.flatnonzero(keep);n=len(ids)
    selected=rows[ids];filtered=selected[keep[selected]].reshape((n,n-1))
    a=np.broadcast_to(ids[:,None],(n,n-2)).ravel()
    tri=np.stack((a,filtered[:,:-1].ravel(),filtered[:,1:].ravel()),axis=1);tri.sort(axis=1)
    keys=tri[:,0]*N*N+tri[:,1]*N+tri[:,2]
    _,counts=np.unique(keys,return_counts=True)
    return int(np.count_nonzero(counts==3))

def save(ar,keep,t,path,metadata):
    lines=[ar['lines'][i]for i in np.flatnonzero(keep)];check=arrangement(lines)
    assert len(check['triangles'])==t
    path.write_text(json.dumps(dict(n=len(lines),triangle_count=t,simple=True,
        lines_frac=[[str(c)for c in l]for l in lines],
        kept_indices=np.flatnonzero(keep).tolist(),verification='two exact adjacency reconstructions; direct-sign pending',**metadata),indent=2)+'\n')

def greedy(path,out,minimum,only_new=False):
    out.mkdir(parents=True,exist_ok=True);ar,rows=prepare(path);N=len(rows);keep=np.ones(N,dtype=bool)
    initial=len(ar['triangles']);assert count(rows,keep)==initial;report=[];start=time.monotonic()
    for n in range(N-1,minimum-1,-1):
        best=-1;winner=None
        for i in np.flatnonzero(keep):
            if only_new and i<=(N-1)//2:continue
            keep[i]=False;t=count(rows,keep);keep[i]=True
            if t>best:best=t;winner=int(i)
        if winner is None:break
        keep[winner]=False
        baseline=n*(n-3)//3+1+n%2
        row=dict(n=n,triangles=best,baseline=baseline,removed=winner,seconds=time.monotonic()-start,only_new=only_new)
        report.append(row)
        if best>=baseline:save(ar,keep,best,out/f'n{n:03d}.json',dict(source=str(path),construction='greedy deletion from exact BBL family'))
        print(json.dumps(row),flush=True)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--minimum',type=int,required=True);p.add_argument('--only-new',action='store_true');a=p.parse_args()
    greedy(a.path,a.out,a.minimum,a.only_new)
