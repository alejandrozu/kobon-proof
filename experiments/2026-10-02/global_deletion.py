"""Global subset optimization in an exact real arrangement.

Unlike a greedy single-line deletion, every potential support triple is given
its exact set of cutting lines. A subset contains that triangular cell iff it
retains all three supports and deletes every cutter. This gives a compact
0/1 optimization problem, scored exactly and independent of coordinates after
preprocessing. MILP bounds are solver diagnostics, never mathematical upper
bounds. Promoted coordinates must pass both independent exact counters.
"""
from pathlib import Path
import os
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import sys, json, itertools as it, hashlib, time, argparse, random, warnings
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement, read_lines
from verify_direct import verify
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix


def prepare(path, max_delete):
    lines=read_lines(path); n=len(lines); ar=arrangement(lines)
    assert len(ar['points'])==n*(n-1)//2, 'simple nonparallel input required'
    pairs=list(it.combinations(range(n),2)); pi={p:i for i,p in enumerate(pairs)}
    ds=[1 if lines[i][0]*lines[j][1]-lines[i][1]*lines[j][0]>0 else -1 for i,j in pairs]
    pos=[0]*len(pairs); neg=[0]*len(pairs)
    triples=list(it.combinations(range(n),3))
    for i,j,k in triples:
        a,b,c=lines[i];d,e,f=lines[j];g,h,z=lines[k]
        determinant=a*(e*z-f*h)-b*(d*z-f*g)+c*(d*h-e*g)
        assert determinant
        sign=1 if determinant>0 else -1
        ps=(pi[i,j],pi[i,k],pi[j,k])
        for p,r,s in zip(ps,(k,j,i),(-sign*ds[ps[0]],sign*ds[ps[1]],-sign*ds[ps[2]])):
            (pos if s>0 else neg)[p] |= 1<<r
    terms=[]
    for t in triples:
        i,j,k=t;p,q,r=pi[i,j],pi[i,k],pi[j,k]
        cutters=(pos[p]|pos[q]|pos[r]) & (neg[p]|neg[q]|neg[r])
        if cutters.bit_count()<=max_delete:
            terms.append((sum(1<<x for x in t),cutters,t))
    assert sum(not cutters for support,cutters,t in terms)==len(ar['triangles'])
    return lines,terms,len(ar['triangles'])


def score(terms, removed):
    return sum(not (support&removed) and cutters&removed==cutters for support,cutters,t in terms)


def save(lines, removed, count, source, out):
    kept=[i for i in range(len(lines)) if not (removed>>i)&1]
    selected=[lines[i] for i in kept]
    exact=arrangement(selected)
    assert len(exact['triangles'])==count
    data=dict(n=len(kept),triangle_count=count,simple=True,
              lines_frac=[[str(v) for v in l] for l in selected],
              kept_indices=kept,deleted_indices=[i for i in range(len(lines)) if (removed>>i)&1],
              source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              construction='Global exact support/cutter subset optimization',
              verification='Exact adjacency and independent direct sign counters agree')
    out.write_text(json.dumps(data,indent=2)+'\n')
    direct=verify(out)
    return direct


def run(source, targets, out, seconds, mode, seed, width):
    out.mkdir(parents=True,exist_ok=True);start=time.time(); N=len(read_lines(source))
    lines,terms,initial=prepare(source,N-min(targets)); rng=random.Random(seed)
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                source_order=N,source_count=initial,terms=len(terms),mode=mode,seed=seed,seconds_per_order=seconds,records=[])
    print(json.dumps({k:v for k,v in report.items() if k!='records'}),flush=True)
    previous={0:initial}
    for target in sorted(targets,reverse=True):
        d=N-target; tt=[v for v in terms if v[1].bit_count()<=d]
        s=time.time()
        if mode=='milp':
            # x_i = deleted line; y_t = counted triangle. Maximizing y makes
            # only the forward implications necessary.
            rows=[];cols=[];vals=[];lo=[d];hi=[d]
            rows.extend([0]*N);cols.extend(range(N));vals.extend([1]*N)
            row=1
            for q,(support,cutters,t) in enumerate(tt):
                for i in t:
                    rows.extend((row,row));cols.extend((i,N+q));vals.extend((1,1));lo.append(-np.inf);hi.append(1);row+=1
                for i in range(N):
                    if cutters>>i&1:
                        rows.extend((row,row));cols.extend((i,N+q));vals.extend((-1,1));lo.append(-np.inf);hi.append(0);row+=1
            mat=coo_matrix((vals,(rows,cols)),shape=(row,N+len(tt))).tocsc()
            objective=np.r_[np.zeros(N),-np.ones(len(tt))]
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                sol=milp(objective,integrality=np.ones(N+len(tt)),bounds=Bounds(0,1),
                         constraints=LinearConstraint(mat,np.array(lo),np.array(hi)),
                         options={'time_limit':seconds,'threads':1,'mip_rel_gap':0})
            if sol.x is None:
                record=dict(n=target,deleted=d,result=str(sol.message),seconds=time.time()-s)
                report['records'].append(record);print(json.dumps(record),flush=True);continue
            removed=sum(1<<i for i in range(N) if sol.x[i]>.5)
            assert removed.bit_count()==d
            best=score(tt,removed)
            record=dict(n=target,deleted=d,triangles=best,solver_objective=-float(sol.fun),
                        solver_dual_bound=-float(sol.mip_dual_bound),solver_gap=float(sol.mip_gap),
                        solver_nodes=int(sol.mip_node_count),result=str(sol.message),seconds=time.time()-s)
        else:
            # Breadth-first subset enumeration through two deletions, then
            # bounded beam search with an exact scorer and seeded tie order.
            for level in range(next(iter(previous)).bit_count()+1,d+1):
                proposals={}
                for old in previous:
                    for i in range(N):
                        if old>>i&1:continue
                        mask=old|(1<<i)
                        if mask not in proposals:proposals[mask]=score(tt,mask)
                ranked=list(proposals.items());rng.shuffle(ranked);ranked.sort(key=lambda z:z[1],reverse=True)
                previous=dict(ranked if level<=2 else ranked[:width])
                print(json.dumps(dict(event='beam_level',deleted=level,proposals=len(proposals),retained=len(previous),best=ranked[0][1])),flush=True)
            removed,best=max(previous.items(),key=lambda z:z[1])
            record=dict(n=target,deleted=d,triangles=best,beam_width=width,seconds=time.time()-s,
                        exhaustive_subsets=(d<=2),result='bounded exact subset search')
        record['baseline']=target*(target-3)//3+1+target%2
        record['deleted_indices']=[i for i in range(N) if removed>>i&1]
        path=out/f'n{target:03d}.json'
        record['independent_verification']=save(lines,removed,best,source,path)
        report['records'].append(record);print(json.dumps(record),flush=True)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    report['total_seconds']=time.time()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--targets',required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--mode',choices=['milp','beam'],default='milp');p.add_argument('--seed',type=int,default=20261002)
    p.add_argument('--width',type=int,default=40);a=p.parse_args()
    run(a.source.resolve(),list(map(int,a.targets.split(','))),a.out,a.seconds,a.mode,a.seed,a.width)
