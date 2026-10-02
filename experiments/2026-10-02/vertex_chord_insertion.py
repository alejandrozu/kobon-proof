"""Exact insertion of a line through two existing vertices.

The old arrangement is simple; the new line may create several triple points.
For each old vertex, both intersections with the new line must be on its
incident elementary segments/rays. Convexity then makes that support triple
an empty triangle. Old triangles survive exactly when their vertices have
one weak sign. All signs are integer, without numerical ranking or tolerances.
Any best output is independently checked by adjacency and direct signs.
"""
from pathlib import Path
import sys,time,json,itertools as it,random,hashlib,argparse,math
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import numpy as np
from exact_geometry import arrangement,read_lines,primitive
from verify_direct import verify


def sign(x):return (x>0)-(x<0)


class Insertion:
    def __init__(self,path):
        self.lines=read_lines(path);ar=arrangement(self.lines);self.n=len(self.lines)
        assert len(ar['points'])==self.n*(self.n-1)//2
        self.points=list(ar['points']);self.m=len(self.points);ix={p:i for i,p in enumerate(self.points)}
        self.supports=np.array([sorted(ar['points'][p]) for p in self.points],dtype=np.int32)
        self.tri=np.array([[ix[p] for p in t]for t in ar['triangle_vertices']],dtype=np.int32)
        self.left=np.full((self.m,2),self.m,dtype=np.int32);self.right=self.left.copy()
        for i,row in enumerate(ar['rows']):
            for pos,p in enumerate(row):
                v=ix[p];side=int(self.supports[v,1]==i)
                if pos:self.left[v,side]=ix[row[pos-1]]
                if pos+1<len(row):self.right[v,side]=ix[row[pos+1]]
        self.isleft=self.left==self.m;self.isright=self.right==self.m
        self.initial=len(ar['triangles'])

    def score(self,line):
        a,b,c=line
        ds=[]
        for A,B,C in self.lines:
            det=a*B-b*A
            if not det:return None
            ds.append(sign(det*B) if B else sign(b))
        signs=np.array([sign(a*x+b*y-c*z)for x,y,z in self.points]+[0],dtype=np.int8)
        tri=signs[self.tri];retained=int(np.sum(~(np.any(tri>0,axis=1)&np.any(tri<0,axis=1))))
        sv=signs[:-1,None];slope=np.array(ds,dtype=np.int8)[self.supports]
        left=signs[self.left];right=signs[self.right]
        valid=((~self.isleft)&(sv*left<=0))|((~self.isright)&(sv*right<=0))|(self.isleft&(sv*slope>0))|(self.isright&(sv*slope<0))
        gained=int(np.sum((signs[:-1]!=0)&np.all(valid,axis=1)))
        return retained+gained,retained,gained,int(np.sum(signs[:-1]==0))

    def chord(self,i,j):
        x,y,z=self.points[i];u,v,w=self.points[j]
        return primitive((y*w-z*v,z*u-x*w,y*u-x*v))


def run(source,out,seconds,seed,target,limit):
    source=source.resolve();out.mkdir(parents=True,exist_ok=True);model=Insertion(source)
    rng=random.Random(seed);pairs=list(it.combinations(range(model.m),2));rng.shuffle(pairs)
    start=time.time();best=-1;bestline=None;attempts=valid=0;records=[];seen=set()
    sourcehash=hashlib.sha256(source.read_bytes()).hexdigest()
    print(json.dumps(dict(event='start',n=model.n+1,old=model.initial,vertices=model.m,pair_candidates=len(pairs),target=target,seconds=seconds,seed=seed)),flush=True)
    # Sanity controls exercise the independent scorer on random rational lines.
    for q in range(5):
        line=tuple(rng.randrange(-100,101)for _ in range(3));value=model.score(line)
        if value is not None:assert len(arrangement(model.lines+[line])['triangles'])==value[0]
    for i,j in pairs:
        if time.time()-start>seconds or (limit and attempts>=limit):break
        attempts+=1
        if set(model.supports[i])&set(model.supports[j]):continue
        line=model.chord(i,j)
        if line in seen:continue
        seen.add(line);value=model.score(line)
        if value is None:continue
        valid+=1;count,retained,gained,triplepoints=value
        if count>best:
            best=count;bestline=line
            row=dict(attempt=attempts,valid=valid,triangles=count,retained=retained,new_triangles=gained,
                     new_triple_points=triplepoints,vertices=[i,j],seconds=time.time()-start)
            records.append(row);print(json.dumps(dict(event='best',**row)),flush=True)
            if best>=target:
                lines=model.lines+[line];check=arrangement(lines);assert len(check['triangles'])==best
                dest=out/f'n{model.n+1:03d}-t{best}.json'
                dest.write_text(json.dumps(dict(n=model.n+1,triangle_count=best,lines_frac=[[str(z)for z in l]for l in lines],
                  source=str(source.relative_to(ROOT)),source_sha256=sourcehash,
                  construction='Exact vertex-chord insertion; permits triple intersections',
                  proposal=row,verification='Exact local segment scorer plus independent adjacency and direct sign counters'),indent=2)+'\n')
                row['independent_verification']=verify(dest)
        if attempts%5000==0:
            print(json.dumps(dict(event='progress',attempts=attempts,valid=valid,best=best,seconds=time.time()-start)),flush=True)
            (out/'progress.json').write_text(json.dumps(dict(attempts=attempts,valid=valid,best=best,seconds=time.time()-start)))
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=sourcehash,source_count=model.initial,
                target_order=model.n+1,target_count=target,seed=seed,time_limit=seconds,
                pair_candidates=len(pairs),attempts=attempts,distinct_nonparallel_chords=valid,best=best,
                complete_pair_scan=attempts==len(pairs),seconds=time.time()-start,improvements=records,
                scope='Exact bounded vertex-chord insertion search in this fixed old arrangement; no global nonexistence or optimality assertion.')
    if bestline is not None:
        report['best_line']=[str(v)for v in bestline]
        check=arrangement(model.lines+[bestline]);assert len(check['triangles'])==best
        report['best_adjacency_check']=len(check['triangles'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(event='done',**{k:v for k,v in report.items() if k not in ('improvements','best_line')})),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=300);p.add_argument('--seed',type=int,default=20261002)
    p.add_argument('--target',type=int,required=True);p.add_argument('--limit',type=int,default=0)
    a=p.parse_args();run(a.source,a.out,a.seconds,a.seed,a.target,a.limit)
