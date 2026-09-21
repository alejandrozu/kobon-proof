"""Search straight-line insertions, using vertex sectors as a fast proposal score.

Floating point is used only to rank proposals. Every saved improvement is
reconstructed from rational data and counted by the exact adjacency counter.
Lines are a*x+b*y=c. This is not an exhaustive search over arrangements.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import sys, time, argparse, hashlib
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent/'vendor'))
import numpy as np
from research import *
from functools import cmp_to_key
from extension_audit import angle_compare, exterior_choices


class InsertionScore:
    def __init__(self, lines):
        self.ar = arrangement(lines)
        self.lines = self.ar['lines']
        self.points = list(self.ar['points'])
        ix = {p:i for i,p in enumerate(self.points)}
        self.finite = len(self.points)
        self.coords = list(self.points)
        self.incidence = [sum(1 << i for i in self.ar['points'][p]) for p in self.points]
        ends = {}
        for i, row in enumerate(self.ar['rows']):
            a,b,c = self.lines[i]
            d = (b,-a)
            axis = 0 if b else 1
            if d[axis] < 0: d = (-d[0],-d[1])
            neg = len(self.coords); self.coords.append((-d[0],-d[1],0))
            pos = len(self.coords); self.coords.append((d[0],d[1],0))
            for j,p in enumerate(row):
                ends[(i,ix[p])] = ((d[0],d[1],ix[row[j+1]] if j+1<len(row) else pos),
                                   (-d[0],-d[1],ix[row[j-1]] if j else neg))
        sectors = []
        for p,incident in self.ar['points'].items():
            pi = ix[p]
            rays = [r for i in incident for r in ends[(i,pi)]]
            rays.sort(key=cmp_to_key(angle_compare))
            for r,s in zip(rays,rays[1:]+rays[:1]):
                if r[0]*s[1]-r[1]*s[0] > 0:
                    sectors.append((pi,r[2],s[2]))
        self.sectors = np.array(sectors,dtype=np.int32).T
        self.tri = np.array([[ix[p] for p in tri] for tri in self.ar['triangle_vertices']],dtype=np.int32).T
        self.xyz = np.array([[float(F(v,max(abs(x) for x in p))) for v in p] for p in self.coords])
        self.base = len(self.ar['triangles'])

    def exact_sign_score(self, line):
        a,b,c = line
        vals = [a*x+b*y-c*z for x,y,z in self.coords]
        s = [1 if v>0 else -1 if v<0 else 0 for v in vals]
        loss = sum(min(s[i] for i in tri)<0<max(s[i] for i in tri) for tri in self.tri.T)
        gain = sum(s[p] != 0 and s[p]*s[q]<=0 and s[p]*s[r]<=0
                   and (q<self.finite or s[q]!=0) and (r<self.finite or s[r]!=0)
                   for p,q,r in self.sectors.T)
        return int(self.base-loss+gain)

    def scores(self, hs, forced=None, tolerance=1e-11):
        hs=np.atleast_2d(hs)
        hs=hs/np.max(np.abs(hs),axis=1)[:,None]
        vals = hs[:,0,None]*self.xyz[None,:,0]+hs[:,1,None]*self.xyz[None,:,1]+hs[:,2,None]*self.xyz[None,:,2]
        signs = ((vals>tolerance).astype(np.int8)-(vals<-tolerance).astype(np.int8))
        if forced is not None:
            for j in range(forced.shape[1]): signs[np.arange(len(hs)),forced[:,j]]=0
        a,b,c = signs[:,self.tri[0]],signs[:,self.tri[1]],signs[:,self.tri[2]]
        loss=np.sum((np.minimum(np.minimum(a,b),c)<0)&(np.maximum(np.maximum(a,b),c)>0),axis=1)
        p,q,r = self.sectors
        sp,sq,sr=signs[:,p],signs[:,q],signs[:,r]
        gain=np.sum((sp!=0)&(sp*sq<=0)&(sp*sr<=0)&((q<self.finite)|(sq!=0))&((r<self.finite)|(sr!=0)),axis=1)
        return self.base-loss+gain

    def line_through(self,p,q):
        x,y,z = self.coords[p];u,v,w = self.coords[q]
        return primitive((y*w-z*v,z*u-x*w,y*u-x*v))


def save_result(path, lines, count, source, operation, details):
    data=dict(n=len(lines),triangle_count=count,lines_frac=[[str(x) for x in l] for l in lines],
              source=source,operation=operation,details=details,
              priority_status='Unestablished; search output, not a claim of a new world record.',
              declared_parallel_pairs=[[i,j] for i,j in it.combinations(range(len(lines)),2)
                                       if lines[i][0]*lines[j][1]==lines[i][1]*lines[j][0]])
    Path(path).write_text(json.dumps(data,indent=2),encoding='utf-8')


def chord_search(path, out, drop=None, target=0, batch=128, max_pairs=0):
    lines=read_lines(path)
    if drop is not None: lines.pop(drop)
    sc=InsertionScore(lines)
    gain,line=exterior_choices(sc.ar)[0]
    best=sc.base+gain
    winner=line
    print(json.dumps(dict(event='start',source=str(path),n=len(lines)+1,base=sc.base,exterior=best,
                          vertices=sc.finite,sectors=len(sc.sectors[0]),drop=drop)),flush=True)
    save_result(out,lines+[line],best,str(path),'exterior insertion',dict(drop=drop,gain=gain))
    checked=0; exact_checked=0; approximate_false=0; start=time.time(); last=start
    proposals=[]
    def process(pairs):
        nonlocal best,winner,checked,exact_checked,approximate_false
        if not pairs:return
        ij=np.array(pairs,dtype=np.int32)
        hs=np.cross(sc.xyz[ij[:,0]],sc.xyz[ij[:,1]])
        scores=sc.scores(hs,ij)
        checked+=len(pairs)
        promising=np.flatnonzero(scores>best)
        promising=promising[np.argsort(scores[promising])[::-1]]
        for j in promising:
            if scores[j]<=best:continue
            p,q=pairs[j];candidate=sc.line_through(p,q)
            if candidate in sc.lines:continue
            exact_checked+=1
            fast_exact=sc.exact_sign_score(candidate)
            if fast_exact<=best:
                approximate_false+=int(fast_exact!=scores[j]);continue
            ar=arrangement(lines+[candidate]);exact=len(ar['triangles'])
            assert exact==fast_exact,(exact,fast_exact)
            best=exact;winner=candidate
            details=dict(drop=drop,p=p,q=q,old_vertex_lines=[sorted(sc.ar['points'][sc.points[k]]) for k in (p,q)],
                         elapsed=time.time()-start,proposals=checked)
            save_result(out,lines+[candidate],best,str(path),'line through two exact old vertices',details)
            print(json.dumps(dict(event='improvement',n=len(lines)+1,best=best,details=details)),flush=True)
    for p,q in it.combinations(range(sc.finite),2):
        if sc.incidence[p]&sc.incidence[q]:continue
        proposals.append((p,q))
        if len(proposals)==batch:
            process(proposals);proposals=[]
            if target and best>=target:break
            if max_pairs and checked>=max_pairs:break
            if time.time()-last>20:
                print(json.dumps(dict(event='progress',checked=checked,best=best,seconds=round(time.time()-start,2))),flush=True);last=time.time()
    process(proposals)
    report=dict(source=str(path),n=len(lines)+1,base=sc.base,best=best,drop=drop,proposals=checked,
                exact_candidates_checked=exact_checked,approximate_false=approximate_false,seconds=time.time()-start,
                scope='All pairs of finite old vertices without a common input line' if not max_pairs and not(target and best>=target)
                      else 'Bounded pair search',
                limitations='Floating ranking may miss a better candidate. No global optimality or priority claim.')
    Path(str(out)+'.search.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    print(json.dumps(dict(event='done',**report)),flush=True)
    return report


def validate():
    import random
    rng=random.Random(271)
    ls=[(1,0,0),(0,1,0),(1,1,0),(1,-1,1),(2,1,3),(-2,1,2)]
    for lines in (ls,read_lines(Path(__file__).with_name('certificate-38.json'))):
        sc=InsertionScore(lines)
        proposals=[primitive((rng.randint(1,20),rng.randint(-20,20),rng.randint(-20,20))) for _ in range(30)]
        for p,q in list(it.combinations(range(sc.finite),2))[::max(1,sc.finite**2//100)]:
            if not sc.incidence[p]&sc.incidence[q]:proposals.append(sc.line_through(p,q))
        for l in proposals:
            if l in sc.lines:continue
            exact=len(arrangement(lines+[l])['triangles'])
            assert sc.exact_sign_score(l)==exact,(l,sc.exact_sign_score(l),exact)
        print('sector scoring validation passed',len(lines),'lines',len(proposals),'proposals',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('path',nargs='?');parser.add_argument('out',nargs='?')
    parser.add_argument('--drop',type=int);parser.add_argument('--target',type=int,default=0)
    parser.add_argument('--max-pairs',type=int,default=0);parser.add_argument('--validate',action='store_true')
    a=parser.parse_args()
    if a.validate:validate()
    else:chord_search(a.path,a.out,a.drop,a.target,max_pairs=a.max_pairs)
