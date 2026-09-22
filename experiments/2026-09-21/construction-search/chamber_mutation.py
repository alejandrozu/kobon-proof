"""Coupled line-offset mutation via realizable oriented-matroid chambers.

Normals stay fixed, but a linear program moves all offsets together to cross
one triangular chamber wall while preserving every other triple orientation.
Scores are combinatorial, and every accepted realization is checked exactly.
Allowing occasional negative moves tests neighborhoods absent from the earlier
one-line, nondecreasing searches. This is a bounded heuristic, not optimality.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import sys,time,json,argparse,itertools,math,random,warnings
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'experiments/2026-09-20'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack
from research import arrangement,read_lines,primitive,F
from hybrid_search import save_result
from verify_direct import verify

def integer_preserve(values):
    values=[F(v) for v in values];den=math.lcm(*(x.denominator for x in values))
    z=[x.numerator*(den//x.denominator) for x in values];g=math.gcd(*z)
    return tuple(x//g for x in z)


class Chamber:
    def __init__(self,lines):
        self.lines=lines;self.current_lines=lines;self.n=len(lines);n=self.n
        self.triples=list(itertools.combinations(range(n),3));self.tidx={t:i for i,t in enumerate(self.triples)}
        self.pairs=list(itertools.combinations(range(n),2));self.pidx={p:i for i,p in enumerate(self.pairs)}
        self.det=[lines[i][0]*lines[j][1]-lines[i][1]*lines[j][0] for i,j in self.pairs]
        assert all(self.det)
        self.ds=[1 if d>0 else -1 for d in self.det]
        self.ts=[];self.signs=[];self.affected=[]
        self.pos=[0]*len(self.pairs);self.neg=[0]*len(self.pairs)
        for t in self.triples:
            i,j,k=t;a,b,c=lines[i];d,e,f=lines[j];g,h,l=lines[k]
            determinant=a*(e*l-f*h)-b*(d*l-f*g)+c*(d*h-e*g)
            assert determinant
            sign=1 if determinant>0 else -1;self.signs.append(sign)
            ps=[self.pidx[i,j],self.pidx[i,k],self.pidx[j,k]]
            self.ts.append(ps)
            for pair,r,s in zip(ps,(k,j,i),(-sign*self.ds[ps[0]],sign*self.ds[ps[1]],-sign*self.ds[ps[2]])):
                (self.pos if s>0 else self.neg)[pair]|=1<<r
            aff=set()
            for x,y in ((i,j),(i,k),(j,k)):
                aff.update(self.tidx[tuple(sorted((x,y,r)))] for r in range(n) if r not in (x,y))
            self.affected.append(tuple(aff))
        self.empty=[self.is_empty(q) for q in range(len(self.triples))]
        self.score=sum(self.empty)
        assert self.score==len(arrangement(lines)['triangles'])
        # Each determinant is linear in the line offsets, with fixed normals.
        normals=np.array([[float(a),float(b)] for a,b,c in lines]);self.norm=np.linalg.norm(normals,axis=1)
        normals/=self.norm[:,None]
        row=[];col=[];values=[]
        for q,(i,j,k) in enumerate(self.triples):
            ai,bi=normals[i];aj,bj=normals[j];ak,bk=normals[k]
            vv=np.array([aj*bk-bj*ak,ak*bi-bk*ai,ai*bj-bi*aj]);vv/=max(abs(vv))
            row.extend([q]*3);col.extend([i,j,k]);values.extend(vv)
        self.matrix=csr_matrix((values,(row,col)),shape=(len(self.triples),n))
        self.margin=csr_matrix(np.ones((len(self.triples),1)))

    def is_empty(self,q):
        a,b,c=self.ts[q]
        return not ((self.pos[a]|self.pos[b]|self.pos[c])&(self.neg[a]|self.neg[b]|self.neg[c]))

    def toggle(self,q):
        i,j,k=self.triples[q]
        for p,r in zip(self.ts[q],(k,j,i)):
            self.pos[p]^=1<<r;self.neg[p]^=1<<r
        self.signs[q]*=-1

    def gain(self,q):
        old=sum(self.empty[r] for r in self.affected[q]);self.toggle(q)
        new=sum(self.is_empty(r) for r in self.affected[q]);self.toggle(q)
        return new-old

    def realize(self,q,mode='offset'):
        signs=np.array(self.signs);signs[q]*=-1
        if mode=='offset':
            constraints=hstack((self.matrix.multiply(-signs[:,None]),self.margin),format='csr')
        else:
            # With b,c fixed, all triple determinants and normal determinants
            # are linear in the a-coefficients. This is a second LP block,
            # allowing collective rotations as well as collective translations.
            scales=np.array([max(map(abs,l)) for l in self.current_lines],dtype=float)
            bc=np.array([[float(F(b,max(map(abs,line)))),float(F(c,max(map(abs,line))))]
                         for line in self.current_lines for a,b,c in [line]])
            rows=[];cols=[];vv=[]
            for row,(i,j,k) in enumerate(self.triples):
                bi,ci=bc[i];bj,cj=bc[j];bk,ck=bc[k]
                v=np.array([bj*ck-cj*bk,ci*bk-bi*ck,bi*cj-ci*bj])
                if max(abs(v))<1e-14:return None,'normal-block determinant degeneracy'
                v*=(-signs[row]/max(abs(v)))
                rows.extend([row]*3);cols.extend([i,j,k]);vv.extend(v)
            base=len(self.triples)
            for pp,(i,j) in enumerate(self.pairs):
                v=np.array([bc[j,0],-bc[i,0]])
                if max(abs(v))<1e-14:return None,'normal-block parallel degeneracy'
                v*=(-self.ds[pp]/max(abs(v)))
                rows.extend([base+pp]*2);cols.extend([i,j]);vv.extend(v)
            matrix=csr_matrix((vv,(rows,cols)),shape=(base+len(self.pairs),self.n))
            constraints=hstack((matrix,csr_matrix(np.ones((matrix.shape[0],1)))),format='csr')
        obj=np.zeros(self.n+1);obj[-1]=-1
        with warnings.catch_warnings():
            warnings.simplefilter('ignore')
            result=linprog(obj,A_ub=constraints,b_ub=np.zeros(constraints.shape[0]),
                           bounds=[(-1,1)]*self.n+[(0,1)],method='highs',
                           options={'time_limit':5.0,'threads':1})
        if not result.success or result.x[-1]<1e-8:return None,result.message
        if mode=='offset':
            candidate=[integer_preserve((a,b,F(str(float(z*norm))).limit_denominator(10**12)))
                       for (a,b,c),z,norm in zip(self.lines,result.x[:-1],self.norm)]
        else:
            candidate=[integer_preserve((F(str(float(z*scale))).limit_denominator(10**12),b,c))
                       for (a,b,c),z,scale in zip(self.current_lines,result.x[:-1],scales)]
        # Independent exact orientation check guards both the LP and rounding.
        for target,(i,j,k) in zip(signs,self.triples):
            a,b,c=candidate[i];d,e,f=candidate[j];g,h,l=candidate[k]
            determinant=a*(e*l-f*h)-b*(d*l-f*g)+c*(d*h-e*g)
            if int(target)*determinant<=0:return None,'exact orientation mismatch'
        for target,(i,j) in zip(self.ds,self.pairs):
            if target*(candidate[i][0]*candidate[j][1]-candidate[j][0]*candidate[i][1])<=0:
                return None,'exact direction mismatch'
        if mode=='normal':
            for digits in (9,12,15,18):
                compact=[tuple(round(F(v,max(map(abs,l)))*10**digits) for v in l) for l in candidate]
                good=True
                for target,(i,j,k) in zip(signs,self.triples):
                    a,b,c=compact[i];d,e,f=compact[j];g,h,l=compact[k]
                    determinant=a*(e*l-f*h)-b*(d*l-f*g)+c*(d*h-e*g)
                    if int(target)*determinant<=0:good=False;break
                if good:
                    for target,(i,j) in zip(self.ds,self.pairs):
                        if target*(compact[i][0]*compact[j][1]-compact[j][0]*compact[i][1])<=0:
                            good=False;break
                if good:candidate=compact;break
        return candidate,float(result.x[-1])

    def accept(self,q,lines):
        self.toggle(q)
        for r in self.affected[q]:self.empty[r]=self.is_empty(r)
        self.score=sum(self.empty)
        assert self.score==len(arrangement(lines)['triangles'])
        self.current_lines=lines


def run(path,out,seconds=600,seed=20260922,temperature=.3,max_steps=500,normal_probability=0):
    start=time.time();last=start;rng=random.Random(seed)
    initial_lines=read_lines(path);ch=Chamber(initial_lines);initial=best=ch.score
    bestlines=initial_lines;events=[];attempts=0;accepted=0;seen={tuple(ch.signs)}
    unfeasible=set();bestchiro=tuple(ch.signs)
    print(json.dumps(dict(event='chamber_start',n=ch.n,initial=initial,seed=seed,temperature=temperature)),flush=True)
    while time.time()-start<seconds and accepted<max_steps:
        triangles=[q for q,v in enumerate(ch.empty) if v]
        options=[(ch.gain(q),rng.random(),q) for q in triangles]
        options.sort(reverse=True);moved=False
        # Randomized gain priority allows small temporary losses while retaining
        # every discovered maximum independently of the wandering state.
        ranked=sorted(options,key=lambda t:t[0]+temperature*rng.gammavariate(1,1),reverse=True)
        for gain,_,q in ranked:
            if time.time()-start>=seconds:break
            if gain < -2:continue
            mode='normal' if rng.random()<normal_probability else 'offset'
            key=(tuple(ch.signs),q,mode)
            if key in unfeasible:continue
            ch.toggle(q);nextkey=tuple(ch.signs);ch.toggle(q)
            if nextkey in seen:continue
            attempts+=1;candidate,reason=ch.realize(q,mode)
            if candidate is None:unfeasible.add(key);continue
            ch.accept(q,candidate);accepted+=1;seen.add(nextkey);moved=True
            if mode=='normal':ch=Chamber(candidate)
            event=dict(step=accepted,triangle=list(ch.triples[q]),gain=gain,score=ch.score,
                       mode=mode,margin=reason,seconds=time.time()-start,attempts=attempts)
            events.append(event)
            if ch.score>best:
                best=ch.score;bestlines=candidate;bestchiro=tuple(ch.signs)
                save_result(out,candidate,best,str(path),'Coupled LP realization of triangle-wall mutations',
                            dict(seed=seed,temperature=temperature,initial=initial,event=event))
                verify(out)
                print(json.dumps(dict(event='chamber_improvement',n=ch.n,**event)),flush=True)
            break
        if not moved:break
        if time.time()-last>30:
            print(json.dumps(dict(event='chamber_progress',n=ch.n,best=best,current=ch.score,
                                 accepted=accepted,attempts=attempts,seconds=time.time()-start)),flush=True);last=time.time()
        Path(str(out)+'.progress.json').write_text(json.dumps(dict(initial=initial,best=best,events=events),indent=2))
    report=dict(n=ch.n,source=str(path),initial=initial,best=best,current=ch.score,accepted=accepted,
                attempts=attempts,seed=seed,temperature=temperature,normal_probability=normal_probability,seconds=time.time()-start,
                events=events,limitations='Bounded fixed-normal realizable chamber search; no global optimality or priority claim.')
    Path(str(out)+'.report.json').write_text(json.dumps(report,indent=2))
    save_result(str(out)+'.last.json',ch.current_lines,ch.score,str(path),
                'Final exact-checked state of bounded chamber mutation',
                {k:v for k,v in report.items() if k!='events'})
    print(json.dumps(dict(event='chamber_done',**{k:v for k,v in report.items() if k!='events'})),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('out');p.add_argument('--seconds',type=float,default=600)
    p.add_argument('--seed',type=int,default=20260922);p.add_argument('--temperature',type=float,default=.3)
    p.add_argument('--max-steps',type=int,default=500)
    p.add_argument('--normal-probability',type=float,default=0);a=p.parse_args()
    run(a.path,a.out,a.seconds,a.seed,a.temperature,a.max_steps,a.normal_probability)
