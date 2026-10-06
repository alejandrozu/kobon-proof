"""Bounded first-order parametric grid feasibility screens.
Numerical LP failure is NOT an exact infeasibility theorem. Positive jets
require a separate exact sign-germ certificate before promotion.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools as it,json,sys,time,math,warnings,argparse
R=Path(__file__).resolve().parents[3];sys.path.insert(0,str(R/'experiments/2026-10-05/seed_search'));sys.path.insert(0,str(R/'experiments/2026-10-02'));sys.path.insert(0,str(R/'research/kobon-hybrid'))
from word_grid_fit import tensor,chart_signs
from facet_walk61 import np,sparse,linprog,geometry
from exact_geometry import primitive

def matrices(q):
 roots=np.array(sorted([math.tan(k*math.pi/q) for k in range(-q//2+1,q//2) if k]+[0.,0.]));dr=np.zeros(q);dr[q//2-1]=-1;dr[q//2]=1
 pairs=list(it.combinations(range(q),2));triples=list(it.combinations(range(q),3));rr=[];cc=[];aa=[];bb=[]
 for row,(i,j) in enumerate(pairs):rr.extend([row,row]);cc.extend([i,j]);aa.extend([1.,-1.]);bb.extend([0.,0.])
 for row,(i,j,k) in enumerate(triples,len(pairs)):
  co=[roots[j]-roots[k],roots[k]-roots[i],roots[i]-roots[j]];dc=[dr[j]-dr[k],dr[k]-dr[i],dr[i]-dr[j]];scale=max(map(abs,co));assert scale>0
  rr.extend([row]*3);cc.extend([i,j,k]);aa.extend(c/scale for c in co);bb.extend(c/scale for c in dc)
 shape=(len(pairs)+len(triples),q)
 return roots,pairs,sparse.csr_matrix((aa,(rr,cc)),shape=shape),sparse.csr_matrix((bb,(rr,cc)),shape=shape)

def lp(c,A,b,bounds,Aeq=None,beq=None):
 with warnings.catch_warnings():
  warnings.simplefilter('ignore');return linprog(c,A_ub=A,b_ub=b,A_eq=Aeq,b_eq=beq,bounds=bounds,method='highs',options={'threads':1,'time_limit':5,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--orders',nargs='+',type=int,default=[41,45]);ap.add_argument('--axes',type=int,default=8);ap.add_argument('--seconds',type=float,default=180);a=ap.parse_args();start=time.time();out=R/'research/openmath-seven-hour-2026-10-05/constructions/parametric-grid-second-jets';out.mkdir(parents=True,exist_ok=True);records=[]
 for n in a.orders:
  q=n-1;path=R/f'work/openmath-rohith/kobon-triangles/submissions/n{n}/solution.json';raw=json.loads(path.read_text());lines=[primitive((F(x),F(y),-F(z))) for x,y,z in raw['lines']];hs=[(x,y,-z) for x,y,z in lines]+[(F(0),F(0),F(1))];entries=[]
  for i,j,k in it.combinations(range(n+1),3):
   x,y,z=hs[i];p,t,v=hs[j];s,w,h=hs[k];D=x*(t*h-v*w)-y*(p*h-v*s)+z*(p*w-t*s);assert D;entries.append(((i,j,k),1 if D>0 else-1))
  chi=tensor(n+1,entries);roots,pairs,A0,A1=matrices(q)
  for axis in range(min(n,a.axes)):
   if time.time()-start>a.seconds:break
   labels,signs=chart_signs(chi,axis,n);M0=sparse.diags(signs.astype(float))@A0;M1=sparse.diags(signs.astype(float))@A1;ranks=np.zeros(q,dtype=int)
   for z,(i,j) in enumerate(pairs):ranks[i if signs[z]>0 else j]+=1
   mi=int(np.argmin(ranks));ma=int(np.argmax(ranks));eq=np.zeros((2,q));eq[0,mi]=1;eq[1,ma]=1
   r=lp(-np.asarray(M0.sum(axis=0)).ravel(),-M0,np.zeros(M0.shape[0]),[(-1,1)]*q,eq,np.array([-1.,1.]))
   rec=dict(n=n,axis=axis,source_labels=labels,normalized_weak_status=int(r.status));records.append(rec)
   if r.success:
    u0=r.x;v0=np.asarray(M0@u0);Z=np.where(v0<1e-7)[0];rec.update(weak_residual=float(v0.min()),weak_slack_sum=float(v0.sum()),tight_rows=len(Z),u0_clusters=len(set(np.round(u0,7))))
    B=sparse.hstack([-M0[Z],np.ones((len(Z),1))],format='csr');rhs=np.asarray(M1[Z]@u0);c=np.zeros(q+1);c[-1]=-1
    r1=lp(c,B,rhs,[(-1000,1000)]*q+[(0,1)])
    rec.update(first_order_status=int(r1.status),jet_margin=float(r1.x[-1]) if r1.success else None)
    if r1.success and r1.x[-1]<=1e-7:
     cweak=-np.asarray(M0[Z].sum(axis=0)).ravel();rw=lp(cweak,-M0[Z],np.asarray(M1[Z]@u0),[(-1000,1000)]*q)
     if rw.success:
      u1=rw.x;v1=np.asarray(M0[Z]@u1+M1[Z]@u0);Z1=Z[v1<1e-6];B2=sparse.hstack([-M0[Z1],np.ones((len(Z1),1))],format='csr');rhs2=np.asarray(M1[Z1]@u1);r2=lp(c,B2,rhs2,[(-1000000,1000000)]*q+[(0,1)])
      rec.update(first_weak_residual=float(v1.min()),second_tight_rows=len(Z1),second_order_status=int(r2.status),second_margin=float(r2.x[-1]) if r2.success else None)
      if r2.success and r2.x[-1]>1e-6:
       u2=r2.x[:-1];samples=[]
       for e in[1e-3,1e-5,1e-7,1e-9]:
        uu=u0+e*u1+e*e*u2;res=np.asarray((M0+e*M1)@uu);g=geometry(roots,uu,e);samples.append(dict(epsilon=e,residual=float(res.min()),triangles=len(g['triangles']),caps=sum(0 in t for t,v in g['triangles'])))
       rec['second_samples']=samples;candidate=dict(n=n,axis=axis,u0=[str(F(float(v)).limit_denominator(10**12)) for v in u0],u1=[str(F(float(v)).limit_denominator(10**12)) for v in u1],u2=[str(F(float(v)).limit_denominator(10**12)) for v in u2],samples=samples,status='Numerical second-order jet proposal; exact leading coefficients and actual angle enclosure proof required');cp=out/f'n{n}-axis{axis}-second-jet.json';cp.write_text(json.dumps(candidate,indent=2)+'\n');rec['second_proposal']=str(cp.relative_to(R))
    if r1.success and r1.x[-1]>1e-7:
     u1=r1.x[:-1];samples=[]
     for e in[1e-3,1e-5,1e-7,1e-9]:
      uu=u0+e*u1;res=np.asarray((M0+e*M1)@uu);g=geometry(roots,uu,e);samples.append(dict(epsilon=e,residual=float(res.min()),triangles=len(g['triangles']),caps=sum(0 in t for t,v in g['triangles'])))
     rec['samples']=samples;candidate=dict(n=n,axis=axis,u0=[str(F(float(v)).limit_denominator(10**12)) for v in u0],u1=[str(F(float(v)).limit_denominator(10**12)) for v in u1],samples=samples,status='Numerical first-order jet proposal; exact leading coefficients and actual angle enclosure proof required')
     cp=out/f'n{n}-axis{axis}-jet.json';cp.write_text(json.dumps(candidate,indent=2)+'\n');rec['proposal']=str(cp.relative_to(R))
   print(json.dumps(rec),flush=True);(out/'report.json').write_text(json.dumps(dict(scope='Bounded numerical parametric LP screening, neither an exact obstruction nor a certified family',records=records,seconds=time.time()-start),indent=2)+'\n')
 print(json.dumps(dict(event='finished',cases=len(records),positive=sum('proposal'in r for r in records),seconds=time.time()-start)),flush=True)
if __name__=='__main__':main()
