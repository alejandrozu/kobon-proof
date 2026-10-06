"""Exact rational interval Farkas certificate for a selected small-epsilon cell.
Scope is the exported normalized sign-constraint cell, not all arrangements.
Actual tangent interval endpoints are checked by the existing rigorous
arctangent-quarter certificate inequalities, independently in Fraction arithmetic.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json,itertools as it,math,importlib.util,time
R=Path(__file__).resolve().parents[3];sys.path.insert(0,str(R/'work/python-deps'));sys.path.insert(0,str(R/'experiments/2026-10-05/seed_search'));sys.path.insert(0,str(R/'experiments/2026-10-02'));sys.path.insert(0,str(R/'research/kobon-hybrid'))
import mpmath as mp
mp.mp.dps=90
sp=importlib.util.spec_from_file_location('jets',R/'experiments/2026-10-05/constructions/parametric_grid_jets.py');j=importlib.util.module_from_spec(sp);sp.loader.exec_module(j)
from word_grid_fit import tensor,chart_signs
from exact_geometry import primitive
np,sparse,linprog=j.np,j.sparse,j.linprog
start=time.time();n=41;q=40;d=19;axis=0
raw=json.loads((R/'work/openmath-rohith/kobon-triangles/submissions/n41/solution.json').read_text());ls=[primitive((F(a),F(b),-F(c))) for a,b,c in raw['lines']];hs=[(a,b,-c) for a,b,c in ls]+[(F(0),F(0),F(1))];entries=[]
for i,k,r in it.combinations(range(n+1),3):
 a,b,c=hs[i];v,w,x=hs[k];y,z,t=hs[r];D=a*(w*t-x*z)-b*(v*t-x*y)+c*(v*z-w*y);assert D;entries.append(((i,k,r),1 if D>0 else-1))
labels,signs=chart_signs(tensor(n+1,entries),axis,n);roots,pairs,A0,A1=j.matrices(q);M0=sparse.diags(signs.astype(float))@A0;ranks=np.zeros(q,dtype=int)
for z,(i,k) in enumerate(pairs):ranks[i if signs[z]>0 else k]+=1
mi,ma=int(np.argmin(ranks)),int(np.argmax(ranks));rg=np.zeros((1,q));rg[0,ma]=1;rg[0,mi]=-1
B=sparse.vstack([M0,sparse.csr_matrix(rg)],format='csr');rhs=np.zeros(B.shape[0]);rhs[-1]=1;obj=-rhs
EQ=sparse.vstack([B.T,sparse.csr_matrix(np.ones((1,B.shape[0])))],format='csr');eqrhs=np.r_[np.zeros(q),1.]
r=linprog(obj,A_eq=EQ,b_eq=eqrhs,bounds=[(0,None)]*B.shape[0],method='highs',options={'time_limit':30,'threads':1});assert r.success,r.message
weights={i:F(float(v)).limit_denominator(10**12) for i,v in enumerate(r.x) if v>1e-12};print('dual',len(weights),float(sum(weights.values())),float(weights.get(B.shape[0]-1,0)),flush=True)
# Certify quarter-angle tangent intervals via alternating rational atan sums.
piL=F(314159265358979323846,10**20);piU=F(314159265358979323847,10**20);tanlo=[];tanhi=[];quarters=[]
def atanpoly(x,num):return sum((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(num))
def twice(x):return 2*x/(1-x*x)
for k in range(1,d+1):
 x=F(str(mp.tan(mp.pi*k/(4*q))));D=10**22;lo=F((x*D).__floor__()-200,D);hi=F((x*D).__ceil__()+200,D)
 assert 0<=lo<1 and 0<=hi<1 and twice(hi)<1
 assert atanpoly(lo,33)<=k*piL/(4*q) and k*piU/(4*q)<=atanpoly(hi,32)
 tl,th=twice(twice(lo)),twice(twice(hi));tanlo.append(tl);tanhi.append(th);quarters.append(dict(k=k,terms=16,lo=str(lo),hi=str(hi),lower=str(tl),upper=str(th)))
rootforms=[];rootder=[]
for k in range(-(q//2-1),0):rootforms.append({abs(k)-1:F(-1)});rootder.append(F(0))
rootforms += [{},{}];rootder += [F(-1),F(1)]
for k in range(1,q//2):rootforms.append({k-1:F(1)});rootder.append(F(0))
triples=list(it.combinations(range(q),3));f=[{} for _ in range(q)];w=[F(0)]*q;selected=[]
def addform(target,form,c):
 for k,v in form.items():target[k]=target.get(k,F(0))+c*v
for row,weight in weights.items():
 if row==B.shape[0]-1:continue
 sg=F(int(signs[row]));co=[];dc=[]
 if row<len(pairs):
  i,k=pairs[row];co=[{None:F(1)},{None:F(-1)}];inds=[i,k];dc=[F(0)]*2;scale=F(1)
 else:
  i,k,t=triples[row-len(pairs)];inds=[i,k,t];scale=F(str(max(abs(roots[k]-roots[t]),abs(roots[t]-roots[i]),abs(roots[i]-roots[k]))));co=[]
  for a,b in[(k,t),(t,i),(i,k)]:
   v={};addform(v,rootforms[a],F(1));addform(v,rootforms[b],F(-1));co.append(v);dc.append(rootder[a]-rootder[b])
 for ix,cf,der in zip(inds,co,dc):addform(f[ix],cf,weight*sg/scale);w[ix]+=weight*sg*der/scale
 selected.append(dict(row=row,weight=str(weight),sign=int(signs[row]),kind='pair' if row<len(pairs) else'triple',indices=inds,scale=str(scale)))
b=weights[B.shape[0]-1];f[ma][None]=f[ma].get(None,F(0))+b;f[mi][None]=f[mi].get(None,F(0))-b
s0=F(0)
for cf in f:
 low=cf.get(None,F(0))+sum(v*(tanlo[k] if v>=0 else tanhi[k]) for k,v in cf.items() if k is not None)
 high=cf.get(None,F(0))+sum(v*(tanhi[k] if v>=0 else tanlo[k]) for k,v in cf.items() if k is not None)
 s0+=max(abs(low),abs(high))
s1=sum(abs(v) for v in w);eta=(b-s0)/(2*(1+s1));assert eta>0,(float(b),float(s0),float(s1))
record=dict(scope='Exact small-epsilon exclusion of this exported normalized sign cell, not all41-line arrangements',n=n,axis=axis,source_labels=labels,normalization=dict(min=mi,max=ma,range_at_least=1,bounds=[-1,1]),rhs=str(b),S0=str(s0),S1=str(s1),epsilon_threshold=str(eta),threshold_float=float(eta),strict_verified=b>s0+eta*s1,quarter_certificates=quarters,selected_rows=selected,coefficients=[{('constant'if k is None else str(k)):str(v) for k,v in cf.items() if v} for cf in f],epsilon_coefficients=[str(v) for v in w],seconds=time.time()-start,formal_status='Exact Fraction inequalities and generic Lean atan bridge available; concrete dual theorem replay pending')
out=R/'research/openmath-seven-hour-2026-10-05/constructions/parametric-farkas-cell41.json';out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k] for k in ['n','axis','threshold_float','strict_verified','seconds']}),flush=True)
