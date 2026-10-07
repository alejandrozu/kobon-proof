from pathlib import Path
from collections import Counter
import json,time
R=Path.cwd()
c=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
counts=Counter(x for t in c['triangles'] for x in t)

def nk(h,i,k):
 if i==2*h:return 4*k if k<h else 4*k+4
 if k==2*h:return 4*i if i<h else 4*i+4
 if i<h and k<h:
  return 4*(i+k+h)+5 if i+k<h-1 else 8*h-1 if i+k==h-1 else 4*(i+k-h)+1
 if i>=h and k>=h:
  return 4*(i+k-h)+7 if i+k<3*h-1 else -1 if i+k==3*h-1 else 4*(i+k-3*h)+3
 return 4*(i+k-h)+3 if i+k<2*h-1 else 4*h if i+k==2*h-1 else 4*(i+k-h)+5

def cap(r,j):
 if j==2*r-1:return 4*r
 if j<2*r-1:return 3*r+j//2 if j%2==0 else r+1+j//2
 return (j-2*r)//2 if j%2==0 else 2*r+(j-2*r)//2

def backward(r,i):
 if i==8*r:return 0
 if i<4*r:return (2*i+1 if i<2*r else 2*i)+1
 return (2*(i-4*r) if i-4*r<2*r else 2*(i-4*r)+1)+1
out=[]
T=1190;q=60
for depth in range(7):
 least=min(counts.values());best=[i for i in range(q+1) if counts[i]==least]
 bound=T-least;baseline=q*(q-3)//3+1
 record=dict(depth=depth,n=q+1,T=T,incidence_min=least,least_lines=best,incidence_distribution=dict(sorted(Counter(counts.values()).items())),deletion_n=q,deletion_bound=bound,baseline=baseline,gain=bound-baseline)
 out.append(record);print(record,flush=True)
 if depth==6:break
 r=q//4;raw=Counter();mix_old=Counter();mix_aux=Counter();mixed=0
 for i in range(q+1):
  for k in range(i+1,q+1):
   K=nk(q//2,i,k);j0=(K-2)//4
   for j in [j0,j0+1]:
    if 0<=j<q and abs(K-(4*j+2))<4:
     mixed+=1;mix_old[j]+=1;mix_aux[i]+=1;mix_aux[k]+=1
 for j in range(q):raw[j]=counts[j+1]+mix_old[j]
 for k in range(q+1):raw[q+k]=mix_aux[k]
 for j in range(q-1):raw[q+cap(r,j)]+=1
 counts=Counter({backward(r,i):v for i,v in raw.items()});T+=mixed;q*=2
 assert sum(counts.values())==3*T
 assert counts[0]==q-1
 print('mixed',mixed,'oldincrements',dict(Counter(mix_old.values())),'auxdist',dict(Counter(mix_aux.values())),flush=True)
(R/'research/openmath-seven-hour-2026-10-05/constructions/bbl61-incidence-transport-audit.json').write_text(json.dumps(out,indent=2)+'\n')
