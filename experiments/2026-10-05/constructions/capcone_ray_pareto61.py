"""Nonlocal reciprocal-slope ray search inside the59-axis-cap cone.
Finite floating chambers are proposals only. All certified sources stay fixed.
"""
from pathlib import Path
import os
os.environ.setdefault('OMP_NUM_THREADS','1');os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,time,itertools,importlib.util,argparse,copy
from fractions import Fraction as F
R=Path(__file__).resolve().parents[3];sys.path.insert(0,str(R/'work/construction-deps'))
import numpy as np
spec=importlib.util.spec_from_file_location('facet',R/'experiments/2026-10-05/constructions/facet_walk61_reduced.py');facet=importlib.util.module_from_spec(spec);spec.loader.exec_module(facet)
old=facet.old

def cap_matrix(roots,h):
 rows=[];q=len(h)
 for i in range(q-1):
  co=np.zeros(q);co[i]=1;co[i+1]=-1;co*=np.sign(co@h);rows.append(co)
  for k in range(q):
   if k in(i,i+1):continue
   co=np.zeros(q);co[i]=roots[i+1]-roots[k];co[i+1]=roots[k]-roots[i];co[k]=roots[i]-roots[i+1]
   scale=np.max(abs(co))
   if scale<1e-15:continue
   co/=scale;sg=np.sign(co@h)
   if not sg:continue
   rows.append(co*sg)
 return np.array(rows)

def update(g,labels,kind):
 rem=set();add=set();ids=g['pair_ids'];boundary_changed=kind=='parallel'
 if kind=='parallel':
  i,j=labels;v=ids[tuple(sorted((i,j)))]
  for line in(i,j):
   row=g['rows'][line]
   if row[0]==v:oldv,newv=row[1],row[-1]
   elif row[-1]==v:oldv,newv=row[-2],row[0]
   else:return None
   rem.add(tuple(sorted((v,oldv))));add.add(tuple(sorted((v,newv))))
 else:
  i,j,k=labels
  for line,x,y in[(i,j,k),(j,i,k),(k,i,j)]:
   a=ids[tuple(sorted((line,x)))];b=ids[tuple(sorted((line,y)))];row=g['rows'][line];ia=row.index(a);ib=row.index(b)
   if abs(ia-ib)!=1:return None
   if ia>ib:a,b=b,a;ia,ib=ib,ia
   boundary_changed |= ia==0 or ib==len(row)-1
   if ia:rem.add(tuple(sorted((row[ia-1],a))));add.add(tuple(sorted((row[ia-1],b))))
   if ib+1<len(row):rem.add(tuple(sorted((b,row[ib+1]))));add.add(tuple(sorted((a,row[ib+1]))))
 score=old.changed_score(g,labels,rem,add);score['boundary_changed']=boundary_changed
 for a,b in rem:g['adj'][a].remove(b);g['adj'][b].remove(a)
 for a,b in add:g['adj'][a].add(b);g['adj'][b].add(a)
 if kind=='parallel':
  for line in labels:
   row=g['rows'][line]
   if row[0]==v:row.pop(0);row.append(v)
   else:row.pop();row.insert(0,v)
 else:
  for line,x,y in[(i,j,k),(j,i,k),(k,i,j)]:
   a=ids[tuple(sorted((line,x)))];b=ids[tuple(sorted((line,y)))];row=g['rows'][line];ia=row.index(a);ib=row.index(b);row[ia],row[ib]=row[ib],row[ia]
 return score

def visibility(g,h):
 q=len(h);n=q+1;rank=np.empty(q,dtype=int);order=np.argsort(-h);rank[order]=np.arange(q)
 flags={}
 for i,row in enumerate(g['rows']):
  flags.setdefault(row[0],[]).append((i,-1));flags.setdefault(row[-1],[]).append((i,1))
 faces=[fs for fs in flags.values() if len(fs)==2];allvals=[];which=[]
 for sign in(1,-1):
  diff=np.zeros(n+1,dtype=int)
  for fs in faces:
   low=0;high=q
   for i,flag in fs:
    if i==0:
     if flag!=sign:high=-1;break
    elif flag==sign:low=max(low,int(rank[i-1])+1)
    else:high=min(high,int(rank[i-1]))
   if low<=high:diff[low]+=1;diff[high+1]-=1
  vals=np.cumsum(diff[:-1]);allvals.extend(vals.tolist());which.extend((sign,k) for k in range(n))
 assert sum(allvals)==q*len(faces)
 idx=int(np.argmax(allvals));sign,k=which[idx];roots=-h[order]
 value=roots[0]-1 if k==0 else roots[-1]+1 if k==q else (roots[k-1]+roots[k])/2
 return int(allvals[idx]),(sign,sign*float(value)),len(faces)

def copy_g(g):return dict(n=g['n'],pairs=g['pairs'],pair_ids=g['pair_ids'],rows=[r.copy() for r in g['rows']],adj=[x.copy() for x in g['adj']])

def main():
 p=argparse.ArgumentParser();p.add_argument('--minutes',type=float,default=90);p.add_argument('--seed',type=int,default=61021);p.add_argument('--floor',type=int,default=1183);p.add_argument('--pilot',type=int,default=0);a=p.parse_args()
 raw=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text());vals=[float((F(l)+F(h))/2) for l,h in zip(raw['lo'],raw['hi'])];roots=np.array([vals[k]*s for k,s in raw['labels'][1:]]);eps=1e-13;roots[29]=-eps;roots[30]=eps
 initial=np.array([float(1/F(m)) for m in raw['slopes'][1:]]);initial=.95*(2*(initial-initial.min())/(initial.max()-initial.min())-1);h=initial.copy();q=len(h)
 B=cap_matrix(roots,h);triples=np.array(list(itertools.combinations(range(q),3)));pairs=np.array(list(itertools.combinations(range(q),2)))
 co=np.stack([roots[triples[:,1]]-roots[triples[:,2]],roots[triples[:,2]]-roots[triples[:,0]],roots[triples[:,0]]-roots[triples[:,1]]],axis=1)
 rng=np.random.default_rng(a.seed);start=time.time();end=start+60*a.minutes;out=R/f'research/openmath-seven-hour-2026-10-05/constructions/capcone-pareto-ray-seed{a.seed}';out.mkdir(parents=True,exist_ok=True)
 g=old.geometry(roots,h,eps);T=len(g['triangles']);assert T==1190;best=1190;best_combined=1218;rays=events_total=failures=accepted=0;records=[];stagnant=0;archive=[initial.copy()]
 print(json.dumps(dict(event='start',cap_constraints=B.shape[0],initial_T=T)),flush=True)
 while time.time()<end and (not a.pilot or rays<a.pilot):
  rays+=1;d=rng.normal(size=q);d-=np.mean(d);d/=np.linalg.norm(d);bh=B@h;bd=B@d
  if min(bh)<-1e-10:raise RuntimeError('cap cone left')
  nz=abs(bd)>1e-16;limits=-bh[nz]/bd[nz];low=max(limits[bd[nz]>0].max(),np.max((-1-h[d>0])/d[d>0]),np.max((1-h[d<0])/d[d<0]));high=min(limits[bd[nz]<0].min(),np.min((1-h[d>0])/d[d>0]),np.min((-1-h[d<0])/d[d<0]));low*=.999999;high*=.999999
  dh=(co*h[triples]).sum(axis=1);dd=(co*d[triples]).sum(axis=1);pn=h[pairs[:,0]]-h[pairs[:,1]];pd=d[pairs[:,0]]-d[pairs[:,1]]
  candidates=[];rayevents=0;source_vis=visibility(g,h)
  all_events=[]
  for z in np.where(abs(dd)>1e-16)[0]:
   t=-dh[z]/dd[z]
   if low<t<high:all_events.append((float(t),'triangle',tuple(int(x)+1 for x in triples[z])))
  for z in np.where(abs(pd)>1e-16)[0]:
   t=-pn[z]/pd[z]
   if low<t<high:all_events.append((float(t),'parallel',tuple(int(x)+1 for x in pairs[z])))
  for positive in(True,False):
   ev=sorted((x for x in all_events if (x[0]>0)==positive),reverse=not positive);gg=copy_g(g);tt=T;boundary=high if positive else low;prev=0.;vv,normal,faces=source_vis
   for z,(t,kind,labels) in enumerate(ev):
    if abs(t-prev)<1e-15:failures+=1;break
    score=update(gg,labels,kind)
    if score is None:failures+=1;break
    tt+=score['delta'];rayevents+=1
    if score['cap_delta']!=0:failures+=1;break
    nxt=ev[z+1][0] if z+1<len(ev) else boundary
    mid=(t+nxt)/2
    if score['boundary_changed']:vv,normal,faces=visibility(gg,h+mid*d)
    if tt>=a.floor:candidates.append((tt,mid,vv))
    prev=t
  events_total+=rayevents
  if candidates:
   vmax=max(z[0] for z in candidates);cmax=max(z[0]+z[2] for z in candidates)
   # Prefer rare new high chambers, then explore near the current plateau.
   if vmax>best or cmax>best_combined:
    selected=[z for z in candidates if z[0]>best or z[0]+z[2]>best_combined];tt,t,vexpected=selected[rng.integers(len(selected))]
   else:
    temperature=.25+.6*((rays%300)/300);weights=np.exp(np.array([z[0]+z[2]-max(T+source_vis[0],cmax) for z in candidates])/temperature);weights/=weights.sum();tt,t,vexpected=candidates[rng.choice(len(candidates),p=weights)]
   x=h+t*d;check=old.geometry(roots,x,eps);observed=len(check['triangles']);caps=sum(0 in labels for labels,vs in check['triangles'])
   vcheck,ncheck,bcheck=visibility(check,x)
   if observed==tt and caps==59 and vcheck==vexpected:
    h=x;g=check;T=tt;accepted+=1
    if (T>=1190 or T+vcheck>=1218) and rays%5==0:archive.append(h.copy())
    if T>best or T+vcheck>best_combined:
     stable=[len(old.geometry(roots,h,e)['triangles']) for e in(1e-10,1e-12,1e-14)];stable_caps=[sum(0 in labels for labels,vs in old.geometry(roots,h,e)['triangles']) for e in(1e-10,1e-12,1e-14)]
     proposal=dict(n=61,triangle_screen=T,caps_screen=caps,epsilon_screen=str(eps),epsilon_checks=stable,cap_checks=stable_caps,reciprocal_slopes=[str(F(float(z+2)).limit_denominator(10**14)) for z in h],visible_screen=vcheck,combined_screen=T+vcheck,normal_before_shear=list(ncheck),normal_after_shear=[ncheck[0],ncheck[1]-2*ncheck[0]],reflection_required=ncheck[0]<0,status='Floating proposal; exact true-tangent interval and Lean replay required')
     path=out/f'proposal-T{T}-V{vcheck}-ray{rays:06d}.json';path.write_text(json.dumps(proposal,indent=2)+'\n');best=max(best,T);best_combined=max(best_combined,T+vcheck);print(json.dumps(dict(event='improvement',T=T,path=str(path.relative_to(R)),stable=stable)),flush=True)
   else:failures+=1
  if rays%300==0 or (T<1187 and rays%30==0):h=archive[rng.integers(len(archive))].copy();g=old.geometry(roots,h,eps);T=len(g['triangles'])
  if rays%10==0:
   rec=dict(rays=rays,events=events_total,accepted=accepted,failures=failures,current=T,best=best,best_combined=best_combined,archive=len(archive),elapsed=time.time()-start);records.append(rec);(out/'search.json').write_text(json.dumps(dict(scope='Bounded floating multi-coordinate cone-ray search, no ceiling or verified bound claim',records=records,**rec),indent=2)+'\n');print(json.dumps(rec),flush=True)
 rec=dict(event='finished',rays=rays,events=events_total,accepted=accepted,failures=failures,current=T,best=best,best_combined=best_combined,elapsed=time.time()-start);print(json.dumps(rec),flush=True);(out/'final.json').write_text(json.dumps(rec,indent=2)+'\n')
if __name__=='__main__':main()
