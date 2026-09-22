"""Scan independent uniform cosets on the two real elliptic components.

Includes the direct-product torsion subgroup Z/m x Z/2, not just the cyclic
embedding in elliptic_scan.py. The projective score is a numerical filter.
Retained coordinate arrangements receive exact affine verification; candidates
require an independent exact projective census before any global assertion.
"""
import argparse,json,math,sys,time
from pathlib import Path
import numpy as np
from elliptic_scan import ellipj,ellipk,score,certify

def curve_components(na,nb,modulus,phasea,phaseb):
    e3=-(1+modulus)/3
    parts=[]
    for count,phase,component in ((na,phasea,0),(nb,phaseb,1)):
        if not count:continue
        u=2*ellipk(modulus)*(np.arange(count)+phase)/count
        sn,cn,dn,_=ellipj(u,modulus)
        if not component:
            x=e3+1/sn**2;y=-2*cn*dn/sn**3
        else:
            x=e3+modulus*sn**2;y=2*modulus*sn*cn*dn
        p=np.column_stack((x,y,np.ones(count)))
        parts.append(p/np.linalg.norm(p,axis=1)[:,None])
    return np.concatenate(parts)

def fp_projective(n):
    if n%6==0:return n*(n-3)//3
    if n%6 in (1,5):return (n*(n-3)+5)//3
    if n%6 in (2,4):return (n*(n-3)+8)//3
    return (n*(n-3)+9)//3

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--first',type=int,default=5)
    p.add_argument('--last',type=int,default=80)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args();args.out.mkdir(exist_ok=True,parents=True)
    start=time.monotonic();report=[]
    phases=(1/12,1/6,1/4,5/12,1/2,7/12,3/4,5/6,11/12)
    for n in range(args.first,args.last+1):
        best=-1;winner=None;trials=0
        splits=sorted({n//2,n//2+1,max(1,n//2-1),n//3,2*n//3})
        for na in splits:
            nb=n-na
            for modulus in (.03,.3,.7,.97):
                for a in phases:
                    for b in phases:
                        # An ABB triple is concurrent precisely when its group
                        # sum is zero. Exclude exact torsion coincidences from
                        # this simple-arrangement numerical scanner.
                        if (nb*round(12*a)+2*na*round(12*b))%(12*math.gcd(na,nb))==0:
                            continue
                        ls=curve_components(na,nb,modulus,a,b)
                        value=score(ls,projective=True);trials+=1
                        if value is not None and value>best:
                            best=value;winner=dict(na=na,nb=nb,modulus=modulus,phasea=a,phaseb=b)
        row=dict(n=n,trials=trials,best_projective_float=best,fp_projective=fp_projective(n),winner=winner)
        if best>=fp_projective(n):
            ls=curve_components(**winner);affine=score(ls)
            certify(ls,args.out/f'n{n:03d}.json',affine,dict(projective_float=best,**winner))
            row['exact_affine_count']=affine
        report.append(row)
        (args.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(row),flush=True)
    print('seconds',time.monotonic()-start,flush=True)
