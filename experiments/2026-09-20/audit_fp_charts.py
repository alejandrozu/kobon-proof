"""Explore affine charts of the published FP Example 2; exploratory floats
only select charts. Counts use the exact sign data of audit_fp_nonsimple.
"""
import itertools as it, math, random, json
from pathlib import Path

def setup(n):
    pairs=list(it.combinations(range(n),2));index={p:i for i,p in enumerate(pairs)}
    pos=[0]*len(pairs);neg=[0]*len(pairs)
    for i,j,k in it.combinations(range(n),3):
        if (i+j+k)%n==0:continue
        s=1 if ((i+j+k)//n)%2==0 else -1
        for pair,v,sign in (((i,j),k,s),((i,k),j,-s),((j,k),i,s)):
            (pos if sign>0 else neg)[index[pair]]|=1<<v
    faces=[]
    for i,j,k in it.combinations(range(n),3):
        if (i+j+k)%n==0:continue
        a,b,c=[index[p] for p in ((i,j),(i,k),(j,k))]
        for sb,sc in it.product((0,1),repeat=2):
            if not ((pos[a]|(neg[b] if sb else pos[b])|(neg[c] if sc else pos[c])) &
                    (neg[a]|(pos[b] if sb else neg[b])|(pos[c] if sc else neg[c]))):
                faces.append((a,b,c,sb,sc))
    ls=[(math.sin(math.pi*i/n),math.cos(math.pi*i/n),math.sin(3*math.pi*i/n)) for i in range(n)]
    points=[]
    for i,j in pairs:
        a,b,c=ls[i];d,e,f=ls[j];z=a*e-b*d
        points.append(((c*e-b*f)/z,(a*f-c*d)/z))
    return points,faces

if __name__=='__main__':
    rng=random.Random(192026)
    result=[]
    for n in [9,13,15,27,39,44,51,58,99,195]:
        points,faces=setup(n)
        best=-1;winner=None
        charts=[(0.,0.,1.)]
        for _ in range(3000):
            theta=rng.uniform(0,math.pi)
            charts.append((math.cos(theta),math.sin(theta),rng.uniform(-3.2,3.2)))
        for a,b,c in charts:
            values=[a*x+b*y+c for x,y in points]
            if min(abs(v) for v in values)<1e-8:continue
            signs=[int(v<0) for v in values]
            score=sum(signs[i]==(signs[j]^sj)==(signs[k]^sk) for i,j,k,sj,sk in faces)
            if score>best:best=score;winner=(a,b,c)
        record=dict(n=n,projective_triangles=len(faces),best_sampled_affine=best,chart=winner)
        result.append(record);print(record,flush=True)
    Path(__file__).with_name('audit_fp_charts.json').write_text(json.dumps(result,indent=2))
