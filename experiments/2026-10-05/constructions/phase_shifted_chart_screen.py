"""Exploratory affine charts of the simple phase-shifted FP arrangement.
Combinatorial projective faces are selected from exact signs of sin((s+1/2)π/n).
Floating coordinates only select charts; no floating infeasibility is a theorem.
"""
import itertools as it, math, random, json, time
from pathlib import Path

def setup(n,phase):
    pairs=list(it.combinations(range(n),2));idx={p:i for i,p in enumerate(pairs)}
    pos=[0]*len(pairs);neg=[0]*len(pairs)
    for i,j,k in it.combinations(range(n),3):
        s=1 if math.floor((i+j+k+3*phase)/n)%2==0 else -1
        for pair,v,sgn in (((i,j),k,s),((i,k),j,-s),((j,k),i,s)):
            (pos if sgn>0 else neg)[idx[pair]]|=1<<v
    faces=[]
    for i,j,k in it.combinations(range(n),3):
        a,b,c=[idx[p] for p in ((i,j),(i,k),(j,k))]
        for sb,sc in it.product((0,1),repeat=2):
            if not ((pos[a]|(neg[b] if sb else pos[b])|(neg[c] if sc else pos[c])) &
                    (neg[a]|(pos[b] if sb else neg[b])|(pos[c] if sc else neg[c]))):
                faces.append((a,b,c,sb,sc))
    ls=[(math.sin(math.pi*(i+phase)/n),math.cos(math.pi*(i+phase)/n),math.sin(3*math.pi*(i+phase)/n)) for i in range(n)]
    ps=[]
    for i,j in pairs:
        a,b,c=ls[i];d,e,f=ls[j];z=a*e-b*d
        ps.append(((c*e-b*f)/z,(a*f-c*d)/z))
    return ps,faces

def search(n,phase,angles=180):
    ps,faces=setup(n,phase)
    affine=sum(not sj and not sk for _,_,_,sj,sk in faces)
    best=affine;win=None
    for ai in range(angles):
        theta=math.pi*(ai+0.237)/angles
        ax,ay=math.cos(theta),math.sin(theta)
        vals=[ax*x+ay*y for x,y in ps]
        order=sorted(range(len(ps)),key=lambda k:vals[k])
        in_face=[[] for _ in ps]
        for fi,face in enumerate(faces):
            for idx in face[:3]:in_face[idx].append(fi)
        signs=[0]*len(ps)
        good=[not sj and not sk for _,_,_,sj,sk in faces]
        score=sum(good)
        for pos,i in enumerate(order):
            for fi in in_face[i]:score-=good[fi]
            signs[i]=1
            for fi in in_face[i]:
                a,b,c,sb,sc=faces[fi];good[fi]=signs[a]==(signs[b]^sb)==(signs[c]^sc)
                score+=good[fi]
            if score>best:
                best=score;win=[theta,vals[i],pos]
    return dict(n=n,phase=phase,projective_triangles=len(faces),affine=affine,best_sampled_affine=best,chart=win,angles=angles)

if __name__=='__main__':
    rs=[]
    for n in [12,14,16,18,20,22,24,26,28,30,36,42,48,60,72,90]:
        r=search(n,1/6,120);rs.append(r);print(r,flush=True)
    Path(__file__).with_name('phase-shifted-chart-screen.json').write_text(json.dumps(rs,indent=2)+'\n')