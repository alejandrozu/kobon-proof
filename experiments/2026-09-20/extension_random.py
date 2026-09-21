from extension_audit import *
import random, sys, time

rng=random.Random(200926)
ns=list(map(int,sys.argv[1:])) or [5,6,7,8,9]
for n in ns:
    for trial in range(100):
        while True:
            lines=[(i,-1,rng.randrange(-1000,1001)) for i in range(n)]
            ar=arrangement(lines)
            if all(len(s)==2 for s in ar['points'].values()):break
        old=set(ar['triangles']);target=len(old)+n//2
        tris=ar['triangle_vertices']
        max_preserving=0;win=None;sampled=0
        for line in line_samples(ar):
            sampled+=1
            a,b,c=line
            if any(min(a*x+b*y-c*z for x,y,z in t)<0<max(a*x+b*y-c*z for x,y,z in t) for t in tris):continue
            tri=set(arrangement(lines+[line])['triangles'])
            if old<=tri and len(tri)>max_preserving:
                max_preserving=len(tri);win=line
                if len(tri)>=target:break
        if max_preserving<target:
            result=dict(n=n,trial=trial,triangles=len(old),maximum_preserving=max_preserving,
                lines=lines,witness=win,samples=sampled)
            Path(__file__).with_name('counterexample-append.json').write_text(json.dumps(result,indent=2))
            print('FAIL',json.dumps(result),flush=True);sys.exit(0)
        if trial%10==0:print(n,trial,'old',len(old),'gain',max_preserving-len(old),flush=True)
print('No counterexample found.',flush=True)
