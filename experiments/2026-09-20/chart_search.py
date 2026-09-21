"""Exact search over affine charts of a fixed real projective arrangement.

Projective faces are triangles made of consecutive cyclic line segments;
the number of wrapped sides must be even. Candidate chart boundaries are
dual vertices, with each adjacent open cell examined by symbolic perturbation.
"""
from research import *
import sys

def projective_faces(ar):
    ps=sorted(ar['points']);ix={p:i for i,p in enumerate(ps)}
    edges={};neighbors=defaultdict(set)
    for line,row in enumerate(ar['rows']):
        assert len(row)>3
        for k,(p,q) in enumerate(zip(row,row[1:]+row[:1])):
            u,v=ix[p],ix[q];edges[frozenset((u,v))]=(line,k==len(row)-1)
            neighbors[u].add(v);neighbors[v].add(u)
    faces=[]
    for u,adj in neighbors.items():
        for v,w in it.combinations(sorted(x for x in adj if x>u),2):
            e3=edges.get(frozenset((v,w)))
            if e3 is None:continue
            e1=edges[frozenset((u,v))];e2=edges[frozenset((u,w))]
            if len({e1[0],e2[0],e3[0]})<3:continue
            if (e1[1]+e2[1]+e3[1])%2:continue
            faces.append(((u,1),(v,-1 if e1[1] else 1),(w,-1 if e2[1] else 1)))
    assert sum(all(s==1 for i,s in f) for f in faces)==len(ar['triangles'])
    return ps,faces

def through(p,q):
    x,y,z=p;u,v,w=q
    return primitive((y*w-z*v,z*u-x*w,y*u-x*v))

def transform(lines,h):
    a,b,c=h
    assert c
    return [primitive((c*A-C*a,c*B-C*b,-C)) for A,B,C in lines]

def search(path,limit=0):
    ar=arrangement(read_lines(path));ps,faces=projective_faces(ar)
    best=len(ar['triangles']);seen=set();win=None
    print('n',len(ar['lines']),'vertices',len(ps),'projective faces',len(faces),'initial',best,flush=True)
    for pairno,(p,q) in enumerate(it.combinations(ps,2)):
        h=through(p,q)
        if h in seen:continue
        seen.add(h);a,b,c=h
        signs=[];zeros=[]
        for i,(x,y,z) in enumerate(ps):
            val=a*x+b*y-c*z
            signs.append(1 if val>0 else -1 if val<0 else 0)
            if not val:zeros.append(i)
        fixed=0;clauses=[]
        for face in faces:
            values=[s*signs[i] for i,s in face if signs[i]]
            if not values or any(v!=values[0] for v in values):continue
            needs=[(i,s*values[0]) for i,s in face if not signs[i]]
            if not needs:fixed+=1
            else:clauses.append(needs)
        if fixed+len(clauses)<=best:continue
        axis=0 if b else 1
        zeros.sort(key=lambda i:F(ps[i][axis],ps[i][2]))
        for initial in (-1,1):
            assignment={i:initial for i in zeros}
            for pos in range(len(zeros)+1):
                score=fixed+sum(all(assignment[i]==s for i,s in clause) for clause in clauses)
                if score>best:
                    best=score;win=(h,zeros.copy(),axis,initial,pos)
                    print('BEST',best,'charts examined',len(seen),'zero vertices',len(zeros),flush=True)
                if pos<len(zeros):assignment[zeros[pos]]*=-1
        if limit and len(seen)>=limit:break
    print('DONE best',best,'distinct chart boundary vertices',len(seen),flush=True)
    if win:
        h,zeros,axis,initial,pos=win
        vals=[F(ps[i][axis],ps[i][2]) for i in zeros]
        threshold=vals[0]-1 if pos==0 else vals[-1]+1 if pos==len(vals) else (vals[pos-1]+vals[pos])/2
        k=[F(0),F(0),threshold];k[axis]=1;k=[initial*v for v in k]
        a,b,c=h;ka,kb,kc=k
        eps=min(abs(F(a*x+b*y-c*z))/(2*(abs(ka*x+kb*y-kc*z)+1)) for x,y,z in ps if a*x+b*y-c*z)
        newh=primitive([x+eps*y for x,y in zip(h,k)])
        ls=transform(ar['lines'],newh)
        exact=len(arrangement(ls)['triangles']);assert exact==best,(exact,best)
        out=dict(n=len(ls),triangle_count=best,source=path,chart=[str(x) for x in newh],lines_frac=[[str(x) for x in l] for l in ls])
        Path(__file__).with_name('chart-'+Path(path).name).write_text(json.dumps(out,indent=2))

if __name__=='__main__':search(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 0)
