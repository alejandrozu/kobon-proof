"""Count FP projective triangular faces by exact cyclic rows and lift parity.

An old affine row's last-to-first edge crosses infinity. Three-edge cycles
with even total wrap parity lift to closed spherical triangles. Every candidate
also has three distinct supporting lines. The coordinate chart search is a
separate numerical proposal layer and is never a symbolic all-n theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import cmp_to_key
from collections import Counter
import itertools as it,json,argparse,math,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
import numpy as np
from screen_fp_deleted_curvature import Arrangement

class SimpleArrangement:
    def __init__(self,n,shift):
        self.n=n;self.shift=shift;self.vertices=list(it.combinations(range(n),2));self.ids={p:i for i,p in enumerate(self.vertices)};self.rows=[]
        assert (3*shift).denominator!=1
        for i in range(n):
            def compare(p,q):
                if p==q:return 0
                j=next(x for x in p if x!=i);k=next(x for x in q if x!=i)
                band=(F(i+j+k)+3*shift)//n
                sine=1 if band%2==0 else -1
                return (1 if k>j else -1)*sine
            row=sorted((p for p in self.vertices if i in p),key=cmp_to_key(compare))
            assert all(compare(p,q)<0 for p,q in it.combinations(row,2))
            self.rows.append([self.ids[p] for p in row])

def projective_faces(n,shift=F(0)):
    ar=Arrangement(n) if not shift else SimpleArrangement(n,shift);adj={i:set() for i in range(len(ar.vertices))};edges={}
    for line,row in enumerate(ar.rows):
        assert len(row)>=3
        for a,b in zip(row,row[1:]):
            edge=tuple(sorted((a,b)));assert edge not in edges;edges[edge]=(line,0);adj[a].add(b);adj[b].add(a)
        a,b=row[-1],row[0];edge=tuple(sorted((a,b)));assert edge not in edges;edges[edge]=(line,1);adj[a].add(b);adj[b].add(a)
    faces=[];noncontractible=[]
    for a in adj:
        for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
            if c not in adj[b]:continue
            ab,ac,bc=[edges[tuple(sorted(e))] for e in [(a,b),(a,c),(b,c)]]
            if len(set([ab[0],ac[0],bc[0]]))<3:continue
            item=dict(vertices=[a,b,c],lines=sorted([ab[0],ac[0],bc[0]]),wrap_count=ab[1]+ac[1]+bc[1],lift_signs=[1,-1 if ab[1] else 1,-1 if ac[1] else 1])
            (faces if item['wrap_count']%2==0 else noncontractible).append(item)
    default=sum(t['wrap_count']==0 for t in faces)
    known=(n*n-3*n+3-math.gcd(n,3))//3
    if not shift:assert default==known
    return ar,faces,noncontractible

def homogeneous_vertices(n,ar):
    shift=float(getattr(ar,'shift',0))
    normals=np.array([[math.sin(math.pi*(i+shift)/n),math.cos(math.pi*(i+shift)/n),-math.sin(3*math.pi*(i+shift)/n)] for i in range(n)])
    coords=[]
    for support in ar.vertices:
        i,j=support[:2];v=np.cross(normals[i],normals[j]);assert abs(v[2])>1e-10
        if v[2]<0:v=-v
        coords.append(v/np.linalg.norm(v))
    return np.array(coords),normals

def chart_count(phi,points,faces):
    evaluation=points@np.array(phi)
    if np.min(np.abs(evaluation))<1e-12:return None
    return sum(all(t['lift_signs'][j]*evaluation[v]>0 for j,v in enumerate(t['vertices'])) or all(t['lift_signs'][j]*evaluation[v]<0 for j,v in enumerate(t['vertices'])) for t in faces)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--orders',nargs='+',type=int,default=[8,14,18,20,26,32,38,50,60]);args=ap.parse_args();results=[];start=time.time()
    for n in args.orders:
        ar,faces,noncontractible=projective_faces(n);points,normals=homogeneous_vertices(n,ar);best={'count':chart_count([0,0,1],points,faces),'phi':[0,0,1]};records=[]
        # Near an actual old line, two perturbation senses need not cut the
        # same projective triangular faces. This is a finite direction screen.
        for i in range(n):
            for side in [-1,1]:
                for eps in [1e-3,1e-5,1e-7]:
                    phi=normals[i]+np.array([0,0,side*eps]);count=chart_count(phi,points,faces)
                    if count is not None and count>best['count']:best=dict(count=count,phi=list(map(float,phi)),near_line=i,epsilon=side*eps)
        r=dict(n=n,vertices=len(ar.vertices),projective_triangles=len(faces),default_bounded=sum(t['wrap_count']==0 for t in faces),noncontractible_three_cycles=len(noncontractible),best_numerical_chart=best,wrap_count_profile=dict(Counter(t['wrap_count'] for t in faces)))
        results.append(r);print(json.dumps(r),flush=True)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/fp-projective-charts';out.mkdir(parents=True,exist_ok=True)
    (out/'initial-report.json').write_text(json.dumps(dict(results=results,seconds=time.time()-start,projective_trust='Exact cyclic row incidence and edge-lift parity',chart_trust='Floating preliminary chart count; no exact proposed chart or all-order improvement claimed'),indent=2)+'\n')

if __name__=='__main__':main()
