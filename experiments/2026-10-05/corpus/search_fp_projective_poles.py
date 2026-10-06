"""Screen every vertex of the dual FP pole arrangement and adjacent sectors.

Projective triangle incidences/lift signs come from the exact cyclic-row audit.
Coordinates and dual-cell enumeration are floating diagnostics. A positive pole
must receive an independent exact algebraic/interval verification before use.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,itertools as it,time,json,math,argparse
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fp_projective_faces import np,projective_faces,homogeneous_vertices,chart_count

def search(n,seconds,shift=F(0)):
    start=time.time();ar,faces,nc=projective_faces(n,shift);points,normals=homogeneous_vertices(n,ar)
    vertices=np.array([t['vertices'] for t in faces]);lifts=np.array([t['lift_signs'] for t in faces]);best=dict(count=sum(t['wrap_count']==0 for t in faces),phi=[0,0,1]);tested=0;seen=set();degenerate=0;hist={}
    def count_signs(signs):
        ss=signs[vertices]*lifts
        return int(np.sum(np.all(ss>0,axis=1)|np.all(ss<0,axis=1)))
    for i,j in it.combinations(range(len(points)),2):
        if time.time()-start>seconds:break
        pole=np.cross(points[i],points[j]);size=np.linalg.norm(pole)
        if size<1e-12:continue
        pole/=size
        if pole[np.argmax(np.abs(pole))]<0:pole=-pole
        key=tuple(np.round(pole,11))
        if key in seen:continue
        seen.add(key);value=points@pole;zeros=np.where(np.abs(value)<1e-9)[0];assert i in zeros and j in zeros
        if len(zeros)>2:degenerate+=1
        u=points[i];u/=np.linalg.norm(u);v=np.cross(pole,u);v/=np.linalg.norm(v)
        au=points[zeros]@u;av=points[zeros]@v
        roots=sorted(set(round(float(math.atan2(-a,b)%(2*math.pi)),12) for a,b in zip(au,av))|set(round(float((math.atan2(-a,b)+math.pi)%(2*math.pi)),12) for a,b in zip(au,av)))
        for r,s in zip(roots,roots[1:]+[roots[0]+2*math.pi]):
            if s-r<1e-8:continue
            angle=(r+s)/2;direction=math.cos(angle)*u+math.sin(angle)*v
            derivative=points@direction;sg=np.sign(value);sg[zeros]=np.sign(derivative[zeros]);assert all(sg)
            count=count_signs(sg);tested+=1;hist[count]=hist.get(count,0)+1
            if count>best['count']:
                nonzero=np.ones(len(points),dtype=bool);nonzero[zeros]=False
                ratios=np.abs(value[nonzero])/(2*np.maximum(np.abs(derivative[nonzero]),1e-100));step=min(0.00001,float(np.min(ratios)))
                phi=pole+step*direction;actual=chart_count(phi,points,faces);assert actual==count
                rational=[str(F(float(x)).limit_denominator(10**12)) for x in phi]
                best=dict(count=count,phi=list(map(float,phi)),rational_phi=rational,min_vertex_abs_eval=float(np.min(np.abs(points@phi))),wall_vertices=[i,j],wall_concurrency=len(zeros),step=step)
                print(json.dumps(dict(event='best',n=n,**best)),flush=True)
    return dict(n=n,shift=str(shift),projective_triangles=len(faces),default=sum(t['wrap_count']==0 for t in faces),current_G=n*(n-3)//3+1+n%2,best_numerical=best,unique_poles=len(seen),adjacent_cells=tested,degenerate_poles=degenerate,histogram=hist,seconds=time.time()-start,scope='Floating full/partial dual arrangement cell screen with exact projective triangle combinatorics; no exact new chart or universal maximum theorem')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--orders',nargs='+',type=int,default=[8,14,18,20,26]);ap.add_argument('--seconds-per-order',type=float,default=120);ap.add_argument('--shift',default='0');args=ap.parse_args();shift=F(args.shift)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/fp-projective-charts';out.mkdir(parents=True,exist_ok=True);results=[]
    for n in args.orders:
        r=search(n,args.seconds_per_order,shift);results.append(r);print(json.dumps(dict(event='finish',**r)),flush=True)
        name='dual-cell-report.json' if not shift else f'dual-cell-report-shift{str(shift).replace("/","_")}.json'
        (out/name).write_text(json.dumps(dict(results=results,trust='Numerical chart screen, exact incidence inputs; positive poles need a separate exact verification'),indent=2)+'\n')

if __name__=='__main__':main()
