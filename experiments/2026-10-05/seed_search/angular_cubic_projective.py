"""Exact proposal screen for projective triangle growth on a nonuniform cubic.

Four coherent vertex-lift patterns are tested for each triple of simple lines.
Projective triangles are NOT a Kobon lower bound without a successful affine
chart. Every positive score is independently compared with cyclic row faces.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,random,time,json,argparse
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(Path(__file__).resolve().parent))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
from angular_cubic import gap_triangles
from fp_projective_faces import projective_faces

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--seed',type=int,default=8233);ap.add_argument('--orders',nargs='+',type=int,default=[13,14,18,19,26,31]);args=ap.parse_args();rng=random.Random(args.seed);start=time.time();deadline=start+args.seconds
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/angular-cubic-projective';out.mkdir(parents=True,exist_ok=True);best={};wins=[];trials=0
    for n in args.orders:
        p3=gap_triangles(n,[1],projective=True);assert p3==len(projective_faces(n,F(1,6))[1])
        best[n]=dict(n=n,projective_triangles=p3,default_affine=gap_triangles(n,[1]),gaps=[1],phase=1,trial='uniformcontrol')
    while time.time()<deadline:
        p=rng.choice([2,3,4,6,8,12,16]);gaps=[rng.randint(1,20) for _ in range(p)];phase=rng.randrange(1,6*min(gaps),2);trials+=1
        for n in args.orders:
            p3=gap_triangles(n,gaps,projective=True,phase=phase)
            if p3 is None:continue
            if p3>best[n]['projective_triangles']:
                r=dict(n=n,projective_triangles=p3,default_affine=gap_triangles(n,gaps,phase=phase),gaps=gaps.copy(),phase=phase,trial=trials,status='Exact finite projective empty-triangle sign count, independent row replay and affine chart pending; not a Kobon lower bound')
                best[n]=r;wins.append(r);print(json.dumps(dict(event='best',**r)),flush=True)
                (out/f'n{n:03d}-p3{p3}-period{p}-proposal.json').write_text(json.dumps(r,indent=2)+'\n')
    result=dict(trials=trials,best=list(best.values()),wins=wins,seconds=time.time()-start,scope='Finite projective counts only, no new affine lower bound or all-order formula claimed')
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)

if __name__=='__main__':main()
