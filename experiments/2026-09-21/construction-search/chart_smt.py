"""Exact rational linear-arithmetic test for retaining all projective faces.

Z3 results here are diagnostic solver evidence, not Lean theorems. SAT results
are independently reconstructed and counted. UNSAT reports retain named face
constraints so a small obstruction can be inspected or formalized separately.
"""
import sys,json,argparse,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'experiments/2026-09-21/construction-search'))
from cusp_chart_family import build,arrangement,F,save_result,transform
from chart_optimize import projective_faces
import z3

def run(n,out,timeout=60000):
    start=time.time();lines=build(n,F(1,2));ar=arrangement(lines);ps,faces=projective_faces(ar)
    h=z3.Reals('h0 h1 h2');solver=z3.Solver();solver.set(timeout=timeout,unsat_core=True)
    for ix,face in enumerate(faces):
        vals=[s*(h[0]*p[0]+h[1]*p[1]-h[2]*p[2]) for j,s in face for p in [ps[j]]]
        solver.assert_and_track(z3.Or(z3.And([v>0 for v in vals]),z3.And([v<0 for v in vals])),f'face_{ix}')
    status=solver.check();report=dict(n=n,affine=len(ar['triangles']),projective=len(faces),
                                    result=str(status),seconds=time.time()-start,
                                    limitation='Exact QF_LRA solver evidence; UNSAT has not been checked in Lean.')
    if status==z3.unsat:
        core=[int(str(v).split('_')[1]) for v in solver.unsat_core()]
        # Greedy reduction under the same exact logic, preserving a readable
        # small obstruction when the solver returns a redundant core.
        constraints={int(str(c.arg(0)).split('_')[1]):c.arg(1) for c in solver.assertions()}
        changed=True
        while changed:
            changed=False
            for remove in core.copy():
                trial=z3.Solver();trial.set(timeout=5000)
                trial.add([constraints[ix] for ix in core if ix!=remove])
                if trial.check()==z3.unsat:core.remove(remove);changed=True
        report['core']=[dict(index=ix,vertices=[dict(point=[str(x) for x in ps[j]],
                              lines=sorted(ar['points'][ps[j]]),lift=s) for j,s in faces[ix]]) for ix in core]
    elif status==z3.sat:
        model=solver.model();hh=[F(str(model.eval(x))) for x in h]
        new=transform(lines,hh);count=len(arrangement(new)['triangles'])
        assert count==len(faces)
        save_result(str(out)+'.certificate.json',new,count,'FP half-phase arrangement',
                    'Exact SMT-found affine chart retaining every projective triangle',report)
        report['chart']=[str(x) for x in hh]
    Path(out).write_text(json.dumps(report,indent=2))
    print(json.dumps({k:v for k,v in report.items() if k!='core'} |
                     {'core_size':len(report.get('core',[]))}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('n',type=int);p.add_argument('out')
    p.add_argument('--timeout',type=int,default=60000);a=p.parse_args();run(a.n,a.out,a.timeout)
