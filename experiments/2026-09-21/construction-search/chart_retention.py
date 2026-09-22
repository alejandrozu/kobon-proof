"""Exact QF_LRA test for a chart retaining a prescribed triangle count.

SAT outputs receive independent exact geometric verification. UNSAT is
solver evidence for this fixed projective arrangement, not a Lean theorem.
"""
import sys,json,time,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'experiments/2026-09-20'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import z3
from research import arrangement,read_lines,F
from chart_search import projective_faces
from chart_optimize import transform
from hybrid_search import save_result
from verify_direct import verify


def run(path,out,minimum=0,timeout=60000,core_search=False):
    start=time.time();lines=read_lines(path);ar=arrangement(lines)
    points,faces=projective_faces(ar);initial=len(ar['triangles'])
    if not minimum:minimum=initial+1
    solver=z3.SolverFor('QF_LRA');solver.set(timeout=timeout)
    hx,hy=z3.Reals('hx hy');kept=[]
    for face in faces:
        values=[]
        for index,sign in face:
            x,y,z=points[index]
            values.append(sign*(hx*int(x)+hy*int(y)-int(z)))
        kept.append(z3.Or(z3.And([v>0 for v in values]),z3.And([v<0 for v in values])))
    checks=0;cores=[]
    if core_search and minimum<=len(faces):
        labels=[z3.Bool('keep_'+str(i)) for i in range(len(faces))]
        solver.add([z3.Implies(k,v) for k,v in zip(labels,kept)])
        max_drops=len(faces)-minimum;visited=set();deadline=start+timeout/1000
        def solve(dropped):
            nonlocal checks
            key=frozenset(dropped)
            if key in visited:return z3.unsat
            visited.add(key)
            remaining=deadline-time.time()
            if remaining<=0:return z3.unknown
            solver.set(timeout=max(1,min(5000,int(1000*remaining))))
            checks+=1
            status=solver.check([k for i,k in enumerate(labels) if i not in dropped])
            if status!=z3.unsat:return status
            if len(dropped)==max_drops:return z3.unsat
            conflict=[int(str(x).split('_')[1]) for x in solver.unsat_core()]
            cores.append(conflict)
            unknown=False
            for index in conflict:
                result=solve(dropped|{index})
                if result==z3.sat:return result
                unknown|=result==z3.unknown
                if time.time()>=deadline:return z3.unknown
            return z3.unknown if unknown else z3.unsat
        result=solve(set())
    else:
        if minimum==len(faces):solver.add(kept)
        elif minimum>len(faces):solver.add(False)
        else:solver.add(z3.PbGe([(k,1) for k in kept],minimum))
        result=solver.check();checks=1
    report=dict(n=len(lines),source=str(path),initial=initial,projective=len(faces),
                minimum=minimum,result=str(result),seconds=time.time()-start,checks=checks,
                method='unsat-core branching' if core_search else 'direct pseudo-Boolean count',
                scope='Fixed projective arrangement only; UNSAT is solver evidence, not Lean-verified.')
    if result==z3.sat:
        model=solver.model()
        def rat(x):
            v=model.eval(x,model_completion=True)
            return F(v.numerator_as_long(),v.denominator_as_long())
        h=[rat(hx),rat(hy),F(1)]
        values=[h[0]*x+h[1]*y-z for x,y,z in points]
        zero=[p for p,v in zip(points,values) if not v]
        if zero:
            # Triangle retention is open. Move off any other arrangement
            # vertices while preserving every already nonzero vertex sign.
            direction=0
            while any(x+direction*y==0 for x,y,z in zero):direction+=1
            derivatives=[x+direction*y for x,y,z in points]
            eps=min([abs(v)/(2*(abs(d)+1)) for v,d in zip(values,derivatives) if v]+[F(1)])
            h[0]+=eps;h[1]+=direction*eps
            assert all(h[0]*x+h[1]*y-z for x,y,z in points)
        candidate=transform(lines,h);score=len(arrangement(candidate)['triangles'])
        assert score>=minimum
        report.update(triangles=score,chart=[str(x) for x in h])
        save_result(out,candidate,score,str(path),'Exact SMT affine-chart retention',report)
        verify(out)
    elif result==z3.unknown:report['reason']='time or solver limit' if core_search else solver.reason_unknown()
    if core_search:report['cores']=cores
    Path(str(out)+'.report.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({k:v for k,v in report.items() if k!='cores'}),flush=True)
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('out')
    p.add_argument('--minimum',type=int,default=0);p.add_argument('--timeout',type=int,default=60000)
    p.add_argument('--core-search',action='store_true')
    a=p.parse_args();run(a.path,a.out,a.minimum,a.timeout,a.core_search)
