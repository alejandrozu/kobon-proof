"""Exact-checked realizable mutations including currently unbounded cells.

This extends chamber_mutation.py by allowing any triangular projective cell
to mutate, and alternates LP blocks for offsets and normal coefficients.
The projective and affine scores are exact combinatorial sign tests. LP
realizations and promoted coordinate files are checked with exact arithmetic.
The optimization is a bounded heuristic, never an optimality certificate.
"""
from chamber_mutation import *
from chart_search import projective_faces


class ProjectiveChamber(Chamber):
    def __init__(self, lines):
        super().__init__(lines)
        self.pempty=[self.is_projective_empty(q) for q in range(len(self.triples))]
        self.pscore=sum(self.pempty)
        assert self.pscore==len(projective_faces(arrangement(lines))[1])

    def is_projective_empty(self,q):
        a,b,c=self.ts[q]
        pa,na=self.pos[a],self.neg[a]
        pb,nb=self.pos[b],self.neg[b]
        pc,nc=self.pos[c],self.neg[c]
        return (not ((pa|pb|pc)&(na|nb|nc)) or
                not ((pa|nb|pc)&(na|pb|nc)) or
                not ((pa|pb|nc)&(na|nb|pc)) or
                not ((pa|nb|nc)&(na|pb|pc)))

    def gains(self,q):
        old=sum(self.empty[r] for r in self.affected[q])
        pold=sum(self.pempty[r] for r in self.affected[q])
        self.toggle(q)
        new=sum(self.is_empty(r) for r in self.affected[q])
        pnew=sum(self.is_projective_empty(r) for r in self.affected[q])
        self.toggle(q)
        return new-old,pnew-pold

    def accept(self,q,lines):
        super().accept(q,lines)
        for r in self.affected[q]:self.pempty[r]=self.is_projective_empty(r)
        self.pscore=sum(self.pempty)

    def realize(self,q,mode='offset'):
        if mode!='normal_b':return super().realize(q,mode)
        # A determinant-one rotation changes the variable coefficient block
        # from a to b without changing any chirotope or affine triangle.
        rotated=Chamber([(b,-a,c) for a,b,c in self.current_lines])
        assert rotated.signs==self.signs
        candidate,reason=rotated.realize(q,'normal')
        if candidate is None:return None,reason
        return [(-b,a,c) for a,b,c in candidate],reason


def run_projective(path,out,seconds=600,seed=20260923,temperature=.3,
                   normal_probability=.3,projective_weight=.1,restart=200):
    start=time.time();last=start;rng=random.Random(seed)
    lines=read_lines(path);ch=ProjectiveChamber(lines)
    initial=best=ch.score;initialp=pbest=ch.pscore;bestlines=lines
    events=[];attempts=accepted=restarts=0;seen={tuple(ch.signs)};unfeasible=set()
    pbestlines=lines;lastbest=0
    print(json.dumps(dict(event='projective_mutation_start',n=ch.n,initial=initial,
          projective=ch.pscore,seed=seed,temperature=temperature)),flush=True)
    while time.time()-start<seconds:
        options=[]
        for q,v in enumerate(ch.pempty):
            if not v:continue
            gain,pgain=ch.gains(q)
            options.append((gain+projective_weight*pgain+temperature*rng.expovariate(1),gain,pgain,q))
        options.sort(reverse=True);moved=False
        for _,gain,pgain,q in options:
            if time.time()-start>=seconds:break
            if gain < -2:continue
            mode=rng.choice(('normal','normal_b')) if rng.random()<normal_probability else 'offset'
            key=(tuple(ch.signs),q,mode)
            if key in unfeasible:continue
            ch.toggle(q);nextkey=tuple(ch.signs);ch.toggle(q)
            if nextkey in seen:continue
            attempts+=1;candidate,reason=ch.realize(q,mode)
            if candidate is None:unfeasible.add(key);continue
            ch.accept(q,candidate);accepted+=1;seen.add(nextkey);moved=True
            event=dict(step=accepted,triangle=list(ch.triples[q]),gain=gain,
                       projective_gain=pgain,score=ch.score,projective=ch.pscore,
                       mode=mode,margin=reason,seconds=time.time()-start,attempts=attempts)
            events.append(event)
            if mode!='offset':ch=ProjectiveChamber(candidate)
            if ch.pscore>pbest:
                pbest=ch.pscore;pbestlines=candidate
                save_result(str(out)+'.projective.json',candidate,ch.score,str(path),
                            'Projective oriented-matroid triangle mutation',event)
                print(json.dumps(dict(event='projective_record',**event)),flush=True)
            if ch.score>best:
                best=ch.score;bestlines=candidate;lastbest=accepted
                save_result(out,candidate,best,str(path),
                            'Mixed LP realization of projective triangle-cell mutations',event)
                verify(out)
                print(json.dumps(dict(event='affine_record',**event)),flush=True)
            break
        if not moved or (restart and accepted-lastbest>=restart):
            restarts+=1;lastbest=accepted
            # Alternate the two archives, retaining the projective archive only
            # when it has improved the initial number of projective triangles.
            base=pbestlines if restarts%2 and pbest>initialp else bestlines
            ch=ProjectiveChamber(base)
            # The geometry can change while retaining the same chirotope, so
            # allow a fresh exact-checked path through a previous sign pattern.
            seen={tuple(ch.signs)};unfeasible=set()
            if not moved and len(options)==0:break
        if time.time()-last>30:
            print(json.dumps(dict(event='projective_mutation_progress',n=ch.n,best=best,
                     projective_best=pbest,current=ch.score,projective=ch.pscore,
                     accepted=accepted,attempts=attempts,restarts=restarts,seconds=time.time()-start)),flush=True)
            last=time.time()
        Path(str(out)+'.progress.json').write_text(json.dumps(dict(initial=initial,best=best,
                       projective_best=pbest,events=events),indent=2))
    report=dict(n=ch.n,source=str(path),initial=initial,best=best,initial_projective=initialp,
                best_projective=pbest,current=ch.score,current_projective=ch.pscore,
                accepted=accepted,attempts=attempts,restarts=restarts,seed=seed,
                temperature=temperature,normal_probability=normal_probability,
                projective_weight=projective_weight,restart=restart,seconds=time.time()-start,
                events=events,limitations='Bounded realizable mutation heuristic; no global optimality or priority claim.')
    Path(str(out)+'.report.json').write_text(json.dumps(report,indent=2))
    save_result(str(out)+'.last.json',ch.current_lines,ch.score,str(path),
                'Final exact-checked state of projective mutation search',
                {k:v for k,v in report.items() if k!='events'})
    print(json.dumps(dict(event='projective_mutation_done',**{k:v for k,v in report.items() if k!='events'})),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('out')
    p.add_argument('--seconds',type=float,default=600);p.add_argument('--seed',type=int,default=20260923)
    p.add_argument('--temperature',type=float,default=.3);p.add_argument('--normal-probability',type=float,default=.3)
    p.add_argument('--projective-weight',type=float,default=.1);p.add_argument('--restart',type=int,default=200)
    a=p.parse_args();run_projective(a.path,a.out,a.seconds,a.seed,a.temperature,
                          a.normal_probability,a.projective_weight,a.restart)
