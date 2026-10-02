"""Discover shared positive-dependency subsystems for the complete affine input.

Dual costs favor inequalities common to many perfect types. All output remains
heuristic until symbolic coefficient production and independent exact checking.
"""
from grid_obstruction import *


def main(source,out,epsilon=.001,seconds=180):
    out.mkdir(parents=True,exist_ok=True);start=time.time();raw=[s for s in source.read_text().splitlines()if ')'in s]
    assert len(raw)==236;triples=list(it.combinations(range(20),3));idx={t:i for i,t in enumerate(triples)}
    reflection=np.array([idx[tuple(19-x for x in reversed(t))]for t in triples]);types=[];seen={}
    for ci,word in enumerate(raw):
        n,chi=from_word(word)
        for I in range(21):
            ids,sg=free_signs(chi,I,0);caps=[]
            for i in range(19):
                cap={int(sg[idx[tuple(sorted((i,i+1,k)))]])*(1 if k<i else -1)for k in range(20)if k not in(i,i+1)}
                assert len(cap)==1;caps.append(cap.pop())
            factor=-caps[9];sg=sg*factor;caps=np.array(caps)*factor
            assert list(caps)==[(-1)**i for i in range(19)]
            refl=-sg[reflection]
            mirrored=refl.tobytes()<sg.tobytes()
            if mirrored:sg=refl
            key=sg.tobytes()
            if key not in seen:
                seen[key]=len(types);types.append(dict(class_index=ci,I=I,shift=0,sign=factor,reflection=bool(mirrored),signs=sg))
    S=np.array([r['signs']for r in types]);N=len(S);covered=np.zeros(N,dtype=bool)
    aa=np.array(sorted([math.tan(k*math.pi/20)for k in range(-9,10)if k]+[-epsilon,epsilon]))
    M=np.zeros((len(triples)+19,20));meta=[]
    for r,(i,j,k)in enumerate(triples):
        M[r,i]=aa[j]-aa[k];M[r,j]=aa[k]-aa[i];M[r,k]=aa[i]-aa[j];meta.append(['triple',i,j,k])
    for i in range(19):M[len(triples)+i,i]=(-1)**i;M[len(triples)+i,i+1]=-(-1)**i;meta.append(['cap',i,i+1])
    norms=np.max(abs(M),axis=1);base=M/norms[:,None]
    report=dict(source=str(source.resolve().relative_to(ROOT)),epsilon=epsilon,normalized_types=N,records=[],
       scope='Floating discovery and subsystem matching only; symbolic proof and exact coverage pending')
    obj=np.zeros(21);obj[-1]=-1;common=np.all(S==S[0],axis=0);commonmat=np.vstack([S[0,common,None]*base[:1140][common],base[1140:]])
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        universal=linprog(obj,A_ub=np.column_stack([-commonmat,np.ones(len(commonmat))]),b_ub=np.zeros(len(commonmat)),
            bounds=[(-1,1)]*20+[(0,1)],method='highs',options={'threads':1})
    print(json.dumps(dict(event='universal',types=N,common_rows=int(common.sum())+19,margin=float(universal.x[-1]),seconds=time.time()-start)),flush=True)
    report['common_rows']=int(common.sum())+19;report['common_margin']=float(universal.x[-1]);freq=(S>0).mean(axis=0)
    if (out/'supports.json').exists():
        previous=json.loads((out/'supports.json').read_text())
        if previous.get('epsilon')==epsilon:
            report['records']=previous['records']
            for row in report['records']:covered[row['covered_normalized_types']]=True
    for step in range(len(report['records']),N):
        if covered.all()or time.time()-start>seconds:break
        target=int(np.flatnonzero(~covered)[0]);sg=S[target];A=np.vstack([sg[:,None]*base[:1140],base[1140:]])
        popularity=np.r_[np.where(sg>0,freq,1-freq),np.ones(19)];best=None
        for power in (1,2,4):
            costs=(1-popularity)**power
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                opt=linprog(costs,A_eq=np.vstack([A.T,np.ones(len(A))]),b_eq=np.r_[np.zeros(20),1],bounds=(0,None),
                   method='highs',options={'threads':1})
            if not opt.success:continue
            active=np.flatnonzero(opt.x>1e-8);tr=active[active<1140]
            matches=np.all(S[:,tr]==sg[tr],axis=1);gain=int((matches&~covered).sum())
            if best is None or gain>best[0]:best=(gain,active,matches,opt.x[active]/norms[active])
        if best is None:
            print(json.dumps(dict(event='no_dual',target=target)),flush=True);break
        gain,active,matches,weights=best;covered|=matches
        support=[meta[i]+[int(sg[i])if i<1140 else (-1)**(i-1140)]for i in active]
        record={k:v for k,v in types[target].items()if k!='signs'}
        record.update(case_index=10000+step,support=support,weights=weights.tolist(),covered_normalized_types=np.flatnonzero(matches).tolist(),gain=gain)
        report['records'].append(record)
        report.update(covered=int(covered.sum()),uncovered=np.flatnonzero(~covered).tolist(),seconds=time.time()-start)
        if step%25==0:
            tmp=out/'supports.tmp.json';tmp.write_text(json.dumps(report,indent=2)+'\n');tmp.replace(out/'supports.json')
            print(json.dumps(dict(event='cover',certificate=step,gain=gain,covered=int(covered.sum()),total=N,support=len(active),seconds=time.time()-start)),flush=True)
    serial=[{k:v for k,v in r.items()if k!='signs'}for r in types]
    report.update(type_representatives=serial,covered=int(covered.sum()),uncovered=np.flatnonzero(~covered).tolist(),seconds=time.time()-start)
    (out/'supports.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--epsilon',type=float,default=.001);p.add_argument('--seconds',type=float,default=180)
    a=p.parse_args();main(a.source,a.out,a.epsilon,a.seconds)
