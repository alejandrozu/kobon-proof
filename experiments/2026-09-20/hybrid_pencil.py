"""Optimize a compatible seed by rotating lines about their fixed grid points."""
from hybrid_relaxed_seed import *
import random,argparse


def run(path,seconds=120,seed=19073):
    data=json.loads(Path(path).read_text());n=data['n']-1;eps=F(str(data['eps']))
    mp.dps=75
    aa=sorted([F(str(mp.tan(mp.mpf(k)*mp.pi/n))) for k in range(-n//2+1,n//2) if k]+[-eps,eps])
    vv=[F(x) for x in data['v']]
    rng=random.Random(seed)
    lines=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(aa,vv)]
    ar=arrangement(lines);best=len(ar['triangles']);initial=best;bestv=vv.copy()
    normalized=[(a,v,i) for i,(a,v) in enumerate(zip(aa,vv))]
    soft,hard=rows(normalized,list(map(float,aa)))
    current=best;accepted=0;start=time.time();last=start;proposals=0;sweep=0
    print('PENCIL START',n+1,best,flush=True)
    while time.time()-start<seconds:
        ids=list(range(n));rng.shuffle(ids);changed=False
        for i in ids:
            if time.time()-start>=seconds:break
            rest=[l for j,l in enumerate(lines) if j!=i+1];sc=InsertionScore(rest)
            breaks=set([F(-10),F(10)]+[v for j,v in enumerate(vv) if j!=i])
            for x,y,z in sc.points:
                if y:breaks.add((F(x)-aa[i]*z)/y)
            br=sorted(breaks)
            samples=[((a+b)/2).limit_denominator(10**12) for a,b in zip(br,br[1:]) if not a<=vv[i]<=b]
            vals=np.array(list(map(float,samples)))
            vfloat=np.array(list(map(float,vv)))
            old=hard@vfloat-hard[:,i]*vfloat[i]
            if len(samples)==0:continue
            valid=np.max(old[:,None]+hard[:,i,None]*vals[None,:],axis=0)<-1e-11
            samples=[s for s,ok in zip(samples,valid) if ok]
            if not samples:continue
            vals=np.array(list(map(float,samples)))
            hs=np.column_stack((np.ones(len(vals)),-vals,np.full(len(vals),-float(aa[i]))))
            scores=np.concatenate([sc.scores(hs[k:k+128]) for k in range(0,len(hs),128)])
            proposals+=len(scores)
            eligible=[j for j,s in enumerate(scores) if s>=current]
            rng.shuffle(eligible);eligible.sort(key=lambda j:int(scores[j]),reverse=True)
            for j in eligible:
                candidate=primitive((1,-samples[j],aa[i]))
                exact=sc.exact_sign_score(candidate)
                if exact<current:continue
                new=lines.copy();new[i+1]=candidate
                nar=arrangement(new)
                assert exact==len(nar['triangles'])
                if len(nar['points'])!=n*(n+1)//2:continue
                if sum(0 in tri for tri in nar['triangles'])!=n-1:continue
                lines=new;vv[i]=samples[j];current=exact;accepted+=1;changed=True
                if current>best:
                    best=current;bestv=vv.copy()
                    out=data.copy();out.update(triangle_count=best,v=[str(v) for v in bestv],
                                              operation='Soft fitting plus pencil optimization on the BBL grid',
                                              pencil_seed=seed,pencil_seconds=time.time()-start)
                    dest=Path(__file__).with_name(f'pencil-seed-{n+1}.json');dest.write_text(json.dumps(out,indent=2))
                    save_result(Path(__file__).with_name(f'pencil-lines-{n+1}.json'),lines,best,str(path),out['operation'],dict(sweep=sweep))
                    print('PENCIL BEST',n+1,best,'sweep',sweep,'seconds',round(time.time()-start,2),flush=True)
                break
            if time.time()-last>20:
                print('pencil progress',n+1,'best',best,'sweep',sweep,'accepted',accepted,'seconds',round(time.time()-start,2),flush=True);last=time.time()
        sweep+=1
        if not changed:break
    report=dict(n=n+1,initial=initial,best=best,proposals=proposals,accepted=accepted,sweeps=sweep,
                seconds=time.time()-start,seed=seed)
    Path(__file__).with_name(f'pencil-report-{n+1}.json').write_text(json.dumps(report,indent=2))
    print('PENCIL DONE',report,flush=True)
    data.update(triangle_count=best,v=[str(v) for v in bestv])
    Path(__file__).with_name(f'pencil-seed-{n+1}.json').write_text(json.dumps(data,indent=2))
    double_finite(data,2)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('--seconds',type=int,default=120)
    p.add_argument('--seed',type=int,default=19073);a=p.parse_args();run(a.path,a.seconds,a.seed)
