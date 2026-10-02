"""Exact coupled insertion through prescribed old vertices.

Every angular chamber of a line through an old vertex is scored, including
the parallel-direction breaks. At multiple old vertices, only adjacent rays
can form a new triangle; determinant-sign compatibility checks this exactly.
The two-stage search retains a bounded, seeded sample of best first insertions
and performs complete pivot scans for each. No global optimality is asserted.
"""
from vertex_chord_insertion import *
from fractions import Fraction
from functools import cmp_to_key


def normal(a,b):
    g=math.gcd(a,b)
    if a<0 or (a==0 and b<0):g=-g
    return a//g,b//g


def normal_cmp(u,v):
    # Half-circle with a>0, plus its upper endpoint (0,1).
    return sign(u[1]*v[0]-v[1]*u[0])


class SingularInsertion:
    def __init__(self,lines):
        self.lines=list(lines);self.n=len(lines);ar=arrangement(lines)
        self.points=list(ar['points']);self.m=len(self.points);ix={p:i for i,p in enumerate(self.points)}
        self.tri=np.array([[ix[p]for p in t]for t in ar['triangle_vertices']],dtype=np.int32)
        supports=[];vertex=[];required=[]
        ds={(i,j):sign(lines[i][0]*lines[j][1]-lines[i][1]*lines[j][0]) for i in range(self.n)for j in range(self.n)if i!=j}
        assert all(ds.values()), 'parallel old lines excluded'
        slots={}
        for line,row in enumerate(ar['rows']):
            for k,p in enumerate(row):slots[ix[p],line]=(ix[row[k-1]] if k else self.m,ix[row[k+1]] if k+1<len(row)else self.m)
        left=[];right=[]
        for v,p in enumerate(self.points):
            incident=ar['points'][p]
            for i,j in it.combinations(sorted(incident),2):
                directions={ds[k,i]*ds[k,j] for k in incident if k not in (i,j)}
                req=next(iter(directions)) if len(directions)==1 else (2 if directions else 0)
                supports.append((i,j));vertex.append(v);required.append(req)
                left.append((slots[v,i][0],slots[v,j][0]));right.append((slots[v,i][1],slots[v,j][1]))
        self.supports=np.array(supports,dtype=np.int32);self.vertex=np.array(vertex,dtype=np.int32)
        self.required=np.array(required,dtype=np.int8);self.left=np.array(left,dtype=np.int32);self.right=np.array(right,dtype=np.int32)
        self.isleft=self.left==self.m;self.isright=self.right==self.m;self.initial=len(ar['triangles'])

    def score(self,line,return_key=False):
        a,b,c=line;ds=[];slopes=[]
        for A,B,C in self.lines:
            det=a*B-b*A
            if not det:return None
            ds.append(sign(det));slopes.append(sign(det*B) if B else sign(b))
        signs=np.array([sign(a*x+b*y-c*z)for x,y,z in self.points]+[0],dtype=np.int8)
        tri=signs[self.tri];retained=int(np.sum(~(np.any(tri>0,axis=1)&np.any(tri<0,axis=1))))
        sv=signs[self.vertex,None];slope=np.array(slopes,dtype=np.int8)[self.supports]
        left=signs[self.left];right=signs[self.right]
        valid=((~self.isleft)&(sv*left<=0))|((~self.isright)&(sv*right<=0))|(self.isleft&(sv*slope>0))|(self.isright&(sv*slope<0))
        d=np.array(ds,dtype=np.int8)[self.supports];sector=(self.required==0)|(self.required==d[:,0]*d[:,1])
        gained=int(np.sum((signs[self.vertex]!=0)&np.all(valid,axis=1)&sector))
        result=(retained+gained,retained,gained,int(np.sum(signs[:-1]==0)))
        if return_key:return result,signs.tobytes()+bytes(v+1 for v in ds)
        return result

    def directions(self,p):
        x,y,z=p;norms={normal(a,b)for a,b,c in self.lines}
        for u,v,w in self.points:
            a,b=y*w-z*v,z*u-x*w
            if a or b:norms.add(normal(a,b))
        return sorted(norms,key=cmp_to_key(normal_cmp))

    def pivot_lines(self,v,include_boundaries=False):
        p=self.points[v];x,y,z=p;ns=self.directions(p)
        for i,(a,b) in enumerate(ns):
            u,w=ns[i+1] if i+1<len(ns)else(-ns[0][0],-ns[0][1])
            A,B=a+u,b+w
            if A or B:yield primitive((A*z,B*z,A*x+B*y))
            if include_boundaries:yield primitive((a*z,b*z,a*x+b*y))


def sanity(model,rng):
    for q in range(8):
        line=tuple(rng.randrange(-100,101)for _ in range(3));s=model.score(line)
        if s is not None:assert len(arrangement(model.lines+[line])['triangles'])==s[0]
    for v in rng.sample(range(model.m),min(4,model.m)):
        line=next(model.pivot_lines(v));s=model.score(line)
        if s is not None:assert len(arrangement(model.lines+[line])['triangles'])==s[0]


def scan(model,rng,seconds,retain=30,minimum=0,include_boundaries=False):
    start=time.time();best=-1;count=0;pool=[];seen=set();orders=list(range(model.m));rng.shuffle(orders)
    complete=True
    for v in orders:
        for line in model.pivot_lines(v,include_boundaries):
            if time.time()-start>seconds:complete=False;break
            scored=model.score(line,True)
            if scored is None:continue
            value,key=scored;count+=1
            if value[0]<best-1 or key in seen:continue
            seen.add(key)
            if value[0]>best:
                best=value[0];pool=[a for a in pool if a[0]>=best-1]
            if best>=minimum:
                pool.append((value[0],rng.random(),line,value,v))
                pool.sort(key=lambda a:(a[0],a[1]),reverse=True);pool=pool[:retain]
        if not complete:break
    return pool,dict(candidates=count,best=best,complete_pivot_scan=complete,seconds=time.time()-start,
                     unique_near_best_topologies=len(seen),include_boundaries=include_boundaries)


def write_candidate(lines,count,path,source,metadata):
    ar=arrangement(lines);assert len(ar['triangles'])==count
    path.write_text(json.dumps(dict(n=len(lines),triangle_count=count,lines_frac=[[str(z)for z in l]for l in lines],
        source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        construction='Two-stage exact singular pivot insertion',metadata=metadata,
        verification='Exact local interval scorer, independent adjacency, independent direct sign counter'),indent=2)+'\n')
    return verify(path)


def run(source,out,seconds,width,target,seed):
    source=source.resolve();out.mkdir(parents=True,exist_ok=True);rng=random.Random(seed);start=time.time()
    model=SingularInsertion(read_lines(source));sanity(model,rng)
    pool,first=scan(model,rng,min(120,seconds/4),retain=width,include_boundaries=False)
    report=dict(source=str(source.relative_to(ROOT)),source_count=model.initial,target_order=model.n+2,
                target_count=target,seed=seed,time_limit=seconds,beam_width=width,first_scan=first,second_scans=[])
    print(json.dumps(dict(event='first_scan',**first,retained=len(pool))),flush=True)
    best=-1
    for q,item in enumerate(pool):
        if time.time()-start>=seconds:break
        first_count,priority,line,value,v=item;extended=model.lines+[line];m=SingularInsertion(extended);sanity(m,rng)
        remaining=seconds-(time.time()-start)
        second,record=scan(m,rng,remaining,retain=1,include_boundaries=True)
        record.update(index=q,first_count=first_count,first_line=[str(z)for z in line])
        if second:
            count,_,last,value,lastv=second[0]
            if count>best:
                best=count;final=extended+[last]
                record['independent_verification']=write_candidate(final,best,out/f'n{len(final):03d}-best.json',source,record)
                print(json.dumps(dict(event='record',triangles=best,index=q,first_count=first_count,seconds=time.time()-start)),flush=True)
        report['second_scans'].append(record);report['best']=best;report['seconds']=time.time()-start
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(dict(event='second_scan',index=q,**{k:v for k,v in record.items()if k not in ('first_line','independent_verification','index')})),flush=True)
        if best>=target:break
    report['scope']='Bounded first-stage beam; exact finite pivot scans of the retained configurations. No global optimality conclusion.'
    report['seconds']=time.time()-start;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(event='done',best=best,target=target,second_scans=len(report['second_scans']),seconds=time.time()-start)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=600);p.add_argument('--width',type=int,default=30)
    p.add_argument('--target',type=int,required=True);p.add_argument('--seed',type=int,default=20261002)
    a=p.parse_args();run(a.source,a.out,a.seconds,a.width,a.target,a.seed)
