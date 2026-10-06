"""Exact component stress test of the upper branch's marked-port budgets.

Marked means an actual shared-core ray with ordinary-shared rays immediately
before and after it in the cyclic radial order. Profiles and component costs
are checked on retained rational sources and exact FP sine-index row orders.
No general inequality is asserted from a finite screen.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from functools import cmp_to_key
import json,sys,itertools as it,time,random,argparse
ROOT=Path(__file__).resolve().parents[3];BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus'
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement
from screen_fp_deleted_curvature import Arrangement

def components(profiles):
    seen=set();result=[]
    for v in profiles:
        if v in seen:continue
        S={v};stack=[v];seen.add(v)
        while stack:
            p=stack.pop()
            for w in profiles[p]['neighbors']:
                if w not in seen:S.add(w);seen.add(w);stack.append(w)
        D1=sum(profiles[v]['d1'] for v in S);D2=sum(profiles[v]['d2'] for v in S)//2
        A=sum(profiles[v]['d1']==2 and profiles[v]['d2']==4 and profiles[v]['marked']==0 for v in S);B=sum(profiles[v]['d1']==1 and profiles[v]['d2']==5 for v in S);E=sum(profiles[v]['d1']==3 for v in S);P=sum(profiles[v]['d1']==2 and profiles[v]['d2']==1 for v in S);cost=3*len(S)-D1-D2
        result.append(dict(vertices=len(S),D1=D1,D2=D2,A24=A,B15=B,E3=E,P21=P,localCost=cost,corrected_cost=cost+2*A+B,sharp_slack=2*cost+2*A+B-3*E-3*P,
            profiles=[dict(vertex=str(v),**{k:z for k,z in profiles[v].items() if k!='neighbors'},neighbors=list(map(str,profiles[v]['neighbors']))) for v in S]))
    return result

def rational_profiles(lines):
    ar=arrangement(lines);lines=ar['lines'];cores={p for p,s in ar['points'].items() if len(s)>=3}
    if any(len(ar['points'][p])!=3 for p in cores):return None
    if any(a*e-b*d==0 for (a,b,c),(d,e,f) in it.combinations(lines,2)):return None
    use=Counter();fan=Counter()
    for tri in ar['triangle_vertices']:use.update(frozenset(e) for e in it.combinations(tri,2));fan.update(tri)
    def cmp(r,s):
        x,y=r['direction'];u,v=s['direction'];half=lambda x,y:0 if y>0 or (y==0 and x>=0) else 1;h,h2=half(x,y),half(u,v)
        if h!=h2:return h-h2
        return -((x*v-y*u>0)-(x*v-y*u<0))
    profiles={}
    for p in cores:
        rays=[]
        for i in ar['points'][p]:
            row=ar['rows'][i];idx=row.index(p);a,b,c=lines[i];d=(b,-a)
            if (b and b<0) or (not b and -a<0):d=(-d[0],-d[1])
            for side in [-1,1]:
                j=idx+side;q=row[j] if 0<=j<len(row) else None;u=use[frozenset((p,q))] if q is not None else -1;t=4 if u==2 and q in cores else 3 if u==2 else u+1
                rays.append(dict(direction=(side*d[0],side*d[1]),type=t,neighbor=q))
        rays.sort(key=cmp_to_key(cmp));types=[r['type'] for r in rays];d1=types.count(3);d2=types.count(4);marked=sum(types[j]==4 and types[(j-1)%6]==3 and types[(j+1)%6]==3 for j in range(6));neighbors=[r['neighbor'] for r in rays if r['type']==4]
        profiles[p]=dict(d1=d1,d2=d2,marked=marked,fan=fan[p],radial_types=types,neighbors=neighbors)
    return components(profiles)

def fp_profiles(A,S):
    r=A.ledger(S,True);cores={int(v) for v,s in r['actual_vertex_supports'].items() if len(s)==3};use={tuple(e['vertices']):e['use'] for e in r['edge_use']};rowmap=dict(zip(sorted(S),r['ordered_rows']));fan=Counter(v for tri in r['triangle_vertices'] for v in tri);profiles={}
    for p in cores:
        support=sorted(r['actual_vertex_supports'][str(p)],reverse=True);rays=[]
        for side in [-1,1]:
            for i in support:
                row=rowmap[i];idx=row.index(p);j=idx+side;q=row[j] if 0<=j<len(row) else None;u=use[tuple(sorted((p,q)))] if q is not None else -1;t=4 if u==2 and q in cores else 3 if u==2 else u+1;rays.append((t,q))
        types=[t for t,q in rays];profiles[p]=dict(d1=types.count(3),d2=types.count(4),marked=sum(types[j]==4 and types[(j-1)%6]==3 and types[(j+1)%6]==3 for j in range(6)),fan=fan[p],radial_types=types,neighbors=[q for t,q in rays if t==4])
    return components(profiles)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=150);args=ap.parse_args();start=time.time();records=[];violations=[];types=Counter();minimum=None;minsharp=None;negative_adjacencies=Counter();rng=random.Random(6137)
    def consume(cc,source):
        global minimum,minsharp
        if cc is None:return
        for c in cc:
            c['source']=source
            if minimum is None or c['corrected_cost']<minimum['corrected_cost']:minimum=c
            if minsharp is None or c['sharp_slack']<minsharp['sharp_slack']:minsharp=c
            if c['corrected_cost']<1 or c['sharp_slack']<0:violations.append(c)
            lookup={p['vertex']:p for p in c['profiles']}
            for p in c['profiles']:
                types[p['d1'],p['d2'],p['marked']]+=1
                if 6-2*p['d1']-p['d2']<0:
                    for w in p['neighbors']:
                        q=lookup[w];negative_adjacencies[p['d1'],p['d2'],q['d1'],q['d2']]+=1
        records.append(dict(source=source,components=len(cc),min_corrected=min((c['corrected_cost'] for c in cc),default=None),min_sharp=min((c['sharp_slack'] for c in cc),default=None)))
    data=json.loads((BASE/'triple-ordinary-shared-sanity.json').read_text());seen=set()
    for r in data['tested']:
        if not r['q'] or r['source'] in seen:continue
        seen.add(r['source']);raw=json.loads((ROOT/r['source']).read_text());ll=raw.get('lines_frac') or [(a,b,-c) for a,b,c in raw['lines']];consume(rational_profiles(ll),r['source'])
    for name in ['antipodal-two-cap-five-sector.json','antipodal-full-two-cap-fan.json','four-line-first-budget-counterexample.json']:
        raw=json.loads((BASE/name).read_text());consume(rational_profiles(raw['lines_frac']),name)
    for n in [8,14,18,24,30,36,42,48,54,60,99]:
        if time.time()-start>args.seconds or violations:break
        A=Arrangement(n);consume(fp_profiles(A,range(n)),f'FP{n} full')
        for trial in range(90):
            if time.time()-start>args.seconds or violations:break
            S=rng.sample(range(n),rng.randint(max(6,n//2),n-1));consume(fp_profiles(A,S),f'FP{n} subset seed6137 trial{trial} labels{S}')
    out=dict(passed=not violations,records=records,arrangements=len(records),minimum_corrected=minimum,minimum_sharp=minsharp,violations=violations,types=[dict(d1=a,d2=b,marked=c,count=n) for (a,b,c),n in sorted(types.items())],negative_adjacencies=[dict(d1=a,d2=b,neighbor_d1=c,neighbor_d2=d,count=n) for (a,b,c,d),n in sorted(negative_adjacencies.items())],seconds=time.time()-start,scope='Exact rational retained sources and exact FP incidence/row order, actual radial marks; finite screen only, no general proof')
    (BASE/'marked-component-curvature.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['passed','arrangements','minimum_corrected','minimum_sharp','violations','types','negative_adjacencies','seconds']}),flush=True)
