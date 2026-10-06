"""Exact census of actual triple-core fan types and negative local weights."""
from pathlib import Path
from collections import Counter
import json,sys,itertools as it,time
ROOT=Path(__file__).resolve().parents[3];BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus';sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement
from profile_fp_boundary import profile

def local_types(lines):
    ar=arrangement(lines);cores={p for p,s in ar['points'].items() if len(s)>=3}
    if any(len(ar['points'][p])!=3 for p in cores):return None
    use=Counter();fan=Counter()
    for tri in ar['triangle_vertices']:use.update(frozenset(e) for e in it.combinations(tri,2));fan.update(tri)
    result=[]
    for p in cores:
        c=Counter();axes=[];neighbors=[]
        for i in ar['points'][p]:
            row=ar['rows'][i];idx=row.index(p)
            for j in [idx-1,idx+1]:
                if not 0<=j<len(row):c['unbounded']+=1;continue
                q=row[j];u=use[frozenset((p,q))]
                if u==0:c['unused']+=1
                elif u==1:c['single']+=1
                elif q in cores:c['core_shared']+=1;neighbors.append(q)
                else:c['ordinary_shared']+=1;axes.append(i)
        result.append(dict(core=list(map(str,p)),triangle_sectors=fan[p],ordinary_shared_axes=axes,ordinary_caps_antipodal=len(axes)==2 and axes[0]==axes[1],core_neighbors=[list(map(str,q)) for q in neighbors],**c))
    return result

def main():
    start=time.time();types=Counter();negative=[];sources=[];local_examples=[]
    def consume(profiles,source):
        lookup={tuple(p['core']):p for p in profiles}
        for p in profiles:
            d1=p.get('ordinary_shared',0);d2=p.get('core_shared',0);p=dict(p,d1=d1,d2=d2,local_weight=6-2*d1-d2,source=source)
            types[d1,d2,p['triangle_sectors']]+=1
            if p['local_weight']<0:
                p['neighbor_types']=[dict(d1=lookup[tuple(q)].get('ordinary_shared',0),d2=lookup[tuple(q)].get('core_shared',0),fan=lookup[tuple(q)]['triangle_sectors']) for q in p.get('core_neighbors',[]) if tuple(q) in lookup]
                negative.append(p)
            if d1==2 and d2==4:local_examples.append(p)
        sources.append(dict(source=source,cores=len(profiles),max_degree=max((p.get('core_shared',0) for p in profiles),default=0)))
    fp=json.loads((BASE/'fp-shared-rule.json').read_text())
    for r in fp['rows']:
        if r['n'] not in [8,14,18,20,26,32,38,48,50,60,99]:continue
        p=profile(r);consume(p['ray_profiles'],f'FP phasezero n{r["n"]}')
    data=json.loads((BASE/'triple-ordinary-shared-sanity.json').read_text());seen=set()
    for r in data['tested']:
        if not r['q'] or r['source'] in seen:continue
        seen.add(r['source']);raw=json.loads((ROOT/r['source']).read_text());ll=raw.get('lines_frac') or [(a,b,-c) for a,b,c in raw['lines']];p=local_types(ll)
        if p is not None:consume(p,r['source'])
    for name in ['antipodal-two-cap-five-sector.json']:
        raw=json.loads((BASE/name).read_text());p=local_types(raw['lines_frac']);consume(p,name)
    result=dict(types=[dict(d1=d1,d2=d2,fan=f,count=c) for (d1,d2,f),c in sorted(types.items())],sources=sources,negative_local_weight_cases=negative,d1_2_d2_4_cases=local_examples,seconds=time.time()-start,scope='Exact finite incidence profiles; antipodality means the two ordinary cap rays use the same old line. No untested classification is inferred.')
    (BASE/'triple-fan-type-census.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(types=result['types'],sources=len(sources),negative=len(negative),d1_2_d2_4=len(local_examples),antipodal_d1_2_d2_4=sum(p['ordinary_caps_antipodal'] for p in local_examples),seconds=result['seconds'])),flush=True)

if __name__=='__main__':main()
