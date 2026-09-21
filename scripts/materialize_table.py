"""Reproduce finite witnesses covering every numerical row of the prior table.

Existing configurations retain their authorship. Exterior extensions are
checked exactly; no general extension theorem is assumed by the Lean proofs.
"""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research'/'kobon-hybrid'))
from verify_seed import F,tan_pi
from exact_geometry import primitive,arrangement
from exterior_extension import best_exterior


def materialize():
    dest=ROOT/'research'/'finite-table';dest.mkdir(exist_ok=True)
    prior=ROOT/'data'/'prior-configurations'
    simple={};classical={}
    def keep(lines,source,construction):
        lines=[primitive(l) for l in lines]
        ar=arrangement(lines);n=len(lines);T=len(ar['triangles'])
        d=dict(n=n,triangle_count=T,lines_frac=[[str(x) for x in l] for l in lines],
               source=source,construction=construction,declared_parallel_pairs=[])
        if n not in classical or T>classical[n]['triangle_count']:classical[n]=d
        if len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values()):
            if n not in simple or T>simple[n]['triangle_count']:simple[n]=d
        return d
    for p in sorted(prior.glob('gallery-*.json')):
        d=json.loads(p.read_text())
        if isinstance(d,dict) and 'lines_frac' in d:
            keep(d['lines_frac'],d.get('source',p.name),'Published gallery input; not our discovery')
    for d in json.loads((prior/'furedi-palasti-table.json').read_text()):
        keep(d['lines'],'Furedi-Palasti (1984); rational reproduction','Previously generated comparison configuration')
    for p in sorted((ROOT/'research').rglob('*.json')):
        if dest in p.parents:continue
        d=json.loads(p.read_text(encoding='utf-8-sig'))
        if isinstance(d,dict) and 'lines_frac' in d:
            keep(d['lines_frac'],p.relative_to(ROOT).as_posix(),'Existing research witness')
    # Published BBL seed coefficients; finite rational proposals are counted.
    for q,slopes,steps in [
        (6,[3,1,-7,7,-1,-3],3),
        (14,['1.66','4.4','3.28','14.4','13.1',-65,50,-45,-52,'-12.4',-22,'-4.8','-5.3','-1.86'],2)]:
        positive=[tan_pi(k,q).midpoint() for k in range(1,q//2)]
        intercepts=[-a for a in positive[::-1]]+[-F(1,100000),F(1,100000)]+positive
        mm=[F(x) for x in slopes]
        lines=[(0,1,0)]+[primitive((m,-1,m*a)) for m,a in zip(mm,intercepts)]
        sigma=1 if mm[q//2-1]>0 else -1
        for t in range(steps+1):
            expected=(q*q-1)//3
            d=keep(lines,'https://arxiv.org/html/0706.0723v1','Published BBL family; finite rational reproduction')
            assert d['triangle_count']==expected,(q,d['triangle_count'],expected)
            if t==steps:break
            pos=[tan_pi(k,2*q).midpoint() for k in range(1,q,2)]
            bs=[-a for a in pos[::-1]]+pos
            ms=[sigma*min(abs(m) for m in mm)/q**10*(2*b/(1+b*b)+1/(q**6*b)) for b in bs]
            lines.extend(primitive((m,-1,m*b)) for m,b in zip(ms,bs));mm.extend(ms);q*=2
    index=[]
    for n in range(3,61):
        if n>3:
            ar=arrangement(simple[n-1]['lines_frac'])
            gain,line,b=best_exterior(ar)
            d=keep(ar['lines']+[line],f'finite-table/simple-{n-1:03d}.json',
                   'Exact exterior extension of the retained simple witness')
            assert d['triangle_count']==len(ar['triangles'])+gain
        for kind,items in [('simple',simple),('classical',classical)]:
            d=items[n]
            (dest/f'{kind}-{n:03d}.json').write_text(json.dumps(d,indent=2)+'\n')
        index.append(dict(n=n,simple_lower=simple[n]['triangle_count'],
                          classical_lower=classical[n]['triangle_count']))
        print('TABLE',n,simple[n]['triangle_count'],classical[n]['triangle_count'],flush=True)
    old=json.loads((ROOT/'research'/'kobon-own-results'/'inventory.json').read_text())['rows']
    for r in old:
        if r['n']<=60:assert classical[r['n']]['triangle_count']>=r['lower_bound'],r
    (dest/'index.json').write_text(json.dumps(index,indent=2)+'\n')

if __name__=='__main__':materialize()
