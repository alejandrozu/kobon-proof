"""Materialize further BBL members and the fixed-normal exterior extension.

This extends a checked existing coordinate witness, not a heuristic proposal.
Both independent exact counters nevertheless recheck each saved arrangement.
"""
from pathlib import Path
import sys,json,time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from verify_seed import tan_pi,F
from exact_geometry import primitive,arrangement,read_lines
from verify_direct import verify

DEST=ROOT/'experiments/2026-09-21/hybrid-family'

def save(n,lines,count,kind):
    started=time.monotonic()
    ar=arrangement(lines)
    assert len(ar['triangles'])==count,(n,len(ar['triangles']),count)
    assert len(ar['points'])==n*(n-1)//2
    assert all(len(s)==2 for s in ar['points'].values())
    path=DEST/f'n{n:03d}.json'
    data=dict(n=n,triangle_count=count,lines_frac=[[str(x) for x in l] for l in lines],
              construction=kind,declared_parallel_pairs=[],
              priority_status='Finite certification of an already stated hybrid family; numerical priority not established')
    path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    second=verify(path)
    report=dict(n=n,triangles=count,simple=True,adjacency_count=count,direct_count=second['triangles'],
                seconds=round(time.monotonic()-started,3),path=str(path.relative_to(ROOT)))
    print(json.dumps(report),flush=True)
    return ar,report

def generate(maximum_q=640):
    DEST.mkdir(parents=True,exist_ok=True)
    lines=read_lines(ROOT/'research/kobon-hybrid/certificates/n161.json')
    q=160;reports=[]
    while q<maximum_q:
        positive=[tan_pi(k,2*q).midpoint() for k in range(1,q,2)]
        bb=[-x for x in positive[::-1]]+positive
        slopes=[F(-a,b) for a,b,c in lines[1:]]
        minimum=min(abs(m) for m in slopes)
        mm=[minimum/F(q**10)*(2*b/(1+b*b)+1/(q**6*b)) for b in bb]
        lines += [primitive((m,-1,m*b)) for m,b in zip(mm,bb)]
        q*=2
        count=(q*q-4)//3
        ar,report=save(q+1,lines,count,'Compatible eleven-line seed followed by BBL doubling')
        reports.append(report)
        (DEST/'larger-members-verification.json').write_text(json.dumps(reports,indent=2)+'\n',encoding='utf-8')
        h=1+max(F(10*p[0]-13*p[1],p[2]) for p in ar['points'])
        added=primitive((10,-13,h))
        _,report=save(q+2,lines+[added],count+q//2,'BBL odd member followed by fixed-normal (10,-13) exterior addition')
        reports.append(report)
        (DEST/'larger-members-verification.json').write_text(json.dumps(reports,indent=2)+'\n',encoding='utf-8')
    return reports

if __name__=='__main__':generate(int(sys.argv[1]) if len(sys.argv)>1 else 640)
