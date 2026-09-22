"""Exhaust all four simple local chirotopes at Maiorana's two-triple seed.

Only offsets change. Every originally nonzero 3x3 determinant retains its
exact sign, so this describes all local simple resolution types, independently
of a global simple-arrangement upper theorem.
"""
import itertools,json,sys
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from exact_geometry import arrangement,primitive
from verify_direct import verify
OUT=ROOT/'research/six-hour-2026-09-21/general-bounds/maiorana14'

def det(a,b,c):
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])

def main():
    src=json.loads((OUT/'certificate-01.json').read_text())
    ls=[tuple(map(F,l))for l in src['lines_frac']]
    ts=list(itertools.combinations(range(14),3))
    d0={t:det(*(ls[i]for i in t))for t in ts}
    zeros=[t for t,d in d0.items()if not d]
    assert zeros==[(0,4,10),(0,11,12)]
    reports=[]
    for s1,s2 in itertools.product([-1,1],repeat=2):
        direction=[F(0)]*14;direction[4]=F(s1);direction[11]=F(s2)
        unit=[(a,b,c+direction[i])for i,(a,b,c)in enumerate(ls)]
        dd={t:det(*(unit[i]for i in t))-d0[t]for t in ts}
        eps=min([F(1,1000)]+[abs(d0[t]/dd[t])/2 for t in ts if d0[t] and dd[t]])
        pert=[(a,b,c+eps*direction[i])for i,(a,b,c)in enumerate(ls)]
        dz={t:det(*(pert[i]for i in t))for t in ts}
        assert all(dz[t] for t in ts)
        assert all(d0[t]*dz[t]>0 for t in ts if d0[t])
        ar=arrangement(pert);count=len(ar['triangles'])
        zero_signs=[1 if dz[t]>0 else -1 for t in zeros]
        certificate=dict(n=14,triangle_count=count,lines_frac=[[str(z)for z in l]for l in pert],
            triangles=[list(t)for t in ar['triangles']],attribution=src['attribution'],
            source='Exact small offset perturbation of Maiorana solution1',
            offset_signs=[s1,s2],resolved_triple_signs=zero_signs,epsilon=str(eps))
        path=OUT/f'resolution-{s1:+d}-{s2:+d}.json';path.write_text(json.dumps(certificate,indent=2)+'\n')
        verify(path)
        old=set(map(tuple,src['triangles']));new=set(ar['triangles'])
        reports.append(dict(offset_signs=[s1,s2],resolved_triple_signs=zero_signs,triangles=count,
            epsilon=str(eps),old_survived=len(old&new),old_lost=sorted(old-new),new_triangles=sorted(new-old)))
    assert len(set(tuple(r['resolved_triple_signs'])for r in reports))==4
    report=dict(source_triangles=54,source_triples=zeros,resolutions=reports,
        maximum_local_simple_triangles=max(r['triangles']for r in reports),
        method='All originally nonzero determinants preserve exact signs; both zero determinant signs independently exhausted.')
    (OUT/'resolutions.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
