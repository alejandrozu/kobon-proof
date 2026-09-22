"""Exact coordinate validation of all local resolution choices in PU seeds."""
import itertools,json,sys,time
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(Path(__file__).parent));sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from collinear_resolution import model
from collapse_search import det
from exact_geometry import arrangement,read_lines,primitive
from check_pu_current import direct_count

def main():
    root=ROOT/'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current';reports=[]
    for n in [8,14,20,26,32,38,50]:
        p=root/f'certificate-{n:03d}.json';ls=read_lines(p);rec=model(ls);private=rec['private_lines'];q=len(private)
        triples=list(itertools.combinations(range(n),3));d0={t:det(*(ls[i]for i in t))for t in triples}
        eps=F(1)
        for t in triples:
            if not d0[t]:continue
            variation=0
            for i in t:
                if i not in private:continue
                v=list(ls);a,b,c=v[i];v[i]=(a,b,c+1);variation+=abs(det(*(v[j]for j in t))-d0[t])
            if variation:eps=min(eps,F(abs(d0[t]),2*variation))
        records=[];start=time.monotonic();best=None
        for mask,bits in enumerate(itertools.product([0,1],repeat=q)):
            dd={i:2*b-1 for i,b in zip(private,bits)}
            rat=[(F(a),F(b),F(c)+eps*dd.get(i,0))for i,(a,b,c)in enumerate(ls)]
            ints=[primitive(l)for l in rat]
            for i in range(n):
                if ints[i][0]*ls[i][0]+ints[i][1]*ls[i][1]<0:ints[i]=tuple(-v for v in ints[i])
            ds={t:det(*(ints[i]for i in t))for t in triples}
            assert all(ds.values())
            assert all(ds[t]*d0[t]>0 for t in triples if d0[t])
            a=arrangement(ints);cert=dict(n=n,triangle_count=len(a['triangles']),lines_frac=[[str(x)for x in l]for l in ints])
            assert set(direct_count(cert))==set(a['triangles'])
            assert cert['triangle_count']==rec['all_resolution_counts'][mask]
            records.append(cert['triangle_count'])
            if best is None or cert['triangle_count']>best['triangle_count']:best=cert
        best.update(source=str(p.relative_to(ROOT)),construction='Exact independent offset resolution of all collinear triple points')
        (root/f'best-simple-resolution-{n:03d}.json').write_text(json.dumps(best,indent=2)+'\n')
        row=dict(n=n,source_T=rec['T'],q=q,epsilon=str(eps),all_counts=records,maximum=max(records),minimum=min(records),
            loss=rec['T']-max(records),seconds=time.monotonic()-start)
        reports.append(row);print(json.dumps(row),flush=True)
    (root/'all-local-resolutions.json').write_text(json.dumps(reports,indent=2)+'\n')

if __name__=='__main__':main()
