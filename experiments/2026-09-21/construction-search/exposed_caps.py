"""Canonical exact finite checks of the exposed-cap chart construction.

These certificates use rational approximations as proposals and certify the
resulting finite arrangements independently. The all-order trigonometric proof
is separate. No floating point enters either final triangle count.
"""
import argparse,json,time
from pathlib import Path
from cusp_chart_family import build,arrangement,transform,F,save_result,verify


def make(n,dest):
    start=time.time();phase=F(1,2) if n%2 else F(1,6)
    lines=build(n,phase);ar=arrangement(lines);old=set(ar['triangles'])
    if n%2:
        vertices=sorted(ar['points'],key=lambda p:F(p[0],p[2]))
        if n%3:
            a,b=vertices[-1],vertices[-2]
            height=(F(a[0],a[2])+F(b[0],b[2]))/2
            caps=[sorted(ar['points'][a])]
        else:
            assert n>=9
            a,b=vertices[1],vertices[2]
            height=(F(a[0],a[2])+F(b[0],b[2]))/2
            caps=[sorted(ar['points'][p]) for p in vertices[:2]]
        lines=transform(lines,[1,0,height]);nar=arrangement(lines)
    else:
        caps=[];height=None;nar=ar
    new=set(nar['triangles']);count=len(new)
    expected=n*(n-3)//3+1+n%2
    assert count==expected,(n,count,expected)
    assert old<=new,(n,'an old triangle was cut')
    # Compact the finite witness for fast independent checking and Lean native
    # evaluation. This is another proposal step, accepted only after exact
    # adjacency and simplicity checks reproduce the entire triangle list.
    compact_scale=None
    for digits in (6,9,12,15,18):
        denominator=10**digits
        compact=[tuple(round(F(v,max(map(abs,line)))*denominator) for v in line) for line in lines]
        car=arrangement(compact)
        if set(car['triangles'])==new and len(car['points'])==n*(n-1)//2:
            lines=compact;nar=car;compact_scale=denominator;break
    details=dict(n=n,phase=str(phase),before=len(old),triangles=count,
                 exposed_pairs=caps,chart_height=str(height),
                 added_triangles=[list(t) for t in sorted(new-old)],
                 removed_triangles=[],compact_integer_scale=compact_scale,seconds=time.time()-start)
    path=dest/f'n{n:03d}.json'
    save_result(path,lines,count,'Classical Furedi-Palasti trigonometric family',
                'Phase choice and one- or two-cap projective chart',details)
    direct=verify(path)
    details['independent_sign_count']=direct['triangles']
    details['simple']=len(nar['points'])==n*(n-1)//2
    assert details['simple']
    return details


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--orders',default='39,47,48,51,53,54,55,59,60,99,195')
    p.add_argument('--outdir',default=str(Path(__file__).with_name('exposed-cap-certificates')))
    args=p.parse_args();dest=Path(args.outdir);dest.mkdir(exist_ok=True,parents=True)
    rows=[]
    for n in map(int,args.orders.split(',')):
        row=make(n,dest);rows.append(row);print(json.dumps(row),flush=True)
        (dest/'verification.json').write_text(json.dumps(rows,indent=2))
