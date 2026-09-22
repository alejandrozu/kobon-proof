"""Independently verify finite members of the classical optimal dyadic family.

The odd family is classical Tamura/BBL, not a new numerical claim.  The
exterior extension is checked from actual rational coordinates.  This script
does not substitute for a quantified geometric iteration theorem in Lean.
"""
from pathlib import Path
import argparse,json,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from verify_seed import F,tan_pi
from exact_geometry import arrangement,primitive
from verify_direct import verify
from exterior_extension import best_exterior,wedges

def main():
    p=argparse.ArgumentParser();p.add_argument('--steps',type=int,default=4)
    p.add_argument('--out',type=Path,default=Path(__file__).parent/'tamura-family')
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    # A shear normalizes the central slopes to opposite signs.
    V=list(map(F,[-15,10,-10,30]));epsilon=min(F(1,100000),F(1,16*2**args.steps))
    aa=[F(-1),-epsilon,epsilon,F(1)]
    lines=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(aa,V)]
    slopes=[1/v for v in V];q=4;records=[]
    def save(lines,count,stage,description):
        n=len(lines);start=time.monotonic();ar=arrangement(lines)
        assert len(ar['triangles'])==count,(n,len(ar['triangles']),count)
        assert len(ar['points'])==n*(n-1)//2
        data=dict(n=n,triangle_count=count,lines_frac=[[str(x) for x in l] for l in lines],
            construction=description,doubling_steps=stage,
            priority_status='Classical Tamura/BBL family and independently checked exterior extension; no numerical priority claim')
        path=args.out/f'n{n:03d}.json';path.write_text(json.dumps(data,indent=2)+'\n')
        result=verify(path);result.update(adjacency_count=count,simple=True,
            seconds=round(time.monotonic()-start,3))
        records.append(result);print(json.dumps(result),flush=True)
        return ar
    for stage in range(args.steps+1):
        count=(q*q-1)//3
        ar=save(lines,count,stage,'Classical dyadic Tamura/BBL construction from a rational compatible5-line seed')
        assert sum(0 in t for t in ar['triangles'])==q-1
        visible=sum(10*u[0]-13*u[1]>0 and 10*v[0]-13*v[1]>0 for u,v in wedges(ar))
        gain,added,free=best_exterior(ar)
        print(json.dumps(dict(n=q+1,visible_10_minus13=visible,exterior_gain=gain,free_wedges=free)),flush=True)
        assert gain==q//2,(q,gain)
        ext=save(lines+[added],count+gain,stage,'Classical dyadic odd family followed by a certified exterior addition')
        assert set(ar['triangles'])<=set(ext['triangles'])
        if stage==args.steps:break
        positive=[tan_pi(k,2*q).midpoint() for k in range(1,q,2)]
        bb=[-x for x in positive[::-1]]+positive
        minimum=min(abs(m) for m in slopes)
        mm=[minimum/F(q**10)*(2*b/(1+b*b)+1/(q**6*b)) for b in bb]
        lines += [primitive((m,-1,m*b)) for m,b in zip(mm,bb)]
        slopes += mm;q*=2
    (args.out/'verification.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':main()
