"""Exact rational-interval verification of a uniform 49-line tangent-grid seed.

Discovery slopes are rounded once; all subsequent arithmetic is Fraction-only.
Machin's identity and alternating Taylor bounds enclose the actual trigonometric
constants. No floating optimizer or numerical trigonometric value is trusted.
This is a computer-assisted certificate, separate from a Lean theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,itertools as it,math,sys,hashlib,time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive
from verify_direct import verify


def add(x,y):return x[0]+y[0],x[1]+y[1]
def scale(x,k):return (x[0]*k,x[1]*k)if k>=0 else(x[1]*k,x[0]*k)
def mul(x,y):
    z=[a*b for a in x for b in y];return min(z),max(z)
def divide(x,y):
    assert y[0]>0
    return mul(x,(1/y[1],1/y[0]))
def dyadic(x,bits=160):
    denominator=2**bits
    return F(x[0]*denominator//1,denominator),F(-((-x[1]*denominator)//1),denominator)
def atan_bound(x,terms=64):
    value=sum(((-1)**j*x**(2*j+1)/F(2*j+1)for j in range(terms)),F(0))
    next_term=(-1)**terms*x**(2*terms+1)/F(2*terms+1)
    return min(value,value+next_term),max(value,value+next_term)
def trig_bound(x,sine,terms=32):
    # Interval evaluation of the Taylor polynomial, with an absolute remainder.
    degree=1 if sine else 0;power=x if sine else(F(1),F(1));square=mul(x,x);value=(F(0),F(0))
    for j in range(terms):
        value=add(value,scale(power,F((-1)**j,math.factorial(degree+2*j))))
        power=mul(power,square)
    error=power[1]/math.factorial(degree+2*terms)
    return dyadic((value[0]-error,value[1]+error),200)
def tangent_bounds():
    pi=dyadic(add(scale(atan_bound(F(1,5)),16),scale(atan_bound(F(1,239)),-4)),200)
    assert F(314,100)<pi[0]<pi[1]<F(315,100)
    return pi,[dyadic(divide(trig_bound(scale(pi,F(k,48)),True),trig_bound(scale(pi,F(k,48)),False)))for k in range(1,24)]
def encoded(iv):return [str(x)for x in iv]


def run(slopes,out):
    started=time.time();slopes=slopes.resolve();out=out.resolve();out.mkdir(parents=True,exist_ok=True);data=json.loads(slopes.read_text())
    denominator=10**10;v=[F(round(F(s)*denominator),denominator)for s in data['reciprocal_slopes']]
    assert len(v)==48 and len(set(v))==48 and all(x>0 for x in v)
    assert v[23]>v[24]  # Central apex y=2 epsilon/(v23-v24)>0.
    pi,tan=tangent_bounds();zero=(F(0),F(0));a=[scale(x,-1)for x in reversed(tan)]+[zero,zero]+tan
    coeff=[F(0)]*48;coeff[23]=-1;coeff[24]=1
    radius=F(1,100);minimum=None;rows=[]
    for i,j,k in it.combinations(range(48),3):
        constant=add(add(scale(a[i],v[k]-v[j]),scale(a[j],v[i]-v[k])),scale(a[k],v[j]-v[i]))
        assert constant[0]>0 or constant[1]<0,(i,j,k,constant)
        sign=1 if constant[0]>0 else -1;positive=scale(constant,sign)
        linear=sign*(coeff[i]*(v[k]-v[j])+coeff[j]*(v[i]-v[k])+coeff[k]*(v[j]-v[i]))
        minimum=positive[0]if minimum is None else min(minimum,positive[0])
        if linear<0:radius=min(radius,positive[0]/(-2*linear))
        rows.append([i,j,k,sign])
    simple_denominator=1
    while F(1,simple_denominator)>radius:simple_denominator*=10
    epsilon_upper=F(1,simple_denominator);epsilon=epsilon_upper/2
    assert epsilon_upper<tan[0][0]  # All Y0 crossings stay strictly ordered.
    midpoint=[sum(x)/2 for x in a];midpoint[23]=-epsilon;midpoint[24]=epsilon
    lines=[(0,1,0)]+[primitive((1,-slope,intercept))for slope,intercept in zip(v,midpoint)]
    # Every old determinant has exactly the certified sign at the sample.
    for i,j,k,sign in rows:
        det=(midpoint[j]-midpoint[k])*v[i]+(midpoint[k]-midpoint[i])*v[j]+(midpoint[i]-midpoint[j])*v[k]
        assert sign*det>0
    ar=arrangement(lines);triangles=sorted(ar['triangles']);caps=[t for t in triangles if 0 in t]
    assert len(triangles)==767 and len(caps)==47
    assert len(ar['points'])==49*48//2 and all(len(support)==2 for support in ar['points'].values())
    output=dict(n=49,triangle_count=767,lines_frac=[[str(c)for c in line]for line in lines],
        reciprocal_slopes=[str(x)for x in v],epsilon=str(epsilon),epsilon_upper=str(epsilon_upper),
        Y0_triangles=len(caps),central_apex_positive=True,
        source=str(slopes.relative_to(ROOT)),source_sha256=hashlib.sha256(slopes.read_bytes()).hexdigest(),
        trigonometric_intervals=dict(pi=encoded(pi),positive_tangents=[encoded(x)for x in tan]),
        triangles=[list(t)for t in triangles],cap_triangles=[list(t)for t in caps],
        strict_old_triple_signs=rows,minimum_zero_epsilon_determinant_lower=str(minimum),
        minimum_zero_epsilon_determinant_lower_float=float(minimum),
        uniform_epsilon_radius_float=float(radius),
        trust='Exact rational interval verification; global sign-stability argument documented separately; not yet a Lean seed theorem')
    path=out/'uniform-seed.json';path.write_text(json.dumps(output,indent=2)+'\n');output['direct']=verify(path)
    path.write_text(json.dumps(output,indent=2)+'\n')
    summary=dict(passed=True,n=49,triangles=767,caps=47,epsilon_upper=str(epsilon_upper),
        simple=True,central_apex_positive=True,all_fixed_slopes_positive=True,
        old_triple_signs=len(rows),distinct_pair_normals=48*47//2,
        exact_tangent_enclosures=23,smallest_determinant_lower=float(minimum),seconds=time.time()-started)
    (out/'verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('slopes',type=Path);parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();run(args.slopes,args.out)
