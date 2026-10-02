"""Produce exact symbolic positive dependencies over Q(tan(pi/20))[epsilon].

A nonzero nonnegative dependence sum w_i A_i = 0 makes simultaneous strict
inequalities A_i v > 0 impossible. Signs are checked by the leading nonzero
epsilon coefficient, giving a punctured right neighborhood of zero, without
any bound on slopes or any assumption that slopes converge.
"""
from pathlib import Path
import sys,json,time,argparse
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/python-deps'))
sys.path.insert(0,str(ROOT/'work/construction-deps'))
import sympy as sp
from sympy.polys.matrices import DomainMatrix

t,e=sp.symbols('t e')
K=sp.QQ.alg_field_from_poly(sp.Poly(t**4-4*t**3-14*t**2-4*t+1,t),alias='t',root_index=2)
R=K.poly_ring(e);x=K.unit;E=R.gens[0]
tan=[K.zero]
for k in range(9):tan.append((tan[-1]+x)/(K.one-tan[-1]*x))
aa=[R(-tan[k])for k in range(9,0,-1)]+[-E,E]+[R(tan[k])for k in range(1,10)]
lo=F(158384440324536293838883092694,10**30)
hi=F(158384440324536293838883092695,10**30)
def quartic(v):return v**4-4*v**3-14*v**2-4*v+1
assert quartic(lo)>0>quartic(hi)
for _ in range(100):
    mid=(lo+hi)/2
    if quartic(mid)>0:lo=mid
    else:hi=mid


def interval_mul(a,b):
    z=[a[i]*b[j]for i in (0,1)for j in (0,1)];return min(z),max(z)


def alg_coeff(v):
    return [str(F(int(c.numerator),int(c.denominator)))for c in v.to_list()]


def alg_interval(v):
    iv=(F(0),F(0))
    for c in v.to_list():
        iv=interval_mul(iv,(lo,hi));c=F(int(c.numerator),int(c.denominator));iv=(iv[0]+c,iv[1]+c)
    return iv


def alg_sign(v):
    if not v:return 0
    iv=alg_interval(v)
    assert iv[0]>0 or iv[1]<0,('root interval insufficient',alg_coeff(v))
    return 1 if iv[0]>0 else -1


def poly_data(v):
    return [{'power':int(mon[0]),'coefficient':alg_coeff(coeff)}for mon,coeff in sorted(v.items())]


def leading_sign(v):
    if not v:return 0
    return alg_sign(v[min(v.keys())])


def positive_radius(v):
    if not v:return F(1)
    lead=min(v.keys());iv=alg_interval(v[lead]);assert iv[0]>0
    tail=sum(max(abs(a),abs(b))for mon,c in v.items()if mon!=lead for a,b in [alg_interval(c)])
    return min(F(1),iv[0]/(2*tail))if tail else F(1)


def row_from(meta):
    row=[R.zero]*20
    if meta[0]=='triple':
        _,i,j,k,s=meta;row[i]=s*(aa[j]-aa[k]);row[j]=s*(aa[k]-aa[i]);row[k]=s*(aa[i]-aa[j])
    else:
        _,i,j,s=meta;row[i]=R(s);row[j]=R(-s)
    return row


def main(source,out,max_cases=0,start_case=0):
    for _ in range(100):
        try:data=json.loads(source.read_text());break
        except json.JSONDecodeError:time.sleep(.1)
    cases=data['records'][start_case:start_case+max_cases if max_cases else None];out.mkdir(parents=True,exist_ok=True)
    report=dict(source=str(source.resolve().relative_to(ROOT)),field_polynomial=[1,-4,-14,-4,1],
      root_interval=[str(lo),str(hi)],epsilon_scope='Exact positive dependence on the reported explicit punctured epsilon interval',records=[])
    start=time.time();success=0;radius=F(1)
    for ci,record in enumerate(cases):
        rows=[row_from(m)for m in record['support']];A=DomainMatrix.from_list(rows,R)
        ker=A.transpose().nullspace();vectors=ker.to_list();good=None
        for vv in vectors:
            signs={leading_sign(v)for v in vv}-{0}
            if len(signs)==1:
                sg=signs.pop();good=[sg*v for v in vv];break
        row=dict(case_index=record.get('case_index',ci+start_case),class_index=record['class_index'],I=record['I'],shift=record['shift'],support=record['support'],nullity=len(vectors))
        if 'reflection'in record:row['source_normalization']=dict(reflection=record['reflection'],sign=record['sign'])
        if good is not None:
            for col in range(20):assert sum((w*rows[i][col]for i,w in enumerate(good)),R.zero)==R.zero
            bound=min(positive_radius(w)for w in good);radius=min(radius,bound)
            row.update(status='exact_symbolic_positive_dependency',weights=[poly_data(w)for w in good],epsilon_upper=str(bound));success+=1
        else:row.update(status='support_not_positive_near_zero')
        report['records'].append(row)
        print(json.dumps(dict(case=ci,success=success,nullity=len(vectors),status=row['status'],seconds=time.time()-start)),flush=True)
        report.update(success=success,epsilon_upper=str(radius),epsilon_upper_float=float(radius),seconds=time.time()-start)
        if ci%10==0 or ci==len(cases)-1:
            tmp=out/'certificates.tmp.json';tmp.write_text(json.dumps(report,separators=(',',':'))+'\n')
            for attempt in range(100):
                try:tmp.replace(out/'certificates.json');break
                except PermissionError:
                    if attempt==99:raise
                    time.sleep(.1)
    print(json.dumps(dict(done=True,success=success,cases=len(cases),seconds=time.time()-start)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--max-cases',type=int,default=0);p.add_argument('--start-case',type=int,default=0)
    a=p.parse_args();main(a.source,a.out,a.max_cases,a.start_case)
