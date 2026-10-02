"""Export a compact epsilon-independent representative for Lean integration."""
from exact_grid_obstruction import *


def main(certificate,out,case=238):
    for _ in range(100):
        try:data=json.loads(certificate.read_text());break
        except json.JSONDecodeError:time.sleep(.1)
    rec=next(r for r in data['records']if r['case_index']==case)
    assert all(p['power']==0 for w in rec['weights']for p in w)
    rec['normalization']='Every weight multiplied by the positive scalar5/64'
    for w in rec['weights']:
        for p in w:p['coefficient']=[str(F(s)*F(5,64))for s in p['coefficient']]
    rec['tangent_coefficients']={str(k):alg_coeff(v)for k,v in enumerate(tan)}
    rec['grid']='a0..a8=-T9..-T1;a9=-epsilon;a10=epsilon;a11..a19=T1..T9'
    rec['field_polynomial']=[1,-4,-14,-4,1];rec['root_interval']=['3/20','17/100']
    def expression(cs):return sum(sp.Rational(c)*t**j for j,c in enumerate(reversed(cs)))
    polys=[expression(alg_coeff(v))for v in tan]
    intercepts=[-polys[k]for k in range(9,0,-1)]+[-e,e]+[polys[k]for k in range(1,10)]
    sums=[sp.Integer(0)]*20
    for meta,weight in zip(rec['support'],rec['weights']):
        _,i,j,k,s=meta;w=expression(weight[0]['coefficient'])
        sums[i]+=s*w*(intercepts[j]-intercepts[k]);sums[j]+=s*w*(intercepts[k]-intercepts[i]);sums[k]+=s*w*(intercepts[i]-intercepts[j])
    quotients=[]
    for z in sums:
        q,r=sp.div(sp.expand(z),t**4-4*t**3-14*t**2-4*t+1,t);assert r==0
        quotients.append(str(q))
    rec['weighted_column_quotients_by_quartic']=quotients
    out.write_text(json.dumps(rec,indent=2)+'\n');print(out)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--case',type=int,default=238)
    a=p.parse_args();main(a.certificate,a.out,a.case)
