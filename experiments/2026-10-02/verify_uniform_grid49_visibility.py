"""Exact uniform exterior-visibility check for the 49-line tangent-grid seed."""
from verify_uniform_grid49 import *


def determinant(normals,i,j):
    a,b=normals[i];c,d=normals[j];return a*d-b*c


def run_visibility(seed,out):
    data=json.loads(seed.read_text());v=[F(s)for s in data['reciprocal_slopes']]
    tan=[tuple(F(x)for x in z)for z in data['trigonometric_intervals']['positive_tangents']]
    upper=F(data['epsilon_upper']);assert 0<upper<tan[0][0]
    normals=[(F(0),F(1))]+[(F(1),-s)for s in v];w=(F(1),F(-2))
    directions=[w[0]*b-w[1]*a for a,b in normals];assert all(directions)
    def constants(epsilon):
        return [(F(0),F(0))]+[scale(x,-1)for x in reversed(tan)]+[(-epsilon,-epsilon),(epsilon,epsilon)]+tan
    ends=[constants(F(0)),constants(upper)];mid=[sum(z)/2 for z in constants(upper/2)]
    def coefficients(i,j,r):
        a,b=normals[r];c,d=normals[i];e,f=normals[j]
        return a*f-b*e,-a*d+b*c,-determinant(normals,i,j)
    visible=[];checks=0
    for i,j in it.combinations(range(49),2):
        good=True
        for r in range(49):
            if r in(i,j):continue
            di=determinant(normals,r,i)*directions[i]
            dj=determinant(normals,r,j)*directions[j]
            if di*dj<0:good=False;break
            sign=1 if di>0 or dj>0 else -1
            ci,cj,cr=coefficients(i,j,r)
            evaluation=(ci*mid[i]+cj*mid[j]+cr*mid[r])*determinant(normals,i,j)
            if sign*evaluation<0:good=False;break
        if not good:continue
        visible.append([i,j,49])
        for r in range(49):
            if r in(i,j):continue
            di=determinant(normals,r,i)*directions[i]
            dj=determinant(normals,r,j)*directions[j]
            assert di*dj>0
            sign=1 if di>0 else -1;ci,cj,cr=coefficients(i,j,r)
            for aa in ends:
                evaluation=add(add(scale(aa[i],ci),scale(aa[j],cj)),scale(aa[r],cr))
                positive=scale(evaluation,sign*determinant(normals,i,j))
                assert positive[0]>=0,(i,j,r,positive)
                checks+=1
    assert len(visible)==24 and [0,48,49]in visible,(len(visible),visible)
    report=dict(passed=True,seed=str(seed),seed_sha256=hashlib.sha256(seed.read_bytes()).hexdigest(),
        normal=[1,-2],visible_pairs=visible,count=len(visible),rightmost_pair=[0,48,49],
        epsilon_interval='0 < epsilon <= '+str(upper),endpoint_sign_checks=checks,
        principle='Affine evaluation numerators are affine in epsilon; nonnegative endpoint intervals and constant derivative signs imply uniform visibility.',
        trust='Exact rational interval certificate; not itself a Lean theorem')
    out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:z for k,z in report.items()if k!='visible_pairs'}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('seed',type=Path);parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();run_visibility(args.seed,args.out)
