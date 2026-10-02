"""Fit one exact affine witness to prescribed tangent intercepts.

Every original triple orientation AND every orientation with the original
line at infinity is retained. Floating feasibility is only discovery; saved
coordinates are rational approximations, checked by two exact cell counters.
True-tangent or uniform-small-epsilon compatibility is a separate obligation.
"""
from word_grid_fit import *


def run_affine(source, out, epsilons, seconds):
    source=source.resolve();out=out.resolve();out.mkdir(parents=True,exist_ok=True)
    start=time.time();lines=read_lines(source);n=len(lines);q=n-1
    homogeneous=[(a,b,-c)for a,b,c in lines]+[(0,0,1)];entries=[]
    for i,j,k in it.combinations(range(n+1),3):
        a,b,c=homogeneous[i];d,e,f=homogeneous[j];g,h,z=homogeneous[k]
        determinant=a*(e*z-f*h)-b*(d*z-f*g)+c*(d*h-e*g)
        assert determinant
        entries.append(((i,j,k),1 if determinant>0 else -1))
    chi=tensor(n+1,entries);pairs=list(it.combinations(range(q),2));triples=list(it.combinations(range(q),3))
    expected=json.loads(source.read_text())['triangle_count']
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        n=n,source_triangle_count=expected,epsilon_values=epsilons,records=[],wins=[],
        scope='One retained affine type, all distinguished supports. Floating LP diagnostics are not nonrealizability proofs.',
        chart_formula_control=validate_chart_formula())
    for epsilon in epsilons:
        aa=np.array(sorted([math.tan(k*math.pi/q)for k in range(-q//2+1,q//2)if k]+[-epsilon,epsilon]))
        base=np.zeros((len(pairs)+len(triples),q+1))
        for row,(i,j)in enumerate(pairs):base[row,i]=1;base[row,j]=-1
        for row,(i,j,k)in enumerate(triples,len(pairs)):
            base[row,i]=aa[j]-aa[k];base[row,j]=aa[k]-aa[i];base[row,k]=aa[i]-aa[j]
        base/=np.max(abs(base),axis=1)[:,None];obj=np.zeros(q+1);obj[-1]=-1;seen=set()
        for I in range(n):
            if time.time()-start>seconds:break
            ids,sg=chart_signs(chi,I,n);key=sg.tobytes()
            if key in seen:
                report['records'].append(dict(epsilon=epsilon,I=I,duplicate=True));continue
            seen.add(key);matrix=-sg[:,None]*base;matrix[:,-1]=1
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                result=linprog(obj,A_ub=matrix,b_ub=np.zeros(len(matrix)),bounds=[(-1,1)]*q+[(0,1)],
                    method='highs',options={'threads':1,'time_limit':5})
            margin=float(result.x[-1])if result.success else None
            row=dict(epsilon=epsilon,I=I,margin=margin,status=int(result.status));report['records'].append(row)
            if margin is not None and margin>1e-8:
                vv=[F(float(v)).limit_denominator(10**11)for v in result.x[:-1]]
                if vv[q//2-1]<vv[q//2]:vv=[-v for v in vv]
                vv=[v+2 for v in vv]
                if epsilon==0:
                    path=out/f'n{n:03d}-I{I:02d}-limit-slopes.json'
                    data=dict(n=n,source=str(source.relative_to(ROOT)),source_labels=ids,distinguished=I,
                        reciprocal_slopes=[str(v)for v in vv],numerical_lp_margin=margin,
                        verification='Limit slopes only; no arrangement at epsilon zero is claimed')
                    path.write_text(json.dumps(data,indent=2)+'\n');report['wins'].append(str(path.relative_to(ROOT)))
                    print(json.dumps(dict(event='limit_slopes',**row)),flush=True)
                    continue
                intercepts=[F(float(a)).limit_denominator(10**13)for a in aa]
                intercepts[q//2-1]=-F(str(epsilon));intercepts[q//2]=F(str(epsilon))
                proposal=[(0,1,0)]+[primitive((1,-v,a))for a,v in zip(intercepts,vv)]
                cells=arrangement(proposal);count=len(cells['triangles']);caps=sum(0 in t for t in cells['triangles'])
                assert count==expected,(I,epsilon,count,expected)
                path=out/f'n{n:03d}-I{I:02d}-eps{epsilon:g}.json'
                data=dict(n=n,triangle_count=count,lines_frac=[[str(x)for x in line]for line in proposal],
                    source=str(source.relative_to(ROOT)),source_labels=ids,distinguished=I,epsilon=str(epsilon),
                    reciprocal_slopes=[str(v)for v in vv],Y0_triangles=caps,numerical_lp_margin=margin,
                    verification='Exact rational midpoint; true-tangent and uniform-epsilon realization not yet proved')
                path.write_text(json.dumps(data,indent=2)+'\n');data['direct']=verify(path)
                path.write_text(json.dumps(data,indent=2)+'\n');report['wins'].append(str(path.relative_to(ROOT)))
                print(json.dumps(dict(event='exact_midpoint',n=n,triangles=count,caps=caps,**row)),flush=True)
            report['seconds']=time.time()-start
            (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
            print(json.dumps(dict(event='LP',**row,seconds=report['seconds'])),flush=True)
        if time.time()-start>seconds:break
    report.update(seconds=time.time()-start,complete=len(report['records'])==len(epsilons)*n)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(done=True,complete=report['complete'],cases=len(report['records']),wins=len(report['wins']))),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('source',type=Path);parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--epsilon',type=float,nargs='+',default=[.001,.00001,.01,.03]);parser.add_argument('--seconds',type=float,default=600)
    args=parser.parse_args();run_affine(args.source,args.out,args.epsilon,args.seconds)
