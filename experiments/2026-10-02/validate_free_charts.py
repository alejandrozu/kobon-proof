"""Geometric control of cyclic reorientation and adjacent-cap sign formulas.

Transform actual rational lines, move infinity to every gap on every support,
and compare the derived signs against actual determinants and triangle cells.
"""
from free_chart_grid_fit import *
from importlib.util import spec_from_file_location,module_from_spec


def main(source,out):
    spec=spec_from_file_location('transfer',ROOT/'experiments/2026-09-21/general-bounds/projective_seed_transfer.py')
    mod=module_from_spec(spec);spec.loader.exec_module(mod)
    lines=read_lines(source);n=len(lines);q=n-1
    lr=[(a,b,-c)for a,b,c in lines]+[(0,0,1)];entries=[]
    for i,j,k in it.combinations(range(n+1),3):
        det=mod.dot(lr[i],mod.cross(lr[j],lr[k]));assert det
        entries.append(((i,j,k),1 if det>0 else -1))
    chi=tensor(n+1,entries);checks=0;capschecked=0;start=time.time()
    for I in range(n):
        base,_=mod.normalize_projective(lr,I,n)
        for cut in range(q):
            h=(base[cut-1][0]+base[cut][0])/2 if cut else base[0][0]-1
            actual=sorted((1/(h-a),v/(a-h),label)for a,v,label in base)
            ids,sg=free_signs(chi,I,cut);assert ids==[p[2]for p in actual]
            aa=[p[0]for p in actual];vv=[p[1]for p in actual]
            es=[]
            triples=list(it.combinations(range(q),3))
            for i,j,k in triples:
                E=(aa[j]-aa[k])*vv[i]+(aa[k]-aa[i])*vv[j]+(aa[i]-aa[j])*vv[k]
                assert E;es.append(1 if E>0 else -1)
            factors={int(a*b)for a,b in zip(sg,es)};assert len(factors)==1
            factor=factors.pop();vv=[factor*v for v in vv]
            newlines=[(0,1,0)]+[primitive((1,-v,a))for a,v in zip(aa,vv)]
            ar=arrangement(newlines);triangles=set(ar['triangles']);bytriple=dict(zip(triples,sg))
            for i in range(q-1):
                predicted=all(int(bytriple[tuple(sorted((i,i+1,k)))])*(1 if k<i else -1)*(vv[i]-vv[i+1])>0
                              for k in range(q)if k not in(i,i+1))
                assert predicted==((0,i+1,i+2)in triangles),(I,cut,i,predicted)
                capschecked+=1
            checks+=1
    report=dict(passed=True,source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
       actual_rational_projective_charts=checks,triple_sign_checks=checks*math.comb(q,3),
       cap_vs_exact_cell_checks=capschecked,seconds=time.time()-start)
    out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();main(a.source.resolve(),a.out)
