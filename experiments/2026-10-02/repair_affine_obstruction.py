"""Repair uncovered symbolic supports using smaller-epsilon LP discovery.

The final exact affine checker remains the authority. Discovery margins and
floating dual weights are never used as mathematical certificates.
"""
import exact_grid_obstruction as ex
import grid_obstruction as discovery
from expand_affine_coverage import transformed_support
from pathlib import Path
import json,argparse,warnings
import numpy as np
from scipy.optimize import linprog


def repair(certificate,words):
    data=json.loads(certificate.read_text());raw=[s for s in words.read_text().splitlines()if ')'in s]
    repaired=[];failed=[]
    for rec in data['records']:
        if rec['status']=='exact_symbolic_positive_dependency':continue
        n,chi=discovery.from_word(raw[rec['class_index']]);normal=rec['source_normalization']
        sign=normal['sign']*(-1 if normal['reflection']else 1);refl=normal['reflection'];found=False
        for eps in (.0001,.00001,.000001):
            ids,aa,M,meta=discovery.rows_for(chi,rec['I'],0,eps);norm=np.max(abs(M),axis=1)
            mat=np.column_stack([-M/norm[:,None],np.ones(len(M))]);obj=np.zeros(21);obj[-1]=-1
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                opt=linprog(obj,A_ub=mat,b_ub=np.zeros(len(mat)),bounds=[(-1,1)]*20+[(0,1)],method='highs',options={'threads':1})
            assert opt.success
            if opt.x[-1]>1e-8:raise RuntimeError(('positive numerical margin',rec['case_index'],eps,opt.x[-1]))
            ys=-opt.ineqlin.marginals/norm;active=np.flatnonzero(ys>1e-9)
            support=transformed_support([meta[i]for i in active],refl,sign)
            rows=[ex.row_from(m)for m in support];vectors=ex.DomainMatrix.from_list(rows,ex.R).transpose().nullspace().to_list()
            good=None
            for vv in vectors:
                signs={ex.leading_sign(v)for v in vv}-{0}
                if len(signs)==1:
                    sg=signs.pop();good=[sg*v for v in vv];break
            if good is None:continue
            for col in range(20):assert sum((w*rows[i][col]for i,w in enumerate(good)),ex.R.zero)==ex.R.zero
            bound=min(ex.positive_radius(w)for w in good)
            rec.update(status='exact_symbolic_positive_dependency',support=support,weights=[ex.poly_data(w)for w in good],
                epsilon_upper=str(bound),repair_discovery_epsilon=eps,nullity=len(vectors))
            repaired.append(rec['case_index']);found=True;break
        if not found:failed.append(rec['case_index'])
    data['success']=sum(r['status']=='exact_symbolic_positive_dependency'for r in data['records'])
    data['epsilon_upper']=str(min(ex.F(r['epsilon_upper'])for r in data['records']if 'weights'in r))
    data['epsilon_upper_float']=float(ex.F(data['epsilon_upper']))
    data.setdefault('repairs',[]).append(dict(repaired=repaired,failed=failed,method='LP supports at smaller epsilon, then exact polynomial nullspace and positivity'))
    certificate.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps(dict(repaired=repaired,failed=failed,success=data['success'],epsilon_upper=data['epsilon_upper_float'])),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('words',type=Path)
    a=p.parse_args();repair(a.certificate,a.words)
