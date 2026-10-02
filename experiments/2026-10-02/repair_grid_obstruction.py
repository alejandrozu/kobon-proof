"""Replace failed symbolic supports using another recorded LP discovery run.

Run only after the original producer finishes. The complete result is then
checked by the independent stdlib verifier; a repair is never trusted by itself.
"""
from exact_grid_obstruction import *


def repair(certificate,alternate):
    data=json.loads(certificate.read_text());alt=json.loads(alternate.read_text())
    lookup={(r['class_index'],r['I'],r['shift']):r for r in alt['records']}
    repaired=[]
    for row in data['records']:
        if row['status']=='exact_symbolic_positive_dependency':continue
        rec=lookup[row['class_index'],row['I'],row['shift']]
        rows=[row_from(m)for m in rec['support']]
        vectors=DomainMatrix.from_list(rows,R).transpose().nullspace().to_list()
        good=None
        for vv in vectors:
            signs={leading_sign(v)for v in vv}-{0}
            if len(signs)==1:
                sg=signs.pop();good=[sg*v for v in vv];break
        if good is None:continue
        for col in range(20):assert sum((w*rows[i][col]for i,w in enumerate(good)),R.zero)==R.zero
        radius=min(positive_radius(w)for w in good)
        row.update(status='exact_symbolic_positive_dependency',support=rec['support'],
            weights=[poly_data(w)for w in good],epsilon_upper=str(radius),
            discovery_repair_source=str(alternate.resolve().relative_to(ROOT)),nullity=len(vectors))
        repaired.append(row['case_index'])
    radius=min(F(r['epsilon_upper'])for r in data['records']if r['status']=='exact_symbolic_positive_dependency')
    data.update(success=sum(r['status']=='exact_symbolic_positive_dependency'for r in data['records']),
       epsilon_upper=str(radius),epsilon_upper_float=float(radius))
    data.setdefault('repairs',[]).append(dict(source=str(alternate.resolve().relative_to(ROOT)),cases=repaired))
    certificate.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(repaired=repaired,success=data['success'],epsilon_upper=float(radius))),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('alternate',type=Path)
    a=p.parse_args();repair(a.certificate,a.alternate)
