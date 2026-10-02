"""Stdlib-only exact certificate and complete affine-input coverage checker.

Every polynomial dependence is checked from scratch. Its few row signs may
then cover many input types. Four explicit symmetry transforms are allowed;
the underlying grid satisfies a[19-i] = -a[i] exactly.
"""
from expand_affine_coverage import *


def row_polynomial(meta,aa):
    row=[{}for _ in range(20)]
    if meta[0]=='triple':
        _,i,j,k,s=meta;assert 0<=i<j<k<20 and s in(-1,1)
        row[i]=pscale(padd(aa[j],pscale(aa[k],-1)),s)
        row[j]=pscale(padd(aa[k],pscale(aa[i],-1)),s)
        row[k]=pscale(padd(aa[i],pscale(aa[j],-1)),s)
    else:
        _,i,j,s=meta;assert 0<=i<j<20 and j==i+1 and s in(-1,1)
        row[i]={0:scale(ONE,s)};row[j]={0:scale(ONE,-s)}
    return row


def check_certificate(rec,root,aa):
    weights=[decode_poly(p)for p in rec['weights']];assert any(weights)
    assert len(weights)==len(rec['support']);eps=F(rec['epsilon_upper']);assert 0<eps<=1
    total=[{}for _ in range(20)];rows=[]
    for meta,w in zip(rec['support'],weights):
        if w:
            lead=min(w);lower,upper=alg_interval(w[lead],root);assert lower>0
            tail=sum(max(abs(l),abs(u))for p,c in w.items()if p!=lead for l,u in [alg_interval(c,root)])
            assert eps*tail<=lower/2
        row=row_polynomial(meta,aa);rows.append(row)
        for col in range(20):total[col]=padd(total[col],pmul(w,row[col]))
    assert all(not c for c in total),'Polynomial dependence failed'
    return eps,rows


def run(files,words,out):
    started=time.time();root=None;records=[];inputs=[]
    for file in files:
        data=json.loads(file.read_text());interval=tuple(F(s)for s in data['root_interval'])
        if root is None:root=interval
        else:assert root==interval
        records.extend((str(file),r)for r in data['records']if r['status']=='exact_symbolic_positive_dependency')
        inputs.append(dict(file=str(file),sha256=hashlib.sha256(file.read_bytes()).hexdigest()))
    assert F(15,100)<root[0]<root[1]<F(17,100);assert quartic(root[0])>0>quartic(root[1])
    assert 4*F(17,100)**3-4<0  # A strict upper bound for p' on this interval.
    tan=[Z]
    for _ in range(9):tan.append(mul(add(tan[-1],T),inv(add(ONE,scale(mul(tan[-1],T),-1)))))
    aa=[{0:scale(tan[k],-1)}for k in range(9,0,-1)]+[{1:scale(ONE,-1)},{1:ONE}]+[{0:tan[k]}for k in range(1,10)]
    for i in range(20):assert padd(aa[i],aa[19-i])=={}
    patterns=[];radius=F(1)
    for ci,(file,rec)in enumerate(records):
        eps,rows=check_certificate(rec,root,aa);radius=min(radius,eps)
        for reflection,sign in itertools.product((False,True),(1,-1)):
            sup=transformed_support(rec['support'],reflection,sign)
            # The reflection sends triple rows to reversed coordinate columns;
            # cap rows require the extra minus encoded in transformed_support.
            # Independently check all transformed identities as well.
            for transformed,original in zip(sup,rows):
                new=row_polynomial(transformed,aa)
                expected=[pscale(original[19-j if reflection else j],sign)for j in range(20)]
                assert new==expected
            mask,pos=masks(sup);patterns.append((mask,pos,ci,reflection,sign))
        if ci%100==0:print(json.dumps(dict(event='exact',checked=ci+1,total=len(records),seconds=time.time()-started)),flush=True)
    raw=[s for s in words.read_text().splitlines()if ')'in s];assert len(raw)==236
    assert all(triangle_count(s)==133 for s in raw)
    patterns.sort(key=lambda p:p[0].bit_count());coverage=[];missing=[];used=set()
    for ci,text in enumerate(raw):
        chi=decode_word(text)
        for I in range(21):
            signs,caps=chart(chi,I,0);assert caps is not None
            values=list(signs.values())+caps;bits=sum(1<<i for i,s in enumerate(values)if s>0);match=None
            for mask,pos,cert,refl,sg in patterns:
                if bits&mask==pos:match=dict(certificate=cert,reflection=refl,sign=sg);break
            row=dict(class_index=ci,I=I,covered=match is not None)
            if match:row.update(match);used.add(match['certificate'])
            else:missing.append([ci,I])
            coverage.append(row)
    denominator=1
    while F(1,denominator)>radius:
        denominator*=10
    for divisor in (5,2):
        if denominator%divisor==0 and F(divisor,denominator)<=radius:
            denominator//=divisor
            break
    result=dict(passed=not missing,exact_dependencies_checked=len(records),transformed_dependencies_checked=4*len(records),
        distinct_certificates_used=len(used),affine_classes=236,normalizations=4956,missing=missing,
        epsilon_upper=str(radius),epsilon_upper_float=float(radius),
        simple_epsilon_upper=str(F(1,denominator)),
        source_word_sha256=hashlib.sha256(words.read_bytes()).hexdigest(),certificate_inputs=inputs,
        coverage=coverage,seconds=time.time()-started,
        external_assumption='Parpalak--Utkin completeness of the 236 published Euclidean classes of perfect 21-line arrangements',
        scope='Exact computer-assisted obstruction in the saturated tangent-grid ansatz; permits arbitrary epsilon-dependent slopes; not a general Kobon upper bound or a full Lean classification proof')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('coverage','missing','certificate_inputs')}|{'missing_count':len(missing)}),flush=True)
    return not missing


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('words',type=Path);p.add_argument('certificates',nargs='+',type=Path);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();raise SystemExit(0 if run(a.certificates,a.words,a.out)else 1)
