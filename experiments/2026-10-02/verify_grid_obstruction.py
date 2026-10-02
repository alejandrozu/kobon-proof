"""Independent stdlib-only exact checker for the 21-line grid obstruction.

No NumPy, SciPy, SymPy, or optimizer is used. It checks polynomial identities
in Q[t,e]/(t^4-4t^3-14t^2-4t+1), rational sign enclosures, all support signs
against the supplied words, and coverage of every saturated cyclic chart.
Completeness of the published pseudoline enumeration remains an attributed
external mathematical input, not a claim established by this checker.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import cmp_to_key
import argparse,json,itertools,hashlib,time

Z=(F(0),)*4;ONE=(F(1),F(0),F(0),F(0));T=(F(0),F(1),F(0),F(0))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,s):return tuple(x*s for x in a)
def mul(a,b):
    c=[F(0)]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    for i in range(6,3,-1):
        x=c[i];c[i-1]+=4*x;c[i-2]+=14*x;c[i-3]+=4*x;c[i-4]-=x
    return tuple(c[:4])
def inv(a):
    columns=[mul(a,tuple(F(int(i==j))for i in range(4)))for j in range(4)]
    M=[[columns[j][i]for j in range(4)]+[F(int(i==0))]for i in range(4)]
    for j in range(4):
        k=next(k for k in range(j,4)if M[k][j]);M[j],M[k]=M[k],M[j]
        s=M[j][j];M[j]=[x/s for x in M[j]]
        for k in range(4):
            if k!=j:
                s=M[k][j];M[k]=[x-s*y for x,y in zip(M[k],M[j])]
    out=tuple(row[-1]for row in M);assert mul(a,out)==ONE;return out
def padd(a,b):
    out=dict(a)
    for p,c in b.items():out[p]=add(out.get(p,Z),c)
    return {p:c for p,c in out.items()if c!=Z}
def pscale(a,s):return {p:scale(c,s)for p,c in a.items()if s and c!=Z}
def pmul(a,b):
    out={}
    for p,c in a.items():
        for q,d in b.items():out[p+q]=add(out.get(p+q,Z),mul(c,d))
    return {p:c for p,c in out.items()if c!=Z}
def interval_mul(a,b):
    z=[x*y for x in a for y in b];return min(z),max(z)
def alg_interval(a,root):
    iv=(F(0),F(0))
    for c in reversed(a):
        iv=interval_mul(iv,root);iv=(iv[0]+c,iv[1]+c)
    return iv
def quartic(v):return v**4-4*v**3-14*v**2-4*v+1


def decode_word(raw):
    word=[int(s)for s in raw.split(')',1)[1].split()];n=max(word)+2
    assert n==21 and len(word)==210
    perm=list(range(n));ranks=[{}for _ in range(n)]
    for g in word:
        i,j=perm[g:g+2];assert i<j and j not in ranks[i]
        ranks[i][j]=len(ranks[i]);ranks[j][i]=len(ranks[j]);perm[g],perm[g+1]=j,i
    assert perm==list(reversed(range(n)))
    def chi(i,j,k):
        assert len({i,j,k})==3
        s=-1 if sum(a>b for a,b in ((i,j),(i,k),(j,k)))%2 else 1
        a,b,c=sorted((i,j,k))
        if c==n:return s
        return s*(-1 if ranks[a][b]<ranks[a][c]else 1)
    return chi


def chart(chi,I,cut):
    ids=[j for j in range(21)if j!=I];d=chi(I,21,ids[0]);A={j:chi(j,I,21)for j in ids}
    def compare(i,j):return -d*chi(i,j,I)*A[i]*A[j]
    ids.sort(key=cmp_to_key(compare))
    assert all(compare(i,j)<0 for i,j in itertools.combinations(ids,2))
    for j in ids[:cut]:A[j]*=-1
    ids=ids[cut:]+ids[:cut]
    signs={(i,j,k):chi(ids[i],ids[j],ids[k])*A[ids[i]]*A[ids[j]]*A[ids[k]]
           for i,j,k in itertools.combinations(range(20),3)}
    caps=[]
    for i in range(19):
        required={signs[tuple(sorted((i,i+1,k)))]*(1 if k<i else -1)
                  for k in range(20)if k not in(i,i+1)}
        if len(required)!=1:return signs,None
        caps.append(required.pop())
    return signs,caps


def decode_poly(items):
    out={}
    for item in items:
        c=[F(s)for s in reversed(item['coefficient'])];assert len(c)<=4
        c=tuple(c+[F(0)]*(4-len(c)));p=item['power'];assert p not in out and p>=0
        if c!=Z:out[p]=c
    return out


def main(certs,words,out):
    started=time.time();data=json.loads(certs.read_text());root=tuple(F(s)for s in data['root_interval'])
    assert F(15,100)<root[0]<root[1]<F(17,100)
    assert quartic(root[0])>0>quartic(root[1])
    # p'(t)<4*(.17)^3-4<0 in (.15,.17): the isolated real root is unique.
    assert 4*F(17,100)**3-4<0
    tan=[Z]
    for _ in range(9):tan.append(mul(add(tan[-1],T),inv(add(ONE,scale(mul(tan[-1],T),-1)))))
    aa=[{0:scale(tan[k],-1)}for k in range(9,0,-1)]+[{1:scale(ONE,-1)},{1:ONE}]+[{0:tan[k]}for k in range(1,10)]
    raw=[s for s in words.read_text().splitlines()if ')'in s];assert len(raw)==18
    chis=[decode_word(s)for s in raw];covered={};radius=F(1);passed=0
    for rec in data['records']:
        if rec['status']!='exact_symbolic_positive_dependency':continue
        signs,caps=chart(chis[rec['class_index']],rec['I'],rec['shift']);assert caps is not None
        weights=[decode_poly(p)for p in rec['weights']];assert any(weights)
        assert len(weights)==len(rec['support']);total=[{}for _ in range(20)]
        eps=F(rec['epsilon_upper']);assert 0<eps<=1
        for meta,w in zip(rec['support'],weights):
            if w:
                lead=min(w);lower,upper=alg_interval(w[lead],root);assert lower>0
                tail=sum(max(abs(l),abs(u))for p,c in w.items()if p!=lead for l,u in [alg_interval(c,root)])
                assert eps*tail<=lower/2
            row=[{}for _ in range(20)]
            if meta[0]=='triple':
                _,i,j,k,s=meta;assert i<j<k and s==signs[(i,j,k)]
                row[i]=pscale(padd(aa[j],pscale(aa[k],-1)),s)
                row[j]=pscale(padd(aa[k],pscale(aa[i],-1)),s)
                row[k]=pscale(padd(aa[i],pscale(aa[j],-1)),s)
            else:
                _,i,j,s=meta;assert j==i+1 and s==caps[i]
                row[i]={0:scale(ONE,s)};row[j]={0:scale(ONE,-s)}
            for col in range(20):total[col]=padd(total[col],pmul(w,row[col]))
        assert all(not c for c in total),'Polynomial dependence failed'
        key=tuple(signs.values());covered[key]=rec['case_index'];radius=min(radius,eps);passed+=1
    required={};unsaturable=0
    for ci,chi in enumerate(chis):
        for I,cut in itertools.product(range(21),range(20)):
            signs,caps=chart(chi,I,cut)
            if caps is None:unsaturable+=1;continue
            key=tuple(signs.values());required.setdefault(key,(ci,I,cut))
    missing=[v for k,v in required.items()if k not in covered]
    result=dict(passed=not missing,exact_certificates_checked=passed,distinct_required=len(required),
       missing_cases=missing,charts_total=18*21*20,unsaturable_chart_occurrences=unsaturable,
       epsilon_upper=str(radius),epsilon_upper_float=float(radius),
       word_sha256=hashlib.sha256(words.read_bytes()).hexdigest(),certificate_sha256=hashlib.sha256(certs.read_bytes()).hexdigest(),
       external_assumption='Only the18 supplied21-support representatives are audited here. Published P-classes classify22-support closures including infinity; complete affine coverage needs236 E-classes or all infinity choices.',
       scope='Exact finite computation for the prescribed tangent grid and the18 supplied representatives; not complete affine classification coverage and not a general Kobon upper bound',
       seconds=time.time()-started)
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
    return not missing


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificates',type=Path);p.add_argument('words',type=Path);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();raise SystemExit(0 if main(a.certificates,a.words,a.out)else 1)
