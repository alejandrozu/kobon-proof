"""Exact integer crossing-order model for the BBL auxiliary line pencil.

This describes the combinatorics; its geometric realization is the separate
BBL trigonometric theorem.  Finite comparisons below independently verify the
model against saved real-line rational coordinate witnesses.
"""
from pathlib import Path
from itertools import combinations
import json,sys,time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,read_lines,F


def old_key(j):return 4*j+2


def key(q,i,k):
    """Symmetric rank of the intersection of two auxiliary lines.

    0..q-1 index the added lines in increasing intercept order; q denotes Y0.
    Only comparisons within one crossing row have geometric meaning.
    """
    assert q%2==0 and 0<=i<=q and 0<=k<=q and i!=k
    h=q//2
    if i==q or k==q:
        z=k if i==q else i
        return 4*z if z<h else 4*z+4
    s=i+k-q+1
    if s==-h:return 4*q-1
    if s==h:return -1
    if s==0:return 2*q
    reduced=s+q if s < -h else s-q if s > h else s
    j=reduced+h-(reduced<0)
    shift=-1 if i<h and k<h else 1 if i>=h and k>=h else 1 if s<0 else -1
    return old_key(j)+shift


def neighbors(q,K):
    f=(K-2)//4
    return [j for j in (f,f+1) if 0<=j<q and abs(K-old_key(j))<4]


def row(q,i):
    positions=[(old_key(j),'O',j) for j in range(q)]
    positions += [(key(q,i,k),'U',k) for k in range(q+1) if i!=k]
    assert len({p[0] for p in positions})==2*q,(q,i,'rank collision')
    return sorted(positions)


def model_check(q):
    rows=[row(q,i) for i in range(q+1)]
    sides=set();caps=[]
    for i,positions in enumerate(rows):
        for a,b in zip(positions,positions[1:]):
            if a[1]==b[1]=='U':raise AssertionError((q,i,'two consecutive auxiliary crossings'))
            if a[1]==b[1]=='O':
                caps.append((i,a[2],b[2]))
            else:
                old,other=(a,b) if a[1]=='O' else (b,a)
                sides.add((i,other[2],old[2]))
    expected={(i,k,j) for i in range(q+1) for k in range(q+1) if i!=k for j in neighbors(q,key(q,i,k))}
    assert sides==expected
    assert all((k,i,j) in sides for i,k,j in sides)
    assert len(sides)==2*q*q
    outer=sum(len(neighbors(q,key(q,i,k)))==1 for i,k in combinations(range(q+1),2))
    assert outer==q
    assert len(caps)==q-1
    assert (q,q//2-1,q//2) in caps
    assert sorted((a,b) for i,a,b in caps)==[(j,j+1) for j in range(q-1)]
    return dict(q=q,auxiliary_lines=q+1,mixed_triangles=len(sides)//2,
                exterior_auxiliary_pairs=outer,old_pair_caps=q-2,
                retained_central_triangle=1,all_integer_checks_passed=True)


def compare_coordinates(q):
    data=ROOT/f'research/kobon-hybrid/certificates/n{2*q+1:03d}.json'
    if not data.exists():
        data=ROOT/f'experiments/2026-09-21/hybrid-family/n{2*q+1:03d}.json'
    ar=arrangement(read_lines(data))
    old_order=sorted(range(1,q+1),key=lambda i:F(ar['lines'][i][2],ar['lines'][i][0]))
    old_position={i:j for j,i in enumerate(old_order)}
    comparisons=0
    for i in range(q+1):
        global_i=0 if i==q else q+1+i
        expected=[(kind,index) for _,kind,index in row(q,i)]
        actual=[]
        for p in ar['rows'][global_i]:
            other=next(j for j in ar['points'][p] if j!=global_i)
            actual.append(('U',q) if other==0 else ('O',old_position[other]) if other<=q else ('U',other-q-1))
        assert actual==expected,(q,i,actual,expected)
        comparisons+=1
    expected_triangles={tuple(sorted((old_order[j],0 if i==q else q+1+i,0 if k==q else q+1+k)))
                        for i,k in combinations(range(q+1),2) for j in neighbors(q,key(q,i,k))}
    actual_triangles={t for t in ar['triangles'] if sum(i==0 or i>q for i in t)==2}
    assert actual_triangles==expected_triangles
    return dict(q=q,coordinate_source=str(data.relative_to(ROOT)),crossing_rows_matched=comparisons,
                mixed_triangles_matched=len(expected_triangles),passed=True)


def main():
    start=time.monotonic()
    models=[model_check(q) for q in list(range(2,162,2))+[200,256,320,512,640]]
    geometric=[compare_coordinates(q) for q in [10,20,40,80]]
    report=dict(integer_models=models,coordinate_comparisons=geometric,
                elapsed_seconds=round(time.monotonic()-start,3),
                scope='Finite exact model checks. The all-q combinatorial and trigonometric bridge still require proofs.')
    (Path(__file__).parent/'row-model-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(models=len(models),geometric=geometric,seconds=report['elapsed_seconds']),indent=2))

if __name__=='__main__':main()
