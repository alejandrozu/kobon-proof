"""Exact chirotope census for phase-shifted Furedi--Palasti lines.

Angles are (i+alpha)*pi/n. The determinant factorization proved in
Kobon.FurediPalasti makes every sign below an integer sign test.
This script counts actual empty supporting triples, not just a lower estimate.
It is a reproducible finite experiment, not a proof for every n.
"""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

def sign(x):
    return (x > 0) - (x < 0)

def census(n, alpha):
    shift = 3 * alpha
    def sine(s):
        residue = (F(s) + shift) % (2*n)
        if residue == 0 or residue == n:
            return 0
        return 1 if residue < n else -1
    sums = [sine(s) for s in range(3*n)]
    signs = {(i,j): [sign(r-j)*sign(r-i)*sums[i+j+r]
                    for r in range(n)]
             for i,j in combinations(range(n),2)}
    triangles=[]
    for i,j,k in combinations(range(n),3):
        if not sums[i+j+k]:
            continue
        if all(not (min(a,b,c)<0<max(a,b,c))
               for a,b,c in zip(signs[i,j],signs[i,k],signs[j,k])):
            triangles.append((i,j,k))
    return triangles

def main():
    records=[]
    for n in range(3,61):
        counts={str(a):len(census(n,a)) for a in [F(0),F(1,6),F(1,3),F(1,2),F(2,3),F(5,6)]}
        row=dict(n=n,counts=counts,baseline=(n*(n-3)+2)//3)
        records.append(row)
        print(row,flush=True)
    Path(__file__).with_name('phase-census.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':
    main()
