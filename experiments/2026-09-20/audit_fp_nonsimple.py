"""Exact sign-combinatorial count for Furedi-Palasti Example 2.

L_i: sin(pi*i/n)*x + cos(pi*i/n)*y = sin(3*pi*i/n), 0<=i<n.
For i<j<k the determinant of rows (a,b,c) has sign
sin(pi*(i+j+k)/n); it vanishes iff n divides i+j+k.
All pair determinants sin(pi*(i-j)/n) are negative.
Thus evaluations at the pair vertices, for a sorted triple, have
signs (s,-s,s) at (ij,ik,jk), respectively.
"""
import itertools as it
import json
from pathlib import Path

def count(n):
    pos={p:0 for p in it.combinations(range(n),2)}
    neg={p:0 for p in pos}
    for i,j,k in it.combinations(range(n),3):
        total=i+j+k
        if total%n==0: continue
        s=1 if (total//n)%2==0 else -1
        for pair,index,sign in (((i,j),k,s),((i,k),j,-s),((j,k),i,s)):
            (pos if sign>0 else neg)[pair]|=1<<index
    triangles=[]
    for i,j,k in it.combinations(range(n),3):
        if (i+j+k)%n==0:continue
        if not ((pos[i,j]|pos[i,k]|pos[j,k]) & (neg[i,j]|neg[i,k]|neg[j,k])):
            triangles.append((i,j,k))
    return len(triangles)

if __name__=='__main__':
    ns=list(range(4,61))+[99,195]
    data=[dict(n=n,triangles=count(n)) for n in ns]
    Path(__file__).with_name('audit_fp_nonsimple.json').write_text(json.dumps(data,indent=2))
    for r in data:print(r['n'],r['triangles'],flush=True)
