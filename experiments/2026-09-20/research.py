"""Exact affine line-arrangement research helpers, independently implemented.

Lines use a*x+b*y=c. Vertices are normalized homogeneous integer triples.
Triangle counting uses consecutive vertices along each side, not a float test.
"""
import itertools as it
import json
import math
from collections import Counter, defaultdict
from fractions import Fraction as F
from pathlib import Path

def primitive(values, positive_last=False):
    q = [F(v) for v in values]
    d = math.lcm(*(v.denominator for v in q))
    z = [v.numerator * (d // v.denominator) for v in q]
    g = math.gcd(*z)
    z = [v // g for v in z]
    pivot = z[-1] if positive_last else next(v for v in z if v)
    if pivot < 0:
        z = [-v for v in z]
    return tuple(z)

def intersection(l, m):
    a,b,c=l; d,e,f=m
    z=a*e-b*d
    if not z:
        return None
    p=(c*e-b*f,a*f-c*d,z)
    g=math.gcd(*p)
    if z<0: g=-g
    return tuple(v//g for v in p)

def arrangement(lines):
    lines = [primitive(l) for l in lines]
    assert len(set(lines)) == len(lines), 'duplicate lines'
    points = defaultdict(set)
    for i,j in it.combinations(range(len(lines)),2):
        p=intersection(lines[i],lines[j])
        if p is not None: points[p].update((i,j))
    rows = [[] for _ in lines]
    for p, ls in points.items():
        for i in ls: rows[i].append(p)
    edges = {}
    neighbors = defaultdict(set)
    for i, row in enumerate(rows):
        axis = 0 if lines[i][1] else 1
        row.sort(key=lambda p: F(p[axis],p[2]))
        for p,q in zip(row,row[1:]):
            edges[frozenset((p,q))]=i
            neighbors[p].add(q);neighbors[q].add(p)
    triangles=[]
    triangle_vertices=[]
    for p, adj in neighbors.items():
        for q,r in it.combinations(sorted(x for x in adj if x>p),2):
            third=edges.get(frozenset((q,r)))
            if third is None: continue
            ls=(edges[frozenset((p,q))],edges[frozenset((p,r))],third)
            if len(set(ls))==3:
                triangles.append(tuple(sorted(ls)))
                triangle_vertices.append((p,q,r))
    return dict(lines=lines, points=points, rows=rows, triangles=triangles,
                triangle_vertices=triangle_vertices)

def read_lines(path):
    return [primitive(l) for l in json.loads(Path(path).read_text())['lines_frac']]

def analyze(path):
    lines=read_lines(path); a=arrangement(lines)
    counts=Counter(i for t in a['triangles'] for i in t)
    print('\n',path,'n=',len(lines),'T=',len(a['triangles']), flush=True)
    print('multiples:',[sorted(v) for v in a['points'].values() if len(v)>2])
    print('saturated simple lines:',[i for i in range(len(lines))
        if len(a['rows'][i])==len(lines)-1 and counts[i]==len(lines)-2])
    for r in range(len(lines)):
        b=arrangement([l for i,l in enumerate(lines) if i!=r])
        bc=Counter(i for t in b['triangles'] for i in t)
        simple=[i for i in range(len(lines)-1)
            if len(b['rows'][i])==len(lines)-2 and bc[i]==len(lines)-3]
        original=[i if i<r else i+1 for i in simple]
        if original:
            print('remove',r,'T=',len(b['triangles']),'gain=',len(a['triangles'])-len(b['triangles']),
                  'Y candidates=',original,flush=True)

if __name__=='__main__':
    import sys
    for path in sys.argv[1:]: analyze(path)
