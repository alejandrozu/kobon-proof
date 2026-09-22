"""Bipartite relaxation for small perturbations of the FP triple arrangement.

This is an exploratory combinatorial certificate, not a coordinate proof.
Concurrency is identified by the exact modular identity i+j+k == 0 (mod n),
while cosine ordering and face coloring use floating point and are audited by
minimum separation diagnostics. The conflict graph ignores global realizability.
"""
from __future__ import annotations
import argparse, collections, itertools, json, math
from pathlib import Path
import numpy as np

def base(n):
    theta = np.arange(n)*math.pi/n
    ls = np.column_stack((np.sin(theta), np.cos(theta), np.sin(3*theta)))
    vertices = {}
    rows = []
    minsep = float('inf')
    for i in range(n):
        row = {}
        for j in range(n):
            if i == j: continue
            k = (-i-j)%n
            v = tuple(sorted({i,j,k}))
            if v not in vertices:
                a,b = v[:2]
                vertices[v] = np.linalg.solve(ls[[a,b],:2],ls[[a,b],2])
            row[v] = float(math.cos(theta[i]+2*theta[j]))
        ordered = sorted(row, key=row.get)
        minsep = min([minsep]+[row[b]-row[a] for a,b in zip(ordered,ordered[1:])])
        rows.append(ordered)
    edges = {}
    neighbors = collections.defaultdict(set)
    for i,row in enumerate(rows):
        for p,q in zip(row,row[1:]):
            edges[frozenset((p,q))] = i
            neighbors[p].add(q)
            neighbors[q].add(p)
    faces = []
    for p,adj in neighbors.items():
        for q,r in itertools.combinations(sorted(x for x in adj if x>p),2):
            if frozenset((q,r)) not in edges: continue
            supports = tuple(sorted((edges[frozenset((p,q))],edges[frozenset((p,r))],edges[frozenset((q,r))])))
            if len(set(supports)) != 3: continue
            center = (vertices[p]+vertices[q]+vertices[r])/3
            signs = ls[:,:2]@center-ls[:,2]
            color = int(np.count_nonzero(signs<0)%2)
            faces.append(dict(vertices=(p,q,r), supports=supports,color=color))
    return vertices,faces,minsep

def matching(graph, left):
    # Standard augmenting path bipartite matching, exact on the computed graph.
    partner = {}
    def augment(a,visited):
        for b in sorted(graph[a]):
            if b in visited: continue
            visited.add(b)
            if b not in partner or augment(partner[b],visited):
                partner[b] = a
                return True
        return False
    for a in left: augment(a,set())
    return partner

def analyze(n):
    vertices,faces,minsep = base(n)
    incident = collections.defaultdict(list)
    for a,face in enumerate(faces):
        for v in face['vertices']:
            if len(v)==3: incident[v].append(a)
    graph = collections.defaultdict(set)
    for v,ids in incident.items():
        for a,b in itertools.combinations(ids,2):
            if faces[a]['color'] != faces[b]['color']:
                graph[a].add(b);graph[b].add(a)
    left = [i for i,f in enumerate(faces) if f['color']==0]
    right = [i for i,f in enumerate(faces) if f['color']==1]
    matched = matching(graph,left)
    triples = sum(len(v)==3 for v in vertices)
    # Recover a maximum independent set using Koenig's alternating-path proof.
    inverse = {v:k for k,v in matched.items()}
    reachable = set(a for a in left if a not in inverse)
    todo = list(reachable)
    while todo:
        a = todo.pop()
        if a in left:
            nexts = graph[a]-({inverse[a]} if a in inverse else set())
        else:
            nexts = {matched[a]} if a in matched else set()
        for b in nexts-reachable:
            reachable.add(b);todo.append(b)
    independent = (set(left)&reachable) | (set(right)-reachable)
    assert len(independent)==len(faces)-len(matched)
    assert all(not(graph[a]&independent) for a in independent)
    bound = triples+len(independent)
    return dict(n=n, base_triangles=len(faces), triple_vertices=triples,
                colors=[len(left),len(right)], matching=len(matched),
                relaxed_perturbed_upper=bound,
                uniform_shift_count=(n*(n-3))//3+1,
                minimum_order_gap=minsep,
                max_degree=max(map(len,graph.values()),default=0),
                conflict_edges=sum(map(len,graph.values()))//2,
                selected_faces=[faces[i]['supports'] for i in sorted(independent)])

if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--max-n',type=int,default=80)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    data=[analyze(n) for n in range(3,args.max_n+1)]
    args.out.write_text(json.dumps(data,indent=2)+'\n')
    for row in data:
        print(json.dumps({k:v for k,v in row.items() if k!='selected_faces'}),flush=True)
