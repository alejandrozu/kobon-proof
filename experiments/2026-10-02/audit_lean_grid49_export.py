"""Independently parse the generated Lean49 data and re-evaluate its checks.

This checks the precise rational-box semantics in Parametric and HybridBoundary
using sparse Fraction arithmetic. It does not invoke or replace the Lean kernel.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import argparse,json,re,itertools as it,hashlib,time
ROOT=Path(__file__).resolve().parents[2]


def rational(s):return F(s.strip().strip('()'))
def vector(s):return [rational(x)for x in s.split(',')]
def triples(text,name):
    body=re.search(r'def '+name+r'\s*:\s*List Triple\s*:=\s*\[([^\n]*)\]',text).group(1)
    return [tuple(map(int,t))for t in re.findall(r'⟨(\d+),(\d+),(\d+)⟩',body)]


def source_path(explicit,name):
    if explicit is not None:return explicit.resolve()
    active=ROOT/'Kobon'/name
    if active.exists():return active
    candidates=list((ROOT/'research/three-hour-2026-10-02').rglob(name))
    assert len(candidates)==1,('Supply an explicit source path',name,candidates)
    return candidates[0]


def run(seed_source=None,exterior_source=None,out=None):
    started=time.time();base=source_path(seed_source,'BBLSeed49.lean');ext=source_path(exterior_source,'BBLSeed49Exterior.lean')
    text=base.read_text(encoding='utf-8');external=ext.read_text(encoding='utf-8')
    folder=ROOT/'research/three-hour-2026-10-02/constructions/uniform-grid49'
    seed=json.loads((folder/'uniform-seed.json').read_text());boundary=json.loads((folder/'visibility.json').read_text())
    slopes=[F(s)for s in seed['reciprocal_slopes']]
    lo=vector(re.search(r'def lo[^\n]*!\[([^\]]+)\]',text).group(1))
    hi=vector(re.search(r'def hi[^\n]*!\[([^\]]+)\]',text).group(1))
    assert len(lo)==len(hi)==24 and lo[-1]==0 and hi[-1]==F(1,100)
    tangent=json.loads((ROOT/'research/three-hour-2026-10-02/bbl/tangent48-bounds.json').read_text())['48']
    for k in range(1,24):
        lower,upper=map(F,tangent[str(k)]);assert lo[k-1]<=lower<=upper<=hi[k-1]
    source=re.search(r'def lines[^\n]*:= #\[([\s\S]*?)\]\s*\n\s*def lineAt',text).group(1)
    lines=[]
    for a,b,c in re.findall(r'⟨([^,]+),([^,]+),!\[([^\]]+)\]⟩',source):
        cc=vector(c);assert len(cc)==24
        lines.append((rational(a),rational(b),{j:x for j,x in enumerate(cc)if x}))
    assert len(lines)==49 and lines[0]==(F(0),F(-1),{})
    for i,v in enumerate(slopes):
        index,sign=(22-i,-1)if i<23 else(23,-1)if i==23 else(23,1)if i==24 else(i-25,1)
        assert lines[i+1]==(1/v,F(-1),{index:F(sign)/v}),(i,lines[i+1])
    actual=triples(text,'triangles');visible=triples(external,'visible')
    assert actual==list(map(tuple,seed['triangles'])) and len(set(actual))==767
    assert visible==list(map(tuple,boundary['visible_pairs'])) and len(set(visible))==24
    parameters=re.search(r'def parameters[^\n]*!\[([^\]]+)\]',text).group(1)
    assert re.findall(r'tan \((\d+)\*π/48\)',parameters)==list(map(str,range(1,24)))
    assert parameters.endswith(',epsilon')

    @lru_cache(None)
    def det(i,j):return lines[i][0]*lines[j][1]-lines[i][1]*lines[j][0]
    @lru_cache(None)
    def form(r,i,j):
        # evalForm = scale r.a (scale j.b i.c - scale i.b j.c)
        #          + scale r.b (scale i.a j.c - scale j.a i.c)
        #          - scale det(i,j) r.c.
        coefficients={}
        for label,factor in ((i,lines[r][0]*lines[j][1]-lines[r][1]*lines[j][0]),
                             (j,-lines[r][0]*lines[i][1]+lines[r][1]*lines[i][0]),(r,-det(i,j))):
            for p,c in lines[label][2].items():coefficients[p]=coefficients.get(p,F(0))+factor*c
        return tuple((p,c)for p,c in sorted(coefficients.items())if c)
    def interval(coefficients):
        lower=sum((c*(lo[p]if c>=0 else hi[p])for p,c in coefficients),F(0))
        upper=sum((c*(hi[p]if c>=0 else lo[p])for p,c in coefficients),F(0))
        return lower,upper
    @lru_cache(None)
    def oriented(r,i,j):return interval(tuple((p,c*det(i,j))for p,c in form(r,i,j)))
    directions=0;simple=0;epsilon_only=0
    for i,j in it.combinations(range(49),2):assert det(i,j);directions+=1
    for i,j,k in it.combinations(range(49),3):
        ff=form(k,i,j);lower,upper=interval(ff);exception=len(ff)==1 and ff[0][0]==23
        assert lower>0 or upper<0 or exception,('SimpleCheck',i,j,k,lower,upper)
        simple+=1;epsilon_only+=bool(exception and not(lower>0 or upper<0))
    checks=0
    for i,j,k in actual:
        assert 0<=i<j<k<49
        for r in range(49):
            iv=[oriented(r,a,b)for a,b in ((i,j),(i,k),(j,k))]
            assert all(z[0]>=0 for z in iv)or all(z[1]<=0 for z in iv),('TriangleCheck',i,j,k,r)
            checks+=1
    derivative=lambda r,l:det(r,l)*(lines[l][1]+2*lines[l][0])
    for a,b,c in lines:assert -2*a-b
    vischecks=0
    for i,j,k in visible:
        assert 0<=i<j<49 and k==49
        for r in range(49):
            lower,upper=oriented(r,i,j);di=derivative(r,i);dj=derivative(r,j)
            assert lower>=0 and di>=0 and dj>=0 or upper<=0 and di<=0 and dj<=0,('VisibleCheck',i,j,r)
            vischecks+=1
    files=[base,ext,folder/'uniform-seed.json',folder/'visibility.json',ROOT/'Kobon/Parametric.lean',ROOT/'Kobon/ParametricCached.lean',ROOT/'Kobon/HybridBoundary.lean']
    report=dict(passed=True,exact_family_identity=True,lean_boxes_contain_proved_tangent_bounds=True,
        line_count=49,parameter_count=24,direction_checks=directions,simple_checks=simple,
        epsilon_only_nonzero_cases=epsilon_only,triangle_count=len(actual),triangle_support_checks=checks,
        visible_count=len(visible),visible_support_checks=vischecks,
        epsilon_interval='0 < epsilon <= 1/100',normal=[1,-2],seconds=time.time()-started,
        files=[dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in files],
        scope='Exact Python re-evaluation of the generated Lean data and check semantics; does not establish compilation success or kernel acceptance')
    destination=out.resolve()if out is not None else folder/'lean-export-audit.json'
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='files'}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path)
    parser.add_argument('--seed-source',type=Path)
    parser.add_argument('--exterior-source',type=Path)
    args=parser.parse_args();run(args.seed_source,args.exterior_source,args.out)
