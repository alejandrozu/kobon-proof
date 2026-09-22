"""Exact survival clauses and path DP for collinear triple-point resolutions.

One independent offset on a private line at each triple realizes either local
orientation, for sufficiently small magnitude. An old triangle survives iff
its one or two incident triple-resolution choices match its recorded signs.
"""
import itertools,json,random,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from exact_geometry import arrangement,read_lines,intersection

def ev(l,p):return l[0]*p[0]+l[1]*p[1]-l[2]*p[2]
def sgn(x):return (x>0)-(x<0)

def model(lines):
    ar=arrangement(lines);ls=ar['lines'];n=len(ls)
    core={p:inc for p,inc in ar['points'].items()if len(inc)>2}
    if not core:return None
    assert all(len(inc)==3 for inc in core.values())
    common=set.intersection(*map(set,core.values()))
    assert common
    Y=min(common);row=[p for p in ar['rows'][Y]if p in core]
    idx={p:i for i,p in enumerate(row)};q=len(row)
    private=[min(core[p]-{Y})for p in row]
    assert len(set(private))==q
    clauses=[];points={pair:intersection(*(ls[i]for i in pair))for pair in itertools.combinations(range(n),2)}
    for tri in ar['triangles']:
        required={}
        pairs=list(itertools.combinations(tri,2))
        for pair in pairs:
            p=points[pair]
            if p not in core:continue
            u=idx[p];extra=next(iter(core[p]-set(pair)))
            targets=[sgn(ev(ls[extra],points[t]))for t in pairs if t!=pair]
            assert targets[0] and targets[0]==targets[1]
            alt=list(ls);a,b,c=alt[private[u]];alt[private[u]]=(a,b,c+1)
            value=ev(alt[extra],intersection(*(alt[i]for i in pair)))
            assert value
            required[u]=1 if sgn(value)==targets[0]else 0
        assert len(required)<=2
        if len(required)==2:assert max(required)-min(required)==1
        clauses.append(required)
    const=sum(not c for c in clauses);unary=[[0,0]for _ in row];edge=[[[0,0],[0,0]]for _ in range(q-1)]
    for c in clauses:
        if len(c)==1:
            i,s=next(iter(c.items()));unary[i][s]+=1
        if len(c)==2:
            i=min(c);edge[i][c[i]][c[i+1]]+=1
    dp=unary[0][:];paths=[(0,),(1,)]
    for i in range(1,q):
        nxt=[];npaths=[]
        for b in [0,1]:
            a=max([0,1],key=lambda a:dp[a]+edge[i-1][a][b])
            nxt.append(dp[a]+edge[i-1][a][b]+unary[i][b]);npaths.append(paths[a]+(b,))
        dp,paths=nxt,npaths
    b=max([0,1],key=lambda b:dp[b]);best=const+dp[b]+q
    brute=[]
    if q<=12:
        for bits in itertools.product([0,1],repeat=q):
            brute.append(q+sum(all(bits[i]==s for i,s in c.items())for c in clauses))
        assert max(brute)==best
    return dict(n=n,T=len(clauses),q=q,core_line=Y,private_lines=private,
        best_simple_resolution=best,loss=len(clauses)-best,best_choices=paths[b],
        unchanged_triangles=const,unary=unary,neighbor_pairs=edge,
        all_resolution_counts=brute,clauses=[sorted(c.items())for c in clauses])

def main():
    base=ROOT/'research/six-hour-2026-09-21/general-bounds'
    records=[]
    sources=list((base/'parpalak-utkin-current').glob('certificate-*.json'))
    sources.extend((base/'maiorana14').glob('certificate-*.json'))
    for source in sources:
        ls=read_lines(source)
        try:rec=model(ls)
        except AssertionError:continue # Maiorana's four-point noncollinear type.
        if rec:
            rec['source']=str(source.relative_to(ROOT));records.append(rec)
            print({k:rec[k]for k in ['n','T','q','best_simple_resolution','loss','source']},flush=True)
    (base/'collinear-resolution-model.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':main()
