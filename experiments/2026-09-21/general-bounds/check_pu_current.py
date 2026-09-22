"""Independently recount published exact Parpalak--Utkin gallery data.

Downloads coordinate facts, records immutable provenance, and uses two exact
counts: elementary-segment adjacency and open-interior evaluation signs.
"""
import collections,hashlib,itertools,json,math,sys,urllib.request
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
sys.path.insert(0,str(Path(__file__).parent))
from exact_geometry import arrangement,read_lines
from clean_line_budget import inspect
BASE='https://raw.githubusercontent.com/ud1/kobon-solutions/'
OUT=ROOT/'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current'
ORDERS={8,14,20,26,32,36,38,42,46,50}

def get(url):
    return urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Kobon-independent-verification'}),timeout=30).read()

def direct_count(raw):
    """Independent integer determinant sign count, allowing parallel lines."""
    lines=[]
    for row in raw['lines_frac']:
        q=list(map(Fraction,row));den=math.lcm(*(v.denominator for v in q))
        lines.append(tuple(v.numerator*(den//v.denominator)for v in q))
    pairs={};pos={};neg={}
    for i,j in itertools.combinations(range(len(lines)),2):
        a,b,c=lines[i];d,e,f=lines[j];w=a*e-b*d
        if not w:continue
        p=(c*e-b*f,a*f-c*d,w)
        if w<0:p=tuple(-v for v in p)
        pairs[i,j]=p
        x,y,w=p;sp=sn=0
        for k,(A,B,C)in enumerate(lines):
            ev=A*x+B*y-C*w
            if ev>0:sp|=1<<k
            if ev<0:sn|=1<<k
        pos[i,j]=sp;neg[i,j]=sn
    tris=[]
    for i,j,k in itertools.combinations(range(len(lines)),3):
        keys=[(i,j),(i,k),(j,k)]
        if any(t not in pairs for t in keys):continue
        x,y,w=pairs[i,j];a,b,c=lines[k]
        if a*x+b*y==c*w:continue
        p=pos[i,j]|pos[i,k]|pos[j,k]
        m=neg[i,j]|neg[i,k]|neg[j,k]
        if not p&m:tris.append((i,j,k))
    return tris

def main():
    OUT.mkdir(exist_ok=True)
    co=json.loads(get('https://api.github.com/repos/ud1/kobon-solutions/commits/master'))
    sha=co['sha']; tree=json.loads(get(f'https://api.github.com/repos/ud1/kobon-solutions/git/trees/{sha}?recursive=1'))
    paths=[r['path']for r in tree['tree']if r['path'].startswith('gallery/certificates/')and r['path'].endswith('.json')and int(r['path'].split('/')[2])in ORDERS]
    records=[]
    for path in paths:
        blob=get(BASE+sha+'/'+path);d=json.loads(blob);n=d['n']
        rawpath=OUT/f'upstream-{n:03d}.json';rawpath.write_bytes(blob)
        ls=read_lines(rawpath);ar=arrangement(ls);direct=direct_count(d)
        assert set(ar['triangles'])==set(direct)
        assert len(direct)==d['triangle_count']
        rec=inspect(ls)
        rec.update(source_path=path,source_sha256=hashlib.sha256(blob).hexdigest(),
            incidence_multiplicities=dict(collections.Counter(len(v)for v in ar['points'].values())),
            multiple_incidence=sorted(sorted(v)for v in ar['points'].values()if len(v)>=3),
            independent_sign_counter='PASS')
        d.update(triangles=[list(t)for t in direct],
            attribution='Published gallery of Roman Parpalak and Denis Utkin; original discovery attribution as recorded by OEIS and gallery',
            upstream_commit=sha,upstream_url=f'https://github.com/ud1/kobon-solutions/blob/{sha}/{path}',
            independent_verification_utc='2026-09-22')
        (OUT/f'certificate-{n:03d}.json').write_text(json.dumps(d,indent=2)+'\n')
        records.append(rec); print(json.dumps(rec),flush=True)
    (OUT/'verification.json').write_text(json.dumps(dict(upstream_commit=sha,commit_date=co['commit']['committer']['date'],
        checked_utc='2026-09-22',records=records),indent=2)+'\n')

if __name__=='__main__':main()
