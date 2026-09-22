"""Fetch attributed Maiorana 2026 candidate data; independently verify exact faces.

The downloaded author's code is not executed. Coordinate data use CC BY 4.0.
"""
import hashlib,itertools,json,sys,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
sys.path.insert(0,str(Path(__file__).parent))
from exact_geometry import arrangement,read_lines
from clean_line_budget import inspect
from verify_direct import verify

BASE='https://raw.githubusercontent.com/rufio72/kobon_triangles_k14/'
OUT=ROOT/'research/six-hour-2026-09-21/general-bounds/maiorana14'
def get(url):
    req=urllib.request.Request(url,headers={'User-Agent':'Kobon-independent-verification'})
    return urllib.request.urlopen(req,timeout=30).read()

def main():
    OUT.mkdir(exist_ok=True)
    commit=json.loads(get('https://api.github.com/repos/rufio72/kobon_triangles_k14/commits/main'))
    sha=commit['sha']; report=[]
    for name in ['LICENSE','README.md','SHA256SUMS.txt']:
        (OUT/name).write_bytes(get(BASE+sha+'/'+name))
    for k in range(1,16):
        raw=get(BASE+sha+f'/sol{k}/lines_rational.json')
        path=OUT/f'sol{k:02d}.json';path.write_bytes(raw)
        ls=read_lines(path); ar=arrangement(ls); rec=inspect(ls)
        triples=sorted(sorted(inc)for inc in ar['points'].values()if len(inc)>=3)
        rec.update(solution=k,source_sha256=hashlib.sha256(raw).hexdigest(),multiple_incidence=triples)
        assert rec['T']==54,rec
        assert rec['parallel_pairs']==0,rec
        assert all(len(t)==3 for t in triples),rec
        d=json.loads(raw)
        d.update(n=14,triangle_count=54,triangles=[list(t)for t in ar['triangles']],
            attribution='Andrea Maiorana, August 11-12 2026, CC BY 4.0',
            upstream_url=f'https://github.com/rufio72/kobon_triangles_k14/blob/{sha}/sol{k}/lines_rational.json',
            upstream_commit=sha,independent_verification='Exact arrangement enumeration and general-bounds side-use audit, 2026-09-22')
        certpath=OUT/f'certificate-{k:02d}.json'
        certpath.write_text(json.dumps(d,indent=2)+'\n')
        verify(certpath)
        rec['independent_interior_sign_counter']='PASS'
        report.append(rec); print(json.dumps(rec),flush=True)
    (OUT/'verification.json').write_text(json.dumps(dict(source_commit=sha,source_commit_date=commit['commit']['committer']['date'],
        checked_utc='2026-09-22',author='Andrea Maiorana',license='CC-BY-4.0',records=report),indent=2)+'\n')

if __name__=='__main__':main()
