"""Recheck every distinct promoted coordinate witness by two exact counters."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,sys,time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement
from verify_direct import verify

def main():
    rows=[]
    for d in json.loads((ROOT/'verification/certificate-index.json').read_text()):
        start=time.monotonic();p=ROOT/d['sources'][0]
        data=json.loads(p.read_text(encoding='utf-8-sig'))
        ar=arrangement(data['lines_frac'])
        simple=len(ar['points'])==d['n']*(d['n']-1)//2 and all(len(s)==2 for s in ar['points'].values())
        assert simple==d['simple']
        assert len(ar['triangles'])==d['triangles']
        assert len(set(ar['triangles']))==d['triangles']
        identity=hashlib.sha256(json.dumps(ar['lines'],separators=(',',':')).encode()).hexdigest()
        assert identity==d['coordinate_sha256']
        result=verify(p)
        rows.append(dict(module=d['module'],n=d['n'],triangles=d['triangles'],simple=simple,
            coordinate_sha256=identity,adjacency_count=len(ar['triangles']),
            direct_count=result['triangles'],passed=True,seconds=round(time.monotonic()-start,3)))
    report=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),
        scope='Exact finite counts and simplicity; no infinite geometric claim.',results=rows)
    (ROOT/'verification/coordinate-summary.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
