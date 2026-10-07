"""Exact replay of root's full triple fan with antipodal ordinary caps."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(Path(__file__).resolve().parent));sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from check_global_token_hypotheses import ledger
from census_triple_fan_types import local_types
from exact_geometry import arrangement,primitive

if __name__=='__main__':
    lines=list(map(primitive,[(1,-10,0),(1,-1,0),(1,1,0),(2,1,3),(-3,1,4),(0,1,1),(1,5,-12)]));ar=arrangement(lines);r=ledger(lines);fans=local_types(lines);center=next(p for p in fans if p['core']==['0','0','1'])
    assert center['ordinary_shared']==2 and center['core_shared']==4 and center['triangle_sectors']==6 and center['ordinary_caps_antipodal']
    result=dict(passed=True,attribution='New explicit geometric scope witness supplied by the root research branch',ledger=r,lines_frac=[[str(v) for v in l] for l in lines],triangles=[list(t) for t in ar['triangles']],center=center,core_fans=fans,status='Exact rational finite incidence verification, no new lower-bound record or all-order theorem')
    p=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/antipodal-full-two-cap-fan.json';p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(ledger=r,center=center,fan_types=[dict(core=f['core'],d1=f.get('ordinary_shared',0),d2=f.get('core_shared',0),fan=f['triangle_sectors']) for f in fans])),flush=True)
