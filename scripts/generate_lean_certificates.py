"""Generate readable Lean data from exact coordinate witnesses.

Generation is untrusted: Lean checks the line coordinates and each listed
triangle independently.  No numerical search package is needed.
"""
from pathlib import Path
import hashlib,json,sys,importlib.util

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research'/'kobon-hybrid'))
from exact_geometry import arrangement,primitive


def prepare():
    catalog={}
    for p in sorted((ROOT/'research').rglob('*.json')):
        d=json.loads(p.read_text(encoding='utf-8-sig'))
        if not isinstance(d,dict) or 'lines_frac' not in d:continue
        n=d['n'];T=d['triangle_count']
        lines=[primitive(x) for x in d['lines_frac']]
        identity=hashlib.sha256(json.dumps(lines,separators=(',',':')).encode()).hexdigest()
        key=f'N{n:03d}T{T:05d}H{identity[:8]}'
        if key in catalog:
            catalog[key]['sources'].append(p.relative_to(ROOT).as_posix());continue
        ar=arrangement(lines);tris=sorted(ar['triangles'])
        assert len(tris)==T,(p,len(tris),T)
        assert len(set(tris))==T
        assert all(lines[i][0]*lines[j][1]!=lines[i][1]*lines[j][0]
                   for i in range(n) for j in range(i+1,n))
        simple=len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
        module=ROOT/'Kobon'/'Certificates'/f'{key}.lean'
        module.parent.mkdir(parents=True,exist_ok=True)
        body='import Kobon.Geometry\n\nnamespace Kobon.Certificates.'+key+'\n\n'
        body+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
        body+='def lines : Array (Line ℤ) := #[\n'
        body+=',\n'.join('  ⟨'+','.join(str(x) for x in l)+'⟩' for l in lines)+'\n]\n\n'
        body+='def triangles : List Triple := [\n'
        body+=',\n'.join('  ⟨'+','.join(str(x) for x in t)+'⟩' for t in tris)+'\n]\n\n'
        body+=f'theorem checked : validate lines triangles {T} = true := by native_decide\n\n'
        body+=f'theorem lower_bound : LowerBound {n} {T} :=\n  validate_sound lines triangles {T} checked\n\n'
        body+='#print axioms checked\n#print axioms lower_bound\n\nend Kobon.Certificates.'+key+'\n'
        module.write_text(body,encoding='utf-8')
        catalog[key]=dict(n=n,triangles=T,simple=simple,coordinate_sha256=identity,
            module='Kobon.Certificates.'+key,theorem='Kobon.Certificates.'+key+'.lower_bound',
            sources=[p.relative_to(ROOT).as_posix()],lean_source=module.relative_to(ROOT).as_posix())
        print('GENERATED',key,flush=True)
    dest=ROOT/'verification';dest.mkdir(exist_ok=True)
    (dest/'certificate-index.json').write_text(json.dumps(list(catalog.values()),indent=2)+'\n')
    return catalog

if __name__=='__main__':
    if len(sys.argv)>1:
        raise SystemExit('This command regenerates the full index; no partial-selection arguments are accepted.')
    prepare()
