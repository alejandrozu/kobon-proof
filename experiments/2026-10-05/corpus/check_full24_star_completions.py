"""Exact bounded completions of the seven-line antipodal full star.

Every distinct line through two actual old vertices is tested. Higher
multiplicity and parallel completions are excluded explicitly. This is a
finite source-specific diagnostic, not an all-star exclusion theorem.
"""
from pathlib import Path
import json,sys,itertools as it,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement,primitive
from check_marked_component_curvature import rational_profiles
from check_global_token_hypotheses import ledger

if __name__=='__main__':
    start=time.time();base=ROOT/'research/openmath-seven-hour-2026-10-05/corpus';source=base/'antipodal-full-two-cap-fan.json';raw=json.loads(source.read_text());old=raw['lines_frac'];ar=arrangement(old);vertices=list(ar['points']);seen=set(ar['lines']);cases=[];wins=[]
    for p,q in it.combinations(vertices,2):
        C=primitive((p[1]*q[2]-p[2]*q[1],p[2]*q[0]-p[0]*q[2],p[1]*q[0]-p[0]*q[1]))
        if C in seen:continue
        seen.add(C);ls=old+[C];cc=rational_profiles(ls)
        if cc is None:continue
        profiles={x['vertex']:x for c in cc for x in c['profiles']};c=profiles.get('(0, 0, 1)');g=profiles.get('(1, 1, 1)')
        if not c or not g:continue
        if [c['d1'],c['d2'],c['marked'],c['fan']]!=[2,4,0,6]:continue
        rec=dict(added_line=C,g_profile=g,center_profile=c,ledger=ledger(ls));cases.append(rec)
        if [g['d1'],g['d2'],g['fan']]==[2,4,6]:wins.append(rec)
    out=dict(source=str(source.relative_to(ROOT)),old_vertices=len(vertices),pair_lines_tested=len(seen)-len(ar['lines']),center_preserved_cases=len(cases),full_neighbor_completions=wins,antipodal_neighbor_completions=[r for r in wins if r['g_profile']['marked']==0],seconds=time.time()-start,scope='All vertex-pair one-line completions of this fixed seven-line witness. No unrestricted antipodal-adjacency exclusion inferred.')
    (base/'full24-star-completions.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
