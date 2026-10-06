"""Exact bounded cap completions targeting two-A0 one-cap recipients.

This probes necessity of the remaining half-A0 curvature correction. Negative
screens are source-specific; no general geometric exclusion is inferred.
"""
from pathlib import Path
from itertools import combinations
from fractions import Fraction
import sys,json,time,argparse
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus'
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement,primitive
from check_marked_component_curvature import rational_profiles
from check_global_token_hypotheses import ledger

def profiles(lines):
    cc=rational_profiles(lines)
    if cc is None:return None
    return {p['vertex']:p for c in cc for p in c['profiles']}
def anti(p):return (p['d1'],p['d2'],p['marked'])==(2,4,0)
def candidates(lines):
    ar=arrangement(lines);seen=set(ar['lines'])
    for p,q in combinations(ar['points'],2):
        L=primitive((p[1]*q[2]-p[2]*q[1],p[2]*q[0]-p[0]*q[2],p[1]*q[0]-p[0]*q[1]))
        if L not in seen:seen.add(L);yield L
def assess(pp):
    A={v for v,p in pp.items() if anti(p)}
    R=[dict(vertex=v,anti_neighbors=[w for w in p['neighbors'] if w in A])
       for v,p in pp.items() if (p['d1'],p['d2'])==(1,3)]
    return A,R,max((len(p['anti_neighbors']) for p in R),default=0)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=90);ap.add_argument('--depth',type=int,default=3);args=ap.parse_args()
    start=time.time();tested=valid=preserved=0;records=[];wins=[];queue=[];seen=set()
    for name in ['antipodal-full-two-cap-fan.json','adjacent-antipodal-marked-full24.json','adjacent-antipodal-full15.json']:
        lines=arrangement(json.loads((BASE/name).read_text())['lines_frac'])['lines'];pp=profiles(lines);A,R,m=assess(pp)
        seen.add(tuple(sorted(lines)))
        queue.append((name,lines,A,0));records.append(dict(source=name,lines=len(lines),A0=len(A),max_N13_A0=m))
    while queue and time.time()-start<args.seconds and not wins:
        source,lines,oldA,depth=queue.pop(0)
        for L in candidates(lines):
            if time.time()-start>=args.seconds:break
            tested+=1;ll=lines+[L];key=tuple(sorted(ll))
            if key in seen:continue
            seen.add(key);pp=profiles(ll)
            if pp is None:continue
            valid+=1;A,R,m=assess(pp)
            if not oldA<=A:continue
            preserved+=1
            rec=dict(source=source,added_line=list(map(str,L)),depth=depth+1,n=len(ll),A0=len(A),recipients=R,max_N13_A0=m)
            if len(A)>len(oldA) or m>=2:records.append(rec)
            if m>=2:
                win=dict(**rec,lines_frac=[[str(x) for x in l] for l in ll],ledger=ledger(ll),profiles=list(pp.values()))
                wins.append(win);break
            if depth+1<args.depth:queue.append((source+' plus '+str(L),ll,A,depth+1))
    out=dict(tested=tested,distinct_arrangements=len(seen),all_triple_nonparallel=valid,old_antipodal_stars_preserved=preserved,depth_limit=args.depth,records=records,witnesses=wins,seconds=time.time()-start,scope='Bounded exact old-vertex-pair cap completions of three fixed source stars. Negative output does not prove an all-order exclusion.')
    (BASE/'two-antipodal-recipient-stress.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['tested','all_triple_nonparallel','old_antipodal_stars_preserved','records','seconds']}))
    print('Exact two-A0 recipient witnesses:',len(wins))
if __name__=='__main__':main()
