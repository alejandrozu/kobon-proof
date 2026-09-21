import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parents[2]/'outputs'/'kobon-hybrid'))
from exterior_extension import *

base=Path(__file__).parents[2]/'outputs'/'kobon-hybrid'/'certificates'
for n in (11,21,41,81,161):
    ar=arrangement(read_lines(base/f'n{n:03d}.json'))
    ws=wedges(ar)
    profile=[]
    for x,y in ((10,-13),(1,0),(0,1),(0,-1)):
        count=sum(x*u[0]+y*u[1]>0 and x*v[0]+y*v[1]>0 for u,v in ws)
        profile.append(((x,y),count))
    labels=[]
    for p,incident in ar['points'].items():
        if all(p in (ar['rows'][i][0],ar['rows'][i][-1]) for i in incident):
            labels.append(tuple(sorted(incident)))
    oldq=(n-1)//2
    print(n,'PROFILE',profile,'old pairs',sum(max(x)<=oldq for x in labels),
          'mixed',sum(min(x)<=oldq<max(x) for x in labels),
          'new',sum(min(x)>oldq for x in labels),flush=True)
    if n<=21:print('WEDGES',labels,flush=True)
