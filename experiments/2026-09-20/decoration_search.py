"""Search extra lines through pairs of vertices of the fixed eight-line seed."""
from even_family import *

def line_through(p,q):
    x,y,z=p;u,v,w=q
    return primitive((y*w-z*v,z*u-x*w,y*u-x*v))

def run(t):
    ls=build(t);coreindices=list(range(7))+[len(ls)-1]
    seed=[ls[i] for i in coreindices]
    vertices=list(arrangement(seed)['points'])
    original=set(arrangement(ls)['lines']);tested=set();best=0;winners=[]
    for p,q in it.combinations(vertices,2):
        r=line_through(p,q)
        if r in original or r in tested: continue
        tested.add(r)
        ar=arrangement(ls+[r]);score=len(ar['triangles'])
        if score>best:
            best=score;winners=[]
            print('best t',t,'n',len(ls)+1,'T',score,'vertices',sorted(arrangement(seed)['points'][p]),sorted(arrangement(seed)['points'][q]),flush=True)
        if score==best:
            winners.append(dict(p=sorted(arrangement(seed)['points'][p]),q=sorted(arrangement(seed)['points'][q]),r=[str(x) for x in r]))
    print('DONE',t,'best',best,'tested',len(tested),'winner descriptions',[(w['p'],w['q']) for w in winners],flush=True)
    out=dict(n=len(ls)+1,triangle_count=best,winners=winners,lines_frac=[[str(x) for x in l] for l in ls]+[winners[0]['r']])
    Path(__file__).with_name(f'decorated-{len(ls)+1}.json').write_text(json.dumps(out,indent=2))

if __name__=='__main__':run(int(sys.argv[1]))
