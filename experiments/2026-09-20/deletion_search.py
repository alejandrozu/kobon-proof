from research import *
import sys

def search(path,k):
    ls=read_lines(path); best=-1; winners=[]
    for removed in it.combinations(range(len(ls)),k):
        a=arrangement([l for i,l in enumerate(ls) if i not in removed])
        score=len(a['triangles'])
        if score>best:
            best=score;winners=[]
            print('NEW BEST',path,'n',len(ls)-k,'T',score,'remove',removed,flush=True)
        if score==best:winners.append(removed)
    print('FINAL',path,'n',len(ls)-k,'T',best,'winners',winners[:30],'number',len(winners),flush=True)
    output={'source':path,'n':len(ls)-k,'triangle_count':best,'removed':winners,
            'lines_frac':[[str(x) for x in l] for i,l in enumerate(ls) if i not in winners[0]]}
    Path(__file__).with_name(f'deletion-{len(ls)}-{k}.json').write_text(json.dumps(output,indent=2))

if __name__=='__main__':search(sys.argv[1],int(sys.argv[2]))
