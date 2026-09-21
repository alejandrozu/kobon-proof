from extension_audit import *
import csv, random, sys

def find_extension(lines, tag):
    ar=arrangement(lines);old=set(ar['triangles']);target=len(old)+len(lines)//2
    tris=ar['triangle_vertices'];best=(len(old),None);checked=0
    for line in line_samples(ar):
        checked+=1;a,b,c=line
        if any(min(a*x+b*y-c*z for x,y,z in t)<0<max(a*x+b*y-c*z for x,y,z in t) for t in tris):continue
        tri=set(arrangement(lines+[line])['triangles'])
        if old<=tri and len(tri)>best[0]:
            best=(len(tri),line)
            if best[0]>=target:break
        if checked%5000==0:print('progress',tag,checked,best[0]-len(old),flush=True)
    result=dict(tag=tag,n=len(lines),triangles=len(old),best=best[0],witness=best[1],
        checked=checked,target_reached=best[0]>=target,lines_frac=[[str(x) for x in l] for l in lines])
    Path(__file__).with_name('extension-'+tag+'.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k!='lines_frac'}),flush=True)
    return result

rng=random.Random(91842)
for q in [3,4,5]:
    for trial in range(5):
        ls=[]
        for g in [-1,0,1]:
            for j in range(q):
                slope=F(g)+F(rng.randrange(-999,1000),1000000)
                intercept=F(j-q//2)+F(rng.randrange(-999,1000),10000)
                ls.append(primitive((slope,-1,-intercept)))
        find_extension(ls,f'grid-{q}-{trial}')

ls=[primitive((F(m),-1,-F(b))) for m,b in list(csv.reader(open(Path(__file__).with_name('series18-lines.csv'))))[1:]]
ar=arrangement(ls)
count,line=exterior_choices(ar)[0]
print('seed n19',len(ar['triangles']),'exterior gain',count,flush=True)
find_extension(ls+[line],'simple20')
