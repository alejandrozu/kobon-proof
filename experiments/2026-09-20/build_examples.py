from check_boundary import *
import csv

def simplify_extension(lines, line, target):
    old=set(arrangement(lines)['triangles']);a,b,c=line
    for limit in [10**k for k in range(0,21)]:
        s=F(-a,b).limit_denominator(limit);v=F(c,b).limit_denominator(limit)
        cand=primitive((s,-1,-v));new=arrangement(lines+[cand])
        if len(new['points'])==len(lines)*(len(lines)+1)//2 and all(len(p)==2 for p in new['points'].values()) and old<=set(new['triangles']) and len(new['triangles'])>=target:
            return cand
    return line

ls=[(i,-1,-i*i) for i in range(4)]+[(7,-6,-15)]
examples=[]
for step in range(3):
    print('step',step,'lines',ls,flush=True)
    data=check(ls);data['lines_frac']=[[str(x) for x in l] for l in ls]
    examples.append(data)
    if step==2:break
    line=exterior_choices(arrangement(ls))[0][1]
    ls.append(line)
print(json.dumps(examples),flush=True)
Path(__file__).with_name('small-both-parities.json').write_text(json.dumps(examples,indent=2))

raw=json.loads(Path(__file__).with_name('extension-simple20.json').read_text())
ls=[primitive(l) for l in raw['lines_frac']]
line=simplify_extension(ls,raw['witness'],126)
ar=arrangement(ls+[line])
print('19-20-21 final added line',line,'count',len(ar['triangles']),flush=True)
data=dict(source='Parpalak-Utkin 19-line seed; exterior extension to 20; exact interior extension to 21',
          n=21,triangle_count=len(ar['triangles']),lines_frac=[[str(x) for x in l] for l in ls+[line]])
Path(__file__).with_name('simple21-extension.json').write_text(json.dumps(data,indent=2))
