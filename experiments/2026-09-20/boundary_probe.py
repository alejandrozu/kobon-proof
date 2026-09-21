from extension_audit import *
import csv

ls=[primitive((F(m),-1,-F(b))) for m,b in list(csv.reader(open(Path(__file__).with_name('series18-lines.csv'))))[1:]]
for step in range(4):
    ar=arrangement(ls);n=len(ls);T=len(ar['triangles']);b=len(wedges(ar));options=exterior_choices(ar)
    print('n',n,'T',T,'unused',n*(n-2)-3*T,'wedges',b,'exterior capacity',options[0][0],flush=True)
    ls.append(options[0][1])
for name in ['certificate-20.json','certificate-26.json','certificate-32.json','certificate-38.json','certificate-50.json']:
    ls=read_lines(Path(__file__).with_name(name));ar=arrangement(ls)
    print(name,'T',len(ar['triangles']),'wedges',len(wedges(ar)),'exterior capacity',exterior_choices(ar)[0][0],flush=True)
