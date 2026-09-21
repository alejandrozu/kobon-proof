import sys,json,urllib.request,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'outputs/kobon-extension'))
from exact_geometry import primitive,arrangement
from boundary_extension import exterior_choices
from verify_direct import verify

url='https://raw.githubusercontent.com/ud1/kobon-solutions/master/gallery/certificates/43/43-25yi08ayzo963.json'
raw=urllib.request.urlopen(url).read()
seed=json.loads(raw)
lines=[primitive(x) for x in seed['lines_frac']]
old=arrangement(lines)
assert len(old['triangles'])==587
assert len(old['points'])==43*42//2 and all(len(v)==2 for v in old['points'].values())
gain,line=exterior_choices(old)[0]
new=arrangement(lines+[line])
assert len(new['triangles'])==587+gain==608
assert set(old['triangles'])<=set(new['triangles'])
assert len(new['points'])==44*43//2 and all(len(v)==2 for v in new['points'].values())
dest=root/'outputs/kobon-own-results/certificates/n044.json'
data=dict(n=44,triangle_count=608,lines_frac=[[str(v) for v in x] for x in lines+[line]],
    source_seed=url,source_sha256=hashlib.sha256(raw).hexdigest(),
    derivation='Published Parpalak-Utkin 43-line arrangement with 587 triangles, plus one exact exterior line with gain 21.',
    priority_status='Not established. Exact finite validity does not establish originality.',
    declared_parallel_pairs=[],declared_triple_points=[])
dest.write_text(json.dumps(data,indent=2),encoding='utf-8')
result=verify(dest)
result.update(adjacency_count=608,simple=True,preserves_all_input_triangles=True,gain=21)
(root/'outputs/kobon-own-results/verification_n044.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print('Input 43:587; gain',gain,'output 44:608; simple; old triangles preserved.')
