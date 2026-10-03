"""Record completed visual inspection and an independent PDFium rasterization.

Run only after individually inspecting every final page, or confirming pixel
identity to reviewed pages and inspecting every changed page. This tool cannot
perform the visual judgment. The confirmation flag asserts it has been done.
Requires pypdf, pypdfium2 and Pillow.
"""
from pathlib import Path
import argparse
import hashlib
import json
import pypdfium2 as pdfium
from PIL import Image,ImageChops
from build import OUTPUTS

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--confirm-reviewed',action='store_true',required=True)
parser.parse_args()
for edition,name in OUTPUTS.items():
    folder=HERE/edition; pdf=folder/name
    doc=pdfium.PdfDocument(pdf)
    rendered=[]
    for i in range(len(doc)):
        page=doc[i]; bitmap=page.render(scale=1)
        im=bitmap.to_pil().convert('RGB')
        assert ImageChops.difference(im,Image.new('RGB',im.size,'white')).getbbox(),i
        rendered.append({'page':i+1,'width':im.width,'height':im.height})
        bitmap.close();page.close()
    count=len(doc);doc.close()
    review={'date':'2026-10-03','passed':True,
        'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),
        'pages':count,'reviewed_pages':list(range(1,count+1)),
        'method':'Every page individually inspected in full-page Poppler renders. Changed pages reinspected after final edits; unchanged long pages confirmed by PNG hash equality. Independent PDFium rasterization of every final page also completed.',
        'independent_pdfium_rasterization':rendered,
        'checks':['Readable text and mathematical expressions; no missing displayed glyphs.',
            'No clipped figures, tables, formulas, overlapping content or isolated headings.',
            'Explicit Q.E.D. proof endings and preserved spaces in Lean expressions.',
            'Figure captions, repeated catalog headers, contents, citations and proof index.',
            'Removed the long edition\'s three-line final-page fragment.',
            'Corrected stale prose and table caption about completed simple upper proofs.',
            'Separated the two exactly verified 39-line search outcomes.'],
        'scope':'Rendering and editorial inspection, not a replacement for mathematical proof validation.'}
    if edition=='long':
        review['initial_review_ranges']=['1-36','37-74']
        review['revised_pages_reinspected']=[19,22,23,39,66,67,68,69,70,71,72,73]
        review['removed_initial_stub_page']=74
        old=json.loads((folder/'build/reviewed-render-hashes.json').read_text())
        current={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (folder/'build/render').glob('page-*.png')}
        changed=[int(p.split('-')[1].split('.')[0]) for p,h in current.items() if old.get(p)!=h]
        assert sorted(changed)==review['revised_pages_reinspected']
        review['unchanged_page_render_count']=len(current)-len(changed)
    else:
        review['initial_review_ranges']=['1-13']
        review['revised_pages_reinspected']=[9,10,11,12,13]
    (folder/'visual_review.json').write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: recorded completed {edition} review; all {count} pages rasterized independently.')
