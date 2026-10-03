"""Render every PDF page with Poppler and assemble labeled visual-review sheets.

Requires pdftoppm on PATH, pypdf and Pillow. Rendering is not itself a visual
review: visual_review.json is recorded separately after inspecting the pages.
"""
from pathlib import Path
import argparse
import subprocess
from PIL import Image,ImageDraw
from pypdf import PdfReader
from build import OUTPUTS

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--edition',choices=['long','journal','both'],default='both')
args=parser.parse_args()
for edition in OUTPUTS if args.edition=='both' else [args.edition]:
    folder=HERE/edition
    pdf=folder/OUTPUTS[edition]
    out=folder/'build/render'
    out.mkdir(parents=True,exist_ok=True)
    for pattern in ('page-*.png','contact-*.png'):
        for old in out.glob(pattern): old.unlink()
    subprocess.run(['pdftoppm','-r','100','-png',str(pdf),str(out/'page')],check=True)
    pages=sorted(out.glob('page-*.png'))
    assert len(pages)==len(PdfReader(pdf).pages)
    for offset in range(0,len(pages),6):
        sheet=Image.new('RGB',(1260,1820),'#dddddd')
        draw=ImageDraw.Draw(sheet)
        for j,path in enumerate(pages[offset:offset+6]):
            im=Image.open(path).convert('RGB')
            im.thumbnail((610,860))
            x=(j%2)*630+(630-im.width)//2; y=(j//2)*606+30
            # Scale to 560px height so six pages fit while preserving aspect.
            im.thumbnail((610,565))
            x=(j%2)*630+(630-im.width)//2
            sheet.paste(im,(x,y))
            draw.text(((j%2)*630+12,(j//2)*606+8),f'{edition} page {offset+j+1}',fill='black')
        sheet.save(out/f'contact-{offset+1:03d}-{min(offset+6,len(pages)):03d}.png')
    print(f'Rendered {edition}: {len(pages)} pages. Inspect full-page renders where necessary.')
