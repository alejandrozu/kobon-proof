"""Audit October manuscript outputs, immutable proof links, and preserved releases.

Requires a complete repository checkout and pypdf. This audit supplements the
separate Lean build, exact certificate replays, and human/model visual review;
it does not turn a manuscript proof or external calculation into a Lean proof.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
from urllib.parse import urlsplit,unquote
from pypdf import PdfReader
from build import OUTPUTS

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PIN='2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8'
sys.path.insert(0,str(ROOT/'paper/scripts'))
from pdf_preflight import audit_pdf

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(ref,path):
    return subprocess.check_output(['git','show',f'{ref}:{path}'],cwd=ROOT)

summary=json.loads((ROOT/'verification/lean-summary.json').read_text(encoding='utf-8'))
assert summary['complete'] and len(summary['results'])==270
assert len(summary['source_sha256'])==375
for path,digest in summary['source_sha256'].items():
    assert sha(ROOT/path)==digest, f'Checked Lean source changed: {path}'
old={
    'paper/Kobon_triangle_constructions.pdf':'24e069db61a3c3383f86d403a401ee83632aeb41e381cf80be6204c659cba667',
    'paper/journal/Kobon_journal_version.pdf':'8d79c549c8b473ae1374ae589aa129b628205e5d8ca43f0c8aaa8c4e4bd27214'}
for path,digest in old.items(): assert sha(ROOT/path)==digest,f'Historical PDF changed: {path}'
catalog=json.loads((ROOT/'verification/certificate-index.json').read_text(encoding='utf-8'))
assert len(catalog)==138 and sum(bool(r['simple']) for r in catalog)==104
sources={}
def check_link(url):
    parsed=urlsplit(url)
    if parsed.netloc!='github.com': return
    parts=unquote(parsed.path).split('/')
    if len(parts)<6 or parts[1:3]!=['alejandrozu','kobon-proof'] or parts[3]!='blob': return
    ref=parts[4]; path='/'.join(parts[5:])
    if not re.fullmatch('[0-9a-f]{40}',ref):
        assert (ROOT/path).is_file(),f'Unresolved manuscript repository link: {url}'
        return
    key=(ref,path)
    if key not in sources: sources[key]=blob(ref,path)
    if parsed.fragment.startswith('L'):
        line=int(parsed.fragment[1:].split('-')[0])
        assert 1<=line<=len(sources[key].splitlines()),f'Out-of-range line anchor: {url}'

reports=[]
for edition,name in OUTPUTS.items():
    folder=HERE/edition; pdf=folder/name
    report=audit_pdf(pdf)
    assert report['passed']
    reader=PdfReader(pdf)
    assert reader.metadata.author=='Alejandro Zarzuelo Urdiales'
    if edition=='journal': assert len(reader.pages)<=15
    urls=[]
    for page in reader.pages:
        for annotation in page.get('/Annots',[]):
            obj=annotation.get_object(); action=obj.get('/A')
            if action and action.get('/URI'): urls.append(str(action['/URI']))
    for url in set(urls): check_link(url)
    proof_urls=[u for u in set(urls) if f'/blob/{PIN}/Kobon/' in u]
    assert len(proof_urls)>=20, f'{edition}: insufficient clickable proof links'
    log=(folder/'compilation.log').read_text(encoding='utf-8',errors='replace')
    build_report=json.loads((folder/'compilation.json').read_text(encoding='utf-8'))
    assert build_report['pdf_sha256']==sha(pdf)
    assert build_report['compiler_log_sha256']==sha(folder/'compilation.log')
    for source,digest in build_report['source_sha256'].items():
        assert sha(folder/source)==digest, f'PDF source changed since compilation: {edition}/{source}'
    assert not re.search(r'Overfull \\[hv]box|There were undefined|(?:Reference|Citation) .* undefined|multiply defined|Missing character|^! ',log,re.MULTILINE)
    review=json.loads((folder/'visual_review.json').read_text(encoding='utf-8'))
    assert review['pdf_sha256']==sha(pdf) and review['pages']==len(reader.pages)
    assert review['passed'] and review['reviewed_pages']==list(range(1,len(reader.pages)+1))
    report.update({'edition':edition,'clickable_urls':len(set(urls)),
        'immutable_lean_urls':len(proof_urls),'visual_review_matches':True})
    reports.append(report)

proof_map=json.loads((HERE/'shared/proof_map.json').read_text(encoding='utf-8'))
assert proof_map['math_commit']==PIN
for claim in proof_map['claims']:
    for ref in claim.get('refs',[]):
        path=ref['path']
        if 'source_sha256' in ref:
            # Maps are pinned to Git blobs, whose line endings are authoritative.
            key=(PIN,path)
            if key not in sources: sources[key]=blob(PIN,path)
            data=sources[key]
            assert hashlib.sha256(data).hexdigest()==ref['source_sha256'],f'Proof-map hash: {path}'
        if 'url' in ref: check_link(ref['url'])

report={'passed':True,'date':'2026-10-03','math_commit':PIN,
    'checked_lean_sources':375,'checked_build_targets':270,
    'finite_certificates':138,'simple_certificates':104,
    'historical_pdf_sha256':old,'proof_claims':len(proof_map['claims']),
    'immutable_link_source_files':len(sources),'manuscripts':reports}
(HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(f'PASS: two PDFs, {len(proof_map["claims"])} mapped claims, 375 unchanged checked Lean sources, original PDFs preserved.')
