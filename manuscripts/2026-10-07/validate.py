"""Validate publication proofs, immutable links, preservation and reviewed PDFs."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
from urllib.parse import urlsplit,unquote
from pypdf import PdfReader
from build import OUTPUTS
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PIN='f44f23ee062a255f5cad7d39188fd55c0feb83a8'
VERIFICATION_PIN='af74635d8b25b32703088460bc41854bb18e1a05'
BASELINE='112409e2c62b78ecff7adcad49f1e014ea5f0773'
sys.path.insert(0,str(ROOT/'paper/scripts'))
from pdf_preflight import audit_pdf

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(ref,path):return subprocess.check_output(['git','show',f'{ref}:{path}'],cwd=ROOT)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--allow-pending-ci',action='store_true');args=parser.parse_args()
    summary=json.loads((ROOT/'verification/lean-summary.json').read_text(encoding='utf-8'))
    assert summary['complete'] and len(summary['source_sha256'])==638
    for path,digest in summary['source_sha256'].items():
        assert sha(ROOT/path)==digest,f'Checked source changed: {path}'
        assert hashlib.sha256(blob(PIN,path)).hexdigest()==digest,f'Math pin differs: {path}'
    proof_map=json.loads((HERE/'shared/proof_map.json').read_text(encoding='utf-8'))
    assert proof_map['math_commit']==PIN
    ci=proof_map.get('latest_confirmed_proof_ci',{})
    ci_passed=ci.get('commit')==PIN and ci.get('conclusion')=='success'
    if not args.allow_pending_ci:assert ci_passed,'The exact source pin has not yet passed clean proof CI.'
    names=subprocess.check_output(['git','ls-tree','-r','--name-only',BASELINE,'--','manuscripts/2026-10-03','paper/Kobon_triangle_constructions.pdf','paper/journal/Kobon_journal_version.pdf'],cwd=ROOT,text=True).splitlines()
    old={}
    for path in names:
        digest=hashlib.sha256(blob(BASELINE,path)).hexdigest()
        assert sha(ROOT/path)==digest,f'Historical manuscript changed: {path}'
        if path.endswith('.pdf') and '/figures/' not in path:old[path]=digest
    catalog=json.loads((ROOT/'verification/certificate-index.json').read_text())
    assert len(catalog)==138 and sum(bool(x['simple']) for x in catalog)==104
    original_ids={c['id'] for c in json.loads(blob(BASELINE,'manuscripts/2026-10-03/shared/proof_map.json'))['claims']}
    assert original_ids<={c['id'] for c in proof_map['claims']}
    sources={}
    def check_link(url):
        parsed=urlsplit(url);parts=unquote(parsed.path).split('/')
        if parsed.netloc!='github.com' or len(parts)<6 or parts[1:3]!=['alejandrozu','kobon-proof'] or parts[3]!='blob':return
        ref=parts[4];path='/'.join(parts[5:])
        if not re.fullmatch('[0-9a-f]{40}',ref):
            assert (ROOT/path).is_file(),f'Missing tagged artifact: {url}';return
        key=(ref,path)
        if key not in sources:sources[key]=blob(ref,path)
        if parsed.fragment.startswith('L'):
            line=int(parsed.fragment[1:].split('-')[0]);assert 1<=line<=len(sources[key].splitlines()),url
    reports=[]
    for edition,name in OUTPUTS.items():
        folder=HERE/edition;pdf=folder/name;report=audit_pdf(pdf);assert report['passed']
        reader=PdfReader(pdf);assert reader.metadata.author=='Alejandro Zarzuelo Urdiales'
        if edition=='journal':assert len(reader.pages)<=15
        urls=[]
        for page in reader.pages:
            for annotation in page.get('/Annots',[]):
                action=annotation.get_object().get('/A')
                if action and action.get('/URI'):urls.append(str(action['/URI']))
        for url in set(urls):check_link(url)
        lean_urls=[u for u in set(urls) if f'/blob/{PIN}/Kobon/' in u];assert len(lean_urls)>=20
        comp=json.loads((folder/'compilation.json').read_text());assert comp['pdf_sha256']==sha(pdf)
        assert comp['compiler_log_sha256']==sha(folder/'compilation.log')
        for source,digest in comp['source_sha256'].items():assert sha(folder/source)==digest,(edition,source)
        log=(folder/'compilation.log').read_text(encoding='utf-8')
        assert not re.search(r'Overfull \\[hv]box|There were undefined|(?:Reference|Citation) .* undefined|multiply defined|Missing character|^! ',log,re.M)
        review=json.loads((folder/'visual_review.json').read_text());assert review['pdf_sha256']==sha(pdf)
        assert review['passed'] and review['reviewed_pages']==list(range(1,len(reader.pages)+1))
        report.update(edition=edition,clickable_urls=len(set(urls)),immutable_lean_urls=len(lean_urls),visual_review_matches=True)
        reports.append(report)
    for claim in proof_map['claims']:
        for ref in claim.get('refs',[]):
            if 'source_sha256' in ref:
                commit=ref.get('commit',PIN);data=blob(commit,ref['path']);assert hashlib.sha256(data).hexdigest()==ref['source_sha256'],ref['path']
            if 'url' in ref:check_link(ref['url'])
    report=dict(passed=True,publication_ready=ci_passed,date='2026-10-07',math_commit=PIN,verification_commit=VERIFICATION_PIN,
        proof_ci=ci,checked_lean_sources=638,axiom_audit=summary['whole_project_axiom_audit'],
        finite_certificates=138,simple_certificates=104,historical_files_preserved=len(names),historical_pdf_sha256=old,
        proof_claims=len(proof_map['claims']),immutable_link_source_files=len(sources),manuscripts=reports)
    (HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: two PDFs,{len(proof_map["claims"])} claims,638 source hashes, historical editions preserved; publication_ready={ci_passed}.')
if __name__=='__main__':main()
