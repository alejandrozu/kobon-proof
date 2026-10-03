"""Build either portable manuscript; reject TeX errors and enforce <=15 journal pages."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pypdf import PdfReader

HERE=Path(__file__).resolve().parent
OUTPUTS={'long':'Kobon_comprehensive_2026-10-03.pdf',
         'journal':'Kobon_journal_2026-10-03.pdf'}

def build(edition,engine):
    folder=HERE/edition
    work=folder/'build'
    work.mkdir(exist_ok=True)
    run=subprocess.run([engine,'--keep-logs','--keep-intermediates',
        '--outdir',str(work),'main.tex'],cwd=folder,capture_output=True,
        text=True,encoding='utf-8',errors='replace')
    (work/'compile-console.log').write_text(run.stdout+run.stderr,encoding='utf-8')
    if run.returncode: raise RuntimeError(f'{edition}: compilation failed; see build/compile-console.log')
    log=(work/'main.log').read_text(encoding='utf-8',errors='replace')
    bad=r'Overfull \\[hv]box|There were undefined|(?:Reference|Citation) .* undefined|multiply defined|Missing character|^! '
    problems=re.findall(bad,log,re.MULTILINE)
    reader=PdfReader(work/'main.pdf')
    pages=len(reader.pages)
    if edition=='journal' and pages>15: problems.append(f'{pages} pages exceeds the 15-page limit')
    if reader.metadata.author!='Alejandro Zarzuelo Urdiales': problems.append('Incorrect author metadata')
    if problems: raise RuntimeError(f'{edition}: {problems}; see build/main.log')
    shutil.copy2(work/'main.pdf',folder/OUTPUTS[edition])
    report={'edition':edition,'pages':pages,'author':reader.metadata.author,
        'resolved_references':True,'overflowing_boxes':0,'missing_character_warnings':0,
        'pdf_sha256':hashlib.sha256((folder/OUTPUTS[edition]).read_bytes()).hexdigest(),
        'compiler_log_sha256':hashlib.sha256((work/'main.log').read_bytes()).hexdigest(),
        'source_sha256':{p.relative_to(folder).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(folder.rglob('*')) if p.is_file() and 'build' not in p.relative_to(folder).parts
            and p.suffix in ('.tex','.bib','.pdf') and p.name!=OUTPUTS[edition]}}
    (work/'build-report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    (folder/'compilation.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    shutil.copy2(work/'main.log',folder/'compilation.log')
    print(f'PASS: {edition}, {pages} pages, {OUTPUTS[edition]}',flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edition',choices=['long','journal','both'],default='both')
    parser.add_argument('--engine',default='tectonic')
    args=parser.parse_args()
    for edition in OUTPUTS if args.edition=='both' else [args.edition]: build(edition,args.engine)
