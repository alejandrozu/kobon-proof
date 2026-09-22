"""Audit manuscript references, data provenance, and the frozen proof snapshot."""
from pathlib import Path
import csv
import hashlib
import json
import re
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    sources = [PAPER / 'main.tex', *sorted((PAPER / 'sections').glob('*.tex')),
               *sorted((PAPER / 'generated').glob('*.tex'))]
    text = '\n'.join(p.read_text(encoding='utf-8') for p in sources)
    assert not [(ord(c), i) for i, c in enumerate(text) if ord(c) < 32 and c not in '\n\r\t']
    labels = re.findall(r'\\label\{([^}]+)\}', text)
    refs = re.findall(r'\\(?:eqref|ref|cref|Cref)\{([^}]+)\}', text)
    assert len(labels) == len(set(labels)), 'Duplicate labels'
    assert set(refs) <= set(labels), f'Undefined labels: {set(refs)-set(labels)}'
    bib = (PAPER / 'references.bib').read_text(encoding='utf-8')
    keys = re.findall(r'@\w+\{([^,]+),', bib)
    cites = {k.strip() for c in re.findall(r'\\cite[pt]?\{([^}]+)\}', text) for k in c.split(',')}
    assert cites == set(keys), f'Unresolved or unused bibliography entries: {cites ^ set(keys)}'
    figures = re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}', text)
    assert len(figures) == len(set(figures)) == 16
    for name in figures:
        path = PAPER / name
        if not path.exists():
            path = PAPER / 'figures' / name
        assert path.exists(), name
        reader = PdfReader(path)
        assert len(reader.pages) == 1
        assert sum(len(page.images) for page in reader.pages) == 0, f'Nonvector figure: {name}'
    figure_manifest = json.loads((PAPER / 'generated/figure-manifest.json').read_text(encoding='utf-8'))
    checked_inputs = {}
    for figure in figure_manifest['figures']:
        for source in figure['sources']:
            assert sha(ROOT / source['path']) == source['sha256'], source['path']
            checked_inputs[source['path']] = source['sha256']
    proof = json.loads((ROOT / 'verification/lean-summary.json').read_text(encoding='utf-8'))
    assert proof['complete'] and all(r['passed'] for r in proof['results'])
    for path, expected in proof['source_sha256'].items():
        assert sha(ROOT / path) == expected, f'Lean source changed after verification: {path}'
    catalog = json.loads((PAPER / 'generated/certificate-catalog.json').read_text(encoding='utf-8'))
    assert len(catalog) == len({r['coordinate_sha256'] for r in catalog}) == 138
    for row in catalog:
        for path, expected in row['source_file_sha256'].items():
            assert sha(ROOT / path) == expected, path
    with (PAPER / 'generated/finite-best-3-60.csv').open(encoding='utf-8', newline='') as f:
        rows = list(csv.DictReader(f))
    assert [int(r['n']) for r in rows] == list(range(3, 61))
    for row in rows:
        n = int(row['n'])
        g = 1 if n == 3 else n * (n-3)//3 + 1+n%2
        candidates = [r for r in catalog if r['n'] == n]
        assert int(row['G']) == g
        assert int(row['saved_classical']) == max(r['triangles'] for r in candidates)
        assert int(row['saved_simple']) == max(r['triangles'] for r in candidates if r['simple'])
    pdf = PAPER / 'Kobon_triangle_constructions.pdf'
    reader = PdfReader(pdf)
    assert reader.metadata.author == 'Alejandro Zarzuelo Urdiales'
    assert len(reader.pages) == 60
    visual = json.loads((PAPER / 'visual_review.json').read_text(encoding='utf-8'))
    visual_status = ('Recorded visual review matches this PDF.' if visual['pdf_sha256'] == sha(pdf)
                     else 'PDF changed since the recorded visual review; inspect it again before release.')
    log_path = PAPER / 'build/main.log'
    if log_path.exists():
        log = log_path.read_text(encoding='utf-8', errors='replace')
        assert not re.search(r'Overfull \\[hv]box|There were undefined|multiply defined|^! ', log, re.MULTILINE)
    files = {p.relative_to(PAPER).as_posix(): sha(p) for p in sorted(PAPER.rglob('*'))
             if p.is_file() and 'build' not in p.relative_to(PAPER).parts
             and '__pycache__' not in p.parts and p.name != 'validation.json'}
    report = dict(
        all_passed=True, author=reader.metadata.author, pdf_pages=len(reader.pages),
        bibliography_entries=len(keys), vector_figures=len(figures), finite_orders=len(rows),
        distinct_coordinate_identities=len(catalog), simple_coordinate_identities=sum(r['simple'] for r in catalog),
        frozen_math_commit='99fdc8ec1ef8b1fb22c3da32b011b7361762e958',
        unchanged_verified_lean_sources=len(proof['source_sha256']),
        previously_passed_build_targets=len(proof['results']),
        resolved_labels=len(labels), cited_keys=sorted(cites),
        figure_input_sha256=checked_inputs, paper_file_sha256=files,
        scope='Consistency audit, not a new proof replay. Full Lean verification belongs to the frozen snapshot.',
        visual_review=visual_status)
    (PAPER / 'validation.json').write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
    print(f'PASS: {len(reader.pages)} pages, {len(keys)} references, {len(figures)} vector figures, '
          f'{len(catalog)} coordinate identities, {len(proof["source_sha256"])} unchanged verified Lean sources.')


if __name__ == '__main__':
    main()
