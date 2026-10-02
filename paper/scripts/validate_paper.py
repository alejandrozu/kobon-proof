"""Audit manuscript references, data provenance, and the frozen proof snapshot."""
from pathlib import Path
import csv
import hashlib
import json
import re
import subprocess
from pypdf import PdfReader
from pdf_preflight import audit_pdf

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
HISTORICAL_PAPER_COMMIT = '22d1165f6c455fe45e461baef4410f6d5c78a014'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_paper_files():
    """Hash the current long-paper package, independently of the journal."""
    files = {}
    for path in sorted(PAPER.rglob('*')):
        relative = path.relative_to(PAPER)
        if (not path.is_file() or relative.parts[0] == 'journal'
                or set(relative.parts) & {'build', '__pycache__'}
                or path.name == 'validation.json'):
            continue
        files[relative.as_posix()] = sha(path)
    return files


def historical_snapshot():
    """Verify the original 71 files in Git, without comparing working files."""
    manifest_bytes = subprocess.run(
        ['git', 'show', f'{HISTORICAL_PAPER_COMMIT}:paper/validation.json'],
        cwd=ROOT, capture_output=True, check=True).stdout
    manifest = json.loads(manifest_bytes.decode('utf-8-sig'))
    expected = manifest['paper_file_sha256']
    assert len(expected) == 71, 'Unexpected original long-paper manifest'
    names = sorted(expected)
    batch = subprocess.run(
        ['git', 'cat-file', '--batch'],
        input=''.join(f'{HISTORICAL_PAPER_COMMIT}:paper/{name}\n'
                      for name in names).encode('utf-8'),
        cwd=ROOT, capture_output=True, check=True).stdout
    offset = 0
    for name in names:
        end = batch.index(b'\n', offset)
        header = batch[offset:end].split()
        assert len(header) == 3 and header[1] == b'blob', name
        size = int(header[2])
        blob = batch[end+1:end+1+size]
        assert len(blob) == size and batch[end+1+size:end+2+size] == b'\n', name
        assert hashlib.sha256(blob).hexdigest() == expected[name], name
        offset = end+2+size
    assert offset == len(batch), 'Unexpected historical Git batch output'
    return {
        'commit': HISTORICAL_PAPER_COMMIT,
        'files_verified': len(names),
        'pdf_sha256': expected['Kobon_triangle_constructions.pdf'],
        'validation_sha256': hashlib.sha256(manifest_bytes).hexdigest(),
        'verification': 'Original manifest and all 71 file blobs verified at the historical Git revision.'
    }


def main():
    sources = [PAPER / 'main.tex', *sorted((PAPER / 'sections').glob('*.tex')),
               *sorted((PAPER / 'generated').glob('*.tex'))]
    text = '\n'.join(p.read_text(encoding='utf-8') for p in sources)
    assert not [(ord(c), i) for i, c in enumerate(text) if ord(c) < 32 and c not in '\n\r\t']
    assert not any(re.search(r'\s', name) for name in re.findall(r'\\lean\{([^}]+)\}', text)), \
        'Use texttt, not the URL-style lean macro, for expressions containing spaces'
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
    pdf_text = '\n'.join(page.extract_text() for page in reader.pages)
    proof_endings = text.count(r'\end{proof}')
    assert pdf_text.count('Q.E.D.') == proof_endings, 'A proof-end mark is missing or ambiguous'
    assert 'Universal.bound = max Universal.baseline AllN.bound' in pdf_text, \
        'Lean bound expression lost its spaces'
    toc = (PAPER / 'build/main.toc').read_text(encoding='utf-8')
    toc_entries = re.findall(r'\}\{(\d+)\}\{([^}]+)\}%', toc)
    for page_number, destination in toc_entries:
        assert destination in reader.named_destinations, destination
        assert reader.get_destination_page_number(reader.named_destinations[destination]) + 1 == int(page_number), \
            f'Table of contents points to the wrong page: {destination}'
    assert len(reader.pages) > 0
    preflight = audit_pdf(pdf)
    visual = json.loads((PAPER / 'visual_review.json').read_text(encoding='utf-8'))
    assert visual.get('pdf_sha256') == sha(pdf), 'Current long PDF requires a matching visual review'
    assert visual.get('pages') == len(reader.pages), 'Visual review page count differs from current long PDF'
    log_path = PAPER / 'build/main.log'
    assert log_path.is_file(), 'Build the current long PDF before validating it'
    log = log_path.read_text(encoding='utf-8', errors='replace')
    assert not re.search(
        r'Overfull \\[hv]box|There were undefined|(?:Reference|Citation) .* undefined|'
        r'multiply defined|Missing character|^! ', log, re.MULTILINE)
    files = current_paper_files()
    history = historical_snapshot()
    report = dict(
        all_passed=True, author=reader.metadata.author, pdf_pages=len(reader.pages),
        bibliography_entries=len(keys), vector_figures=len(figures), finite_orders=len(rows),
        distinct_coordinate_identities=len(catalog), simple_coordinate_identities=sum(r['simple'] for r in catalog),
        frozen_math_commit='99fdc8ec1ef8b1fb22c3da32b011b7361762e958',
        unchanged_verified_lean_sources=len(proof['source_sha256']),
        previously_passed_build_targets=len(proof['results']),
        resolved_labels=len(labels), cited_keys=sorted(cites),
        explicit_proof_endings=proof_endings, checked_contents_destinations=len(toc_entries),
        figure_input_sha256=checked_inputs, paper_file_sha256=files,
        current_pdf_sha256=sha(pdf), historical_paper=history,
        pdf_preflight=preflight, visual_review_matches_pdf=True,
        scope='Consistency audit, not a new proof replay. Full Lean verification belongs to the frozen snapshot.',
        visual_review='Recorded visual review matches the current corrected PDF.')
    (PAPER / 'validation.json').write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
    print(f'PASS: {len(reader.pages)} pages, {len(keys)} references, {len(figures)} vector figures, '
          f'{len(catalog)} coordinate identities, {len(proof["source_sha256"])} unchanged verified Lean sources.')


if __name__ == '__main__':
    main()
