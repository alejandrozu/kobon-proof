"""Create a deterministic portable LaTeX archive for both manuscript editions."""
from pathlib import Path
import zipfile
HERE=Path(__file__).resolve().parent
files=[HERE/'README.md',HERE/'build.py']
for edition in ('long','journal'):
    folder=HERE/edition
    files.extend(p for p in folder.rglob('*') if p.is_file()
        and 'build' not in p.relative_to(folder).parts
        and (p.suffix in ('.tex','.bib') or p.suffix=='.pdf' and p.parent.name=='figures'))
files.extend(HERE/'shared'/n for n in ('proof_map.md','proof_map.json',
    'coverage_map.md','literature_scope_audit.md'))
files.append(HERE/'new-figure-manifest.json')
destination=HERE/'Kobon_manuscripts_2026-10-03_sources.zip'
with zipfile.ZipFile(destination,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
    for path in sorted(set(files)):
        info=zipfile.ZipInfo(path.relative_to(HERE).as_posix(),date_time=(2026,10,3,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=0o644<<16
        archive.writestr(info,path.read_bytes())
with zipfile.ZipFile(destination) as archive:
    assert archive.testzip() is None
    for info in archive.infolist():
        assert archive.read(info)==(HERE/info.filename).read_bytes()
print(f'PASS: {len(set(files))} portable source assets, {destination.stat().st_size} bytes')
