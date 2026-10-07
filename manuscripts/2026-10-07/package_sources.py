"""Create a deterministic portable LaTeX archive for both manuscript editions."""
from pathlib import Path
import zipfile
HERE=Path(__file__).resolve().parent
files=[HERE/'README.md',HERE/'build.py',HERE/'render.py',HERE/'package_sources.py',
       HERE/'make_figures.py',HERE/'make_october_figures.py']
for edition in ('long','journal'):
    folder=HERE/edition
    files.extend(p for p in folder.rglob('*') if p.is_file()
        and 'build' not in p.relative_to(folder).parts
        and (p.suffix in ('.tex','.bib') or p.suffix=='.pdf' and p.parent.name=='figures'))
files.extend(p for p in (HERE/'shared').iterdir() if p.is_file() and p.suffix in {'.md','.json','.py'})
files.append(HERE/'new-figure-manifest.json')
files.append(HERE/'october-figure-manifest.json')
destination=HERE/'Kobon_manuscripts_2026-10-07_sources.zip'
with zipfile.ZipFile(destination,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
    for path in sorted(set(files)):
        info=zipfile.ZipInfo(path.relative_to(HERE).as_posix(),date_time=(2026,10,7,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=0o644<<16
        archive.writestr(info,path.read_bytes())
with zipfile.ZipFile(destination) as archive:
    assert archive.testzip() is None
    for info in archive.infolist():
        assert archive.read(info)==(HERE/info.filename).read_bytes()
print(f'PASS: {len(set(files))} portable source assets, {destination.stat().st_size} bytes')
