"""Compile the journal manuscript; enforce the 15-page cap including references."""
from pathlib import Path
import argparse
import re
import shutil
import subprocess
from pypdf import PdfReader

HERE = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", default="tectonic", help="Tectonic executable")
    args = parser.parse_args()
    work = HERE / "build"
    work.mkdir(exist_ok=True)
    run = subprocess.run(
        [args.engine, "--keep-logs", "--keep-intermediates", "--outdir", str(work), "main.tex"],
        cwd=HERE, capture_output=True, text=True, encoding="utf-8", errors="replace")
    (work / "compile-console.log").write_text(run.stdout + run.stderr, encoding="utf-8")
    if run.returncode:
        raise SystemExit("Compilation failed: inspect build/compile-console.log")
    log = (work / "main.log").read_text(encoding="utf-8", errors="replace")
    bad = r"Overfull \\[hv]box|There were undefined|(?:Reference|Citation) .* undefined|multiply defined|Missing character|^! "
    if re.search(bad, log, re.MULTILINE):
        raise SystemExit("Unresolved TeX warning: inspect build/main.log")
    reader = PdfReader(work / "main.pdf")
    if not 1 <= len(reader.pages) <= 15:
        raise SystemExit(f"Page limit exceeded: {len(reader.pages)} pages, including references.")
    if reader.metadata.author != "Alejandro Zarzuelo Urdiales":
        raise SystemExit("Unexpected PDF author metadata")
    destination = HERE / "Kobon_journal_version.pdf"
    shutil.copy2(work / "main.pdf", destination)
    print(f"PASS: {len(reader.pages)} pages including references; no unresolved references or overflowing boxes.")

if __name__ == "__main__":
    main()
