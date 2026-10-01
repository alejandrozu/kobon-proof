"""Check the journal manuscript against its unchanged mathematical source release."""
from pathlib import Path
import hashlib
import json
import re
from pypdf import PdfReader

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
ROOT = PAPER.parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    tex = [HERE / "main.tex", *sorted((HERE / "sections").glob("*.tex"))]
    text = "\n".join(p.read_text(encoding="utf-8") for p in tex)
    assert all(ord(c) >= 32 or c in "\n\r\t" for c in text), "Unexpected control character"
    assert not re.search(r"(?<![\\A-Za-z])(?:qquad|quad)\b", text), "Unescaped spacing command"
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    refs = re.findall(r"\\(?:eqref|ref|cref|Cref)\{([^}]+)\}", text)
    assert len(labels) == len(set(labels))
    assert set(refs) <= set(labels), set(refs) - set(labels)
    keys = set(re.findall(r"@\w+\{([^,]+),", (HERE / "references.bib").read_text(encoding="utf-8")))
    citations = {k.strip() for c in re.findall(r"\\cite[pt]?\{([^}]+)\}", text) for k in c.split(",")}
    assert keys == citations, keys ^ citations
    figures = re.findall(r"\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}", text)
    assert len(figures) == len(set(figures)) == 4
    for name in figures:
        local = HERE / "figures" / name
        original = PAPER / "figures" / name
        assert sha(local) == sha(original), name
        figure = PdfReader(local)
        assert len(figure.pages) == 1 and not any(page.images for page in figure.pages)
    old = json.loads((PAPER / "validation.json").read_text(encoding="utf-8"))
    for name, expected in old["paper_file_sha256"].items():
        assert sha(PAPER / name) == expected, f"Original long-paper file changed: {name}"
    proof = json.loads((ROOT / "verification/lean-summary.json").read_text(encoding="utf-8"))
    assert proof["complete"] and all(r["passed"] for r in proof["results"])
    for name, expected in proof["source_sha256"].items():
        assert sha(ROOT / name) == expected, name
    pdf = HERE / "Kobon_journal_version.pdf"
    reader = PdfReader(pdf)
    assert 1 <= len(reader.pages) <= 15
    assert reader.metadata.author == "Alejandro Zarzuelo Urdiales"
    log = (HERE / "build/main.log").read_text(encoding="utf-8", errors="replace")
    assert not re.search(r"Overfull \\[hv]box|There were undefined|multiply defined|Missing character|^! ", log, re.MULTILINE)
    review_file = HERE / "visual_review.json"
    review = json.loads(review_file.read_text(encoding="utf-8")) if review_file.exists() else {}
    report = {
        "all_consistency_checks_passed": True,
        "author": reader.metadata.author,
        "pages_including_references": len(reader.pages),
        "page_limit": 15,
        "cited_references": len(keys),
        "vector_figures": len(figures),
        "labels": len(labels),
        "long_paper_files_preserved": len(old["paper_file_sha256"]),
        "long_paper_pdf_sha256": sha(PAPER / "Kobon_triangle_constructions.pdf"),
        "unchanged_verified_lean_sources": len(proof["source_sha256"]),
        "frozen_math_commit": "99fdc8ec1ef8b1fb22c3da32b011b7361762e958",
        "long_paper_commit": "22d1165f6c455fe45e461baef4410f6d5c78a014",
        "long_paper_ci": {"run": 35779849718, "conclusion": "success"},
        "journal_pdf_sha256": sha(pdf),
        "visual_review_matches_pdf": review.get("pdf_sha256") == sha(pdf),
        "scope": "Editorial and provenance checks. No new Lean theorem or numerical priority claim.",
        "files": {p.relative_to(HERE).as_posix(): sha(p)
                  for p in sorted(HERE.rglob("*")) if p.is_file()
                  and not set(p.relative_to(HERE).parts) & {"build", "__pycache__"}
                  and p.name != "validation.json"}
    }
    (HERE / "validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(reader.pages)} pages, {len(keys)} references, four vector figures; "
          f"all {len(old['paper_file_sha256'])} original paper files and 325 Lean sources unchanged.")

if __name__ == "__main__":
    main()
