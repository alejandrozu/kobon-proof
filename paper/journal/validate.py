"""Check the journal manuscript against its unchanged mathematical source release."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
from pypdf import PdfReader

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
ROOT = PAPER.parent
sys.path.insert(0, str(PAPER / 'scripts'))
from pdf_preflight import audit_pdf
from validate_paper import current_paper_files, historical_snapshot, frozen_math_snapshot

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    tex = [HERE / "main.tex", *sorted((HERE / "sections").glob("*.tex"))]
    text = "\n".join(p.read_text(encoding="utf-8") for p in tex)
    assert all(ord(c) >= 32 or c in "\n\r\t" for c in text), "Unexpected control character"
    assert not any(re.search(r"\s", name) for name in re.findall(r"\\lean\{([^}]+)\}", text)), \
        "Use texttt, not the URL-style lean macro, for expressions containing spaces"
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
    current = json.loads((PAPER / "validation.json").read_text(encoding="utf-8"))
    assert current["all_passed"], "Validate the corrected long paper first"
    assert current_paper_files() == current["paper_file_sha256"], "Current long-paper manifest is stale"
    current_long_pdf = PAPER / "Kobon_triangle_constructions.pdf"
    current_long_sha = sha(current_long_pdf)
    assert current["current_pdf_sha256"] == current_long_sha, "Current long-paper PDF differs from its validation"
    current_long_review = json.loads((PAPER / "visual_review.json").read_text(encoding="utf-8"))
    assert current_long_review.get("pdf_sha256") == current_long_sha, "Current long-paper visual review is stale"
    history = historical_snapshot()
    assert current["historical_paper"] == history, "Historical long-paper verification differs"
    proof = frozen_math_snapshot()
    pdf = HERE / "Kobon_journal_version.pdf"
    reader = PdfReader(pdf)
    assert 1 <= len(reader.pages) <= 15
    assert reader.metadata.author == "Alejandro Zarzuelo Urdiales"
    pdf_text = "\n".join(page.extract_text() for page in reader.pages)
    proof_endings = text.count(r"\end{proof}")
    assert pdf_text.count("Q.E.D.") == proof_endings, "A proof-end mark is missing or ambiguous"
    for identifier in re.findall(r"\\lean\{([^}]+)\}", text):
        assert identifier in pdf_text, f"Lean identifier split or lost characters: {identifier}"
    preflight = audit_pdf(pdf)
    mapping = json.loads((HERE / "proof_map.json").read_text(encoding="utf-8"))
    commit = mapping["math_commit"]
    base = f"https://github.com/alejandrozu/kobon-proof/blob/{commit}/"
    claims = mapping["claims"]
    ids = {claim["id"] for claim in claims}
    assert len(ids) == len(claims), "Duplicate proof-map claim"
    numbered = re.findall(
        r"\\begin\{(?:theorem|lemma|proposition|corollary)\}(?:\[[^]]*\])?\s*\\label\{([^}]+)\}", text)
    equations = re.findall(
        r"\\begin\{(?:equation|align)\}(.*?)\\end\{(?:equation|align)\}", text, re.DOTALL)
    numbered += [lab for eq in equations for lab in re.findall(r"\\label\{([^}]+)\}", eq)]
    assert set(numbered) <= ids, f"Unmapped numbered results: {set(numbered) - ids}"
    catalog = mapping["finite_catalog"]
    original_catalog = json.loads((ROOT / "verification/certificate-index.json").read_text(encoding="utf-8"))
    assert len(catalog) == len(original_catalog) == 138
    assert sum(c["simple"] for c in catalog) == 104
    identity = lambda c: (c["n"], c["triangles"], c["simple"], c["coordinate_sha256"])
    assert sorted(map(identity, catalog)) == sorted(map(identity, original_catalog))
    markdown = (HERE / "proof_map.md").read_text(encoding="utf-8")
    proofrefs = [r for claim in claims + catalog for r in claim["refs"]]
    for r in proofrefs:
        source = ROOT / r["path"]
        assert sha(source) == r["source_sha256"], r
        lines = source.read_text(encoding="utf-8-sig").splitlines()
        assert 1 <= r["line"] <= len(lines), r
        if r.get("declaration"):
            leaf = r["declaration"].rsplit(".", 1)[-1]
            assert re.search(r"\b(?:theorem|lemma|def|abbrev|structure)\s+" + re.escape(leaf)
                             + r"(?:\s|[(:]|$)", lines[r["line"]-1]), r
        assert r["url"] == base + r["path"] + f'#L{r["line"]}', r
        assert r["url"] in markdown, r
    # Check the pinned revision's actual blob bytes, not merely stored metadata.
    sources = sorted({r["path"] for r in proofrefs})
    batch = subprocess.run(["git", "cat-file", "--batch"],
        input="".join(f"{commit}:{p}\n" for p in sources).encode(),
        cwd=ROOT, capture_output=True, check=True).stdout
    offset = 0
    for path in sources:
        end = batch.index(b"\n", offset)
        header = batch[offset:end].split()
        assert len(header) == 3 and header[1] == b"blob", path
        size = int(header[2])
        blob = batch[end+1:end+1+size]
        assert blob == (ROOT / path).read_bytes(), f"Pinned link differs from source: {path}"
        offset = end+1+size+1
    pdf_urls = set()
    for page in reader.pages:
        for annot in page.get("/Annots", []):
            action = annot.get_object().get("/A")
            if action and action.get("/URI"):
                pdf_urls.add(str(action["/URI"]))
    expected_pdf_urls = set()
    for path, line in re.findall(r"\\proofref\{([^}]+)\}\{(\d+)\}", text):
        assert (ROOT / path).is_file()
        assert 1 <= int(line) <= len((ROOT / path).read_text(encoding="utf-8-sig").splitlines())
        expected_pdf_urls.add(base + path + "#L" + line)
    assert expected_pdf_urls <= pdf_urls, expected_pdf_urls - pdf_urls
    assert "https://github.com/alejandrozu/kobon-proof/blob/main/paper/journal/proof_map.md" in pdf_urls
    log_path = HERE / "build/main.log"
    assert log_path.is_file(), "Build the current journal PDF before validating it"
    log = log_path.read_text(encoding="utf-8", errors="replace")
    assert not re.search(r"Overfull \\[hv]box|There were undefined|multiply defined|Missing character|^! ", log, re.MULTILINE)
    review_file = HERE / "visual_review.json"
    review = json.loads(review_file.read_text(encoding="utf-8"))
    assert review.get("pdf_sha256") == sha(pdf), "Current journal PDF requires a matching visual review"
    assert review.get("pages") == len(reader.pages), "Visual review page count differs from current journal PDF"
    report = {
        "all_consistency_checks_passed": True,
        "author": reader.metadata.author,
        "pages_including_references": len(reader.pages),
        "page_limit": 15,
        "cited_references": len(keys),
        "vector_figures": len(figures),
        "explicit_proof_endings": proof_endings,
        "labels": len(labels),
        "current_long_paper_files_checked": len(current["paper_file_sha256"]),
        "current_long_paper_pdf_sha256": current_long_sha,
        "current_long_paper_pdf_pages": current["pdf_pages"],
        "current_long_paper_validation_sha256": sha(PAPER / "validation.json"),
        "current_long_paper_visual_review_matches_pdf": True,
        "historical_long_paper": history,
        "verified_frozen_lean_sources": len(proof["source_sha256"]),
        "frozen_math_commit": "99fdc8ec1ef8b1fb22c3da32b011b7361762e958",
        "historical_long_paper_ci": {"run": 35779849718, "conclusion": "success"},
        "verified_mathematical_sources_ci": mapping["latest_confirmed_proof_ci"],
        "proof_map_claims": len(claims),
        "mapped_numbered_results": len(set(numbered)),
        "linked_finite_certificates": len(catalog),
        "pinned_source_files_checked": len(sources),
        "clickable_pinned_pdf_source_links": len(expected_pdf_urls),
        "journal_pdf_sha256": sha(pdf),
        "pdf_preflight": preflight,
        "visual_review_matches_pdf": True,
        "scope": "Editorial and provenance checks. No new Lean theorem or numerical priority claim.",
        "files": {p.relative_to(HERE).as_posix(): sha(p)
                  for p in sorted(HERE.rglob("*")) if p.is_file()
                  and not set(p.relative_to(HERE).parts) & {"build", "__pycache__"}
                  and p.name != "validation.json"}
    }
    (HERE / "validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(reader.pages)} pages, {len(keys)} references, four vector figures; "
          f"{len(current['paper_file_sha256'])} current long-paper files checked, "
          f"{history['files_verified']} original Git blobs preserved, and "
          f"{len(proof['source_sha256'])} frozen Lean sources verified.")

if __name__ == "__main__":
    main()
