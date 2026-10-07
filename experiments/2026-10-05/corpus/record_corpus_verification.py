"""Record final source hashes and proof/log boundaries for the corpus branch."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/"research/openmath-seven-hour-2026-10-05/corpus"


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


if __name__=="__main__":
    builds=[]
    for source,log in [
        ("Kobon/BBLTangent60Bounds.lean","tangent60/build.log"),
        ("Kobon/BBLRationalTangentBounds.lean","tangent60/generic-build.log"),
        ("Kobon/OpenMathConstructionBooleanMemo.lean","tangent60/memo-build.log")]:
        p=ROOT/source;l=OUT/log;text=l.read_text(encoding="utf8")
        assert "error:" not in text and "sorryAx" not in text and "Lean.ofReduceBool" not in text
        assert "depends on axioms:" in text
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b",p.read_text(encoding="utf8"))
        builds.append(dict(source=source,source_sha256=sha(p),log=str(l.relative_to(ROOT)),log_sha256=sha(l),
            completed=True,trust="standard logical axioms only; selected endpoint prints in log",
            declarations=len(re.findall(r"^theorem ",p.read_text(encoding="utf8"),re.M))))
    files=["source-inventory.json","shared-rule8.json","fp-shared-rule.json","fp-boundary-profiles.json", "shared-segment-counterexamples.json","perfect-seed-deletions.json","seed61-variant-visibility.json","uniform-seed19/uniform-seed.json"]
    output=dict(recorded_at=datetime.now(timezone.utc).isoformat(),lean_builds=builds,
        external_exact_results=[dict(path=str((OUT/f).relative_to(ROOT)),sha256=sha(OUT/f)) for f in files],
        proof_boundaries=["The8-line counterexample has independent exact quadratic-field and chirotope checks, but no direct Lean shared-edge-count theorem here.",
        "All-n FP triangle/shared-edge formulas remain observed/explained; the ordered triple-count formula has a hand counting derivation.",
        "The19 seed is an external exact uniform interval certificate, not a compiled Lean seed or a numerical novelty claim.",
        "The61 seed/family Lean proof is owned by the construction branch and must be assessed from its own final build results.",
        "No unrestricted improved upper bound or complete Kobon solution is claimed by this corpus audit."])
    (OUT/"VERIFICATION.json").write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(dict(verified_modules=len(builds),theorem_declarations=sum(b["declarations"] for b in builds),external_result_files=len(files))))
