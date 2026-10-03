"""Read-only validation of the shared October proof map and manuscript labels."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from build_proof_map import HERE, ROOT, PIN, declaration_line, pinned_blobs

# A long-paper equation may define the inputs to a mapped theorem; an alias
# does not claim that a separate Lean declaration has that exact equation name.
LONG_ALIASES = {
    "j:G": "eq:G lit:our-formula",
    "j:envelope": "eq:envelope prop:envelope",
    "j:gap": "eq:gap",
    "j:phase": "eq:shifted-triples lem:shifted-count",
    "j:residues": "eq:halfphase-triples lem:trig-triangles eq:classical-count lit:baseline lit:residue-comparison",
    "j:sign": "eq:trig-det eq:trig-eval eq:trig-oriented",
    "j:trig": "eq:trig-line",
    "j:covariance": "eq:projective-map eq:line-transform lem:projective-covariance eq:projective-sign",
    "j:caps": "lem:one-cap eq:vertex-x lem:two-caps",
    "j:cell": "thm:certificate-cell",
    "j:certificate-soundness": "prop:finite-sound",
    "long:certificate-definitions": "eq:det eq:oriented-affine def:certificate",
    "lit:classical-upper": "lit:tamura",
    "j:blanc": "lit:blanc-even",
    "j:main": "thm:main cor:gain",
    "j:finite": "eq:march-three",
    "j:44equality": "eq:44-simple",
    "jext:visible": "ext:visible ext:realization",
    "jext:gain": "ext:g",
    "jext:odd-near-perfect": "ext:odd-full",
    "jext:budget": "ext:budget",
    "jext:conditional-iteration": "ext:march ext:full-step ext:conditional-closed ext:49-target",
    "jext:49": "ext:49-unconditional",
    "jfam:doubling": "fam:epsilon fam:old-grid fam:compatible fam:doubling fam:gain fam:pencil fam:crossing fam:displacement fam:neighbors fam:mixed-count fam:deficit-preserved",
    "jfam:seed11": "fam:seed11-slopes fam:seed11-grid",
    "jfam:recursive": "fam:closed-iteration fam:closed-count fam:recursive-quantifier",
    "jfam:families": "fam:odd-verified fam:eleven-family",
    "jfam:strong-even": "fam:visible-iteration fam:visible-step fam:even-conditional fam:even-strong",
    "jext:defect": "ext:defect ext:charging ext:profile ext:average ext:defect-theorem ext:defect-scope fam:even-defect",
    "j:new-envelope-formula": "fam:sparse-bound fam:new-envelope",
    "j:new-envelope": "fam:all-n-envelope",
    "long:envelope-gains": "fam:exact-gains",
    "jfam:windows": "fam:optimality-windows fam:windows",
    "jfam:inherited-families": "fam:tamura fam:pu lit:pu-gap",
    "oct:grid21-coverage": "fam:21-target exp:census-interval",
    "j:exact49": "fam:49-conditional",
    "jup:identity": "upper:identity upper:defect-general upper:shared-endpoint upper:core-identity upper:actual-identity",
    "jup:clean": "upper:clean-charge upper:charging upper:actual-charging",
    "jup:budget": "upper:basic-budget",
    "jup:fan": "upper:no-long-run upper:fan-budget upper:local-fan-budget",
    "jup:weighted": "upper:weighted upper:weighted-defect",
    "jup:high-multiplicity": "upper:high-multiplicity",
    "jup:fan-sharp": "upper:one-core-ray",
    "jup:two-core": "upper:two-core upper:two-core-upper",
    "jup:attainment": "upper:restricted-attainment",
    "jup:shared-fan": "upper:shared-fan upper:median-lines",
    "jup:simple": "upper:actual-simple upper:actual-simple-bounds",
    "jup:sharp-fan": "upper:extremal-structure upper:extremal-weight",
    "oct:core-budget": "upper:core-inputs upper:refined-conditional upper:three-core-conditional",
    "j:obstruction": "exp:farkas exp:linear-determinant exp:quartic exp:actual-grid-obstruction exp:ten-signs",
    "oct:next-proof-plan": "discussion:conditional-graph discussion:conditional-defect",
}
NUMBERED = {"equation", "align", "gather", "multline", "theorem", "lemma", "proposition",
            "corollary", "definition", "remark", "conjecture"}


def numbered_labels(folder):
    answer = []
    for source in sorted(folder.glob("sections/*.tex")):
        content = source.read_text(encoding="utf-8-sig")
        # Comments cannot introduce genuine environment boundaries.
        content = re.sub(r"(?<!\\)%[^\n]*", "", content)
        stack = []
        events = re.compile(r"\\(begin|end|label)\{([^}]+)\}")
        for event in events.finditer(content):
            kind, value = event.groups()
            if kind == "begin":
                stack.append(value)
            elif kind == "end":
                if stack and stack[-1] == value:
                    stack.pop()
            elif any(env in NUMBERED for env in stack):
                answer.append(dict(label=value, path=source.relative_to(ROOT).as_posix(),
                                   environment=next(env for env in reversed(stack) if env in NUMBERED)))
    return answer


def validate(write_report=False):
    data = json.loads((HERE/"proof_map.json").read_text(encoding="utf-8"))
    claims = {claim["id"]: claim for claim in data["claims"]}
    assert len(claims) == len(data["claims"]), "Duplicate claim IDs"
    old = json.loads((ROOT/"paper/journal/proof_map.json").read_text(encoding="utf-8"))
    assert {c["id"] for c in old["claims"]} <= set(claims)
    assert len(old["claims"]) == data["previous_claims_retained"] == 89
    old_catalog = {(r["n"], r["triangles"], r["coordinate_sha256"]) for r in old["finite_catalog"]}
    new_catalog = {(r["n"], r["triangles"], r["coordinate_sha256"]) for r in data["finite_catalog"]}
    assert old_catalog == new_catalog and len(new_catalog) == 138
    assert sum(row["simple"] for row in data["finite_catalog"]) == 104
    assert data["math_commit"] == PIN
    refs = [ref for claim in data["claims"] for ref in claim["refs"]]
    refs += [ref for row in data["finite_catalog"] for ref in row["refs"]]
    paths = sorted({ref["path"] for ref in refs})
    blobs = pinned_blobs(paths)
    for ref in refs:
        digest = hashlib.sha256(blobs[ref["path"]]).hexdigest()
        assert ref["source_sha256"] == digest, ref
        assert ref["git_blob_sha256"] == digest, ref
        assert ref["url"] == f"https://github.com/alejandrozu/kobon-proof/blob/{PIN}/{ref['path']}#L{ref['line']}", ref
        local = (ROOT/ref["path"]).read_bytes()
        assert local.replace(b"\r\n",b"\n") == blobs[ref["path"]].replace(b"\r\n",b"\n"), ref
        assert 1 <= ref["line"] <= len(blobs[ref["path"]].splitlines()), ref
        if ref["declaration"]:
            assert declaration_line(ref["path"], ref["declaration"]) == ref["line"], ref
    aliases = {label: claim for claim, labels in LONG_ALIASES.items() for label in labels.split()}
    label_map = []
    missing = []
    for edition in ("long", "journal"):
        for row in numbered_labels(HERE.parent/edition):
            identifier = row["label"] if edition == "journal" else aliases.get(row["label"])
            if identifier not in claims:
                missing.append((edition,row["label"]))
            else:
                label_map.append(dict(edition=edition, claim_id=identifier, status=claims[identifier]["status"], **row))
    assert not missing, f"Unmapped numbered statements/equations: {missing}"
    result = dict(status="PASS", immutable_revision=PIN, claims=len(claims), retained_claims=89,
        finite_identities=138, simple_identities=104, source_files=len(paths), source_refs=len(refs),
        declaration_anchors=sum(bool(ref["declaration"]) for ref in refs),
        numbered_labels={edition:sum(row["edition"]==edition for row in label_map) for edition in ("long","journal")},
        labels=label_map,
        limitation="Validates source identities, declaration anchors, retained coverage and label mapping; does not rerun Lean or establish unstated mathematical implications.")
    if write_report:
        (HERE/"proof_map_validation.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({key:value for key,value in result.items() if key != "labels"},ensure_ascii=False))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-report", action="store_true", help="Save the successful validation report")
    validate(parser.parse_args().write_report)
