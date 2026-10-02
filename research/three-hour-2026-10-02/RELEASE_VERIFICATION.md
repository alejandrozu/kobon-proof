# Release verification — 2 October 2026

This record accompanies the [research review](RESEARCH_REVIEW.md) and
[declaration-by-declaration proof index](PROOF_INDEX.md). Completed theorems,
external exact computations, and uncompleted drafts have different statuses.

## Active Lean library

The complete release build **passed all 270 requested targets**, covering
**375 active Lean source files**, at **19:33:19 UTC**. This is an increase of
50 active sources over the preceding release. Every active source belongs to
both the requested build closure and the root axiom audit. All 375 source
hashes were unchanged throughout the build and matched again after completion.

The root audit checked **5,241 project theorems**: 4,405 depend only on the
three standard logical axioms; 836 additionally inherit explicitly permitted
native-evaluation dependencies. These are theorem counts, not counts of
distinct native checks. No `sorryAx` or unapproved axiom was found.

The pinned toolchain is `leanprover/lean4:v4.31.0`; Mathlib is pinned to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The verifier checks source hashes
before and after the run and fails if active source contents change. Its
complete record is [lean-summary.json](../../verification/lean-summary.json),
with individual compiler output under
[build-logs](../../verification/build-logs/).

The source scan rejects `sorry`, `admit`, custom `axiom` declarations, and
`unsafe` declarations after stripping strings and nested comments. The Lean
axiom audit separately checks all project theorems. It allows only the three
standard logical axioms and explicitly identified native finite-certificate
checks. Native evaluation trusts Lean's compiler and runtime in addition to
the kernel; it is not described as a kernel-only certificate proof.

The recursive eleven-seed odd family inherits four native checks; the even
family inherits six. Their generic recursion, the actual simple upper bounds,
the geometric charging theorem, and the representative tangent-grid
obstruction use only the standard logical axioms. The one-triangle windows
combine the corresponding upper theorem with the native-certified existence
theorem. Conditional Forge-family theorems retain their uniform seed premises.

## Exact external certificates

The final replay after archiving the uncompleted 49-line Lean sources passed
all five checks, using only standard Python:

| Check | Final scope |
|---|---|
| Affine 21-line obstruction | 3,765 polynomial dependence certificates and 15,060 symmetry variants cover all 4,956 class/support choices in the supplied 236-class input, for `0 < epsilon < 1/2,000,000`. |
| Uniform 49-line seed | Regenerated fixed rational slopes and exact tangent intervals reproduce the frozen certificate; 767 triangles persist on `0 < epsilon <= 1/100`. |
| Uniform exterior visibility | 24 visible pairs and the rightmost pair are checked on the regenerated seed. |
| Local grid robustness | Exact interval elimination certifies the stated radius `1/1000` for the representative obstruction's 11 used intercepts. |
| Generated Lean data export | Independently parses the archived seed/visibility sources and re-evaluates all direction, simplicity, triangle, and visibility predicates with exact fractions. |

The [replay summary](../../verification/research-2026-10-02/summary.json)
records checker hashes, exit codes, and timings. Source hashes are checked
again at the end. Reports are written under `verification/`, so replay does
not overwrite the frozen discovery evidence. Input hashes and classification
provenance are retained in the construction reports. Classification
completeness is an attributed external theorem, not a Lean enumeration result.

## Uncompleted branches

The concrete 33-line base build was stopped after approximately 49 minutes;
the concrete 49-line base build was stopped at 19:12 UTC after approximately
30 minutes. Neither returned a successful full compiler result. Their three
and five dependent sources, respectively, are preserved under
[drafts](drafts/README.md), outside the active library and its build manifest.
No infinite-family claim in this release depends on treating either draft as
checked. The known numerical families retain their literature attribution.

The 49-line tangent bounds and isolated graph/arithmetic checks did pass,
as did its independent exact external certificates. Those facts do not
substitute for a completed Lean check of the entire seed dependency chain.
See [the detailed boundary](bbl/SEED49_STATUS.md).

All three preserved [isolated check inputs](bbl/checks/README.md) were replayed
successfully at 19:29 UTC: the 49-line graph/central-height identities, the
49-family arithmetic, and the 33-line directions-only check. Their
[separate summary](bbl/checks/summary.json) records source hashes and compiler
exit codes. The first two printed roots use standard axioms; the directions
check uses native evaluation. These copied-definition checks remain separate
from full seed validity and from the 375-source active library.

Global cyclic-fan extraction/matching remains unfinished for the nonsimple
upper-bound program. The unrestricted full-gain successor recurrence and
the full Kobon problem remain open. No new finite numerical record is claimed.

The [final continuation memo](NEXT_PROOF_PLAN.md) records a separately
checked mathematical counting argument and the exact proposed next lemmas.
It is labeled unformalized and does not change the completed theorem list or
the 375 audited Lean source files.

## Existing manuscripts and reproduction

Both manuscript validators passed: the long paper remains **60 pages** and
the journal version **14 pages**. Their 325 mathematical source files are
checked against frozen Git revision
`99fdc8ec1ef8b1fb22c3da32b011b7361762e958`. The original 71-file long-paper
snapshot is also preserved and verified separately. Neither PDF changed in
this research session; the new results are documented in the research report.

From the repository root, using the pinned Lean toolchain:

```sh
lake exe cache get
python scripts/verify_lean.py --jobs 2
python scripts/verify_research_2026_10_02.py
python scripts/evidence_manifest.py --check
```

The GitHub workflow also independently rechecks all retained finite
coordinates and the older rational interval argument. A local successful
build does not imply that a newly triggered remote CI run has finished.
