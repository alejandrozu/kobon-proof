# Three hour research release

The user shortened the original six-hour research request to three hours.
The authorized session window is 04:36:37 to 07:36:37 UTC on 22 September 2026. The
directory name retains its original allocation to keep evidence links stable.

Start with the [cumulative review](RESEARCH_REVIEW.md) or its
[Word edition](Kobon_Research_Review.docx). The review covers the original
extension program, the unconditional all-order formula, finite certificates,
one-step geometric doubling, upper-bound ingredients, failed searches,
attribution and the exact next proof obligations.

The main verified formulas are:

- `Universal.baseline_sound`: `G(n)=floor(n(n-3)/3)+1+(n mod2)` for `n>=4`,
  with zero below three and one at three.
- `Universal.all_n`: the maximum of G and all saved finite lower bounds.
- `BBLDoubling.doubling`: for a compatible saturated tangent-grid seed with
  `q=4r>=20`, `0<epsilon<tan(pi/(2q))`, and the central apex above the
  distinguished line, actual simple geometry gives `(q+1,T) -> (2q+1,T+q²)`.

The first two are total all-order constructions. The third is a genuine
one-step construction with explicit geometric seed hypotheses. Infinite
iteration and the unrestricted full-gain successor recurrence remain open.
These statements do not establish numerical first priority for the formula.

## Evidence and continuation

- [Final local release verification](RELEASE_VERIFICATION.md)
- [Exact remaining infinite-iteration plan](hybrid-family/NEXT_ITERATION_PLAN.md)
- [Phase and projective proof](phase-proof.md)
- [General bounds and source audits](general-bounds/README.md)
- [Hybrid geometry and exact large witnesses](hybrid-family/README.md)
- [Construction search and formal cap geometry](construction-search/README.md)
- [Draft proof status](drafts/README.md)
- [Session scope and public rumor check](SESSION.md)
- [Root formalization audit](../../FORMALIZATION.md)
- [Final Lean build results](../../verification/lean-summary.json)
- [Independent coordinate results](../../verification/coordinate-summary.json)

All promoted finite coordinates were checked with two independent exact
counters. Large experimental coordinates outside the certificate catalog
have their own explicit status; the interrupted642-line direct check is not
described as complete. Source snapshots retain original authorship.

## Recreate the Word edition

The optional report builder uses Python with `python-docx`, Pandoc and
LibreOffice for rendering. These are separate from Lean proof dependencies.
Set `PANDOC_EXE` if Pandoc is not on PATH, then run
`python scripts/create_research_review_docx.py` from the repository. Its
equations are editable native Word mathematics; floor and ceiling use named
operators to avoid ambiguous glyph fallback in LibreOffice. The delivered
document was rendered and every page visually inspected.
