# Manuscript release verification — 3 October 2026

Both new editions have been compiled, inspected and audited. No Lean
source or prior manuscript was changed in preparing this release.

| Check | Comprehensive edition | Journal edition |
|---|---:|---:|
| Pages, including references and appendices/index | 73 | 13 |
| Scientific figures used | 18 | 3 |
| Cited bibliography entries | 31 | 18 |
| Distinct clickable external URLs | 89 | 57 |
| Distinct immutable Lean URLs in the PDF | 65 | 39 |
| Embedded fonts inspected structurally | 48 | 21 |
| Overfull boxes, missing characters, unresolved citations/references | 0 | 0 |
| Final pages visually inspected and independently rasterized | 73 | 13 |

The journal page count uses 11-point type and 25 mm margins. All its
references and the result-to-proof index are included in the 13 pages.

## Mathematical traceability

The shared map validates 160 scoped claims, retaining all 89 previous
claim identities and all 138 coordinate identities, 104 of them simple.
It checks 355 immutable source files, 701 source references and 651 Lean
declaration anchors. Every numbered statement or equation is mapped:
116 in the long edition and 36 in the journal edition. These are coverage
and source-identity checks, not an automatic proof of every prose statement.

All 375 active Lean source hashes match the successful mathematical release
at `2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8`. Its 270 targets passed in
[GitHub Actions run 37056093885](https://github.com/alejandrozu/kobon-proof/actions/runs/37056093885).
The source revision and successful proof run are linked from both papers.
This document-only release does not claim to add a new mathematical theorem.

Complete Lean proofs, native finite checks, conditional results, ordinary
manuscript arguments, exact external computations and unfinished drafts
retain different statuses. In particular, the full uniform 49- and 33-line
seed checks, global cyclic-fan extraction and arbitrary successor recurrence
are not presented as completed formalizations.

## Rendering and corrections

Every initial page was examined individually in full-page Poppler renders.
After corrections, every changed page was re-examined; all remaining long
pages were confirmed pixel-identical to their reviewed renders. Every final
page also rendered successfully in PDFium. Structural preflight checked
fonts, text extraction and page geometry. Missing ToUnicode maps, where
reported, are an extraction/accessibility limitation rather than evidence
of absent displayed glyphs.

The review corrected an identifier whose spaces disappeared, stale prose
and a table caption about the now-completed simple upper proof, and a
sentence conflating the separate 39:353 and 39:358 straightening runs. The
long edition's last three-line page was eliminated without removing results.
Proof endings display explicit Q.E.D. The original 60- and 14-page PDFs
remain byte-identical to their previous releases.

The retained `compilation.json` and `compilation.log` files allow inspection
from a fresh checkout without ignored scratch files. Each final PDF also has
a matching `visual_review.json`; the root `validation.json` records the
combined audit. The built-in editor's compiler was unavailable on this host;
the existing multi-file Tectonic build produced both verified PDFs.

## Portable source package

The archive contains 57 typesetting and companion assets. It was extracted
into a separate directory and both manuscripts compiled successfully there,
at 73 and 13 pages. The archive therefore supplies the required document
sources, bibliographies, tables and vector figures independently of the
repository layout. Standard TeX packages and the stated build dependencies
are still required. Proof replay and provenance validation use the complete
repository and its pinned Lean/Mathlib dependencies.

Delivered PDF SHA-256 values:

```text
Comprehensive: 06fbc2841266aeef17a2eb5f4777dc82e809787312b745b27aab09c8e69ef0ed
Journal:       5ca88ff6e8648b4880a17f7b2bec6b130fe0c0da296812238c1d1dbabd68008b
```

The repository evidence manifest includes this release's source, PDFs,
portable archive and verification records. A future edit or rebuild should
update the matching records after the relevant checks are repeated.
