# Kobon manuscripts: comprehensive and journal editions

**Alejandro Zarzuelo Urdiales — 3 October 2026**

These two new editions incorporate the March–September results and the
completed October research. They preserve the earlier manuscripts under
[`paper/`](../../paper/README.md); no historical PDF has been replaced.

- [Comprehensive research edition](long/Kobon_comprehensive_2026-10-03.pdf), 73 pages:
  full arguments, historical results, all 138 finite coordinate identities,
  the 3–60 inventory, literature review, original scientific figures,
  successful and unsuccessful experiments, and the next research tasks.
- [Journal edition](journal/Kobon_journal_2026-10-03.pdf), 13 pages: a concise article
  in 11-point type with 25 mm margins, including references and a clickable
  proof index. The build enforces a maximum of 15 pages in this layout.
- [Portable LaTeX source package](Kobon_manuscripts_2026-10-03_sources.zip):
  both manuscripts and all their required typesetting assets.
- [Complete result-to-proof map](shared/proof_map.md) covering 160 claims,
  [machine-readable map](shared/proof_map.json), and
  [contribution coverage](shared/coverage_map.md). All 89 previous claim IDs
  and all 138 finite coordinate identities remain included.
- [Primary-source and novelty audit](shared/literature_scope_audit.md).

## What has changed

The new editions retain every distinct contribution from the earlier papers,
including the March-associated 28:238, 30:275 and 34:357 inequalities, phase
and affine-chart refinements, exterior extension and its resource limitation,
finite witnesses, local upper-bound arguments, and smoothing diagnostics.

The principal addition is the completed geometric Lean iteration. For
`q = 10 * 2^t`, the construction gives `(q^2 - 4)/3` triangles on `q+1`
lines and that count plus `q/2` on `q+2` lines, for every natural `t`.
The retained all-order envelope combines these families with the previous
general formula and every saved finite certificate. It strictly improves
the previous verified repository envelope on infinitely many orders, starting
with the family pair 321/322. The actual simple upper theorems give a
one-triangle window at both parities. These claims concern the verified
repository envelope, not a new numerical record over all published work.

The editions also include actual edge and clean-line incidence proofs,
extremal local fan results, the exact representative tangent-grid obstruction,
the externally verified 236-class obstruction corpus, and the uniform
49-line seed computation. The full 49- and 33-line finite Lean seed checks,
global cyclic-fan assembly, and unrestricted repeated one-line recurrence
remain unfinished and are labeled accordingly. Final graph deductions are
research directions with explicit remaining hypotheses.

## Proof release and trust

Lean source links are pinned to
[`2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8`](https://github.com/alejandrozu/kobon-proof/tree/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8).
The [successful CI run](https://github.com/alejandrozu/kobon-proof/actions/runs/37056093885)
covers the mathematical release. Its audit checked 270 build targets and
375 active Lean sources, with 5,241 theorem declarations: 4,405 use only
standard logical axioms and 836 inherit native finite-check dependencies.
The catalog has 138 coordinate identities, including 104 simple witnesses.
These implementation counts are not counts of original discoveries.

The manuscripts do not claim that every discussed statement has a complete
Lean proof. General geometric proofs, native finite validation, conditional
implications, ordinary mathematical arguments, external exact computation,
and unfinished branches are identified separately. Numerical methods and
inputs inherited from other researchers retain their attribution.

## Compile the portable sources

Install Tectonic and Python with `pypdf`, then from this directory run:

```sh
python build.py --edition both
```

Use `--engine /path/to/tectonic` to choose an executable, or `--edition journal`
to compile only the short paper. Each typesetting directory contains its
own `main.tex`, section sources, bibliography and vector figures; the long
edition also contains generated catalog tables. Current TeX Live can compile
either edition with `latexmk -pdf -outdir=build main.tex` from that directory.
Tectonic may fetch ordinary TeX packages on its first run.

The existing multi-file Tectonic workflow produced the released PDFs. The
Codex editor opens their sources, but its built-in compiler was unavailable
on this host (`Unable to find standard directories for platform`). No
successful built-in compilation is claimed.

## Reproduce the evidence and PDF checks

These commands require a complete repository checkout, not just the source
archive. From the repository root:

```sh
python manuscripts/2026-10-03/shared/validate_proof_map.py
python manuscripts/2026-10-03/validate.py
python scripts/evidence_manifest.py --check
```

The release validator checks the unchanged 375 verified Lean sources, pinned
link targets, preserved historical PDFs, embedded PDF fonts, resolved
references, page counts, and matching visual-review records. Rebuilding the
PDFs can change their bytes; review the new renders before replacing a
visual-review record. The recorded review identifies the delivered bytes.

To regenerate the two new scientific figures, use `make_figures.py` with
NumPy and Matplotlib. Their formulas and source hashes are recorded in
`new-figure-manifest.json`. Sixteen earlier figures are preserved from the
original paper with their original generation data. The seed illustration
shows explicitly cropped windows, not all triangles at once.

To render every page, run `render.py` with `pypdf`, Pillow, and Poppler's
`pdftoppm` on PATH. Visual inspection supplements structural checks; a
successful TeX build alone does not establish rendering quality.

The full Lean and exact-arithmetic replay commands remain in the
[repository README](../../README.md) and the
[October research review](../../research/three-hour-2026-10-02/RESEARCH_REVIEW.md).
The page limit applies to the supplied layout; a journal's typesetting
class may change pagination.
