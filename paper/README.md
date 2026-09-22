# Kobon Triangle Constructions

**Author: Alejandro Zarzuelo Urdiales**

**Manuscript date: 22 September 2026**

[Read the paper](Kobon_triangle_constructions.pdf). The main LaTeX file is
[main.tex](main.tex); its bibliography is [references.bib](references.bib).
This is a comprehensive research manuscript, not a claim of journal acceptance.

The paper covers the March proposal, the corrected extension statements,
individual certificates, the uniform lower bound, compatible doubling seeds,
sparse families, multiplicity-sensitive upper arguments, and unsuccessful
research directions. Its principal unconditional all-order construction is

`G(n) = floor(n(n-3)/3) + 1 + (n mod 2)` for `n >= 4`,

with zero below three and `G(3)=1`. A finite maximum retains all 138 promoted
coordinate certificates. General Lean theorems, native-evaluated finite
certificates, manuscript proofs, and unfinished assertions are identified
separately. The original unrestricted successor rule and end-to-end Lean
iteration of the sparse BBL family remain unfinished. Published constructions
retain their original attribution; numerical first priority for the uniform
refinement is not established.

## Contents

- `sections/`: eleven main sections and four appendices.
- `references.bib`: 29 references, with versions and source status.
- `figures/`: 16 newly generated vector PDF figures and PNG previews.
- `generated/`: complete 3–60 table, 138-coordinate catalog, historical
  inventory, exact rendering data, source hashes, and figure QA.
- `literature_audit.md`: primary-source checks and priority decisions.
- `family_claim_audit.md`: exact status of extensions and sparse families.
- `figure_audit.md`: scientific meaning, provenance, and limits of each plot.
- `validation.json`: source, reference, figure, table, and PDF audit.
- `scripts/`: manuscript build, figure generation, and validation tools.

The mathematical sources are frozen at commit
`99fdc8ec1ef8b1fb22c3da32b011b7361762e958`. The later manuscript commit adds
exposition and figures without changing those Lean sources. The full source
archive includes the repository's exact coordinates, Lean files, licenses and
verification records; `generated/certificate-catalog.json` maps each coordinate
identity to its source files and theorem module.

## Build the PDF

Install [Tectonic](https://tectonic-typesetting.github.io/), then run from the
repository root:

```sh
python paper/scripts/build_paper.py
```

Or specify an executable directly:

```sh
python paper/scripts/build_paper.py --engine /path/to/tectonic
```

Tectonic downloads standard TeX packages on its first run. The script compiles
references to convergence, rejects undefined references and overflowing boxes,
and writes `paper/Kobon_triangle_constructions.pdf`. Temporary compilation and
page-rendering files belong in the ignored `paper/build/` directory.

The LaTeX document can also be built with a current TeX Live installation:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -outdir=build main.tex
```

Only the `paper/` folder is needed to compile the supplied LaTeX and vector
figures. The whole repository is needed to regenerate figures from their
original coordinate and experiment inputs.

## Reproduce figures and validation

Use Python with NumPy and Matplotlib. The release was rendered with NumPy 2.4.3
and Matplotlib 3.10.8. Figure geometry is enumerated with exact rational
arithmetic before floating-point conversion for drawing.

```sh
python -m pip install numpy==2.4.3 matplotlib==3.10.8 pypdf
python paper/scripts/generate_figures.py
python paper/scripts/build_paper.py
python paper/scripts/validate_paper.py
```

The validation script checks all 325 Lean source hashes against the completed
proof audit, all figure-input hashes, the catalog and finite table, resolved
LaTeX labels/citations, the 16 included figures, and the PDF metadata/page count.
This is a consistency audit; it does not replace replaying Lean. The repository
root [FORMALIZATION.md](../FORMALIZATION.md) explains how to replay the proofs.

All pages of the release PDF were rendered and visually inspected. Figure
previews were also inspected separately. No pre-existing illustration was
copied; the arrangements and datasets retain their mathematical attribution.

## Reuse and attribution

The sole named manuscript author is Alejandro Zarzuelo Urdiales. Computer and
AI assistance is disclosed in Section 10. External data retain their own
attribution and license notices; the manuscript does not grant new rights over
those sources. The exact finite checks do not confer authorship of an imported
construction or prove numerical optimality without a matching upper theorem.
