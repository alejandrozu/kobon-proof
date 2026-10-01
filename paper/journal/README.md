# Journal-length Kobon manuscript

**Author:** Alejandro Zarzuelo Urdiales

**Version date:** 1 October 2026

[Read the journal version](Kobon_journal_version.pdf). It is a separate,
13-page article **including references**, in 11-point type with 25 mm margins.
The [original 60-page manuscript](https://github.com/alejandrozu/kobon-proof/blob/22d1165f6c455fe45e461baef4410f6d5c78a014/paper/Kobon_triangle_constructions.pdf) remains
unchanged and serves as the detailed companion.

The article retains all substantive contributions from the completed research:
the uniform affine lower bound, exact geometric certificates, quantitative
extensions and their obstruction, compatible seeds and the geometric BBL step,
restricted multiplicity-sensitive upper estimates, finite consequences, and
exact smoothing diagnostics. It contains four vector figures and 17 references.

The long catalog, chronological narrative, repeated scope explanations, full
bibliographic audit, individual checkpoint drawings, implementation inventories,
and unsuccessful-search logs remain in the companion. The short article cites
an immutable revision of that document. [contribution_map.md](contribution_map.md)
records where each contribution is covered.

Claims keep their existing verification status. In particular, no unrestricted
successor theorem or completed infinite Lean BBL iteration is newly asserted;
the restricted upper proofs are distinguished from their checked local Lean
components. Numerical discovery credit for prior constructions is preserved.

## Compile the portable source

Install Tectonic and Python with pypdf, then run:

    python build.py

Use the --engine option for a specific Tectonic executable. Tectonic downloads
ordinary TeX packages on its first run. The build rejects unresolved references,
overflowing boxes, and a PDF longer than 15 pages. The output is
Kobon_journal_version.pdf.

The folder is self-contained for LaTeX compilation: main.tex, sections/,
references.bib, and the four vector PDFs under figures/ are all required.
It also compiles with current TeX Live using:

    latexmk -pdf -outdir=build main.tex

## Verification and preservation

Run the following from a full checkout to audit references, figure provenance,
the original manuscript's preserved hashes, and all 325 frozen Lean source hashes:

    python validate.py

The 60-page paper's GitHub verification run 35779849718 completed successfully.
The new article changes exposition only.

The visual_review.json record identifies the PDF whose pages were rendered and
reviewed; validation.json records the consistency audit. Scratch compilation
and rendering files are ignored in build/. The source archive can be handed to
an editor for adaptation to the chosen journal's class and bibliography style.
The page count applies to this supplied layout, not an unspecified publisher's
future typesetting.
