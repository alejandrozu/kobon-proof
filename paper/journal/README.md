# Journal-length Kobon manuscript

**Author:** Alejandro Zarzuelo Urdiales

**Version date:** 1 October 2026

[Read the journal version](Kobon_journal_version.pdf). It is a separate,
14-page article **including references and the proof index**, in 11-point type with 25 mm margins.
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

The PDF now contains a clickable result-to-proof index. The
[detailed proof map](proof_map.md) covers 89 claims and every one of the
138 finite certificate identities, with exact declaration links pinned to
the verified mathematical revision. Its [machine-readable counterpart](proof_map.json)
records source hashes and the verification scope of each claim.

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
the original manuscript's preserved hashes, all 325 frozen Lean source hashes,
all numbered theorem/equation mappings, declaration anchors, 297 pinned source
files, and clickable PDF proof links:

    python validate.py

The [journal release's GitHub verification run 36830561024](https://github.com/alejandrozu/kobon-proof/actions/runs/36830561024)
completed successfully at commit 6f7e11e. This traceability update changes
exposition and documentation only; every mathematical source remains unchanged.

**Ready for scholarly review does not mean every statement is formalized.**
The universal construction, geometric exterior and one-step BBL interfaces,
and finite certificates have Lean proofs with their stated hypotheses.
The global defect-extension geometry, global upper-bound geometry, and full
recursive BBL integration still lack end-to-end Lean proofs. The paper and
proof map state these limits explicitly. The cell lemma's general manuscript
wording and connected-component interpretation also exceed the present Lean
sign-cell interface, which assumes global nonparallelism.

The visual_review.json record identifies the PDF whose pages were rendered and
reviewed; validation.json records the consistency audit. Scratch compilation
and rendering files are ignored in build/. The source archive can be handed to
an editor for adaptation to the chosen journal's class and bibliography style.
The page count applies to this supplied layout, not an unspecified publisher's
future typesetting.
