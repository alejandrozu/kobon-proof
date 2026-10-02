# Rendering revision, 2 October 2026

The current comprehensive manuscript has 60 pages; the journal version has
14 pages including references and its proof index.

The reported hollow squares after proofs on page 12 of the original long
manuscript are standard amsthm proof-end marks. Poppler and PDFium reproduced
them as intended; the review did not find a missing-font cause. Both versions
now use explicit **Q.E.D.** text to remove that ambiguity.

The full review also corrected:

- A Lean expression whose URL-style formatting suppressed spaces between
  identifiers. It now reads “Universal.bound = max Universal.baseline AllN.bound”.
- A journal-page identifier split inside its name. Short-paper Lean identifiers
  now stay together.
- Excessive spacing in the journal proof-index columns.
- A forced page break that stranded two closing lines on an almost-empty page.
- The journal's companion reference, which now leads to the corrected long PDF.

All pages of both final PDFs were visually inspected. Poppler rendering,
PDF structural checks, embedded-font checks, extracted-text checks, and TeX
diagnostics supplement that review. The validators now reject missing-character
warnings, invalid font/page/text structure, and stale visual-review hashes.
The URL-style identifier macro is checked against expressions containing spaces.
Missing ToUnicode maps in some legacy math fonts are recorded as a copy/accessibility
limitation, not incorrectly labeled as missing displayed glyphs.

The mathematical statements, Lean proof files, certificate data, and scientific
figures are unchanged. This revision does not complete any partial formalization.
The original release and all 71 of its recorded file hashes remain verifiable
at commit 22d1165f6c455fe45e461baef4410f6d5c78a014. The current corrected package
has a separate manifest and PDF hash. An old commit URL necessarily continues
to show the historical version; use the current paper links when sharing.

The hash-bound records are visual_review.json and validation.json in each
paper folder. The repository evidence manifest covers both packages.
