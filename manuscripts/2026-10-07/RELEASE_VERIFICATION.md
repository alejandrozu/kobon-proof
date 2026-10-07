# Manuscript release verification - 7 October 2026

Both updated editions compile and have been visually reviewed. [Publication workflow 37620972643](https://github.com/alejandrozu/kobon-proof/actions/runs/37620972643) passed every publication check. It verifies source-equivalence to the already successful clean Lean build and audit, then independently runs the corrected exact-data replays, generators, evidence hashes and document checks.

| Check | Comprehensive | Journal |
|---|---:|---:|
| Pages, including references and appendices/index | 88 | 15 |
| Scientific figures used | 21 | 3 |
| Cited bibliography entries | 35 | 21 |
| Distinct clickable URLs | 148 | 79 |
| Immutable Lean source URLs | 119 | 59 |
| Embedded fonts inspected | 54 | 21 |
| Overfull boxes, missing glyph warnings, unresolved references | 0 | 0 |

The short edition retains 11-point body type and 25 mm margins. All references and the proof index are inside the 15-page limit.

## Proof and source traceability

Mathematical sources are pinned to `f44f23ee062a255f5cad7d39188fd55c0feb83a8`; the complete local publication replay is pinned to `af74635d8b25b32703088460bc41854bb18e1a05`. The replay covers 638 modules and audits 9058 declarations: 8046 standard-axiom only and 1012 native-evaluation descendants. No admitted proofs or unapproved axioms were found. Unchanged baseline closures and freshly compiled closures are distinguished.

The expanded map contains 200 scoped entries, preserves all 160 October 3 claim IDs and all 89 earlier IDs, and retains all 138 finite coordinate identities (104 simple). It verifies 409 source files, 836 references and 787 declaration anchors, including 141 long and 48 short numbered labels. These are coverage counts, not counts of original discoveries.

The six certificate helpers no longer write diagnostic files into an ignored local directory. This removes the clean-build dependency without changing mathematical statements. Compiler-assisted finite evaluation remains explicitly disclosed. Ordinary manuscript topology/resource arguments, exact external computations, incomplete concrete dual certificates and remaining conjectures retain separate statuses.

## Rendering and portability

Every final page was inspected in Poppler contact sheets, with full-page review of scientific formulas, figures, references and table continuations. Two oversized displays and the long contents numbering were repaired. The journal proof index fits a nonfloating table without a one-row continuation. All unchanged long body images were confirmed pixel-identical after the contents repair. Visual records identify the delivered PDF bytes.

The deterministic source archive contains 74 portable assets. Extracting it into a separate directory compiled both manuscripts at 88 and 15 pages. Standard TeX packages, Tectonic and Python/pypdf are build dependencies; Lean replay and provenance validation require the complete repository.

## Historical preservation

All 110 files from the October 3 manuscript release, including its two PDFs, remain byte-identical. The original earlier PDFs under `paper/` are also unchanged. New editions use separate dated paths.

PDF SHA-256 values:

```text
long: d56f87ce5989dec24e0b58700e9d49fadd2e75b64d19420204375a681cd49f81
journal: 7b3ff0bde1a5cd3083eafab2d8d87c9a9dc98e4ce4f7d4f1be8c588c19bc7221
```

The original workflow 37613706987 passed its clean Lean build, axiom audit, coordinate checks and interval checks, but its overall conclusion remains failure because its old export parser no longer matched the split source files. The parser was repaired without weakening its exact assertions. The successful separate publication workflow verifies all 638 current Lean source hashes against that clean receipt and reruns every remaining check. This composite status is recorded explicitly, rather than relabelling the original workflow. The final release validator is run without `--allow-pending-ci`.
