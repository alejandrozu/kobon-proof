# Kobon constructions, certificates, and proof audit

Research repository of **Alejandro Zarzuelo Urdiales**. This revision consolidates the March 2026 paper and the subsequent extension, comparison, and hybrid-construction work.

**Comprehensive manuscript:** [Kobon Triangle Constructions (PDF)](paper/Kobon_triangle_constructions.pdf), with [LaTeX source and reproduction instructions](paper/README.md). The 60-page paper includes 29 references, 16 original vector figures, the 3–60 table, and the complete 138-certificate catalog. It distinguishes completed proofs from conditional families and unfinished claims.

**A stronger explicit lower bound for every natural order is now proved in Lean.** For `n >= 4`, `Kobon.Universal.baseline_sound` constructs a simple real-line arrangement with at least

`G(n) = floor(n(n-3)/3) + 1 + (n mod 2)`

triangles, with `G(0)=G(1)=G(2)=0` and `G(3)=1`. It improves the previously formalized classical ceiling baseline by 0, 1, or 2 triangles, depending on the residue class. `Universal.all_n` takes the maximum with every saved finite certificate. The infinite geometric proof uses only Lean's standard logical axioms. This is a verified refinement of a classical construction, not an established claim of first numerical discovery or a solution of the Kobon problem.

Read the [cumulative research review](research/six-hour-2026-09-21/RESEARCH_REVIEW.md) and [formula and novelty audit](research/six-hour-2026-09-21/phase-proof.md). The unrestricted full-gain recurrence and end-to-end infinite BBL iteration remain separate obligations; [FORMALIZATION.md](FORMALIZATION.md) records the distinction.

Start with:

- [RESEARCH_LEDGER.md](RESEARCH_LEDGER.md): evidence, research history, failed approaches, corrections, and the next research tasks.
- [RESULTS.md](RESULTS.md): coordinate witnesses and their Lean theorem names, including the earlier 28:238, 30:275, and 34:357 bounds.
- [FORMALIZATION.md](FORMALIZATION.md): precisely what each proof establishes and which assumptions remain outside Lean.
- [All-order formalization](research/all-n-formalization/README.md): the total formula, full classical construction proof, finite enhancements, unconditional 49-seed target, and novelty limits.
- [Successor formalization](research/successor-formalization/README.md): the requested recurrence, its conditional formula, the new geometric Lean proof, and the obstruction to repeating exterior full-gain steps.
- [evidence/sources.json](evidence/sources.json): source URLs, roles, versions, and provenance.
- [verification/lean-summary.json](verification/lean-summary.json): build outcomes and source hashes; [coordinate-summary.json](verification/coordinate-summary.json): independent exact counts.

The finite catalog includes independently reproduced recent witnesses from Andrea Maiorana and Parpalak–Utkin, including 14:54, 20:117, 26:204, 32:315, 38:450, and 50:792. These published results retain their authorship. The new universal formula also supersedes several earlier repository values, for example 39:470, 51:818, 99:3170, and 195:12482. These are lower bounds, **not claims of first discovery or an exhaustive global record survey**. Classical arrangements may have multiple intersections; simple arrangements may not. An upper bound for simple arrangements cannot automatically be used for the classical problem.

The current catalog contains **138 distinct finite coordinate certificates**, including **104 simple witnesses**, with exact coordinates, source provenance, and named Lean theorems. The earlier 3–60 inventory inequalities retain finite witnesses and named aliases. These counts include published inputs, weaker checkpoints, and reproduced comparisons; they are not counts of original discoveries. The final build and coordinate summaries give the verification status for this revision.

## Verify from a fresh checkout

Install [Lean through elan](https://github.com/leanprover/elan) and Python 3.10 or later. The toolchain and Mathlib revision are pinned; the checkout contains the coordinates and all project proof sources. Initial setup needs network access for these pinned dependencies.

```sh
lake exe cache get
python scripts/verify_lean.py --jobs 2
python scripts/verify_coordinates.py
python scripts/verify_seed_interval.py
python scripts/evidence_manifest.py --check
```

The bounded build command compiles every certificate, result alias, and the axiom audit. Large certificates can take several minutes each. A normal `lake build` also builds the library; `lake build Kobon.Audit` runs the additional axiom check. Set `LEAN_NUM_THREADS=2` on memory-constrained machines.

Finite certificates use Lean's `native_decide`: this is placeholder-free but trusts native evaluation, including Lean's compiler/runtime. The audit reports these generated dependencies separately. The generic soundness, counting, and arithmetic proofs use the usual logical axioms; no unproved geometric assertion is introduced as an axiom. Small rational examples additionally use kernel reduction.

## Repository map

| Path | Contents |
|---|---|
| `Kobon/Geometry.lean`, `Simple.lean` | Real straight-line witness predicates and integer certificate soundness |
| `Kobon/Certificates/`, `SimpleCertificates/` | Explicit coordinates, triangle lists, finite lower bounds, simplicity checks |
| `Kobon/Results.lean` | Named 3–60 table results and every earlier numerical inventory claim |
| `Kobon/FurediPalastiCount.lean`, `FurediPalasti.lean`, `AllN.lean` | Proved all-order classical construction, finite enhancement envelope, and unconditional 49-seed numerical target |
| `Kobon/Universal.lean`, `ShiftedFurediPalasti.lean`, `FurediPalastiTwoCaps.lean` | Stronger parity-sensitive all-order construction and precise improvement formula |
| `Kobon/Cells.lean` | Actual uncut triangle interiors, sign cells, and disjointness |
| `Kobon/BBL*.lean`, `Reindex.lean` | Real analytic doubling ingredients, crossing-order geometry, cap replacement, visibility and finite assembly |
| `Kobon/SharedFan.lean`, `FanGeometry.lean`, `FanCount.lean`, `CyclicFan.lean`, `CleanLineBudget.lean` | Verified local incidence geometry and explicitly conditional upper-budget arithmetic |
| `research/six-hour-2026-09-21/` | Three-hour session review, evidence, current proof status, and separately labeled drafts |
| `experiments/2026-09-21/` | Reproducible searches, local obstructions, exact finite families and negative results |
| `Kobon/BoundaryExtension.lean` | Cyclic counting and conditional numerical extension consequences |
| `Kobon/Exterior.lean` | Real exterior construction and triangle creation/counting from visible old pairs, for either parity |
| `Kobon/Parametric.lean`, `TangentBounds.lean`, `SeedFamily.lean` | Real parameter family, exact tangent enclosures, and arbitrarily small valid eleven-line seeds |
| `Kobon/Iteration.lean`, `Iteration49.lean` | Conditional full-recurrence formula, resource-budget obstruction, and finite profile checks |
| `Kobon/Families.lean`, `AffineLemmas.lean` | Arithmetic identities and endpoint/convexity lemmas |
| `research/kobon-extension/` | Both-parity boundary-defect manuscript, algorithms, and examples |
| `research/kobon-hybrid/` | Stable eleven-line seed, interval proof, BBL-based manuscript, finite family |
| `research/kobon-own-results/` | Earlier inventory and priority audit, including dominated outputs |
| `research/kobon-research/` | Additional-line family draft and 51/99/195 certificates |
| `research/finite-table/` | Explicit witnesses for all 3–60 numerical claims in our inventory |
| `data/prior-configurations/` | Attributed comparison inputs |
| `experiments/2026-09-20/` | Frozen search scripts, proposal logs, intermediate seeds, and unsuccessful directions |
| `archive/2026-03-original/` | Original repository files, preserved with their incomplete proofs clearly labeled |
| `scripts/`, `verification/`, `evidence/` | Reproduction tools, build logs, proof index, and evidence hashes |

The `research/` packages preserve the earlier deliverables and their historical manifests. Their original relative links are interpreted within each package. The root ledger and formalization status govern the current verification claims. No changes to OEIS, Archivara, or other researchers' repositories are made by this project.
