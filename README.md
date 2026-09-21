# Kobon constructions, certificates, and proof audit

Research repository of **Alejandro Zarzuelo Urdiales**. This revision consolidates the March 2026 paper and the subsequent extension, comparison, and hybrid-construction work.

**An unconditional lower bound for every natural order is now proved in Lean.** `Kobon.AllN.all_n` combines a complete real-coordinate proof of the classical Furedi–Palasti baseline `ceil(n(n-3)/3)` with 52 stronger saved finite values. It also proves the former 49-seed numerical target unconditionally. See [the all-order report](research/all-n-formalization/README.md). The unrestricted full-gain recurrence and the separate BBL-based hybrid-family geometry remain unfinished; [FORMALIZATION.md](FORMALIZATION.md) distinguishes these obligations.

Start with:

- [RESEARCH_LEDGER.md](RESEARCH_LEDGER.md): evidence, research history, failed approaches, corrections, and the next research tasks.
- [RESULTS.md](RESULTS.md): coordinate witnesses and their Lean theorem names, including the earlier 28:238, 30:275, and 34:357 bounds.
- [FORMALIZATION.md](FORMALIZATION.md): precisely what each proof establishes and which assumptions remain outside Lean.
- [All-order formalization](research/all-n-formalization/README.md): the total formula, full classical construction proof, finite enhancements, unconditional 49-seed target, and novelty limits.
- [Successor formalization](research/successor-formalization/README.md): the requested recurrence, its conditional formula, the new geometric Lean proof, and the obstruction to repeating exterior full-gain steps.
- [evidence/sources.json](evidence/sources.json): source URLs, roles, versions, and provenance.
- [verification/lean-summary.json](verification/lean-summary.json): build outcomes and source hashes; [coordinate-summary.json](verification/coordinate-summary.json): independent exact counts.

The retained finite highlights are 39:469, 44:608, 51:817, 81:2132, 82:2172, 99:3169, 161:8532, 162:8612, and 195:12481. These are lower bounds, **not claims of first discovery or an exhaustive global record survey**. Construction inputs retain their original authorship. Classical Kobon arrangements may have multiple intersections; simple arrangements may not. Never apply an upper bound for the simple variant to the classical problem.

The consolidation verified **86 distinct finite coordinate certificates**, including **75 simple witnesses**, and preserved **212 experimental files**. The earlier 3–60 inventory inequalities all have finite witnesses and named Lean aliases. This count includes published inputs, weaker checkpoints, and reproduced comparisons, not 86 original discoveries.

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
