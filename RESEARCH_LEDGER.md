# Evidence and research ledger

Owner: Alejandro Zarzuelo Urdiales. Research session: 20 September 2026 (America/Los_Angeles). Reorganization starts from repository commit `fba9680` of 22 March 2026. Verification reports carry their actual UTC timestamps, which may fall on 21 September.

Read this file before resuming. It records what was retained, what failed, where the evidence lives, and what still needs proof. [FORMALIZATION.md](FORMALIZATION.md) is the authoritative Lean scope statement; [RESULTS.md](RESULTS.md) maps concrete claims to files.

## Evidence register

| Evidence | Location | What it supports |
|---|---|---|
| Original paper/repository | `archive/2026-03-original/`; public Archivara link in `evidence/sources.json` | Historical claims and attribution, including the unfinished Lean source |
| OEIS comparison | `evidence/oeis-observations.json`; `research/kobon-own-results/novelty-audit.md` | Entries/attributions observed during the audit, not proof of priority |
| Boundary argument | `research/kobon-extension/manuscript.md`, `boundary_extension.py`, `verification.json` | Ordinary geometric proof, exact boundary computation, and 560 deterministic test arrangements |
| Formal counting core | `Kobon/BoundaryExtension.lean` | Cyclic identities and numerical consequences with stated hypotheses |
| All promoted coordinates | `verification/certificate-index.json` | Unique coordinate hashes, original aliases, simple/nonsimple status, and Lean theorem names |
| Independent finite checks | `verification/coordinate-summary.json` | Agreement of adjacency and open-interior-sign counters |
| Lean compilation/axioms | `verification/lean-summary.json`, `verification/build-logs/` | Actual builds, scope, source hashes, and native-evaluation dependencies |
| Hybrid seed interval proof | `research/kobon-hybrid/verify_seed.py`, `seed-verification.json`, `seed-combinatorics.json` | 240 strict rational endpoint checks and the complete reference incidence data |
| Searches and discarded candidates | `experiments/2026-09-20/` and its index | Parameters, trial counts, successes, failed directions, and intermediate configurations |
| Earlier numerical comparisons | `research/kobon-own-results/`; `data/prior-configurations/` | Dominated values, published inputs, and exact reproduced benchmarks |
| Source versions and evidence integrity | `evidence/sources.json`, `evidence/file-manifest.json` | Links, source roles, pinned Git revisions, file sizes and SHA-256 hashes |

The source register identifies the relevant original works: Füredi–Palásti, Bartholdi–Blanc–Loisel (BBL), Blanc, Honma/Savchuk, Parpalak–Utkin, OEIS, and the Zarzuelo paper. Published inputs and their formulas remain attributed to their authors. Pseudoline results were not used as straight-line witnesses without a realizability argument.

## Research history and corrections

1. **Attribution audit.** OEIS explicitly names Zarzuelo for 28:238, 30:275, and 34:357, and links the Archivara paper. Attribution in a table is not first-discovery evidence. Earlier constructions already supply some equal or stronger numerical consequences; the priority audit records these comparisons. We have not established an accusation of missing credit or first discovery for the candidate families.
2. **Original proof audit.** The public March Lean file contained eight placeholders, including `kobon_extension` and several inputs. No newer completed proof was located in the inspected repository. The paper's assertion of complete formal verification is unsupported by that file. Its unqualified alternating-segment reasoning also fails for some choices of an exterior line: the exact five-line example has 3 triangles, and the specified sixth line gives only 4. This does not refute the maximum-function inequality.
3. **Extension for both parities.** The replacement argument counts unbounded wedges and charges unpaired free rays to unused bounded edges. For a simple arrangement with `n` lines, `T` triangles, and `d=n(n-2)-3T`, it gives the manuscript bound

   `T + ceil((n-1)*max(3,n-d)/(2*n))`.

   The cyclic counting and numerical consequences are in Lean. The Euclidean realization/charging bridge remains an ordinary proof. If an odd arrangement has defect at most two, the full odd-to-even gain follows from this argument. The unrestricted full-gain recurrence remains unproved.
4. **Finite tables and novelty screening.** The initial retained/extension tables mixed our derived outputs with stronger existing inputs. The own-results inventory separated them; the priority audit then removed dominated candidates. The current coordinate table materializes each earlier claimed inequality, using a stronger witness where available, and marks that witness's provenance. It is not a list of exclusively original records.
5. **Additional-line family.** Exact coordinates retained 39:469 and 51:817, 99:3169, 195:12481. The 39-line witness uses a published 38-line input; the other three use the Parpalak–Utkin even series. The general family formula is `n=q+3`, `q=6*2^t`, `T=q^2/3+q+1` at the relevant stages. Finite lower bounds now have independent coordinate certificates; the all-parameter geometric derivation still needs Lean formalization.
6. **The 44-line case.** An exact exterior addition to the published 43-line, 587-triangle simple input gives 608 triangles. The simple upper bound cited in the priority audit matches 608. Only the lower bound and simplicity are established by our coordinate development; the equality additionally uses that published upper bound. It says nothing equivalent about the unrestricted maximum.
7. **Hybrid search.** We investigated interior insertions, one-line local changes, coordinate normalization, tangent-grid compatibility, and relaxed seeds. An intermediate 21-line compatible seed improved from 129 to 131 triangles, reducing its infinite-family deficit from four to two. It is superseded by the final eleven-line seed below, which has deficit one.
8. **Final compatible seed.** Starting with the Honma-based eleven-line arrangement described by Savchuk, we selected a different distinguished line, fit a tangent-grid realization, and simplified its reciprocal slopes. The count 32 and the general doubling method are prior work. The additional evidence is a concrete grid-compatible realization valid for an entire small-parameter interval, together with the resulting manuscript family consequences. Priority remains unresolved.
9. **This consolidation.** Explicit coordinates were added wherever the earlier 3–60 own-results table had only a theorem-derived number. The active Lean library checks finite witnesses, rather than assuming the unfinished general extension. The original files, negative experiments, and weaker superseded claims remain accessible as history.

## Current hybrid seed and claim

Use `Y0: y=0` and `Li: x-vi*y=ai`, with ordered reciprocal slopes

`v = (15,-2,14,1,4,-4,5,-3,12,-5)/10`.

The ordered intercepts are

`(-tan(4*pi/10), -tan(3*pi/10), -tan(2*pi/10), -tan(pi/10), -epsilon, epsilon, tan(pi/10), tan(2*pi/10), tan(3*pi/10), tan(4*pi/10))`.

For `0 < epsilon <= 1/100000`, the interval verifier checks the same simple 32-triangle type, with all nine bounded segments of `Y0` used. It checks 120 determinants at two endpoints; every interval is more than 0.034 from zero. The determinants not involving `Y0` are affine in epsilon. The zero endpoint supplies limits only and is not asserted to be a simple arrangement. Machin's identity and Taylor remainders provide rational bounds on the tangent constants; the separate real-analysis formalization is still needed.

The manuscript combines this input with the published geometric iteration to obtain

`K_s(10*2^t+1) >= (100*4^t-4)/3`.

For each target order choose `epsilon=min(1/100000,1/(40*2^t))`. This is a family of finite constructions, not a claim that one fixed positive epsilon works through infinitely many stages. The exact finite odd witnesses retained here are 11:32, 21:132, 41:532, 81:2132, 161:8532. The first two larger checkpoints 21 and 41 are weaker than known 133 and 533 inputs.

The boundary-defect manuscript gives adjacent even bounds `(q^2-4)/3+q/2-1`, where `q=10*2^t`. Finite searches gain one more triangle at 12,22,42,82,162, yielding 37,142,552,2172,8612. The first three do not improve the retained catalogue. The extra one for all parameters is **not proved**. `Families.lean` verifies these closed-form identities, not the geometric existence statements.

## Negative and superseded directions

| Direction | Recorded result | How to resume productively |
|---|---|---|
| Vertex-chord insertions on selected 38/43/50 inputs | 1,274,096 proposals; no improvement over retained bounds | Change seed type or insertion model. Floating ranking may miss candidates; this is not exhaustive optimality. See `hybrid-*.search.json`. |
| Local one-line search at 39/47/51 | 5,867,928 proposals; accepted changes checked exactly; no improved retained bound | Use a new neighborhood or multi-line moves. See `local-*.search.json` and `hybrid_local.py`. |
| Exact-grid fitting of optimal 21/23/27/31/35/41/43/45 inputs | No compatible type-preserving fit found in the recorded trials | Find a structural obstruction or change distinguished line/type. The 19-to-37 positive control succeeded. See `grid-report-*.json`. |
| Relaxed 21-line family | 129 then 131 triangles; deficits four then two | Preserved as an intermediate result; the eleven-line family is stronger. See `earlier-gap-two-*`. |
| Secondary compatible candidates | 23:145, 27:199, 35:364 and finite doubled examples | Exploratory checks only; no promoted interval theorem or complete independent/Lean verification for this branch. See mutation/pencil/relaxed reports. |
| Full exterior gain under arbitrary repeated insertion | Seven-line example has maximum exterior gain 2 rather than 3 | The boundary criterion must be maintained explicitly; do not assume an induction from a few successful steps. |
| Sampling alternate affine charts of nonsimple FP inputs | No better result in tested charts | Bounded search only, not a maximum or priority proof. See `audit_fp_*`. |

The frozen experiments may contain preliminary counts, abandoned hypotheses, and old paths. They are evidence of attempts, not promoted claims. [experiments/README.md](experiments/README.md) explains how to reconstruct their original working layout. Only the certificate index identifies promoted finite witnesses.

## Priority and comparison guardrails

The earlier omitted outputs at 40,47,48,52,53,54,55,56,57,59,60 were already dominated by older constructions. The 58:1073 consequence was already obtainable from published input and extension results. See the exact comparison table in the priority audit. The five earlier remaining candidates (39,44,51,99,195) and newer hybrid counts are candidates after the comparisons performed here, not certified firsts.

The 3–60 materialization does not attempt to include every externally known classical witness: for example it retains simple 8:14 while OEIS lists classical 8:15. This difference is not an improvement or a contradiction. The source table and variant must accompany every comparison.

## Next tasks, in order

1. Finish the Euclidean-to-cyclic proof obligations in [FORMALIZATION.md](FORMALIZATION.md), including a formal cell/empty-triple bridge. Preserve the present theorem statements and do not replace missing geometry by assumptions bearing the same conclusion.
2. Formalize the actual seed interval theorem and geometric BBL iteration; connect them to `Families.lean`. This is required for a self-contained infinite-family Lean claim.
3. Analyze the fixed exterior normal `(10,-13)` observed to attain the full finite gain at the checked hybrid stages. Derive an all-stage boundary invariant or find a counterexample. Record any normalization needed before comparing normals.
4. Seek a compatible seed/type that eliminates the last odd-family triangle, or prove an obstruction for this type. The current finite 81/161 bounds have a one-triangle gap in the working catalogue; this is a research target, not an established impossibility.
5. Formalize the second additional-line family and prove or correct its parameter range.
6. Extend the independent priority review to implicit consequences of earlier constructions. Check both simple and nonsimple variants. Only after this review should a first-discovery or OEIS update claim be drafted.

At each resume: read this ledger, inspect `git status`, check the last verification reports against file hashes, choose one explicit obligation, and preserve any new negative result with its seed, parameters, stopping rule, and exact-validation status. Do not relabel a numerical search or an arithmetic identity as a geometric existence proof.
