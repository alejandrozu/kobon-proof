# Result-to-proof map for both October manuscripts

Audited 7 October 2026. Mathematical sources are pinned to `f44f23ee062a255f5cad7d39188fd55c0feb83a8`; verification metadata is pinned to `af74635d8b25b32703088460bc41854bb18e1a05`. Every linked revision is explicit in the JSON.

This map preserves all **89 historical claim identities**, all **160 October 3 claim identities**, and **138 finite coordinate identities** (104 simple). It adds the completed quantitative successor, compatible 33/37/49/61 families, actual degree-free structural bounds and exact translation calculus. It does not claim every manuscript argument is formalized in Lean.

The actual whole-arrangement fan assembly and terminal counting are now complete. The strongest global all-triple bound retains M22; the strongest component portfolio retains N12 but has no M22 term. Residual equality analysis and the concrete 41-line dual remain respectively mathematical analysis and external exact computation.

**Trust.** Standard proofs use only `propext`, `Classical.choice`, and `Quot.sound`. Native descendants additionally trust Lean's compiler/runtime; the ten-dyadic odd/even family inherits four/six checks, while the61 odd/even seed families inherit five/seven. A conditional Lean theorem proves its implication, not automatic satisfaction of every hypothesis. The sign-cell/component interpretation includes the manuscript's elementary topology argument.

The current [local verification summary](https://github.com/alejandrozu/kobon-proof/blob/af74635d8b25b32703088460bc41854bb18e1a05/verification/lean-summary.json) covers 638 active Lean sources and audits 9058 theorem declarations (8046 standard-only, 1012 finite-native descendants). Local mode: `incremental-hash-pinned-baseline-plus-direct-compilation`; complete: `True`. Unchanged baseline source/import closures are reused. The last confirmed CI listed in the JSON is identified by its own commit; a successful older run is not attributed to this mathematical pin. These are audit counts, not mathematical-discovery counts.

The [machine-readable map](proof_map.json) binds every declaration line to its source SHA-256 and immutable Git blob. Rebuild with `python manuscripts/2026-10-07/shared/build_proof_map.py`; validate without editing with `python manuscripts/2026-10-07/shared/validate_proof_map.py`.

## Evidence labels

- **lean/general:** the stated proposition for arbitrary permitted parameters, with recorded trust dependencies.
- **lean/finite:** exact finite coordinate certificate, with native evaluation where disclosed.
- **lean/derived:** immediate mathematical corollary of linked complete Lean results; no separate wrapper asserted.
- **lean/conditional-interface:** fully checked implication with explicit geometric or seed premises.
- **partial/manuscript:** a broader ordinary argument includes components not yet formalized.
- **computation:** exact external calculation with its input and parameter scope.
- **external/research-plan:** attributed literature result or explicitly unfinished deduction.

## Claim inventory

### j:main — Uniform affine refinement for every natural order

**Status: lean/general.** SimpleLowerBound n (baseline n) is proved for real lines at every n with standard logical axioms. The interpretation as complement components uses the manuscript's elementary sign-cell/topology bridge.

- [Kobon.Universal.baseline_sound, line 26](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L26)
- [Kobon.Universal.baseline_improvement, line 72](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L72)

### j:G — Closed formula for G

**Status: lean/general.** The definition handles n<3 and n=3; the stated floor formula is baseline_formula for n>=4. Natural division is floor division.

- [Kobon.Universal.baseline, line 11](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L11)
- [Kobon.Universal.baseline_formula, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L59)

### j:cell — Certified triangular interiors and disjointness

**Status: partial.** Under global NoParallel, Lean proves nonempty triangle interiors, equality with the strict sign cell, and pairwise disjointness. The manuscript's ordinary convexity and connected-component argument supplies the topological interpretation. The October wording uses the global nonparallel hypothesis rather than enlarging the Lean theorem.

- [Kobon.Cells.interior_nonempty, line 461](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Cells.lean#L461)
- [Kobon.Cells.interior_eq_signCell, line 486](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Cells.lean#L486)
- [Kobon.Cells.distinct_interiors_disjoint, line 453](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Cells.lean#L453)

### j:sign — Trigonometric determinant and oriented evaluation identities

**Status: lean/general.** Symbolic identities for arbitrary real angles.

- [Kobon.FurediPalasti.det_line, line 13](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalasti.lean#L13)
- [Kobon.FurediPalasti.oriented_line, line 123](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalasti.lean#L123)

### j:residues — Selected triples and classical affine count

**Status: lean/general.** The two sets of residue classes yield certified triangles and the classical count. No numerical novelty is claimed for the older half-phase construction.

- [Kobon.FurediPalasti.selected_triangle, line 186](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalasti.lean#L186)
- [Kobon.ShiftedFurediPalasti.selected_triangle, line 144](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/ShiftedFurediPalasti.lean#L144)
- [Kobon.FurediPalastiCount.ordered_bound, line 186](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalastiCount.lean#L186)
- [Kobon.FurediPalasti.lower_bound, line 301](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalasti.lean#L301)

### j:phase — Phase correction

**Status: lean/general.** Actual simple real arrangements for every n>=3 with floor(n(n-3)/3)+1 triangles; the repeated-index saving is separately proved.

- [Kobon.ShiftedFurediPalasti.simple_lower_bound, line 274](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/ShiftedFurediPalasti.lean#L274)
- [Kobon.ShiftedCount.ordered_bound_plus, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/ShiftedCount.lean#L59)

### j:covariance — Projective change of chart

**Status: lean/general.** Exact determinant/evaluation covariance and triangle preservation under the stated cut inequalities.

- [Kobon.Projective.det_transform, line 14](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Projective.lean#L14)
- [Kobon.Projective.eval_transform, line 19](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Projective.lean#L19)
- [Kobon.Projective.oriented_transform, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Projective.lean#L25)
- [Kobon.Projective.triangle_preserved, line 111](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Projective.lean#L111)
- [Kobon.Projective.triangle_preserved_negative, line 138](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Projective.lean#L138)

### j:caps — One-cap and two-cap constructions

**Status: lean/general.** The one-cap theorem uses n=2m+1 with m>=1. The two-cap theorem uses n=6k+3 with k>=1. Both construct simple real arrangements.

- [Kobon.FurediPalastiWrap.one_cap_simple_lower_bound, line 191](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalastiWrap.lean#L191)
- [Kobon.FurediPalastiTwoCaps.two_cap_simple_lower_bound, line 282](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalastiTwoCaps.lean#L282)

### j:gap — Exact gap to the classical comparison polynomial

**Status: lean/general.** Arithmetic identity only; this does not formalize the external upper-bound theorem or prove it unrestrictedly.

- [Kobon.Universal.polynomial_gap_exact, line 90](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L90)

### j:envelope — Finite-enhanced lower envelope

**Status: lean/general.** Universal.all_n proves max(G, AllN.bound); AllN.bound is max of the older baseline and a finite certified enhancement. Since G dominates the older baseline, this equals the paper's max(G, C). The identification of C with the external certificate catalog is checked by the manifest/catalog, rather than C being a directly parsed Lean definition. This theorem imports finite native_decide certificates and therefore has their additional runtime trust.

- [Kobon.Universal.all_n, line 117](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L117)
- [Kobon.Universal.classical_baseline_le, line 63](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L63)
- [Kobon.AllN.dominates_every_saved_certificate, line 255](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/AllN.lean#L255)

### j:after195 — Saved envelope equals G after order 195

**Status: lean/general.** Immediate combination of AllN.baseline_after_last_exception, Universal.classical_baseline_le and the definition Universal.bound; no separately named combined theorem. Does not assert optimality after 195.

- [Kobon.AllN.baseline_after_last_exception, line 465](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/AllN.lean#L465)
- [Kobon.Universal.classical_baseline_le, line 63](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L63)
- [Kobon.Universal.bound, line 112](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L112)

### j:44equality — Simple optimum K_s(44)=608

**Status: lean/derived.** The retained finite SimpleLowerBound 44 608 certificate and the now-formalized simple even upper theorem imply exact simple optimality by substitution 44*(2*44-5)/6=608. This is an immediate mathematical corollary of the linked Lean theorems; there is no separately named 44-line optimality wrapper. It makes no nonsimple optimality or first numerical priority claim.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L461)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### j:old-q-family — G supersedes the earlier q=6*2^t additional-line formula

**Status: manuscript.** The identity G(q+3)=q^2/3+q+2 follows by substitution into the verified formula; no dedicated theorem for this exact q-family identity was found. It is an arithmetic consequence, not a new formalized generic extension mechanism.

- [Kobon.Universal.baseline_formula, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L59)
- [Kobon.Universal.strict_odd_multiples, line 143](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L143)

### j:certificate-soundness — Integer certificate validation

**Status: lean/general.** Integer sign checks lift to real nonparallel lines and distinct uncut triangular support triples. Simplicity is separately checked. Finite checked instances use native_decide.

- [Kobon.validate_sound, line 135](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Geometry.lean#L135)
- [Kobon.validate_simple_sound, line 39](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Simple.lean#L39)

### jup:shared-fan — Six actual triangles with six distinct shared elementary radial sides

**Status: lean/finite.** The fixed six integer lines and six supporting triples are kernel-checked. Lean proves the lifted real triangles, distinct supporting triples, triple center, six distinct nonzero elementary radial segments, and that each radial segment is a side of two distinct triangles. This is a finite formal counterexample to a literal local bound of two incident shared sides, not to a global Kobon upper theorem. SharedFan does not separately enumerate all possible triangles or formalize the local classification d1=d2=3.

- [Kobon.SharedFan.integerLines, line 17](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L17)
- [Kobon.SharedFan.integer_triangles, line 27](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L27)
- [Kobon.SharedFan.real_triangles, line 32](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L32)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L51)
- [Kobon.SharedFan.adjacent_triangles_distinct, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L58)
- [Kobon.SharedFan.center_is_triple, line 61](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L61)
- [Kobon.SharedFan.radial_segments_injective, line 105](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L105)
- [Kobon.SharedFan.radial_elementary, line 113](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L113)

### j:finite — Table 1: selected simple certificates

**Status: lean/finite.** Each individual simple lower bound is proved through the finite certificate pipeline (native_decide). Improvements are relative to earlier project witnesses, not claims of first numerical priority or global optimality.

- [Kobon.Results.best_simple_028, line 429](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L429)
- [Kobon.Results.best_simple_030, line 433](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L433)
- [Kobon.Results.best_simple_034, line 441](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L441)
- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L461)
- [Kobon.Results.best_simple_039, line 451](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L451)
- [Kobon.Results.best_simple_047, line 467](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L467)
- [Kobon.Results.best_simple_048, line 469](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L469)
- [Kobon.Results.best_simple_051, line 475](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L475)
- [Kobon.Results.best_simple_053, line 479](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L479)
- [Kobon.Results.best_simple_054, line 481](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L481)
- [Kobon.Results.best_simple_055, line 483](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L483)
- [Kobon.Results.best_simple_059, line 491](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L491)
- [Kobon.Results.best_simple_060, line 493](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L493)
- [Kobon.Results.best_simple_099, line 503](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L503)
- [Kobon.Results.best_simple_195, line 513](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L513)

### j:finite-28 — Simple 28-line certificate with at least 238 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_028, line 429](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L429)

### j:finite-30 — Simple 30-line certificate with at least 275 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_030, line 433](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L433)

### j:finite-34 — Simple 34-line certificate with at least 357 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_034, line 441](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L441)

### j:finite-44 — Simple 44-line certificate with at least 608 cells

**Status: lean/finite.** Finite lower bound only; the optimum assertion additionally needs Blanc's external upper theorem. Uses native_decide.

- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L461)

### j:finite-39 — Simple 39-line certificate with at least 470 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_039, line 451](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L451)

### j:finite-47 — Simple 47-line certificate with at least 691 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_047, line 467](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L467)

### j:finite-48 — Simple 48-line certificate with at least 721 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_048, line 469](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L469)

### j:finite-51 — Simple 51-line certificate with at least 818 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_051, line 475](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L475)

### j:finite-53 — Simple 53-line certificate with at least 885 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_053, line 479](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L479)

### j:finite-54 — Simple 54-line certificate with at least 919 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_054, line 481](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L481)

### j:finite-55 — Simple 55-line certificate with at least 955 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_055, line 483](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L483)

### j:finite-59 — Simple 59-line certificate with at least 1103 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_059, line 491](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L491)

### j:finite-60 — Simple 60-line certificate with at least 1141 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_060, line 493](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L493)

### j:finite-99 — Simple 99-line certificate with at least 3170 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_099, line 503](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L503)

### j:finite-195 — Simple 195-line certificate with at least 12482 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_195, line 513](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Results.lean#L513)

### j:maiorana-inputs — Fifteen Maiorana 14-line certificates

**Status: lean/finite.** All fifteen imported coordinate identities have Lean lower-bound certificates (native_decide), each with 54 cells. Discovery credit remains Maiorana. This does not establish an unrestricted optimum.

- [Kobon.Certificates.N014T00054Hd47aea63.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hd47aea63.lean#L84)
- [Kobon.Certificates.N014T00054H18bbcff4.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H18bbcff4.lean#L84)
- [Kobon.Certificates.N014T00054H78f750c0.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H78f750c0.lean#L84)
- [Kobon.Certificates.N014T00054H912da8ec.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H912da8ec.lean#L84)
- [Kobon.Certificates.N014T00054H91349990.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H91349990.lean#L84)
- [Kobon.Certificates.N014T00054H9c871e10.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H9c871e10.lean#L84)
- [Kobon.Certificates.N014T00054Hb3dcae0b.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hb3dcae0b.lean#L84)
- [Kobon.Certificates.N014T00054H9219cdaa.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H9219cdaa.lean#L84)
- [Kobon.Certificates.N014T00054Hd2babc1b.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hd2babc1b.lean#L84)
- [Kobon.Certificates.N014T00054H2b34ca22.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H2b34ca22.lean#L84)
- [Kobon.Certificates.N014T00054Hfa427b3d.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hfa427b3d.lean#L84)
- [Kobon.Certificates.N014T00054H1ec1fd5c.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H1ec1fd5c.lean#L84)
- [Kobon.Certificates.N014T00054H3e5d182f.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H3e5d182f.lean#L84)
- [Kobon.Certificates.N014T00054H17f8c052.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H17f8c052.lean#L84)
- [Kobon.Certificates.N014T00054Hc472f972.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hc472f972.lean#L84)

### j:pu-gallery — Ten Parpalak-Utkin gallery witnesses

**Status: lean/finite.** Ten gallery coordinate identities have Lean lower-bound certificates (native_decide), including 26:204 and 50:792. Discovery credit remains the original authors. The separate complete recount uses independent exact programs.

- [Kobon.Certificates.N046T00667H32b8ca2f.lower_bound, line 729](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N046T00667H32b8ca2f.lean#L729)
- [Kobon.Certificates.N008T00015Ha1380810.lower_bound, line 39](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N008T00015Ha1380810.lean#L39)
- [Kobon.Certificates.N014T00054H10576514.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H10576514.lean#L84)
- [Kobon.Certificates.N020T00117H382171ac.lower_bound, line 153](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N020T00117H382171ac.lean#L153)
- [Kobon.Certificates.N026T00204Hf71379c4.lower_bound, line 246](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N026T00204Hf71379c4.lean#L246)
- [Kobon.Certificates.N032T00315H5914f2bb.lower_bound, line 363](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N032T00315H5914f2bb.lean#L363)
- [Kobon.Certificates.N036T00402Hce43a107.lower_bound, line 454](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N036T00402Hce43a107.lean#L454)
- [Kobon.Certificates.N038T00450H8ba2bdb1.lower_bound, line 504](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N038T00450H8ba2bdb1.lean#L504)
- [Kobon.Certificates.N042T00553H9849e255.lower_bound, line 611](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N042T00553H9849e255.lean#L611)
- [Kobon.Certificates.N050T00792H3d40cb58.lower_bound, line 858](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N050T00792H3d40cb58.lean#L858)

### jext:visible — Verified exterior realization

**Status: lean/general.** Actual real-coordinate simple arrangement with T plus the length of an explicit duplicate-free visible-pair list. Admissibility and beyond-all-vertices height are explicit geometric hypotheses. No parity restriction or future-count assumption.

- [Kobon.Exterior.extension, line 164](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Exterior.lean#L164)
- [Kobon.Exterior.safeHeight_beyond, line 191](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Exterior.lean#L191)

### jext:defect — Boundary-defect extension proposition

**Status: lean/general.** For each supplied SimpleLowerBound n T with n>=3, actual terminal-ray extraction proves a simple n+1 witness with the exact deficit-dependent gain g. The proof now discharges the former boundary and averaging interfaces end to end, uses standard axioms only, and permits indefinite both-parity iteration. The gain remains input-dependent.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.OpenMathExtensionFormula.closed_form_successor, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathExtensionFormula.lean#L56)
- [Kobon.OpenMathEveryOrderExtension.infinite_quantitative_extension, line 82](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathEveryOrderExtension.lean#L82)

### jext:gain — Both-parity defect gain formula

**Status: lean/general.** For n>=3 the exact gain is min(floor(n/2), ceil(max(3, max(0, n-delta))/2)), equal to ceil((n-1)max(3, max(0, n-delta))/(2n)). Actual simple geometry supplies the inputs; no boundary-count premise is assumed. The finite arithmetic and geometric successor are both fully checked with standard axioms.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.OpenMathExtensionFormula.stepGain_formula, line 50](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathExtensionFormula.lean#L50)
- [Kobon.OpenMathExtensionFormula.closed_form_successor, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathExtensionFormula.lean#L56)

### jext:odd-near-perfect — Odd inputs of defect at most two admit full gain

**Status: lean/general; inherited special examples.** For odd n>=3 every supplied simple witness with delta<=2 admits a successor gaining floor(n/2). The actual boundary extraction is now complete. The perfect case and known individual near-perfect examples retain BBL and Blanc attribution; this does not assert optimal odd seeds at every order.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.OpenMathBoundarySuccessor.odd_defect_two_successor, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathBoundarySuccessor.lean#L84)
- [Kobon.OpenMathOptimalSuccessor.optimal_odd_to_even, line 21](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathOptimalSuccessor.lean#L21)
- [Kobon.OpenMathOptimalSuccessor.even_optimality, line 38](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathOptimalSuccessor.lean#L38)

### jext:budget — Exterior wedge budget and obstruction to indefinite full gains

**Status: partial.** The resource inequality and cumulative geometric bound are manuscript proofs. Lean proves the contradiction conditional on the resource inequality and full gains; it does not extract the wedge budget from geometry.

- [Kobon.Iteration.no_infinite_full_gain_budget, line 105](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration.lean#L105)
- [Kobon.Iteration.two_steps_49_obstruction, line 121](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration.lean#L121)

### jext:figure — The 49-line seed successor chain and sector capacities

**Status: partial.** Exact coordinate-to-profile audit plus Lean finite cyclic profile maxima. The values 24, 23, 2, 2, 2 belong to these saved arrangements and are not upper bounds for the maximum function. The real-coordinate identification of the finite arrays is performed by the independent audit script, not Lean.

- [Kobon.Iteration49.profile_bound_49, line 13](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration49.lean#L13)
- [Kobon.Iteration49.profile_attains_49, line 16](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration49.lean#L16)
- [Kobon.Iteration49.profile_bound_50, line 21](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration49.lean#L21)
- [Kobon.Iteration49.profile_bound_51, line 29](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration49.lean#L29)
- [Kobon.Iteration49.profile_bound_52, line 37](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration49.lean#L37)
- [Kobon.Iteration49.profile_bound_53, line 45](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration49.lean#L45)
- [scripts/audit_successor_chain.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/scripts/audit_successor_chain.py#L1)
- [experiments/2026-09-20/successor-49/chain.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-20/successor-49/chain.json#L1)

### jext:conditional-iteration — Closed form conditional on the full successor recurrence

**Status: partial.** Fully proved arithmetic implication with FullStepClaim K visibly assumed. It does not establish that recurrence for the Kobon maximum function.

- [Kobon.Iteration.gainPrefix_closed, line 31](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration.lean#L31)
- [Kobon.Iteration.full_step_iteration, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration.lean#L59)
- [Kobon.Iteration.from_49_conditional, line 76](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Iteration.lean#L76)

### jext:49 — Unconditional 49-seed numerical target for all n at least 49

**Status: lean/general.** Unconditional real geometric lower bound floor((n-1)^2/4)+191, obtained from saved 49/50 certificates and the all-order classical baseline for n at least 51. It does not produce a nested full-gain chain.

- [Kobon.AllN.from_49_unconditional, line 504](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/AllN.lean#L504)
- [Kobon.Universal.dominates_49_target, line 125](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Universal.lean#L125)

### jfam:doubling — Verified one-step geometric BBL construction

**Status: lean/general.** One actual real-coordinate simple arrangement step for q=4r with r at least 5, positive small epsilon, saturated ordered tangent-grid input, positive central apex, and a duplicate-free certified triangle list. Produces SimpleLowerBound (2q+1) (T+q^2). Does not return the recursive compatible seed invariant, and does not include the initial q=10 step.

- [Kobon.BBLDoubling.doubling, line 15](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLDoubling.lean#L15)

### jfam:seed11 — Uniform real eleven-line seed and five-pair exterior extension

**Status: lean/general.** For every real 0<epsilon<=10^-5, actual simple real arrangement with 32 triangles, nine distinguished triangles, and five visible pairs; actual exterior arrangement with 12 lines and 37 triangles. These seed computations use kernel evaluation, with proved interval and trigonometric bounds.

- [Kobon.SeedFamily.simple_lower_bound, line 115](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SeedFamily.lean#L115)
- [Kobon.SeedFamily.distinguished_triangles, line 108](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SeedFamily.lean#L108)
- [Kobon.SeedFamily.arbitrarily_small, line 121](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SeedFamily.lean#L121)
- [Kobon.HybridBoundary.seed_visible, line 138](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/HybridBoundary.lean#L138)
- [Kobon.HybridBoundary.seed_exterior, line 148](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/HybridBoundary.lean#L148)

### jfam:families — Completed odd and stronger even q=10*2^t geometric families

**Status: lean/general.** For every natural t, q=10*2^t gives actual simple real-line witnesses of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. All geometric seed and visibility hypotheses are discharged. At each finite depth the proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even families inherit four/six existing native checks, respectively. BBL doubling is inherited; the completed recursive formalization is not a new numerical-record claim.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L51)

### jfam:strong-even — Stronger even family T_q+q/2

**Status: lean/general.** For every natural t, q=10*2^t gives actual simple real-line witnesses of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. All geometric seed and visibility hypotheses are discharged. At each finite depth the proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even families inherit four/six existing native checks, respectively. BBL doubling is inherited; the completed recursive formalization is not a new numerical-record claim.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L51)

### jfam:seed21 — Uniform real 21-line true-grid seed

**Status: lean/general.** For every real 0<epsilon<=10^-5, the verified parameter arrangement has 132 certified triangles, 19 distinguished triangles, and 10 visible pairs; exterior extension yields 22:142. Finite interval checks in this module use native_decide, so compiler/runtime trust supplements the Lean kernel.

- [Kobon.BBLSeed21.simple_lower_bound, line 163](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21.lean#L163)
- [Kobon.BBLSeed21.all_distinguished, line 108](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21.lean#L108)
- [Kobon.BBLSeed21.distinguished_count, line 115](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21.lean#L115)
- [Kobon.BBLSeed21.all_visible, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21.lean#L100)
- [Kobon.BBLSeed21.exterior_lower_bound, line 168](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21.lean#L168)
- [Kobon.BBLSeed21.arbitrarily_small, line 179](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21.lean#L179)

### jfam:recursive-components — Next-grid saturation and sorting permutation

**Status: lean/general.** The recursive seed record now closes under actual geometric doubling, including the grid, saturation, positive apex, simplicity, triangle-list transport and exterior visibility. The generic theorems retain an explicit uniform seed premise; the concrete 21-line seed discharges it.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLRecursiveSeed.seed_step, line 61](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveSeed.lean#L61)
- [Kobon.BBLEvenRecursive.visible_seed_step, line 9](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenRecursive.lean#L9)
- [Kobon.BBLInfinite.uniform_iterate, line 32](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L32)
- [Kobon.BBLEvenInfinite.uniform_iterate, line 27](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenInfinite.lean#L27)

### jfam:seed5 — Corrected uniform five-line normalization

**Status: lean/general.** For every real 0<epsilon<=10^-5, five triangles, three distinguished triangles, two visible pairs, and exterior extension to 6:7 are proved; this does not itself formalize the whole inherited dyadic optimal family.

- [Kobon.TamuraSeed5.simple_lower_bound, line 113](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/TamuraSeed5.lean#L113)
- [Kobon.TamuraSeed5.all_distinguished, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/TamuraSeed5.lean#L59)
- [Kobon.TamuraSeed5.all_visible, line 64](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/TamuraSeed5.lean#L64)
- [Kobon.TamuraSeed5.exterior_lower_bound, line 118](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/TamuraSeed5.lean#L118)
- [Kobon.TamuraSeed5.arbitrarily_small, line 129](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/TamuraSeed5.lean#L129)

### jfam:large-completed — 321:34132, 322:34292 and 641:136532

**Status: lean/general + computation.** The numerical lower bounds 321:34132, 322:34292 and 641:136532 are now consequences of the complete infinite Lean families. The previously saved coordinate files independently passed two external exact counters, but are not thereby retroactively included in the finite Lean certificate catalog.

Previous map status: `computation`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L51)
- [experiments/2026-09-21/hybrid-family/larger-members-verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/hybrid-family/larger-members-verification.json#L1)

### jfam:large-incomplete — 642:136852 existence proved; old individual coordinate verification remains separate

**Status: lean/general + pending-coordinate-check.** The existence of a simple 642-line arrangement with 136852 triangles is now proved by the infinite even family. The earlier saved 642-line coordinate file's unfinished second counter remains unfinished; the existence theorem does not certify that particular file.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L51)
- [experiments/2026-09-21/hybrid-family/large-run-status.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/hybrid-family/large-run-status.json#L1)

### jfam:chart-obstruction — Fixed 81- and 161-line seeds admit no chart-only count improvement

**Status: computation.** Exact projective face census equals bounded triangle count for these particular saved seeds. This is a finite exact program calculation, not a Lean theorem or a restriction on other arrangements of the same size.

- [experiments/2026-09-20/chart_search.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-20/chart_search.py#L1)
- [research/kobon-hybrid/certificates/n081.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/kobon-hybrid/certificates/n081.json#L1)
- [research/kobon-hybrid/certificates/n161.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/kobon-hybrid/certificates/n161.json#L1)

### jfam:seed19 — Parpalak-Utkin 19-line interval seed reproduction

**Status: computation.** Exact interval calculation for 107 triangles and 17 distinguished triangles for 0<epsilon<=10^-3. The uniform interval calculation is not a Lean theorem. A single rational specialization is separately in the finite Lean catalogue; attribution to Parpalak-Utkin remains.

- [research/six-hour-2026-09-21/general-bounds/prior-seed19-interval.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/prior-seed19-interval.json#L1)
- [research/six-hour-2026-09-21/general-bounds/prior-seed19-rational.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/prior-seed19-rational.json#L1)

### jfam:inherited-families — q=4*2^t and q=18*2^t inherited odd families and even companions

**Status: external + completed Lean tails.** The full q=4*2^s and q=18*2^s odd numerical series retain Forge--Ramirez Alfonsin and Parpalak--Utkin attribution. Their compatible33/37-line tails now have complete Lean odd/even family and simple-optimality theorems. The generic actual optimal odd-to-even theorem supplies the companion from any supplied rounded-optimal simple odd witness; the whole published series from its smallest seed is not relabeled as a separately formalized current family theorem.

Previous map status: `external`. The new scope above controls the October claim.

- [Kobon.OpenMathConstructionForgeFamily.odd_family, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L25)
- [Kobon.OpenMathConstructionForgeFamily.even_family, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L28)
- [Kobon.OpenMathConstructionFamily37.odd_family, line 54](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L54)
- [Kobon.OpenMathConstructionFamily37.even_family, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L58)
- [Kobon.OpenMathOptimalSuccessor.optimal_odd_to_even, line 21](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathOptimalSuccessor.lean#L21)

### jfam:finite-11 — 11:32 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N011T00032Hb955e7c9.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N011T00032Hb955e7c9.lean#L10)

### jfam:finite-12 — 12:37 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N012T00037H8c718a33.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N012T00037H8c718a33.lean#L10)

### jfam:finite-21 — 21:132 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N021T00132H3d8bae2f.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N021T00132H3d8bae2f.lean#L10)

### jfam:finite-22 — 22:142 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N022T00142He683945e.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N022T00142He683945e.lean#L10)

### jfam:finite-41 — 41:532 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N041T00532H6d48a341.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N041T00532H6d48a341.lean#L10)

### jfam:finite-42 — 42:552 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N042T00552H7b29a6bd.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N042T00552H7b29a6bd.lean#L10)

### jfam:finite-81 — 81:2132 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N081T02132H7bc6b303.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N081T02132H7bc6b303.lean#L10)

### jfam:finite-82 — 82:2172 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N082T02172Hd75c9101.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N082T02172Hd75c9101.lean#L10)

### jfam:finite-161 — 161:8532 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N161T08532H230691d5.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N161T08532H230691d5.lean#L10)

### jfam:finite-162 — 162:8612 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N162T08612H1512e696.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N162T08612H1512e696.lean#L10)

### jup:section — Scope of multiplicity-sensitive upper estimates

**Status: lean/general + scoped ordinary arguments.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. All numbered structural endpoints use actual extracted inventories. Simple, all-triple, parity, degree and component-size hypotheses are retained where stated. The surviving corrections prevent an unrestricted improved numerical formula. Historical smoothing classification and remaining equality analysis keep their ordinary-proof tiers.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon/UpperOpenMathGlobalFans.lean, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L1)
- [Kobon/UpperOpenMathMixedCurvatureBound.lean, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCurvatureBound.lean#L1)

### jup:identity — Elementary-segment incidence and defect identities

**Status: lean/general.** For n>=2 pairwise nonparallel actual real lines and any finite injective certified triangle family, Lean extracts the actual vertices, bounded elementary segments, shared endpoints and multiplicities, and proves E=n(n-2)-S, 3T=E-U+D1+D2 and delta=S+U-D1-D2. Unused/shared are relative to the selected family, which need not enumerate all triangular cells. No global incidence identity is assumed.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon.UpperEdgeInventory.edge_cardinality, line 188](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeInventory.lean#L188)
- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeInventory.lean#L345)
- [Kobon.UpperTriangleIncidence.certificate_incidence, line 230](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTriangleIncidence.lean#L230)
- [Kobon.UpperSharedEdge.Pair.not_both_endpoints_ordinary, line 98](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSharedEdge.lean#L98)

### jup:clean — Clean-line parity and charging inequality

**Status: lean/general.** For even n>=4, NoParallel and an injective selected certificate, the actual clean-line budget n-h<=2U+D1 has a fully extracted charge map and finite fibers. This is distinct from the newly completed exterior terminal-ray successor, which also has a full actual proof.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCharging.lean#L100)
- [Kobon.UpperCleanCover.certificate_clean_line_charge, line 401](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCover.lean#L401)

### jup:budget — Combined clean-line defect budget

**Status: lean/derived.** The actual defect identity and clean-line charging yield 2delta>=n+2S-h-3D1-2D2 by algebra. Whole-arrangement fans are now extracted in the new library and supply the further structural estimates. This row records the combined budget itself, not an unrestricted numerical upper formula.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.CleanLineBudget.parity_budget, line 18](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/CleanLineBudget.lean#L18)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)
- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeInventory.lean#L345)
- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCharging.lean#L100)

### jup:parallel-obstruction — Why simply excluding parallel-participating lines does not repair charging

**Status: manuscript.** The three-parallel-verticals plus one-horizontal example shows that the horizontal line can be clean while all transverse pieces at its crossings are unbounded. This is a direct geometric counterexample to the attempted local argument with that weakened hypothesis, not a claimed counterexample to Blanc's theorem.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:fan — Fan bounds at an r-fold point

**Status: lean/conditional-interface + actual-extraction.** The retained local Sectors inequalities keep their explicit interfaces. The new actual radial-chart and shared-side matching library supplies their arrangement-level instances for the structural results below; the former missing global assembly is no longer the frontier. This does not identify every old proposed aggregate bound with a new theorem.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperFan.Sectors.ordinary_shared_card_le, line 166](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L166)
- [Kobon.UpperFan.Sectors.core_shared_card_eq_three_of_extremal, line 187](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L187)
- [Kobon.UpperFan.Sectors.ordinary_shared_card_le_of_core_le_two, line 202](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L202)
- [Kobon.UpperFan.Sectors.weighted_local_bound, line 227](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L227)
- [Kobon/UpperOpenMathTripleCharts.lean, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathTripleCharts.lean#L1)

### jup:fan-propagation — Opposite-support propagation along an actual geometric fan

**Status: lean/general.** At an ordinary radial endpoint, any two other indexed incident lines coincide. For a FanStrip of actual real points and indexed supporting lines, all opposite supporting lines agree and the two outer endpoints cannot lie on opposite rays from the center. No aggregate run-bound conclusion is assumed. The input FanStrip explicitly supplies incidences, ordinary internal endpoints, nondegenerate triangles and opposite lines avoiding the center.

- [Kobon.FanGeometry.ordinary_nonradial_unique, line 24](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanGeometry.lean#L24)
- [Kobon.FanGeometry.FanStrip, line 47](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanGeometry.lean#L47)
- [Kobon.FanGeometry.FanStrip.ofTriangles, line 65](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanGeometry.lean#L65)
- [Kobon.FanGeometry.FanStrip.all_opposites_eq, line 113](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanGeometry.lean#L113)
- [Kobon.FanGeometry.no_opposite_end_fan, line 160](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanGeometry.lean#L160)

### jup:fan-local-count — Actual cyclic fan has no long selected run and at most 2r-3 selected rays

**Status: lean/general.** For r>=3 and Geometry n r L, no r-1 consecutive selected ordinary shared rays can occur, and selected.card<=2*r-3. Geometry supplies 2r actual radial endpoints with antipodal partners, ordinary selected endpoints and the actual opposite supporting lines of adjacent triangular sectors. The no-long-run property is proved, not assumed; automatic construction of Geometry from a whole arrangement is not in these declarations.

- [Kobon.CyclicFan.Geometry, line 20](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/CyclicFan.lean#L20)
- [Kobon.CyclicFan.Geometry.no_long_run, line 44](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/CyclicFan.lean#L44)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/CyclicFan.lean#L96)

### jup:fan-window — Cyclic window count used in the fan proof

**Status: lean/general.** For a Finset S in ZMod(2*r), r>=3, and an explicit missing selected ray in every window of length r-1, ordinary_shared_ray_bound proves S.card<=2*r-3. Its proof establishes the intermediate double-count inequality (r-1)*S.card<=2*r*(r-2). The intermediate inequality is not separately named, but window_bound is a named helper. CyclicFan supplies the run premise from actual geometry.

- [Kobon.FanCount.window_bound, line 18](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanCount.lean#L18)
- [Kobon.FanCount.ordinary_shared_ray_bound, line 37](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FanCount.lean#L37)
- [Kobon.CyclicFan.Geometry.no_long_run, line 44](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/CyclicFan.lean#L44)

### jup:fan-sharp — Sharper actual local fan theorem for at most two core-ended shared rays

**Status: lean/conditional-interface + actual-extraction.** The local sharper fan inequality d2<=2 implies d1<=2r-4 remains fully checked. Actual fan extraction and occurrence matching are now completed in the structural library. This row retains the local theorem's exact interface rather than asserting an unstated numerical upper bound.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon.UpperFan.Sectors.ordinary_shared_card_le_of_core_le_two, line 202](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L202)
- [Kobon/UpperOpenMathFullTripleChart.lean, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathFullTripleChart.lean#L1)

### jup:upper — Restricted upper-estimate theorem

**Status: lean/general.** For even n>=4, NoParallel and an injective selected triangle certificate, actual global fans and boundary budgets prove the retained weighted estimate and the at-most-two/three-core upper bounds. In particular6T<=n(2n-5)+6 when q<=2 and 6T<=n(2n-5)+12 when q<=3. No abstract fan, boundary or incidence premise remains.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperOpenMathGlobalFans.certificate_defect_even, line 204](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L204)
- [Kobon.UpperOpenMathBoundaryBudgets.certificate_two_core_upper, line 137](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathBoundaryBudgets.lean#L137)
- [Kobon.UpperOpenMathBoundaryBudgets.certificate_three_core_upper, line 128](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathBoundaryBudgets.lean#L128)

### jup:weighted — Weighted defect inequality for arbitrary core size

**Status: lean/derived.** For even n>=4 actual NoParallel certificates, the completed global fan budget implies 2delta>=n+sum_(r>=3)(2r^2-11r+6)t_r. The underlying extracted theorem is stronger and retains exceptional-core/shared-core corrections; dropping nonnegative improvements recovers this old weight. No supplied aggregate geometry remains.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperOpenMathGlobalFans.certificate_defect_even, line 204](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L204)

### jup:two-core — At most two finite multiple points: upper polynomial plus one

**Status: lean/general.** For even n>=4 actual NoParallel certificates with at most two cores, 6T<=n(2n-5)+6, giving the displayed floor upper bound. Core multiplicities are arbitrary. Actual boundary support, local fans, core paths and parity rounding are discharged in Lean.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperOpenMathBoundaryBudgets.certificate_two_core_upper, line 137](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathBoundaryBudgets.lean#L137)

### jup:zero-one-core — Sharper zero-core and one-core defects

**Status: lean/derived.** For even n>=4 actual NoParallel certificates, q=0 gives delta>=n/2 and q=1 gives delta>=n/2-1, including a single core of arbitrary multiplicity. Substitute q and D2=0 into the extracted three-core defect theorem and use integer parity. These are immediate corollaries; no separately named general one-core wrapper is asserted.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperOpenMathBoundaryBudgets.certificate_three_core_defect, line 116](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathBoundaryBudgets.lean#L116)

### jup:high-multiplicity — Simple-style polynomial under nonnegative total core weight

**Status: lean/general + derived retained comparison.** For even n>=4 NoParallel certificates with every core multiplicity at least five, the actual boundary-sensitive theorem gives a penalized bound stronger than the old T<=floor(n(n-5/2)/3) comparison. The multiplicity hypothesis is essential; triple and quadruple weights cannot be treated as nonnegative.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperOpenMathBoundaryBudgets.certificate_even_high_five, line 156](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathBoundaryBudgets.lean#L156)

### jup:attainment — Externally attributed exact attainment at 8, 14, 26 and 50 lines

**Status: partial.** The lower witnesses 8:15, 14:54, 26:204 and 50:792 are Lean-certified finite lower bounds. Their exact full triangle counts, nonparallel status and exactly two triple points are documented by exact computational censuses; the generic lower_bound declarations do not assert upper bounds or core cardinalities. The 14-line example must be Maiorana certificate-01 (or another two-triple Maiorana example), NOT the PU gallery 14-line witness, which has five triple points. Equality with the restricted manuscript upper theorem proves sharpness only in its stated subclass. Discovery attributions remain external.

- [Kobon.Certificates.N008T00015Ha1380810.lower_bound, line 39](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N008T00015Ha1380810.lean#L39)
- [Kobon.Certificates.N014T00054Hd47aea63.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hd47aea63.lean#L84)
- [Kobon.Certificates.N026T00204Hf71379c4.lower_bound, line 246](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N026T00204Hf71379c4.lean#L246)
- [Kobon.Certificates.N050T00792H3d40cb58.lower_bound, line 858](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N050T00792H3d40cb58.lean#L858)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/verification.json#L1)
- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/verification.json#L1)

### jup:figure — Shared-fan figure and geometric certificate

**Status: lean/finite.** The six depicted cells have nonempty, uncut and pairwise disjoint open interiors in Lean; each highlighted radial segment is elementary and shared by the appropriate two cells. The caption's formal claim is supported in this constructive sense. Exhaustivity of the complete triangle census and the endpoint-type count d1=d2=3 are exact computational additions, not named SharedFan theorems.

- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L51)
- [Kobon.SharedFan.interiors_uncut, line 66](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L66)
- [Kobon.SharedFan.interiors_nonempty, line 70](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L70)
- [Kobon.SharedFan.interiors_disjoint, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L73)
- [Kobon.SharedFan.radial_elementary, line 113](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L113)
- [research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json#L1)

### jup:shared-fan-census — Exact shared-fan census and endpoint types

**Status: computation.** The exact arrangement counter finds exactly six triangular cells, four triple points, and at the center (1, 1) six incident shared segments split as d1=3 and d2=3. This complete census is reproducible from the six coordinates; it is not an exhaustive-count theorem in SharedFan. The six certified cells and elementary sides themselves are formally established.

- [research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json#L1)
- [experiments/2026-09-21/general-bounds/shared_fan_counterexample.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/general-bounds/shared_fan_counterexample.py#L1)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L51)

### jup:clement-reading — Scope of the Clément–Bader wording objection

**Status: external.** The recorded source audit identifies page 2, Lemma 1 item 3 of the OEIS-hosted Clément–Bader draft. The six-side example refutes only a literal local incidence reading; it neither disproves the draft's final theorem nor rules out a corrected global assignment argument. This bibliographical/interpretive claim is not a Lean theorem.

- [research/six-hour-2026-09-21/general-bounds/upper-bound-scope-audit.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/upper-bound-scope-audit.md#L1)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SharedFan.lean#L51)

### jup:smoothing-maiorana — Four exact local resolutions of Maiorana's 14:54 witness

**Status: computation.** Maiorana certificate-01 has precisely the two zero triple determinants on supports {0, 4, 10} and {0, 11, 12}. The independent offsets realize all four resolution-sign choices, preserve every initially nonzero triple-determinant sign and leave pair directions fixed; exact triangle counts are 52, 52, 53, 52. The script checks each resolution by adjacency and the independent interior-sign verifier. This finite enumeration is not a Lean theorem.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)
- [experiments/2026-09-21/general-bounds/maiorana_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/general-bounds/maiorana_resolutions.py#L1)

### jup:smoothing-classification — Exhaustion of sufficiently small simple perturbations

**Status: manuscript.** Finite continuity preserves all initially nonzero pair-direction and triple-determinant signs. The two formerly zero triple signs exhaust the possible nearby simple chirotopes, all represented in the exact enumeration; hence every sufficiently small simple perturbation of this fixed 14-line input has at most 53 triangular cells. The sign-stability/classification argument is ordinary geometry, not Lean, and makes no statement about distant arrangements.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [experiments/2026-09-21/general-bounds/maiorana_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/general-bounds/maiorana_resolutions.py#L1)

### jup:smoothing-gallery — All 132 recorded local resolutions of seven gallery inputs

**Status: computation.** The saved exact reports contain 4+32+64+4+16+8+4=132 resolutions for n=8, 14, 20, 26, 32, 38, 50. Their maxima are respectively 14, 51, 114, 203, 313, 448, 791. Private-line offsets realize every binary local choice; the verifier checks all originally nonzero determinant signs, simplicity and equality of the two exact triangle sets. These are fixed-input computations, not a formalized general smoothing theorem or an upper bound on arbitrary simple arrangements.

- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/collinear-resolution-model.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/collinear-resolution-model.json#L1)
- [experiments/2026-09-21/general-bounds/collinear_resolution.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/general-bounds/collinear_resolution.py#L1)
- [experiments/2026-09-21/general-bounds/check_collinear_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/experiments/2026-09-21/general-bounds/check_collinear_resolutions.py#L1)

### jup:smoothing-loss — Failure of nondecreasing and loss-at-most-one local smoothing shortcuts

**Status: computation.** For the fixed Maiorana input the best nearby simple count drops from 54 to 53, ruling out universal nondecreasing local smoothing. For the PU gallery 14- and 20-line types the exact local maxima drop by three, and at 32 and 38 by two, ruling out universal loss-at-most-one local resolution. Transfer from exhaustive sign choices to all sufficiently small perturbations uses the stated manuscript continuity argument; no global lower or upper optimum is changed.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)

### jup:formalization-status — Boundary between completed formal components and remaining global geometry

**Status: lean/general + research-frontier.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Canonical radial fans, occurrence matching, component partitions, marked-port charging and finite geometric escape are now extracted in Lean. The completed structural bounds retain their class conditions and correction counts. Removing the residual one-cap correction or proving the proposed global even token trade-off remains open; no new unrestricted numerical upper formula is claimed.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperOpenMathMixedCurvatureBound.certificate_mixed_curvature_component_bound, line 41](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCurvatureBound.lean#L41)
- [Kobon.UpperOpenMathM22Curvature.certificate_m22_source_free_defect_bound, line 117](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathM22Curvature.lean#L117)

### j:trig — Classical trigonometric line family

**Status: lean/general.** This is the definition used in the formal construction, inherited from Furedi-Palasti rather than a new family.

- [Kobon.FurediPalasti.line, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/FurediPalasti.lean#L10)

### j:blanc — Blanc's simple even-order upper bound

**Status: lean/general; inherited theorem.** The classical simple even bound T<=floor(n(2n-5)/6) is now proved from actual geometry for every SimpleLowerBound witness of even n>=4. Blanc's prior mathematical result remains attributed; this release adds its complete formalization. The simplicity hypothesis is essential.

Previous map status: `external`. The new scope above controls the October claim.

- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_upper, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L56)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### jfam:recursive — Closed geometric recursive seed and visibility invariants

**Status: lean/general.** For every natural t, q=10*2^t gives actual simple real-line witnesses of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. All geometric seed and visibility hypotheses are discharged. At each finite depth the proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even families inherit four/six existing native checks, respectively. BBL doubling is inherited; the completed recursive formalization is not a new numerical-record claim.

- [Kobon.BBLRecursiveSeed.seed_step, line 61](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveSeed.lean#L61)
- [Kobon.BBLEvenRecursive.visible_seed_step, line 9](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenRecursive.lean#L9)
- [Kobon.BBLInfinite.uniform_iterate, line 32](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L32)
- [Kobon.BBLInfinite.infinite_family, line 46](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L46)
- [Kobon.BBLInfinite.triangleCount_identity, line 52](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L52)
- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L51)

### jfam:windows — Actual one-triangle optimality windows for simple arrangements

**Status: lean/general.** For each q=10*2^t both family counts are attainable in simple arrangements, and every SimpleLowerBound witness at the same order has at most the constructed count plus one. Upper halves use only standard axioms; existence inherits the recorded native checks. The window is specific to simple arrangements and need not mean that exact optimum is unknown at every small order.

- [Kobon.BBLFamilyOptimality.odd_window, line 29](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyOptimality.lean#L29)
- [Kobon.BBLFamilyOptimality.even_window, line 35](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyOptimality.lean#L35)

### j:new-envelope — All-natural-order envelope retaining the completed recursive families

**Status: lean/general.** The October7 construction portfolio is a LowerBound at every natural order, retains the previous RecursiveEnvelope pointwise, and adds the 33/37/49/61 candidates over0<=t<=n. The former ten-dyadic strict-tail comparison remains proved and retained. New61 gains are stated against G or the preserved28-pair family; no blanket strict comparison with all preceding candidates or all literature is inferred.

- [Kobon.RecursiveEnvelope.all_n, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L51)
- [Kobon.RecursiveEnvelope.previous_le, line 57](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L57)
- [Kobon.RecursiveEnvelope.strict_previous_tail, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L73)
- [Kobon.OpenMathConstructionEnvelope.all_n, line 97](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L97)
- [Kobon.OpenMathConstructionEnvelope.previous_le, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L100)
- [Kobon.OpenMathConstructionEnvelope.bound, line 94](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L94)

### j:new-envelope-formula — Executable formula for the retained recursive envelope

**Status: lean/general.** Definitions candidate, familyBound and bound implement the displayed finite maximum; the two sparse branches select q+1 and q+2 respectively, and all other candidates are zero.

- [Kobon.RecursiveEnvelope.candidate, line 12](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L12)
- [Kobon.RecursiveEnvelope.familyBound, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L25)
- [Kobon.RecursiveEnvelope.bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L49)

### j:new-gains — Exact recursive improvements over G and the previous envelope

**Status: lean/general.** At q=10*2^t the odd/even family gains over G are respectively floor(q/3)-2 and q/2-floor(q/3)-2. B=G above 195; strict improvements hold for both tails t>=5. At321/322 gains are104/52, and at 641/642 they are211/105.

- [Kobon.BBLFamilyBenchmarks.odd_baseline_gain, line 52](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L52)
- [Kobon.BBLFamilyBenchmarks.even_baseline_gain, line 65](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L65)
- [Kobon.BBLFamilyBenchmarks.strict_previous_tail, line 152](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L152)

### long:envelope-gains — Exact gains of the new total envelope on its sparse tail

**Status: lean/derived.** Above order 195 the former envelope is G. The family-minus-G equalities and uniqueness of the matching sparse branch give the displayed exact H-minus-previous values. The repository proves the family differences and strict-tail comparison directly; no separate Lean wrapper for every exact H equality is asserted.

- [Kobon.BBLFamilyBenchmarks.odd_baseline_gain, line 52](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L52)
- [Kobon.BBLFamilyBenchmarks.even_baseline_gain, line 65](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L65)
- [Kobon.BBLFamilyBenchmarks.strict_previous_tail, line 152](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L152)
- [Kobon.RecursiveEnvelope.bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L49)
- [Kobon.RecursiveEnvelope.strict_previous_tail, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L73)

### jup:simple — Classical simple upper bounds extracted from actual geometry

**Status: lean/general.** Every SimpleLowerBound n T obeys 3T<=n(n-2) for n>=2; for even n>=4 it obeys 6T<=n(2n-5). Both conclusions and floor forms are kernel proofs. These formalize inherited simple-arrangement results, not new unrestricted upper bounds.

- [Kobon.UpperSimpleOptimality.simple_lower_bound_upper, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSimpleOptimality.lean#L58)
- [Kobon.UpperSimpleOptimality.simple_lower_bound_floor, line 70](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSimpleOptimality.lean#L70)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_upper, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L56)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### j:obstruction — Exact ten-sign impossibility on the 20-intercept tangent grid

**Status: lean/general.** One explicitly listed ten-sign orientation system is impossible for actual tangents and arbitrary real reciprocal slopes, for every real epsilon. The proof derives the quartic of tan(pi/20), identifies all required tangent values, and uses positive linear dependence. It does not classify all perfect21-line arrangements or imply K(21)<=132.

- [Kobon.BBLGridObstruction.actual_grid_orientation_impossible, line 263](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLGridObstruction.lean#L263)
- [Kobon.BBLGridObstruction.actual_grid_infeasible, line 240](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLGridObstruction.lean#L240)
- [Kobon.BBLTangentAlgebra.tan_quartic, line 20](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentAlgebra.lean#L20)
- [Kobon.BBLTangentAlgebra.tan_root_interval, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentAlgebra.lean#L51)
- [Kobon.StrictLinearCertificate.infeasible, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/StrictLinearCertificate.lean#L25)

### oct:grid21-coverage — Complete supplied affine-input obstruction audit

**Status: computation + external-input.** 3765 exact polynomial certificates and 15060 reflected/reoriented variants cover236 supplied Euclidean classes times21 distinguished supports=4956 normalizations, with no missing cases, for 0<epsilon<1/2000000. The checker independently validates signs and coverage for these inputs. Completeness of Parpalak-Utkin's classification is an external attributed premise, neither rerun nor formalized in Lean. The earlier18 projective representatives alone did not establish full affine coverage.

- [research/three-hour-2026-10-02/constructions/grid21-obstruction/README.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/three-hour-2026-10-02/constructions/grid21-obstruction/README.md#L1)
- [research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-verification.json#L1)

### oct:local-robustness — Ten-sign obstruction persists under small intercept perturbations

**Status: computation.** Exact outward interval elimination certifies independent perturbations of radius 1/1000 on the 11 used intercepts of the explicit representative. This robustness calculation is external and is not an all-grid or all-arrangement obstruction.

- [research/three-hour-2026-10-02/bbl/LOCAL_ROBUSTNESS.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/three-hour-2026-10-02/bbl/LOCAL_ROBUSTNESS.md#L1)

### j:exact49 — Uniform49-line compatibility certificate and its proof boundary

**Status: lean/general; inherited numerical family.** The actual-tangent 49-line uniform seed, simplicity, all 767 listed triangles, axis caps and 24 visible pairs now feed a complete infinite odd/even geometric family. At q=48*2^t the counts are 768*4^t-1 and that count plus24*2^t, attaining the classical simple-model floors. The orbit is a tail of prior BBL constructions, not a new numerical family. Exact finite native roots remain disclosed in the library audit.

- [Kobon.BBL49VerifiedFamilies.seed49_uniform, line 18](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L18)
- [Kobon.BBL49VerifiedFamilies.seed49_visible_uniform, line 41](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L41)
- [Kobon.BBL49VerifiedFamilies.odd_family, line 36](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L36)
- [Kobon.BBL49VerifiedFamilies.even_family, line 48](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L48)
- [Kobon.BBL49VerifiedFamilies.odd_exact, line 82](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L82)
- [Kobon.BBL49VerifiedFamilies.even_exact, line 95](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L95)

### oct:forge33 — Forge-family formulas with the33-line seed still explicit

**Status: lean/general; inherited numerical family.** The archived compatible 33-line seed is now completed and iterated. For q=32*2^t, the odd count is (1024*4^t-1)/3 and the even count adds16*2^t; both are optimal in the simple model. These are the known Forge--Ramirez Alfonsin numerical orbit. The advance is exact compatible certification and its formal recursion, with finite native checks explicitly distinguished from standard structural proofs.

- [Kobon.OpenMathConstructionForgeFamily.uniform_seed, line 14](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L14)
- [Kobon.OpenMathConstructionForgeFamily.uniform_visible_seed, line 19](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L19)
- [Kobon.OpenMathConstructionForgeFamily.odd_family, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L25)
- [Kobon.OpenMathConstructionForgeFamily.even_family, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L28)
- [Kobon.OpenMathConstructionForgeFamily.odd_optimal_in_simple_arrangements, line 33](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L33)
- [Kobon.OpenMathConstructionForgeFamily.even_optimal_in_simple_arrangements, line 42](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L42)

### jup:sharp-fan — Rigid extremal local fans and the strengthened weighted inequality

**Status: lean/general + retained local interface.** Canonical actual radial fans supply the retained Sectors extremal theorem: a=2r-3 forces all sectors triangular and d=3, and 3a+d<=6r-8+2e. The new actual summation matches all original triangle occurrences; no whole-arrangement extraction gap remains for these structural bounds.

- [Kobon.UpperFan.Sectors.all_sectors_of_extremal, line 171](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L171)
- [Kobon.UpperFan.Sectors.core_shared_card_eq_three_of_extremal, line 187](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L187)
- [Kobon.UpperFan.Sectors.ordinary_shared_card_le_of_core_le_two, line 202](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L202)
- [Kobon.UpperFan.Sectors.weighted_local_bound, line 227](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L227)
- [Kobon.UpperOpenMathGlobalFans.certificate_weighted_fan_sum, line 78](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L78)

### oct:triple-fan — Matched extremal triple fans cannot be adjacent

**Status: lean/conditional-interface.** Actual full triple fans are incompatible under the explicit shared-edge matching hypotheses. The canonical global matching and rotation interface remains to be extracted.

- [Kobon.UpperTripleFan.extremal_triple_fans_not_adjacent, line 156](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTripleFan.lean#L156)
- [Kobon.UpperTripleFan.incompatible_full_triple_fans, line 65](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTripleFan.lean#L65)

### oct:core-budget — Stronger conditional weighted and at-most-three-core budgets

**Status: lean/general + retained conditional arithmetic.** The formerly conditional aggregate inequality now has an actual counterpart in GlobalFans. The completed BoundaryBudgets theorem proves6T<=n(2n-5)+12 for even n>=4 and q<=3. The old arithmetic interfaces remain preserved as implications; actual geometry now discharges their appropriate stronger endpoint hypotheses.

- [Kobon.UpperOpenMathGlobalFans.certificate_defect_even, line 204](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L204)
- [Kobon.UpperOpenMathBoundaryBudgets.certificate_three_core_upper, line 128](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathBoundaryBudgets.lean#L128)

### oct:next-proof-plan — Unformalized next-step deductions and research obligations

**Status: lean/derived with explicit exceptional-triple condition.** The earlier next-step graph deductions now follow from completed actual cap-heavy triple independence and incidence. If every exceptional full fan is triple, then 3e<=D2; substituting into the actual even global budget yields 2delta>=n+2S-7I+8q+e and 6delta>=3n+6S-21I+24q+D2. These are immediate mathematical corollaries, not separately named Lean wrappers. Higher-order extremal fans are not asserted independent; the condition cannot be dropped.

- [Kobon.UpperOpenMathCapHeavyTriples.certificate_cap_heavy_degree_sum, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathCapHeavyTriples.lean#L100)
- [Kobon.UpperOpenMathGlobalFans.certificate_defect_even, line 204](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L204)

### oct:searches — Completed bounded construction searches

**Status: computation.** Saved deletion, chord insertion, singular insertion, straightening and grid-fitting searches produced the exact diagnostics recorded in the construction review, with no new numerical lower-bound record. Time-limited incumbents, failed fits and fixed-input obstructions do not establish unrestricted optimality or nonstretchability.

- [research/three-hour-2026-10-02/constructions/README.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/three-hour-2026-10-02/constructions/README.md#L1)

### oct:release — Complete active-source build and trust audit

**Status: verification-metadata.** Current local verification covers 638 active sources in incremental-hash-pinned-baseline-plus-direct-compilation mode, with 9058 audited theorems: 8046 standard-only and 1012 explicit finite-native descendants. Baseline reuse and clean CI are reported separately. This is implementation provenance, not a count of new mathematical discoveries. Local summary complete=True; no passing final CI is inferred from that field.

- [verification/lean-summary.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/af74635d8b25b32703088460bc41854bb18e1a05/verification/lean-summary.json#L1)
- [research/openmath-seven-hour-2026-10-05/RELEASE_VERIFICATION.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/af74635d8b25b32703088460bc41854bb18e1a05/research/openmath-seven-hour-2026-10-05/RELEASE_VERIFICATION.json#L1)

### long:certificate-definitions — Coordinate definitions and affine orientation identity

**Status: lean/general.** The determinant, oriented vertex evaluation and TrianglePredicate definitions are formalized, and nonparallel affine intersections satisfy the displayed orientation identity.

- [Kobon.det, line 26](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Geometry.lean#L26)
- [Kobon.orientedEval, line 38](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Geometry.lean#L38)
- [Kobon.TrianglePredicate, line 44](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Geometry.lean#L44)
- [Kobon.orientedEval_affine, line 94](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Geometry.lean#L94)

### lit:classical-upper — Historical unrestricted upper benchmark

**Status: external.** The classical Tamura and Clement-Bader upper comparisons in the literature review are cited mathematical results. The repository's arithmetic comparisons with their polynomials do not constitute a formal proof of the unrestricted upper theorem.

- [paper/references.bib, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/paper/references.bib#L1)

### jup:exceptional — Conditional exceptional-fan correction

**Status: lean/general.** For even n>=4 actual NoParallel injective certificates, 2delta>=n+2S-7I+8q+D2-2e. The exceptional full-fan count e and all local/global incidences are extracted; the older supplied summed-fan premise has been discharged.

- [Kobon.UpperOpenMathGlobalFans.certificate_defect_even, line 204](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathGlobalFans.lean#L204)

### module:Permutation — Permutation supporting declarations

**Status: lean/general.** K. Actual triangle support and equal-length, duplicate-free witness transport under bounded label bijections/injections.

- [Kobon.Permutation.triangle_pullback_support, line 70](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Permutation.lean#L70)
- [Kobon.Permutation.transport_list, line 168](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Permutation.lean#L168)
- [Kobon.Permutation.transport_list_of_injective, line 189](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Permutation.lean#L189)

### module:BBLRecursiveWitness — BBLRecursiveWitness supporting declarations

**Status: lean/general.** K. From an actual simple saturated tangent-grid seed with positive central apex and r≥5, constructs the next simple arrangement, at least T+(4r)^2 triangles, the next saturated grid, and positive central apex. The epsilon bound is explicit.

- [Kobon.BBLRecursiveWitness.canonical_step, line 13](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveWitness.lean#L13)

### module:BBLRecursiveGrid — BBLRecursiveGrid supporting declarations

**Status: lean/general.** K. The actual coefficient identity and inverse label maps put the output on the next tangent grid.

- [Kobon.BBLRecursiveGrid.forward, line 9](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveGrid.lean#L9)
- [Kobon.BBLRecursiveGrid.backward, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveGrid.lean#L10)
- [Kobon.BBLRecursiveGrid.graph_reindex, line 90](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveGrid.lean#L90)

### module:BBLRecursiveSeed — BBLRecursiveSeed supporting declarations

**Status: lean/general.** K. Closes the whole geometric seed record under r→2r; Seed includes simplicity, all consecutive distinguished triangles, central orientation, and a valid counted triangle list.

- [Kobon.BBLRecursiveSeed.Seed, line 11](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveSeed.lean#L11)
- [Kobon.BBLRecursiveSeed.seed_step, line 61](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveSeed.lean#L61)
- [Kobon.BBLRecursiveSeed.compatible_step, line 104](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveSeed.lean#L104)
- [Kobon.BBLRecursiveSeed.seed_lower_bound, line 110](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveSeed.lean#L110)

### module:BBLInfinite — BBLInfinite supporting declarations

**Status: lean/general.** K. A uniformly available seed on some positive epsilon interval gives actual arrangements at every finite depth. A uniform seed remains an explicit premise of the generic theorem.

- [Kobon.BBLInfinite.UniformSeed, line 9](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L9)
- [Kobon.BBLInfinite.uniform_step, line 12](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L12)
- [Kobon.BBLInfinite.uniform_iterate, line 32](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L32)
- [Kobon.BBLInfinite.infinite_family, line 46](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L46)
- [Kobon.BBLInfinite.triangleCount_identity, line 52](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLInfinite.lean#L52)

### module:BBLSeed21Normalized — BBLSeed21Normalized supporting declarations

**Status: lean/general.** N. Discharges the odd seed premise for r=5, T=132, 0<ε≤10⁻⁵; the 19 caps, count, and central height 5ε/2 are transported from the existing actual21-line certificate.

- [Kobon.BBLSeed21Normalized.graph_identity, line 29](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21Normalized.lean#L29)
- [Kobon.BBLSeed21Normalized.saturated, line 54](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21Normalized.lean#L54)
- [Kobon.BBLSeed21Normalized.central_height, line 68](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21Normalized.lean#L68)
- [Kobon.BBLSeed21Normalized.seed_with_slopes, line 75](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21Normalized.lean#L75)
- [Kobon.BBLSeed21Normalized.compatible, line 91](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21Normalized.lean#L91)

### module:BBLRecursiveChoice — BBLRecursiveChoice supporting declarations

**Status: lean/general.** K. Retains the complete one-step witness for all sufficiently small positive pencil scales, for each analytically admissible delta. This permits intersection with the extra boundary requirements.

- [Kobon.BBLRecursiveChoice.canonical_eventually, line 12](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRecursiveChoice.lean#L12)

### module:BBLProjection — BBLProjection supporting declarations

**Status: lean/general.** K. Transfers actual row order from horizontal to oblique projection when the projected graph directions have the required sign.

- [Kobon.BBLProjection.graph_projection_mono, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLProjection.lean#L10)
- [Kobon.BBLProjection.graph_projection_strict_mono, line 19](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLProjection.lean#L19)
- [Kobon.BBLProjection.crossing_order_transfer, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLProjection.lean#L28)

### module:BBLRightmost — BBLRightmost supporting declarations

**Status: lean/general.** K. Proves the actual last-intersection property on the old rightmost line, using the seed's clean rightward ray and positive slope.

- [Kobon.BBLRightmost.factor_sine, line 11](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRightmost.lean#L11)
- [Kobon.BBLRightmost.pencil_max_eventually, line 57](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRightmost.lean#L57)
- [Kobon.BBLRightmost.canonical_row_eventually, line 122](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLRightmost.lean#L122)

### module:BBLNextBoundary — BBLNextBoundary supporting declarations

**Status: lean/general.** K. Derives the next rightmost clean ray from actual auxiliary graph equations and row order.

- [Kobon.BBLNextBoundary.positive_directions_eventually, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLNextBoundary.lean#L28)
- [Kobon.BBLNextBoundary.crossing_order_oblique, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLNextBoundary.lean#L56)
- [Kobon.BBLNextBoundary.next_rightmost_boundary, line 69](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLNextBoundary.lean#L69)

### module:BBLVisibleReindex — BBLVisibleReindex supporting declarations

**Status: lean/general.** K. Exact transport of actual visible-pair lists and projection admissibility.

- [Kobon.BBLVisibleReindex.transport_list_of_injective, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVisibleReindex.lean#L84)
- [Kobon.BBLVisibleReindex.visible_congr, line 106](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVisibleReindex.lean#L106)
- [Kobon.BBLVisibleReindex.admissible_pullback, line 115](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVisibleReindex.lean#L115)

### module:BBLVisibleSeed — BBLVisibleSeed supporting declarations

**Status: lean/general.** K. Defines the additional explicit boundary invariant and applies the proved exterior extension to obtain T+V actual triangles.

- [Kobon.BBLVisibleSeed.VisibleSeed, line 7](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVisibleSeed.lean#L7)
- [Kobon.BBLVisibleSeed.even_lower_bound, line 22](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVisibleSeed.lean#L22)

### module:BBLEvenStep — BBLEvenStep supporting declarations

**Status: lean/general.** K. The geometric doubling output has at least V+2r visible pairs; the old and new visible pairs are actually constructed.

- [Kobon.BBLEvenStep.visible_retained_eventually, line 16](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenStep.lean#L16)
- [Kobon.BBLEvenStep.canonical_visible_step, line 34](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenStep.lean#L34)

### module:BBLEvenRecursive — BBLEvenRecursive supporting declarations

**Status: lean/general.** K. Closes the complete visible seed record under doubling. Its projection normal satisfies the explicit positive-horizontal-component hypothesis.

- [Kobon.BBLEvenRecursive.visible_seed_step, line 9](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenRecursive.lean#L9)

### module:BBLEvenInfinite — BBLEvenInfinite supporting declarations

**Status: lean/general.** K. Generic iteration with a uniform visible seed. Initial visibility 2r gives full visibility 2r·2^t at depth t.

- [Kobon.BBLEvenInfinite.UniformVisibleSeed, line 8](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenInfinite.lean#L8)
- [Kobon.BBLEvenInfinite.uniform_iterate, line 27](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenInfinite.lean#L27)
- [Kobon.BBLEvenInfinite.infinite_even_family, line 43](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenInfinite.lean#L43)
- [Kobon.BBLEvenInfinite.visibleCount_full, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLEvenInfinite.lean#L56)

### module:BBLSeed21Visible — BBLSeed21Visible supporting declarations

**Status: lean/general.** N. Discharges the visible seed premise for r=5, T=132, V=10, normal (10, −13), and 0<ε≤10⁻⁵.

- [Kobon.BBLSeed21Visible.compatible, line 44](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLSeed21Visible.lean#L44)

### module:BBLVerifiedFamilies — BBLVerifiedFamilies supporting declarations

**Status: lean/conditional-interface.** N. Unconditional geometric lower bounds in the displayed formulas; no unresolved geometric hypothesis remains. The original11/12 initial cases are kernel proofs, while the overall family inherits the 21-line seed's finite native checks.

- [Kobon.BBLVerifiedFamilies.odd_family, line 18](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L18)
- [Kobon.BBLVerifiedFamilies.even_family, line 42](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L42)
- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLVerifiedFamilies.lean#L51)

### module:BBLFamilyBenchmarks — BBLFamilyBenchmarks supporting declarations

**Status: lean/general.** K for the arithmetic comparisons. The family lies one below the indicated odd/even classical polynomial benchmarks. These equalities do not formalize those expressions as universal upper bounds. The strict-tail comparison is against this repository's previous complete verified envelope, not an assertion of literature priority.

- [Kobon.BBLFamilyBenchmarks.odd_baseline_gain, line 52](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L52)
- [Kobon.BBLFamilyBenchmarks.even_baseline_gain, line 65](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L65)
- [Kobon.BBLFamilyBenchmarks.odd_polynomial_gap, line 94](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L94)
- [Kobon.BBLFamilyBenchmarks.even_simple_polynomial_gap, line 104](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L104)
- [Kobon.BBLFamilyBenchmarks.previous_envelope, line 117](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L117)
- [Kobon.BBLFamilyBenchmarks.strict_previous_tail, line 152](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyBenchmarks.lean#L152)

### module:RecursiveEnvelope — RecursiveEnvelope supporting declarations

**Status: lean/general.** N for all-order existence; K for comparisons. The executable finite maximum retains the previous all-order bound and the two recursive families. It strictly improves the former envelope at orders 10·2^(t+5)+1 and 10·2^(t+5)+2 for every t.

- [Kobon.RecursiveEnvelope.all_n, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L51)
- [Kobon.RecursiveEnvelope.previous_le, line 57](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L57)
- [Kobon.RecursiveEnvelope.odd_family_le, line 62](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L62)
- [Kobon.RecursiveEnvelope.even_family_le, line 67](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L67)
- [Kobon.RecursiveEnvelope.strict_previous_tail, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/RecursiveEnvelope.lean#L73)

### module:BBLForgeConditional — BBLForgeConditional supporting declarations

**Status: lean/conditional-interface.** K, conditional. The formulas (1024·4^t−1)/3 and that quantity plus 16·2^t require respectively UniformSeed 8 341 and a corresponding UniformVisibleSeed 8 341 16 w. This module alone does not supply those seeds. The inherited optimal family is attributed to Forge–Ramírez Alfonsín and the BBL method.

- [Kobon.BBLForgeConditional.odd_family, line 52](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLForgeConditional.lean#L52)
- [Kobon.BBLForgeConditional.even_family, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLForgeConditional.lean#L58)
- [Kobon.BBLForgeConditional.odd_polynomial_exact, line 95](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLForgeConditional.lean#L95)
- [Kobon.BBLForgeConditional.even_simple_polynomial_exact, line 104](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLForgeConditional.lean#L104)

### module:StrictLinearCertificate — StrictLinearCertificate supporting declarations

**Status: lean/general.** K. Positive weighted linear contradiction certificates; these are generic implications from the explicitly supplied identities and positivity.

- [Kobon.StrictLinearCertificate.infeasible, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/StrictLinearCertificate.lean#L25)
- [Kobon.StrictLinearCertificate.homogeneous_infeasible, line 43](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/StrictLinearCertificate.lean#L43)

### module:BBLTangentAlgebra — BBLTangentAlgebra supporting declarations

**Status: lean/general.** K. tan(π/20) satisfies t⁴−4t³−14t²−4t+1=0 and is the unique root in (3/20, 17/100).

- [Kobon.BBLTangentAlgebra.tan_quartic, line 20](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentAlgebra.lean#L20)
- [Kobon.BBLTangentAlgebra.tan_root_interval, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentAlgebra.lean#L51)
- [Kobon.BBLTangentAlgebra.quartic_root_unique, line 57](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentAlgebra.lean#L57)
- [Kobon.BBLTangentAlgebra.real_root_characterization, line 70](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentAlgebra.lean#L70)

### module:BBLTangentValues — BBLTangentValues supporting declarations

**Status: lean/general.** K. The explicit cubic expressions equal the actual tangent values tan(kπ/20) for k<10.

- [Kobon.BBLTangentValues.value_eq_tan, line 62](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangentValues.lean#L62)

### module:BBLTangent48Bounds — BBLTangent48Bounds supporting declarations

**Status: lean/general.** K. Actual rational enclosures for all 23 positive tangent values required by a48-intercept seed, with widths at most 5·10⁻³⁶. The proofs use tan(π/3)=√3, half-angle identities, and complementary-angle inverses. Python only proposes rational endpoints.

- [Kobon.BBLTangent48Bounds.tan_48_1_bounds, line 203](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangent48Bounds.lean#L203)
- [Kobon.BBLTangent48Bounds.tan_48_23_bounds, line 308](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangent48Bounds.lean#L308)

### module:BBLGridObstruction — BBLGridObstruction supporting declarations

**Status: lean/general.** K. Ten specified orientation signs are impossible on the actual20-intercept tangent grid, for every real epsilon and arbitrary real slopes. This is one explicit sign system, not a classification of every optimal21-line arrangement.

- [Kobon.BBLGridObstruction.actual_grid_infeasible, line 240](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLGridObstruction.lean#L240)
- [Kobon.BBLGridObstruction.actual_grid_orientation_impossible, line 263](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLGridObstruction.lean#L263)

### module:BBLObstructionReduction — BBLObstructionReduction supporting declarations

**Status: lean/general.** K. Two omitted weighted columns follow from the affine row identities and distinct omitted intercepts; the reduced system yields a contradiction.

- [Kobon.BBLObstructionReduction.two_columns_follow, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLObstructionReduction.lean#L28)
- [Kobon.BBLObstructionReduction.reduced_infeasible, line 63](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLObstructionReduction.lean#L63)

### module:UpperElementaryEdges — UpperElementaryEdges supporting declarations

**Status: lean/general.** K. The three actual sides of each certified triangle are consecutive intersection segments on their supporting lines.

- [Kobon.UpperElementaryEdges.predicate_all_sides_elementary, line 83](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperElementaryEdges.lean#L83)

### module:UpperEdgeCapacity — UpperEdgeCapacity supporting declarations

**Status: lean/general.** K. At most two pairwise interior-disjoint nondegenerate actual triangles can have the same base segment.

- [Kobon.UpperEdgeCapacity.at_most_two, line 113](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeCapacity.lean#L113)

### module:UpperTriangleIncidence — UpperTriangleIncidence supporting declarations

**Status: lean/general.** K. Derives 3T = used sides + shared sides; the certificate application derives disjointness from the actual triangle predicates.

- [Kobon.UpperTriangleIncidence.exact_incidence, line 196](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTriangleIncidence.lean#L196)
- [Kobon.UpperTriangleIncidence.certificate_incidence, line 230](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTriangleIncidence.lean#L230)

### module:UpperSharedEdge — UpperSharedEdge supporting declarations

**Status: lean/general.** K. An actual shared side cannot have two ordinary endpoints, for indexed supporting lines and disjoint triangle interiors.

- [Kobon.UpperSharedEdge.Pair.has_nonordinary_endpoint, line 108](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSharedEdge.lean#L108)
- [Kobon.UpperSharedEdge.Pair.not_both_endpoints_ordinary, line 98](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSharedEdge.lean#L98)

### module:UpperSharedIncidence — UpperSharedIncidence supporting declarations

**Status: lean/general.** K. Actual shared-side endpoint classification plus its finite incidence partition. The generic counting identity alone is combinatorial; the geometric certificate application supplies the classification.

- [Kobon.UpperSharedIncidence.shared_has_nonordinary_endpoint, line 93](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSharedIncidence.lean#L93)
- [Kobon.UpperSharedIncidence.oneCore_has_both_kinds, line 146](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSharedIncidence.lean#L146)
- [Kobon.UpperSharedIncidence.core_incidence, line 157](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSharedIncidence.lean#L157)

### module:UpperVertexBudget — UpperVertexBudget supporting declarations

**Status: lean/general.** K. Extracts actual intersection multiplicities, point-line incidences, and consecutive bounded interval counts.

- [Kobon.UpperVertexBudget.multiplicity_identity, line 79](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperVertexBudget.lean#L79)
- [Kobon.UpperVertexBudget.point_line_incidence, line 110](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperVertexBudget.lean#L110)
- [Kobon.UpperVertexBudget.line_interval_budget, line 132](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperVertexBudget.lean#L132)

### module:UpperEdgeInventory — UpperEdgeInventory supporting declarations

**Status: lean/general.** K. From actual nonparallel lines with n≥2 and a finite injective certified triangle family, constructs the side inventory and proves δ=S+U−D₁−D₂. No supplied global capacity, edge-count, or incidence identity is needed.

- [Kobon.UpperEdgeInventory.edge_cardinality, line 188](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeInventory.lean#L188)
- [Kobon.UpperEdgeInventory.predicate_side_mem_edges, line 290](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeInventory.lean#L290)
- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEdgeInventory.lean#L345)

### module:UpperCoreExtraction — UpperCoreExtraction supporting declarations

**Status: lean/general.** K. Restricts multiplicity loss to the actual nonordinary core and identifies a D₁ edge as having exactly one ordinary endpoint. The empty-core corollary proves the classical simple-arrangement inequality 3T≤n(n−2).

- [Kobon.UpperCoreExtraction.defect_identity, line 61](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreExtraction.lean#L61)
- [Kobon.UpperCoreExtraction.certificate_oneCore_classification, line 76](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreExtraction.lean#L76)
- [Kobon.UpperCoreExtraction.simple_arrangement_upper, line 99](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreExtraction.lean#L99)

### module:UpperSimpleOptimality — UpperSimpleOptimality supporting declarations

**Status: lean/general.** K. Discharges empty-core and finite-family extraction directly from NoParallel, NoConcurrent, and SimpleLowerBound. For n≥2, every such witness obeys 3T≤n(n−2) and T≤floor(n(n−2)/3). This is a complete formalization of the classical simple bound, not a new unrestricted upper bound.

- [Kobon.UpperSimpleOptimality.core_empty, line 37](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSimpleOptimality.lean#L37)
- [Kobon.UpperSimpleOptimality.certificate_upper, line 49](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSimpleOptimality.lean#L49)
- [Kobon.UpperSimpleOptimality.simple_lower_bound_upper, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSimpleOptimality.lean#L58)
- [Kobon.UpperSimpleOptimality.simple_lower_bound_floor, line 70](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperSimpleOptimality.lean#L70)

### module:UpperCoreLineIncidence — UpperCoreLineIncidence supporting declarations

**Status: lean/general.** K. Derives the actual incidence inequality D₂+h≤I by counting consecutive core vertices along each supporting line.

- [Kobon.UpperCoreLineIncidence.core_line_budget, line 139](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreLineIncidence.lean#L139)

### module:UpperCoreCombinatorics — UpperCoreCombinatorics supporting declarations

**Status: lean/general.** K. Derives D₂≤binom(q, 2), its q≤3 specialization, and nonnegative summed multiple-point surplus.

- [Kobon.UpperCoreCombinatorics.core_edge_count, line 35](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreCombinatorics.lean#L35)
- [Kobon.UpperCoreCombinatorics.three_core_edge_count, line 43](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreCombinatorics.lean#L43)
- [Kobon.UpperCoreCombinatorics.core_surplus, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreCombinatorics.lean#L56)

### module:UpperFan — UpperFan supporting declarations

**Status: lean/conditional-interface.** K, explicit local interface. Actual cyclic fan data, with its orientation and incidence hypotheses supplied, imply the local sector-count conclusions. Whole-arrangement extraction of this interface is not proved here.

- [Kobon.UpperFan.Sectors.all_sectors_of_extremal, line 171](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L171)
- [Kobon.UpperFan.Sectors.core_shared_card_eq_three_of_extremal, line 187](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L187)
- [Kobon.UpperFan.Sectors.weighted_local_bound, line 227](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFan.lean#L227)

### module:UpperFanSupport — UpperFanSupport supporting declarations

**Status: lean/conditional-interface.** K, explicit local interface. The three core-ended rays of a full extremal fan cannot all lie in the indicated closed half-plane under the positive cyclic orientation and support-line hypotheses.

- [Kobon.UpperFanSupport.Sectors.extremal_core_not_in_halfplane, line 171](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperFanSupport.lean#L171)

### module:UpperCoreBoundary — UpperCoreBoundary supporting declarations

**Status: lean/conditional-interface.** K, conditional assembly. A supplied family of actual fans and endpoint-to-core incidence maps gives the aggregate local bound. The source does not extract that entire family from an arbitrary arrangement.

- [Kobon.UpperCoreBoundary.bound_at_supported_core, line 19](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreBoundary.lean#L19)
- [Kobon.UpperCoreBoundary.CoreFamily.sum_ordinary_bound, line 75](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreBoundary.lean#L75)

### module:UpperTripleFan — UpperTripleFan supporting declarations

**Status: lean/conditional-interface.** K, explicit matching interface. Neighboring full triple fans are incompatible under the stated matching across their common edge.

- [Kobon.UpperTripleFan.extremal_triple_fans_not_adjacent, line 156](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTripleFan.lean#L156)
- [Kobon.UpperTripleFan.incompatible_full_triple_fans, line 65](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperTripleFan.lean#L65)

### module:UpperCoreBudget — UpperCoreBudget supporting declarations

**Status: lean/conditional-interface.** K, conditional aggregate arithmetic. The integer inequalities imply the advertised restricted bounds when their fan, charging, and incidence premises are supplied. This is not an unconditional new upper bound for all arrangements.

- [Kobon.UpperCoreBudget.weighted_defect_with_core_edges, line 47](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreBudget.lean#L47)
- [Kobon.UpperCoreBudget.at_most_three_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreBudget.lean#L58)
- [Kobon.UpperCoreBudget.triangles_from_three_core_defect, line 72](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCoreBudget.lean#L72)

### module:UpperCleanHalfplane — UpperCleanHalfplane supporting declarations

**Status: lean/general.** K. An actual clean line has n−1 distinct crossings; one common open half-plane contains another intersection on every transverse line. Triangles at its ordinary crossings have a side on the line. For even n, an actual two-element partition of its crossings is impossible. Extracting that partition from degree-one edge assumptions remains separate.

- [Kobon.UpperCleanHalfplane.common_halfplane, line 62](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanHalfplane.lean#L62)
- [Kobon.UpperCleanHalfplane.clean_crossings_injective, line 92](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanHalfplane.lean#L92)
- [Kobon.UpperCleanHalfplane.ordinary_vertex_pairs_on_line, line 115](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanHalfplane.lean#L115)
- [Kobon.UpperCleanHalfplane.clean_crossing_card, line 163](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanHalfplane.lean#L163)
- [Kobon.UpperCleanHalfplane.clean_line_no_pair_partition, line 179](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanHalfplane.lean#L179)

### module:UpperCleanEdges — UpperCleanEdges supporting declarations

**Status: lean/general.** K. Turns the common half-plane intersections into actual consecutive bounded segments incident to the clean-line crossings.

- [Kobon.UpperCleanEdges.incident_positive_edge, line 27](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanEdges.lean#L27)
- [Kobon.UpperCleanEdges.incident_negative_edge, line 63](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanEdges.lean#L63)
- [Kobon.UpperCleanEdges.common_bounded_side, line 77](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanEdges.lean#L77)

### module:UpperCleanPairing — UpperCleanPairing supporting declarations

**Status: lean/general.** K. Actual consecutive-edge indices and half-plane signs give uniqueness of the selected incident segment. The global map is assembled in UpperCleanCharging below.

- [Kobon.UpperCleanPairing.pair_indices_consecutive, line 14](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanPairing.lean#L14)
- [Kobon.UpperCleanPairing.incident_positive_unique, line 42](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanPairing.lean#L42)
- [Kobon.UpperCleanPairing.incident_negative_unique, line 78](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanPairing.lean#L78)

### module:UpperCleanCover — UpperCleanCover supporting declarations

**Status: lean/general.** K. Extracts the actual pair cover under the degree-one assumption and contradicts its parity. Every clean line in an even-order nonparallel arrangement with n≥3 therefore has an actual incident charge edge that is unused or has one ordinary endpoint and one core endpoint, relative to the supplied finite injective certified triangle family. The aggregate charge-fiber count is supplied by UpperCleanCharging below.

- [Kobon.UpperCleanCover.actual_base_cover, line 212](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCover.lean#L212)
- [Kobon.UpperCleanCover.clean_line_bad_degree, line 355](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCover.lean#L355)
- [Kobon.UpperCleanCover.certificate_clean_line_charge, line 401](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCover.lean#L401)

### module:UpperCleanCharging — UpperCleanCharging supporting declarations

**Status: lean/general.** K. Actual even-order clean-line charging: n-h <= 2U+D1 for nonparallel real lines, n>=3, and any finite injective certified triangle family. The charge map and its finite fibers are extracted, with no charging premise.

- [Kobon.UpperCleanCharging.charge_line_unique, line 55](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCharging.lean#L55)
- [Kobon.UpperCleanCharging.oneCore_ordinary_card, line 75](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCharging.lean#L75)
- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperCleanCharging.lean#L100)

### module:UpperEvenSimpleOptimality — UpperEvenSimpleOptimality supporting declarations

**Status: lean/general.** K. The actual incidence identity and extracted charging imply 6T <= n(2n-5) and its floor form for every simple certificate witness with even n>=4. This formalizes the classical simple even upper bound; it is not an unrestricted nonsimple bound.

- [Kobon.UpperEvenSimpleOptimality.shared_empty, line 12](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L12)
- [Kobon.UpperEvenSimpleOptimality.certificate_even_upper, line 31](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L31)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_upper, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L56)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### module:BBLFamilyOptimality — BBLFamilyOptimality supporting declarations

**Status: lean/general.** K for both universal upper halves; N for existence and the combined windows. At n=10*2^t+1, +2, actual simple arrangements realize the verified family counts, and every simple certificate witness has at most that count plus one. This upgrades the earlier polynomial benchmark comparison to a genuine formal optimality window.

- [Kobon.BBLFamilyOptimality.odd_upper, line 12](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyOptimality.lean#L12)
- [Kobon.BBLFamilyOptimality.even_upper, line 20](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyOptimality.lean#L20)
- [Kobon.BBLFamilyOptimality.odd_window, line 29](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyOptimality.lean#L29)
- [Kobon.BBLFamilyOptimality.even_window, line 35](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLFamilyOptimality.lean#L35)

### module:ParametricCached — Materialized parameter arrays preserve checker soundness

**Status: lean/general.** Materializing parameter forms in arrays preserves the exact checker and its soundness. No measured performance improvement is asserted.

- [Kobon.ParametricCached.cache_eq, line 14](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/ParametricCached.lean#L14)
- [Kobon.ParametricCached.simple_sound, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/ParametricCached.lean#L28)
- [Kobon.ParametricCached.triangle_eq, line 47](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/ParametricCached.lean#L47)

### om:family37 — Completed compatible 37-line known orbit

**Status: lean/general.** For every natural t, q=36*2^t gives actual simple witnesses with 432*4^t-1 triangles at q+1 lines and 432*4^t-1+18*2^t at q+2. Both meet the simple upper floors. This is the already known Parpalak--Utkin18-dyadic orbit at its next depth; at 38 its449 simple triangles do not improve the retained450 unrestricted witness.

- [Kobon.OpenMathConstructionFamily37.uniform_seed, line 22](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L22)
- [Kobon.OpenMathConstructionFamily37.odd_family, line 54](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L54)
- [Kobon.OpenMathConstructionFamily37.even_family, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L58)
- [Kobon.OpenMathConstructionFamily37.odd_optimal_in_simple_arrangements, line 98](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L98)
- [Kobon.OpenMathConstructionFamily37.even_optimal_in_simple_arrangements, line 107](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L107)

### om:known-orbits — Completed compatible 33/37/49 numerical orbits

**Status: lean/general; inherited numerical families.** For every natural t the compatible33, 37, 49 seeds give q=32*2^t, 36*2^t, 48*2^t with odd counts respectively(1024*4^t-1)/3, 432*4^t-1, 768*4^t-1, and even companions adding q/2. All meet the appropriate simple-model upper floors. These numerical orbits remain attributed to Forge--Ramirez Alfonsin, Parpalak--Utkin/Blanc, and BBL. Exact compatible seed certification and formal recursive integration are the current contribution, with native finite roots retained separately from standard upper proofs.

- [Kobon.OpenMathConstructionForgeFamily.odd_family, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L25)
- [Kobon.OpenMathConstructionForgeFamily.even_family, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L28)
- [Kobon.OpenMathConstructionForgeFamily.odd_optimal_in_simple_arrangements, line 33](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L33)
- [Kobon.OpenMathConstructionForgeFamily.even_optimal_in_simple_arrangements, line 42](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionForgeFamily.lean#L42)
- [Kobon.OpenMathConstructionFamily37.odd_family, line 54](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L54)
- [Kobon.OpenMathConstructionFamily37.even_family, line 58](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L58)
- [Kobon.OpenMathConstructionFamily37.odd_optimal_in_simple_arrangements, line 98](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L98)
- [Kobon.OpenMathConstructionFamily37.even_optimal_in_simple_arrangements, line 107](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily37.lean#L107)
- [Kobon.BBL49VerifiedFamilies.odd_family, line 36](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L36)
- [Kobon.BBL49VerifiedFamilies.even_family, line 48](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L48)
- [Kobon.BBL49VerifiedFamilies.odd_exact, line 82](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L82)
- [Kobon.BBL49VerifiedFamilies.even_exact, line 95](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBL49VerifiedFamilies.lean#L95)

### om:family61 — Compatible 61-line seed and preserved 28-pair family

**Status: lean/general.** For every natural t, q=60*2^t gives actual simple real-line witnesses of1200*4^t-10 triangles at q+1 and 1200*4^t+30*2^t-12 at q+2. The seed retains1190 triangles, 59 axis caps and 28 visible pairs for 0<epsilon<=1/100000000 using actual tangent directions. A positive interval may shrink at each depth. Poola owns the original 61:1190 point count; BBL owns the doubling method. Odd/even existence inherit five/seven explicit native certificate roots. No absolute numerical-priority assertion is made.

- [Kobon.OpenMathConstructionFamily61.uniform_seed, line 23](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily61.lean#L23)
- [Kobon.OpenMathConstructionFamily61.uniform_visible_seed, line 28](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily61.lean#L28)
- [Kobon.OpenMathConstructionFamily61.odd_family, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily61.lean#L73)
- [Kobon.OpenMathConstructionFamily61.even_family, line 77](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily61.lean#L77)
- [Kobon.OpenMathConstructionFamily61.odd_window, line 142](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily61.lean#L142)
- [Kobon.OpenMathConstructionFamily61.even_window, line 151](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionFamily61.lean#L151)
- [research/openmath-seven-hour-2026-10-05/constructions/construction-proof-provenance.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/constructions/construction-proof-provenance.json#L1)

### om:pareto61 — 29-pair seed and strongest 60-dyadic even family

**Status: lean/general.** The compatible seed still has1190 triangles and 59 axis caps, now with 29 visible pairs. For every natural t, V_t=30*2^t-1 and the even family is 1200*4^t+30*2^t-11 at 60*2^t+2 lines, exactly one above the preserved28-pair family at every depth. The odd count remains1200*4^t-10. The simple upper gaps are9/10. The new even witness at 62 is1219, below the retained1220 baseline. Seven explicit native finite roots support the seed; recursive geometry is standard.

- [Kobon.OpenMathConstructionParetoFamily61.uniform_visible_seed, line 18](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L18)
- [Kobon.OpenMathConstructionParetoFamily61.visible_formula, line 30](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L30)
- [Kobon.OpenMathConstructionParetoFamily61.odd_family, line 48](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L48)
- [Kobon.OpenMathConstructionParetoFamily61.even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L51)
- [Kobon.OpenMathConstructionParetoFamily61.even_polynomial, line 42](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L42)
- [Kobon.OpenMathConstructionParetoFamily61.improves_prior_even_family, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L59)
- [Kobon.OpenMathConstructionParetoFamily61.even_window, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionParetoFamily61.lean#L84)

### om:construction-envelope — Pointwise retained all-natural-order construction portfolio

**Status: lean/general.** The executable maximum retains RecursiveEnvelope.bound and the 33, 37, 49, 61 odd/even candidates over0<=t<=n. For every natural n it gives an actual LowerBound, never below the previous envelope or baseline. The61 gains over G are20*2^t-11 odd and 10*2^t-11 even for t>=1. Comparisons with G and the old28-pair family are exact; they do not imply strict improvement over every prior portfolio candidate or literature bound.

- [Kobon.OpenMathConstructionEnvelope.bound, line 94](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L94)
- [Kobon.OpenMathConstructionEnvelope.all_n, line 97](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L97)
- [Kobon.OpenMathConstructionEnvelope.previous_le, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L100)
- [Kobon.OpenMathConstructionEnvelope.baseline_le, line 102](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L102)
- [Kobon.OpenMathConstructionEnvelope.retains_old_even_family_plus_one, line 141](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L141)
- [Kobon.OpenMathConstructionEnvelope.odd_baseline_gain, line 145](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L145)
- [Kobon.OpenMathConstructionEnvelope.even_baseline_gain, line 151](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionEnvelope.lean#L151)

### om:boundary-budget — Actual terminal-resource identities

**Status: lean/general.** For simple NoParallel real arrangements and an injective selected triangle family, n>=3: A+2B=2n, A<=2U, delta=U, and B>=n-delta, where terminal incidences are extracted from sorted actual crossing vertices. Every simple arrangement also has B>=3. No exterior-visibility or convex-hull oracle is a premise.

- [Kobon.OpenMathSimpleBoundary.terminal_partition, line 433](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSimpleBoundary.lean#L433)
- [Kobon.OpenMathSimpleBoundary.certificate_single_terminal_budget, line 371](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSimpleBoundary.lean#L371)
- [Kobon.OpenMathSimpleBoundary.certificate_double_terminal_budget, line 454](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSimpleBoundary.lean#L454)
- [Kobon.OpenMathSimpleBoundary.certificate_boundary_defect, line 467](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSimpleBoundary.lean#L467)
- [Kobon/OpenMathBoundaryMinimum.lean, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathBoundaryMinimum.lean#L1)

### om:successor — Indefinite simple successor with deficit-dependent gain

**Status: lean/general.** For every supplied SimpleLowerBound n T with n>=3, set signed delta=n(n-2)-3T and b=max(3, max(0, n-delta)). There is a simple real straight-line witness at n+1 with at least T+g triangles, where g=min(floor(n/2), ceil(b/2)). The same g equals ceil((n-1)b/(2n)); natural subtractions in the implementation truncate at zero. Actual terminal rays, critical roots and integer averaging discharge all visibility premises.

- [Kobon.OpenMathExtensionFormula.stepGain_formula, line 50](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathExtensionFormula.lean#L50)
- [Kobon.OpenMathExtensionFormula.closed_form_successor, line 56](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathExtensionFormula.lean#L56)
- [Kobon.OpenMathEveryOrderExtension.successor, line 45](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathEveryOrderExtension.lean#L45)

### om:successor-iteration — Both-parity indefinite quantitative iteration

**Status: lean/general.** Starting from any supplied simple n>=3 seed, the count recurrence T_(k+1)=T_k+g(n+k, T_k) gives actual SimpleLowerBound witnesses at every later order. For n>=4 each step gains at least two and hence T_k>=T+2k. This does not prove a half-order gain for arbitrary seeds; its numerical envelope may be weaker than the established quadratic baseline.

- [Kobon.OpenMathEveryOrderExtension.stepGain_at_least_two, line 51](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathEveryOrderExtension.lean#L51)
- [Kobon.OpenMathEveryOrderExtension.infinite_linear_extension, line 67](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathEveryOrderExtension.lean#L67)
- [Kobon.OpenMathEveryOrderExtension.iteratedCount, line 76](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathEveryOrderExtension.lean#L76)
- [Kobon.OpenMathEveryOrderExtension.infinite_quantitative_extension, line 82](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathEveryOrderExtension.lean#L82)

### om:perfect-successor — Near-perfect odd successor and simple optimality

**Status: lean/general.** For odd n=2m+1>=3, a supplied simple witness with delta<=2 has a successor gaining m. A supplied witness attaining the odd simple upper floor therefore has a successor attaining the even simple floor. The existence of such an optimal input is a premise; optimal odd seeds are not asserted at every order. BBL's older perfect exterior step and Blanc's individual near-perfect examples remain credited.

- [Kobon.OpenMathBoundarySuccessor.odd_defect_two_successor, line 84](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathBoundarySuccessor.lean#L84)
- [Kobon.OpenMathOptimalSuccessor.optimal_odd_to_even, line 21](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathOptimalSuccessor.lean#L21)
- [Kobon.OpenMathOptimalSuccessor.even_optimality, line 38](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathOptimalSuccessor.lean#L38)

### om:ray-resources — Exact actual ray and defect resources

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. The actual resource identities are D1+2D2+C+Rc=2I and 2delta=2 sum_core r(r-3)+2U+C+Rc-D1. C counts bounded nonshared core endpoints and Rc actual unbounded core rays; arbitrary core multiplicities are allowed.

- [Kobon.UpperOpenMathRayResources.certificate_ray_resource_identity, line 116](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathRayResources.lean#L116)
- [Kobon.UpperOpenMathRayResources.certificate_defect_ray_identity, line 140](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathRayResources.lean#L140)

### om:component-hull — Actual component hull deficit penalty

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. With b_h the sum of supporting hull-point counts of the actual shared-core components, 2delta>=2U+2 sum_(r>=3)r(r-4)t_r+3q+3b_h. Each supported core consumes actual nonshared/ray resources. For all core multiplicities at least R>=4 this gives 6T+(2R(R-4)+3)q+3b_h+2U<=2n(n-2). No convex-hull oracle is assumed.

- [Kobon.UpperOpenMathComponentHullDeficit.certificate_component_hull_deficit, line 86](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathComponentHullDeficit.lean#L86)

### om:triple-cap — Actual triple-cap transfer budget

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. D1+2E3+P21<=2q and delta>=U+q-D2+2E3+P21. Marked shared rays transfer actual source capacity to poor targets; no cap-count hypothesis is assumed.

- [Kobon.UpperOpenMathTripleCapBudget.certificate_triple_cap_budget, line 57](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathTripleCapBudget.lean#L57)
- [Kobon.UpperOpenMathTripleCapBudget.certificate_triple_cap_defect, line 161](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathTripleCapBudget.lean#L161)

### om:cap-heavy — Actual cap-heavy triple independence and incidence

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Cap-heavy triple sources cannot be adjacent across an actual shared-core side. Their core-degree sum consumes distinct actual core-to-core edges. Other core multiplicities are unrestricted. Full extremal triples contribute three incidences; the statement does not assert independence of higher-multiplicity extremal fans.

- [Kobon.UpperOpenMathCapHeavyTriples.certificate_cap_heavy_not_adjacent, line 37](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathCapHeavyTriples.lean#L37)
- [Kobon.UpperOpenMathCapHeavyTriples.certificate_cap_heavy_degree_sum, line 100](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathCapHeavyTriples.lean#L100)

### om:mixed-cap — Mixed multiplicity weighted cap budget

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. With Q=sum_(r>=4)(r(r-4)+1) and P the poor-triple core-degree sum, 3D1+3q+3Q+2P<=3S and 3delta>=3(U+q-D2+Q)+2P. Higher extremal fans need not be independent; their multiplicity surplus supplies the charge.

- [Kobon.UpperOpenMathMixedCapBudget.certificate_mixed_weighted_budget, line 53](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCapBudget.lean#L53)
- [Kobon.UpperOpenMathMixedCapBudget.certificate_mixed_weighted_defect, line 235](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCapBudget.lean#L235)
- [Kobon.UpperOpenMathMixedCapBudget.certificate_mixed_core_defect, line 249](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCapBudget.lean#L249)

### om:mixed-curvature — Degree-free mixed component curvature

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. For arbitrary multiplicities, degrees and component sizes, delta+Aall+sum_s ceil(B_s/2)>=U+c+h, with h=sum_(r>=4)r(r-4). Aall counts all full(2, 4) triple cores and B_s full(1, 5) triples. The doubled companion is2delta+2Aall+B>=2U+c+2h. Every component includes its isolated core vertices. Corrections are retained; they cannot be discarded for a universal numerical upper bound.

- [Kobon.UpperOpenMathMixedCurvatureBound.certificate_mixed_curvature_component_bound, line 41](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCurvatureBound.lean#L41)
- [Kobon.UpperOpenMathMixedCurvatureBound.certificate_mixed_doubled_component_bound, line 68](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedCurvatureBound.lean#L68)

### om:paid-curvature — Degree-free marked all-triple component curvature

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. delta+A0+sum_s ceil(B_s/2)>=U+c, where A0 counts only unmarked full(2, 4) triples. The actual marked-port payment and finite escape proof exclude the zero paid case. No degree, independence or component-size hypothesis is imposed.

- [Kobon.UpperOpenMathPaidCurvatureBound.certificate_component_half_penalty_bound, line 116](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathPaidCurvatureBound.lean#L116)
- [Kobon.UpperOpenMathPaidCurvatureBound.certificate_half_exception_bound, line 171](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathPaidCurvatureBound.lean#L171)

### om:half-curvature — Retained half-coefficient and gain portfolio

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. 2delta+A0+B>=2U; a stronger gain version has 4delta+2A0+2B>=4U+6E3+5P21. The component maximum retains strict paid curvature and the rounded gain score before summing; Lean proves its dominance over the older hybrid. These intermediate formulas are retained even where the later N12 theorem is stronger.

- [Kobon.UpperOpenMathHalfCurvature.certificate_half_defect_bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathHalfCurvature.lean#L49)
- [Kobon.UpperOpenMathHalfCurvatureGain.certificate_half_gain_defect_bound, line 79](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathHalfCurvatureGain.lean#L79)
- [Kobon.UpperOpenMathClosedHalfCurvature.certificate_hybrid_component_defect, line 178](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathClosedHalfCurvature.lean#L178)
- [Kobon.UpperOpenMathClosedHalfCurvature.certificate_hybrid_gain_component_defect, line 236](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathClosedHalfCurvature.lean#L236)
- [Kobon.UpperOpenMathClosedHalfCurvature.hybrid_gain_dominates, line 255](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathClosedHalfCurvature.lean#L255)

### om:n13-global — Source-free all-triple defect gain

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. An actual(1, 3) recipient has at most one antipodal full source neighbor, eliminating J13. A(2, 1) recipient has none. Hence2delta+B>=2U+3(E3+P21), with no component size or degree restriction. The corresponding source-free component score is also proved.

- [Kobon.UpperOpenMathN13ActualNoDouble.certificate_n13_no_two_anti_neighbors, line 13](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathN13ActualNoDouble.lean#L13)
- [Kobon.UpperOpenMathPartialRecipients.certificate_partial_anti_degree_zero, line 12](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathPartialRecipients.lean#L12)
- [Kobon.UpperOpenMathN13Curvature.certificate_source_free_defect_bound, line 37](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathN13Curvature.lean#L37)
- [Kobon.UpperOpenMathN13Curvature.certificate_source_free_hybrid_component_defect, line 66](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathN13Curvature.lean#L66)

### om:n12-global — N12 all-triple positive gain

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. An actual(1, 2) recipient has at most one antipodal source neighbor. Therefore2delta+B>=2U+3(E3+P21)+N12, with no degree or component-size restriction. This is an actual arrangement endpoint, not a supplied radial-interface implication.

- [Kobon.UpperOpenMathN12Recipient.certificate_n12_anti_degree_le_one, line 152](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathN12Recipient.lean#L152)
- [Kobon.UpperOpenMathN12Curvature.certificate_n12_source_free_defect_bound, line 99](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathN12Curvature.lean#L99)

### om:n12-components — Strongest completed all-triple component portfolio

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. delta>=U+sum_s max(1-A_s-ceil(B_s/2), ceil((3E_s+3P_s+N12_s-B_s)/2)). All counts are taken within each actual connected component before rounding or taking the maximum. Lean proves dominance over the preceding source-free portfolio. This component theorem contains no M22 term.

- [Kobon.UpperOpenMathClosedN12Curvature.certificate_closed_n12_source_free_gain, line 219](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathClosedN12Curvature.lean#L219)
- [Kobon.UpperOpenMathClosedN12Curvature.certificate_n12_source_free_hybrid_component_defect, line 282](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathClosedN12Curvature.lean#L282)
- [Kobon.UpperOpenMathClosedN12Curvature.source_free_n12_dominates, line 306](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathClosedN12Curvature.lean#L306)

### om:m22-global — Strongest completed global marked-balanced gain

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. With M22 counting marked(2, 2) cores, the proved global endpoint is 2delta+B>=2U+3(E3+P21)+N12+M22. The local actual incident-edge competition m+degreeFrom(A0, p)<=d makes the marked balanced gap positive. M22 is currently retained globally; no componentwise M22 portfolio is asserted.

- [Kobon.UpperOpenMathLocalPortBudget.certificate_marked_plus_anti_degree_le, line 10](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathLocalPortBudget.lean#L10)
- [Kobon.UpperOpenMathM22Curvature.certificate_m22_source_free_defect_bound, line 117](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathM22Curvature.lean#L117)

### om:profile-positive — Explicit positive-profile sufficient condition

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. If every component satisfies B_s+1<=3E_s+3P_s+N12_s, then delta>=U+c. The condition is an explicit hypothesis about actual extracted profiles, not a theorem that every component has it. Arbitrarily large components and degrees are permitted.

- [Kobon.UpperOpenMathPositiveProfileComponents.certificate_positive_profile_component_defect, line 43](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathPositiveProfileComponents.lean#L43)

### om:mixed-degree3 — Mixed degree-at-most-three strict curvature

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. If every shared-core degree is at most3, delta>=U+c+h. Arbitrary multiplicities, component sizes, branching and cycles are allowed; actual equality geometry supplies one positive unit per component.

- [Kobon.UpperOpenMathMixedDegreeThree.certificate_mixed_degree_three_component_bound, line 158](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedDegreeThree.lean#L158)

### om:mixed-degree4 — Mixed degree-at-most-four strict curvature

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. If every shared-core degree is at most4, delta+Aall>=U+c+h. The full(2, 4) triple correction remains; components can have arbitrary order and multiplicities.

- [Kobon.UpperOpenMathMixedDegreeFour.certificate_mixed_degree_four_component_bound, line 169](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedDegreeFour.lean#L169)

### om:five-components — Five-core component strict bounds

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. If every actual shared-core component has at most5 vertices, delta>=U+c+h for arbitrary multiplicities, and delta>=U+c in the all-triple subclass. The total number of cores and components is unrestricted. Perfect-implies-simple in this sufficient scope formalizes a conclusion already stated by Clement--Bader, with no first-discovery claim.

- [Kobon.UpperOpenMathMixedFiveCoreComponents.certificate_mixed_five_component_bound, line 96](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedFiveCoreComponents.lean#L96)
- [Kobon.UpperOpenMathMixedFiveCoreComponents.certificate_mixed_five_component_perfect_simple, line 131](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedFiveCoreComponents.lean#L131)
- [Kobon.UpperOpenMathFiveCoreComponents.certificate_five_core_component_bound, line 112](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathFiveCoreComponents.lean#L112)

### om:forest — Actual shared-core forest bounds

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. If the actual shared-core graph is acyclic, D2+c=q. With arbitrary degrees and multiplicities delta>=U+c+Q and 3delta>=3(U+c+Q)+2P; in the all-triple class delta>=U+c+2E3+P21. This includes branching trees of arbitrary size.

- [Kobon.UpperOpenMathForestBudget.certificate_forest_edge_component_count, line 25](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathForestBudget.lean#L25)
- [Kobon.UpperOpenMathForestBudget.certificate_triple_forest_bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathForestBudget.lean#L49)
- [Kobon.UpperOpenMathForestBudget.certificate_mixed_forest_bound, line 95](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathForestBudget.lean#L95)
- [Kobon.UpperOpenMathForestBudget.certificate_mixed_forest_weighted_bound, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathForestBudget.lean#L73)

### om:graph-classes — Retained actual degree, order and forest portfolio

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. The proved class corollaries retain delta>=U+c+h at shared-core degree<=3 or component order<=5; at degree<=4 they retain the Aall correction. Forests instead retain the mixed weighted cap bound and the stronger all-triple positive cap terms. Each restriction is stated separately; no class condition is silently dropped.

- [Kobon.UpperOpenMathMixedDegreeThree.certificate_mixed_degree_three_component_bound, line 158](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedDegreeThree.lean#L158)
- [Kobon.UpperOpenMathMixedDegreeFour.certificate_mixed_degree_four_component_bound, line 169](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedDegreeFour.lean#L169)
- [Kobon.UpperOpenMathMixedFiveCoreComponents.certificate_mixed_five_component_bound, line 96](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathMixedFiveCoreComponents.lean#L96)
- [Kobon.UpperOpenMathForestBudget.certificate_mixed_forest_weighted_bound, line 73](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathForestBudget.lean#L73)
- [Kobon.UpperOpenMathForestBudget.certificate_triple_forest_bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathForestBudget.lean#L49)

### om:antipodal-intersection — Two antipodal sources share at most two neighbors

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Two distinct antipodal full triple sources have at most two common actual core neighbors. Only the source cores must be triple; neighbors may have arbitrary multiplicity. Strict cevian crossing and elementary-segment blocking supply the geometry.

- [Kobon.UpperOpenMathAntipodalThreeNeighbors.certificate_common_neighbor_card_le_two, line 94](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathAntipodalThreeNeighbors.lean#L94)

### om:seven-components — At-most-one-source and seven-core component portfolios

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. A component with at most7 core vertices has at most one antipodal source. The proved score ceil((3E_s+2P_s-B_s)/2) applies under that source condition, and the adaptive theorem retains the preceding score otherwise. The B correction cannot be omitted to claim delta>=U+c for all seven-core components.

- [Kobon.UpperOpenMathSingleSourceComponents.certificate_seven_core_single_source, line 15](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathSingleSourceComponents.lean#L15)
- [Kobon.UpperOpenMathSingleSourceComponents.certificate_adaptive_component_defect, line 128](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathSingleSourceComponents.lean#L128)
- [Kobon.UpperOpenMathSingleSourceComponents.certificate_seven_component_defect, line 147](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathSingleSourceComponents.lean#L147)

### om:n13-support — Actual affine-maximum exclusion for N13 recipients

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. A(1, 3) core with an antipodal source neighbor cannot maximize an affine functional injective on an actual finite closed core set containing it. This completed boundary lemma does not exclude an N13 neighbor of a maximum balanced core or prove every component strictly positive without corrections.

- [Kobon.UpperOpenMathN13ActualSupportExtreme.certificate_n13_positive_anti_degree_not_max, line 45](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathN13ActualSupportExtreme.lean#L45)

### om:even-line-budget — Safe actual all-line parity budget

**Status: lean/general.** For n>=2 pairwise nonparallel real lines and any finite injective selected family of certified triangles, with all inventories extracted from that actual arrangement. Counts of unused sides are relative to the selected family. Every core has exactly three supporting lines. For even n>=4, n<=2U+2D1+C. A shared core-ordinary side may pay as both a transverse charge and a base; dropping the second D1 is false. The stronger token trade-off and C>=2D1 remain research hypotheses rather than inputs to current theorems.

- [Kobon.UpperOpenMathOrdinaryGlobalCharge.certificate_all_line_parity_budget, line 146](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/UpperOpenMathOrdinaryGlobalCharge.lean#L146)

### om:translation-germs — Exact simultaneous triangle classification under line translation

**Status: lean/general.** For any finite pairwise nonparallel actual real arrangement, translating one line makes the determinant-side evaluations affine in epsilon. A common positive threshold classifies every supporting triple exactly by its constant and linear coefficients. This is a general real-parameter proof with standard axioms only.

- [Kobon.OpenMathTranslationGerms.eval_translate_affine, line 140](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTranslationGerms.lean#L140)
- [Kobon.OpenMathTranslationGerms.side_translate_affine, line 146](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTranslationGerms.lean#L146)
- [Kobon.OpenMathTranslationGerms.simultaneous_triangle_stability, line 205](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTranslationGerms.lean#L205)

### om:translation-identity — Global exact birth/loss count and retention criterion

**Status: lean/general.** For sufficiently small positive epsilon, T(epsilon)+lost=T(0)+born, with complete global germ birth/loss sets. The untouched-corner/stationary-zero conditions imply no loss and, with an appropriate tiny triangle, a one-triangle gain. These retention conditions are explicit; a half-plane count is not substituted for the loss set.

- [Kobon.OpenMathTranslationCounting.translated_birth_loss_identity, line 98](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTranslationCounting.lean#L98)
- [Kobon.OpenMathTranslationRetention.no_loss_count, line 54](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTranslationRetention.lean#L54)
- [Kobon.OpenMathTranslationRetention.classical_gain_one, line 119](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTranslationRetention.lean#L119)

### om:isolated-birth — Exact isolated concurrent-triple birth

**Status: lean/general.** Under NoParallel and an explicitly unique concurrent supporting triple, moving its incident line in the specified sign direction produces exactly one germ birth. The resulting identity retains the exact global loss count; it asserts no universal bound of two on losses.

- [Kobon.OpenMathTripleBirth.tiny_triangle_germ, line 64](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathTripleBirth.lean#L64)
- [Kobon.OpenMathIsolatedTripleResolution.unique_birth_card, line 69](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathIsolatedTripleResolution.lean#L69)
- [Kobon.OpenMathIsolatedTripleResolution.isolated_resolution_identity, line 78](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathIsolatedTripleResolution.lean#L78)

### om:four-line — Exact four-line counterexample to the specified half-plane yield formula

**Status: lean/general.** For y=0, y=x, y=-x, 2x+y=2, the sole triple point is isolated and all other vertices ordinary. Both old triangle interiors have x-y>0. Replacing y=x by y=x+epsilon for every0<epsilon<1 leaves exactly two triangles although the stated moved-side half-plane count is zero and Liu v1 Theorem1.1 predicts three. This refutes only that formula within its stated scope, not unrelated claims in the preprint.

- [Kobon.OpenMathFourLineResolution.old_unique_triple, line 99](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathFourLineResolution.lean#L99)
- [Kobon.OpenMathFourLineResolution.old_interiors_positive, line 156](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathFourLineResolution.lean#L156)
- [Kobon.OpenMathFourLineResolution.negative_count_zero, line 168](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathFourLineResolution.lean#L168)
- [Kobon.OpenMathFourLineResolution.moved_count, line 142](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathFourLineResolution.lean#L142)
- [Kobon.OpenMathFourLineResolution.halfplane_yield_fails, line 190](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathFourLineResolution.lean#L190)
- [research/openmath-seven-hour-2026-10-05/corpus/DESINGULARIZATION_AUDIT.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/corpus/DESINGULARIZATION_AUDIT.md#L1)

### om:six-line — Exact six-line translation and reverse wall crossing

**Status: lean/general.** For the explicit six-line arrangement and every0<epsilon<1/100, the old count is6, upward resolution gives7 and downward resolution4. The latter loses three alternating old triangles and creates one; its reverse gains two. The entire open intervals, NoParallel and old isolated triple are kernel proved with standard axioms.

- [Kobon.OpenMathSixLineResolution.old_count, line 548](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSixLineResolution.lean#L548)
- [Kobon.OpenMathSixLineResolution.up_count, line 557](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSixLineResolution.lean#L557)
- [Kobon.OpenMathSixLineResolution.down_count, line 566](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSixLineResolution.lean#L566)
- [Kobon.OpenMathSixLineResolution.reversal_gain_two, line 570](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSixLineResolution.lean#L570)
- [Kobon.OpenMathSixLineResolution.downward_breaks_three, line 579](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSixLineResolution.lean#L579)
- [Kobon.OpenMathSixLineResolution.old_unique_triple, line 612](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathSixLineResolution.lean#L612)

### om:analytic-checkers — Standard analytic boxes and sound finite-check infrastructure

**Status: lean/general.** Actual tan(k*pi/60), k=1..29 and tan(k*pi/36), k=1..17 are enclosed by explicit rational bounds using standard analytic lemmas and kernel arithmetic. Memoized Boolean and sparse integer box checks are proved extensionally equal/sound for the original geometric predicates. Executed finite seed equalities retain their separate native trust.

- [Kobon.BBLTangent60Bounds.tan_1_bounds, line 108](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangent60Bounds.lean#L108)
- [Kobon.BBLTangent60Bounds.tan_29_bounds, line 243](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangent60Bounds.lean#L243)
- [Kobon.BBLTangent36Bounds.tan_1_bounds, line 16](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangent36Bounds.lean#L16)
- [Kobon.BBLTangent36Bounds.tan_17_bounds, line 272](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/BBLTangent36Bounds.lean#L272)
- [Kobon.OpenMathConstructionBooleanMemo.simple_sound, line 57](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionBooleanMemo.lean#L57)
- [Kobon.OpenMathConstructionBooleanMemo.triangles_sound, line 79](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionBooleanMemo.lean#L79)
- [Kobon.OpenMathConstructionBooleanMemo.visibles_sound, line 102](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathConstructionBooleanMemo.lean#L102)
- [Kobon.OpenMathIntegerSparseBoxes.support_card_le_three, line 59](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathIntegerSparseBoxes.lean#L59)
- [Kobon.OpenMathIntegerSparseBoxes.simpleSparse_sound, line 108](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/OpenMathIntegerSparseBoxes.lean#L108)

### om:cell41-dual — Exact prescribed 41-line sign-cell dual obstruction

**Status: computation.** An exact small-epsilon positive-dependence certificate excludes only the exported normalized41-line sign cell. The concrete coefficients and checks are external exact arithmetic; the general StrictLinearCertificate lemma does not turn this specific41-line artifact into a Lean theorem. No all 41-arrangement impossibility is claimed.

- [research/openmath-seven-hour-2026-10-05/constructions/parametric-farkas-cell41.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/constructions/parametric-farkas-cell41.json#L1)

### om:equality-analysis — Remaining zero-component saturation analysis

**Status: manuscript/research-plan.** The equality decomposition and saturated poor-profile reduction are mathematical analysis recorded after the N12 and local-port proofs. The R22-to-N13 and R22-to-R04 boundary coupling cases remain unproved. N13's own affine-maximum exclusion does not exclude it as a neighbor of an R22 maximum. No new Lean equality theorem or unconditional positive component correction is inferred.

- [research/openmath-seven-hour-2026-10-05/constructions/remaining-zero-component-analysis.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/constructions/remaining-zero-component-analysis.md#L1)

### om:searches — Source-pinned bounded construction and curvature experiments

**Status: computation + external-input.** The retained cap-cone, fixed-axis nesting, corridor insertion, deletion, projective-chart, LP and mutation screens specify their inputs and search limits. Their failures do not prove general infeasibility or nonstretchability. Exact counterexamples refute selected shared-side/token/independence shortcuts; abstract finite charging equality graphs are not thereby geometrically realizable. Primary contestant sources and individual input credits are preserved rather than adopting the judging archive as a theorem oracle.

- [research/openmath-seven-hour-2026-10-05/corpus/TECHNIQUES_AND_OBSTRUCTIONS.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/corpus/TECHNIQUES_AND_OBSTRUCTIONS.md#L1)
- [research/openmath-seven-hour-2026-10-05/corpus/source-inventory.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/corpus/source-inventory.json#L1)
- [research/openmath-seven-hour-2026-10-05/seed_search/STRUCTURAL_PROBES.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/research/openmath-seven-hour-2026-10-05/seed_search/STRUCTURAL_PROBES.md#L1)

## Every retained finite coordinate identity

Repeated orders with different coordinate hashes are separate identities. Counts alone do not establish priority; original input attribution is preserved in the linked certificate and data records.

| Order | Triangles | Simple | Coordinate SHA-256 prefix | Lean certificate |
|---:|---:|:---:|---|---|
| 3 | 1 | yes | `05c82de62571155d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N003T00001H05c82de6.lean#L20); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N003T00001H05c82de6.lean#L10) |
| 4 | 2 | yes | `0e541bd5bbe7bee9` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N004T00002H0e541bd5.lean#L22); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N004T00002H0e541bd5.lean#L10) |
| 5 | 5 | yes | `948a0bdf2dd3be69` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N005T00005H948a0bdf.lean#L26); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N005T00005H948a0bdf.lean#L10) |
| 6 | 7 | yes | `6ea9ebaa7bf29c8c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N006T00007H6ea9ebaa.lean#L29); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N006T00007H6ea9ebaa.lean#L10) |
| 7 | 11 | yes | `e6b9a626a163e528` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N007T00011He6b9a626.lean#L34); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N007T00011He6b9a626.lean#L10) |
| 8 | 14 | yes | `2a63f4d9308d7a6d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N008T00014H2a63f4d9.lean#L38); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N008T00014H2a63f4d9.lean#L10) |
| 9 | 21 | yes | `6ebbed82d06399ea` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N009T00021H6ebbed82.lean#L46); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N009T00021H6ebbed82.lean#L10) |
| 10 | 25 | yes | `b767c427fa30087d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N010T00025Hb767c427.lean#L51); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N010T00025Hb767c427.lean#L10) |
| 11 | 32 | yes | `b955e7c9923ad0f9` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N011T00032Hb955e7c9.lean#L59); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N011T00032Hb955e7c9.lean#L10) |
| 12 | 38 | no | `38f69f38009707d8` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N012T00038H38f69f38.lean#L66) |
| 13 | 47 | yes | `ddec1f78855078d4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N013T00047Hddec1f78.lean#L76); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N013T00047Hddec1f78.lean#L10) |
| 14 | 53 | yes | `45157b2f20fe49b1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00053H45157b2f.lean#L83); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N014T00053H45157b2f.lean#L10) |
| 15 | 65 | yes | `4d3bf3b46db579eb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N015T00065H4d3bf3b4.lean#L96); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N015T00065H4d3bf3b4.lean#L10) |
| 16 | 72 | yes | `391cf79afe243177` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N016T00072H391cf79a.lean#L104); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N016T00072H391cf79a.lean#L10) |
| 17 | 85 | yes | `7cf3c061a447ff3f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N017T00085H7cf3c061.lean#L118); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N017T00085H7cf3c061.lean#L10) |
| 18 | 93 | yes | `edb6246a6de7d974` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N018T00093Hedb6246a.lean#L127); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N018T00093Hedb6246a.lean#L10) |
| 19 | 107 | yes | `a2f32bdbcd1ea442` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N019T00107Ha2f32bdb.lean#L142); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N019T00107Ha2f32bdb.lean#L10) |
| 20 | 116 | yes | `adc03eed024d9f01` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N020T00116Hadc03eed.lean#L152); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N020T00116Hadc03eed.lean#L10) |
| 21 | 133 | yes | `36bae754f19804b0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N021T00133H36bae754.lean#L170); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N021T00133H36bae754.lean#L10) |
| 22 | 143 | yes | `54396c646a7b60c1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N022T00143H54396c64.lean#L181); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N022T00143H54396c64.lean#L10) |
| 23 | 161 | yes | `969ad7d3adaf5833` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N023T00161H969ad7d3.lean#L200); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N023T00161H969ad7d3.lean#L10) |
| 24 | 172 | yes | `e63e906b99030e8b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N024T00172He63e906b.lean#L212); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N024T00172He63e906b.lean#L10) |
| 25 | 191 | yes | `b568bffb5a197067` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N025T00191Hb568bffb.lean#L232); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N025T00191Hb568bffb.lean#L10) |
| 26 | 203 | yes | `e61b423c7c3d7b55` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N026T00203He61b423c.lean#L245); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N026T00203He61b423c.lean#L10) |
| 27 | 225 | yes | `7d6ae9a04c46543f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N027T00225H7d6ae9a0.lean#L268); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N027T00225H7d6ae9a0.lean#L10) |
| 28 | 238 | yes | `56ef2acb9edd6a94` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N028T00238H56ef2acb.lean#L282); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N028T00238H56ef2acb.lean#L10) |
| 29 | 261 | yes | `d4805c25a121d33b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N029T00261Hd4805c25.lean#L306); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N029T00261Hd4805c25.lean#L10) |
| 30 | 275 | yes | `dcfe649a79cf71f0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N030T00275Hdcfe649a.lean#L321); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N030T00275Hdcfe649a.lean#L10) |
| 31 | 299 | yes | `70f23b9463cb77cb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N031T00299H70f23b94.lean#L346); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N031T00299H70f23b94.lean#L10) |
| 32 | 314 | yes | `9ab78b00c233bf92` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N032T00314H9ab78b00.lean#L362); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N032T00314H9ab78b00.lean#L10) |
| 33 | 341 | yes | `95f3b770119e6301` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N033T00341H95f3b770.lean#L390); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N033T00341H95f3b770.lean#L10) |
| 34 | 357 | yes | `fbde0a760c6e9c21` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N034T00357Hfbde0a76.lean#L407); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N034T00357Hfbde0a76.lean#L10) |
| 35 | 385 | yes | `9ee99af6b980c0b9` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N035T00385H9ee99af6.lean#L436); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N035T00385H9ee99af6.lean#L10) |
| 36 | 402 | yes | `3fc01b7d2a1ce99e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N036T00402H3fc01b7d.lean#L454); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N036T00402H3fc01b7d.lean#L10) |
| 37 | 431 | yes | `11f0bde7bac3eddf` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N037T00431H11f0bde7.lean#L484); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N037T00431H11f0bde7.lean#L10) |
| 38 | 449 | yes | `46ad5a32af834f7d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N038T00449H46ad5a32.lean#L503); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N038T00449H46ad5a32.lean#L10) |
| 39 | 469 | no | `cf24d7d33c00f6e1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N039T00469Hcf24d7d3.lean#L524) |
| 40 | 494 | yes | `785374ca691bcc56` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N040T00494H785374ca.lean#L550); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N040T00494H785374ca.lean#L10) |
| 41 | 533 | yes | `01e2ef66f8fdeceb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N041T00533H01e2ef66.lean#L590); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N041T00533H01e2ef66.lean#L10) |
| 42 | 553 | yes | `2bdc9d67365a3ec1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N042T00553H2bdc9d67.lean#L611); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N042T00553H2bdc9d67.lean#L10) |
| 43 | 587 | yes | `861d8be27deed6d3` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N043T00587H861d8be2.lean#L646); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N043T00587H861d8be2.lean#L10) |
| 44 | 608 | yes | `b5277675e356739f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N044T00608Hb5277675.lean#L668); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N044T00608Hb5277675.lean#L10) |
| 45 | 645 | yes | `3dc6e882e9b83723` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N045T00645H3dc6e882.lean#L706); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N045T00645H3dc6e882.lean#L10) |
| 46 | 667 | yes | `32b8ca2f231ddf83` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N046T00667H32b8ca2f.lean#L729); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N046T00667H32b8ca2f.lean#L10) |
| 47 | 690 | yes | `d8af27fc13d18221` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N047T00690Hd8af27fc.lean#L753); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N047T00690Hd8af27fc.lean#L10) |
| 48 | 720 | yes | `5e9767e73b31c34c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N048T00720H5e9767e7.lean#L784); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N048T00720H5e9767e7.lean#L10) |
| 49 | 767 | yes | `957e6f151a57c598` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N049T00767H957e6f15.lean#L832); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N049T00767H957e6f15.lean#L10) |
| 50 | 791 | yes | `2ea22b558bf879c5` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N050T00791H2ea22b55.lean#L857); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N050T00791H2ea22b55.lean#L10) |
| 51 | 817 | no | `bd215f67ab1067d2` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N051T00817Hbd215f67.lean#L884) |
| 52 | 850 | yes | `4b0d823a1fa89bb4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N052T00850H4b0d823a.lean#L918); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N052T00850H4b0d823a.lean#L10) |
| 53 | 884 | yes | `723d7eff8d45b6dd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N053T00884H723d7eff.lean#L953); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N053T00884H723d7eff.lean#L10) |
| 54 | 918 | yes | `915abb8ed17c1286` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N054T00918H915abb8e.lean#L988); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N054T00918H915abb8e.lean#L10) |
| 55 | 954 | yes | `ea7675d9b8a30ae0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N055T00954Hea7675d9.lean#L1025); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N055T00954Hea7675d9.lean#L10) |
| 56 | 990 | yes | `de8a415c9b297a67` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N056T00990Hde8a415c.lean#L1062); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N056T00990Hde8a415c.lean#L10) |
| 57 | 1045 | yes | `9a1d337c75ba6de1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N057T01045H9a1d337c.lean#L1118); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N057T01045H9a1d337c.lean#L10) |
| 58 | 1073 | yes | `d988db55253084b0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N058T01073Hd988db55.lean#L1147); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N058T01073Hd988db55.lean#L10) |
| 59 | 1102 | yes | `fd3b4280376ea0f4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N059T01102Hfd3b4280.lean#L1177); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N059T01102Hfd3b4280.lean#L10) |
| 60 | 1140 | yes | `16af6d0b260ee2bb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N060T01140H16af6d0b.lean#L1216); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N060T01140H16af6d0b.lean#L10) |
| 12 | 37 | yes | `8c718a334b7bed0f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N012T00037H8c718a33.lean#L65); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N012T00037H8c718a33.lean#L10) |
| 39 | 468 | yes | `5c5b0b26ee2241d2` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N039T00468H5c5b0b26.lean#L523); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N039T00468H5c5b0b26.lean#L10) |
| 51 | 816 | yes | `6fa6b7d91d28819b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N051T00816H6fa6b7d9.lean#L883); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N051T00816H6fa6b7d9.lean#L10) |
| 5 | 3 | yes | `6265d6a7c5576172` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N005T00003H6265d6a7.lean#L24); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N005T00003H6265d6a7.lean#L10) |
| 6 | 4 | yes | `7e060e9a0ac15660` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N006T00004H7e060e9a.lean#L26); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N006T00004H7e060e9a.lean#L10) |
| 19 | 107 | yes | `5d2a7588c1e2ddfd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N019T00107H5d2a7588.lean#L142); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N019T00107H5d2a7588.lean#L10) |
| 21 | 126 | yes | `f18756b727918616` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N021T00126Hf18756b7.lean#L163); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N021T00126Hf18756b7.lean#L10) |
| 5 | 5 | yes | `dd0748b7cdfb14f7` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N005T00005Hdd0748b7.lean#L26); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N005T00005Hdd0748b7.lean#L10) |
| 7 | 10 | yes | `4b5bb6e99d6224c4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N007T00010H4b5bb6e9.lean#L33); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N007T00010H4b5bb6e9.lean#L10) |
| 21 | 132 | yes | `3d8bae2fa7295d74` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N021T00132H3d8bae2f.lean#L169); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N021T00132H3d8bae2f.lean#L10) |
| 22 | 142 | yes | `e683945e66cdf396` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N022T00142He683945e.lean#L180); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N022T00142He683945e.lean#L10) |
| 41 | 532 | yes | `6d48a3411f413135` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N041T00532H6d48a341.lean#L589); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N041T00532H6d48a341.lean#L10) |
| 42 | 552 | yes | `7b29a6bd1191f25d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N042T00552H7b29a6bd.lean#L610); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N042T00552H7b29a6bd.lean#L10) |
| 81 | 2132 | yes | `7bc6b303744fa706` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N081T02132H7bc6b303.lean#L2229); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N081T02132H7bc6b303.lean#L10) |
| 82 | 2172 | yes | `d75c9101c8a5c62b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N082T02172Hd75c9101.lean#L2270); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N082T02172Hd75c9101.lean#L10) |
| 161 | 8532 | yes | `230691d59eee84b4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N161T08532H230691d5.lean#L8709); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N161T08532H230691d5.lean#L10) |
| 162 | 8612 | yes | `1512e69660740eae` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N162T08612H1512e696.lean#L8790); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N162T08612H1512e696.lean#L10) |
| 9 | 19 | no | `e16410b887ee5bb8` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N009T00019He16410b8.lean#L44) |
| 15 | 61 | no | `7c38d54f9e52590b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N015T00061H7c38d54f.lean#L92) |
| 21 | 127 | no | `b8dcff224cdbe59b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N021T00127Hb8dcff22.lean#L164) |
| 27 | 217 | no | `6670a2b142843e2a` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N027T00217H6670a2b1.lean#L260) |
| 33 | 331 | no | `25fd8f0c3311d01e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N033T00331H25fd8f0c.lean#L380) |
| 48 | 715 | no | `ba6f5baae76d20ff` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N048T00715Hba6f5baa.lean#L779) |
| 99 | 3169 | no | `4fef38d87d0c5550` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N099T03169H4fef38d8.lean#L3284) |
| 195 | 12481 | no | `cd3497dbf8468a75` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N195T12481Hcd3497db.lean#L12692) |
| 195 | 12480 | yes | `1b9230fb738a2ca6` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N195T12480H1b9230fb.lean#L12691); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N195T12480H1b9230fb.lean#L10) |
| 44 | 602 | yes | `0b0250bf6213b6ae` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N044T00602H0b0250bf.lean#L662); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N044T00602H0b0250bf.lean#L10) |
| 99 | 3168 | yes | `a0ea30825a737b92` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N099T03168Ha0ea3082.lean#L3283); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N099T03168Ha0ea3082.lean#L10) |
| 39 | 470 | yes | `30caa6f7f89472aa` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N039T00470H30caa6f7.lean#L525); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N039T00470H30caa6f7.lean#L10) |
| 47 | 691 | yes | `fac44af18c558b7a` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N047T00691Hfac44af1.lean#L754); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N047T00691Hfac44af1.lean#L10) |
| 48 | 721 | yes | `2fb5ef0df4cf6a93` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N048T00721H2fb5ef0d.lean#L785); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N048T00721H2fb5ef0d.lean#L10) |
| 51 | 818 | yes | `c18e1baf25f50900` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N051T00818Hc18e1baf.lean#L885); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N051T00818Hc18e1baf.lean#L10) |
| 53 | 885 | yes | `6bc5b14d0b68627c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N053T00885H6bc5b14d.lean#L954); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N053T00885H6bc5b14d.lean#L10) |
| 54 | 919 | yes | `a254c1b4f05b17a1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N054T00919Ha254c1b4.lean#L989); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N054T00919Ha254c1b4.lean#L10) |
| 55 | 955 | yes | `202625a3908524c7` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N055T00955H202625a3.lean#L1026); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N055T00955H202625a3.lean#L10) |
| 59 | 1103 | yes | `ba482375103b9e14` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N059T01103Hba482375.lean#L1178); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N059T01103Hba482375.lean#L10) |
| 60 | 1141 | yes | `9bc5096cc3fd10a0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N060T01141H9bc5096c.lean#L1217); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N060T01141H9bc5096c.lean#L10) |
| 65 | 1365 | yes | `b1dcbeb4ff39eb3b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N065T01365Hb1dcbeb4.lean#L1446); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N065T01365Hb1dcbeb4.lean#L10) |
| 66 | 1397 | yes | `327ecbb9b7bafefe` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N066T01397H327ecbb9.lean#L1479); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N066T01397H327ecbb9.lean#L10) |
| 99 | 3170 | yes | `ea507e2de1372dd8` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N099T03170Hea507e2d.lean#L3285); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N099T03170Hea507e2d.lean#L10) |
| 129 | 5461 | yes | `6dae0012aa49d5cf` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N129T05461H6dae0012.lean#L5606); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N129T05461H6dae0012.lean#L10) |
| 130 | 5525 | yes | `e0559b54aee5366e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N130T05525He0559b54.lean#L5671); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N130T05525He0559b54.lean#L10) |
| 195 | 12482 | yes | `5413dd7b60ee64bf` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N195T12482H5413dd7b.lean#L12693); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N195T12482H5413dd7b.lean#L10) |
| 14 | 54 | no | `d47aea63afc13985` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hd47aea63.lean#L84) |
| 14 | 54 | no | `18bbcff4f43351df` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H18bbcff4.lean#L84) |
| 14 | 54 | no | `78f750c071a5610e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H78f750c0.lean#L84) |
| 14 | 54 | no | `912da8ec9bc76efd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H912da8ec.lean#L84) |
| 14 | 54 | no | `9134999072a9cae0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H91349990.lean#L84) |
| 14 | 54 | no | `9c871e103a465b86` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H9c871e10.lean#L84) |
| 14 | 54 | no | `b3dcae0bc1d84132` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hb3dcae0b.lean#L84) |
| 14 | 54 | no | `9219cdaa6f90ac3b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H9219cdaa.lean#L84) |
| 14 | 54 | no | `d2babc1b9431b2fb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hd2babc1b.lean#L84) |
| 14 | 54 | no | `2b34ca22dc8980b3` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H2b34ca22.lean#L84) |
| 14 | 54 | no | `fa427b3d27ef501f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hfa427b3d.lean#L84) |
| 14 | 54 | no | `1ec1fd5cb2ee863c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H1ec1fd5c.lean#L84) |
| 14 | 54 | no | `3e5d182f84085aae` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H3e5d182f.lean#L84) |
| 14 | 54 | no | `17f8c0524eb16e50` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H17f8c052.lean#L84) |
| 14 | 54 | no | `c472f97237f10e5e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054Hc472f972.lean#L84) |
| 14 | 52 | yes | `2eb83dc242a1a606` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00052H2eb83dc2.lean#L82); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N014T00052H2eb83dc2.lean#L10) |
| 14 | 53 | yes | `5e6068f5003e0ecd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00053H5e6068f5.lean#L83); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N014T00053H5e6068f5.lean#L10) |
| 14 | 52 | yes | `b3f4749f6dee6452` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00052Hb3f4749f.lean#L82); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N014T00052Hb3f4749f.lean#L10) |
| 14 | 52 | yes | `c6615430ae3d4cc4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00052Hc6615430.lean#L82); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N014T00052Hc6615430.lean#L10) |
| 8 | 14 | yes | `ebff58687458ee11` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N008T00014Hebff5868.lean#L38); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N008T00014Hebff5868.lean#L10) |
| 14 | 51 | yes | `d67e7a6b3b089546` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00051Hd67e7a6b.lean#L81); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N014T00051Hd67e7a6b.lean#L10) |
| 20 | 114 | yes | `bc312fc85ea5d6aa` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N020T00114Hbc312fc8.lean#L150); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N020T00114Hbc312fc8.lean#L10) |
| 26 | 203 | yes | `5452b4ffa1a9f082` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N026T00203H5452b4ff.lean#L245); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N026T00203H5452b4ff.lean#L10) |
| 32 | 313 | yes | `018f9fc6b73f13a7` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N032T00313H018f9fc6.lean#L361); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N032T00313H018f9fc6.lean#L10) |
| 38 | 448 | yes | `7d59f504aba872af` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N038T00448H7d59f504.lean#L502); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N038T00448H7d59f504.lean#L10) |
| 50 | 791 | yes | `6bde86a3dcbdd30a` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N050T00791H6bde86a3.lean#L857); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N050T00791H6bde86a3.lean#L10) |
| 8 | 15 | no | `a138081033c3b257` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N008T00015Ha1380810.lean#L39) |
| 14 | 54 | no | `105765145381c27d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N014T00054H10576514.lean#L84) |
| 20 | 117 | no | `382171ac62ccad67` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N020T00117H382171ac.lean#L153) |
| 26 | 204 | no | `f71379c4db0380d0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N026T00204Hf71379c4.lean#L246) |
| 32 | 315 | no | `5914f2bb88d115ce` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N032T00315H5914f2bb.lean#L363) |
| 36 | 402 | yes | `ce43a1077597aac1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N036T00402Hce43a107.lean#L454); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N036T00402Hce43a107.lean#L10) |
| 38 | 450 | no | `8ba2bdb14e85b408` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N038T00450H8ba2bdb1.lean#L504) |
| 42 | 553 | yes | `9849e255d5da63f0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N042T00553H9849e255.lean#L611); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N042T00553H9849e255.lean#L10) |
| 50 | 792 | no | `3d40cb58261638e6` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N050T00792H3d40cb58.lean#L858) |
| 19 | 107 | yes | `6e8ca6f56a85d29d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N019T00107H6e8ca6f5.lean#L142); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/SimpleCertificates/N019T00107H6e8ca6f5.lean#L10) |
| 6 | 6 | no | `af8f599eb8a15e6d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/f44f23ee062a255f5cad7d39188fd55c0feb83a8/Kobon/Certificates/N006T00006Haf8f599e.lean#L28) |
