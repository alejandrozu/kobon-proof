# Result-to-proof map for both October manuscripts

Audited 3 October 2026. Every mathematical/evidence link is pinned to `2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8`.

This map preserves all **89 previous claim identities** and **138 finite coordinate identities** (104 simple), and adds the completed recursion, upper geometry, exact obstructions, conditional and unfinished branches. It is not a claim that every manuscript argument is formalized in Lean.

The concrete odd/even recursive families, actual incidence and clean-line charging, classical simple upper bounds, one-triangle simple optimality windows, and the explicit ten-sign obstruction are now proved. Exterior-boundary quantitative charging and whole-arrangement cyclic-fan assembly remain partly ordinary mathematics. The 33/49 uniform seed drafts remain unverified as complete seeds.

**Trust.** Standard proofs use only `propext`, `Classical.choice`, and `Quot.sound`. Native descendants additionally trust Lean's compiler/runtime; the concrete odd/even family inherits four/six existing native checks. A conditional Lean theorem proves its implication, not automatic satisfaction of every hypothesis. The sign-cell/component interpretation includes the manuscript's elementary topology argument.

The [successful release verification](https://github.com/alejandrozu/kobon-proof/actions/runs/37056093885) covers 375 active Lean files and 270 build targets; the axiom audit lists 5241 theorems (4405 standard-only, 836 native descendants). These are audit counts, not mathematical-discovery counts.

The [machine-readable map](proof_map.json) binds every declaration line to its source SHA-256 and immutable Git blob. Rebuild with `python manuscripts/2026-10-03/shared/build_proof_map.py`; validate without editing with `python manuscripts/2026-10-03/shared/validate_proof_map.py`.

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

- [Kobon.Universal.baseline_sound, line 26](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L26)
- [Kobon.Universal.baseline_improvement, line 72](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L72)

### j:G — Closed formula for G

**Status: lean/general.** The definition handles n<3 and n=3; the stated floor formula is baseline_formula for n>=4. Natural division is floor division.

- [Kobon.Universal.baseline, line 11](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L11)
- [Kobon.Universal.baseline_formula, line 59](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L59)

### j:cell — Certified triangular interiors and disjointness

**Status: partial.** Under global NoParallel, Lean proves nonempty triangle interiors, equality with the strict sign cell, and pairwise disjointness. The manuscript's ordinary convexity and connected-component argument supplies the topological interpretation. The October wording uses the global nonparallel hypothesis rather than enlarging the Lean theorem.

- [Kobon.Cells.interior_nonempty, line 461](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Cells.lean#L461)
- [Kobon.Cells.interior_eq_signCell, line 486](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Cells.lean#L486)
- [Kobon.Cells.distinct_interiors_disjoint, line 453](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Cells.lean#L453)

### j:sign — Trigonometric determinant and oriented evaluation identities

**Status: lean/general.** Symbolic identities for arbitrary real angles.

- [Kobon.FurediPalasti.det_line, line 13](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalasti.lean#L13)
- [Kobon.FurediPalasti.oriented_line, line 123](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalasti.lean#L123)

### j:residues — Selected triples and classical affine count

**Status: lean/general.** The two sets of residue classes yield certified triangles and the classical count. No numerical novelty is claimed for the older half-phase construction.

- [Kobon.FurediPalasti.selected_triangle, line 186](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalasti.lean#L186)
- [Kobon.ShiftedFurediPalasti.selected_triangle, line 144](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/ShiftedFurediPalasti.lean#L144)
- [Kobon.FurediPalastiCount.ordered_bound, line 186](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalastiCount.lean#L186)
- [Kobon.FurediPalasti.lower_bound, line 301](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalasti.lean#L301)

### j:phase — Phase correction

**Status: lean/general.** Actual simple real arrangements for every n>=3 with floor(n(n-3)/3)+1 triangles; the repeated-index saving is separately proved.

- [Kobon.ShiftedFurediPalasti.simple_lower_bound, line 274](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/ShiftedFurediPalasti.lean#L274)
- [Kobon.ShiftedCount.ordered_bound_plus, line 59](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/ShiftedCount.lean#L59)

### j:covariance — Projective change of chart

**Status: lean/general.** Exact determinant/evaluation covariance and triangle preservation under the stated cut inequalities.

- [Kobon.Projective.det_transform, line 14](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Projective.lean#L14)
- [Kobon.Projective.eval_transform, line 19](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Projective.lean#L19)
- [Kobon.Projective.oriented_transform, line 25](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Projective.lean#L25)
- [Kobon.Projective.triangle_preserved, line 111](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Projective.lean#L111)
- [Kobon.Projective.triangle_preserved_negative, line 138](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Projective.lean#L138)

### j:caps — One-cap and two-cap constructions

**Status: lean/general.** The one-cap theorem uses n=2m+1 with m>=1. The two-cap theorem uses n=6k+3 with k>=1. Both construct simple real arrangements.

- [Kobon.FurediPalastiWrap.one_cap_simple_lower_bound, line 191](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalastiWrap.lean#L191)
- [Kobon.FurediPalastiTwoCaps.two_cap_simple_lower_bound, line 282](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalastiTwoCaps.lean#L282)

### j:gap — Exact gap to the classical comparison polynomial

**Status: lean/general.** Arithmetic identity only; this does not formalize the external upper-bound theorem or prove it unrestrictedly.

- [Kobon.Universal.polynomial_gap_exact, line 90](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L90)

### j:envelope — Finite-enhanced lower envelope

**Status: lean/general.** Universal.all_n proves max(G, AllN.bound); AllN.bound is max of the older baseline and a finite certified enhancement. Since G dominates the older baseline, this equals the paper's max(G, C). The identification of C with the external certificate catalog is checked by the manifest/catalog, rather than C being a directly parsed Lean definition. This theorem imports finite native_decide certificates and therefore has their additional runtime trust.

- [Kobon.Universal.all_n, line 117](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L117)
- [Kobon.Universal.classical_baseline_le, line 63](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L63)
- [Kobon.AllN.dominates_every_saved_certificate, line 255](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/AllN.lean#L255)

### j:after195 — Saved envelope equals G after order 195

**Status: lean/general.** Immediate combination of AllN.baseline_after_last_exception, Universal.classical_baseline_le and the definition Universal.bound; no separately named combined theorem. Does not assert optimality after 195.

- [Kobon.AllN.baseline_after_last_exception, line 465](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/AllN.lean#L465)
- [Kobon.Universal.classical_baseline_le, line 63](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L63)
- [Kobon.Universal.bound, line 112](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L112)

### j:44equality — Simple optimum K_s(44)=608

**Status: lean/derived.** The retained finite SimpleLowerBound 44 608 certificate and the now-formalized simple even upper theorem imply exact simple optimality by substitution 44*(2*44-5)/6=608. This is an immediate mathematical corollary of the linked Lean theorems; there is no separately named 44-line optimality wrapper. It makes no nonsimple optimality or first numerical priority claim.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L461)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### j:old-q-family — G supersedes the earlier q=6*2^t additional-line formula

**Status: manuscript.** The identity G(q+3)=q^2/3+q+2 follows by substitution into the verified formula; no dedicated theorem for this exact q-family identity was found. It is an arithmetic consequence, not a new formalized generic extension mechanism.

- [Kobon.Universal.baseline_formula, line 59](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L59)
- [Kobon.Universal.strict_odd_multiples, line 143](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L143)

### j:certificate-soundness — Integer certificate validation

**Status: lean/general.** Integer sign checks lift to real nonparallel lines and distinct uncut triangular support triples. Simplicity is separately checked. Finite checked instances use native_decide.

- [Kobon.validate_sound, line 135](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Geometry.lean#L135)
- [Kobon.validate_simple_sound, line 39](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Simple.lean#L39)

### jup:shared-fan — Six actual triangles with six distinct shared elementary radial sides

**Status: lean/finite.** The fixed six integer lines and six supporting triples are kernel-checked. Lean proves the lifted real triangles, distinct supporting triples, triple center, six distinct nonzero elementary radial segments, and that each radial segment is a side of two distinct triangles. This is a finite formal counterexample to a literal local bound of two incident shared sides, not to a global Kobon upper theorem. SharedFan does not separately enumerate all possible triangles or formalize the local classification d1=d2=3.

- [Kobon.SharedFan.integerLines, line 17](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L17)
- [Kobon.SharedFan.integer_triangles, line 27](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L27)
- [Kobon.SharedFan.real_triangles, line 32](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L32)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L51)
- [Kobon.SharedFan.adjacent_triangles_distinct, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L58)
- [Kobon.SharedFan.center_is_triple, line 61](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L61)
- [Kobon.SharedFan.radial_segments_injective, line 105](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L105)
- [Kobon.SharedFan.radial_elementary, line 113](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L113)

### j:finite — Table 1: selected simple certificates

**Status: lean/finite.** Each individual simple lower bound is proved through the finite certificate pipeline (native_decide). Improvements are relative to earlier project witnesses, not claims of first numerical priority or global optimality.

- [Kobon.Results.best_simple_028, line 429](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L429)
- [Kobon.Results.best_simple_030, line 433](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L433)
- [Kobon.Results.best_simple_034, line 441](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L441)
- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L461)
- [Kobon.Results.best_simple_039, line 451](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L451)
- [Kobon.Results.best_simple_047, line 467](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L467)
- [Kobon.Results.best_simple_048, line 469](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L469)
- [Kobon.Results.best_simple_051, line 475](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L475)
- [Kobon.Results.best_simple_053, line 479](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L479)
- [Kobon.Results.best_simple_054, line 481](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L481)
- [Kobon.Results.best_simple_055, line 483](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L483)
- [Kobon.Results.best_simple_059, line 491](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L491)
- [Kobon.Results.best_simple_060, line 493](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L493)
- [Kobon.Results.best_simple_099, line 503](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L503)
- [Kobon.Results.best_simple_195, line 513](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L513)

### j:finite-28 — Simple 28-line certificate with at least 238 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_028, line 429](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L429)

### j:finite-30 — Simple 30-line certificate with at least 275 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_030, line 433](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L433)

### j:finite-34 — Simple 34-line certificate with at least 357 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_034, line 441](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L441)

### j:finite-44 — Simple 44-line certificate with at least 608 cells

**Status: lean/finite.** Finite lower bound only; the optimum assertion additionally needs Blanc's external upper theorem. Uses native_decide.

- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L461)

### j:finite-39 — Simple 39-line certificate with at least 470 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_039, line 451](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L451)

### j:finite-47 — Simple 47-line certificate with at least 691 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_047, line 467](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L467)

### j:finite-48 — Simple 48-line certificate with at least 721 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_048, line 469](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L469)

### j:finite-51 — Simple 51-line certificate with at least 818 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_051, line 475](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L475)

### j:finite-53 — Simple 53-line certificate with at least 885 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_053, line 479](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L479)

### j:finite-54 — Simple 54-line certificate with at least 919 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_054, line 481](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L481)

### j:finite-55 — Simple 55-line certificate with at least 955 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_055, line 483](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L483)

### j:finite-59 — Simple 59-line certificate with at least 1103 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_059, line 491](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L491)

### j:finite-60 — Simple 60-line certificate with at least 1141 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_060, line 493](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L493)

### j:finite-99 — Simple 99-line certificate with at least 3170 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_099, line 503](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L503)

### j:finite-195 — Simple 195-line certificate with at least 12482 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_195, line 513](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Results.lean#L513)

### j:maiorana-inputs — Fifteen Maiorana 14-line certificates

**Status: lean/finite.** All fifteen imported coordinate identities have Lean lower-bound certificates (native_decide), each with 54 cells. Discovery credit remains Maiorana. This does not establish an unrestricted optimum.

- [Kobon.Certificates.N014T00054Hd47aea63.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hd47aea63.lean#L84)
- [Kobon.Certificates.N014T00054H18bbcff4.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H18bbcff4.lean#L84)
- [Kobon.Certificates.N014T00054H78f750c0.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H78f750c0.lean#L84)
- [Kobon.Certificates.N014T00054H912da8ec.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H912da8ec.lean#L84)
- [Kobon.Certificates.N014T00054H91349990.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H91349990.lean#L84)
- [Kobon.Certificates.N014T00054H9c871e10.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H9c871e10.lean#L84)
- [Kobon.Certificates.N014T00054Hb3dcae0b.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hb3dcae0b.lean#L84)
- [Kobon.Certificates.N014T00054H9219cdaa.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H9219cdaa.lean#L84)
- [Kobon.Certificates.N014T00054Hd2babc1b.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hd2babc1b.lean#L84)
- [Kobon.Certificates.N014T00054H2b34ca22.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H2b34ca22.lean#L84)
- [Kobon.Certificates.N014T00054Hfa427b3d.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hfa427b3d.lean#L84)
- [Kobon.Certificates.N014T00054H1ec1fd5c.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H1ec1fd5c.lean#L84)
- [Kobon.Certificates.N014T00054H3e5d182f.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H3e5d182f.lean#L84)
- [Kobon.Certificates.N014T00054H17f8c052.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H17f8c052.lean#L84)
- [Kobon.Certificates.N014T00054Hc472f972.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hc472f972.lean#L84)

### j:pu-gallery — Ten Parpalak-Utkin gallery witnesses

**Status: lean/finite.** Ten gallery coordinate identities have Lean lower-bound certificates (native_decide), including 26:204 and 50:792. Discovery credit remains the original authors. The separate complete recount uses independent exact programs.

- [Kobon.Certificates.N046T00667H32b8ca2f.lower_bound, line 729](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N046T00667H32b8ca2f.lean#L729)
- [Kobon.Certificates.N008T00015Ha1380810.lower_bound, line 39](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N008T00015Ha1380810.lean#L39)
- [Kobon.Certificates.N014T00054H10576514.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H10576514.lean#L84)
- [Kobon.Certificates.N020T00117H382171ac.lower_bound, line 153](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N020T00117H382171ac.lean#L153)
- [Kobon.Certificates.N026T00204Hf71379c4.lower_bound, line 246](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N026T00204Hf71379c4.lean#L246)
- [Kobon.Certificates.N032T00315H5914f2bb.lower_bound, line 363](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N032T00315H5914f2bb.lean#L363)
- [Kobon.Certificates.N036T00402Hce43a107.lower_bound, line 454](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N036T00402Hce43a107.lean#L454)
- [Kobon.Certificates.N038T00450H8ba2bdb1.lower_bound, line 504](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N038T00450H8ba2bdb1.lean#L504)
- [Kobon.Certificates.N042T00553H9849e255.lower_bound, line 611](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N042T00553H9849e255.lean#L611)
- [Kobon.Certificates.N050T00792H3d40cb58.lower_bound, line 858](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N050T00792H3d40cb58.lean#L858)

### jext:visible — Verified exterior realization

**Status: lean/general.** Actual real-coordinate simple arrangement with T plus the length of an explicit duplicate-free visible-pair list. Admissibility and beyond-all-vertices height are explicit geometric hypotheses. No parity restriction or future-count assumption.

- [Kobon.Exterior.extension, line 164](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Exterior.lean#L164)
- [Kobon.Exterior.safeHeight_beyond, line 191](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Exterior.lean#L191)

### jext:defect — Boundary-defect extension proposition

**Status: partial.** The manuscript proves ray charging and identifies geometric wedges with cyclic data. Lean proves the finite cyclic averaging and conditional defect arithmetic; no end-to-end real-arrangement extension theorem with this defect gain is present.

- [KobonBoundary.cap_mass, line 20](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L20)
- [KobonBoundary.exists_average, line 35](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L35)
- [KobonBoundary.charging_bound, line 75](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L75)
- [KobonBoundary.defect_extension_bound, line 79](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L79)

### jext:gain — Both-parity defect gain formula

**Status: partial.** The cyclic inequality in Lean assumes the three-wedge and boundary inequalities. Iteration.defectGain implements the rounded formula as a definition; its geometric interpretation depends on the manuscript's unformalized extraction and charging arguments.

- [KobonBoundary.defect_extension_bound, line 79](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L79)

### jext:odd-near-perfect — Odd inputs of defect at most two admit full gain

**Status: partial.** Lean proves the finite cyclic consequence assuming the boundary inequality and a wedge set; the passage from an arbitrary simple Euclidean arrangement to this cyclic data remains a manuscript argument.

- [KobonBoundary.odd_full_gain, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L51)
- [KobonBoundary.near_perfect_odd_extension, line 89](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BoundaryExtension.lean#L89)

### jext:budget — Exterior wedge budget and obstruction to indefinite full gains

**Status: partial.** The resource inequality and cumulative geometric bound are manuscript proofs. Lean proves the contradiction conditional on the resource inequality and full gains; it does not extract the wedge budget from geometry.

- [Kobon.Iteration.no_infinite_full_gain_budget, line 105](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration.lean#L105)
- [Kobon.Iteration.two_steps_49_obstruction, line 121](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration.lean#L121)

### jext:figure — The 49-line seed successor chain and sector capacities

**Status: partial.** Exact coordinate-to-profile audit plus Lean finite cyclic profile maxima. The values 24, 23, 2, 2, 2 belong to these saved arrangements and are not upper bounds for the maximum function. The real-coordinate identification of the finite arrays is performed by the independent audit script, not Lean.

- [Kobon.Iteration49.profile_bound_49, line 13](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration49.lean#L13)
- [Kobon.Iteration49.profile_attains_49, line 16](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration49.lean#L16)
- [Kobon.Iteration49.profile_bound_50, line 21](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration49.lean#L21)
- [Kobon.Iteration49.profile_bound_51, line 29](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration49.lean#L29)
- [Kobon.Iteration49.profile_bound_52, line 37](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration49.lean#L37)
- [Kobon.Iteration49.profile_bound_53, line 45](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration49.lean#L45)
- [scripts/audit_successor_chain.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/scripts/audit_successor_chain.py#L1)
- [experiments/2026-09-20/successor-49/chain.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-20/successor-49/chain.json#L1)

### jext:conditional-iteration — Closed form conditional on the full successor recurrence

**Status: partial.** Fully proved arithmetic implication with FullStepClaim K visibly assumed. It does not establish that recurrence for the Kobon maximum function.

- [Kobon.Iteration.gainPrefix_closed, line 31](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration.lean#L31)
- [Kobon.Iteration.full_step_iteration, line 59](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration.lean#L59)
- [Kobon.Iteration.from_49_conditional, line 76](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Iteration.lean#L76)

### jext:49 — Unconditional 49-seed numerical target for all n at least 49

**Status: lean/general.** Unconditional real geometric lower bound floor((n-1)^2/4)+191, obtained from saved 49/50 certificates and the all-order classical baseline for n at least 51. It does not produce a nested full-gain chain.

- [Kobon.AllN.from_49_unconditional, line 504](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/AllN.lean#L504)
- [Kobon.Universal.dominates_49_target, line 125](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Universal.lean#L125)

### jfam:doubling — Verified one-step geometric BBL construction

**Status: lean/general.** One actual real-coordinate simple arrangement step for q=4r with r at least 5, positive small epsilon, saturated ordered tangent-grid input, positive central apex, and a duplicate-free certified triangle list. Produces SimpleLowerBound (2q+1) (T+q^2). Does not return the recursive compatible seed invariant, and does not include the initial q=10 step.

- [Kobon.BBLDoubling.doubling, line 15](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLDoubling.lean#L15)

### jfam:seed11 — Uniform real eleven-line seed and five-pair exterior extension

**Status: lean/general.** For every real 0<epsilon<=10^-5, actual simple real arrangement with 32 triangles, nine distinguished triangles, and five visible pairs; actual exterior arrangement with 12 lines and 37 triangles. These seed computations use kernel evaluation, with proved interval and trigonometric bounds.

- [Kobon.SeedFamily.simple_lower_bound, line 115](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SeedFamily.lean#L115)
- [Kobon.SeedFamily.distinguished_triangles, line 108](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SeedFamily.lean#L108)
- [Kobon.SeedFamily.arbitrarily_small, line 121](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SeedFamily.lean#L121)
- [Kobon.HybridBoundary.seed_visible, line 138](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/HybridBoundary.lean#L138)
- [Kobon.HybridBoundary.seed_exterior, line 148](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/HybridBoundary.lean#L148)

### jfam:families — Completed odd and stronger even q=10*2^t geometric families

**Status: lean/general.** For every natural t, q=10*2^t gives actual simple real-line witnesses of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. All geometric seed and visibility hypotheses are discharged. At each finite depth the proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even families inherit four/six existing native checks, respectively. BBL doubling is inherited; the completed recursive formalization is not a new numerical-record claim.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L51)

### jfam:strong-even — Stronger even family T_q+q/2

**Status: lean/general.** For every natural t, q=10*2^t gives actual simple real-line witnesses of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. All geometric seed and visibility hypotheses are discharged. At each finite depth the proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even families inherit four/six existing native checks, respectively. BBL doubling is inherited; the completed recursive formalization is not a new numerical-record claim.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L51)

### jfam:seed21 — Uniform real 21-line true-grid seed

**Status: lean/general.** For every real 0<epsilon<=10^-5, the verified parameter arrangement has 132 certified triangles, 19 distinguished triangles, and 10 visible pairs; exterior extension yields 22:142. Finite interval checks in this module use native_decide, so compiler/runtime trust supplements the Lean kernel.

- [Kobon.BBLSeed21.simple_lower_bound, line 163](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21.lean#L163)
- [Kobon.BBLSeed21.all_distinguished, line 108](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21.lean#L108)
- [Kobon.BBLSeed21.distinguished_count, line 115](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21.lean#L115)
- [Kobon.BBLSeed21.all_visible, line 100](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21.lean#L100)
- [Kobon.BBLSeed21.exterior_lower_bound, line 168](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21.lean#L168)
- [Kobon.BBLSeed21.arbitrarily_small, line 179](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21.lean#L179)

### jfam:recursive-components — Next-grid saturation and sorting permutation

**Status: lean/general.** The recursive seed record now closes under actual geometric doubling, including the grid, saturation, positive apex, simplicity, triangle-list transport and exterior visibility. The generic theorems retain an explicit uniform seed premise; the concrete 21-line seed discharges it.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLRecursiveSeed.seed_step, line 61](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveSeed.lean#L61)
- [Kobon.BBLEvenRecursive.visible_seed_step, line 9](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenRecursive.lean#L9)
- [Kobon.BBLInfinite.uniform_iterate, line 32](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L32)
- [Kobon.BBLEvenInfinite.uniform_iterate, line 27](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenInfinite.lean#L27)

### jfam:seed5 — Corrected uniform five-line normalization

**Status: lean/general.** For every real 0<epsilon<=10^-5, five triangles, three distinguished triangles, two visible pairs, and exterior extension to 6:7 are proved; this does not itself formalize the whole inherited dyadic optimal family.

- [Kobon.TamuraSeed5.simple_lower_bound, line 113](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/TamuraSeed5.lean#L113)
- [Kobon.TamuraSeed5.all_distinguished, line 59](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/TamuraSeed5.lean#L59)
- [Kobon.TamuraSeed5.all_visible, line 64](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/TamuraSeed5.lean#L64)
- [Kobon.TamuraSeed5.exterior_lower_bound, line 118](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/TamuraSeed5.lean#L118)
- [Kobon.TamuraSeed5.arbitrarily_small, line 129](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/TamuraSeed5.lean#L129)

### jfam:large-completed — 321:34132, 322:34292 and 641:136532

**Status: lean/general + computation.** The numerical lower bounds 321:34132, 322:34292 and 641:136532 are now consequences of the complete infinite Lean families. The previously saved coordinate files independently passed two external exact counters, but are not thereby retroactively included in the finite Lean certificate catalog.

Previous map status: `computation`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L51)
- [experiments/2026-09-21/hybrid-family/larger-members-verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/hybrid-family/larger-members-verification.json#L1)

### jfam:large-incomplete — 642:136852 existence proved; old individual coordinate verification remains separate

**Status: lean/general + pending-coordinate-check.** The existence of a simple 642-line arrangement with 136852 triangles is now proved by the infinite even family. The earlier saved 642-line coordinate file's unfinished second counter remains unfinished; the existence theorem does not certify that particular file.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L51)
- [experiments/2026-09-21/hybrid-family/large-run-status.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/hybrid-family/large-run-status.json#L1)

### jfam:chart-obstruction — Fixed 81- and 161-line seeds admit no chart-only count improvement

**Status: computation.** Exact projective face census equals bounded triangle count for these particular saved seeds. This is a finite exact program calculation, not a Lean theorem or a restriction on other arrangements of the same size.

- [experiments/2026-09-20/chart_search.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-20/chart_search.py#L1)
- [research/kobon-hybrid/certificates/n081.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/kobon-hybrid/certificates/n081.json#L1)
- [research/kobon-hybrid/certificates/n161.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/kobon-hybrid/certificates/n161.json#L1)

### jfam:seed19 — Parpalak-Utkin 19-line interval seed reproduction

**Status: computation.** Exact interval calculation for 107 triangles and 17 distinguished triangles for 0<epsilon<=10^-3. The uniform interval calculation is not a Lean theorem. A single rational specialization is separately in the finite Lean catalogue; attribution to Parpalak-Utkin remains.

- [research/six-hour-2026-09-21/general-bounds/prior-seed19-interval.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/prior-seed19-interval.json#L1)
- [research/six-hour-2026-09-21/general-bounds/prior-seed19-rational.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/prior-seed19-rational.json#L1)

### jfam:inherited-families — q=4*2^t and q=18*2^t inherited odd families and even companions

**Status: external.** The odd geometric families retain Forge-Ramirez Alfonsin and Parpalak-Utkin attribution respectively; the paper's even companions use the manuscript boundary-defect argument. No new all-family Lean theorem is claimed.


### jfam:finite-11 — 11:32 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N011T00032Hb955e7c9.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N011T00032Hb955e7c9.lean#L10)

### jfam:finite-12 — 12:37 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N012T00037H8c718a33.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N012T00037H8c718a33.lean#L10)

### jfam:finite-21 — 21:132 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N021T00132H3d8bae2f.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N021T00132H3d8bae2f.lean#L10)

### jfam:finite-22 — 22:142 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N022T00142He683945e.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N022T00142He683945e.lean#L10)

### jfam:finite-41 — 41:532 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N041T00532H6d48a341.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N041T00532H6d48a341.lean#L10)

### jfam:finite-42 — 42:552 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N042T00552H7b29a6bd.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N042T00552H7b29a6bd.lean#L10)

### jfam:finite-81 — 81:2132 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N081T02132H7bc6b303.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N081T02132H7bc6b303.lean#L10)

### jfam:finite-82 — 82:2172 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N082T02172Hd75c9101.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N082T02172Hd75c9101.lean#L10)

### jfam:finite-161 — 161:8532 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N161T08532H230691d5.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N161T08532H230691d5.lean#L10)

### jfam:finite-162 — 162:8612 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N162T08612H1512e696.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N162T08612H1512e696.lean#L10)

### jup:section — Scope of multiplicity-sensitive upper estimates

**Status: manuscript.** All global upper assertions in this section concern even n>=4 distinct pairwise nonparallel affine lines and the total number of bounded triangular cells. They are ordinary geometric theorems in the stated subclasses, not unconditional Lean upper bounds for the unrestricted Kobon problem. The referenced source files agree with immutable source commit 99fdc8ec1ef8b1fb22c3da32b011b7361762e958.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)
- [research/six-hour-2026-09-21/general-bounds/multiplicity-budget.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/multiplicity-budget.md#L1)

### jup:identity — Elementary-segment incidence and defect identities

**Status: lean/general.** For n>=2 pairwise nonparallel actual real lines and any finite injective certified triangle family, Lean extracts the actual vertices, bounded elementary segments, shared endpoints and multiplicities, and proves E=n(n-2)-S, 3T=E-U+D1+D2 and delta=S+U-D1-D2. Unused/shared are relative to the selected family, which need not enumerate all triangular cells. No global incidence identity is assumed.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon.UpperEdgeInventory.edge_cardinality, line 188](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L188)
- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L345)
- [Kobon.UpperTriangleIncidence.certificate_incidence, line 230](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTriangleIncidence.lean#L230)
- [Kobon.UpperSharedEdge.Pair.not_both_endpoints_ordinary, line 98](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSharedEdge.lean#L98)

### jup:clean — Clean-line parity and charging inequality

**Status: lean/general.** For even n>=4 pairwise nonparallel real lines and any finite injective certified triangle family, n-h<=2U+D1 is extracted from actual clean-line crossings and bounded-edge pairing. The charge map and its finite fibers are proved, without a charging hypothesis. This upper-bound charging is distinct from the still partly formalized exterior-boundary gain argument.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCharging.lean#L100)
- [Kobon.UpperCleanCover.certificate_clean_line_charge, line 401](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCover.lean#L401)

### jup:budget — Combined clean-line defect budget

**Status: lean/derived.** The earlier combined defect budget follows by algebra from the actual extracted defect identity and clean-line charging. The linked arithmetic lemma can now receive these geometric inputs; it is not an unrestricted improved numerical upper bound without the remaining fan estimate.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.CleanLineBudget.parity_budget, line 18](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L18)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)
- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L345)
- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCharging.lean#L100)

### jup:parallel-obstruction — Why simply excluding parallel-participating lines does not repair charging

**Status: manuscript.** The three-parallel-verticals plus one-horizontal example shows that the horizontal line can be clean while all transverse pieces at its crossings are unbounded. This is a direct geometric counterexample to the attempted local argument with that weakened hypothesis, not a claimed counterexample to Blanc's theorem.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:fan — Fan bounds at an r-fold point

**Status: lean/conditional-interface.** The local real-geometry cyclic-fan interfaces prove d1<=2r-3 and 3d1+d2<=6r-6. The new equality analysis proves that d1=2r-3 forces every sector triangular and exactly d2=3, so d2<=2 implies d1<=2r-4. Whole-arrangement extraction and matching of these interfaces remains unfinished, independently of the completed incidence and charging theorems.

Previous map status: `partial`. The new scope above controls the October claim.

- [Kobon.UpperFan.Sectors.ordinary_shared_card_le, line 166](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L166)
- [Kobon.UpperFan.Sectors.core_shared_card_eq_three_of_extremal, line 187](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L187)
- [Kobon.UpperFan.Sectors.ordinary_shared_card_le_of_core_le_two, line 202](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L202)
- [Kobon.UpperFan.Sectors.weighted_local_bound, line 227](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L227)

### jup:fan-propagation — Opposite-support propagation along an actual geometric fan

**Status: lean/general.** At an ordinary radial endpoint, any two other indexed incident lines coincide. For a FanStrip of actual real points and indexed supporting lines, all opposite supporting lines agree and the two outer endpoints cannot lie on opposite rays from the center. No aggregate run-bound conclusion is assumed. The input FanStrip explicitly supplies incidences, ordinary internal endpoints, nondegenerate triangles and opposite lines avoiding the center.

- [Kobon.FanGeometry.ordinary_nonradial_unique, line 24](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanGeometry.lean#L24)
- [Kobon.FanGeometry.FanStrip, line 47](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanGeometry.lean#L47)
- [Kobon.FanGeometry.FanStrip.ofTriangles, line 65](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanGeometry.lean#L65)
- [Kobon.FanGeometry.FanStrip.all_opposites_eq, line 113](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanGeometry.lean#L113)
- [Kobon.FanGeometry.no_opposite_end_fan, line 160](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanGeometry.lean#L160)

### jup:fan-local-count — Actual cyclic fan has no long selected run and at most 2r-3 selected rays

**Status: lean/general.** For r>=3 and Geometry n r L, no r-1 consecutive selected ordinary shared rays can occur, and selected.card<=2*r-3. Geometry supplies 2r actual radial endpoints with antipodal partners, ordinary selected endpoints and the actual opposite supporting lines of adjacent triangular sectors. The no-long-run property is proved, not assumed; automatic construction of Geometry from a whole arrangement is not in these declarations.

- [Kobon.CyclicFan.Geometry, line 20](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CyclicFan.lean#L20)
- [Kobon.CyclicFan.Geometry.no_long_run, line 44](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CyclicFan.lean#L44)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CyclicFan.lean#L96)

### jup:fan-window — Cyclic window count used in the fan proof

**Status: lean/general.** For a Finset S in ZMod(2*r), r>=3, and an explicit missing selected ray in every window of length r-1, ordinary_shared_ray_bound proves S.card<=2*r-3. Its proof establishes the intermediate double-count inequality (r-1)*S.card<=2*r*(r-2). The intermediate inequality is not separately named, but window_bound is a named helper. CyclicFan supplies the run premise from actual geometry.

- [Kobon.FanCount.window_bound, line 18](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanCount.lean#L18)
- [Kobon.FanCount.ordinary_shared_ray_bound, line 37](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FanCount.lean#L37)
- [Kobon.CyclicFan.Geometry.no_long_run, line 44](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CyclicFan.lean#L44)

### jup:fan-sharp — Sharper actual local fan theorem for at most two core-ended shared rays

**Status: lean/conditional-interface.** The stronger local statement d2<=2 implies d1<=2r-4 is now proved for an explicit actual cyclic Sectors interface. This includes the earlier d2<=1 case. Whole-arrangement construction and incidence matching of every fan remain separate obligations.

Previous map status: `manuscript`. The new scope above controls the October claim.

- [Kobon.UpperFan.Sectors.ordinary_shared_card_le_of_core_le_two, line 202](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L202)

### jup:upper — Restricted upper-estimate theorem

**Status: partial.** The complete theorem about actual even pairwise nonparallel arrangements is a manuscript theorem. Its global edge incidence, charging, fan extraction and sharper d2<=1 arguments are not all in Lean. The weighted and at-most-two-core integer deductions have formal conditional counterparts; neither is an unconditional upper theorem about all Euclidean arrangements.

- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L73)
- [Kobon.CleanLineBudget.at_most_two_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L58)
- [Kobon.CleanLineBudget.triangles_from_defect, line 106](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L106)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:weighted — Weighted defect inequality for arbitrary core size

**Status: partial.** The manuscript proves 2*delta>=n+sum_{r>=3}(2*r^2-11*r+6)*t_r. The formal general_multiplicity_budget proves n+2*S-7*I+6*q<=2*delta from explicit integer incidence, charging, core-incidence h<=I, fan-run D1<=2*I-3*q, and fan-ray D1+2*D2<=2*I premises. The connection of those sums and premises to an arbitrary arrangement remains ordinary geometry.

- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L73)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CyclicFan.lean#L96)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:two-core — At most two finite multiple points: upper polynomial plus one

**Status: partial.** For even n=2*m>=4 and at most two core points, the manuscript proves T<=floor(n*(n-5/2)/3)+1. The integer theorem at_most_two_multiple_points proves m-3<=delta assuming the incidence identity, charging, D1<=2*I-4*q, h<=I-D2, D2<=1, q between 0 and 2, and weighted surplus 0<=2*S-7*I+15*q. multiplicity_surplus proves the local surplus polynomial for r>=3. triangles_from_defect proves the corresponding inequality 3*T<=n*(n-2)-m+3; rounding to the displayed floor is ordinary arithmetic here.

- [Kobon.CleanLineBudget.multiplicity_surplus, line 50](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L50)
- [Kobon.CleanLineBudget.at_most_two_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L58)
- [Kobon.CleanLineBudget.triangles_from_defect, line 106](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L106)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:zero-one-core — Sharper zero-core and one-core defects

**Status: partial.** The manuscript gives delta>=n/2 when q=0 and delta>=n/2-1 when q=1, including a single core point of any multiplicity. Lean one_triple_point proves only the single TRIPLE-point conditional arithmetic case, from incidence, charging, D1<=2 and h<=3. It must not be cited as a direct theorem for one core point of arbitrary multiplicity. The general manuscript proof uses the surplus polynomial and integer parity.

- [Kobon.CleanLineBudget.one_triple_point, line 40](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L40)
- [Kobon.CleanLineBudget.multiplicity_surplus, line 50](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L50)
- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L73)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:high-multiplicity — Simple-style polynomial under nonnegative total core weight

**Status: partial.** The manuscript consequence T<=floor(n*(n-5/2)/3) holds if the total weight sum(2*r^2-11*r+6)*t_r is nonnegative, in particular if every core multiplicity is at least five. Lean high_multiplicity_weight proves the local weight is at least one for r>=5; nonnegative_core_weight proves n<=2*delta from an explicit nonnegative weight and the other abstract geometric budgets. The weights -9 at r=3 and -6 at r=4 are direct arithmetic and show why this does not cover arbitrary low-multiplicity cores.

- [Kobon.CleanLineBudget.high_multiplicity_weight, line 85](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L85)
- [Kobon.CleanLineBudget.nonnegative_core_weight, line 92](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/CleanLineBudget.lean#L92)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:attainment — Externally attributed exact attainment at 8, 14, 26 and 50 lines

**Status: partial.** The lower witnesses 8:15, 14:54, 26:204 and 50:792 are Lean-certified finite lower bounds. Their exact full triangle counts, nonparallel status and exactly two triple points are documented by exact computational censuses; the generic lower_bound declarations do not assert upper bounds or core cardinalities. The 14-line example must be Maiorana certificate-01 (or another two-triple Maiorana example), NOT the PU gallery 14-line witness, which has five triple points. Equality with the restricted manuscript upper theorem proves sharpness only in its stated subclass. Discovery attributions remain external.

- [Kobon.Certificates.N008T00015Ha1380810.lower_bound, line 39](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N008T00015Ha1380810.lean#L39)
- [Kobon.Certificates.N014T00054Hd47aea63.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hd47aea63.lean#L84)
- [Kobon.Certificates.N026T00204Hf71379c4.lower_bound, line 246](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N026T00204Hf71379c4.lean#L246)
- [Kobon.Certificates.N050T00792H3d40cb58.lower_bound, line 858](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N050T00792H3d40cb58.lean#L858)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/verification.json#L1)
- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/verification.json#L1)

### jup:figure — Shared-fan figure and geometric certificate

**Status: lean/finite.** The six depicted cells have nonempty, uncut and pairwise disjoint open interiors in Lean; each highlighted radial segment is elementary and shared by the appropriate two cells. The caption's formal claim is supported in this constructive sense. Exhaustivity of the complete triangle census and the endpoint-type count d1=d2=3 are exact computational additions, not named SharedFan theorems.

- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L51)
- [Kobon.SharedFan.interiors_uncut, line 66](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L66)
- [Kobon.SharedFan.interiors_nonempty, line 70](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L70)
- [Kobon.SharedFan.interiors_disjoint, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L73)
- [Kobon.SharedFan.radial_elementary, line 113](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L113)
- [research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json#L1)

### jup:shared-fan-census — Exact shared-fan census and endpoint types

**Status: computation.** The exact arrangement counter finds exactly six triangular cells, four triple points, and at the center (1, 1) six incident shared segments split as d1=3 and d2=3. This complete census is reproducible from the six coordinates; it is not an exhaustive-count theorem in SharedFan. The six certified cells and elementary sides themselves are formally established.

- [research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json#L1)
- [experiments/2026-09-21/general-bounds/shared_fan_counterexample.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/general-bounds/shared_fan_counterexample.py#L1)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L51)

### jup:clement-reading — Scope of the Clément–Bader wording objection

**Status: external.** The recorded source audit identifies page 2, Lemma 1 item 3 of the OEIS-hosted Clément–Bader draft. The six-side example refutes only a literal local incidence reading; it neither disproves the draft's final theorem nor rules out a corrected global assignment argument. This bibliographical/interpretive claim is not a Lean theorem.

- [research/six-hour-2026-09-21/general-bounds/upper-bound-scope-audit.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/upper-bound-scope-audit.md#L1)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SharedFan.lean#L51)

### jup:smoothing-maiorana — Four exact local resolutions of Maiorana's 14:54 witness

**Status: computation.** Maiorana certificate-01 has precisely the two zero triple determinants on supports {0, 4, 10} and {0, 11, 12}. The independent offsets realize all four resolution-sign choices, preserve every initially nonzero triple-determinant sign and leave pair directions fixed; exact triangle counts are 52, 52, 53, 52. The script checks each resolution by adjacency and the independent interior-sign verifier. This finite enumeration is not a Lean theorem.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)
- [experiments/2026-09-21/general-bounds/maiorana_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/general-bounds/maiorana_resolutions.py#L1)

### jup:smoothing-classification — Exhaustion of sufficiently small simple perturbations

**Status: manuscript.** Finite continuity preserves all initially nonzero pair-direction and triple-determinant signs. The two formerly zero triple signs exhaust the possible nearby simple chirotopes, all represented in the exact enumeration; hence every sufficiently small simple perturbation of this fixed 14-line input has at most 53 triangular cells. The sign-stability/classification argument is ordinary geometry, not Lean, and makes no statement about distant arrangements.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [experiments/2026-09-21/general-bounds/maiorana_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/general-bounds/maiorana_resolutions.py#L1)

### jup:smoothing-gallery — All 132 recorded local resolutions of seven gallery inputs

**Status: computation.** The saved exact reports contain 4+32+64+4+16+8+4=132 resolutions for n=8, 14, 20, 26, 32, 38, 50. Their maxima are respectively 14, 51, 114, 203, 313, 448, 791. Private-line offsets realize every binary local choice; the verifier checks all originally nonzero determinant signs, simplicity and equality of the two exact triangle sets. These are fixed-input computations, not a formalized general smoothing theorem or an upper bound on arbitrary simple arrangements.

- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/collinear-resolution-model.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/collinear-resolution-model.json#L1)
- [experiments/2026-09-21/general-bounds/collinear_resolution.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/general-bounds/collinear_resolution.py#L1)
- [experiments/2026-09-21/general-bounds/check_collinear_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/experiments/2026-09-21/general-bounds/check_collinear_resolutions.py#L1)

### jup:smoothing-loss — Failure of nondecreasing and loss-at-most-one local smoothing shortcuts

**Status: computation.** For the fixed Maiorana input the best nearby simple count drops from 54 to 53, ruling out universal nondecreasing local smoothing. For the PU gallery 14- and 20-line types the exact local maxima drop by three, and at 32 and 38 by two, ruling out universal loss-at-most-one local resolution. Transfer from exhaustive sign choices to all sufficiently small perturbations uses the stated manuscript continuity argument; no global lower or upper optimum is changed.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)

### jup:formalization-status — Boundary between completed formal components and remaining global geometry

**Status: partial.** Completed: elementary-side extraction, side capacity, multiplicity and defect identities, core incidences, actual clean-line charging, both classical simple upper bounds, actual local fan rigidity and sharper local counts. Remaining: canonical whole-arrangement cyclic-fan extraction, matching across shared edges and global summation for the proposed general nonsimple bounds. Conditional aggregate arithmetic is not an unconditional new upper theorem.

- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L345)
- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCharging.lean#L100)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L69)
- [Kobon.UpperCoreBoundary.CoreFamily.sum_ordinary_bound, line 75](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBoundary.lean#L75)

### j:trig — Classical trigonometric line family

**Status: lean/general.** This is the definition used in the formal construction, inherited from Furedi-Palasti rather than a new family.

- [Kobon.FurediPalasti.line, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/FurediPalasti.lean#L10)

### j:blanc — Blanc's simple even-order upper bound

**Status: lean/general; inherited theorem.** The classical simple even bound T<=floor(n(2n-5)/6) is now proved from actual geometry for every SimpleLowerBound witness of even n>=4. Blanc's prior mathematical result remains attributed; this release adds its complete formalization. The simplicity hypothesis is essential.

Previous map status: `external`. The new scope above controls the October claim.

- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_upper, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L56)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### jfam:recursive — Closed geometric recursive seed and visibility invariants

**Status: lean/general.** For every natural t, q=10*2^t gives actual simple real-line witnesses of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. All geometric seed and visibility hypotheses are discharged. At each finite depth the proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even families inherit four/six existing native checks, respectively. BBL doubling is inherited; the completed recursive formalization is not a new numerical-record claim.

- [Kobon.BBLRecursiveSeed.seed_step, line 61](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveSeed.lean#L61)
- [Kobon.BBLEvenRecursive.visible_seed_step, line 9](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenRecursive.lean#L9)
- [Kobon.BBLInfinite.uniform_iterate, line 32](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L32)
- [Kobon.BBLInfinite.infinite_family, line 46](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L46)
- [Kobon.BBLInfinite.triangleCount_identity, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L52)
- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L51)

### jfam:windows — Actual one-triangle optimality windows for simple arrangements

**Status: lean/general.** For each q=10*2^t both family counts are attainable in simple arrangements, and every SimpleLowerBound witness at the same order has at most the constructed count plus one. Upper halves use only standard axioms; existence inherits the recorded native checks. The window is specific to simple arrangements and need not mean that exact optimum is unknown at every small order.

- [Kobon.BBLFamilyOptimality.odd_window, line 29](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyOptimality.lean#L29)
- [Kobon.BBLFamilyOptimality.even_window, line 35](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyOptimality.lean#L35)

### j:new-envelope — All-natural-order envelope retaining the completed recursive families

**Status: lean/general.** H(n)=max(B(n), L(n)) is a LowerBound for every natural n, where B is the former finite-enhanced envelope and L selects the two recursive family counts. A finite maximum over t<n+1 implements the definition. H>=B everywhere and strictly exceeds B on both dyadic tails from orders 321 and 322. These are gains over the previous verified repository envelope, not claims of improving all published constructions.

- [Kobon.RecursiveEnvelope.all_n, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L51)
- [Kobon.RecursiveEnvelope.previous_le, line 57](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L57)
- [Kobon.RecursiveEnvelope.strict_previous_tail, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L73)

### j:new-envelope-formula — Executable formula for the retained recursive envelope

**Status: lean/general.** Definitions candidate, familyBound and bound implement the displayed finite maximum; the two sparse branches select q+1 and q+2 respectively, and all other candidates are zero.

- [Kobon.RecursiveEnvelope.candidate, line 12](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L12)
- [Kobon.RecursiveEnvelope.familyBound, line 25](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L25)
- [Kobon.RecursiveEnvelope.bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L49)

### j:new-gains — Exact recursive improvements over G and the previous envelope

**Status: lean/general.** At q=10*2^t the odd/even family gains over G are respectively floor(q/3)-2 and q/2-floor(q/3)-2. B=G above 195; strict improvements hold for both tails t>=5. At321/322 gains are104/52, and at 641/642 they are211/105.

- [Kobon.BBLFamilyBenchmarks.odd_baseline_gain, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L52)
- [Kobon.BBLFamilyBenchmarks.even_baseline_gain, line 65](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L65)
- [Kobon.BBLFamilyBenchmarks.strict_previous_tail, line 152](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L152)

### long:envelope-gains — Exact gains of the new total envelope on its sparse tail

**Status: lean/derived.** Above order 195 the former envelope is G. The family-minus-G equalities and uniqueness of the matching sparse branch give the displayed exact H-minus-previous values. The repository proves the family differences and strict-tail comparison directly; no separate Lean wrapper for every exact H equality is asserted.

- [Kobon.BBLFamilyBenchmarks.odd_baseline_gain, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L52)
- [Kobon.BBLFamilyBenchmarks.even_baseline_gain, line 65](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L65)
- [Kobon.BBLFamilyBenchmarks.strict_previous_tail, line 152](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L152)
- [Kobon.RecursiveEnvelope.bound, line 49](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L49)
- [Kobon.RecursiveEnvelope.strict_previous_tail, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L73)

### jup:simple — Classical simple upper bounds extracted from actual geometry

**Status: lean/general.** Every SimpleLowerBound n T obeys 3T<=n(n-2) for n>=2; for even n>=4 it obeys 6T<=n(2n-5). Both conclusions and floor forms are kernel proofs. These formalize inherited simple-arrangement results, not new unrestricted upper bounds.

- [Kobon.UpperSimpleOptimality.simple_lower_bound_upper, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSimpleOptimality.lean#L58)
- [Kobon.UpperSimpleOptimality.simple_lower_bound_floor, line 70](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSimpleOptimality.lean#L70)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_upper, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L56)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### j:obstruction — Exact ten-sign impossibility on the 20-intercept tangent grid

**Status: lean/general.** One explicitly listed ten-sign orientation system is impossible for actual tangents and arbitrary real reciprocal slopes, for every real epsilon. The proof derives the quartic of tan(pi/20), identifies all required tangent values, and uses positive linear dependence. It does not classify all perfect21-line arrangements or imply K(21)<=132.

- [Kobon.BBLGridObstruction.actual_grid_orientation_impossible, line 263](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLGridObstruction.lean#L263)
- [Kobon.BBLGridObstruction.actual_grid_infeasible, line 240](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLGridObstruction.lean#L240)
- [Kobon.BBLTangentAlgebra.tan_quartic, line 20](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentAlgebra.lean#L20)
- [Kobon.BBLTangentAlgebra.tan_root_interval, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentAlgebra.lean#L51)
- [Kobon.StrictLinearCertificate.infeasible, line 25](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/StrictLinearCertificate.lean#L25)

### oct:grid21-coverage — Complete supplied affine-input obstruction audit

**Status: computation + external-input.** 3765 exact polynomial certificates and 15060 reflected/reoriented variants cover236 supplied Euclidean classes times21 distinguished supports=4956 normalizations, with no missing cases, for 0<epsilon<1/2000000. The checker independently validates signs and coverage for these inputs. Completeness of Parpalak-Utkin's classification is an external attributed premise, neither rerun nor formalized in Lean. The earlier18 projective representatives alone did not establish full affine coverage.

- [research/three-hour-2026-10-02/constructions/grid21-obstruction/README.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/constructions/grid21-obstruction/README.md#L1)
- [research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-verification.json#L1)

### oct:local-robustness — Ten-sign obstruction persists under small intercept perturbations

**Status: computation.** Exact outward interval elimination certifies independent perturbations of radius 1/1000 on the 11 used intercepts of the explicit representative. This robustness calculation is external and is not an all-grid or all-arrangement obstruction.

- [research/three-hour-2026-10-02/bbl/LOCAL_ROBUSTNESS.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/bbl/LOCAL_ROBUSTNESS.md#L1)

### j:exact49 — Uniform49-line compatibility certificate and its proof boundary

**Status: computation + partial.** Exact interval checks establish the prescribed49-line rational-slope/actual-tangent family with 767 triangles, 47 caps and 24 visible pairs throughout 0<epsilon<=1/100. Actual tangent enclosures are Lean theorems. The full finite native base check did not complete, so the 49-line normalized visible seed and its infinite family remain outside the active library. Target counts768*4^t-1 and 768*4^t+24*2^t-1 belong to a preexisting BBL family; they are not new numerical records.

- [research/three-hour-2026-10-02/bbl/SEED49_STATUS.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/bbl/SEED49_STATUS.md#L1)
- [research/three-hour-2026-10-02/constructions/uniform-grid49/uniform-seed.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/constructions/uniform-grid49/uniform-seed.json#L1)
- [research/three-hour-2026-10-02/constructions/uniform-grid49/visibility.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/constructions/uniform-grid49/visibility.json#L1)
- [Kobon.BBLTangent48Bounds.tan_48_1_bounds, line 203](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangent48Bounds.lean#L203)
- [Kobon.BBLTangent48Bounds.tan_48_23_bounds, line 308](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangent48Bounds.lean#L308)

### oct:forge33 — Forge-family formulas with the33-line seed still explicit

**Status: lean/conditional-interface.** Generic odd/even formulas are proved assuming UniformSeed8 341 and the corresponding uniform visible seed. The33-line native base check and normalization/visibility drafts did not complete. Numerical families are attributed to Forge-Ramirez Alfonsin and BBL, not to the legacy internal source name TamuraSeed33.

- [Kobon.BBLForgeConditional.odd_family, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L52)
- [Kobon.BBLForgeConditional.even_family, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L58)
- [Kobon.BBLForgeConditional.odd_polynomial_exact, line 95](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L95)
- [Kobon.BBLForgeConditional.even_simple_polynomial_exact, line 104](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L104)
- [research/three-hour-2026-10-02/drafts/README.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/drafts/README.md#L1)

### jup:sharp-fan — Rigid extremal local fans and the strengthened weighted inequality

**Status: lean/conditional-interface.** For a supplied actual cyclic fan, d1=2r-3 forces a full triangular fan and exactly three core-ended shared rays. Consequently d2<=2 implies d1<=2r-4, and 3d1+d2<=6r-8+2e. Extracting these local interfaces for every core of an arbitrary arrangement and identifying the global incidences remains unfinished.

- [Kobon.UpperFan.Sectors.all_sectors_of_extremal, line 171](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L171)
- [Kobon.UpperFan.Sectors.core_shared_card_eq_three_of_extremal, line 187](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L187)
- [Kobon.UpperFan.Sectors.ordinary_shared_card_le_of_core_le_two, line 202](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L202)
- [Kobon.UpperFan.Sectors.weighted_local_bound, line 227](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L227)

### oct:triple-fan — Matched extremal triple fans cannot be adjacent

**Status: lean/conditional-interface.** Actual full triple fans are incompatible under the explicit shared-edge matching hypotheses. The canonical global matching and rotation interface remains to be extracted.

- [Kobon.UpperTripleFan.extremal_triple_fans_not_adjacent, line 156](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTripleFan.lean#L156)
- [Kobon.UpperTripleFan.incompatible_full_triple_fans, line 65](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTripleFan.lean#L65)

### oct:core-budget — Stronger conditional weighted and at-most-three-core budgets

**Status: lean/conditional-interface.** Given the displayed aggregate fan bound, actual incidence and charging data imply 2delta>=n+2S-7I+8q-2e+D2. The small-core arithmetic gives delta>=m-6 for q<=3 and hence T<=floor(m(4m-5)/3)+2. Remaining geometric fan hypotheses prevent these from being unconditional new nonsimple upper theorems.

- [Kobon.UpperCoreBudget.weighted_defect_with_core_edges, line 47](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L47)
- [Kobon.UpperCoreBudget.at_most_three_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L58)
- [Kobon.UpperCoreBudget.triangles_from_three_core_defect, line 72](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L72)
- [Kobon.UpperCoreLineIncidence.core_line_budget, line 139](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreLineIncidence.lean#L139)
- [Kobon.UpperCoreCombinatorics.core_edge_count, line 35](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreCombinatorics.lean#L35)
- [Kobon.UpperCoreCombinatorics.core_surplus, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreCombinatorics.lean#L56)

### oct:next-proof-plan — Unformalized next-step deductions and research obligations

**Status: research-plan.** The degree-three independent exceptional-triple graph idea and inequalities 3e<=D2, 2delta>=n+2S-7I+8q+e and 6delta>=3n+6S-21I+24q+D2 are explicitly prospective deductions under missing global interfaces. They are not current Lean theorems and do not strengthen a retained exact correction without further information.

- [research/three-hour-2026-10-02/NEXT_PROOF_PLAN.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/NEXT_PROOF_PLAN.md#L1)

### oct:searches — Completed bounded construction searches

**Status: computation.** Saved deletion, chord insertion, singular insertion, straightening and grid-fitting searches produced the exact diagnostics recorded in the construction review, with no new numerical lower-bound record. Time-limited incumbents, failed fits and fixed-input obstructions do not establish unrestricted optimality or nonstretchability.

- [research/three-hour-2026-10-02/constructions/README.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/constructions/README.md#L1)

### oct:release — Complete active-source build and trust audit

**Status: verification-metadata.** 375 active Lean sources, 270 build targets and 5241 audited theorems:4405 use only standard logical axioms and 836 additionally descend from native evaluation. No active sorry, admit, unsafe declaration or custom geometric axiom is accepted. These are implementation audit counts, not discovery counts. Archived March source and October drafts are outside the active verified library.

- [verification/lean-summary.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/verification/lean-summary.json#L1)
- [FORMALIZATION.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/FORMALIZATION.md#L1)
- [research/three-hour-2026-10-02/RELEASE_VERIFICATION.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/research/three-hour-2026-10-02/RELEASE_VERIFICATION.md#L1)

### long:certificate-definitions — Coordinate definitions and affine orientation identity

**Status: lean/general.** The determinant, oriented vertex evaluation and TrianglePredicate definitions are formalized, and nonparallel affine intersections satisfy the displayed orientation identity.

- [Kobon.det, line 26](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Geometry.lean#L26)
- [Kobon.orientedEval, line 38](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Geometry.lean#L38)
- [Kobon.TrianglePredicate, line 44](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Geometry.lean#L44)
- [Kobon.orientedEval_affine, line 94](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Geometry.lean#L94)

### lit:classical-upper — Historical unrestricted upper benchmark

**Status: external.** The classical Tamura and Clement-Bader upper comparisons in the literature review are cited mathematical results. The repository's arithmetic comparisons with their polynomials do not constitute a formal proof of the unrestricted upper theorem.

- [paper/references.bib, line 1](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/paper/references.bib#L1)

### jup:exceptional — Conditional exceptional-fan correction

**Status: lean/conditional-interface.** Given the displayed summed fan premise, the actual incidence/charging/core inequalities yield 2delta>=n+2S-7I+8q+D2-2e. Global extraction of that fan premise is not proved.

- [Kobon.UpperCoreBudget.weighted_defect_with_core_edges, line 47](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L47)

### module:Permutation — Permutation supporting declarations

**Status: lean/general.** K. Actual triangle support and equal-length, duplicate-free witness transport under bounded label bijections/injections.

- [Kobon.Permutation.triangle_pullback_support, line 70](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Permutation.lean#L70)
- [Kobon.Permutation.transport_list, line 168](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Permutation.lean#L168)
- [Kobon.Permutation.transport_list_of_injective, line 189](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Permutation.lean#L189)

### module:BBLRecursiveWitness — BBLRecursiveWitness supporting declarations

**Status: lean/general.** K. From an actual simple saturated tangent-grid seed with positive central apex and r≥5, constructs the next simple arrangement, at least T+(4r)^2 triangles, the next saturated grid, and positive central apex. The epsilon bound is explicit.

- [Kobon.BBLRecursiveWitness.canonical_step, line 13](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveWitness.lean#L13)

### module:BBLRecursiveGrid — BBLRecursiveGrid supporting declarations

**Status: lean/general.** K. The actual coefficient identity and inverse label maps put the output on the next tangent grid.

- [Kobon.BBLRecursiveGrid.forward, line 9](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveGrid.lean#L9)
- [Kobon.BBLRecursiveGrid.backward, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveGrid.lean#L10)
- [Kobon.BBLRecursiveGrid.graph_reindex, line 90](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveGrid.lean#L90)

### module:BBLRecursiveSeed — BBLRecursiveSeed supporting declarations

**Status: lean/general.** K. Closes the whole geometric seed record under r→2r; Seed includes simplicity, all consecutive distinguished triangles, central orientation, and a valid counted triangle list.

- [Kobon.BBLRecursiveSeed.Seed, line 11](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveSeed.lean#L11)
- [Kobon.BBLRecursiveSeed.seed_step, line 61](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveSeed.lean#L61)
- [Kobon.BBLRecursiveSeed.compatible_step, line 104](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveSeed.lean#L104)
- [Kobon.BBLRecursiveSeed.seed_lower_bound, line 110](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveSeed.lean#L110)

### module:BBLInfinite — BBLInfinite supporting declarations

**Status: lean/general.** K. A uniformly available seed on some positive epsilon interval gives actual arrangements at every finite depth. A uniform seed remains an explicit premise of the generic theorem.

- [Kobon.BBLInfinite.UniformSeed, line 9](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L9)
- [Kobon.BBLInfinite.uniform_step, line 12](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L12)
- [Kobon.BBLInfinite.uniform_iterate, line 32](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L32)
- [Kobon.BBLInfinite.infinite_family, line 46](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L46)
- [Kobon.BBLInfinite.triangleCount_identity, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLInfinite.lean#L52)

### module:BBLSeed21Normalized — BBLSeed21Normalized supporting declarations

**Status: lean/general.** N. Discharges the odd seed premise for r=5, T=132, 0<ε≤10⁻⁵; the 19 caps, count, and central height 5ε/2 are transported from the existing actual21-line certificate.

- [Kobon.BBLSeed21Normalized.graph_identity, line 29](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21Normalized.lean#L29)
- [Kobon.BBLSeed21Normalized.saturated, line 54](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21Normalized.lean#L54)
- [Kobon.BBLSeed21Normalized.central_height, line 68](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21Normalized.lean#L68)
- [Kobon.BBLSeed21Normalized.seed_with_slopes, line 75](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21Normalized.lean#L75)
- [Kobon.BBLSeed21Normalized.compatible, line 91](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21Normalized.lean#L91)

### module:BBLRecursiveChoice — BBLRecursiveChoice supporting declarations

**Status: lean/general.** K. Retains the complete one-step witness for all sufficiently small positive pencil scales, for each analytically admissible delta. This permits intersection with the extra boundary requirements.

- [Kobon.BBLRecursiveChoice.canonical_eventually, line 12](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRecursiveChoice.lean#L12)

### module:BBLProjection — BBLProjection supporting declarations

**Status: lean/general.** K. Transfers actual row order from horizontal to oblique projection when the projected graph directions have the required sign.

- [Kobon.BBLProjection.graph_projection_mono, line 10](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLProjection.lean#L10)
- [Kobon.BBLProjection.graph_projection_strict_mono, line 19](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLProjection.lean#L19)
- [Kobon.BBLProjection.crossing_order_transfer, line 28](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLProjection.lean#L28)

### module:BBLRightmost — BBLRightmost supporting declarations

**Status: lean/general.** K. Proves the actual last-intersection property on the old rightmost line, using the seed's clean rightward ray and positive slope.

- [Kobon.BBLRightmost.factor_sine, line 11](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRightmost.lean#L11)
- [Kobon.BBLRightmost.pencil_max_eventually, line 57](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRightmost.lean#L57)
- [Kobon.BBLRightmost.canonical_row_eventually, line 122](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLRightmost.lean#L122)

### module:BBLNextBoundary — BBLNextBoundary supporting declarations

**Status: lean/general.** K. Derives the next rightmost clean ray from actual auxiliary graph equations and row order.

- [Kobon.BBLNextBoundary.positive_directions_eventually, line 28](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLNextBoundary.lean#L28)
- [Kobon.BBLNextBoundary.crossing_order_oblique, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLNextBoundary.lean#L56)
- [Kobon.BBLNextBoundary.next_rightmost_boundary, line 69](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLNextBoundary.lean#L69)

### module:BBLVisibleReindex — BBLVisibleReindex supporting declarations

**Status: lean/general.** K. Exact transport of actual visible-pair lists and projection admissibility.

- [Kobon.BBLVisibleReindex.transport_list_of_injective, line 84](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVisibleReindex.lean#L84)
- [Kobon.BBLVisibleReindex.visible_congr, line 106](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVisibleReindex.lean#L106)
- [Kobon.BBLVisibleReindex.admissible_pullback, line 115](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVisibleReindex.lean#L115)

### module:BBLVisibleSeed — BBLVisibleSeed supporting declarations

**Status: lean/general.** K. Defines the additional explicit boundary invariant and applies the proved exterior extension to obtain T+V actual triangles.

- [Kobon.BBLVisibleSeed.VisibleSeed, line 7](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVisibleSeed.lean#L7)
- [Kobon.BBLVisibleSeed.even_lower_bound, line 22](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVisibleSeed.lean#L22)

### module:BBLEvenStep — BBLEvenStep supporting declarations

**Status: lean/general.** K. The geometric doubling output has at least V+2r visible pairs; the old and new visible pairs are actually constructed.

- [Kobon.BBLEvenStep.visible_retained_eventually, line 16](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenStep.lean#L16)
- [Kobon.BBLEvenStep.canonical_visible_step, line 34](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenStep.lean#L34)

### module:BBLEvenRecursive — BBLEvenRecursive supporting declarations

**Status: lean/general.** K. Closes the complete visible seed record under doubling. Its projection normal satisfies the explicit positive-horizontal-component hypothesis.

- [Kobon.BBLEvenRecursive.visible_seed_step, line 9](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenRecursive.lean#L9)

### module:BBLEvenInfinite — BBLEvenInfinite supporting declarations

**Status: lean/general.** K. Generic iteration with a uniform visible seed. Initial visibility 2r gives full visibility 2r·2^t at depth t.

- [Kobon.BBLEvenInfinite.UniformVisibleSeed, line 8](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenInfinite.lean#L8)
- [Kobon.BBLEvenInfinite.uniform_iterate, line 27](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenInfinite.lean#L27)
- [Kobon.BBLEvenInfinite.infinite_even_family, line 43](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenInfinite.lean#L43)
- [Kobon.BBLEvenInfinite.visibleCount_full, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLEvenInfinite.lean#L56)

### module:BBLSeed21Visible — BBLSeed21Visible supporting declarations

**Status: lean/general.** N. Discharges the visible seed premise for r=5, T=132, V=10, normal (10, −13), and 0<ε≤10⁻⁵.

- [Kobon.BBLSeed21Visible.compatible, line 44](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLSeed21Visible.lean#L44)

### module:BBLVerifiedFamilies — BBLVerifiedFamilies supporting declarations

**Status: lean/conditional-interface.** N. Unconditional geometric lower bounds in the displayed formulas; no unresolved geometric hypothesis remains. The original11/12 initial cases are kernel proofs, while the overall family inherits the 21-line seed's finite native checks.

- [Kobon.BBLVerifiedFamilies.odd_family, line 18](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L18)
- [Kobon.BBLVerifiedFamilies.even_family, line 42](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L42)
- [Kobon.BBLVerifiedFamilies.eleven_odd_family, line 24](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L24)
- [Kobon.BBLVerifiedFamilies.eleven_even_family, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLVerifiedFamilies.lean#L51)

### module:BBLFamilyBenchmarks — BBLFamilyBenchmarks supporting declarations

**Status: lean/general.** K for the arithmetic comparisons. The family lies one below the indicated odd/even classical polynomial benchmarks. These equalities do not formalize those expressions as universal upper bounds. The strict-tail comparison is against this repository's previous complete verified envelope, not an assertion of literature priority.

- [Kobon.BBLFamilyBenchmarks.odd_baseline_gain, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L52)
- [Kobon.BBLFamilyBenchmarks.even_baseline_gain, line 65](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L65)
- [Kobon.BBLFamilyBenchmarks.odd_polynomial_gap, line 94](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L94)
- [Kobon.BBLFamilyBenchmarks.even_simple_polynomial_gap, line 104](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L104)
- [Kobon.BBLFamilyBenchmarks.previous_envelope, line 117](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L117)
- [Kobon.BBLFamilyBenchmarks.strict_previous_tail, line 152](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyBenchmarks.lean#L152)

### module:RecursiveEnvelope — RecursiveEnvelope supporting declarations

**Status: lean/general.** N for all-order existence; K for comparisons. The executable finite maximum retains the previous all-order bound and the two recursive families. It strictly improves the former envelope at orders 10·2^(t+5)+1 and 10·2^(t+5)+2 for every t.

- [Kobon.RecursiveEnvelope.all_n, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L51)
- [Kobon.RecursiveEnvelope.previous_le, line 57](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L57)
- [Kobon.RecursiveEnvelope.odd_family_le, line 62](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L62)
- [Kobon.RecursiveEnvelope.even_family_le, line 67](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L67)
- [Kobon.RecursiveEnvelope.strict_previous_tail, line 73](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/RecursiveEnvelope.lean#L73)

### module:BBLForgeConditional — BBLForgeConditional supporting declarations

**Status: lean/conditional-interface.** K, conditional. The formulas (1024·4^t−1)/3 and that quantity plus 16·2^t require respectively UniformSeed 8 341 and a corresponding UniformVisibleSeed 8 341 16 w. This module alone does not supply those seeds. The inherited optimal family is attributed to Forge–Ramírez Alfonsín and the BBL method.

- [Kobon.BBLForgeConditional.odd_family, line 52](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L52)
- [Kobon.BBLForgeConditional.even_family, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L58)
- [Kobon.BBLForgeConditional.odd_polynomial_exact, line 95](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L95)
- [Kobon.BBLForgeConditional.even_simple_polynomial_exact, line 104](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLForgeConditional.lean#L104)

### module:StrictLinearCertificate — StrictLinearCertificate supporting declarations

**Status: lean/general.** K. Positive weighted linear contradiction certificates; these are generic implications from the explicitly supplied identities and positivity.

- [Kobon.StrictLinearCertificate.infeasible, line 25](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/StrictLinearCertificate.lean#L25)
- [Kobon.StrictLinearCertificate.homogeneous_infeasible, line 43](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/StrictLinearCertificate.lean#L43)

### module:BBLTangentAlgebra — BBLTangentAlgebra supporting declarations

**Status: lean/general.** K. tan(π/20) satisfies t⁴−4t³−14t²−4t+1=0 and is the unique root in (3/20, 17/100).

- [Kobon.BBLTangentAlgebra.tan_quartic, line 20](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentAlgebra.lean#L20)
- [Kobon.BBLTangentAlgebra.tan_root_interval, line 51](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentAlgebra.lean#L51)
- [Kobon.BBLTangentAlgebra.quartic_root_unique, line 57](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentAlgebra.lean#L57)
- [Kobon.BBLTangentAlgebra.real_root_characterization, line 70](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentAlgebra.lean#L70)

### module:BBLTangentValues — BBLTangentValues supporting declarations

**Status: lean/general.** K. The explicit cubic expressions equal the actual tangent values tan(kπ/20) for k<10.

- [Kobon.BBLTangentValues.value_eq_tan, line 62](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangentValues.lean#L62)

### module:BBLTangent48Bounds — BBLTangent48Bounds supporting declarations

**Status: lean/general.** K. Actual rational enclosures for all 23 positive tangent values required by a48-intercept seed, with widths at most 5·10⁻³⁶. The proofs use tan(π/3)=√3, half-angle identities, and complementary-angle inverses. Python only proposes rational endpoints.

- [Kobon.BBLTangent48Bounds.tan_48_1_bounds, line 203](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangent48Bounds.lean#L203)
- [Kobon.BBLTangent48Bounds.tan_48_23_bounds, line 308](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLTangent48Bounds.lean#L308)

### module:BBLGridObstruction — BBLGridObstruction supporting declarations

**Status: lean/general.** K. Ten specified orientation signs are impossible on the actual20-intercept tangent grid, for every real epsilon and arbitrary real slopes. This is one explicit sign system, not a classification of every optimal21-line arrangement.

- [Kobon.BBLGridObstruction.actual_grid_infeasible, line 240](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLGridObstruction.lean#L240)
- [Kobon.BBLGridObstruction.actual_grid_orientation_impossible, line 263](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLGridObstruction.lean#L263)

### module:BBLObstructionReduction — BBLObstructionReduction supporting declarations

**Status: lean/general.** K. Two omitted weighted columns follow from the affine row identities and distinct omitted intercepts; the reduced system yields a contradiction.

- [Kobon.BBLObstructionReduction.two_columns_follow, line 28](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLObstructionReduction.lean#L28)
- [Kobon.BBLObstructionReduction.reduced_infeasible, line 63](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLObstructionReduction.lean#L63)

### module:UpperElementaryEdges — UpperElementaryEdges supporting declarations

**Status: lean/general.** K. The three actual sides of each certified triangle are consecutive intersection segments on their supporting lines.

- [Kobon.UpperElementaryEdges.predicate_all_sides_elementary, line 83](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperElementaryEdges.lean#L83)

### module:UpperEdgeCapacity — UpperEdgeCapacity supporting declarations

**Status: lean/general.** K. At most two pairwise interior-disjoint nondegenerate actual triangles can have the same base segment.

- [Kobon.UpperEdgeCapacity.at_most_two, line 113](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeCapacity.lean#L113)

### module:UpperTriangleIncidence — UpperTriangleIncidence supporting declarations

**Status: lean/general.** K. Derives 3T = used sides + shared sides; the certificate application derives disjointness from the actual triangle predicates.

- [Kobon.UpperTriangleIncidence.exact_incidence, line 196](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTriangleIncidence.lean#L196)
- [Kobon.UpperTriangleIncidence.certificate_incidence, line 230](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTriangleIncidence.lean#L230)

### module:UpperSharedEdge — UpperSharedEdge supporting declarations

**Status: lean/general.** K. An actual shared side cannot have two ordinary endpoints, for indexed supporting lines and disjoint triangle interiors.

- [Kobon.UpperSharedEdge.Pair.has_nonordinary_endpoint, line 108](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSharedEdge.lean#L108)
- [Kobon.UpperSharedEdge.Pair.not_both_endpoints_ordinary, line 98](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSharedEdge.lean#L98)

### module:UpperSharedIncidence — UpperSharedIncidence supporting declarations

**Status: lean/general.** K. Actual shared-side endpoint classification plus its finite incidence partition. The generic counting identity alone is combinatorial; the geometric certificate application supplies the classification.

- [Kobon.UpperSharedIncidence.shared_has_nonordinary_endpoint, line 93](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSharedIncidence.lean#L93)
- [Kobon.UpperSharedIncidence.oneCore_has_both_kinds, line 146](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSharedIncidence.lean#L146)
- [Kobon.UpperSharedIncidence.core_incidence, line 157](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSharedIncidence.lean#L157)

### module:UpperVertexBudget — UpperVertexBudget supporting declarations

**Status: lean/general.** K. Extracts actual intersection multiplicities, point-line incidences, and consecutive bounded interval counts.

- [Kobon.UpperVertexBudget.multiplicity_identity, line 79](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperVertexBudget.lean#L79)
- [Kobon.UpperVertexBudget.point_line_incidence, line 110](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperVertexBudget.lean#L110)
- [Kobon.UpperVertexBudget.line_interval_budget, line 132](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperVertexBudget.lean#L132)

### module:UpperEdgeInventory — UpperEdgeInventory supporting declarations

**Status: lean/general.** K. From actual nonparallel lines with n≥2 and a finite injective certified triangle family, constructs the side inventory and proves δ=S+U−D₁−D₂. No supplied global capacity, edge-count, or incidence identity is needed.

- [Kobon.UpperEdgeInventory.edge_cardinality, line 188](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L188)
- [Kobon.UpperEdgeInventory.predicate_side_mem_edges, line 290](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L290)
- [Kobon.UpperEdgeInventory.certificate_defect_identity, line 345](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEdgeInventory.lean#L345)

### module:UpperCoreExtraction — UpperCoreExtraction supporting declarations

**Status: lean/general.** K. Restricts multiplicity loss to the actual nonordinary core and identifies a D₁ edge as having exactly one ordinary endpoint. The empty-core corollary proves the classical simple-arrangement inequality 3T≤n(n−2).

- [Kobon.UpperCoreExtraction.defect_identity, line 61](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreExtraction.lean#L61)
- [Kobon.UpperCoreExtraction.certificate_oneCore_classification, line 76](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreExtraction.lean#L76)
- [Kobon.UpperCoreExtraction.simple_arrangement_upper, line 99](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreExtraction.lean#L99)

### module:UpperSimpleOptimality — UpperSimpleOptimality supporting declarations

**Status: lean/general.** K. Discharges empty-core and finite-family extraction directly from NoParallel, NoConcurrent, and SimpleLowerBound. For n≥2, every such witness obeys 3T≤n(n−2) and T≤floor(n(n−2)/3). This is a complete formalization of the classical simple bound, not a new unrestricted upper bound.

- [Kobon.UpperSimpleOptimality.core_empty, line 37](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSimpleOptimality.lean#L37)
- [Kobon.UpperSimpleOptimality.certificate_upper, line 49](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSimpleOptimality.lean#L49)
- [Kobon.UpperSimpleOptimality.simple_lower_bound_upper, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSimpleOptimality.lean#L58)
- [Kobon.UpperSimpleOptimality.simple_lower_bound_floor, line 70](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperSimpleOptimality.lean#L70)

### module:UpperCoreLineIncidence — UpperCoreLineIncidence supporting declarations

**Status: lean/general.** K. Derives the actual incidence inequality D₂+h≤I by counting consecutive core vertices along each supporting line.

- [Kobon.UpperCoreLineIncidence.core_line_budget, line 139](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreLineIncidence.lean#L139)

### module:UpperCoreCombinatorics — UpperCoreCombinatorics supporting declarations

**Status: lean/general.** K. Derives D₂≤binom(q, 2), its q≤3 specialization, and nonnegative summed multiple-point surplus.

- [Kobon.UpperCoreCombinatorics.core_edge_count, line 35](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreCombinatorics.lean#L35)
- [Kobon.UpperCoreCombinatorics.three_core_edge_count, line 43](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreCombinatorics.lean#L43)
- [Kobon.UpperCoreCombinatorics.core_surplus, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreCombinatorics.lean#L56)

### module:UpperFan — UpperFan supporting declarations

**Status: lean/conditional-interface.** K, explicit local interface. Actual cyclic fan data, with its orientation and incidence hypotheses supplied, imply the local sector-count conclusions. Whole-arrangement extraction of this interface is not proved here.

- [Kobon.UpperFan.Sectors.all_sectors_of_extremal, line 171](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L171)
- [Kobon.UpperFan.Sectors.core_shared_card_eq_three_of_extremal, line 187](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L187)
- [Kobon.UpperFan.Sectors.weighted_local_bound, line 227](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFan.lean#L227)

### module:UpperFanSupport — UpperFanSupport supporting declarations

**Status: lean/conditional-interface.** K, explicit local interface. The three core-ended rays of a full extremal fan cannot all lie in the indicated closed half-plane under the positive cyclic orientation and support-line hypotheses.

- [Kobon.UpperFanSupport.Sectors.extremal_core_not_in_halfplane, line 171](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperFanSupport.lean#L171)

### module:UpperCoreBoundary — UpperCoreBoundary supporting declarations

**Status: lean/conditional-interface.** K, conditional assembly. A supplied family of actual fans and endpoint-to-core incidence maps gives the aggregate local bound. The source does not extract that entire family from an arbitrary arrangement.

- [Kobon.UpperCoreBoundary.bound_at_supported_core, line 19](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBoundary.lean#L19)
- [Kobon.UpperCoreBoundary.CoreFamily.sum_ordinary_bound, line 75](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBoundary.lean#L75)

### module:UpperTripleFan — UpperTripleFan supporting declarations

**Status: lean/conditional-interface.** K, explicit matching interface. Neighboring full triple fans are incompatible under the stated matching across their common edge.

- [Kobon.UpperTripleFan.extremal_triple_fans_not_adjacent, line 156](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTripleFan.lean#L156)
- [Kobon.UpperTripleFan.incompatible_full_triple_fans, line 65](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperTripleFan.lean#L65)

### module:UpperCoreBudget — UpperCoreBudget supporting declarations

**Status: lean/conditional-interface.** K, conditional aggregate arithmetic. The integer inequalities imply the advertised restricted bounds when their fan, charging, and incidence premises are supplied. This is not an unconditional new upper bound for all arrangements.

- [Kobon.UpperCoreBudget.weighted_defect_with_core_edges, line 47](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L47)
- [Kobon.UpperCoreBudget.at_most_three_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L58)
- [Kobon.UpperCoreBudget.triangles_from_three_core_defect, line 72](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCoreBudget.lean#L72)

### module:UpperCleanHalfplane — UpperCleanHalfplane supporting declarations

**Status: lean/general.** K. An actual clean line has n−1 distinct crossings; one common open half-plane contains another intersection on every transverse line. Triangles at its ordinary crossings have a side on the line. For even n, an actual two-element partition of its crossings is impossible. Extracting that partition from degree-one edge assumptions remains separate.

- [Kobon.UpperCleanHalfplane.common_halfplane, line 62](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanHalfplane.lean#L62)
- [Kobon.UpperCleanHalfplane.clean_crossings_injective, line 92](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanHalfplane.lean#L92)
- [Kobon.UpperCleanHalfplane.ordinary_vertex_pairs_on_line, line 115](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanHalfplane.lean#L115)
- [Kobon.UpperCleanHalfplane.clean_crossing_card, line 163](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanHalfplane.lean#L163)
- [Kobon.UpperCleanHalfplane.clean_line_no_pair_partition, line 179](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanHalfplane.lean#L179)

### module:UpperCleanEdges — UpperCleanEdges supporting declarations

**Status: lean/general.** K. Turns the common half-plane intersections into actual consecutive bounded segments incident to the clean-line crossings.

- [Kobon.UpperCleanEdges.incident_positive_edge, line 27](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanEdges.lean#L27)
- [Kobon.UpperCleanEdges.incident_negative_edge, line 63](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanEdges.lean#L63)
- [Kobon.UpperCleanEdges.common_bounded_side, line 77](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanEdges.lean#L77)

### module:UpperCleanPairing — UpperCleanPairing supporting declarations

**Status: lean/general.** K. Actual consecutive-edge indices and half-plane signs give uniqueness of the selected incident segment. The global map is assembled in UpperCleanCharging below.

- [Kobon.UpperCleanPairing.pair_indices_consecutive, line 14](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanPairing.lean#L14)
- [Kobon.UpperCleanPairing.incident_positive_unique, line 42](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanPairing.lean#L42)
- [Kobon.UpperCleanPairing.incident_negative_unique, line 78](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanPairing.lean#L78)

### module:UpperCleanCover — UpperCleanCover supporting declarations

**Status: lean/general.** K. Extracts the actual pair cover under the degree-one assumption and contradicts its parity. Every clean line in an even-order nonparallel arrangement with n≥3 therefore has an actual incident charge edge that is unused or has one ordinary endpoint and one core endpoint, relative to the supplied finite injective certified triangle family. The aggregate charge-fiber count is supplied by UpperCleanCharging below.

- [Kobon.UpperCleanCover.actual_base_cover, line 212](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCover.lean#L212)
- [Kobon.UpperCleanCover.clean_line_bad_degree, line 355](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCover.lean#L355)
- [Kobon.UpperCleanCover.certificate_clean_line_charge, line 401](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCover.lean#L401)

### module:UpperCleanCharging — UpperCleanCharging supporting declarations

**Status: lean/general.** K. Actual even-order clean-line charging: n-h <= 2U+D1 for nonparallel real lines, n>=3, and any finite injective certified triangle family. The charge map and its finite fibers are extracted, with no charging premise.

- [Kobon.UpperCleanCharging.charge_line_unique, line 55](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCharging.lean#L55)
- [Kobon.UpperCleanCharging.oneCore_ordinary_card, line 75](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCharging.lean#L75)
- [Kobon.UpperCleanCharging.certificate_clean_line_budget, line 100](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperCleanCharging.lean#L100)

### module:UpperEvenSimpleOptimality — UpperEvenSimpleOptimality supporting declarations

**Status: lean/general.** K. The actual incidence identity and extracted charging imply 6T <= n(2n-5) and its floor form for every simple certificate witness with even n>=4. This formalizes the classical simple even upper bound; it is not an unrestricted nonsimple bound.

- [Kobon.UpperEvenSimpleOptimality.shared_empty, line 12](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L12)
- [Kobon.UpperEvenSimpleOptimality.certificate_even_upper, line 31](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L31)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_upper, line 56](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L56)
- [Kobon.UpperEvenSimpleOptimality.simple_lower_bound_even_floor, line 69](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/UpperEvenSimpleOptimality.lean#L69)

### module:BBLFamilyOptimality — BBLFamilyOptimality supporting declarations

**Status: lean/general.** K for both universal upper halves; N for existence and the combined windows. At n=10*2^t+1, +2, actual simple arrangements realize the verified family counts, and every simple certificate witness has at most that count plus one. This upgrades the earlier polynomial benchmark comparison to a genuine formal optimality window.

- [Kobon.BBLFamilyOptimality.odd_upper, line 12](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyOptimality.lean#L12)
- [Kobon.BBLFamilyOptimality.even_upper, line 20](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyOptimality.lean#L20)
- [Kobon.BBLFamilyOptimality.odd_window, line 29](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyOptimality.lean#L29)
- [Kobon.BBLFamilyOptimality.even_window, line 35](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/BBLFamilyOptimality.lean#L35)

### module:ParametricCached — Materialized parameter arrays preserve checker soundness

**Status: lean/general.** Materializing parameter forms in arrays preserves the exact checker and its soundness. No measured performance improvement is asserted.

- [Kobon.ParametricCached.cache_eq, line 14](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/ParametricCached.lean#L14)
- [Kobon.ParametricCached.simple_sound, line 28](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/ParametricCached.lean#L28)
- [Kobon.ParametricCached.triangle_eq, line 47](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/ParametricCached.lean#L47)

## Every retained finite coordinate identity

Repeated orders with different coordinate hashes are separate identities. Counts alone do not establish priority; original input attribution is preserved in the linked certificate and data records.

| Order | Triangles | Simple | Coordinate SHA-256 prefix | Lean certificate |
|---:|---:|:---:|---|---|
| 3 | 1 | yes | `05c82de62571155d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N003T00001H05c82de6.lean#L20); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N003T00001H05c82de6.lean#L10) |
| 4 | 2 | yes | `0e541bd5bbe7bee9` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N004T00002H0e541bd5.lean#L22); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N004T00002H0e541bd5.lean#L10) |
| 5 | 5 | yes | `948a0bdf2dd3be69` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N005T00005H948a0bdf.lean#L26); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N005T00005H948a0bdf.lean#L10) |
| 6 | 7 | yes | `6ea9ebaa7bf29c8c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N006T00007H6ea9ebaa.lean#L29); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N006T00007H6ea9ebaa.lean#L10) |
| 7 | 11 | yes | `e6b9a626a163e528` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N007T00011He6b9a626.lean#L34); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N007T00011He6b9a626.lean#L10) |
| 8 | 14 | yes | `2a63f4d9308d7a6d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N008T00014H2a63f4d9.lean#L38); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N008T00014H2a63f4d9.lean#L10) |
| 9 | 21 | yes | `6ebbed82d06399ea` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N009T00021H6ebbed82.lean#L46); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N009T00021H6ebbed82.lean#L10) |
| 10 | 25 | yes | `b767c427fa30087d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N010T00025Hb767c427.lean#L51); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N010T00025Hb767c427.lean#L10) |
| 11 | 32 | yes | `b955e7c9923ad0f9` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N011T00032Hb955e7c9.lean#L59); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N011T00032Hb955e7c9.lean#L10) |
| 12 | 38 | no | `38f69f38009707d8` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N012T00038H38f69f38.lean#L66) |
| 13 | 47 | yes | `ddec1f78855078d4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N013T00047Hddec1f78.lean#L76); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N013T00047Hddec1f78.lean#L10) |
| 14 | 53 | yes | `45157b2f20fe49b1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00053H45157b2f.lean#L83); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N014T00053H45157b2f.lean#L10) |
| 15 | 65 | yes | `4d3bf3b46db579eb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N015T00065H4d3bf3b4.lean#L96); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N015T00065H4d3bf3b4.lean#L10) |
| 16 | 72 | yes | `391cf79afe243177` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N016T00072H391cf79a.lean#L104); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N016T00072H391cf79a.lean#L10) |
| 17 | 85 | yes | `7cf3c061a447ff3f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N017T00085H7cf3c061.lean#L118); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N017T00085H7cf3c061.lean#L10) |
| 18 | 93 | yes | `edb6246a6de7d974` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N018T00093Hedb6246a.lean#L127); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N018T00093Hedb6246a.lean#L10) |
| 19 | 107 | yes | `a2f32bdbcd1ea442` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N019T00107Ha2f32bdb.lean#L142); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N019T00107Ha2f32bdb.lean#L10) |
| 20 | 116 | yes | `adc03eed024d9f01` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N020T00116Hadc03eed.lean#L152); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N020T00116Hadc03eed.lean#L10) |
| 21 | 133 | yes | `36bae754f19804b0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N021T00133H36bae754.lean#L170); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N021T00133H36bae754.lean#L10) |
| 22 | 143 | yes | `54396c646a7b60c1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N022T00143H54396c64.lean#L181); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N022T00143H54396c64.lean#L10) |
| 23 | 161 | yes | `969ad7d3adaf5833` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N023T00161H969ad7d3.lean#L200); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N023T00161H969ad7d3.lean#L10) |
| 24 | 172 | yes | `e63e906b99030e8b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N024T00172He63e906b.lean#L212); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N024T00172He63e906b.lean#L10) |
| 25 | 191 | yes | `b568bffb5a197067` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N025T00191Hb568bffb.lean#L232); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N025T00191Hb568bffb.lean#L10) |
| 26 | 203 | yes | `e61b423c7c3d7b55` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N026T00203He61b423c.lean#L245); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N026T00203He61b423c.lean#L10) |
| 27 | 225 | yes | `7d6ae9a04c46543f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N027T00225H7d6ae9a0.lean#L268); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N027T00225H7d6ae9a0.lean#L10) |
| 28 | 238 | yes | `56ef2acb9edd6a94` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N028T00238H56ef2acb.lean#L282); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N028T00238H56ef2acb.lean#L10) |
| 29 | 261 | yes | `d4805c25a121d33b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N029T00261Hd4805c25.lean#L306); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N029T00261Hd4805c25.lean#L10) |
| 30 | 275 | yes | `dcfe649a79cf71f0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N030T00275Hdcfe649a.lean#L321); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N030T00275Hdcfe649a.lean#L10) |
| 31 | 299 | yes | `70f23b9463cb77cb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N031T00299H70f23b94.lean#L346); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N031T00299H70f23b94.lean#L10) |
| 32 | 314 | yes | `9ab78b00c233bf92` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N032T00314H9ab78b00.lean#L362); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N032T00314H9ab78b00.lean#L10) |
| 33 | 341 | yes | `95f3b770119e6301` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N033T00341H95f3b770.lean#L390); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N033T00341H95f3b770.lean#L10) |
| 34 | 357 | yes | `fbde0a760c6e9c21` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N034T00357Hfbde0a76.lean#L407); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N034T00357Hfbde0a76.lean#L10) |
| 35 | 385 | yes | `9ee99af6b980c0b9` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N035T00385H9ee99af6.lean#L436); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N035T00385H9ee99af6.lean#L10) |
| 36 | 402 | yes | `3fc01b7d2a1ce99e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N036T00402H3fc01b7d.lean#L454); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N036T00402H3fc01b7d.lean#L10) |
| 37 | 431 | yes | `11f0bde7bac3eddf` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N037T00431H11f0bde7.lean#L484); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N037T00431H11f0bde7.lean#L10) |
| 38 | 449 | yes | `46ad5a32af834f7d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N038T00449H46ad5a32.lean#L503); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N038T00449H46ad5a32.lean#L10) |
| 39 | 469 | no | `cf24d7d33c00f6e1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N039T00469Hcf24d7d3.lean#L524) |
| 40 | 494 | yes | `785374ca691bcc56` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N040T00494H785374ca.lean#L550); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N040T00494H785374ca.lean#L10) |
| 41 | 533 | yes | `01e2ef66f8fdeceb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N041T00533H01e2ef66.lean#L590); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N041T00533H01e2ef66.lean#L10) |
| 42 | 553 | yes | `2bdc9d67365a3ec1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N042T00553H2bdc9d67.lean#L611); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N042T00553H2bdc9d67.lean#L10) |
| 43 | 587 | yes | `861d8be27deed6d3` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N043T00587H861d8be2.lean#L646); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N043T00587H861d8be2.lean#L10) |
| 44 | 608 | yes | `b5277675e356739f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N044T00608Hb5277675.lean#L668); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N044T00608Hb5277675.lean#L10) |
| 45 | 645 | yes | `3dc6e882e9b83723` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N045T00645H3dc6e882.lean#L706); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N045T00645H3dc6e882.lean#L10) |
| 46 | 667 | yes | `32b8ca2f231ddf83` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N046T00667H32b8ca2f.lean#L729); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N046T00667H32b8ca2f.lean#L10) |
| 47 | 690 | yes | `d8af27fc13d18221` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N047T00690Hd8af27fc.lean#L753); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N047T00690Hd8af27fc.lean#L10) |
| 48 | 720 | yes | `5e9767e73b31c34c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N048T00720H5e9767e7.lean#L784); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N048T00720H5e9767e7.lean#L10) |
| 49 | 767 | yes | `957e6f151a57c598` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N049T00767H957e6f15.lean#L832); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N049T00767H957e6f15.lean#L10) |
| 50 | 791 | yes | `2ea22b558bf879c5` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N050T00791H2ea22b55.lean#L857); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N050T00791H2ea22b55.lean#L10) |
| 51 | 817 | no | `bd215f67ab1067d2` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N051T00817Hbd215f67.lean#L884) |
| 52 | 850 | yes | `4b0d823a1fa89bb4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N052T00850H4b0d823a.lean#L918); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N052T00850H4b0d823a.lean#L10) |
| 53 | 884 | yes | `723d7eff8d45b6dd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N053T00884H723d7eff.lean#L953); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N053T00884H723d7eff.lean#L10) |
| 54 | 918 | yes | `915abb8ed17c1286` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N054T00918H915abb8e.lean#L988); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N054T00918H915abb8e.lean#L10) |
| 55 | 954 | yes | `ea7675d9b8a30ae0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N055T00954Hea7675d9.lean#L1025); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N055T00954Hea7675d9.lean#L10) |
| 56 | 990 | yes | `de8a415c9b297a67` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N056T00990Hde8a415c.lean#L1062); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N056T00990Hde8a415c.lean#L10) |
| 57 | 1045 | yes | `9a1d337c75ba6de1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N057T01045H9a1d337c.lean#L1118); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N057T01045H9a1d337c.lean#L10) |
| 58 | 1073 | yes | `d988db55253084b0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N058T01073Hd988db55.lean#L1147); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N058T01073Hd988db55.lean#L10) |
| 59 | 1102 | yes | `fd3b4280376ea0f4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N059T01102Hfd3b4280.lean#L1177); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N059T01102Hfd3b4280.lean#L10) |
| 60 | 1140 | yes | `16af6d0b260ee2bb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N060T01140H16af6d0b.lean#L1216); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N060T01140H16af6d0b.lean#L10) |
| 12 | 37 | yes | `8c718a334b7bed0f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N012T00037H8c718a33.lean#L65); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N012T00037H8c718a33.lean#L10) |
| 39 | 468 | yes | `5c5b0b26ee2241d2` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N039T00468H5c5b0b26.lean#L523); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N039T00468H5c5b0b26.lean#L10) |
| 51 | 816 | yes | `6fa6b7d91d28819b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N051T00816H6fa6b7d9.lean#L883); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N051T00816H6fa6b7d9.lean#L10) |
| 5 | 3 | yes | `6265d6a7c5576172` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N005T00003H6265d6a7.lean#L24); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N005T00003H6265d6a7.lean#L10) |
| 6 | 4 | yes | `7e060e9a0ac15660` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N006T00004H7e060e9a.lean#L26); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N006T00004H7e060e9a.lean#L10) |
| 19 | 107 | yes | `5d2a7588c1e2ddfd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N019T00107H5d2a7588.lean#L142); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N019T00107H5d2a7588.lean#L10) |
| 21 | 126 | yes | `f18756b727918616` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N021T00126Hf18756b7.lean#L163); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N021T00126Hf18756b7.lean#L10) |
| 5 | 5 | yes | `dd0748b7cdfb14f7` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N005T00005Hdd0748b7.lean#L26); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N005T00005Hdd0748b7.lean#L10) |
| 7 | 10 | yes | `4b5bb6e99d6224c4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N007T00010H4b5bb6e9.lean#L33); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N007T00010H4b5bb6e9.lean#L10) |
| 21 | 132 | yes | `3d8bae2fa7295d74` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N021T00132H3d8bae2f.lean#L169); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N021T00132H3d8bae2f.lean#L10) |
| 22 | 142 | yes | `e683945e66cdf396` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N022T00142He683945e.lean#L180); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N022T00142He683945e.lean#L10) |
| 41 | 532 | yes | `6d48a3411f413135` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N041T00532H6d48a341.lean#L589); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N041T00532H6d48a341.lean#L10) |
| 42 | 552 | yes | `7b29a6bd1191f25d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N042T00552H7b29a6bd.lean#L610); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N042T00552H7b29a6bd.lean#L10) |
| 81 | 2132 | yes | `7bc6b303744fa706` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N081T02132H7bc6b303.lean#L2229); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N081T02132H7bc6b303.lean#L10) |
| 82 | 2172 | yes | `d75c9101c8a5c62b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N082T02172Hd75c9101.lean#L2270); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N082T02172Hd75c9101.lean#L10) |
| 161 | 8532 | yes | `230691d59eee84b4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N161T08532H230691d5.lean#L8709); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N161T08532H230691d5.lean#L10) |
| 162 | 8612 | yes | `1512e69660740eae` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N162T08612H1512e696.lean#L8790); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N162T08612H1512e696.lean#L10) |
| 9 | 19 | no | `e16410b887ee5bb8` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N009T00019He16410b8.lean#L44) |
| 15 | 61 | no | `7c38d54f9e52590b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N015T00061H7c38d54f.lean#L92) |
| 21 | 127 | no | `b8dcff224cdbe59b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N021T00127Hb8dcff22.lean#L164) |
| 27 | 217 | no | `6670a2b142843e2a` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N027T00217H6670a2b1.lean#L260) |
| 33 | 331 | no | `25fd8f0c3311d01e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N033T00331H25fd8f0c.lean#L380) |
| 48 | 715 | no | `ba6f5baae76d20ff` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N048T00715Hba6f5baa.lean#L779) |
| 99 | 3169 | no | `4fef38d87d0c5550` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N099T03169H4fef38d8.lean#L3284) |
| 195 | 12481 | no | `cd3497dbf8468a75` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N195T12481Hcd3497db.lean#L12692) |
| 195 | 12480 | yes | `1b9230fb738a2ca6` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N195T12480H1b9230fb.lean#L12691); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N195T12480H1b9230fb.lean#L10) |
| 44 | 602 | yes | `0b0250bf6213b6ae` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N044T00602H0b0250bf.lean#L662); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N044T00602H0b0250bf.lean#L10) |
| 99 | 3168 | yes | `a0ea30825a737b92` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N099T03168Ha0ea3082.lean#L3283); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N099T03168Ha0ea3082.lean#L10) |
| 39 | 470 | yes | `30caa6f7f89472aa` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N039T00470H30caa6f7.lean#L525); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N039T00470H30caa6f7.lean#L10) |
| 47 | 691 | yes | `fac44af18c558b7a` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N047T00691Hfac44af1.lean#L754); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N047T00691Hfac44af1.lean#L10) |
| 48 | 721 | yes | `2fb5ef0df4cf6a93` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N048T00721H2fb5ef0d.lean#L785); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N048T00721H2fb5ef0d.lean#L10) |
| 51 | 818 | yes | `c18e1baf25f50900` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N051T00818Hc18e1baf.lean#L885); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N051T00818Hc18e1baf.lean#L10) |
| 53 | 885 | yes | `6bc5b14d0b68627c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N053T00885H6bc5b14d.lean#L954); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N053T00885H6bc5b14d.lean#L10) |
| 54 | 919 | yes | `a254c1b4f05b17a1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N054T00919Ha254c1b4.lean#L989); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N054T00919Ha254c1b4.lean#L10) |
| 55 | 955 | yes | `202625a3908524c7` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N055T00955H202625a3.lean#L1026); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N055T00955H202625a3.lean#L10) |
| 59 | 1103 | yes | `ba482375103b9e14` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N059T01103Hba482375.lean#L1178); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N059T01103Hba482375.lean#L10) |
| 60 | 1141 | yes | `9bc5096cc3fd10a0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N060T01141H9bc5096c.lean#L1217); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N060T01141H9bc5096c.lean#L10) |
| 65 | 1365 | yes | `b1dcbeb4ff39eb3b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N065T01365Hb1dcbeb4.lean#L1446); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N065T01365Hb1dcbeb4.lean#L10) |
| 66 | 1397 | yes | `327ecbb9b7bafefe` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N066T01397H327ecbb9.lean#L1479); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N066T01397H327ecbb9.lean#L10) |
| 99 | 3170 | yes | `ea507e2de1372dd8` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N099T03170Hea507e2d.lean#L3285); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N099T03170Hea507e2d.lean#L10) |
| 129 | 5461 | yes | `6dae0012aa49d5cf` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N129T05461H6dae0012.lean#L5606); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N129T05461H6dae0012.lean#L10) |
| 130 | 5525 | yes | `e0559b54aee5366e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N130T05525He0559b54.lean#L5671); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N130T05525He0559b54.lean#L10) |
| 195 | 12482 | yes | `5413dd7b60ee64bf` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N195T12482H5413dd7b.lean#L12693); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N195T12482H5413dd7b.lean#L10) |
| 14 | 54 | no | `d47aea63afc13985` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hd47aea63.lean#L84) |
| 14 | 54 | no | `18bbcff4f43351df` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H18bbcff4.lean#L84) |
| 14 | 54 | no | `78f750c071a5610e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H78f750c0.lean#L84) |
| 14 | 54 | no | `912da8ec9bc76efd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H912da8ec.lean#L84) |
| 14 | 54 | no | `9134999072a9cae0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H91349990.lean#L84) |
| 14 | 54 | no | `9c871e103a465b86` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H9c871e10.lean#L84) |
| 14 | 54 | no | `b3dcae0bc1d84132` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hb3dcae0b.lean#L84) |
| 14 | 54 | no | `9219cdaa6f90ac3b` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H9219cdaa.lean#L84) |
| 14 | 54 | no | `d2babc1b9431b2fb` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hd2babc1b.lean#L84) |
| 14 | 54 | no | `2b34ca22dc8980b3` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H2b34ca22.lean#L84) |
| 14 | 54 | no | `fa427b3d27ef501f` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hfa427b3d.lean#L84) |
| 14 | 54 | no | `1ec1fd5cb2ee863c` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H1ec1fd5c.lean#L84) |
| 14 | 54 | no | `3e5d182f84085aae` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H3e5d182f.lean#L84) |
| 14 | 54 | no | `17f8c0524eb16e50` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H17f8c052.lean#L84) |
| 14 | 54 | no | `c472f97237f10e5e` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054Hc472f972.lean#L84) |
| 14 | 52 | yes | `2eb83dc242a1a606` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00052H2eb83dc2.lean#L82); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N014T00052H2eb83dc2.lean#L10) |
| 14 | 53 | yes | `5e6068f5003e0ecd` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00053H5e6068f5.lean#L83); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N014T00053H5e6068f5.lean#L10) |
| 14 | 52 | yes | `b3f4749f6dee6452` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00052Hb3f4749f.lean#L82); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N014T00052Hb3f4749f.lean#L10) |
| 14 | 52 | yes | `c6615430ae3d4cc4` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00052Hc6615430.lean#L82); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N014T00052Hc6615430.lean#L10) |
| 8 | 14 | yes | `ebff58687458ee11` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N008T00014Hebff5868.lean#L38); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N008T00014Hebff5868.lean#L10) |
| 14 | 51 | yes | `d67e7a6b3b089546` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00051Hd67e7a6b.lean#L81); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N014T00051Hd67e7a6b.lean#L10) |
| 20 | 114 | yes | `bc312fc85ea5d6aa` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N020T00114Hbc312fc8.lean#L150); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N020T00114Hbc312fc8.lean#L10) |
| 26 | 203 | yes | `5452b4ffa1a9f082` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N026T00203H5452b4ff.lean#L245); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N026T00203H5452b4ff.lean#L10) |
| 32 | 313 | yes | `018f9fc6b73f13a7` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N032T00313H018f9fc6.lean#L361); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N032T00313H018f9fc6.lean#L10) |
| 38 | 448 | yes | `7d59f504aba872af` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N038T00448H7d59f504.lean#L502); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N038T00448H7d59f504.lean#L10) |
| 50 | 791 | yes | `6bde86a3dcbdd30a` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N050T00791H6bde86a3.lean#L857); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N050T00791H6bde86a3.lean#L10) |
| 8 | 15 | no | `a138081033c3b257` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N008T00015Ha1380810.lean#L39) |
| 14 | 54 | no | `105765145381c27d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N014T00054H10576514.lean#L84) |
| 20 | 117 | no | `382171ac62ccad67` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N020T00117H382171ac.lean#L153) |
| 26 | 204 | no | `f71379c4db0380d0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N026T00204Hf71379c4.lean#L246) |
| 32 | 315 | no | `5914f2bb88d115ce` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N032T00315H5914f2bb.lean#L363) |
| 36 | 402 | yes | `ce43a1077597aac1` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N036T00402Hce43a107.lean#L454); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N036T00402Hce43a107.lean#L10) |
| 38 | 450 | no | `8ba2bdb14e85b408` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N038T00450H8ba2bdb1.lean#L504) |
| 42 | 553 | yes | `9849e255d5da63f0` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N042T00553H9849e255.lean#L611); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N042T00553H9849e255.lean#L10) |
| 50 | 792 | no | `3d40cb58261638e6` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N050T00792H3d40cb58.lean#L858) |
| 19 | 107 | yes | `6e8ca6f56a85d29d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N019T00107H6e8ca6f5.lean#L142); [simple_lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/SimpleCertificates/N019T00107H6e8ca6f5.lean#L10) |
| 6 | 6 | no | `af8f599eb8a15e6d` | [lower_bound](https://github.com/alejandrozu/kobon-proof/blob/2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8/Kobon/Certificates/N006T00006Haf8f599e.lean#L28) |
