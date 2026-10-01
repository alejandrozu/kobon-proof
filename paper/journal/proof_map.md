# Result-to-proof map for the journal manuscript

Audited 1 October 2026. Every source link below is pinned to mathematical revision 99fdc8ec1ef8b1fb22c3da32b011b7361762e958.

**This is not a claim that the entire paper has an end-to-end Lean proof.** The uniform real-line construction is proved; global boundary extraction, global upper-bound geometry, and recursive BBL integration remain incomplete as formalizations. Exact computation and cited literature are separately labeled.

The Lean development defines coordinate-based lower-bound witnesses. It proves nonempty uncut interiors, sign-cell equality and disjointness under its stated hypotheses. The ordinary connected-component interpretation is supplied in the manuscript; the general cell lemma allows more arrangements than the present Lean sign-cell interface.

General versus finite describes quantifier scope, not a trust category: some parameterized families and the finite-enhanced all-order envelope use finite native checks. Standard logical axioms and additional compiler/runtime trust are distinguished in each source and in the [formalization audit](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/FORMALIZATION.md). Active proof sources have no placeholders or custom geometric axioms. The unfinished March source is historical and excluded.

A [successful GitHub verification run](https://github.com/alejandrozu/kobon-proof/actions/runs/36830561024) checked the unchanged mathematical sources at commit 6f7e11e. The [machine-readable map](proof_map.json) binds every line reference to a source SHA-256 and checked Git blob. Run python paper/journal/validate.py from a full checkout after compiling to verify the current document, anchors and PDF links.

## Evidence labels

- **lean/general:** a theorem with general parameters, subject to the precise hypotheses and trust boundary stated below.
- **lean/finite:** a finite coordinate certificate, usually using native evaluation.
- **partial:** formal components exist; the full manuscript claim is not proved end to end in Lean.
- **manuscript:** ordinary mathematical argument, without a matching complete Lean theorem.
- **computation:** exact finite or interval calculation outside Lean.
- **external:** a cited literature result, not formalized here.

## Individual claims

### Result 1.1 — Uniform affine refinement for every natural order

**Status: lean/general.** SimpleLowerBound n (baseline n) is proved for real lines at every n with standard logical axioms. The interpretation as complement components uses the manuscript's elementary sign-cell/topology bridge.

- [Kobon.Universal.baseline_sound, line 26](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L26)
- [Kobon.Universal.baseline_improvement, line 72](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L72)

### Equation 1 — Closed formula for G

**Status: lean/general.** The definition handles n<3 and n=3; the stated floor formula is baseline_formula for n>=4. Natural division is floor division.

- [Kobon.Universal.baseline, line 11](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L11)
- [Kobon.Universal.baseline_formula, line 59](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L59)

### Result 2.1 — Certified triangular interiors and disjointness

**Status: partial.** Lean proves nonempty interiors, strict sign-cell equality and disjointness when the whole arrangement has no parallel pairs. The paper states a more general lemma requiring only the three supports to be pairwise nonparallel; that extension and the connected-component interpretation are ordinary arguments in the manuscript. All delivered lower-bound witnesses satisfy the stronger Lean premise.

- [Kobon.Cells.interior_nonempty, line 461](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Cells.lean#L461)
- [Kobon.Cells.interior_eq_signCell, line 486](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Cells.lean#L486)
- [Kobon.Cells.distinct_interiors_disjoint, line 453](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Cells.lean#L453)

### Equation 4 — Trigonometric determinant and oriented evaluation identities

**Status: lean/general.** Symbolic identities for arbitrary real angles.

- [Kobon.FurediPalasti.det_line, line 13](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalasti.lean#L13)
- [Kobon.FurediPalasti.oriented_line, line 123](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalasti.lean#L123)

### Equation 5 — Selected triples and classical affine count

**Status: lean/general.** The two sets of residue classes yield certified triangles and the classical count. No numerical novelty is claimed for the older half-phase construction.

- [Kobon.FurediPalasti.selected_triangle, line 186](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalasti.lean#L186)
- [Kobon.ShiftedFurediPalasti.selected_triangle, line 144](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/ShiftedFurediPalasti.lean#L144)
- [Kobon.FurediPalastiCount.ordered_bound, line 186](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalastiCount.lean#L186)
- [Kobon.FurediPalasti.lower_bound, line 301](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalasti.lean#L301)

### Result 2.2 — Phase correction

**Status: lean/general.** Actual simple real arrangements for every n>=3 with floor(n(n-3)/3)+1 triangles; the repeated-index saving is separately proved.

- [Kobon.ShiftedFurediPalasti.simple_lower_bound, line 274](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/ShiftedFurediPalasti.lean#L274)
- [Kobon.ShiftedCount.ordered_bound_plus, line 59](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/ShiftedCount.lean#L59)

### Equation 6 — Projective change of chart

**Status: lean/general.** Exact determinant/evaluation covariance and triangle preservation under the stated cut inequalities.

- [Kobon.Projective.det_transform, line 14](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Projective.lean#L14)
- [Kobon.Projective.eval_transform, line 19](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Projective.lean#L19)
- [Kobon.Projective.oriented_transform, line 25](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Projective.lean#L25)
- [Kobon.Projective.triangle_preserved, line 111](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Projective.lean#L111)
- [Kobon.Projective.triangle_preserved_negative, line 138](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Projective.lean#L138)

### Result 2.3 — One-cap and two-cap constructions

**Status: lean/general.** The one-cap theorem uses n=2m+1 with m>=1. The two-cap theorem uses n=6k+3 with k>=1. Both construct simple real arrangements.

- [Kobon.FurediPalastiWrap.one_cap_simple_lower_bound, line 191](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalastiWrap.lean#L191)
- [Kobon.FurediPalastiTwoCaps.two_cap_simple_lower_bound, line 282](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalastiTwoCaps.lean#L282)

### Equation 7 — Exact gap to the classical comparison polynomial

**Status: lean/general.** Arithmetic identity only; this does not formalize the external upper-bound theorem or prove it unrestrictedly.

- [Kobon.Universal.polynomial_gap_exact, line 90](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L90)

### Equation 16 — Finite-enhanced lower envelope

**Status: lean/general.** Universal.all_n proves max(G, AllN.bound); AllN.bound is max of the older baseline and a finite certified enhancement. Since G dominates the older baseline, this equals the paper's max(G,C). The identification of C with the external certificate catalog is checked by the manifest/catalog, rather than C being a directly parsed Lean definition. This theorem imports finite native_decide certificates and therefore has their additional runtime trust.

- [Kobon.Universal.all_n, line 117](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L117)
- [Kobon.Universal.classical_baseline_le, line 63](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L63)
- [Kobon.AllN.dominates_every_saved_certificate, line 255](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/AllN.lean#L255)

### j:after195 — Saved envelope equals G after order 195

**Status: lean/general.** Immediate combination of AllN.baseline_after_last_exception, Universal.classical_baseline_le and the definition Universal.bound; no separately named combined theorem. Does not assert optimality after 195.

- [Kobon.AllN.baseline_after_last_exception, line 465](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/AllN.lean#L465)
- [Kobon.Universal.classical_baseline_le, line 63](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L63)
- [Kobon.Universal.bound, line 112](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L112)

### j:44equality — Simple optimum K_s(44)=608

**Status: partial.** The simple lower certificate 608 is in Lean; equality additionally uses Blanc's external simple-arrangement upper theorem. No equality for unrestricted K(44) is claimed.

- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L461)

### j:old-q-family — G supersedes the earlier q=6*2^t additional-line formula

**Status: manuscript.** The identity G(q+3)=q^2/3+q+2 follows by substitution into the verified formula; no dedicated theorem for this exact q-family identity was found. It is an arithmetic consequence, not a new formalized generic extension mechanism.

- [Kobon.Universal.baseline_formula, line 59](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L59)
- [Kobon.Universal.strict_odd_multiples, line 143](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L143)

### j:certificate-soundness — Integer certificate validation

**Status: lean/general.** Integer sign checks lift to real nonparallel lines and distinct uncut triangular support triples. Simplicity is separately checked. Finite checked instances use native_decide.

- [Kobon.validate_sound, line 135](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Geometry.lean#L135)
- [Kobon.validate_simple_sound, line 39](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Simple.lean#L39)

### jup:shared-fan — Six actual triangles with six distinct shared elementary radial sides

**Status: lean/finite.** The fixed six integer lines and six supporting triples are kernel-checked. Lean proves the lifted real triangles, distinct supporting triples, triple center, six distinct nonzero elementary radial segments, and that each radial segment is a side of two distinct triangles. This is a finite formal counterexample to a literal local bound of two incident shared sides, not to a global Kobon upper theorem. SharedFan does not separately enumerate all possible triangles or formalize the local classification d1=d2=3.

- [Kobon.SharedFan.integerLines, line 17](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L17)
- [Kobon.SharedFan.integer_triangles, line 27](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L27)
- [Kobon.SharedFan.real_triangles, line 32](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L32)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L51)
- [Kobon.SharedFan.adjacent_triangles_distinct, line 58](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L58)
- [Kobon.SharedFan.center_is_triple, line 61](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L61)
- [Kobon.SharedFan.radial_segments_injective, line 105](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L105)
- [Kobon.SharedFan.radial_elementary, line 113](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L113)

### Table 1 — Table 1: selected simple certificates

**Status: lean/finite.** Each individual simple lower bound is proved through the finite certificate pipeline (native_decide). Improvements are relative to earlier project witnesses, not claims of first numerical priority or global optimality.

- [Kobon.Results.best_simple_028, line 429](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L429)
- [Kobon.Results.best_simple_030, line 433](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L433)
- [Kobon.Results.best_simple_034, line 441](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L441)
- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L461)
- [Kobon.Results.best_simple_039, line 451](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L451)
- [Kobon.Results.best_simple_047, line 467](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L467)
- [Kobon.Results.best_simple_048, line 469](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L469)
- [Kobon.Results.best_simple_051, line 475](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L475)
- [Kobon.Results.best_simple_053, line 479](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L479)
- [Kobon.Results.best_simple_054, line 481](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L481)
- [Kobon.Results.best_simple_055, line 483](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L483)
- [Kobon.Results.best_simple_059, line 491](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L491)
- [Kobon.Results.best_simple_060, line 493](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L493)
- [Kobon.Results.best_simple_099, line 503](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L503)
- [Kobon.Results.best_simple_195, line 513](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L513)

### j:finite-28 — Simple 28-line certificate with at least 238 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_028, line 429](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L429)

### j:finite-30 — Simple 30-line certificate with at least 275 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_030, line 433](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L433)

### j:finite-34 — Simple 34-line certificate with at least 357 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_034, line 441](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L441)

### j:finite-44 — Simple 44-line certificate with at least 608 cells

**Status: lean/finite.** Finite lower bound only; the optimum assertion additionally needs Blanc's external upper theorem. Uses native_decide.

- [Kobon.Results.best_simple_044, line 461](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L461)

### j:finite-39 — Simple 39-line certificate with at least 470 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_039, line 451](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L451)

### j:finite-47 — Simple 47-line certificate with at least 691 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_047, line 467](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L467)

### j:finite-48 — Simple 48-line certificate with at least 721 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_048, line 469](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L469)

### j:finite-51 — Simple 51-line certificate with at least 818 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_051, line 475](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L475)

### j:finite-53 — Simple 53-line certificate with at least 885 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_053, line 479](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L479)

### j:finite-54 — Simple 54-line certificate with at least 919 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_054, line 481](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L481)

### j:finite-55 — Simple 55-line certificate with at least 955 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_055, line 483](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L483)

### j:finite-59 — Simple 59-line certificate with at least 1103 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_059, line 491](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L491)

### j:finite-60 — Simple 60-line certificate with at least 1141 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_060, line 493](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L493)

### j:finite-99 — Simple 99-line certificate with at least 3170 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_099, line 503](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L503)

### j:finite-195 — Simple 195-line certificate with at least 12482 cells

**Status: lean/finite.** Finite simple lower bound using native_decide; no numerical priority or optimality claim.

- [Kobon.Results.best_simple_195, line 513](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Results.lean#L513)

### j:maiorana-inputs — Fifteen Maiorana 14-line certificates

**Status: lean/finite.** All fifteen imported coordinate identities have Lean lower-bound certificates (native_decide), each with 54 cells. Discovery credit remains Maiorana. This does not establish an unrestricted optimum.

- [Kobon.Certificates.N014T00054Hd47aea63.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hd47aea63.lean#L84)
- [Kobon.Certificates.N014T00054H18bbcff4.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H18bbcff4.lean#L84)
- [Kobon.Certificates.N014T00054H78f750c0.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H78f750c0.lean#L84)
- [Kobon.Certificates.N014T00054H912da8ec.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H912da8ec.lean#L84)
- [Kobon.Certificates.N014T00054H91349990.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H91349990.lean#L84)
- [Kobon.Certificates.N014T00054H9c871e10.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H9c871e10.lean#L84)
- [Kobon.Certificates.N014T00054Hb3dcae0b.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hb3dcae0b.lean#L84)
- [Kobon.Certificates.N014T00054H9219cdaa.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H9219cdaa.lean#L84)
- [Kobon.Certificates.N014T00054Hd2babc1b.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hd2babc1b.lean#L84)
- [Kobon.Certificates.N014T00054H2b34ca22.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H2b34ca22.lean#L84)
- [Kobon.Certificates.N014T00054Hfa427b3d.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hfa427b3d.lean#L84)
- [Kobon.Certificates.N014T00054H1ec1fd5c.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H1ec1fd5c.lean#L84)
- [Kobon.Certificates.N014T00054H3e5d182f.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H3e5d182f.lean#L84)
- [Kobon.Certificates.N014T00054H17f8c052.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H17f8c052.lean#L84)
- [Kobon.Certificates.N014T00054Hc472f972.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hc472f972.lean#L84)

### j:pu-gallery — Ten Parpalak-Utkin gallery witnesses

**Status: lean/finite.** Ten gallery coordinate identities have Lean lower-bound certificates (native_decide), including 26:204 and 50:792. Discovery credit remains the original authors. The separate complete recount uses independent exact programs.

- [Kobon.Certificates.N046T00667H32b8ca2f.lower_bound, line 729](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N046T00667H32b8ca2f.lean#L729)
- [Kobon.Certificates.N008T00015Ha1380810.lower_bound, line 39](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N008T00015Ha1380810.lean#L39)
- [Kobon.Certificates.N014T00054H10576514.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H10576514.lean#L84)
- [Kobon.Certificates.N020T00117H382171ac.lower_bound, line 153](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N020T00117H382171ac.lean#L153)
- [Kobon.Certificates.N026T00204Hf71379c4.lower_bound, line 246](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N026T00204Hf71379c4.lean#L246)
- [Kobon.Certificates.N032T00315H5914f2bb.lower_bound, line 363](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N032T00315H5914f2bb.lean#L363)
- [Kobon.Certificates.N036T00402Hce43a107.lower_bound, line 454](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N036T00402Hce43a107.lean#L454)
- [Kobon.Certificates.N038T00450H8ba2bdb1.lower_bound, line 504](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N038T00450H8ba2bdb1.lean#L504)
- [Kobon.Certificates.N042T00553H9849e255.lower_bound, line 611](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N042T00553H9849e255.lean#L611)
- [Kobon.Certificates.N050T00792H3d40cb58.lower_bound, line 858](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N050T00792H3d40cb58.lean#L858)

### Result 3.1 — Verified exterior realization

**Status: lean/general.** Actual real-coordinate simple arrangement with T plus the length of an explicit duplicate-free visible-pair list. Admissibility and beyond-all-vertices height are explicit geometric hypotheses. No parity restriction or future-count assumption.

- [Kobon.Exterior.extension, line 164](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Exterior.lean#L164)
- [Kobon.Exterior.safeHeight_beyond, line 191](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Exterior.lean#L191)

### Result 3.2 — Boundary-defect extension proposition

**Status: partial.** The manuscript proves ray charging and identifies geometric wedges with cyclic data. Lean proves the finite cyclic averaging and conditional defect arithmetic; no end-to-end real-arrangement extension theorem with this defect gain is present.

- [KobonBoundary.cap_mass, line 20](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L20)
- [KobonBoundary.exists_average, line 35](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L35)
- [KobonBoundary.charging_bound, line 75](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L75)
- [KobonBoundary.defect_extension_bound, line 79](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L79)

### Equation 8 — Both-parity defect gain formula

**Status: partial.** The cyclic inequality in Lean assumes the three-wedge and boundary inequalities. Iteration.defectGain implements the rounded formula as a definition; its geometric interpretation depends on the manuscript's unformalized extraction and charging arguments.

- [KobonBoundary.defect_extension_bound, line 79](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L79)

### jext:odd-near-perfect — Odd inputs of defect at most two admit full gain

**Status: partial.** Lean proves the finite cyclic consequence assuming the boundary inequality and a wedge set; the passage from an arbitrary simple Euclidean arrangement to this cyclic data remains a manuscript argument.

- [KobonBoundary.odd_full_gain, line 51](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L51)
- [KobonBoundary.near_perfect_odd_extension, line 89](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BoundaryExtension.lean#L89)

### Equation 9 — Exterior wedge budget and obstruction to indefinite full gains

**Status: partial.** The resource inequality and cumulative geometric bound are manuscript proofs. Lean proves the contradiction conditional on the resource inequality and full gains; it does not extract the wedge budget from geometry.

- [Kobon.Iteration.no_infinite_full_gain_budget, line 105](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration.lean#L105)
- [Kobon.Iteration.two_steps_49_obstruction, line 121](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration.lean#L121)

### Figure 3 — The 49-line seed successor chain and sector capacities

**Status: partial.** Exact coordinate-to-profile audit plus Lean finite cyclic profile maxima. The values 24,23,2,2,2 belong to these saved arrangements and are not upper bounds for the maximum function. The real-coordinate identification of the finite arrays is performed by the independent audit script, not Lean.

- [Kobon.Iteration49.profile_bound_49, line 13](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration49.lean#L13)
- [Kobon.Iteration49.profile_attains_49, line 16](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration49.lean#L16)
- [Kobon.Iteration49.profile_bound_50, line 21](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration49.lean#L21)
- [Kobon.Iteration49.profile_bound_51, line 29](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration49.lean#L29)
- [Kobon.Iteration49.profile_bound_52, line 37](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration49.lean#L37)
- [Kobon.Iteration49.profile_bound_53, line 45](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration49.lean#L45)
- [scripts/audit_successor_chain.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/scripts/audit_successor_chain.py#L1)
- [experiments/2026-09-20/successor-49/chain.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-20/successor-49/chain.json#L1)

### jext:conditional-iteration — Closed form conditional on the full successor recurrence

**Status: partial.** Fully proved arithmetic implication with FullStepClaim K visibly assumed. It does not establish that recurrence for the Kobon maximum function.

- [Kobon.Iteration.gainPrefix_closed, line 31](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration.lean#L31)
- [Kobon.Iteration.full_step_iteration, line 59](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration.lean#L59)
- [Kobon.Iteration.from_49_conditional, line 76](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Iteration.lean#L76)

### Equation 10 — Unconditional 49-seed numerical target for all n at least 49

**Status: lean/general.** Unconditional real geometric lower bound floor((n-1)^2/4)+191, obtained from saved 49/50 certificates and the all-order classical baseline for n at least 51. It does not produce a nested full-gain chain.

- [Kobon.AllN.from_49_unconditional, line 504](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/AllN.lean#L504)
- [Kobon.Universal.dominates_49_target, line 125](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Universal.lean#L125)

### Result 4.1 — Verified one-step geometric BBL construction

**Status: lean/general.** One actual real-coordinate simple arrangement step for q=4r with r at least 5, positive small epsilon, saturated ordered tangent-grid input, positive central apex, and a duplicate-free certified triangle list. Produces SimpleLowerBound (2q+1) (T+q^2). Does not return the recursive compatible seed invariant, and does not include the initial q=10 step.

- [Kobon.BBLDoubling.doubling, line 15](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLDoubling.lean#L15)

### jfam:seed11 — Uniform real eleven-line seed and five-pair exterior extension

**Status: lean/general.** For every real 0<epsilon<=10^-5, actual simple real arrangement with 32 triangles, nine distinguished triangles, and five visible pairs; actual exterior arrangement with 12 lines and 37 triangles. These seed computations use kernel evaluation, with proved interval and trigonometric bounds.

- [Kobon.SeedFamily.simple_lower_bound, line 115](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SeedFamily.lean#L115)
- [Kobon.SeedFamily.distinguished_triangles, line 108](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SeedFamily.lean#L108)
- [Kobon.SeedFamily.arbitrarily_small, line 121](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SeedFamily.lean#L121)
- [Kobon.HybridBoundary.seed_visible, line 138](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/HybridBoundary.lean#L138)
- [Kobon.HybridBoundary.seed_exterior, line 148](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/HybridBoundary.lean#L148)

### Equation 11 — Odd q=10*2^t family and weaker even companions

**Status: partial.** Odd geometric family invokes published BBL iteration and the compatible seed; weaker even formula additionally invokes the manuscript defect-extension proposition. Lean proves the recurrence identities and fixed-depth certificates, not an all-depth geometric existence theorem.

- [Kobon.Families.triple_count, line 22](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Families.lean#L22)
- [Kobon.Families.closed_form, line 30](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Families.lean#L30)
- [Kobon.Families.one_triangle_gap, line 34](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Families.lean#L34)
- [Kobon.Families.gap_preserved, line 43](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Families.lean#L43)

### jfam:strong-even — Stronger even family T_q+q/2

**Status: partial.** Conditional on a recursive q/2-visible-pair invariant. Finite checkpoints and local visibility components do not prove the invariant at every depth; no unconditional infinite-family Lean theorem is claimed.

- [Kobon.Exterior.extension, line 164](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Exterior.lean#L164)
- [Kobon.HybridBoundary.seed_visible, line 138](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/HybridBoundary.lean#L138)

### jfam:seed21 — Uniform real 21-line true-grid seed

**Status: lean/general.** For every real 0<epsilon<=10^-5, the verified parameter arrangement has 132 certified triangles, 19 distinguished triangles, and 10 visible pairs; exterior extension yields 22:142. Finite interval checks in this module use native_decide, so compiler/runtime trust supplements the Lean kernel.

- [Kobon.BBLSeed21.simple_lower_bound, line 163](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLSeed21.lean#L163)
- [Kobon.BBLSeed21.all_distinguished, line 108](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLSeed21.lean#L108)
- [Kobon.BBLSeed21.distinguished_count, line 115](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLSeed21.lean#L115)
- [Kobon.BBLSeed21.all_visible, line 100](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLSeed21.lean#L100)
- [Kobon.BBLSeed21.exterior_lower_bound, line 168](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLSeed21.lean#L168)
- [Kobon.BBLSeed21.arbitrarily_small, line 179](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLSeed21.lean#L179)

### jfam:recursive-components — Next-grid saturation and sorting permutation

**Status: partial.** The named components are proved in Lean. next_saturated assumes the central output triangle and crossing order. Full iteration still needs returning a suitable seed witness, transporting its duplicate-free list, central retention independently of that list, and parameter induction; the full all-depth family is not established.

- [Kobon.BBLNextSaturation.next_saturated, line 41](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLNextSaturation.lean#L41)
- [Kobon.BBLGridReindex.inv_perm, line 20](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLGridReindex.lean#L20)
- [Kobon.BBLGridReindex.perm_inv, line 24](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLGridReindex.lean#L24)
- [Kobon.BBLGridReindex.central_left, line 34](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLGridReindex.lean#L34)
- [Kobon.BBLGridReindex.central_right, line 38](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLGridReindex.lean#L38)
- [Kobon.BBLGridReindex.next_cut, line 51](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/BBLGridReindex.lean#L51)

### jfam:seed5 — Corrected uniform five-line normalization

**Status: lean/general.** For every real 0<epsilon<=10^-5, five triangles, three distinguished triangles, two visible pairs, and exterior extension to 6:7 are proved; this does not itself formalize the whole inherited dyadic optimal family.

- [Kobon.TamuraSeed5.simple_lower_bound, line 113](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/TamuraSeed5.lean#L113)
- [Kobon.TamuraSeed5.all_distinguished, line 59](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/TamuraSeed5.lean#L59)
- [Kobon.TamuraSeed5.all_visible, line 64](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/TamuraSeed5.lean#L64)
- [Kobon.TamuraSeed5.exterior_lower_bound, line 118](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/TamuraSeed5.lean#L118)
- [Kobon.TamuraSeed5.arbitrarily_small, line 129](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/TamuraSeed5.lean#L129)

### jfam:large-completed — 321:34132, 322:34292 and 641:136532

**Status: computation.** Passed two independent exact rational counters; these arrangements are not in the Lean catalogue. No new numerical-record claim.

- [experiments/2026-09-21/hybrid-family/larger-members-verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/hybrid-family/larger-members-verification.json#L1)

### jfam:large-incomplete — 642:136852 candidate

**Status: partial.** Adjacency count and simplicity computation passed but the second independent count was interrupted; not a completed dual-counter or Lean certificate.

- [experiments/2026-09-21/hybrid-family/large-run-status.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/hybrid-family/large-run-status.json#L1)

### jfam:chart-obstruction — Fixed 81- and 161-line seeds admit no chart-only count improvement

**Status: computation.** Exact projective face census equals bounded triangle count for these particular saved seeds. This is a finite exact program calculation, not a Lean theorem or a restriction on other arrangements of the same size.

- [experiments/2026-09-20/chart_search.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-20/chart_search.py#L1)
- [research/kobon-hybrid/certificates/n081.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/kobon-hybrid/certificates/n081.json#L1)
- [research/kobon-hybrid/certificates/n161.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/kobon-hybrid/certificates/n161.json#L1)

### jfam:seed19 — Parpalak-Utkin 19-line interval seed reproduction

**Status: computation.** Exact interval calculation for 107 triangles and 17 distinguished triangles for 0<epsilon<=10^-3. The uniform interval calculation is not a Lean theorem. A single rational specialization is separately in the finite Lean catalogue; attribution to Parpalak-Utkin remains.

- [research/six-hour-2026-09-21/general-bounds/prior-seed19-interval.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/prior-seed19-interval.json#L1)
- [research/six-hour-2026-09-21/general-bounds/prior-seed19-rational.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/prior-seed19-rational.json#L1)

### jfam:inherited-families — q=4*2^t and q=18*2^t inherited odd families and even companions

**Status: external.** The odd geometric families retain Forge-Ramirez Alfonsin and Parpalak-Utkin attribution respectively; the paper's even companions use the manuscript boundary-defect argument. No new all-family Lean theorem is claimed.


### jfam:finite-11 — 11:32 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N011T00032Hb955e7c9.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N011T00032Hb955e7c9.lean#L10)

### jfam:finite-12 — 12:37 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N012T00037H8c718a33.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N012T00037H8c718a33.lean#L10)

### jfam:finite-21 — 21:132 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N021T00132H3d8bae2f.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N021T00132H3d8bae2f.lean#L10)

### jfam:finite-22 — 22:142 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N022T00142He683945e.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N022T00142He683945e.lean#L10)

### jfam:finite-41 — 41:532 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N041T00532H6d48a341.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N041T00532H6d48a341.lean#L10)

### jfam:finite-42 — 42:552 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N042T00552H7b29a6bd.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N042T00552H7b29a6bd.lean#L10)

### jfam:finite-81 — 81:2132 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N081T02132H7bc6b303.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N081T02132H7bc6b303.lean#L10)

### jfam:finite-82 — 82:2172 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N082T02172Hd75c9101.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N082T02172Hd75c9101.lean#L10)

### jfam:finite-161 — 161:8532 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N161T08532H230691d5.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N161T08532H230691d5.lean#L10)

### jfam:finite-162 — 162:8612 finite simple family checkpoint

**Status: lean/finite.** Actual finite simple real arrangement with the stated lower bound; the exact rational certificate uses native_decide and therefore compiler/runtime trust. This is a finite checkpoint, not an infinite-family proof or numerical-priority claim.

- [Kobon.Certificates.N162T08612H1512e696.simple_lower_bound, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N162T08612H1512e696.lean#L10)

### jup:section — Scope of multiplicity-sensitive upper estimates

**Status: manuscript.** All global upper assertions in this section concern even n>=4 distinct pairwise nonparallel affine lines and the total number of bounded triangular cells. They are ordinary geometric theorems in the stated subclasses, not unconditional Lean upper bounds for the unrestricted Kobon problem. The referenced source files agree with immutable source commit 99fdc8ec1ef8b1fb22c3da32b011b7361762e958.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)
- [research/six-hour-2026-09-21/general-bounds/multiplicity-budget.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/multiplicity-budget.md#L1)

### Equation 12 — Elementary-segment incidence and defect identities

**Status: manuscript.** E=sum r*t_r-n=n(n-2)-S, 3T=E-U+D1+D2, and delta=S+U-D1-D2 are proved by ordinary pair, incidence and edge-use counting. The absence of a shared segment with two ordinary endpoints is also manuscript geometry. No Lean declaration proves these identities for an arbitrary actual arrangement; CleanLineBudget receives the defect identity as an explicit hypothesis.

- [research/six-hour-2026-09-21/general-bounds/multiplicity-budget.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/multiplicity-budget.md#L1)
- [experiments/2026-09-21/general-bounds/multiplicity_budget.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/multiplicity_budget.py#L1)
- [Kobon.CleanLineBudget.parity_budget, line 18](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L18)

### Result 5.1 — Clean-line parity and charging inequality

**Status: manuscript.** For even n>=4 pairwise nonparallel arrangements, n-h<=2U+D1 follows from the supplied local parity induction and endpoint argument. The extraction of elementary edges and the charging of each clean line are not formalized. The proof adapts Blanc's simple-arrangement parity argument locally, retaining nonparallelism even away from the clean line.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)
- [experiments/2026-09-21/general-bounds/clean_line_budget.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/clean_line_budget.py#L1)
- [Kobon.CleanLineBudget.parity_budget, line 18](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L18)

### Equation 13 — Combined clean-line defect budget

**Status: partial.** The geometric assertion 2*delta>=n+2*S-h-3*D1-2*D2 is a manuscript consequence of jup:identity and jup:clean. The Lean theorem parity_budget proves the exact integer implication, allowing an extra abstract parallel-pair variable P, from incidence delta=2P+S+U-D1-D2 and charging n-h<=2U+D1+2P. Set P=0 here. It does not establish either geometric premise or validate the argument for parallel arrangements.

- [Kobon.CleanLineBudget.parity_budget, line 18](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L18)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:parallel-obstruction — Why simply excluding parallel-participating lines does not repair charging

**Status: manuscript.** The three-parallel-verticals plus one-horizontal example shows that the horizontal line can be clean while all transverse pieces at its crossings are unbounded. This is a direct geometric counterexample to the attempted local argument with that weakened hypothesis, not a claimed counterexample to Blanc's theorem.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### Result 5.2 — Fan bounds at an r-fold point

**Status: partial.** The lemma contains three assertions with different formal scopes. The bound d1<=2r-3 is fully proved in Lean from an actual local CyclicFan.Geometry object; extracting that object from an arbitrary arrangement remains manuscript work. The capacity d1+d2<=2r and resulting 3d1+d2<=6r-6 are ordinary geometric/arithmetic consequences, not a dedicated global extraction theorem. The stronger d2<=1 => d1<=2r-4 is manuscript only.

- [Kobon.CyclicFan.Geometry, line 20](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L20)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L96)
- [Kobon.FanCount.ordinary_shared_ray_bound, line 37](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanCount.lean#L37)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:fan-propagation — Opposite-support propagation along an actual geometric fan

**Status: lean/general.** At an ordinary radial endpoint, any two other indexed incident lines coincide. For a FanStrip of actual real points and indexed supporting lines, all opposite supporting lines agree and the two outer endpoints cannot lie on opposite rays from the center. No aggregate run-bound conclusion is assumed. The input FanStrip explicitly supplies incidences, ordinary internal endpoints, nondegenerate triangles and opposite lines avoiding the center.

- [Kobon.FanGeometry.ordinary_nonradial_unique, line 24](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanGeometry.lean#L24)
- [Kobon.FanGeometry.FanStrip, line 47](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanGeometry.lean#L47)
- [Kobon.FanGeometry.FanStrip.ofTriangles, line 65](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanGeometry.lean#L65)
- [Kobon.FanGeometry.FanStrip.all_opposites_eq, line 113](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanGeometry.lean#L113)
- [Kobon.FanGeometry.no_opposite_end_fan, line 160](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanGeometry.lean#L160)

### jup:fan-local-count — Actual cyclic fan has no long selected run and at most 2r-3 selected rays

**Status: lean/general.** For r>=3 and Geometry n r L, no r-1 consecutive selected ordinary shared rays can occur, and selected.card<=2*r-3. Geometry supplies 2r actual radial endpoints with antipodal partners, ordinary selected endpoints and the actual opposite supporting lines of adjacent triangular sectors. The no-long-run property is proved, not assumed; automatic construction of Geometry from a whole arrangement is not in these declarations.

- [Kobon.CyclicFan.Geometry, line 20](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L20)
- [Kobon.CyclicFan.Geometry.no_long_run, line 44](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L44)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L96)

### jup:fan-window — Cyclic window count used in the fan proof

**Status: lean/general.** For a Finset S in ZMod(2*r), r>=3, and an explicit missing selected ray in every window of length r-1, ordinary_shared_ray_bound proves S.card<=2*r-3. Its proof establishes the intermediate double-count inequality (r-1)*S.card<=2*r*(r-2). The intermediate inequality is not separately named, but window_bound is a named helper. CyclicFan supplies the run premise from actual geometry.

- [Kobon.FanCount.window_bound, line 18](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanCount.lean#L18)
- [Kobon.FanCount.ordinary_shared_ray_bound, line 37](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanCount.lean#L37)
- [Kobon.CyclicFan.Geometry.no_long_run, line 44](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L44)

### jup:fan-sharp — Sharper fan bound when at most one shared side ends at another core point

**Status: manuscript.** d2<=1 implies d1<=2*r-4 by the cyclic nontriangular-sector argument in the manuscript. The ordinary run obstruction used inside the argument is formalized, but no Lean theorem formalizes this sharper sector argument or its complete conclusion. In CleanLineBudget.at_most_two_multiple_points its summed consequence D1<=2*I-4*q is an explicit premise.

- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L96)
- [Kobon.CleanLineBudget.at_most_two_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L58)

### Result 5.3 — Restricted upper-estimate theorem

**Status: partial.** The complete theorem about actual even pairwise nonparallel arrangements is a manuscript theorem. Its global edge incidence, charging, fan extraction and sharper d2<=1 arguments are not all in Lean. The weighted and at-most-two-core integer deductions have formal conditional counterparts; neither is an unconditional upper theorem about all Euclidean arrangements.

- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L73)
- [Kobon.CleanLineBudget.at_most_two_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L58)
- [Kobon.CleanLineBudget.triangles_from_defect, line 106](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L106)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### Equation 14 — Weighted defect inequality for arbitrary core size

**Status: partial.** The manuscript proves 2*delta>=n+sum_{r>=3}(2*r^2-11*r+6)*t_r. The formal general_multiplicity_budget proves n+2*S-7*I+6*q<=2*delta from explicit integer incidence, charging, core-incidence h<=I, fan-run D1<=2*I-3*q, and fan-ray D1+2*D2<=2*I premises. The connection of those sums and premises to an arbitrary arrangement remains ordinary geometry.

- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L73)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L96)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### Equation 15 — At most two finite multiple points: upper polynomial plus one

**Status: partial.** For even n=2*m>=4 and at most two core points, the manuscript proves T<=floor(n*(n-5/2)/3)+1. The integer theorem at_most_two_multiple_points proves m-3<=delta assuming the incidence identity, charging, D1<=2*I-4*q, h<=I-D2, D2<=1, q between 0 and 2, and weighted surplus 0<=2*S-7*I+15*q. multiplicity_surplus proves the local surplus polynomial for r>=3. triangles_from_defect proves the corresponding inequality 3*T<=n*(n-2)-m+3; rounding to the displayed floor is ordinary arithmetic here.

- [Kobon.CleanLineBudget.multiplicity_surplus, line 50](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L50)
- [Kobon.CleanLineBudget.at_most_two_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L58)
- [Kobon.CleanLineBudget.triangles_from_defect, line 106](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L106)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:zero-one-core — Sharper zero-core and one-core defects

**Status: partial.** The manuscript gives delta>=n/2 when q=0 and delta>=n/2-1 when q=1, including a single core point of any multiplicity. Lean one_triple_point proves only the single TRIPLE-point conditional arithmetic case, from incidence, charging, D1<=2 and h<=3. It must not be cited as a direct theorem for one core point of arbitrary multiplicity. The general manuscript proof uses the surplus polynomial and integer parity.

- [Kobon.CleanLineBudget.one_triple_point, line 40](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L40)
- [Kobon.CleanLineBudget.multiplicity_surplus, line 50](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L50)
- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L73)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:high-multiplicity — Simple-style polynomial under nonnegative total core weight

**Status: partial.** The manuscript consequence T<=floor(n*(n-5/2)/3) holds if the total weight sum(2*r^2-11*r+6)*t_r is nonnegative, in particular if every core multiplicity is at least five. Lean high_multiplicity_weight proves the local weight is at least one for r>=5; nonnegative_core_weight proves n<=2*delta from an explicit nonnegative weight and the other abstract geometric budgets. The weights -9 at r=3 and -6 at r=4 are direct arithmetic and show why this does not cover arbitrary low-multiplicity cores.

- [Kobon.CleanLineBudget.high_multiplicity_weight, line 85](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L85)
- [Kobon.CleanLineBudget.nonnegative_core_weight, line 92](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L92)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### jup:attainment — Externally attributed exact attainment at 8, 14, 26 and 50 lines

**Status: partial.** The lower witnesses 8:15, 14:54, 26:204 and 50:792 are Lean-certified finite lower bounds. Their exact full triangle counts, nonparallel status and exactly two triple points are documented by exact computational censuses; the generic lower_bound declarations do not assert upper bounds or core cardinalities. The 14-line example must be Maiorana certificate-01 (or another two-triple Maiorana example), NOT the PU gallery 14-line witness, which has five triple points. Equality with the restricted manuscript upper theorem proves sharpness only in its stated subclass. Discovery attributions remain external.

- [Kobon.Certificates.N008T00015Ha1380810.lower_bound, line 39](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N008T00015Ha1380810.lean#L39)
- [Kobon.Certificates.N014T00054Hd47aea63.lower_bound, line 84](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hd47aea63.lean#L84)
- [Kobon.Certificates.N026T00204Hf71379c4.lower_bound, line 246](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N026T00204Hf71379c4.lean#L246)
- [Kobon.Certificates.N050T00792H3d40cb58.lower_bound, line 858](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N050T00792H3d40cb58.lean#L858)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/verification.json#L1)
- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/verification.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/verification.json#L1)

### Figure 4 — Shared-fan figure and geometric certificate

**Status: lean/finite.** The six depicted cells have nonempty, uncut and pairwise disjoint open interiors in Lean; each highlighted radial segment is elementary and shared by the appropriate two cells. The caption's formal claim is supported in this constructive sense. Exhaustivity of the complete triangle census and the endpoint-type count d1=d2=3 are exact computational additions, not named SharedFan theorems.

- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L51)
- [Kobon.SharedFan.interiors_uncut, line 66](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L66)
- [Kobon.SharedFan.interiors_nonempty, line 70](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L70)
- [Kobon.SharedFan.interiors_disjoint, line 73](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L73)
- [Kobon.SharedFan.radial_elementary, line 113](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L113)
- [research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json#L1)

### jup:shared-fan-census — Exact shared-fan census and endpoint types

**Status: computation.** The exact arrangement counter finds exactly six triangular cells, four triple points, and at the center (1,1) six incident shared segments split as d1=3 and d2=3. This complete census is reproducible from the six coordinates; it is not an exhaustive-count theorem in SharedFan. The six certified cells and elementary sides themselves are formally established.

- [research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json#L1)
- [experiments/2026-09-21/general-bounds/shared_fan_counterexample.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/shared_fan_counterexample.py#L1)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L51)

### jup:clement-reading — Scope of the Clément–Bader wording objection

**Status: external.** The recorded source audit identifies page 2, Lemma 1 item 3 of the OEIS-hosted Clément–Bader draft. The six-side example refutes only a literal local incidence reading; it neither disproves the draft's final theorem nor rules out a corrected global assignment argument. This bibliographical/interpretive claim is not a Lean theorem.

- [research/six-hour-2026-09-21/general-bounds/upper-bound-scope-audit.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/upper-bound-scope-audit.md#L1)
- [Kobon.SharedFan.six_shared_sides, line 51](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SharedFan.lean#L51)

### jup:smoothing-maiorana — Four exact local resolutions of Maiorana's 14:54 witness

**Status: computation.** Maiorana certificate-01 has precisely the two zero triple determinants on supports {0,4,10} and {0,11,12}. The independent offsets realize all four resolution-sign choices, preserve every initially nonzero triple-determinant sign and leave pair directions fixed; exact triangle counts are 52,52,53,52. The script checks each resolution by adjacency and the independent interior-sign verifier. This finite enumeration is not a Lean theorem.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)
- [experiments/2026-09-21/general-bounds/maiorana_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/maiorana_resolutions.py#L1)

### jup:smoothing-classification — Exhaustion of sufficiently small simple perturbations

**Status: manuscript.** Finite continuity preserves all initially nonzero pair-direction and triple-determinant signs. The two formerly zero triple signs exhaust the possible nearby simple chirotopes, all represented in the exact enumeration; hence every sufficiently small simple perturbation of this fixed 14-line input has at most 53 triangular cells. The sign-stability/classification argument is ordinary geometry, not Lean, and makes no statement about distant arrangements.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [experiments/2026-09-21/general-bounds/maiorana_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/maiorana_resolutions.py#L1)

### jup:smoothing-gallery — All 132 recorded local resolutions of seven gallery inputs

**Status: computation.** The saved exact reports contain 4+32+64+4+16+8+4=132 resolutions for n=8,14,20,26,32,38,50. Their maxima are respectively 14,51,114,203,313,448,791. Private-line offsets realize every binary local choice; the verifier checks all originally nonzero determinant signs, simplicity and equality of the two exact triangle sets. These are fixed-input computations, not a formalized general smoothing theorem or an upper bound on arbitrary simple arrangements.

- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/collinear-resolution-model.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/collinear-resolution-model.json#L1)
- [experiments/2026-09-21/general-bounds/collinear_resolution.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/collinear_resolution.py#L1)
- [experiments/2026-09-21/general-bounds/check_collinear_resolutions.py, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/experiments/2026-09-21/general-bounds/check_collinear_resolutions.py#L1)

### jup:smoothing-loss — Failure of nondecreasing and loss-at-most-one local smoothing shortcuts

**Status: computation.** For the fixed Maiorana input the best nearby simple count drops from 54 to 53, ruling out universal nondecreasing local smoothing. For the PU gallery 14- and 20-line types the exact local maxima drop by three, and at 32 and 38 by two, ruling out universal loss-at-most-one local resolution. Transfer from exhaustive sign choices to all sufficiently small perturbations uses the stated manuscript continuity argument; no global lower or upper optimum is changed.

- [research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/all-local-resolutions.json#L1)
- [research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/maiorana14/INDEPENDENT-REVIEW.md#L1)

### jup:formalization-status — Boundary between completed formal components and remaining global geometry

**Status: partial.** Completed: actual FanStrip geometry, the CyclicFan bridge from real local fan data, cyclic counting, the finite SharedFan example, and conditional integer budgets. Remaining manuscript components: global elementary-edge and cyclic-sector extraction, the incidence identity, clean-line charging, and the sharper d2<=1 fan refinement. Parallel classes are outside the section's theorem. No source declaration establishes an unrestricted upper bound from these modules.

- [Kobon.FanGeometry.no_opposite_end_fan, line 160](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanGeometry.lean#L160)
- [Kobon.CyclicFan.Geometry.selected_card_le, line 96](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CyclicFan.lean#L96)
- [Kobon.FanCount.ordinary_shared_ray_bound, line 37](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FanCount.lean#L37)
- [Kobon.CleanLineBudget.general_multiplicity_budget, line 73](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L73)
- [Kobon.CleanLineBudget.at_most_two_multiple_points, line 58](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/CleanLineBudget.lean#L58)
- [research/six-hour-2026-09-21/general-bounds/clean-line-parity.md, line 1](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/research/six-hour-2026-09-21/general-bounds/clean-line-parity.md#L1)

### Equation 3 — Classical trigonometric line family

**Status: lean/general.** This is the definition used in the formal construction, inherited from Furedi-Palasti rather than a new family.

- [Kobon.FurediPalasti.line, line 10](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/FurediPalasti.lean#L10)

### Equation 2 — Blanc's simple even-order upper bound

**Status: external.** Cited from [Blanc's paper](https://arxiv.org/abs/0801.2845), not a Lean theorem of this repository. Its simplicity hypothesis is essential. In particular, the equality at order 44 combines this external upper theorem with a finite Lean lower certificate.


## Complete finite certificate catalog

All 138 coordinate identities are listed individually, including 104 simple witnesses. These are lower-bound certificates, not claims of numerical novelty or unrestricted optimality. Each certificate uses native evaluation; the links expose the exact theorem and its assumptions. The machine-readable map preserves coordinate hashes and original evidence paths. Multiple rows with the same order and count can represent different coordinate witnesses.

| Lines | Triangles | Class | Lower-bound theorem | Simple-witness theorem |
|---:|---:|---|---|---|
| 3 | 1 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N003T00001H05c82de6.lean#L20) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N003T00001H05c82de6.lean#L10) |
| 4 | 2 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N004T00002H0e541bd5.lean#L22) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N004T00002H0e541bd5.lean#L10) |
| 5 | 5 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N005T00005H948a0bdf.lean#L26) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N005T00005H948a0bdf.lean#L10) |
| 6 | 7 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N006T00007H6ea9ebaa.lean#L29) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N006T00007H6ea9ebaa.lean#L10) |
| 7 | 11 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N007T00011He6b9a626.lean#L34) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N007T00011He6b9a626.lean#L10) |
| 8 | 14 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N008T00014H2a63f4d9.lean#L38) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N008T00014H2a63f4d9.lean#L10) |
| 9 | 21 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N009T00021H6ebbed82.lean#L46) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N009T00021H6ebbed82.lean#L10) |
| 10 | 25 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N010T00025Hb767c427.lean#L51) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N010T00025Hb767c427.lean#L10) |
| 11 | 32 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N011T00032Hb955e7c9.lean#L59) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N011T00032Hb955e7c9.lean#L10) |
| 12 | 38 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N012T00038H38f69f38.lean#L66) | — |
| 13 | 47 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N013T00047Hddec1f78.lean#L76) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N013T00047Hddec1f78.lean#L10) |
| 14 | 53 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00053H45157b2f.lean#L83) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N014T00053H45157b2f.lean#L10) |
| 15 | 65 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N015T00065H4d3bf3b4.lean#L96) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N015T00065H4d3bf3b4.lean#L10) |
| 16 | 72 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N016T00072H391cf79a.lean#L104) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N016T00072H391cf79a.lean#L10) |
| 17 | 85 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N017T00085H7cf3c061.lean#L118) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N017T00085H7cf3c061.lean#L10) |
| 18 | 93 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N018T00093Hedb6246a.lean#L127) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N018T00093Hedb6246a.lean#L10) |
| 19 | 107 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N019T00107Ha2f32bdb.lean#L142) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N019T00107Ha2f32bdb.lean#L10) |
| 20 | 116 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N020T00116Hadc03eed.lean#L152) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N020T00116Hadc03eed.lean#L10) |
| 21 | 133 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N021T00133H36bae754.lean#L170) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N021T00133H36bae754.lean#L10) |
| 22 | 143 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N022T00143H54396c64.lean#L181) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N022T00143H54396c64.lean#L10) |
| 23 | 161 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N023T00161H969ad7d3.lean#L200) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N023T00161H969ad7d3.lean#L10) |
| 24 | 172 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N024T00172He63e906b.lean#L212) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N024T00172He63e906b.lean#L10) |
| 25 | 191 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N025T00191Hb568bffb.lean#L232) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N025T00191Hb568bffb.lean#L10) |
| 26 | 203 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N026T00203He61b423c.lean#L245) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N026T00203He61b423c.lean#L10) |
| 27 | 225 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N027T00225H7d6ae9a0.lean#L268) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N027T00225H7d6ae9a0.lean#L10) |
| 28 | 238 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N028T00238H56ef2acb.lean#L282) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N028T00238H56ef2acb.lean#L10) |
| 29 | 261 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N029T00261Hd4805c25.lean#L306) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N029T00261Hd4805c25.lean#L10) |
| 30 | 275 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N030T00275Hdcfe649a.lean#L321) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N030T00275Hdcfe649a.lean#L10) |
| 31 | 299 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N031T00299H70f23b94.lean#L346) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N031T00299H70f23b94.lean#L10) |
| 32 | 314 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N032T00314H9ab78b00.lean#L362) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N032T00314H9ab78b00.lean#L10) |
| 33 | 341 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N033T00341H95f3b770.lean#L390) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N033T00341H95f3b770.lean#L10) |
| 34 | 357 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N034T00357Hfbde0a76.lean#L407) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N034T00357Hfbde0a76.lean#L10) |
| 35 | 385 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N035T00385H9ee99af6.lean#L436) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N035T00385H9ee99af6.lean#L10) |
| 36 | 402 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N036T00402H3fc01b7d.lean#L454) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N036T00402H3fc01b7d.lean#L10) |
| 37 | 431 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N037T00431H11f0bde7.lean#L484) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N037T00431H11f0bde7.lean#L10) |
| 38 | 449 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N038T00449H46ad5a32.lean#L503) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N038T00449H46ad5a32.lean#L10) |
| 39 | 469 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N039T00469Hcf24d7d3.lean#L524) | — |
| 40 | 494 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N040T00494H785374ca.lean#L550) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N040T00494H785374ca.lean#L10) |
| 41 | 533 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N041T00533H01e2ef66.lean#L590) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N041T00533H01e2ef66.lean#L10) |
| 42 | 553 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N042T00553H2bdc9d67.lean#L611) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N042T00553H2bdc9d67.lean#L10) |
| 43 | 587 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N043T00587H861d8be2.lean#L646) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N043T00587H861d8be2.lean#L10) |
| 44 | 608 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N044T00608Hb5277675.lean#L668) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N044T00608Hb5277675.lean#L10) |
| 45 | 645 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N045T00645H3dc6e882.lean#L706) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N045T00645H3dc6e882.lean#L10) |
| 46 | 667 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N046T00667H32b8ca2f.lean#L729) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N046T00667H32b8ca2f.lean#L10) |
| 47 | 690 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N047T00690Hd8af27fc.lean#L753) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N047T00690Hd8af27fc.lean#L10) |
| 48 | 720 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N048T00720H5e9767e7.lean#L784) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N048T00720H5e9767e7.lean#L10) |
| 49 | 767 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N049T00767H957e6f15.lean#L832) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N049T00767H957e6f15.lean#L10) |
| 50 | 791 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N050T00791H2ea22b55.lean#L857) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N050T00791H2ea22b55.lean#L10) |
| 51 | 817 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N051T00817Hbd215f67.lean#L884) | — |
| 52 | 850 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N052T00850H4b0d823a.lean#L918) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N052T00850H4b0d823a.lean#L10) |
| 53 | 884 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N053T00884H723d7eff.lean#L953) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N053T00884H723d7eff.lean#L10) |
| 54 | 918 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N054T00918H915abb8e.lean#L988) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N054T00918H915abb8e.lean#L10) |
| 55 | 954 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N055T00954Hea7675d9.lean#L1025) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N055T00954Hea7675d9.lean#L10) |
| 56 | 990 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N056T00990Hde8a415c.lean#L1062) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N056T00990Hde8a415c.lean#L10) |
| 57 | 1045 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N057T01045H9a1d337c.lean#L1118) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N057T01045H9a1d337c.lean#L10) |
| 58 | 1073 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N058T01073Hd988db55.lean#L1147) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N058T01073Hd988db55.lean#L10) |
| 59 | 1102 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N059T01102Hfd3b4280.lean#L1177) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N059T01102Hfd3b4280.lean#L10) |
| 60 | 1140 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N060T01140H16af6d0b.lean#L1216) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N060T01140H16af6d0b.lean#L10) |
| 12 | 37 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N012T00037H8c718a33.lean#L65) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N012T00037H8c718a33.lean#L10) |
| 39 | 468 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N039T00468H5c5b0b26.lean#L523) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N039T00468H5c5b0b26.lean#L10) |
| 51 | 816 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N051T00816H6fa6b7d9.lean#L883) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N051T00816H6fa6b7d9.lean#L10) |
| 5 | 3 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N005T00003H6265d6a7.lean#L24) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N005T00003H6265d6a7.lean#L10) |
| 6 | 4 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N006T00004H7e060e9a.lean#L26) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N006T00004H7e060e9a.lean#L10) |
| 19 | 107 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N019T00107H5d2a7588.lean#L142) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N019T00107H5d2a7588.lean#L10) |
| 21 | 126 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N021T00126Hf18756b7.lean#L163) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N021T00126Hf18756b7.lean#L10) |
| 5 | 5 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N005T00005Hdd0748b7.lean#L26) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N005T00005Hdd0748b7.lean#L10) |
| 7 | 10 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N007T00010H4b5bb6e9.lean#L33) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N007T00010H4b5bb6e9.lean#L10) |
| 21 | 132 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N021T00132H3d8bae2f.lean#L169) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N021T00132H3d8bae2f.lean#L10) |
| 22 | 142 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N022T00142He683945e.lean#L180) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N022T00142He683945e.lean#L10) |
| 41 | 532 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N041T00532H6d48a341.lean#L589) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N041T00532H6d48a341.lean#L10) |
| 42 | 552 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N042T00552H7b29a6bd.lean#L610) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N042T00552H7b29a6bd.lean#L10) |
| 81 | 2132 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N081T02132H7bc6b303.lean#L2229) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N081T02132H7bc6b303.lean#L10) |
| 82 | 2172 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N082T02172Hd75c9101.lean#L2270) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N082T02172Hd75c9101.lean#L10) |
| 161 | 8532 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N161T08532H230691d5.lean#L8709) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N161T08532H230691d5.lean#L10) |
| 162 | 8612 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N162T08612H1512e696.lean#L8790) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N162T08612H1512e696.lean#L10) |
| 9 | 19 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N009T00019He16410b8.lean#L44) | — |
| 15 | 61 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N015T00061H7c38d54f.lean#L92) | — |
| 21 | 127 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N021T00127Hb8dcff22.lean#L164) | — |
| 27 | 217 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N027T00217H6670a2b1.lean#L260) | — |
| 33 | 331 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N033T00331H25fd8f0c.lean#L380) | — |
| 48 | 715 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N048T00715Hba6f5baa.lean#L779) | — |
| 99 | 3169 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N099T03169H4fef38d8.lean#L3284) | — |
| 195 | 12481 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N195T12481Hcd3497db.lean#L12692) | — |
| 195 | 12480 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N195T12480H1b9230fb.lean#L12691) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N195T12480H1b9230fb.lean#L10) |
| 44 | 602 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N044T00602H0b0250bf.lean#L662) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N044T00602H0b0250bf.lean#L10) |
| 99 | 3168 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N099T03168Ha0ea3082.lean#L3283) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N099T03168Ha0ea3082.lean#L10) |
| 39 | 470 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N039T00470H30caa6f7.lean#L525) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N039T00470H30caa6f7.lean#L10) |
| 47 | 691 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N047T00691Hfac44af1.lean#L754) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N047T00691Hfac44af1.lean#L10) |
| 48 | 721 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N048T00721H2fb5ef0d.lean#L785) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N048T00721H2fb5ef0d.lean#L10) |
| 51 | 818 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N051T00818Hc18e1baf.lean#L885) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N051T00818Hc18e1baf.lean#L10) |
| 53 | 885 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N053T00885H6bc5b14d.lean#L954) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N053T00885H6bc5b14d.lean#L10) |
| 54 | 919 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N054T00919Ha254c1b4.lean#L989) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N054T00919Ha254c1b4.lean#L10) |
| 55 | 955 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N055T00955H202625a3.lean#L1026) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N055T00955H202625a3.lean#L10) |
| 59 | 1103 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N059T01103Hba482375.lean#L1178) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N059T01103Hba482375.lean#L10) |
| 60 | 1141 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N060T01141H9bc5096c.lean#L1217) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N060T01141H9bc5096c.lean#L10) |
| 65 | 1365 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N065T01365Hb1dcbeb4.lean#L1446) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N065T01365Hb1dcbeb4.lean#L10) |
| 66 | 1397 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N066T01397H327ecbb9.lean#L1479) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N066T01397H327ecbb9.lean#L10) |
| 99 | 3170 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N099T03170Hea507e2d.lean#L3285) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N099T03170Hea507e2d.lean#L10) |
| 129 | 5461 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N129T05461H6dae0012.lean#L5606) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N129T05461H6dae0012.lean#L10) |
| 130 | 5525 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N130T05525He0559b54.lean#L5671) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N130T05525He0559b54.lean#L10) |
| 195 | 12482 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N195T12482H5413dd7b.lean#L12693) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N195T12482H5413dd7b.lean#L10) |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hd47aea63.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H18bbcff4.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H78f750c0.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H912da8ec.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H91349990.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H9c871e10.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hb3dcae0b.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H9219cdaa.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hd2babc1b.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H2b34ca22.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hfa427b3d.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H1ec1fd5c.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H3e5d182f.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H17f8c052.lean#L84) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054Hc472f972.lean#L84) | — |
| 14 | 52 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00052H2eb83dc2.lean#L82) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N014T00052H2eb83dc2.lean#L10) |
| 14 | 53 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00053H5e6068f5.lean#L83) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N014T00053H5e6068f5.lean#L10) |
| 14 | 52 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00052Hb3f4749f.lean#L82) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N014T00052Hb3f4749f.lean#L10) |
| 14 | 52 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00052Hc6615430.lean#L82) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N014T00052Hc6615430.lean#L10) |
| 8 | 14 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N008T00014Hebff5868.lean#L38) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N008T00014Hebff5868.lean#L10) |
| 14 | 51 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00051Hd67e7a6b.lean#L81) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N014T00051Hd67e7a6b.lean#L10) |
| 20 | 114 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N020T00114Hbc312fc8.lean#L150) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N020T00114Hbc312fc8.lean#L10) |
| 26 | 203 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N026T00203H5452b4ff.lean#L245) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N026T00203H5452b4ff.lean#L10) |
| 32 | 313 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N032T00313H018f9fc6.lean#L361) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N032T00313H018f9fc6.lean#L10) |
| 38 | 448 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N038T00448H7d59f504.lean#L502) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N038T00448H7d59f504.lean#L10) |
| 50 | 791 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N050T00791H6bde86a3.lean#L857) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N050T00791H6bde86a3.lean#L10) |
| 8 | 15 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N008T00015Ha1380810.lean#L39) | — |
| 14 | 54 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N014T00054H10576514.lean#L84) | — |
| 20 | 117 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N020T00117H382171ac.lean#L153) | — |
| 26 | 204 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N026T00204Hf71379c4.lean#L246) | — |
| 32 | 315 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N032T00315H5914f2bb.lean#L363) | — |
| 36 | 402 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N036T00402Hce43a107.lean#L454) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N036T00402Hce43a107.lean#L10) |
| 38 | 450 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N038T00450H8ba2bdb1.lean#L504) | — |
| 42 | 553 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N042T00553H9849e255.lean#L611) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N042T00553H9849e255.lean#L10) |
| 50 | 792 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N050T00792H3d40cb58.lean#L858) | — |
| 19 | 107 | Simple | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N019T00107H6e8ca6f5.lean#L142) | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/SimpleCertificates/N019T00107H6e8ca6f5.lean#L10) |
| 6 | 6 | General | [proof](https://github.com/alejandrozu/kobon-proof/blob/99fdc8ec1ef8b1fb22c3da32b011b7361762e958/Kobon/Certificates/N006T00006Haf8f599e.lean#L28) | — |

## Readiness boundary

This package is suitable for scholarly review with the distinctions above. It is not ready to be described as a complete formalization of every manuscript result. Before making that stronger claim, complete the global boundary/segment extraction, clean-line charging and sharper fan bridge, and compatible-seed recursive induction. External optimality results and numerical-priority questions require their own literature evidence. The original 60-page account remains byte-for-byte unchanged.
