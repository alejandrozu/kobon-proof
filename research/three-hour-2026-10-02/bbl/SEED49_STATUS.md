# 49-line compatible seed: verification boundary

Final release status: the complete native parameter-box check was stopped at
19:12 UTC on 2 October after approximately 30 minutes without a completed
compiler result. The 49-line seed and its dependent family files are
**not completed Lean results**. All five sources are preserved in
[`../drafts/`](../drafts/README.md), outside the active library and build manifest.

## Completed evidence

* `Kobon/BBLTangent48Bounds.lean` proves rational enclosures for all23 actual
  positive numbers `tan(kπ/48)`, `1≤k≤23`, using only the three standard Lean
  axioms. Its generator and exact rational endpoints are in this directory.
* The independent exact interval certificate in
  `constructions/uniform-grid49/uniform-seed.json` uses48 fixed rational
  reciprocal slopes and proves strict determinant signs throughout
  `0<ε≤1/100`. Its rational midpoint has767 triangles and47 distinguished
  triangles; both exact triangle checkers passed.
* `constructions/uniform-grid49/visibility.json` checks24 visible pairs for
  normal `(1,−2)` on that whole epsilon interval, including the rightmost pair.
  The last graph slope is `1/3`, so its projected rightward direction is
  positive.
* An isolated Lean check using literal copied seed definitions proves the
  sorted graph identity and the positive central height
  `(5000000000/212664377)ε`. This checks those proof bodies without claiming
  that the uncompleted seed certificate compiled. See
  `seed49-isolated-graph-axioms.log` and the preserved
  [standalone check sources](checks/README.md).
* The closed-form arithmetic was independently checked in Lean:
  `T_t=768·4^t−1` on `48·2^t+1` lines, and the prospective even companion is
  `T_t+24·2^t` on `48·2^t+2` lines. These are conditional targets until the
  actual uniform seed premise is discharged.
* `UpperSimpleOptimality` already proves the classical simple-arrangement
  upper bound directly from any finite `SimpleLowerBound` witness. Therefore
  the completed49 seed would give actual odd simple optimality, rather than
  just a polynomial comparison.

The external scripts were independently read for sign stability and interval
soundness. Fixed pair normals, strict old-triple determinants, and ordered
`Y0` intercepts preserve the triangle tests. Each visibility numerator is
affine in epsilon; the endpoint interval checks and fixed derivative signs
imply the uniform visibility statement. This is computer-assisted evidence,
separate from the uncompleted Lean parameter-box computation.

## Archived dependency chain

`BBLSeed49.lean`, `BBLSeed49Normalized.lean`, `BBLSeed49Exterior.lean`,
`BBLSeed49Visible.lean`, and `BBL49VerifiedFamilies.lean` form one uncompleted
dependency chain. They were moved together under
`research/three-hour-2026-10-02/drafts/` before the release freeze.
They must all pass before promotion to the active library; the strengthened
verifier rejects silently unbuilt active sources.

The known odd family is the `s=t+3` tail of `6·2^s+1` in
Bartholdi--Blanc--Loisel, [Theorem1.3](https://arxiv.org/html/0706.0723v1).
Completing this chain would be a Lean realization and optimality proof of a
known family, not a new numerical record.

## Concrete continuation plan

1. Profile the finite direction, simplicity, triangle, and visibility checks
   separately. The interrupted full build does not identify which obligation
   dominates; do not infer a failed mathematical predicate from elapsed time.
2. Split the large finite checks into independently compiled batches and prove
   their conjunction implies the existing `Parametric` predicates. Keep the
   exact exported rational data and sign conventions unchanged.
3. `ParametricCached` already proves equivalence of materialized coefficient
   forms with the original checks. No speedup for the complete 49-line build
   has been established; measure it before choosing that optimization.
4. Compile the seed, normalization, exterior, visible-seed, and family modules
   in dependency order, then run the full source and axiom audit. Only after
   that success may the 49-seed family enter `RecursiveEnvelope`.
