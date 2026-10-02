# Proof index: 2 October 2026 research session

This index records the mathematical scope of the new declarations. Individual
successful checks are documented in the linked audits; the release-wide build
status is recorded separately in `verification/lean-summary.json`. A declaration
with hypotheses is a proved implication, not a proof that its hypotheses hold
for every arrangement.

**Trust notation.** **K** means Lean kernel proofs using only `propext`,
`Classical.choice`, and `Quot.sound`. **N** additionally inherits explicitly
reported `native_decide` certificate axioms. **E** means an exact external
computation, not a Lean theorem. Conditional results are identified in the scope
column independently of their trust notation.

## Closed recursive construction

For every natural number `t`, the completed concrete theorems construct simple
real straight-line arrangements with

\[
q_t=10\,2^t,\qquad
K_s(q_t+1)\ge (q_t^2-4)/3,\qquad
K_s(q_t+2)\ge (q_t^2-4)/3+q_t/2.
\]

The proof is an actual geometric iteration. Its quantifiers allow a smaller
positive epsilon interval at each depth; they do not assert that one fixed
epsilon works at every depth. The concrete seed at order21 supplies the
iteration, and the separately proved11-line seed supplies the initial term.
The construction builds on the BBL doubling method. Closing the recursive
geometric invariant and boundary visibility is the present formalization
advance; the formulas are not claimed as new numerical records.

| File | Main declarations | Trust and precise scope |
|---|---|---|
| [Permutation](../../Kobon/Permutation.lean) | `triangle_pullback_support`, `transport_list`, `transport_list_of_injective` | **K.** Actual triangle support and equal-length, duplicate-free witness transport under bounded label bijections/injections. |
| [BBLRecursiveWitness](../../Kobon/BBLRecursiveWitness.lean) | `canonical_step` | **K.** From an actual simple saturated tangent-grid seed with positive central apex and `r≥5`, constructs the next simple arrangement, at least `T+(4r)^2` triangles, the next saturated grid, and positive central apex. The epsilon bound is explicit. |
| [BBLRecursiveGrid](../../Kobon/BBLRecursiveGrid.lean) | `forward`, `backward`, `graph_reindex` | **K.** The actual coefficient identity and inverse label maps put the output on the next tangent grid. |
| [BBLRecursiveSeed](../../Kobon/BBLRecursiveSeed.lean) | `Seed`, `seed_step`, `compatible_step`, `seed_lower_bound` | **K.** Closes the whole geometric seed record under `r→2r`; `Seed` includes simplicity, all consecutive distinguished triangles, central orientation, and a valid counted triangle list. |
| [BBLInfinite](../../Kobon/BBLInfinite.lean) | `UniformSeed`, `uniform_step`, `uniform_iterate`, `infinite_family`, `triangleCount_identity` | **K.** A uniformly available seed on some positive epsilon interval gives actual arrangements at every finite depth. A uniform seed remains an explicit premise of the generic theorem. |
| [BBLSeed21Normalized](../../Kobon/BBLSeed21Normalized.lean) | `graph_identity`, `saturated`, `central_height`, `seed_with_slopes`, `compatible` | **N.** Discharges the odd seed premise for `r=5,T=132,0<ε≤10⁻⁵`; the19 caps, count, and central height `5ε/2` are transported from the existing actual21-line certificate. |
| [BBLRecursiveChoice](../../Kobon/BBLRecursiveChoice.lean) | `canonical_eventually` | **K.** Retains the complete one-step witness for all sufficiently small positive pencil scales, for each analytically admissible delta. This permits intersection with the extra boundary requirements. |
| [BBLProjection](../../Kobon/BBLProjection.lean) | `graph_projection_mono`, `graph_projection_strict_mono`, `crossing_order_transfer` | **K.** Transfers actual row order from horizontal to oblique projection when the projected graph directions have the required sign. |
| [BBLRightmost](../../Kobon/BBLRightmost.lean) | `factor_sine`, `pencil_max_eventually`, `canonical_row_eventually` | **K.** Proves the actual last-intersection property on the old rightmost line, using the seed's clean rightward ray and positive slope. |
| [BBLNextBoundary](../../Kobon/BBLNextBoundary.lean) | `positive_directions_eventually`, `crossing_order_oblique`, `next_rightmost_boundary` | **K.** Derives the next rightmost clean ray from actual auxiliary graph equations and row order. |
| [BBLVisibleReindex](../../Kobon/BBLVisibleReindex.lean) | `transport_list_of_injective`, `visible_congr`, `admissible_pullback` | **K.** Exact transport of actual visible-pair lists and projection admissibility. |
| [BBLVisibleSeed](../../Kobon/BBLVisibleSeed.lean) | `VisibleSeed`, `even_lower_bound` | **K.** Defines the additional explicit boundary invariant and applies the proved exterior extension to obtain `T+V` actual triangles. |
| [BBLEvenStep](../../Kobon/BBLEvenStep.lean) | `visible_retained_eventually`, `canonical_visible_step` | **K.** The geometric doubling output has at least `V+2r` visible pairs; the old and new visible pairs are actually constructed. |
| [BBLEvenRecursive](../../Kobon/BBLEvenRecursive.lean) | `visible_seed_step` | **K.** Closes the complete visible seed record under doubling. Its projection normal satisfies the explicit positive-horizontal-component hypothesis. |
| [BBLEvenInfinite](../../Kobon/BBLEvenInfinite.lean) | `UniformVisibleSeed`, `uniform_iterate`, `infinite_even_family`, `visibleCount_full` | **K.** Generic iteration with a uniform visible seed. Initial visibility `2r` gives full visibility `2r·2^t` at depth `t`. |
| [BBLSeed21Visible](../../Kobon/BBLSeed21Visible.lean) | `compatible` | **N.** Discharges the visible seed premise for `r=5,T=132,V=10`, normal `(10,−13)`, and `0<ε≤10⁻⁵`. |
| [BBLVerifiedFamilies](../../Kobon/BBLVerifiedFamilies.lean) | `odd_family`, `even_family`, `eleven_odd_family`, `eleven_even_family` | **N.** Unconditional geometric lower bounds in the displayed formulas; no unresolved geometric hypothesis remains. The original11/12 initial cases are kernel proofs, while the overall family inherits the21-line seed's finite native checks. |
| [BBLFamilyBenchmarks](../../Kobon/BBLFamilyBenchmarks.lean) | `odd_baseline_gain`, `even_baseline_gain`, `odd_polynomial_gap`, `even_simple_polynomial_gap`, `previous_envelope`, `strict_previous_tail` | **K** for the arithmetic comparisons. The family lies one below the indicated odd/even classical polynomial benchmarks. These equalities do **not** formalize those expressions as universal upper bounds. The strict-tail comparison is against this repository's previous complete verified envelope, not an assertion of literature priority. |
| [RecursiveEnvelope](../../Kobon/RecursiveEnvelope.lean) | `all_n`, `previous_le`, `odd_family_le`, `even_family_le`, `strict_previous_tail` | **N** for all-order existence; **K** for comparisons. The executable finite maximum retains the previous all-order bound and the two recursive families. It strictly improves the former envelope at orders `10·2^(t+5)+1` and `10·2^(t+5)+2` for every `t`. |
| [BBLForgeConditional](../../Kobon/BBLForgeConditional.lean) | `odd_family`, `even_family`, `odd_polynomial_exact`, `even_simple_polynomial_exact` | **K, conditional.** The formulas `(1024·4^t−1)/3` and that quantity plus `16·2^t` require respectively `UniformSeed 8 341` and a corresponding `UniformVisibleSeed 8 341 16 w`. This module alone does not supply those seeds. The inherited optimal family is attributed to Forge–Ramírez Alfonsín and the BBL method. |

The concrete odd family uses four existing native certificate checks in
`BBLSeed21`: `directions`, `simple`, `triangle_checks`, and
`distinguished_checks`. The even family also uses `admissible_check` and
`visible_checks`. No new custom axiom or `sorry` was introduced. Details:
[recursive proof audit](bbl/RECURSIVE_PROOF_AUDIT.md) and
[family evidence](bbl/README.md).

## Exact obstruction for one prescribed sign system

| File or artifact | Main declarations | Trust and precise scope |
|---|---|---|
| [StrictLinearCertificate](../../Kobon/StrictLinearCertificate.lean) | `infeasible`, `homogeneous_infeasible` | **K.** Positive weighted linear contradiction certificates; these are generic implications from the explicitly supplied identities and positivity. |
| [BBLTangentAlgebra](../../Kobon/BBLTangentAlgebra.lean) | `tan_quartic`, `tan_root_interval`, `quartic_root_unique`, `real_root_characterization` | **K.** `tan(π/20)` satisfies `t⁴−4t³−14t²−4t+1=0` and is the unique root in `(3/20,17/100)`. |
| [BBLTangentValues](../../Kobon/BBLTangentValues.lean) | `value_eq_tan` | **K.** The explicit cubic expressions equal the actual tangent values `tan(kπ/20)` for `k<10`. |
| [BBLTangent48Bounds](../../Kobon/BBLTangent48Bounds.lean) | `tan_48_1_bounds` through `tan_48_23_bounds` | **K.** Actual rational enclosures for all23 positive tangent values required by a48-intercept seed, with widths at most `5·10⁻³⁶`. The proofs use `tan(π/3)=√3`, half-angle identities, and complementary-angle inverses. Python only proposes rational endpoints. |
| [BBLGridObstruction](../../Kobon/BBLGridObstruction.lean) | `actual_grid_infeasible`, `actual_grid_orientation_impossible` | **K.** Ten specified orientation signs are impossible on the actual20-intercept tangent grid, for every real epsilon and arbitrary real slopes. This is one explicit sign system, not a classification of every optimal21-line arrangement. |
| [BBLObstructionReduction](../../Kobon/BBLObstructionReduction.lean) | `two_columns_follow`, `reduced_infeasible` | **K.** Two omitted weighted columns follow from the affine row identities and distinct omitted intercepts; the reduced system yields a contradiction. |
| [Local robustness audit](bbl/LOCAL_ROBUSTNESS.md) | `verify_local_robustness.py`, `local-robustness.json` | **E.** Exact outward interval Gaussian elimination proves persistence of the ten-sign obstruction under independent intercept perturbations of radius `10⁻³` on its11 used intercepts. The interval computation itself is outside Lean. |

The broader finite chart search has its own input-coverage limitations. In
particular, all charts of a supplied set of representatives must not be
described as all perfect21-line arrangements without a separate exhaustive
classification-to-input bridge. See [obstruction scope](bbl/TANGENT_OBSTRUCTION.md).

## Actual incidence extraction and local upper-bound geometry

Throughout the certificate applications, the lines are **pairwise
nonparallel** and the triangles form a **finite injective certified family**.
That family may be a proper subset of the arrangement's triangular cells.
Unused and shared edges are counted relative to that selected family. The
identity is exact for this semantics; it does not define or compute a maximal
Kobon number. Multiple intersection points are allowed unless a statement
explicitly assumes otherwise.

| File | Main declarations | Trust and precise scope |
|---|---|---|
| [UpperElementaryEdges](../../Kobon/UpperElementaryEdges.lean) | `predicate_all_sides_elementary` | **K.** The three actual sides of each certified triangle are consecutive intersection segments on their supporting lines. |
| [UpperEdgeCapacity](../../Kobon/UpperEdgeCapacity.lean) | `at_most_two` | **K.** At most two pairwise interior-disjoint nondegenerate actual triangles can have the same base segment. |
| [UpperTriangleIncidence](../../Kobon/UpperTriangleIncidence.lean) | `exact_incidence`, `certificate_incidence` | **K.** Derives `3T = used sides + shared sides`; the certificate application derives disjointness from the actual triangle predicates. |
| [UpperSharedEdge](../../Kobon/UpperSharedEdge.lean) | `Pair.has_nonordinary_endpoint`, `Pair.not_both_endpoints_ordinary` | **K.** An actual shared side cannot have two ordinary endpoints, for indexed supporting lines and disjoint triangle interiors. |
| [UpperSharedIncidence](../../Kobon/UpperSharedIncidence.lean) | `shared_has_nonordinary_endpoint`, `oneCore_has_both_kinds`, `core_incidence` | **K.** Actual shared-side endpoint classification plus its finite incidence partition. The generic counting identity alone is combinatorial; the geometric certificate application supplies the classification. |
| [UpperVertexBudget](../../Kobon/UpperVertexBudget.lean) | `multiplicity_identity`, `point_line_incidence`, `line_interval_budget` | **K.** Extracts actual intersection multiplicities, point-line incidences, and consecutive bounded interval counts. |
| [UpperEdgeInventory](../../Kobon/UpperEdgeInventory.lean) | `edge_cardinality`, `predicate_side_mem_edges`, `certificate_defect_identity` | **K.** From actual nonparallel lines with `n≥2` and a finite injective certified triangle family, constructs the side inventory and proves `δ=S+U−D₁−D₂`. No supplied global capacity, edge-count, or incidence identity is needed. |
| [UpperCoreExtraction](../../Kobon/UpperCoreExtraction.lean) | `defect_identity`, `certificate_oneCore_classification`, `simple_arrangement_upper` | **K.** Restricts multiplicity loss to the actual nonordinary core and identifies a `D₁` edge as having exactly one ordinary endpoint. The empty-core corollary proves the classical simple-arrangement inequality `3T≤n(n−2)`. |
| [UpperSimpleOptimality](../../Kobon/UpperSimpleOptimality.lean) | `core_empty`, `certificate_upper`, `simple_lower_bound_upper`, `simple_lower_bound_floor` | **K.** Discharges empty-core and finite-family extraction directly from `NoParallel`, `NoConcurrent`, and `SimpleLowerBound`. For `n≥2`, every such witness obeys `3T≤n(n−2)` and `T≤floor(n(n−2)/3)`. This is a complete formalization of the classical simple bound, not a new unrestricted upper bound. |
| [UpperCoreLineIncidence](../../Kobon/UpperCoreLineIncidence.lean) | `core_line_budget` | **K.** Derives the actual incidence inequality `D₂+h≤I` by counting consecutive core vertices along each supporting line. |
| [UpperCoreCombinatorics](../../Kobon/UpperCoreCombinatorics.lean) | `core_edge_count`, `three_core_edge_count`, `core_surplus` | **K.** Derives `D₂≤binom(q,2)`, its `q≤3` specialization, and nonnegative summed multiple-point surplus. |
| [UpperFan](../../Kobon/UpperFan.lean) | `Sectors.all_sectors_of_extremal`, `Sectors.core_shared_card_eq_three_of_extremal`, `Sectors.weighted_local_bound` | **K, explicit local interface.** Actual cyclic fan data, with its orientation and incidence hypotheses supplied, imply the local sector-count conclusions. Whole-arrangement extraction of this interface is not proved here. |
| [UpperFanSupport](../../Kobon/UpperFanSupport.lean) | `Sectors.extremal_core_not_in_halfplane` | **K, explicit local interface.** The three core-ended rays of a full extremal fan cannot all lie in the indicated closed half-plane under the positive cyclic orientation and support-line hypotheses. |
| [UpperCoreBoundary](../../Kobon/UpperCoreBoundary.lean) | `bound_at_supported_core`, `CoreFamily.sum_ordinary_bound` | **K, conditional assembly.** A supplied family of actual fans and endpoint-to-core incidence maps gives the aggregate local bound. The source does not extract that entire family from an arbitrary arrangement. |
| [UpperTripleFan](../../Kobon/UpperTripleFan.lean) | `extremal_triple_fans_not_adjacent`, `incompatible_full_triple_fans` | **K, explicit matching interface.** Neighboring full triple fans are incompatible under the stated matching across their common edge. |
| [UpperCoreBudget](../../Kobon/UpperCoreBudget.lean) | `weighted_defect_with_core_edges`, `at_most_three_multiple_points`, `triangles_from_three_core_defect` | **K, conditional aggregate arithmetic.** The integer inequalities imply the advertised restricted bounds when their fan, charging, and incidence premises are supplied. This is not an unconditional new upper bound for all arrangements. |
| [UpperCleanHalfplane](../../Kobon/UpperCleanHalfplane.lean) | `common_halfplane`, `clean_crossings_injective`, `ordinary_vertex_pairs_on_line`, `clean_crossing_card`, `clean_line_no_pair_partition` | **K.** An actual clean line has `n−1` distinct crossings; one common open half-plane contains another intersection on every transverse line. Triangles at its ordinary crossings have a side on the line. For even `n`, an actual two-element partition of its crossings is impossible. Extracting that partition from degree-one edge assumptions remains separate. |
| [UpperCleanEdges](../../Kobon/UpperCleanEdges.lean) | `incident_positive_edge`, `incident_negative_edge`, `common_bounded_side` | **K.** Turns the common half-plane intersections into actual consecutive bounded segments incident to the clean-line crossings. |
| [UpperCleanPairing](../../Kobon/UpperCleanPairing.lean) | `pair_indices_consecutive`, `incident_positive_unique`, `incident_negative_unique` | **K.** Actual consecutive-edge indices and half-plane signs give uniqueness of the selected incident segment. The global map is assembled in UpperCleanCharging below. |
| [UpperCleanCover](../../Kobon/UpperCleanCover.lean) | `actual_base_cover`, `clean_line_bad_degree`, `certificate_clean_line_charge` | **K.** Extracts the actual pair cover under the degree-one assumption and contradicts its parity. Every clean line in an even-order nonparallel arrangement with `n≥3` therefore has an actual incident charge edge that is unused or has one ordinary endpoint and one core endpoint, relative to the supplied finite injective certified triangle family. The aggregate charge-fiber count is supplied by UpperCleanCharging below. |
| [UpperCleanCharging](../../Kobon/UpperCleanCharging.lean) | `charge_line_unique`, `oneCore_ordinary_card`, `certificate_clean_line_budget` | **K.** Actual even-order clean-line charging: `n-h <= 2U+D1` for nonparallel real lines, `n>=3`, and any finite injective certified triangle family. The charge map and its finite fibers are extracted, with no charging premise. |
| [UpperEvenSimpleOptimality](../../Kobon/UpperEvenSimpleOptimality.lean) | `shared_empty`, `certificate_even_upper`, `simple_lower_bound_even_upper`, `simple_lower_bound_even_floor` | **K.** The actual incidence identity and extracted charging imply `6T <= n(2n-5)` and its floor form for every simple certificate witness with even `n>=4`. This formalizes the classical simple even upper bound; it is not an unrestricted nonsimple bound. |
| [BBLFamilyOptimality](../../Kobon/BBLFamilyOptimality.lean) | `odd_upper`, `even_upper`, `odd_window`, `even_window` | **K** for both universal upper halves; **N** for existence and the combined windows. At `n=10*2^t+1,+2`, actual simple arrangements realize the verified family counts, and every simple certificate witness has at most that count plus one. This upgrades the earlier polynomial benchmark comparison to a genuine formal optimality window. |

The independently audited interpretation is in
[INDEPENDENT_SCOPE_AUDIT.md](bbl/INDEPENDENT_SCOPE_AUDIT.md); the upper branch's
precise completion report and hashed checks are in
[LOCAL_FAN_PROGRESS.md](upper/LOCAL_FAN_PROGRESS.md) and
[upper/verification/summary.json](upper/verification/summary.json).

## Supporting checker result

[ParametricCached](../../Kobon/ParametricCached.lean), declarations `cache_eq`,
`simple_sound`, and `triangle_eq`, proves that materializing parameter forms in
arrays preserves the exact checker and its soundness (**K**). No measured
performance improvement is asserted.

## Pending work and release boundary

The unrestricted quantitative one-line successor recurrence, including a
repeatable optimal49-line successor chain, is still not proved. On the upper
side, whole-arrangement cyclic-fan extraction, matching, and summation remain
open for the proposed general nonsimple improvements. Actual clean-line
charging and the classical simple upper bounds are now fully proved.

The33-line uniform seed's long check was stopped without completion; it and its
two normalization/visibility bridges are preserved in [drafts](drafts/), outside
the active release. Consequently the Forge-family row above is intentionally
conditional. The48-grid tangent enclosures are proved, while the candidate
49-line compatible seed must be reported only at its separately achieved proof
status. Its target odd family `48·2^t+1` is the `s=t+3` tail of the already known
`6·2^s+1` family in Bartholdi--Blanc--Loisel,
[Theorem1.3](https://arxiv.org/html/0706.0723v1). Its formalization and simple
optimality proof must not be described as a new numerical family.

The verifier now schedules every transitive consumer of the finite certificate
collection after the bounded certificate phase, audits every active source
through the root import graph, and refuses a complete status if any active
source is unbuilt, unaudited, added, removed, or changed during the build.
