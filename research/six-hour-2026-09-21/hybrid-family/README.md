# Hybrid-family research record

Research session: 22 September 2026, beginning 04:36 UTC. This directory records
the hybrid-family branch of the six-hour investigation. Authorship is Alejandro
Zarzuelo Urdiales with computational and formalization assistance. Attribution
of inherited constructions remains with their original authors.

## Mathematical result under investigation

The existing compatible eleven-line seed has 32 triangles. BBL doubling gives
`q+1` lines and `(q²−4)/3` triangles for `q=10·2^t`. The new working boundary
argument in [boundary-invariant.md](boundary-invariant.md) supports the stronger
even consequence

\[
K_s(q+2)\ge (q^2-4)/3+q/2.
\]

This improves the previous infinite even guarantee by one triangle. The finite
values through 162 already attained this stronger count. It is not a new finite
record at those orders, and priority of the infinite statement is unestablished.
`K_s` means simple affine straight-line arrangements. The simple upper bound
must not be applied to the unrestricted classical Kobon number.

The working proof is an ordinary mathematical argument using the published BBL
construction. It is **not yet an end-to-end infinite-family Lean theorem**. As
of 07:03 UTC, the full one-step geometric doubling theorem has passed Lean:
`BBLDoubling.doubling` takes an actual simple saturated tangent-grid seed with
q=4r≥20, central triangle above Y0, and T certified triangles, and proves the
existence of a simple real arrangement with2q+1 lines and at leastT+q² triangles.
Its crossing order and cap retention are proved rather than assumed. The
next-grid distinguished-segment saturation is also proved, using the canonical
support labels. Whole-witness transport, infinite iteration, and the stronger
even-family visibility invariant remain separate obligations.

## Formal components

These modules use the standard Lean axioms `propext`, `Classical.choice`, and
`Quot.sound`, except for the explicitly marked finite native certificate.

| Module | Proved content |
|---|---|
| `Kobon/HybridBoundary.lean` | Parametric-box visibility soundness; all-small-ε seed11 visibility; actual exterior12:37. |
| `Kobon/BBLExtrema.lean` | Visibility from intersection maxima, converse maxima, preservation criterion, graph projection order. |
| `Kobon/BBLTangentBounds.lean` | Sharp rational enclosures for true `tan(kπ/20)`, obtained from exact algebra and half-angle identities. |
| `Kobon/BBLSeed21.lean` | Actual true-grid parametric21:132 family, ten visible pairs, rightmost positive small slope and extremal old row, exterior22:142. Finite checks use `native_decide`. |
| `Kobon/BBLMaximization.lean` | Discrete sine-grid gap and a quantitative perturbation lemma. |
| `Kobon/BBLAnalytic.lean` | Uniform tangent/cotangent bounds and angle separation. |
| `Kobon/BBLTriangles.lean` | An actual empty triangle follows from two consecutive supporting sides; both index orientations are proved. |
| `Kobon/BBLRowOrder.lean` | All-size integer key bounds, injectivity, and absence of intervening crossings next to an old support. |
| `Kobon/BBLIntersection.lean` | Exact real-line BBL pair-crossing formula, displacement formula, and complementary-pair formula. |
| `Kobon/BBLPersistence.lean` | Strict visibility is open; a finite pencil near a non-supporting old line preserves an old visible wedge. Triangle preservation is also developed here. |
| `Kobon/BBLCentral.lean` | The actual central trigonometric maximizer, and its persistence first in δ and then in the scale ratio; the final theorem concerns actual real-line intersections. |
| `Kobon/BBLGrid.lean` | Exact tangent-sum reduction, complementary/noncomplementary identities, and signs on the half-angle grid. |
| `Kobon/BBLProfiles.lean` | Strict order from disjoint real cut intervals; finite continuity preserves all strict comparisons. |
| `Kobon/BBLGridCuts.lean` | Strictly ordered actual tangent cuts, including the exceptional values −ε,0,+ε; exact anchor identities. |
| `Kobon/BBLPencilLimits.lean` | Actual pair crossings move to the required side of their tangent anchors; the complementary crossings diverge to their correct exterior rays. |
| `Kobon/BBLPencilProfiles.lean` | For every q=4r, r≥5, every permitted ε, and every new pair, all sufficiently small positive δ give the exact interval profile prescribed by the integer row model. |
| `Kobon/BBLPencilRegularity.lean` | Positive perturbations simultaneously realize every pair profile and make all new slope factors nonzero and distinct. |
| `Kobon/BBLCrossingCoordinates.lean` | A continuous coordinate extension at κ=0 agrees with every actual intersection when κ≠0 and the old/new slopes are separated. |
| `Kobon/BBLRealization.lean` | The full actual crossing order, including the horizontal row, and strict injectivity of every new row hold for all sufficiently small κ≠0. |
| `Kobon/BBLRealizedPencil.lean` | For every q=4r≥20, every permitted ε and every simple old graph arrangement on the prescribed grid, actual positive δ and κ give a simple real arrangement of 2q+1 lines with at least q² genuine mixed triangles. |
| `Kobon/BBLCanonicalPencil.lean` | Exact equality with the rotated perturbation pencil used by persistence, plus old/new intercept order and slope-sign facts. |
| `Kobon/BBLNextSaturation.lean` | Every consecutive pair in the next sorted grid supports an actual triangle with Y0: all noncentral gaps are proved mixed triangles, and the central gap is the retained central triangle. The theorem uses canonical support labels. |
| `Kobon/BBLDoubling.lean` (root assembly) | Full one-step geometric existence theorem: a simple saturated tangent-grid q+1-line seed with T triangles and central apex above Y0 gives a simple2q+1-line arrangement with at leastT+q² triangles, for q=4r≥20. No external crossing-order or retained-triangle premise remains. |

The construction-search branch contributes `BBLCount`, `BBLRowGeometry`,
`BBLCaps`, and subsequent cap-envelope modules. Those files prove the count and
geometric soundness of the crossing model; they do not alone prove that the
trigonometric pencil realizes it. Check the root formalization manifest for the
final build and trust status.

## A simpler qualitative proof architecture

The new pencil can be written

\[
M_i:\quad y=\kappa\left(\sin(2\beta_i)+\delta/\tan\beta_i\right)
                 (x-\tan\beta_i).
\]

Two observations substantially simplify the remaining proof.

1. Every old visible wedge not involving `Y0` persists as `κ→0`, because its
   visibility test against `Y0` is strict in a simple arrangement. Thus at most
   the one right-visible `Y0` wedge is lost. There is no need to treat the two
   exceptional central rays separately in this qualitative argument.
2. The intersection of two new lines is independent of `κ`. With `t=tan β_i`,
   `u=tan β_k`, its x coordinate is

   \[
   \frac{2tu(t+u)}{2tu(1-tu)-\delta(1+t^2)(1+u^2)}.
   \]

   Its displacement from `(t+u)/(1−tu)` has an exact rational sign. For a fixed
   new line the nonexceptional limits are distinct tangent-grid points; only
   old-new versus new-new comparisons need this displacement sign. This suggests
   choosing `δ` small first and then `κ` small compared with the resulting gaps.

The published BBL proposition fixes `δ=q⁻⁶` and `κ=m_min·q⁻¹⁰`. It does not state
the arbitrary-small two-scale variant verbatim. Therefore the qualitative
architecture still needs its own geometric realization proof; it must not be
silently substituted for the published quantified theorem.

## Crossing model and independent checks

[row_model.py](row_model.py) uses `q=2h`, old crossing keys `4j+2`, and explicit
integer keys for crossings of the `q+1` auxiliary lines (the q new lines plus
`Y0`). A mixed triangle `(old_j,U_i,U_k)` corresponds to

\[
|\operatorname{key}(i,k)-(4j+2)|<4.
\]

There are two old neighbors for each auxiliary pair except for exactly q
exterior pairs, giving `2·C(q+1,2)−q=q²` mixed triangles. The remaining `q−2`
old-old cap rows and the retained central triangle replace the old triangles
touching `Y0` one for one.

The script checked 85 even sizes through640 and matched every auxiliary row of
the exact rational21/41/81/161 arrangements. These finite checks are diagnostic
evidence; the independent all-size Lean proofs are the mathematical certificate.
The report is [row-model-verification.json](row-model-verification.json).

## Larger exact witnesses

`generate_larger_members.py` writes into
`experiments/2026-09-21/hybrid-family/`. So far:

| Lines | Triangles | Exact counter time | Coordinate file size | Largest rational component |
|---:|---:|---:|---:|---:|
|321|34132|313 seconds|680247 bytes|916 decimal digits|
|322|34292|411 seconds|683237 bytes|985 decimal digits|
|641|136532|4786 seconds|1675338 bytes|1103 decimal digits|

Both the adjacency counter and the independent direct sign counter agree; the
arrangements are simple. These are reproducible exact coordinate certificates,
not routine Lean certificates and not priority claims. The optional run was
stopped at 06:45 UTC after the user shortened the research budget to three
hours. The642-line coordinates passed the adjacency counter and simplicity
checks before being written, but its independent direct counter was interrupted.
It is recorded as partial evidence, not a completed dual-counter certificate.

## Search attempts and negative evidence

* `experiments/2026-09-21/hybrid-family/search_compatible21.py` performs a bounded
  floating reciprocal-slope search for a perfect tangent-grid21:133 seed while
  enforcing all19 distinguished triangles. Floating proposals are accepted as
  results only after both exact rational counters agree. The completed one-hour
  run tested11547910 proposals, accepted2432350 moves, and retained a pool of250
  states. Its best remained132; it produced no133 candidate and therefore made
  zero new exact-candidate checks. This is negative search evidence, not a proof
  that a compatible perfect21-line seed cannot exist.
* `lp_compatible21.py` fixes the optimal21 oriented matroid, augments it by the
  original infinity line, and tries all462 ordered choices of a new `Y0` and
  infinity line. Determinant and direction-order constraints are linear in the
  reciprocal slopes. All3234 LPs at ε=0 and six positive scales failed to find a
  strict feasible margin. This only excludes the tested transfer formulation
  numerically; it is not a mathematical impossibility certificate.

## Attribution and source checks

The primary BBL source is
[Bartholdi–Blanc–Loisel, arXiv:0706.0723](https://arxiv.org/html/0706.0723v1).
Proposition3.1 gives the tangent-grid doubling and explicit slopes; Remark3.2
explains choosing the exceptional parameter for a finite iteration target.
Theorem1.3 supplies straight-line optimal families `q=6·2^t` and `q=14·2^t`;
its `q=18·2^t` assertion is for pseudolines and cannot be imported as a
straight-line result. The introduction already describes optimal even
extensions of perfect odd arrangements, so recovering the dyadic5/9/17/33/65
family and its even extensions is verification of known numerical bounds.

A normalization issue deserves explicit checking: the central old slopes are
taken with opposite signs and the central triangle above `Y0`. A shear fixing
`Y0` can arrange this for the relevant seeds. An exact finite witness with both
central slopes negative does not by itself certify uniform iteration for all
arbitrarily small ε with the published fixed scale.

## Remaining work

1. The full one-step q² gain is now proved, including actual crossing order,
   simplicity, all cap replacements, and finite witness assembly.
2. Transport the whole witness list and graph data through the grid permutation.
   The next distinguished-segment saturation is now proved in canonical labels.
3. Assemble the visibility invariant and induction with explicit ε quantifiers.
4. Audit numerical priority independently; distinguish a new seed, a new
   infinite consequence, a new formal proof, and a new finite best-known bound.
5. Pursue partial insertion or a compatible seed with smaller defect if a
   stronger all-n envelope is wanted. The present sparse family alone does not
   improve every n.

### Concrete next proof interfaces

Strengthen the one-step count theorem's conclusion to return the constructed
arrangement and its next seed data. `BBLNextSaturation` now proves that the
required distinguished triangles are among the mixed triangles adjacent to Y0,
except for the retained central triangle. Use the explicit permutation in
`BBLGridReindex` to sort the old and new intercepts into the next tangent grid;
the central pair stays unchanged and the rightmost support becomes the last
new line. The old central apex therefore remains above Y0.

The iteration invariant should quantify
`∀ ε, 0<ε<ε₀ → ∃ slopes, compatible_seed ε slopes`. It should not require one
fixed set of slopes, one fixed κ, or one fixed positive ε to work for infinitely
many steps. At each finite step, δ and κ may depend on the current ε and old
slopes. Shrinking ε₀ below the next half-grid gap is legitimate. Starting from
the checked21:132 seed would then give q=20·2^t and `(q²−4)/3` triangles; the
separate11-line base recovers the earlier q=10 checkpoint.

For the stronger even family, combine the old visibility-retention theorem
(at most one visible pair uses Y0) with the2r auxiliary pairs and one old/new
central pair constructed in `BBLVisible`. The relative maximum on the old
rightmost line is proved in `BBLCentral`; remaining assembly must compare it
with all old intersections, transfer x-order to the fixed normal `(10,−13)`,
and preserve the rightmost-line invariant under the grid permutation. These
steps are distinct from proving the q² triangle gain. Their completion would
justify the extra even-family triangle in Lean; the present component list
must not be mistaken for that completed theorem.
