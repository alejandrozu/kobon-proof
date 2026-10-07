# The remaining geometric charging problem

This note records the current obstruction to an unrestricted upper-bound
improvement. It separates proved geometry from the finite discharging
relaxation and from research targets. It is not a solution claim.

## Actual objects and proved resources

All counts come from an injective family of certified empty triangles in an
actual arrangement of pairwise nonparallel real lines. In this section every
multiple intersection is a triple core. At a core let `a` count shared edges
to ordinary vertices, `d` count shared edges to other cores, and `m` count
marked ordinary ports. Write `W=6−2a−d`. Then

`ΣW=2(δ−U)`, where `δ=n(n−2)−3T`.

Let `A0` be unmarked full two-cap cores `(a,d,m)=(2,4,0)`. Let `B15`
count `(a,d)=(1,5)` cores. The full two-cap sources are antipodal stars.
Their actual shared edges supply at least two nonfull targets per source:

`2 A0 ≤ Σx`,

where `x(p)` counts neighbours from `A0` at a nonfull target and is zero
at full targets. The poor targets are the cores with `a≤1` and `a+d≤2`.
Marked ports and edges from `A0` compete for the same actual poor-target
resources:

`Σm + Σ_poor x ≤ Σ_poor d`.

Neither inequality is an assumed numerical oracle in the final geometric
theorems. Their proofs use actual fan extraction, elementary segments,
occurrence matching and injective charging. See
[UnmarkedCrossResources](../../../Kobon/UpperOpenMathUnmarkedCrossResources.lean)
and [AntipodalConeIncidence](../../../Kobon/UpperOpenMathAntipodalConeIncidence.lean).

## Why the coefficient improves

Set

`Q=W+unpaidWeight+2m−2d·1_poor`,

where `unpaidWeight` is two at an `A0` source, one at a `B15` core,
and zero elsewhere. The finite local classification proves

`x ≤ 2Q + 4x·1_poor + 1_J`,

where `J` is the exceptional type `(a,d,x)=(1,3,3)`. This classification
only uses displayed finite inequalities and port counts. Summing it with
the two actual resources above yields

`4δ+2A0+2B15+J ≥ 4U`.

The crucial geometric improvement is that **J is empty**: a one-cap triple
core of shared-core degree three has a neighbour outside `A0`. This is
derived from selected triangle sides and actual adjacent fan rays, not
from an abstract graph drawing. Consequently

`2δ+A0+B15 ≥ 2U`.

Proofs: [RefinedHalfCurvatureWeights](../../../Kobon/UpperOpenMathRefinedHalfCurvatureWeights.lean),
[OneCapThreeCoreDegree](../../../Kobon/UpperOpenMathOneCapThreeCoreDegree.lean),
[HalfCurvature](../../../Kobon/UpperOpenMathHalfCurvature.lean).

Keeping the positive terms in that same pointwise classification gives the
stronger, fully completed actual theorem

`4δ+2A0+2B15 ≥ 4U+6E3+5P21`,

where `E3` counts `a=3` cores and `P21` counts `(a,d)=(2,1)` cores. The
partial type has at least one marked port; this is derived from its actual
fan, rather than assumed as a capacity bonus. Proofs:
[HalfCurvatureGainWeights](../../../Kobon/UpperOpenMathHalfCurvatureGainWeights.lean),
[HalfCurvatureGain](../../../Kobon/UpperOpenMathHalfCurvatureGain.lean).

The stronger actual bound two at all nonfull recipients of degree `a+d≤4`
now gives another complete inequality. Define `J13` to count exactly
`(a,d,x)=(1,3,2)`. The finite pointwise rule becomes

`x ≤ Q+2x·1_poor+1_J13−3·1_E3−2·1_P21`,

and its fully extracted actual consequence is

`2δ+B15+J13 ≥ 2U+3E3+2P21`.

This replaces the total source count by a particular double-recipient
count. This intermediate result is complementary to the half-coefficient
bound. The full geometric exclusion of `J13` is now complete, as described
below. Proofs of the intermediate result:
[DoubleRecipientWeights](../../../Kobon/UpperOpenMathDoubleRecipientWeights.lean),
[DoubleRecipientCurvature](../../../Kobon/UpperOpenMathDoubleRecipientCurvature.lean).

## Components retain a separate escape penalty

For each actual connected component `s`, write `A_s,B_s` for its two
correction counts. The earlier paid component argument and the new local
half argument combine into the proved inequality

`δ ≥ U + Σ_s max(1−A_s−ceil(B_s/2), −floor((A_s+B_s)/2))`.

This chooses the stronger rule inside each component. It can improve on
choosing the stronger of two bounds after summing the entire arrangement.
No restriction on component order or shared-core degree is required.
Proof: [ClosedHalfCurvature](../../../Kobon/UpperOpenMathClosedHalfCurvature.lean).

The completed stronger hybrid retains the positive types inside each
component:

`δ ≥ U + Σ_s max(1−A_s−ceil(B_s/2), ceil((6E_s+5P_s−2A_s−2B_s)/4))`.

Both its soundness and its dominance over the earlier hybrid are proved
in `certificate_hybrid_gain_component_defect` and `hybrid_gain_dominates`
in that same module. The integer ceilings apply to signed component costs;
they must not be replaced by truncated natural subtraction.

The completed double-recipient estimate is also local on every closed
component, without a size or degree restriction:

`2H_s+B_s+J_s ≥ 3E_s+2P_s`.

Here `H_s` is its signed component cost and `J_s` counts its `(1,3)`
recipients with two neighbours from sources in that component. Taking the
maximum of the previous hybrid score and
`ceil((3E_s+2P_s−B_s−J_s)/2)` is proved sound before summing components.
See [ClosedDoubleRecipientCurvature](../../../Kobon/UpperOpenMathClosedDoubleRecipientCurvature.lean).

There is already a fully proved class where the source and double-recipient
corrections both disappear. Any closed component containing at most one
antipodal source, regardless of its size, satisfies

`2H_s+B_s ≥ 3E_s+2P_s`.

Two distinct antipodal sources have four neighbours each, are nonadjacent,
and have at most two common neighbours. This implies that a closed
component of at most seven cores contains at most one source. Consequently,
if every component has at most seven cores, the whole arrangement satisfies

`δ ≥ U+Σ_s ceil((3E_s+2P_s−B_s)/2)`.

An adaptive version uses this score whenever the actual source count is
at most one and retains the previous score otherwise. Both soundness and
dominance are checked in
[SingleSourceCurvature](../../../Kobon/UpperOpenMathSingleSourceCurvature.lean) and
[SingleSourceComponents](../../../Kobon/UpperOpenMathSingleSourceComponents.lean).
This statement does not assert `δ≥U+number_of_components` for size seven;
the displayed `B_s` correction is still present.

## The completed double-recipient exclusion

The normalized one-cap, three-core fan has four consecutive shared rays.
Two nonadjacent proposed antipodal source tips give exactly six cases.
The ordinary-middle case forces incompatible indexed supports; the
core-middle case forces contradictory affine area signs; the opposite case
forces nested outward antipodes to coincide. All reflected orientations and
the extraction from actual triangle occurrences are now complete.

Consequently `(1,3)` has at most one antipodal neighbour and `J13=0`.
The `(2,1)` partial type has exactly one marked shared ray, whose neighbour
is poor; it therefore has no antipodal source neighbour. This raises its
positive coefficient, producing

`2δ+B15 ≥ 2U+3(E3+P21)`.

The strongest component score simplifies to

`max(1−A_s−ceil(B_s/2), ceil((3E_s+3P_s−B_s)/2))`.

The global and component bounds, and dominance over the old half-gain
score, are fully checked with the standard logical axioms. There is no
component-size or degree assumption, but all actual cores must be triple.
Proofs: [N13NoDouble](../../../Kobon/UpperOpenMathN13NoDouble.lean),
[N13ActualNoDouble](../../../Kobon/UpperOpenMathN13ActualNoDouble.lean),
[PartialRecipients](../../../Kobon/UpperOpenMathPartialRecipients.lean),
[N13Curvature](../../../Kobon/UpperOpenMathN13Curvature.lean).

## The finite relaxation is weaker than actual geometry

The final `(1,2)` recipient theorem retains one more positive unit for
each such core. With `N12_s` its count in a component, the completed
strongest score is

`max(1−A_s−ceil(B_s/2), ceil((3E_s+3P_s+N12_s−B_s)/2))`.

Globally `2δ+B15≥2U+3E3+3P21+N12`. The geometric restriction,
closed-component extraction, summation and dominance over the preceding
source-free score all pass with the standard logical axioms:
[N12Recipient](../../../Kobon/UpperOpenMathN12Recipient.lean),
[N12Curvature](../../../Kobon/UpperOpenMathN12Curvature.lean),
[ClosedN12Curvature](../../../Kobon/UpperOpenMathClosedN12Curvature.lean).

If every component has `B_s+1≤3E_s+3P_s+N12_s`, its signed cost is at
least one, so `δ≥U+c`. This sufficient profile condition is explicit and
is not known to hold for all arrangements. Proof:
[PositiveProfileComponents](../../../Kobon/UpperOpenMathPositiveProfileComponents.lean).

The actual `(1,3)` recipient with a positive antipodal source degree
also cannot be an injective affine maximum on a finite closed shared-core
set. The complete geometry and actual extraction are proved in
[N13ActualSupportExtreme](../../../Kobon/UpperOpenMathN13ActualSupportExtreme.lean).
Recovering a strict component term for all other zero-margin profiles
is still open.

The final local budget proves `m(p)+degreeFrom(A0,p)≤d(p)` by disjoint
actual incident inventories. It additionally pays one unit for each
marked `(2,2)` core, giving the global strengthening

`2δ+B15≥2U+3E3+3P21+N12+M22`.

Here `M22` counts `(a,d)=(2,2),m≥1`. The local gap is `2m−x`, at least
one under the new slot bound. Proofs:
[LocalPortBudget](../../../Kobon/UpperOpenMathLocalPortBudget.lean),
[M22GainWeights](../../../Kobon/UpperOpenMathM22GainWeights.lean),
[M22Curvature](../../../Kobon/UpperOpenMathM22Curvature.lean).
The existing component portfolio remains independently verified; a closed
component `M22` refinement was not added in this run.

A kernel-checked seven-vertex finite graph satisfies all displayed numerical
charging hypotheses and meets equality at coefficient one half on `A0`.
It defeats a smaller coefficient for that relaxation. Its two antipodal
sources would, however, have the same four core neighbours. Actual strict
antipodal pairings uniquely determine their centre, so two distinct actual
sources cannot do this. The finite graph is therefore **not** a Kobon
arrangement and proves no geometric sharpness claim.

Proofs: [HalfChargingObstruction](../../../Kobon/UpperOpenMathHalfChargingObstruction.lean),
[AntipodalCenterUniqueness](../../../Kobon/UpperOpenMathAntipodalCenterUniqueness.lean),
[AntipodalSameNeighbors](../../../Kobon/UpperOpenMathAntipodalSameNeighbors.lean).

## Next mathematical obligations

1. Exploit the newly **completed** stronger source-incidence theorem: two
   distinct antipodal sources share at most two actual core neighbours.
   The actual extraction and strict cevian crossing obstruction have both
   passed with the standard logical axioms. Other cores may have arbitrary
   multiplicity. This is a geometric prohibition of a complete bipartite
   subgraph with two sources and three targets, beyond the displayed
   finite charging relaxation. Its integration into a stronger general
   penalty remains a research target. Proof:
   [AntipodalThreeNeighbors](../../../Kobon/UpperOpenMathAntipodalThreeNeighbors.lean).
2. Exploit the **completed** bound one at `(1,3)` and bound two at every
   nonfull recipient of degree `a+d≤4`, including `(0,4)`, to recover a
   strict positive component escape term. The one-unit rule is proved;
   strict component positivity is a separate obligation. Proof of the
   broader bound two:
   [NonfullAntipodalRecipients](../../../Kobon/UpperOpenMathNonfullAntipodalRecipients.lean).
3. Pay `B15` through cap continuation and ordinary-end parity, while
   preserving the port budget. Exact rational examples already permit
   `A0–B15` adjacency; assuming independence is invalid.
4. Extend the sharper resources to higher multiplicities, with explicit
   surplus and ray losses. The mixed-multiplicity component inequality
   remains proved separately; the all-triple half coefficient must not
   silently be applied to mixed arrangements.

These are geometric obligations. A bounded negative coordinate search or
a feasible numerical charging graph cannot settle them on its own.
