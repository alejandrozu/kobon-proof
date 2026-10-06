# Upper-bound research: verified geometric and component progress

This file records the upper-bound branch of the 5–6 October 2026 research
session. The inequalities below are theorems about actual real line
arrangements and finite injective families of certified triangular cells.
Their local fans, side matching, degrees, and graph components are extracted
in Lean. They do **not** assume an unproved geometric extraction or an
externally supplied edge/component count.

All named final theorems passed Lean 4.31.0 with only `propext`,
`Classical.choice`, and `Quot.sound`. The full repository integration and
replay are managed by the main session. No unrestricted new numerical bound
for every Kobon arrangement is claimed here.

## Notation and scope

The arrangement has `n >= 2` pairwise nonparallel real lines. `T` is the
number of distinct selected certified triangular cells. A core is an actual
intersection of at least three indexed lines; its multiplicity is `r`.

* `q`: number of cores.
* `D1`: shared elementary sides with one ordinary endpoint and one core.
* `D2`: shared elementary sides with two core endpoints.
* `d1(p), d2(p)`: corresponding actual endpoint degrees.
* `U`: bounded elementary sides unused by the selected triangle family.
* `S = sum_core r(r-2)` and `I = sum_core r`.
* `delta = n(n-2)-3T`: the exact Tamura defect.
* `c`: number of connected components of the actual shared-core graph,
  **including isolated core vertices**. The graph's edges are the actual
  `D2` sides.
* `C`: number of core endpoints on bounded nonshared elementary sides.
  This includes endpoints on singly used and unused sides.
* `Rc`: unbounded rays at cores, defined by first/last core flags in the
  actual ordered vertex list of each line.

The independent exact resource identities are

```
D1 + 2D2 + C + Rc = 2I,
2 delta = 2 sum_core r(r-3) + 2U + C + Rc - D1.
```

See [RayResources](../../../Kobon/UpperOpenMathRayResources.lean).

## Strongest late-session all-triple formula

The completed final charging theorem removes the antipodal-source and
double-recipient corrections entirely:

```
2*delta + B15 >= 2*U + 3*(E3 + P21) + N12.
```

Here `B15` counts full triple cores with `d1=1,d2=5`; `E3` counts triple
cores with `d1=3`; `P21` counts partial triple cores with `d1=2,d2=1`;
`N12` counts triple cores with `d1=1,d2=2`.
Every actual core is assumed triple. There is no graph-degree restriction,
component-size restriction, source-count restriction, supplied fan,
assumed edge budget, or residual recipient hypothesis in this final result.

Equivalently,

```
3*T <= n*(n-2) - U - ceil((3*(E3+P21)+N12-B15)/2).
```

The geometric last step proves that a one-cap degree-three core cannot
receive two antipodal full two-cap sources. Its five triangular sectors
normalize to a four-shared-ray run. Adjacent chosen source tips would
contradict source independence; the remaining six positions are excluded
by actual support-line, ordinary-tip, and opposite-ray continuation
arguments. The complete chart and supporting triangle occurrences are
extracted from the original arrangement in Lean.

The final positive `N12` contribution follows from one more actual
recipient exclusion. A one-cap degree-two triple core has a four-sector
run with three shared rays. Two antipodal-source tips would have to be the
two nonadjacent core rays, with the ordinary tip between them. The verified
ordinary-middle continuation obstruction excludes this configuration.
Such a core receives at most one antipodal source; its local weight two
therefore retains at least one unit of surplus.

A partial `(2,1)` source also cannot receive an antipodal source: its
only shared core side reaches a poor neighbor, while an antipodal source
has ordinary degree two. This raises its coefficient from two to three
in the unit charging rule, and from five to six in the earlier doubled
half rule. The independently completed doubled refinement is

```
4*delta + 2*A24 + 2*B15 >= 4*U + 6*(E3+P21).
```

The final unit theorem implies this doubled theorem because `A24>=0`.
The strongest completed all-triple component portfolio simplifies exactly
to

```
j_s = max(1 - A_s - ceil(B_s/2),
          ceil((3*E_s + 3*P_s + N12_s - B_s)/2)),
delta >= U + sum_components j_s.
```

`A_s` counts unmarked full `(2,4)` cores inside the component. It remains
only in the alternative strictly positive component estimate; the new
unit estimate has no antipodal-source correction. Lean proves this
portfolio dominates both the preceding half-gain portfolio and the
source-free portfolio before the `N12` contribution. The formula is
valid for every line count `n>=2` in the stated all-triple class; it is a
structural upper estimate, not a claimed unrestricted numerical solution
of the Kobon problem.

A completed sufficient condition restores one strict unit per component:
if every actual component satisfies
`B_s+1 <= 3*E_s+3*P_s+N12_s`, then `delta>=U+c`. This condition is an
explicit inequality between actual local fan counts. It is not asserted
for all arrangements; the theorem allows arbitrarily large components
and arbitrary shared-core degrees in the all-triple class.
See [PositiveProfileComponents](../../../Kobon/UpperOpenMathPositiveProfileComponents.lean).

Final roots: `UpperOpenMathN12Curvature.certificate_n12_source_free_defect_bound`,
`UpperOpenMathClosedN12Curvature.certificate_closed_n12_source_free_gain`,
`certificate_n12_source_free_hybrid_component_defect`, and
`source_free_n12_dominates`. The earlier source-free score simplification
is retained in `UpperOpenMathN13Degree.unrestricted_score_simplifies`.
Sources: [N13ActualNoDouble](../../../Kobon/UpperOpenMathN13ActualNoDouble.lean),
[N13Curvature](../../../Kobon/UpperOpenMathN13Curvature.lean),
[N13Degree](../../../Kobon/UpperOpenMathN13Degree.lean),
[N12Recipient](../../../Kobon/UpperOpenMathN12Recipient.lean),
[N12Curvature](../../../Kobon/UpperOpenMathN12Curvature.lean),
[ClosedN12Curvature](../../../Kobon/UpperOpenMathClosedN12Curvature.lean),
[PartialRecipients](../../../Kobon/UpperOpenMathPartialRecipients.lean),
[PartialCurvature](../../../Kobon/UpperOpenMathPartialCurvature.lean),
[PartialHalfCurvature](../../../Kobon/UpperOpenMathPartialHalfCurvature.lean),
[ClosedPartialCurvature](../../../Kobon/UpperOpenMathClosedPartialCurvature.lean).

## Strongest completed structural bounds

### Triple cores, including partial cap fans

Assume every actual core has multiplicity three. Let `e` count cores with
`d1=3`, and let `b` count cores with `d1=2,d2=1`. Then

```
D1 + 2e + b <= 2q,
delta >= U + q - D2 + 2e + b.
```

The first statement is stronger than the initial `D1 <= 2q`. The proof
derives a marked-edge transfer: an extremal or partial cap source has an
actual neighboring triple satisfying `d1<=1` and `d1+d2<=2`. The source
edges are double-counted against those actual target capacities.

Final roots:

* `UpperOpenMathTripleCapBudget.certificate_triple_cap_budget`
* `UpperOpenMathTripleCapBudget.certificate_triple_cap_defect`

Sources: [TripleCapBudget](../../../Kobon/UpperOpenMathTripleCapBudget.lean),
[MarkedPoverty](../../../Kobon/UpperOpenMathMarkedPoverty.lean).

### Mixed multiplicities without a graph-degree restriction

Define

```
A = sum_{r>=4} (r(r-4)+1),
B = {triple cores with d1<=1 and d1+d2<=2},
P = sum_{p in B} d2(p).
```

Then the completed weighted ordinary-cap budget and defect estimate are

```
3D1 + 3q + 3A + 2P <= 3S,
3 delta >= 3(U + q - D2 + A) + 2P.
```

In particular `delta >= U + q - D2 + A`. A higher core contributes
`r(r-4)+1`: one at order four, six at order five, and thirteen at order six.
Higher-order extremal fans are **not** assumed independent. Their quadratic
multiplicity surplus pays the triple sources instead.

Final roots are `certificate_mixed_weighted_budget`,
`certificate_mixed_weighted_defect`, and `certificate_mixed_core_defect`
in [MixedCapBudget](../../../Kobon/UpperOpenMathMixedCapBudget.lean).

### Shared-core degree at most three, arbitrary multiplicities

If every actual core has `d2<=3`, define
`Delta = sum_{r>=4} r(r-4)`. Then

```
delta >= U + c + Delta,
3T + U + c + Delta <= n(n-2).
```

This holds at every order `n>=2` and allows branching and cyclic components.
The proof first establishes nonnegative adjusted component cost. Equality
would leave either a closed set of extremal fans or a closed set of
balanced triple fans. A finite supporting half-plane excludes the first;
the verified three-fan cycle geometry excludes the second. Thus every
actual nonempty component pays one additional unit.

The penalty at a higher core is zero at order four, five at order five, and
twelve at order six. The earlier degree-two component result is retained
as a simpler proof and special case.

Final root:
`UpperOpenMathMixedDegreeThree.certificate_mixed_degree_three_component_bound`.
Sources: [MixedDegreeThree](../../../Kobon/UpperOpenMathMixedDegreeThree.lean),
[ClosedExtremal](../../../Kobon/UpperOpenMathClosedExtremal.lean),
[CoreComponents](../../../Kobon/UpperOpenMathCoreComponents.lean).

### Shared-core forests, arbitrary degrees and multiplicities

If the actual shared-core graph is acyclic, Lean derives `D2+c=q` using
the actual component graphs, the tree edge formula, and the extracted
component partition. Thus

```
delta >= U + c + A,
3 delta >= 3(U+c+A) + 2P.
```

For all-triple forests the separate cap theorem gives
`delta >= U+c+2e+b`. This includes branching trees of arbitrary size;
there is no maximum-degree-two assumption in the forest theorem.

Final roots:

* `certificate_forest_edge_component_count`
* `certificate_triple_forest_bound`
* `certificate_mixed_forest_bound`
* `certificate_mixed_forest_weighted_bound`

See [ForestBudget](../../../Kobon/UpperOpenMathForestBudget.lean).

## Actual equality geometry

The antipodal five-sector fan with `d1=2,d2=2` really exists. It must not be
excluded by claiming it has a marked ray. The proof instead normalizes
its two ordinary caps to rays 0 and 3 and its two core rays to 1 and 2.
Matching original triangle identities forces a closed balanced component
to contain a three-cycle. The third core's cap axis would then contain
an exterior point beyond both endpoints of the same core side, impossible.

The final statement `certificate_two_two_core_empty` and its closed-subset
version are actual arrangement theorems, not abstract fan interfaces.

Sources: [TwoCapCycle](../../../Kobon/UpperOpenMathTwoCapCycle.lean),
[TripleCharts](../../../Kobon/UpperOpenMathTripleCharts.lean),
[TwoTwoCore](../../../Kobon/UpperOpenMathTwoTwoCore.lean).

## All-line parity and the remaining global gap

For even all-triple arrangements, every cut line has an odd number of
ordinary crossings. The common-side lemma supplies actual bounded
transverse segments there. Positive triangle bases touching those crossings
form a pair partition unless a transverse segment has degree different
from one or a base also ends at a core.

The two outcomes have been counted separately. For `n>=4` the safe actual
budget is

```
n <= 2U + 2D1 + C.
```

The second `D1` is necessary in this accounting: a shared core-ordinary
side can pay once as a transverse charge and once as a base. A four-line
pencil-plus-cap exact witness has `U=0,D1=1,C=2,Rc=3`; dropping that factor
would give the false inequality `4<=3`.

Sources: [OrdinaryBaseCover](../../../Kobon/UpperOpenMathOrdinaryBaseCover.lean),
[OrdinaryLineCharge](../../../Kobon/UpperOpenMathOrdinaryLineCharge.lean),
[OrdinaryGlobalCharge](../../../Kobon/UpperOpenMathOrdinaryGlobalCharge.lean).

The conjectural stronger token rule
`n <= 2U + D1 + Rc + 2`, together with `C>=2D1`, would imply the corrected
even bound `6T <= n(2n-5)+2` for all-triple arrangements. Neither global
token rule is being assumed in the verified results above.

## Marked ports and unrestricted triple curvature

For each actual triple core, a marked port is a shared core ray whose two
neighboring shared rays end at ordinary crossings. The marker is extracted
from the canonical radial chart of the original triangle certificates.
An actual shared edge can receive at most one such source marker. Its
other endpoint is a poor triple fan, with `d1<=1` and `d1+d2<=2`.
For every actual shared-core-closed subset `P`, this gives

```
sum(P, markedCount) <= sum(poor(P), d2).
```

The weighted consequence now holds without any maximum-degree hypothesis.
Let `A24` count full fans with `d1=2,d2=4` and no marked port, and let `B15`
count full fans with `d1=1,d2=5`. Then every all-triple arrangement satisfies

```
delta + 2*A24 + B15 >= U + c.
```

The same inequality has a local component form: every nonempty actual
shared-core-closed subset has `componentCost+unpaidWeight>=1`.
The zero case is excluded geometrically. Tight payment forces only four
fan types: `(2,2,m0)`, `(2,4,m1)`, `(0,2,m0)`, and `(0,6,m0)`.
The marked full two-cap fans and the full zero-cap fans form a finite
cluster. Each full zero-cap fan surrounds its center with cluster
neighbors. Each marked two-cap fan has an actual antipodal bridge through
a poor fan and a cluster neighbor in the opposite direction. A point of
maximum squared norm cannot satisfy either condition. If that cluster is
empty, the remaining normalized two-cap fans contradict the actual
three-cycle obstruction. All these alternatives are extracted from the
original cells and actual shared sides.

Thus marked non-antipodal `(2,4)` fans incur no negative correction. Full
antipodal `(2,4)` fans exist, and `(1,5)` fans may be adjacent, so the
remaining terms are retained explicitly.

Sources: [MarkedPorts](../../../Kobon/UpperOpenMathMarkedPorts.lean),
[MarkedZeroGeometry](../../../Kobon/UpperOpenMathMarkedZeroGeometry.lean),
[MarkedZeroEscape](../../../Kobon/UpperOpenMathMarkedZeroEscape.lean),
[MarkedCurvatureBound](../../../Kobon/UpperOpenMathMarkedCurvatureBound.lean).

One correction was strengthened by proving that the entire paid
curvature is strictly positive on every nonempty component, even when its
exception count is positive. If `B_s` is the number of full `(1,5)` fans
in component `s`, this verified triple statement is

```
delta + A24 + sum_components ceil(B_s/2) >= U + c.
```

Here `A24` still counts only unmarked full `(2,4)` fans. There is no degree,
component-order, or independence hypothesis. The strict local inequality
is `2*componentCost+2*A24_component+B_s>=1`; integer rounding gives the
displayed correction.

At zero paid curvature, unmarked full `(2,4)` and full `(1,5)` fans join
the earlier four-type classification. Balanced `(2,2,m0)` fans cannot
touch a full fan when all their neighbors are balanced or full. Tight
payment excludes poor neighbors, so their subset is closed and the actual
two-cap cycle argument removes it. Every remaining unmarked full fan
surrounds its center within the full-fan cluster; marked full two-cap fans
have the antipodal bridge already verified. The same finite maximum-norm
argument excludes the entire zero paid case. Thus the negative corrections
have coefficient one for unmarked `(2,4)` fans and one per pair of `(1,5)`
fans inside a component.

Sources: [FullTripleChart](../../../Kobon/UpperOpenMathFullTripleChart.lean),
[PaidZeroTypes](../../../Kobon/UpperOpenMathPaidZeroTypes.lean),
[PaidZeroEscape](../../../Kobon/UpperOpenMathPaidZeroEscape.lean),
[PaidZeroRigidity](../../../Kobon/UpperOpenMathPaidZeroRigidity.lean),
[PaidCurvatureBound](../../../Kobon/UpperOpenMathPaidCurvatureBound.lean).

The companion mixed-multiplicity theorem also removes every degree
hypothesis. Define `Delta=sum_{r>=4} r(r-4)`, and let `Aall` count all
full `(2,4)` triple fans. For every actual arrangement,

```
delta + Aall + sum_components ceil(B_s/2) >= U + c + Delta.
2*delta + 2*Aall + B15 >= 2*U + c + 2*Delta.
```

The second expression uses the global one-cap count and avoids component
rounding. Higher cores are paid by their actual multiplicity surplus and
the extracted extremal-triple incidence capacity. A putative zero-paid
higher/extremal cluster is closed and entirely full, which contradicts a
finite supporting line. The remaining balanced/full triple mixture is
excluded by the source-preserving neighbor charts. The all-triple marked
theorem improves `Aall` to the unmarked subset `A24`.

Sources: [MixedCurvature](../../../Kobon/UpperOpenMathMixedCurvature.lean),
[MixedCurvatureBound](../../../Kobon/UpperOpenMathMixedCurvatureBound.lean).

## Unrestricted half-curvature with positive cap contributions

The sharper actual all-triple charging theorem is

```
2*delta + A24 + B15 >= 2*U.
4*delta + 2*A24 + 2*B15 >= 4*U + 6*E3 + 5*P21.
```

`E3` counts ordinary-degree-three triple cores; `P21` counts partial
ordinary-degree-two/core-degree-one triple cores. All counts and hypotheses
are extracted from actual line arrangements. No degree bound, component
size bound, independently charged fan, or aggregate resource assumption
remains in these final theorems.

The geometric improvements are crucial. An antipodal full two-cap source
has at least two nonfull core neighbors. It cannot touch a balanced
unmarked `(2,2)` core. A one-cap `(1,3)` core cannot have three such
antipodal sources among its neighbors; this is proved without a marker
assumption. Unmarked cross edges reserve poor endpoint slots, reducing the
capacity available to marked ports. These facts allow a half coefficient
on each residual full-fan type, retaining positive three-cap and partial
two-cap weights.

The same argument is localized to every actual closed component. For its
local counts define

```
h_s = max(1 - A_s - ceil(B_s/2),
          ceil((6*E_s + 5*P_s - 2*A_s - 2*B_s)/4)).
delta >= U + sum_components h_s.
```

The max combines the strictly positive paid-component theorem with the
half-curvature gain. Its gain version formally dominates the earlier
component hybrid that omitted `E_s` and `P_s`. Rounding and choosing the
stronger estimate happen separately inside each actual component.

Sources: [UnmarkedCrossResources](../../../Kobon/UpperOpenMathUnmarkedCrossResources.lean),
[AntipodalConeIncidence](../../../Kobon/UpperOpenMathAntipodalConeIncidence.lean),
[AntipodalBalancedAdjacency](../../../Kobon/UpperOpenMathAntipodalBalancedAdjacency.lean),
[OneCapThreeCore](../../../Kobon/UpperOpenMathOneCapThreeCore.lean),
[OneCapThreeCoreDegree](../../../Kobon/UpperOpenMathOneCapThreeCoreDegree.lean),
[HalfCurvatureGain](../../../Kobon/UpperOpenMathHalfCurvatureGain.lean),
[ClosedHalfCurvature](../../../Kobon/UpperOpenMathClosedHalfCurvature.lean).

Two distinct antipodal source centers also have at most two actual common
core neighbors, even when other cores have higher multiplicities. This
actual geometric no-`K2,3` resource is available for future component and
source-density refinements. It is stronger than the earlier same-four-
neighbors uniqueness statement.

### A component with at most one antipodal source

The source correction can be removed whenever an actual closed component
contains at most one unmarked full `(2,4)` source. The verified inequality is

```
2*H_s + B_s >= 3*E_s + 2*P_s,
g_s = ceil((3*E_s + 2*P_s - B_s)/2),
H_s >= g_s.
```

Here `H_s` is the exact component contribution to `delta-U`. A receiver
has at most one incident edge from the single source, so its finite
charging capacity is stronger. This source restriction is computed from
the arrangement; no side-count hypothesis is supplied externally.

Combining this result with the preceding estimate gives the unrestricted
adaptive all-triple theorem

```
j_s = max(h_s, g_s)  if A_s <= 1,
j_s = h_s           if A_s >= 2,
delta >= U + sum_components j_s.
```

Lean also verifies `h_s <= j_s`: the new formula never weakens the previous
component formula. Its single-source branch is available at arbitrarily
large component orders, not just for a fixed list of small values of `n`.

Every closed core component of order at most seven automatically has at
most one antipodal source. Two such sources cannot share an edge; each
requires four neighbors among the other at most five vertices. Their
neighbor sets would then overlap in at least three vertices, contradicting
the actual no-`K2,3` theorem. Thus if every component has at most seven cores,

```
delta >= U + sum_components ceil((3*E_s + 2*P_s - B_s)/2).
```

The adaptive max remains valid and can be stronger than this last simpler
formula. These are structural upper bounds for arrangements at every line
count; they do not assert a new unrestricted numerical value of `K(n)`.

Final roots: `certificate_closed_single_source_gain`,
`certificate_seven_core_single_source`,
`certificate_adaptive_component_defect`, and
`certificate_seven_component_defect`.
Sources: [SingleSourceCurvature](../../../Kobon/UpperOpenMathSingleSourceCurvature.lean),
[SingleSourceComponents](../../../Kobon/UpperOpenMathSingleSourceComponents.lean),
[AntipodalThreeNeighbors](../../../Kobon/UpperOpenMathAntipodalThreeNeighbors.lean).

### Correction localized to double receivers

A further completed all-triple theorem replaces the total antipodal source
count by a specific recipient count. Let `J13` count cores with
`d1=1,d2=3` incident with exactly two unmarked full `(2,4)` sources. Then

```
2*delta + B15 + J13 >= 2*U + 3*E3 + 2*P21.
```

All nonfull triple recipients can meet at most two antipodal sources. If
three were selected, two source tips would be adjacent across an actual
triangular cap; its shared cap side would violate the verified
antipodal-source independence theorem. The only remaining unit-payment
shortfall is the one-cap degree-three double receiver recorded by `J13`.

This bound is localized in
`certificate_closed_double_recipient_gain`. The unrestricted component
portfolio can take the maximum of `h_s` and
`ceil((3*E_s+2*P_s-B_s-J_s)/2)` independently in each component. A component
with at most one source has `J_s=0`, consistently recovering the stronger
single-source formula above. This intermediate result retains `J13`.
The final late-session theorem above subsequently proves `J13=0`,
strengthens the partial-cap coefficient, and adds the positive `N12`
contribution.

Sources: [NonfullAntipodalRecipients](../../../Kobon/UpperOpenMathNonfullAntipodalRecipients.lean),
[DoubleRecipientCurvature](../../../Kobon/UpperOpenMathDoubleRecipientCurvature.lean),
[ClosedDoubleRecipientCurvature](../../../Kobon/UpperOpenMathClosedDoubleRecipientCurvature.lean).

Source: [AntipodalThreeNeighbors](../../../Kobon/UpperOpenMathAntipodalThreeNeighbors.lean).

## Components with at most five cores

The correction can be removed entirely when every actual shared-core
component contains at most five vertices, with arbitrary intersection
multiplicities. There may be arbitrarily many components and lines.

```
delta >= U + c + Delta.
```

This includes total `q<=5` as a special case. It extends the degree-three
class by handling the remaining possible degree-four vertex. In the
all-triple case `Delta=0`, recovering the earlier five-core statement.
Exact Tamura equality in this component class forces the whole arrangement
to be simple. That is an independent verified sufficient-scope proof of
the previously asserted broad simplicity conclusion, with a quantitative
surplus retained at higher cores.

An unmarked full `(2,4)` fan normalizes to ordinary rays `{0,3}` and core
rays `{1,2,4,5}`. The center and those four distinct neighbors exhaust a
closed subset of order at most five. The center blocks the opposite outer
edges `1--4` and `2--5`; the ordinary cap vertices block `1--5` and
`2--4`. Every outer vertex therefore has shared-core degree at most two.
Each positive outer curvature weight is at least two, since a partial
`(2,1)` outer fan would force its ordinary-degree-two center to be poor.
Neither adjacent outer pair can have both weights zero: two normalized
two-cap fans cannot meet a full third fan in that shared core triangle.
The two pairs pay at least four units, exceeding the center's negative
weight two. This proof uses actual segment parameters and original
triangle occurrences, not an abstract graph drawing assumption.

For mixed outer multiplicities the same proof uses adjusted weights. A
higher outer core of degree at most two contributes at least six. A
non-antipodal full two-cap center normalizes instead to ordinary rays
`{0,2}` and core rays `{1,3,4,5}`. Three actual blocked diagonals force
core ray `1` to have degree at most one and every other outer core degree
at most three. The first endpoint contributes at least three; the others
are nonnegative, so they pay the center's negative weight two. Both full
two-cap shapes are therefore removed from the correction in the mixed
five-core component theorem.

Sources: [AntipodalTwoCapChart](../../../Kobon/UpperOpenMathAntipodalTwoCapChart.lean),
[AntipodalStarDegree](../../../Kobon/UpperOpenMathAntipodalStarDegree.lean),
[AntipodalStarWeights](../../../Kobon/UpperOpenMathAntipodalStarWeights.lean),
[FiveCoreComponents](../../../Kobon/UpperOpenMathFiveCoreComponents.lean),
[NonAntipodalTwoCapChart](../../../Kobon/UpperOpenMathNonAntipodalTwoCapChart.lean),
[NonAntipodalStarDegree](../../../Kobon/UpperOpenMathNonAntipodalStarDegree.lean),
[MixedAntipodalStar](../../../Kobon/UpperOpenMathMixedAntipodalStar.lean),
[MixedFiveCoreComponents](../../../Kobon/UpperOpenMathMixedFiveCoreComponents.lean).

## Attribution and limits

The wrong-ray/shared-apex mechanism is related to Raj Srirangam's
[ALL8_NOTE7, section 4](https://github.com/srirangam-r/kobon_triangles/blob/eed14659a9b2f4ca12777da5d557f2b620b966f6/proofs/all8/ALL8_NOTE7.md).
The broader partial-fan interfaces, actual extraction, and weighted global
budgets above are the verified development in this session. The local
opposite-side kite lemma formalizes the mechanism in
[ALL8_NOTE2, section 3](https://github.com/srirangam-r/kobon_triangles/blob/eed14659a9b2f4ca12777da5d557f2b620b966f6/proofs/all8/ALL8_NOTE2.md).

[Clément–Bader 2007](https://oeis.org/A006066/a006066.pdf) already states
that exact Tamura equality forces a simple configuration. The present
degree-restricted equality conclusion is therefore an independently
checked sufficient-scope proof, not a claim of first discovery of that
broad conclusion. The quantitative component and mixed-multiplicity
penalties are the central new statements to compare in a future priority
review.

No proof of an unrestricted corrected even upper bound, no new individual
optimal Kobon value, and no solution of the whole open problem is claimed
by this upper branch.

## Rejected routes and retained evidence

* `D<=2q` is false even with no parallel lines and only triples: the exact
  phase-zero cubic arrangement at `n=18` has `q=46,D1=15,D2=105`.
* Extremal higher-order fans are not independent: an exact eleven-line
  witness has adjacent order-five full fans with `d1=7,d2=3` at both ends.
* A five-sector `d1=2,d2=2` triple fan need not have a marked ray; the
  antipodal counterexample is explicitly retained.
* An unmarked full `(2,4)` fan can have a marked full `(2,4)` neighbor:
  an exact eight-line witness has seven triple cores and twelve triangles.
  Thus full two-cap fans cannot be declared mutually independent.
* A residual unmarked full `(2,4)` fan can also share a side with a full
  `(1,5)` fan. The exact nine-line witness has eight triple cores and
  sixteen triangles. The residual negative types are not independent.
* `n<=2U+D1+Rc` fails at the exact 38-line/450-triangle witness with four
  triple cores: `U=14,D1=8,Rc=0` gives 36, below 38.
* Adding a universal correction two to that first-token rule does not
  extend to mixed multiplicities: a 14-line/52-triangle witness with one
  quadruple and three triples has token shortfall three.
* The exact corpus screens supporting `C>=2D1` and the triple-only
  corrected first token are evidence, not Lean proofs of those rules.

The corpus branch retains the rational lines, exact triangle lists, and
profile ledgers. These numerical negative examples are research evidence;
they are distinguished from the named Lean theorems above.

## Next proof obligations

1. Reconcile the two D1 charge modes globally using cap continuation,
   ordinary three-fans, and kites, retaining the explicit boundary rays.
2. Prove or refute `C>=2D1` in the all-triple class, concentrating on mutual
   blocks rather than random pencil mixtures.
3. Reduce the remaining corrections for unmarked full `(d1,d2)=(2,4)` and
   full `(1,5)` fans. Marked `(2,4)` fans have now been paid in the verified
   unrestricted component theorem; the residual types cannot be discarded
   by an unjustified independence assumption.
4. Convert any surviving global token trade-off into a corrected even
   bound and audit every multiplicity assumption before applying a
   projective parallel-elimination chart.
5. Audit priority against the primary literature before using “new” for a
   numerical consequence already asserted elsewhere.
