# Local geometry and extracted upper-bound budgets — 2 October 2026

This note records the upper-bound branch of the three-hour research session.
It deliberately distinguishes actual geometric theorems from conditional
aggregate arithmetic and from the remaining cyclic-fan extraction gap.

## Stronger local fan theorem

At a point incident to `r >= 3` arrangement lines, write `d1` for the number
of shared radial sides whose other endpoint is ordinary, and `d2` for those
whose other endpoint is a multiple point. The cyclic data consist of actual
real triangles, actual supporting arrangement lines and antipodal radial
directions (`Kobon/UpperFan.lean`, `UpperFan.Sectors`).

The earlier formal estimate was `d1 <= 2r - 3`. We now prove:

1. If `d1 >= 2r - 3`, every sector is triangular and `d2 = 3`.
2. Consequently `d1 <= 2r - 4` whenever `d2 != 3`; in particular this holds
   for `d2 <= 2`, strengthening the previously discussed `d2 <= 1` case.
3. With `e = 1` exactly when `d1 = 2r - 3`,
   `3d1 + d2 <= 6r - 8 + 2e`.

The proof finds four omitted rays whenever two neighboring rays are omitted.
A nontriangular sector omits its two bounding shared rays. The established
geometric prohibition of a run of `r-1` ordinary rays supplies the two further
omissions. Thus the extremal case must be a full fan, and exactly three of its
`2r` shared rays have nonordinary endpoints.

## Real shared-edge classification

`Kobon/UpperSharedEdge.lean` proves that two real triangles with disjoint
interiors and a common side cannot have two ordinary endpoints of that side,
under the explicit no-parallel-lines condition. At an ordinary endpoint the
two non-edge supports must coincide. Ordinary endpoints at both ends would
therefore force the two triangles' third vertices to coincide, contradicting
disjoint nonempty interiors. A separate lemma extracts a third incident line
at a nonordinary endpoint already incident to two distinct lines.

This closes a local geometric bridge. It does not enumerate all elementary
edges of an arbitrary arrangement.

## Elementary sides and capacity two

`Kobon/UpperElementaryEdges.lean` proves that all three sides of every real
triangle satisfying the certificate predicate are elementary arrangement
segments: only the supporting line can meet a side's relative interior.
Consequently no intermediate arrangement vertex occurs there. This follows
directly from the certificate's weak-side tests, without a new assumption.

`Kobon/UpperEdgeCapacity.lean` proves geometrically that at most two triangles
with pairwise disjoint interiors can share the same side. Two triangles on
the same side of their common base overlap near its midpoint, as shown by an
explicit positive barycentric perturbation. This supplies the geometric
capacity bound required by finite edge-incidence double counting.

`Kobon/UpperTriangleIncidence.lean` constructs unordered real sides and counts
their actual occurrence fibers. Each triangle contributes three distinct
sides and the geometric fiber capacity is at most two. This gives the exact
identity `3T = |used sides| + |shared sides|`. Its direct certificate corollary
derives pairwise disjointness from `TrianglePredicate`, rather than assuming it.

`Kobon/UpperSharedIncidence.lean` extracts two distinct triangles from each
shared-side fiber, aligns their endpoints while preserving indexed supports,
and applies the actual shared-edge classification. Every shared side has a
nonordinary endpoint. The shared sides are partitioned into `D1` (one ordinary
and one nonordinary endpoint) and `D2` (both endpoints nonordinary). This
derives `3T + U = |E| + D1 + D2` for any finite edge universe `E` containing the
triangle sides. The identity's geometric capacity and shared-endpoint premises
are now proved; its edge universe is still explicit at this level.

## Intersection multiplicities

`Kobon/UpperVertexBudget.lean` defines the actual vertices as the image of all
ordered pairs of distinct indexed lines under intersection. The fiber at a
point of multiplicity `r` is the off-diagonal square of its incident-line set,
so finite fiber counting gives `sum r(r-1) = n(n-1)`. Point-line incidence
counting then proves `sum_i (v_i-1) = n(n-2)-sum r(r-2)`, where `v_i` is the
number of distinct actual intersection vertices on line `i`. The sum includes
ordinary points, whose loss contribution `r(r-2)` is zero.

`Kobon/UpperEdgeInventory.lean` now constructs the actual consecutive-segment
inventory. A nonconstant affine coordinate orders the vertices of each line;
the resulting consecutive unordered endpoint pairs are injectively indexed,
and inventories of distinct supporting lines are disjoint. Each certified
triangle side occurs in this inventory, because an intermediate ordered vertex
would contradict the proved elementary-side property. The inventory therefore
has exactly `n(n-2)-sum r(r-2)` segments, and all certified triangle sides are
included without an extra hypothesis.

`UpperEdgeInventory.certificate_defect_identity` combines these constructions
to derive, in Lean, the full identity

```
n(n-2) - 3T = S + U - D1 - D2.
```

`Kobon/UpperCoreExtraction.lean` proves that `OrdinaryAt` is equivalent to an
incident-line set of cardinality two. Its `defect_identity` sums `S` only over
the actual finite multiple-point core. `certificate_oneCore_classification`
proves explicitly that each D1 side is an unordered pair consisting of one
ordinary point and one actual core point. Its final `simple_arrangement_upper`
recovers the classical inequality `3T <= n(n-2)` for arrangements with an
empty core, as a complete geometric check of this extraction pipeline.

Scope: these identities concern `n >= 2` pairwise nonparallel real lines and
any finite injective family of triangles satisfying `TrianglePredicate`.
The family may be a subset of all triangular cells: `U`, `D1` and `D2` are
then defined relative to that chosen family. All identities remain exact.
There is no parallel-line reduction or newly defined maximum-K theorem.

## Extracted core-to-core line budget

`Kobon/UpperCoreLineIncidence.lean` derives `D2 + h <= I` from the actual core
and actual core-to-core shared segments. On each supporting line, the selected
core-to-core intervals form part of a finite path. Their number plus one is
at most the number of selected core vertices when that set is nonempty.
Summation gives the inequality, without assuming a core-edge budget.

`Kobon/UpperCoreCombinatorics.lean` proves that every actual core-to-core
shared side is a two-element subset of the actual core. Thus
`D2 <= choose(q,2)`, and in particular `D2 <= 3` when `q <= 3`.
It also sums the pointwise multiplicity inequality over the actual core to
derive `2S - 7I + 15q >= 0`. These are extracted geometric/counting facts,
not additional assumptions of the conditional three-core calculation below.

## A maximum principle at exposed core points

`Kobon/UpperFanSupport.lean` adds positive orientation of consecutive radial
sectors, the orientation possessed by a counterclockwise cyclic extraction.
For a full fan, its nonordinary outer endpoints meet both open sides of every
valid line through the center. In the extremal case these are exactly the
three core-ended shared endpoints. In ordinary geometric language, the center
lies strictly inside the triangle of those three endpoints; the formal theorem
states the equivalent supporting-half-plane obstruction, without relying on a
separate convex-hull interpretation theorem.

Proof: adjacent opposite supports coincide at an ordinary outer endpoint, so
the three consecutive outer endpoints are collinear. An affine functional's
minimum propagates through each ordinary endpoint. If all nonordinary
endpoints were nonnegative and some endpoint negative, its minimum would
propagate around the fan and contradict antipodality. Thus all endpoints are
nonnegative; antipodality makes them all zero, contradicting a nondegenerate
sector and a valid supporting line.

`Kobon/UpperCoreBoundary.lean` is the bridge to a finite collection of local
fans: an explicit endpoint-to-core map and an actual supporting line for a
core point imply `d1 <= 2r - 4` at that point. Summing over a chosen supported
set `B` yields `D1 <= 2I - 3q - |B|`. The finite collection itself is an explicit
interface, not silently asserted to have been extracted from all arrangements.

## Extremal triple cores cannot be adjacent

`Kobon/UpperTripleFan.lean` proves a further local obstruction. For a triple
point, the three ordinary shared rays in an extremal fan alternate around
the six rays. Two such extremal fans cannot be matched across a shared edge
with its two incident triangular cells. The formal interface explicitly
identifies the common endpoints and the two neighboring outer endpoints.

Proof: at each ordinary neighbor, the two opposite supports coincide. Two
antipodal endpoints are consequently incident to the same two distinct
supporting lines, so are equal. Antipodality and the opposite sides of the
common edge force those equal points to lie on opposite sides, a contradiction.

Once global matching is extracted, extremal triple cores therefore form an
independent set of the elementary shared-core graph. If that graph is simple
and planar, the bipartite subgraph of the `e` extremal triple cores and their
neighbors has `3e` edges, so the usual planar bipartite inequality gives
`3e <= 2q - 4` (for `q >= 3`). That planar graph consequence is presently an
ordinary mathematical deduction, not a Lean theorem in this branch.

## Conditional aggregate consequences

Write `S = sum r(r-2)`, `I = sum r`, `q = number of multiple points`, `U` for
unused elementary edges, `D1` for ordinary-to-core shared edges, `D2` for
core-to-core shared edges, `h` for lines meeting a core point, and
`delta = n(n-2) - 3T`. The following former geometric premises are now
fully extracted and Lean-proved in the nonparallel certificate setting:

```
delta = S + U - D1 - D2,
h <= I - D2.
D2 <= choose(q,2).
2S - 7I + 15q >= 0.
```

For even order at least four, the clean-line charging inequality
`n-h <= 2U+D1` is now fully
extracted in `UpperCleanCharging.certificate_clean_line_budget`. A shorter
perfect-matching proof and its formally verified geometric ingredients are recorded in
[`CLEAN_LINE_MATCHING.md`](CLEAN_LINE_MATCHING.md): one common half-plane has
an actual bounded consecutive segment on every transverse line, that segment
is unique, an ordinary crossing forces triangles to pair crossings on the
clean line, and the actual crossing set has odd cardinality.
`UpperCleanCover` extracts the actual degree-one-to-pair-cover map and then
the unused-or-D1 charge. `UpperCleanCharging` injects clean lines into actual
edge/ordinary-endpoint pairs and proves their capacities two and one.
Extraction of cyclic fan data at every core and their matching/summation
against the global shared sides are also still open.

The new weighted local inequality, when summed with
`sum d2 = 2D2`, gives `3D1 + 2D2 <= 6I - 8q + 2e`, where `e` counts extremal
fans. `Kobon/UpperCoreBudget.lean` checks the resulting aggregate implication

```
2delta >= n + 2S - 7I + 8q - 2e + D2.
```

For at most three multiple points, the new `d2 <= 2` local theorem would apply
everywhere once distinct elementary core endpoints are extracted. With
`D2 <= 3` and the elementary multiplicity surplus
`2S - 7I + 15q >= 0`, the checked arithmetic gives, for `n=2m`,

```
delta >= m - 6,
T <= floor(m(4m-5)/3) + 2.
```

This extends the analogous conditional at-most-two-core calculation, whose
additive term was one. No claim of an unrestricted global Kobon upper bound,
or priority over the literature for this restricted ordinary mathematical
consequence, is made here.

## What is still needed

The main unresolved Lean tasks are now extracting consistent positively
oriented cyclic fan data and their endpoint/matching counts at every actual
core. Global elementary
segment enumeration, geometric side capacity, intersection multiplicities,
the defect identity, the core-to-core line budget, the simple core-edge count
and the multiplicity surplus have been extracted. So have the actual
clean-line pair cover, local charge and global even-order charging budget.
The conditional numerical upper consequences still retain their unproved
fan-extraction and fan-summation hypotheses; the gap has narrowed, not vanished.

Further mathematical directions: count supported/nonextremal cores using the
planar graph of elementary core-to-core shared edges; exploit the fact that
each extremal core has exactly three such neighbors surrounding it; prove
constraints stronger than planarity alone. A planar graph argument by itself
has not yielded a new unrestricted upper bound in this branch.

## Novelty and attribution limits

The incidence identity, multiplicity count, path count and classical simple
upper bound are standard mathematics newly formalized in this repository;
they should not be presented as new numerical Kobon records. The local
`d2 != 3` refinement strengthens our earlier stated `d2 <= 1` case. The
supporting-half-plane obstruction and incompatible extremal triple-fan theorem
are additional structural results produced in this session. Their mathematical
priority beyond the existing literature has not been established by this
branch. A separate literature audit is needed before claiming first discovery.

## Verification record

All 20 modules maintained by this branch passed individual compilation with
standard axioms only. The separate `UpperSimpleOptimality` module maintained
by the hybrid-family branch is integrated in the repository-wide verifier.
The frozen-source batch record below is the authoritative final verification
record for their current hashes.

Run `research/three-hour-2026-10-02/upper/verify_upper.ps1` from any directory.
It compiles all 20 modules sequentially with the repository's pinned `lake`
environment, records source SHA256 hashes and compiler exit codes, and checks
that the printed principal theorem roots use only `propext`,
`Classical.choice` and `Quot.sound`. It additionally rejects placeholder,
custom-axiom and unsafe source markers. Per-file logs and `summary.json` are
written under `upper/verification/`. The final session record consists of
the frozen first 18 modules in `summary.json` and the final two additions in
`summary-supplement.json`, produced with the optional `OnlyModules` argument;
the earlier sources were unchanged when the two additions were checked.
Read their `passed` fields rather than
inferring success from the existence of a source file.

During this session the optional `CompilerRunner` parameter pointed to the
ignored local scheduler `work/lean_light.ps1` so that all agents shared one
small compiler slot beside the heavy certificate build.
The alternate `.elan` binary on this machine reports the same version but
does not load the existing dependency cache correctly. No dependencies were
modified for this work. The working executable is the existing pinned
`lean-env` installation. The reusable verification script does not depend on
that machine-specific location; it uses the normal `lake` on `PATH`.
