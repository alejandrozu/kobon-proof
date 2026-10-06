# Construction branch: uniform seeds and dyadic generalization

Author: Alejandro Zarzuelo Urdiales, with computational assistance.
Session: 5–6 October 2026. This is a live research record; the parent release
report records the final compiled status and hashes.

## Strongest new construction found so far

Rohith Poola's competition repository supplies an exact 61-line arrangement
with 1190 triangular cells. Its original fixed slopes lose eight cells when
the two central tangent-grid intercepts are moved arbitrarily close to zero.
A point count therefore did not supply the uniform geometric premise used
by our existing BBL recursion.

We independently fit reciprocal slopes while preserving the complete affine
orientation type, including the original line at infinity, at the limiting
central intercept value epsilon = 0. A positive floating LP margin was used
only to propose a rational vector. The rationalized vector was then checked
on the entire actual tangent-grid box

    0 < epsilon <= 1/100000000,
    x-intercepts = -tan(29*pi/60), ..., -tan(pi/60),
                   -epsilon, epsilon,
                    tan(pi/60), ..., tan(29*pi/60).

The exact Fraction checker verified 35,990 nonconcurrence boxes and 72,590
triangle/support sign boxes, retaining all 1190 cells and all 59 elementary
triangles incident to y = 0. The actual 29 tangent enclosures are separately
proved by `Kobon/BBLTangent60Bounds.lean`; their outward-rounding to 20 decimal
places is discharged in the seed's analytic parameter-box proof.

The central apex has height `(20000000000/9239253)*epsilon > 0`. The complete
exterior-direction scan finds 28 visible pairs, including the rightmost
boundary pair, for normal `(1, -20025598529/10000000000)`.

The seed, all real geometric bridges and both infinite families have now compiled
successfully. The existing fully proved BBL iteration gives, with q = 60*2^t and t >= 0,

    odd:  n = q+1, T = 1200*4^t - 10,
    even: n = q+2, T = 1200*4^t + 30*2^t - 12.

These are actual simple real straight-line constructions. Their gaps from
the respective classical simple-arrangement upper floors are exactly 9 and
11 for every depth. The allowable positive epsilon interval may shrink with
depth; a single fixed positive epsilon valid at all depths is not claimed.

The gains over the established total construction
`G(n) = floor(n(n-3)/3) + 1 + (n mod 2)` for n >= 4 are

    odd:  q/3 - 11 = 20*2^t - 11,
    even: q/6 - 12 = 10*2^t - 12  (nonnegative from t >= 1).

Thus the odd gains are 9, 29, 69, 149, ... at 61, 121, 241, 481, ... .
The even gains from t = 1 are 8, 28, 68, ... at 122, 242, 482, ... .
The initial even witness 62:1218 is weaker than G(62)=1220 and must be
retained only as the compatible recursion base, not as the best all-order
value at 62.

Numerical priority for the 61:1190 point construction belongs to Poola.
The BBL geometric operation and quadratic recurrence remain attributed to
Bartholdi, Blanc and Loisel. A primary-source check of the main BBL,
Forge–Ramirez Alfonsin, Parpalak–Utkin and Savchuk papers found no q=60 dyadic
straight-line family. This suggests a distinct orbit, but it is a bounded
priority review, not proof of absolute novelty. The potential new contribution
is the explicit compatible uniform seed and its actual infinite realization.

## Formal completion of the earlier optimal family

The previously archived 33-line tangent-grid draft supplies the classical
Forge–Ramirez Alfonsin family when its finite and analytic checks are actually
completed. New modules with prefix `OpenMathConstructionSeed33` preserve the
same coordinates and original check statements, using the optimized finite
reflection engine. The target formulas are

    q = 32*2^t,
    odd  = (1024*4^t - 1)/3 at q+1,
    even = (1024*4^t - 1)/3 + 16*2^t at q+2.

These attain the established odd and even simple-arrangement upper floors.
The numerical family is classical; completing its actual Lean recursion is
a formal scope advance, not a new numerical record.

## Verification infrastructure

`OpenMathConstructionBoolean.lean` proves ordinary kernel soundness from
explicit Boolean decisions to the original DirectionCheck, SimpleCheck,
TriangleCheck, VisibleCheck and AdmissibleCheck predicates. Native evaluation
is submitted only a closed Boolean equality to true, and remains explicitly
inside the native compiler/runtime trust boundary.

The original `ParametricCached.cache` is extensionally correct but its native
compiled arity includes the coordinate argument. Its Array.ofFn could
therefore be rebuilt for every coordinate read. A local array in a Bool-valued
loop fixes that problem. The same issue affects literal coefficient and
bound vectors. `OpenMathConstructionBooleanMemo.lean` materializes all line
coefficient arrays and both bound arrays once before a finite check. Its
extensional equalities and soundness were proved with standard axioms.
The 33-line full simplicity check then completed in 4.46 seconds, versus
stopping a preceding version after approximately eleven CPU minutes.

No change to the mathematical predicate, parameter interval or geometric
premises is justified by a performance optimization. All final finite checks
must be rerun against their released source and dependency hashes.

## Completed bounded screens that were stopped

* Generic random deletion of a dense family does not improve G at the previous
  order: for the q+1 BBL family, the averaged deletion guarantee gives exactly
  G(q). Multi-line random thinning has leading n^3/(3N), below G away from N.
* 120 sampled projective direction charts of the phase-shifted FP arrangement
  at each of 16 even orders from 12 through 90 did not improve its existing
  affine count. This is a finite exploratory screen, not a nonimprovability
  theorem for all charts or arrangements.
* Eight central-slope power scalings at four exact epsilon samples each were
  weaker than the fixed-slope 1182 small-epsilon witness. Only that prescribed
  32-case family was tested. The successful full reciprocal-slope refit replaces
  that direction; no general blow-up obstruction is asserted.
* All normal-direction sectors of the contestant 61:1189 affine type also have
  at most 28 visible pairs. Its best combined count is dominated by the
  1190/28 seed. The 1187 type cannot improve 1218 even with all 30 exterior
  pairs, so it was not prioritized.

## Reproducible files

* `experiments/2026-10-05/constructions/contestant_limit_fit.py`: LP proposals
  for the limiting prescribed grid; positive margins are diagnostic until exact
  verification.
* `experiments/2026-10-05/constructions/refit61_uniform_box.py`: exact whole-box
  finite checks, independent of the LP and Lean tactics.
* `experiments/2026-10-05/constructions/refit61_visibility.py`: exact interval
  visibility and complete positive-normal direction-sector scan.
* `contestant61-refitted-uniform-box.json`: successful rational data, complete
  triangle/cap lists, bounds, visibility and source provenance.
* `contestant-limit-fits/report.json`: all eight finite LP cases, their actual
  margins and statuses.
* `central61-blowup-screen.json` and `phase-shifted-chart-screen.json`: bounded
  negative discovery diagnostics, with the scope described above.
* `generate_seed33_reflection.py` and `generate_seed61_lean.py`: source exporters.
  The final replay uses the released sources, not an uncompiled exporter output.

Source repository for the competition point witnesses:
https://github.com/Rohith18p/rsi-kobon-triangles,
pinned commit `f462d8e18aea2a458376c523c9b6c2980237071f`.

## Next mathematical directions

The parent research branch is searching nearby limit-grid orientation cells
while retaining all 59 axis caps. A stronger compatible seed at 61 improves
every odd dyadic level by the same amount; improved T+V may separately improve
every even level. Distinct primitive q values can supply additional constant-gap
orbits, provided actual true-tangent uniform compatibility is proved. Finite
positive-epsilon counts and floating LP infeasibility are insufficient.
## Final construction checkpoint

`OpenMathConstructionFamily61.lean` is fully compiled. The actual odd family
uses five audited finite native decisions; the even family adds only the
admissibility and visibility decisions. The positive-rescaling input bridge,
analytic tangent60 bounds, geometric normalization and all boundary-sector
lemmas use standard kernel axioms only. There are no admitted placeholders.
Native decisions are compiler-assisted exact finite checks, not additional
mathematical assumptions about an extension or a triangle count.

`construction-proof-provenance.json` lists the precise active successful
modules, source hashes, finite native roots and unpromoted draft status.
`family61-envelope-comparison.json` compares against the actual previous
RecursiveEnvelope plus both33/49 branches. It confirms gains9/29/69/149 at
61/121/241/481, and8/28/68 at122/242/482. At62 the prior1220 remains stronger
than the family1218. These are gains over our prior certified envelope, not
claims of worldwide priority for the isolated finite counts.

The exact input exporter `generate_seed61_lean.py` writes a review directory
by default; `--write` updates only the two immutable input modules and requires
replaying all dependent proofs. Proof modules remain self-contained sources.
The final active source lines are exact positive inverse rescalings of static
integer coefficients, and their boxes are common-denominator grids. This avoids
repeating a large rational array-comparison computation while preserving the
same affine lines. Historical rational rows remain in the data module.

The three old dense integer61 probes were moved to `drafts/` after their
computations were stopped. They are excluded from the active formal target.
The retired sparse rational prototype is likewise explicitly unpromoted.

## Linear cap feasibility and nonlocal chamber searches

`Kobon/OpenMathAxisCapCone.lean` is fully compiled with standard axioms only.
For fixed strictly increasing axis intercepts `a_i`, write each other line as
`x-u_i*y=a_i`. Fix the above/below orientation of each consecutive axis cap.
The cap constraints are linear inequalities in the reciprocal slopes `u_i`:
for each consecutive pair `(j,j+1)` and other index `r`, the wall is

`(a_(j+1)-a_r)u_j+(a_r-a_j)u_(j+1)+(a_j-a_(j+1))u_r`.

`capRegion_iff` proves that these inequalities are equivalent to the actual
empty nondegenerate caps under the declared strict orientation pattern.
`capRegion_convex` proves that convex interpolation preserves the whole cap
region. It does not assert that all other lines remain in general position
along an interpolation: crossing nonaxis concurrence/parallel facets is
precisely what the discovery search uses. This is a formal search framework,
not a newly claimed numerical triangle bound or a worldwide priority claim.

Two complementary reduced-row LP walks use only the adjacent crossing-order
constraints (initially1219 independent walls instead of35990), validate every
realized row order and count, and preserve all59 axis caps. The deeper walk
allows temporary counts down to1185; the heap walk prioritizes high-count
chambers down to1187. Their reports are the `facet-reduced-*` directories.

`capcone_ray_search61.py` uses the larger convex cap cone directly. It moves
all60 reciprocal slopes simultaneously along random feasible rays, processes
all concurrence and parallel events incrementally, and independently recounts
every selected chamber. It explores more than one million facet crossings in
a few minutes. Floating proposals are never promoted without exact actual
true-tangent whole-interval validation and a fresh Lean certificate. Ongoing
bounded search coverage is recorded under `capcone-ray-seed61013/`; a maximum
observed count is not a global ceiling.

## Deletion and visibility transport diagnostics

`bbl61_incidence_audit.py` exactly enumerates the known BBL mixed/replacement
triangle certificate through depths0--6. A retained nonaxis line gains exactly
`q` certified triangles in a step from`q+1` to`2q+1`; each newly introduced
nonaxis line has incidence`2q-1` after cap replacement. The minimum incidence
of this witness list is always`q-7`, inherited from source line59. Its deletion
gives`q^2/3-q-3`, four below`G(q)`, so this specific route was stopped. The
machine-readable counts are in `bbl61-incidence-transport-audit.json`.

`bbl61_visibility_audit.py` independently constructs exact rational finite
arrangements using100-digit tangent proposals, explicitly scoped as numerical
diagnostics rather than an additional true-tangent uniform proof. At orders
61/121/241 it recounts1190/4790/19190 triangles,52/112/232 double terminals,
and maximum visibility28/58/118 across every normal sector. These maxima
match the already proved transported count`q/2-2`, so changing the finite
normal direction did not uncover an extra successor triangle. The data are
in `bbl61-visibility-transport-audit.json`.

## Stronger Pareto61 checkpoint

`OpenMathConstructionParetoFamily61.lean` is fully compiled, together with all
11 independent Pareto61 input, finite-check and actual geometric seed modules.
The new compatible seed keeps1190 triangles and59 axis caps while increasing
the fixed admissible visible resource from28 to29. It was discovered by a
nonlocal cap-cone ray mutation with the objective`T+V`, followed by reflection
and shear to restore the canonical positive right slope and boundary.

For`q=60*2^t`, the strongest completed odd/even constructions now give

* `n=q+1`: `1200*4^t-10`, nine below the simple odd upper floor;
* `n=q+2`: `1200*4^t+30*2^t-11`, ten below the simple even upper floor.

The even formula improves the previous61 even family by one at every depth.
At62 its1219 remains below the retained baseline1220. At122/242/482 it raises
our prior certified maxima4848/19308/77028 to4849/19309/77029. These comparisons
are in `family61-pareto-envelope-comparison.json`. They describe our retained
formal envelope, without asserting global finite numerical priority.

The new exact input is `contestant61-pareto-sparse-uniform-box.json`, checked
independently over all`0<epsilon<=1/100000000`, with normal
`(1,-8000441397/4000000000)` and apex height
`(20000000000/8777037)*epsilon`. Sparse exact rational verification takes
about24seconds for35990 simplicity tests,72590 triangle/support tests, and
all29 visible pairs. The separate original dense checker independently passed
the same whole triangle/cap box. Every Lean finite check was freshly replayed;
no old61 native certificate was reused for the modified geometry.

The full even-family audit has exactly seven compiler-assisted finite Boolean
roots (directions, sorted list, cap membership, simplicity, triangle boxes,
admissibility, visibility). Rescaling, actual tangent bounds, normalization,
boundary transport and infinite iteration use only standard axioms. The final
clean log is `pareto61-family-build-2.log`; there are no admitted placeholders.
The original1190/28 seed and its proof remain available for comparison.

The source exporter `generate_pareto61_lean.py` writes a review directory by
default and updates only independent immutable input modules with`--write`.
The proof modules are maintained separately. Continuing searches optimize
both odd counts and the combined odd/even resource; a higher floating count
is still only a proposal until its whole interval and Lean replay pass.

## Completed37 orbit and all-natural-order formula

`OpenMathConstructionFamily37.lean` is fully compiled. The independent
37:431 refit preserves35 axis caps on the entire actual tangent36 interval
`0<epsilon<=1/100000000`. All17 actual angle enclosures are proved in
`BBLTangent36Bounds.lean` with ordinary kernel rational checks. The affine
input count is credited to Rohith Poola; the numerical orbit is the known
Parpalak--Utkin/Blanc q18 family, with this proof starting at its q36 tail.
No new numerical-priority claim is made for that orbit.

For`q=36*2^t`, the formal counts are`432*4^t-1` at`q+1` and
`432*4^t-1+18*2^t` at`q+2`. Both attain the respective simple-arrangement
upper floors. The even proof uses the newly verified universal deficit-two
successor and inherits the same five finite native roots as the odd source;
it has no extra direction/visibility certificate. At38 its449 remains below
the retained unrestricted witness450. Relative to our earlier formal
portfolio,73/74 improve1705/1752 to1727/1763 and145/146 improve6865/6960 to
6911/6983. These improvements are formal coverage of a known numerical orbit.

`OpenMathConstructionEnvelope.all_n` proves an actual lower witness for every
natural order. Its finite maximum retains the complete RecursiveEnvelope and
selects matching33/49/37/61 dyadic constructors. `previous_le` is pointwise;
`retains_old_even_family_plus_one` includes the stronger61 even branch;
`quadratic_lower` proves`n^2<=3*(bound(n)+n)` for every natural n. That quality
estimate inherits the prior all-order construction and does not claim a new
leading asymptotic constant. No arbitrary full-gain successor rule is used.

The explicit all-order procedure is a portfolio of known and new verified
constructions. Its maxima are legitimate even where unrestricted finite
witnesses exceed the simple-model upper floor; such upper-floor statements
are never asserted for the unrestricted problem.

## Parametric screens and dual obstruction

The41/45 alternative affine-chart runs tested37/42 and24/46 charts,
1477 and1059 unique sign cells, without a positive fixed-slope proposal.
First-order and second-order parametric-jet screens tested eight source axes
per order, with no robust positive margin. Those failures remain bounded
numerical diagnostics rather than exact infeasibility theorems.

A separate sparse Farkas witness with11 positive rational weights was exact
Fraction verified for the exported41-line axis0/original-infinity normalized
cell. It excludes the required weighted budget for every epsilon up to
approximately0.01401555, even if the slope vector depends on epsilon. The
actual tangent intervals were independently checked using exact rational
arctangent-quarter inequalities and the proved20-digit pi band. This is a
metric obstruction for one specified cell, not a global Kobon upper bound or
an exclusion of all41-line types.

`OpenMathParametricDual.no_budget` proves the general coefficient-box and
small-epsilon dual separation theorem with standard axioms only. The concrete
41 data remain clearly labelled pending concrete Lean replay in
`parametric-farkas-cell41.json`; they are not an active formal result.

`bounded-search-summary.json` collects the completed ray/LP search coverage.
Crossed facets may repeat, and rejected floating discrepancies are recorded.
The successful Pareto1190/29 certificate is the promoted outcome; millions of
additional explored facets do not constitute a global1190 ceiling. To resume,
prioritize different compatible types or exact parametric deformations rather
than repeating these already screened fixed-type charts.
