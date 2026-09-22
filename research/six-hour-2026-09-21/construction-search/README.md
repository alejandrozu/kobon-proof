# Projective charts of the Füredi–Palásti construction

This branch investigates projective geometry and convex-hull exposure as a new
search neighborhood. A projective transformation changes all lines together;
it can turn a previously unbounded projective triangular face into a bounded
affine triangle. This differs from the previous insertion and one-line
replacement searches.

The underlying trigonometric arrangement is classical Füredi–Palásti. These
notes record our derivation and its exact finite checks. They do not establish
priority. A consequence of an old construction can already be implicit in
earlier work even if it is absent from an OEIS table.

## Finite results

`experiments/2026-09-21/construction-search/exposed_caps.py` constructs these
simple rational arrangements. It independently checks the final integer
coordinates by adjacency and by open-interior sign tests.

| Lines | Previous saved count | New count | Method |
|---:|---:|---:|---|
| 39 | 469 | 470 | Two exposed vertices |
| 47 | 690 | 691 | One exposed vertex |
| 48 | 720 | 721 | One-sixth phase |
| 51 | 817 | 818 | Two exposed vertices |
| 53 | 884 | 885 | One exposed vertex |
| 54 | 918 | 919 | One-sixth phase |
| 55 | 954 | 955 | One exposed vertex |
| 59 | 1102 | 1103 | One exposed vertex |
| 60 | 1140 | 1141 | One-sixth phase |
| 99 | 3169 | 3170 | Two exposed vertices |
| 195 | 12481 | 12482 | Two exposed vertices |

The original projective experiment found 47:691 after 11,264 proposals. Every
one of the 691 projective triangular faces of that particular arrangement was
bounded in the new chart. The later exposed-vertex description eliminates the
search and provides a direct construction.

Each compact certificate uses integer line coefficients obtained by rounding
a proposal, followed by an exact test that reproduces the entire triangle
list and verifies simplicity. Approximation is not trusted for the final
finite inequality. The final verification report records the accepted scale.

## General construction and proof ingredients

Set `a = π/n`, `c = cos a`, and

\[
\theta_i=(i+1/2)\pi/n,\qquad
\ell_i:\ \sin\theta_i x+\cos\theta_i y=\sin(3\theta_i).
\]

For parameters `u,v`, the intersection has x-coordinate

\[
X(u,v)=\cos(2u)+\cos(2v)+\cos(2u+2v)
      =2zw+2z^2-1,
\quad z=\cos(u+v),\quad w=\cos(u-v).
\]

The unique rightmost vertex is the intersection of lines `0,n−1`, at
`R=1+2c`. Every other vertex has strictly smaller x-coordinate. A line
`x=h` sufficiently close to `R` from the left separates this vertex from
every other vertex. Taking this line as the line at infinity preserves every
old bounded triangular face and bounds the additional face on lines
`0,(n−1)/2,n−1` when n is odd. The cosine-coordinate exposure argument and
the projective realization are separate proof obligations from counting.

For `n=3m≥6`, the two leftmost vertices are exactly the intersections
`(m−1,m)` and `(2m−1,2m)`, both with x-coordinate `−R/2`. Every other
vertex has strictly greater x-coordinate. Here is a direct proof of the
strict part, without an asymptotic estimate.

* If the cyclic distance of the two line indices is at least two,
  `|w|≤cos(2a)=2c²−1`. Completing the square gives

  \[
  X+R/2=2(z+w/2)^2+c-1/2-w^2/2
  \ge(1-c)(2c^3+2c^2-1)>0.
  \]

  The last inequality holds for `n≥6`, since `3/4≤c<1`.

* For adjacent indices, `w=c`, and `z=cos(2ka)` for an integer k. The
  discrete grid, with `3|n`, gives either `z≤−1/2` or `z>1/2−c`.
  Consequently

  \[
  X+R/2=(2z+1)(z+c-1/2)\ge0,
  \]

  with equality only at `k=m,2m`. To check the gap outside the central
  cosine interval, use

  \[
  \cos(2\pi/3-2a)-(1/2-c)
  =c(1-c+2\sin(2\pi/3)\sin a)>0.
  \]

* The remaining cyclically adjacent pair `0,n−1` is the rightmost vertex.

Thus a line `x=h` just to the right of `−R/2` separates the two leftmost
vertices from all remaining vertices. When n is odd, taking this as the
line at infinity preserves the old triangles and bounds two further faces:

\[
((m-1)/2,2m-1,2m),\qquad(m-1,m,(5m-1)/2).
\]

Together with the one-sixth-phase count for even n, the consolidated
formula is

\[
F(n)=\left\lfloor\frac{n(n-3)}3\right\rfloor+1+\mathbf1_{n\text{ odd}}
\quad(n\ge4),
\]

with the usual small-order exceptions handled separately. The two-cap branch
is fully formalized, including existence of the new affine chart, preservation
of the old selected triangles, both new empty triangles, simplicity, and the
count. The theorem
`Kobon.FurediPalastiTwoCaps.two_cap_simple_lower_bound` proves
`SimpleLowerBound (6*k+3) (FurediPalasti.lower (6*k+3)+2)` for every `k≥1`.
`lake build Kobon.FurediPalastiTwoCaps` passed. Its complete dependency audit
uses only `propext`, `Classical.choice`, and `Quot.sound`; it has no native
evaluation dependency or unfinished geometric hypothesis. The root review
records the separate assembly of the parity branches into a total formula.

## Negative and diagnostic results

The exact projective face census for the 81:2132 and 161:8532 hybrid witnesses
equals the number of their already bounded triangles. Changing affine chart
alone cannot improve those particular configurations.

A complete sampled-boundary pass on the saved 39:469 arrangement examined
1,078,980 numerical proposals and found no improvement. The successful
39:470 arrangement instead uses the classical half-phase topology. On the
48-line one-sixth-phase construction, 2,542,512 proposals found no chart
better than 721. These proposal searches use floating ranking, so they are
not exhaustive optimality certificates.

The phase `1/6` does not combine with the same rightmost-vertex flip: every
odd order from 5 through 59 lost the triangle `(0,1,n−1)` and gained none.
This invalidates that tempting shortcut to the two-cap argument.

The cusp-grid scan covered every n from 5 through 80, separately at phases
`1/2` and `1/6`. It found no improvement at even n. It found the one-cap
gain at every tested odd order not divisible by three, and the two-cap gain
at every tested odd multiple of three in the half-phase arrangement.

Charts of two 44-line elliptic-curve seeds improved their affine counts from
589/590 to 593, but each has only 603 projective triangular faces, already
below the saved 608. The 48-line seeds similarly remained below the phase
construction. Exact output coordinates and bounded-search logs are preserved
as negative evidence; they are not new lower-bound records.

The better two-component elliptic seeds also did not improve the affine
baseline. Their projective/initial/final triangle counts were respectively
550/538/539 at n=42, 724/710/712 at n=48, 922/907/908 at n=54, and
1144/1127/1129 at n=60. The n=42 and n=48 scans traversed every proposed
pair boundary; n=54 and n=60 had 90-second limits. Numerical candidate
ranking remains a heuristic in all four runs.

An exact rational QF_LRA calculation for the half-phase 9-line arrangement
found that no affine chart retains all 21 of its projective triangular
cells. A reduced contradictory set of face constraints is recorded in
`chart-smt-009.json`. This is a solver result, not a Lean-verified theorem,
and it concerns this fixed projective arrangement only. The known optimum
K(9)=21 therefore cannot be used to infer that this particular projective
arrangement has an optimal affine chart.

The faster `chart_retention.py` solver branches on contradictory sets of
face-retention constraints. It also found no chart gaining a triangle for
the rational half-phase arrangements at n=14,20,26,44, nor a chart retaining
all 471 projective triangles of the new 39:470 certificate. For the
nonuniform cubic 48-line seed with 724 projective triangles, it ruled out
722 bounded triangles after 2,903 exact linear-arithmetic checks; the
existing affine 721 is therefore chart-optimal for that seed according to
the solver. These statements remain solver diagnostics rather than Lean
upper bounds, and do not concern other projective arrangements.

The complete deletion audit starts from the saved optimal 41-line witness.
Every one-line deletion has 494 affine triangles. Of its 41 resulting
projective arrangements, 37 have only 494 projective triangles; the four
remaining arrangements have 495 or 496. Exact SMT checks ruled out an
affine chart with 495 in all four cases. Thus deleting one line from this
particular witness and changing its affine chart cannot improve 494,
subject to the stated solver trust. `deletion41-chart-audit.json` records
every deletion, the source hash, and the supporting per-case reports.

The first fixed-normal LP mutation experiment at n=39 accepted 500
realizable, exact-checked triangle-wall flips in 97.9 seconds. Its best
affine count remained 470. Later experiments alternate blocks of all line
offsets and all normal coefficients, and include mutations at currently
unbounded projective triangular cells. These bounded searches retain all
accepted steps, their margins, seeds, and final coordinate witnesses; no
failed run establishes an impossibility result.

The first mixed offset/normal 47-line run accepted 473 exact-checked
mutations in 904.9 seconds. The best count remained 691. Its complete
trajectory and final 684-triangle state are retained for reproducibility.
The projective-cell version accepted 731 mutations at n=39 in 1,201.5
seconds and 688 at n=40 in 1,801.5 seconds, with several restarts. Their
best affine/projective counts remained 470/471 and 494/496 respectively.
The 48-line cubic seed retained 721 affine and 724 projective triangles
after 471 accepted mutations in 1,802.7 seconds, including four restarts.
The complete report is `projective-cubic-048.json.report.json`. This
experiment changes the arrangement itself; it is distinct from the fixed
seed's exact chart obstruction.

A separate beam search explores paths of up to ten projective triangle
mutations before requesting straight-line realization. At n=39, 33 seeded
rounds visited 4,559 beam nodes and evaluated 2,122,270 candidate edges in
900.1 seconds. No combinatorial candidate exceeded 470 affine or 471
projective triangles, so no LP promotion was attempted. The search had
beam width20 and allowed an intermediate loss of three triangles. These
limits are recorded in `beam-039.json.report.json`; the result is not an
exhaustive obstruction or a global upper bound.

## Reproduction

Run the scripts from the repository root. `mpmath` is needed only to propose
coordinates, and NumPy only for numerical chart ranking. The finite verifiers
use Python's exact integer and rational arithmetic. The scripts use the
repository's established exact geometry modules and preserve source and
construction metadata. All stochastic chart scans save their seed and
stopping rule.

The main files are:

* `chart_optimize.py`: random-order chart-boundary proposals and exact checks.
* `cusp_chart_family.py`: the initial deltoid cusp-grid exploration.
* `exposed_caps.py`: the direct construction and compact final certificates.
* `exposed-cap-certificates/verification.json`: agreement of final counters.
* `chamber_mutation.py`: mixed LP realization of adjacent orientation chambers.
* `projective_mutation.py`: mutations including unbounded projective triangles.
* `beam_mutation.py`: bounded paths of several combinatorial mutations, with
  LP realization and independent exact checks required for promotion.
* `chart_smt.py`: exact logical tests of retaining every projective triangle.
* `chart_retention.py`: exact chart-retention tests with a permitted loss.
* `deletion_chart_audit.py`: all deletions of the saved optimal 41-line witness.
* `Kobon/FurediPalastiCaps.lean`: all-order convex-hull exposure and a separating chart.
* `Kobon/FurediPalastiTwoCaps.lean`: the complete infinite two-cap family theorem.

The next research question is whether changes to the arrangement itself,
rather than a change of affine chart, can improve this constant correction
or produce a larger general correction term.

## Formal support for the hybrid construction

The search work also supplies independently compiled components for
the separate BBL hybrid formalization. `Kobon.BBLCount.mixed_count` proves
that the explicit integer crossing model at q=4r has at least q² mixed
triples. Each auxiliary pair has two adjacent old crossings, except at
most q explicitly parameterized exterior pairs, which each have one.
The identity 2*binomial(q+1,2)-q=q² gives the count.

`Kobon.BBLRowGeometry.mixed_witness` converts a monotone realization of
those crossing rows by actual real lines into a nodup list of at least q²
genuine empty triangles. `Kobon.BBLCaps.cap_side` proves that the explicit
cap row in every old gap has no intervening crossing along its cap side.
`Kobon.BBLCapSigns.cap_key_signs` identifies the signs at each cap row's
horizontal reference point. `Kobon.BBLCapEnvelope.cap_left_endpoint` and
`cap_right_endpoint` convert these integer comparisons into actual signs
of every other added line at both cap vertices: nonnegative for an even
old gap, nonpositive for an odd gap. `Kobon.BBLCapHeight.cap_endpoint_height`
proves the same sign for the distinguished horizontal line itself.
`Kobon.BBLCentralEnvelope.central_endpoint` treats the two unchanged
horizontal vertices of the central gap. Thus the cap geometry is reduced
to the realized crossing order and continuity at the old apex and old
supporting lines, rather than a separate search for an uncut second side.

`Kobon.BBLLiftedKeys` proves that moving the negative complementary
crossing's integer key beyond the last reference cut preserves every
old/new and new/new comparison within its row. This corrects the global
analytic reference-cut interpretation without changing any counted
triangle or cap row. `Kobon.BBLLiftedRows` gives the complete label-wise
comparison equivalence and row-key injectivity.

`Kobon.BBLConsecutive.supports_consecutive` proves that an old triangle
using Y0 has consecutive supports in the ordered intercept list. Thus the
explicit cap rows account for every old Y0 triangle in an arbitrary
witness list. `Kobon.BBLRowMax.max_pair_visible` turns simultaneous row
maxima into actual visible wedges, using simplicity to make the projected
crossing comparisons strict.

`Kobon.BBLAssembly.doubling_bound` assembles the final finite witness from
actual predicates for every mapped old triangle and the realized crossing
order. It proves map injectivity and separation from the mixed list, giving
T+q² distinct triangles on 2q+1 lines. This theorem is a sound assembly
component: its geometric hypotheses must still be discharged by the
analytic and continuity modules before it establishes an infinite family.

`Kobon.BBLCapBridge` discharges the orientation convention and relabeling
needed by the continuity argument. Its `cap_replaced_eventually` theorem
is an actual triangle-persistence statement, conditional only on the
canonical endpoint signs already supplied by the row geometry.
`Kobon.BBLCentralPersistence.central_replaced_eventually` handles the
central triangle, which stays on Y0 rather than moving to an added cap.
`Kobon.BBLCapRetention.cap_retained_eventually` combines these cases for
every old Y0 triangle in the witness. All of these modules are compiled
with the standard logical axioms.

`Kobon.BBLVisible.new_visible_witness` constructs 2r+1 new visible wedges:
r negative complementary pairs, r−1 positive almost-complementary pairs,
the rightmost Y0/new pair, and the central maximizing new line with the
rightmost old line. The last pair uses the actual rightmost old-row maximum
proved in the analytic branch. `Kobon.BBLVisibleAssembly.visible_gain`
combines them with all old visible wedges except at most one involving
Y0. The proved gain is V_new ≥ V_old+2r, with q=4r.

The actual crossing-order realization is supplied by the sibling
`BBLRealization` and `BBLRealizedPencil` modules. Final one-step integration
belongs to `BBLDoubling`. The additional invariant and seed reindexing
needed for indefinite iteration are not proved by these branch modules.
