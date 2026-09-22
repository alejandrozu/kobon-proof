# A parity budget outside the multiple-point core

This is an independently derived structural refinement of Blanc's parity argument. It gives conditional upper bounds; it is **not** a universal improvement of the unrestricted Kobon upper bound, and priority for the restricted statement has not been established. The [ProofAtlas research summary](https://www.proofatlas.ai/collaboration/kobon-triangle-problem/) already reports a stronger restricted 14-line result covering up to four multiple points. The theorem below covers every even order, with at most two finite multiple points of arbitrary multiplicity and **no parallel pairs**.

## Definitions and identity

Let A consist of n distinct, pairwise nonparallel affine lines, n even and at least four. A triangle always means a bounded triangular face. Let t_r count finite points of multiplicity r, and

`S = sum_{r>=3} r(r-2)t_r`.

Let U count bounded elementary segments incident to no triangle, D1 count segments incident to two triangles with exactly one multiple endpoint, and D2 count those with two multiple endpoints. Let h be the number of lines containing a finite multiple point, and let

`delta = n(n-2)-3T`.

The exact incidence identity from [multiplicity-budget.md](multiplicity-budget.md) reads

`delta = S + U - D1 - D2`.

A segment incident to two triangles cannot have two ordinary endpoints. Otherwise both triangles would use the same three supporting lines, which define only one bounded triangular region. Thus D1+D2 accounts for every shared side.

## Clean-line parity lemma

Call a line clean if it contains no finite multiple point. Then

**`n-h <= 2U+D1`.**

Indeed, a clean line L has n-1 distinct ordinary crossings. The proof of [Blanc, Proposition 2.0.3](https://arxiv.org/html/0801.2845v2) can be applied locally with the following conclusion: at an ordinary point of L there is a bounded segment transverse to L which is unused or belongs to two triangles.

Here is the full local induction, including the endpoint step. Put L horizontally and label its n-1 crossings in increasing order. Let R_i be the transverse line at crossing i. Let l_i be the segment between crossings i and i+1, with l_0 and l_(n-1) the two exterior rays. Write p_i^+ and p_i^- for the upper and lower incident faces, and r_i^+, r_i^- for the upper and lower elementary segments of R_i incident to L. Each bounded l_i has ordinary endpoints, so cannot be shared. Assume for contradiction that every bounded r_i^+ and r_i^- belongs to exactly one triangle.

If both p_1^+ and p_1^- fail to be triangles, then both r_1^+ and r_1^- are unused, because their other neighboring faces touch the exterior ray l_0. At least one of these transverse segments is bounded: R_1 meets another transverse line. This is a contradiction. Reflecting vertically if necessary, we may therefore assume p_1^+ is triangular, and hence p_1^- is not.

For 1<=i<=n-2 we prove two assertions together. If i is even then p_i^+ is not triangular; if i is odd then p_i^- is not triangular. Moreover, if both faces at l_(i-1) are not triangular, then p_i^- is triangular for even i and p_i^+ is triangular for odd i. The base i=1 holds because both faces at the exterior ray l_0 are unbounded and p_1^+ was chosen triangular.

Consider the step with i even; the odd case exchanges upper and lower. If p_(i-1)^+ is triangular, then p_i^+ cannot be triangular, since the two would share r_i^+; the additional implication is vacuous. Otherwise p_(i-1)^+ is not triangular, and the preceding odd step also says p_(i-1)^- is not triangular. This case cannot arise at i=2 because p_1^+ is triangular, so i>=4. The earlier even step says p_(i-2)^+ is not triangular. Thus r_(i-1)^+ is unused and, by the assumed absence of a chargeable bounded segment, is unbounded. Since R_(i-1) and R_i are not parallel, their intersection must lie below L: an intersection above L would make r_(i-1)^+ bounded. It follows that r_i^- is bounded. It is used by assumption, and its left neighboring face p_(i-1)^- is not triangular; therefore its right neighboring face p_i^- is triangular. The ordinary endpoints of l_i then imply p_i^+ is not triangular. This completes both assertions.

As n-2 is even, p_(n-2)^+ is not triangular. If p_(n-2)^- also fails to be triangular, both transverse segments at the last crossing are unused, and at least one is bounded, giving a contradiction. In the remaining case p_1^+ and p_(n-2)^- are triangular. Then r_1^- and r_(n-1)^+ are unused. The transverse lines R_1 and R_(n-1) intersect: if their intersection is below L, r_1^- is bounded; if it is above L, r_(n-1)^+ is bounded. Either possibility again contradicts the assumption. The claimed local alternative follows.

Only the transverse segments incident to L were assumed unshared in this contradiction, and the segments on L were unshared because their endpoints were ordinary. Other finite intersections need not be ordinary.

Charge each clean line to one such transverse segment. An unused segment has at most two ordinary endpoints, and each ordinary endpoint lies on only one transverse line. It can therefore receive at most two charges. A shared segment has at least one multiple endpoint, so it can receive at most one charge; segments counted by D2 receive none. There are n-h clean lines. Summing charges proves the lemma.

Combining it with the incidence identity yields

**`2 delta >= n+2S-h-3D1-2D2`.**

The no-parallel hypothesis matters in the endpoint step. An attempted extension that merely excluded parallel-participating lines from the clean set failed: three parallel vertical lines and one horizontal line leave the horizontal line clean in that sense, but all its transverse segments are unbounded. The argument does not establish the claimed local charge in that situation.

## A local fan lemma for triple points

At a finite triple point v, let d1(v) count incident shared segments with ordinary other endpoint and d2(v) count incident shared segments with multiple other endpoint. Then

`d1(v) <= 3`, and `d1(v)=3` implies `d2(v)>=3`.

Proof: there are six rays and six sectors around v. Two consecutive rays cannot both support segments counted by d1(v). If they did, the three triangular sectors bordering those two rays would have a common opposite supporting line: at each ordinary other endpoint, the two adjacent triangle sides are opposite portions of the same line. That opposite line would meet four consecutive rays from v. Four consecutive rays among three lines contain an opposite pair, which a line not through v cannot meet. This is impossible. Hence the selected rays form an independent set in a six-cycle, so at most three are selected. If three are selected, they alternate and the adjacent triangular sectors fill all six sectors. Each of the other three rays is consequently shared as well, and must be counted by d2(v).

If the arrangement has at most two finite multiple points, both triple, a point has at most one segment to the other multiple point. Therefore d2(v)<=1 and d1(v)<=2.

The following more general fan bound removes the restriction to triple points:

**At an r-fold point with d2(v)<=1, `d1(v)<=2r-4`.**

To prove it, inspect the cyclic list of 2r sectors and mark the triangular ones. A ray supports a shared segment exactly when both neighboring sectors are triangular. A consecutive run of rays counted by d1(v) has length at most r-2: otherwise the adjacent triangles have one common opposite line meeting r+1 consecutive rays, including an opposite pair. Such a line cannot exist.

If all 2r sectors were triangular, all rays would be shared. With at most one ray counted by d2(v), there would be a run of at least 2r-1 rays counted by d1(v), a contradiction. Thus a nontriangular sector exists. Suppose d1(v)>=2r-3. There cannot be two separated nontriangular sectors, because they would exclude at least four shared rays. There also cannot be three consecutive nontriangular sectors, for the same reason. If there is exactly one nontriangular sector, the shared rays form a path of length 2r-2. Removing at most one d2 ray leaves at most two d1 runs; these contain at least 2r-3 rays altogether, exceeding their total capacity 2(r-2). If there are exactly two adjacent nontriangular sectors, at most 2r-3 shared rays remain. To have d1>=2r-3, all those rays must be d1 rays, giving one run of length 2r-3>r-2. Every case is impossible, proving the bound.

## Conditional upper theorem

**For every even n>=4, a pairwise nonparallel arrangement with at most two finite multiple points, of any multiplicity, has**

**`T <= floor(n(n-5/2)/3)+1`.**

The cases of zero and one finite multiple point admit the stronger conclusions

* q=0: `delta >= n/2`;
* q=1: `delta >= n/2-1`;
* q<=2: `delta >= n/2-3`.

Proof: let q<=2 count all finite multiple points, and write their multiplicities r_1,...,r_q. At each point d2(v)<=1, since there is only one possible other multiple point and only one line through the two points. The fan lemma gives D1<=sum_v(2r_v-4). There is at most one shared core-to-core segment, so D2<=q(q-1)/2. Counting incidences of core points with lines also gives h<=sum_v r_v-D2: each core-to-core segment lies on a line counted twice in the incidence sum and only once in h. Consequently the preceding budget gives

`2 delta >= n + sum_v(2r_v^2-11r_v+12) - D2`.

For r>=3, the summand equals `-3+(r-3)(2r-5)`, and is therefore at least -3. Thus

`2 delta >= n-3q-D2`.

For q<=2, the right side is at least n-7. Both 2delta and n are even integers, so 2delta>=n-6. This is the desired defect bound. At q=1, the stronger lower bound n-3 rounds up to n-2; at q=0 it is n.

The theorem recovers restricted upper values 54 at n=14, 117 at n=20, and 239 at n=28. It does not bound arrangements with parallel pairs or three or more multiple points. It therefore does not establish those upper values for the full classical problem. A point of multiplicity four contributes zero rather than -3 in the displayed sum, and higher multiplicities contribute a positive amount.

## A general weighted theorem, allowing arbitrarily many multiple points

The same geometric run obstruction gives a universal local inequality at an r-fold point:

**`d1(v)<=2r-3` for every r>=3.**

There are 2r cyclic rays. Every block of r-1 consecutive rays contains one that is not counted by d1: otherwise the opposite sides of the r intervening triangles lie on the same line, and that line meets two opposite rays from v. It would have to pass through v, contradicting nondegeneracy. Count selected rays in all 2r cyclic blocks of length r-1. Each selected ray appears in exactly r-1 blocks, and each block contains at most r-2 selected rays. Hence

`(r-1)d1(v)<=2r(r-2)`.

If d1 were at least 2r-2, the left side would exceed the right side by at least 2. Thus d1<=2r-3. Also d1+d2<=2r because each ray supports at most one incident elementary segment. Combining these inequalities yields

`3d1(v)+d2(v)<=6r-6`.

Let I=sum r*t_r and q=sum t_r over r>=3. Summing gives 3D1+2D2<=6I-6q. Since h<=I, the clean-line budget proves

**`2 delta >= n + sum_{r>=3}(2r²-11r+6)t_r`.**

This remains a theorem for **even n and pairwise nonparallel affine lines**. No bound on q is imposed. Its local weights are -9 at a triple point, -6 at a quadruple point, 1 at a quintuple point, 12 at a sextuple point, and larger thereafter. In particular, if every finite multiple point has multiplicity at least five, then

**`T <= floor(n(n-5/2)/3)`**,

the same polynomial that Blanc proves for simple arrangements. More precisely, any nonnegative total displayed weight suffices. This is a restricted nonsimple upper theorem, not a proof that the simple polynomial bounds the unrestricted problem. Its priority has not been established.

The positivity assertion follows from the exact factorization

`2r²-11r+6 = 1+(r-5)(2r-1)` for r>=5.

## Formalization of the fan obstruction

`Kobon/FanGeometry.lean` works with actual real lines and points. At an ordinary endpoint it proves that the opposite supports of two adjacent fan triangles coincide. It propagates that equality along a strip of nondegenerate triangles and proves that the outer endpoints cannot lie on opposite rays from the center. Its `FanStrip.ofTriangles` constructor accepts the `TriangleGeometry` structures supplied by `Cells.ofPredicate`.

`Kobon/FanCount.lean` separately proves the cyclic double count from the no-long-run property. The complete extraction of such a cyclic fan from an arbitrary arrangement, the elementary-segment data structure, and the clean-line charging argument are still paper-level geometry. Consequently these modules are geometric and combinatorial components, not a disguised unconditional Lean upper theorem.

`Kobon/CyclicFan.lean` now closes the intermediate bridge: actual antipodal radial points, indexed supporting lines, triangular sectors and ordinary shared-ray hypotheses produce the `FanStrip` obstruction and hence the no-long-run property. It then invokes the cyclic count to obtain `2r-3`. Its hypotheses describe actual local geometry; they do not assume the no-long-run conclusion. The remaining extraction is from an arbitrary global line arrangement into these local sector data.

## Verification status

The complete geometric upper argument above is a paper proof adapting a published local parity proof. It has not been encoded as a theorem about all Euclidean arrangements in Lean. The actual real-line fan obstruction is proved in `Kobon/FanGeometry.lean`; its cyclic double-count consequence is proved in `Kobon/FanCount.lean`. The aggregate arithmetic consequences are separated into an explicitly conditional Lean module; they do not disguise the remaining geometric lemmas as assumptions proving the full Kobon theorem.

`experiments/2026-09-21/general-bounds/clean_line_budget.py` independently checks the local clean-line obstruction, the global charging inequality, and the fan conclusions using exact rational arrangements. It passed 597 arrangements: 97 certificates from the index as it stood when this run began, 300 deterministic random arrangements, and 200 arrangements built from two pencils of multiplicities 3 through 12. The saved JSON records the core and side-use counts. Those finite checks support the derivation but do not prove the general geometry. The expanded nine-theorem conditional arithmetic module `Kobon/CleanLineBudget.lean`, the real geometric `FanGeometry` module, and cyclic `FanCount` module compiled successfully with Lean 4.31.0 on 2026-09-22. Printed theorem axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`.

The audit was also run on all fifteen exact Maiorana14:54 witnesses and the ten current Parpalak–Utkin gallery witnesses retained in adjacent folders. All passed. Fourteen of Maiorana's configurations have precisely two triple points and no parallel pairs, so they attain this paper theorem's restricted upper54 at14; the constructions remain attributed to Maiorana.
