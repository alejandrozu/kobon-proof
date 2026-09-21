# Formalizing successive extensions: target, progress, and obstruction

20 September 2026. This report supersedes claims that the unrestricted recurrence merely needs its existing placeholders filled. It does not retract any independently certified finite coordinate bound.

## The requested recurrence and its formula

The [HandWiki paragraph](https://handwiki.org/wiki/Kobon_triangle_problem) attributes an iterative lower-bound rule to Zarzuelo's March paper. Interpreting division over the reals, and using that triangle counts are integers, its proposed inequality is

\[
 K(n+1)\ge K(n)+\lfloor n/2\rfloor,\qquad n\ge3.\tag{1}
\]

This is a lower-bound inequality, not an equality determining the true maximum. It includes both

\[
K(2m+2)\ge K(2m+1)+m,
\qquad K(2m+1)\ge K(2m)+m.
\]

If (1) holds and a starting bound is \(K(s)\ge T_s\), its iterated consequence is

\[
\boxed{K(n)\ge T_s+
\left\lfloor\frac{(n-1)^2}{4}\right\rfloor-
\left\lfloor\frac{(s-1)^2}{4}\right\rfloor,\qquad n\ge s.}\tag{2}
\]

For the certified simple input \(s=49,T_s=767\), this becomes

\[
\boxed{K(n)\ge \left\lfloor\frac{(n-1)^2}{4}\right\rfloor+191,
\qquad n\ge49.}\tag{3}
\]

**Equations (2) and (3) are conditional on (1).** `Kobon/Iteration.lean` proves this implication, with `FullStepClaim K` explicitly present in the theorem signature. It does not prove (1) for a geometric maximum. The general formula applies to either an odd or an even starting order.

The first target counts from 49 are 767, 791, 816, 841, 867, 893, 920, 947, 975, 1003, 1032, 1061 at orders 49 through 60. These are not new finite records: our existing certificates already meet or exceed every one of them. For example, the retained classical witnesses give 51:817, 52:850, and 60:1140. The 51:817 witness is nonsimple. Separate simple bounds must be used for claims specifically about the simple maximum.

## New completed geometric Lean proof

`Kobon/Exterior.lean` works with actual real line equations, for an arbitrary number of lines of either parity. Given a nonparallel direction \(w\), it constructs an exterior line \(w(x)=H\). An explicit finite sum supplies a height beyond every old vertex.

For an old pair \(L_i,L_j\), let \(p=L_i\cap L_j\). For any old line \(R\), the proof considers its affine value at \(p\) and its directional derivatives along the two rays on which \(w\) increases. When these three values have one common weak sign for every \(R\), the two rays form a certified visible pair. These conditions refer only to the old lines, not to an assumed triangle in the new arrangement.

The theorem `Exterior.extension` proves that:

1. the extended real arrangement is simple;
2. every certified old triangle survives;
3. each distinct certified visible pair creates a distinct new triangle;
4. a list of \(c\) such pairs therefore proves the bound \(T+c\).

The proof includes the exact affine identity along the rays, preservation, nondegeneracy, simplicity, and the disjointness of old and new triangle lists. This closes the geometric realization step **once visible pairs have been supplied**. It does not assert that their number is always \(\lfloor n/2\rfloor\).

These theorems use only the usual Lean logical axioms. There are no placeholders, added geometric axioms, or native-evaluation dependencies in the new geometric proof.

## Why repeated exterior addition cannot prove (1)

Here is an ordinary geometric obstruction, with its numerical core proved in `Kobon/Iteration.lean`. The full wedge/cell counting bridge is still outside Lean.

Write \(b_r\) for the number of unbounded two-sided cells (wedges) before step \(r\), and \(c_r\) for the number of triangles created by an exterior addition. Then

\[
 b_{r+1}+c_r\le b_r+2.\tag{4}
\]

Each newly created triangle closes an old wedge. Adding a line cannot create a previously absent free ray at an old vertex, so it cannot create a new wedge at an old vertex. A wedge at a new vertex must use one of the two free rays of the new line; consequently there are at most two new wedges. Other old wedges can also be lost, which is why (4) is an inequality.

Summing gives

\[
\sum_{j<r}c_j\le b_0+2r-b_r\le b_0+2r-3.\tag{5}
\]

Thus the total gain of a chain consisting solely of exterior additions is at most linear in its length. The gains demanded by (1) sum quadratically. In particular, once the order is at least six, spending at least \(\lfloor n/2\rfloor\ge3\) wedges per step while introducing at most two cannot continue forever. `no_infinite_full_gain_budget` proves this contradiction from (4).

**This obstructs an infinite chain of exterior additions. It does not disprove the recurrence for maxima.** That recurrence could use different arrangements, interior insertions that replace some triangles, or a reconstruction between steps. The earlier odd optimal-input result also remains meaningful as a single extension.

## Exact test from the requested 49-line input

`scripts/audit_successor_chain.py` starts from `research/finite-table/simple-049.json`, an attributed previously published input already verified in Lean. At each step it enumerates exterior direction sectors exactly and chooses a maximizing line, breaking ties as recorded in the evidence file. Every old triangle is checked to survive, and the new count is checked by exact coordinates.

| Input order | Triangles | Wedges | Maximum exterior gain | Gain requested by (1) |
|---:|---:|---:|---:|---:|
| 49 | 767 | 47 | 24 | 24 |
| 50 | 791 | 24 | 23 | 25 |
| 51 | 814 | 3 | 2 | 25 |
| 52 | 816 | 3 | 2 | 26 |
| 53 | 818 | 3 | 2 | 26 |

Coordinates, the chosen lines, every sector count, and source hashes are in `experiments/2026-09-20/successor-49/chain.json`. `Kobon/Iteration49.lean` verifies all five finite profile maxima by kernel reduction. The identification of the profiles with the coordinates is performed by the exact Python geometry program; it is not claimed as a completed Lean theorem.

The obstruction is stronger than this one tie-breaking choice. For this 49-line input, which has 47 wedges, two exterior steps with gains 24 and 25 would force

\[
b_2\le47+2+2-24-25=2,
\]

contradicting the lower bound of three wedges for a simple arrangement. `two_steps_49_obstruction` checks this arithmetic under the stated wedge-budget hypotheses. The geometric wedge count and the three-wedge lemma remain independently checked/ordinary mathematics, as above.

## The weaker defect recurrence is a different formula

The earlier boundary-defect manuscript gives

\[
 T_{n+1}=T_n+
 \left\lceil\frac{n-1}{2n}
 \max\{3,3T_n-n(n-3)\}\right\rceil.\tag{6}
\]

Starting at 49:767, its guaranteed values are 50:791, 51:803, 52:805, and 60:821. They are checked in `defect_samples`. An earlier conversational calculation of 51:804 was an arithmetic error; the correct value is 803.

Equation (6) is an iteratable ordinary geometric theorem in that manuscript, with a formalized cyclic core. The remaining universal ray/edge charging and cyclic-direction realization lemmas still prevent us from calling its complete geometric proof Lean verified. It must not be substituted for the stronger requested rule (1) without saying so.

## Other completed formalization in this revision

`Parametric.lean`, `TangentBounds.lean`, and `SeedFamily.lean` prove a genuine real-parameter theorem: for every \(0<\epsilon\le10^{-5}\), the explicit trigonometric eleven-line seed is simple and has at least 32 certified triangles, including the nine specified triples along its distinguished line. Such seeds exist with \(\epsilon\) below any positive tolerance.

The four tangent enclosures are proved from trigonometric identities and the algebraic value of \(\cos(\pi/5)\), using rational bounds on \(\sqrt5\). Finite rational box checks use kernel reduction. Neither floating-point computations nor the older Python interval program are proof assumptions.

This completes a real-analytic seed obligation for the separate BBL-based family. It does not formalize geometric doubling. The growing-order bound

\[
K_s(10\cdot2^t+1)\ge(100\cdot4^t-4)/3
\]

still has that geometric obligation; its recurrence arithmetic was already verified. It is distinct from the successive one-line target (1).

## How to resume

1. For the requested full recurrence, investigate interior/reconstruction steps or a new family of arrangements. An invariant claiming a full exterior gain at every order is ruled out by the wedge budget, not merely unimplemented.
2. For the proven ordinary defect theorem, formalize the unused-edge charging map and the cyclic direction/visible-pair correspondence, then feed its witnesses to `Exterior.extension`.
3. For the sparse hybrid family, formalize the BBL geometric doubling theorem and connect it to `SeedFamily.arbitrarily_small` and `Families.closed_form`.
4. Keep conditional formulas, finite examples, uniform parameter proofs, and unconditional growing-order existence theorems explicitly distinguished. None establishes first-discovery priority by itself.

Build the new modules and the complete audit with the commands in the root README. The earlier consolidation also passed the independent [GitHub Actions run](https://github.com/alejandrozu/kobon-proof/actions/runs/35549919133).
