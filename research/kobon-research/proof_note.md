# A further extension of the Parpalak–Utkin even family

Research note, 20 September 2026. **Novelty and record status are not established.**

This note gives an analytic argument for a derived infinite family. It depends
on the even construction in the public Parpalak–Utkin draft and the intersection
estimates behind Bartholdi–Blanc–Loisel doubling. The argument has not received
independent mathematical review or been formalized in a proof assistant.
Finite examples accompanying the note have exact rational certificates.

## Statement and attribution

Let K(N) denote the maximum number of bounded triangular cells formed by N
distinct straight lines in the real affine plane. Triple intersections are
allowed. This is the classical convention, not the simple-arrangement problem.

**Derived corollary.** For every integer t >= 0, put q = 6·2^t and N = q+3.
The Parpalak–Utkin construction, followed by the additional line specified
below, gives

\[
K(N)\ \ge\ \frac{q^2}{3}+q+1
       \ =\ \frac{N(N-3)}{3}+1.
\]

The seed and the doubling operation are prior work. The contribution examined
here is the additional line and the count of the unbounded wedges it closes.
This is not a claim to have discovered the underlying even family.

Sources:

1. [Parpalak–Utkin, even-series draft](https://github.com/parpalak/kobon-even-draft/blob/master/8-14-26-even-series.md),
   especially its main theorem, Lemmas 2–3, and Appendix A.
2. [Bartholdi–Blanc–Loisel, arXiv:0706.0723](https://arxiv.org/abs/0706.0723), Proposition 3.1.

## A valid additional-line lemma

An unbounded wedge is a two-sided unbounded cell with a finite vertex p and
two free boundary rays p+ru and p+sv, r,s >= 0, spanning an angle less than pi.
“Free” means that no further arrangement vertex lies on either ray.

Let w be a linear functional, and choose H greater than w(p) at every finite
vertex of an arrangement. The line S = {x : w(x)=H} preserves every bounded
triangular cell. For every unbounded wedge with w(u)>0 and w(v)>0, S closes
that wedge into one new triangular cell.

**Proof.** Every bounded cell is the convex hull of its vertices, so S misses
it. On each specified ray, w increases from w(p)<H to infinity. Consequently S
intersects both rays beyond p. The two ray segments and the intervening segment
of S bound a triangle contained in the original wedge. No other old line enters
its interior. Different wedges have disjoint interiors, so the triangles are
distinct. This proves a lower bound equal to the old count plus the number of
these wedges. ∎

There is no claim here that an arbitrary odd arrangement has (N-1)/2 such
wedges. That extra hypothesis must actually be proved for the arrangement used.

## The input construction and the added line

For a target t, use the source construction with

\[
q=6\,2^t,\quad \epsilon=\frac1{4q},\quad
\eta=3\sqrt3\,q^6,\quad \delta=2q^6.
\]

Its initial lines are Y:y=0, R:y=x-delta, and six lines
L_i:y=m_i(x-a_i), where

\[
(a_1,\ldots,a_6)=(-\sqrt3,-1/\sqrt3,1/\sqrt3,\sqrt3,-\epsilon,\epsilon),
\]

\[
(m_1,\ldots,m_6)=
\left(-\frac12,-\eta,\eta,\frac25,
-\frac{4\eta}{2\eta-3+\epsilon\sqrt3(2\eta+1)},
\frac{4\sqrt3}{\sqrt3+9\epsilon}\right).
\]

R is held aside while doubling the other seven lines. At a stage with n+1
lines, n=6·2^s, add n lines M_j:y=mu_j(x-b_j), with

\[
\beta_j=-\frac\pi2+\left(j-\frac12\right)\frac\pi n,
\quad b_j=\tan\beta_j,
\quad
\mu_j=-\frac{m_{\min}}{n^{10}}
\left(\sin(2\beta_j)+\frac1{n^6b_j}\right).
\]

Here m_min is the smallest absolute nonzero slope in the current core. Restore
R after t stages. Denote this q+2-line arrangement by C_t. The cited even
construction supplies q^2/3+q/2 bounded triangles.

Our added line is completely specified by

\[
\sigma=10^{-6},\qquad
H=1+\max_{p\text{ a vertex of }C_t}(y_p-\sigma x_p),
\qquad S:y=\sigma x+H.
\]

Thus the remaining task is to show that C_t has at least q/2+1 wedges whose
two rays point toward increasing y-sigma·x. No search for S is required.

## Wedge count

Write w(x,y)=y-sigma·x. All lines added by doubling satisfy

\[
|\mu_j|<\frac{2m_{\min}}{n^{10}}
\le\frac{4/5}{6^{10}}<10^{-6}.
\]

Their w-positive ray therefore points to the left. The w-positive ray on Y
also points left. The six initial nonzero slopes have absolute value at least
2/5; none equals sigma. R has slope 1, so S is distinct and nonparallel to every
old line.

**Initial wedges.** The endpoint orders in the eight-line seed give four
w-positive wedges:

\[
(Y,L_1),\qquad(L_2,L_5),\qquad(L_3,L_6),\qquad(L_4,R).
\]

For the first two pairs both free rays point left; for the last two both point
right. The sign of m-sigma verifies w-positivity. Their endpoints are simple
vertices. These endpoint orders hold for the entire parameter range used above,
including when the target t is large.

**One doubling step.** Let L_- be the old line meeting Y at its leftmost vertex.
The selected wedge (Y,L_-) is replaced by n/2+1 selected left wedges involving
new lines. For n divisible by 4, their pairs are

\[
(Y,M_1),\qquad(L_-,M_{n/4+1}),
\]

\[
(M_i,M_{n/2+2-i})\quad(2\le i\le n/4),
\]

\[
(M_i,M_{3n/2+1-i})\quad(n/2+1\le i\le3n/4).
\]

There are 2+(n/4-1)+n/4 = n/2+1 pairs. Their shared intersection is leftmost
on both supporting lines. The first two pairs include the exceptional old
supports; the remaining ones follow from the order of new–new intersections.

Here is why the endpoint assertion follows from the cited estimates, including
the exceptional step. Reflect the core by x -> -x. This takes M_j to the
reflected M_{n+1-j}, exchanges the two extreme old lines, and preserves the
negative sign in the doubling formula. The right-wedge enumeration in the
even draft then gives exactly the displayed pairs. For stages n>=12 the old
leftmost line is a previously added M_1 with positive slope. Its reflected
slope is negative, has absolute value at most 1/2, and satisfies the hypotheses
of that enumeration.

At n=6, the pairs instead are

\[
(Y,M_1),\quad(M_2,M_3),\quad(L_1,M_5),\quad(M_4,M_6).
\]

The only change needed in the reflected n=6 endpoint calculation is that the
extreme old slope has absolute value 1/2 whereas m_min=2/5. Thus rho=m_min/|m|=4/5.
The factor controlling the order is

\[
\frac{\rho n^{-10}}{1+\rho n^{-10}f_j},\qquad
f_j=\sin(2\beta_j)+\frac{n^{-6}}{\tan\beta_j}.
\]

After division by the common positive rho·n^(-10), the relative correction is
bounded by 3n^(-10), just as for every 0<rho<=1. The tied leading terms are
separated by (3-sqrt(3))n^(-6), which exceeds 18n^(-10) at n=6. The selected
endpoint is consequently unchanged. This gives the four listed pairs.

**Why old selected wedges survive.** Apart from (Y,L_-), each previously
selected core wedge lies wholly on one side of Y, and its free rays move farther
from Y. Its vertex is not the exceptional L_5–L_6 intersection. At the current
stage its vertex therefore has |y|>m_min/n, whereas a new line meets an old core
line only where |y|<3m_min/n^9. Such a crossing cannot occur on either of the
free rays. The same separation applies at subsequent stages, using the new
m_min and the refined grid. The three initial selected wedges other than
(Y,L_1) are above Y; the same reasoning protects the two not involving R.

For the remaining wedge (L_4,R), intersections of R with new lines have

\[
x(R\cap M_j)=\frac{\delta-\mu_jb_j}{1-\mu_j}.
\]

Since |mu_j|<10^(-6), |b_j|<q, and delta=2q^6, these lie between 0.99delta and
1.01delta. But x(R cap L_4)=(delta-(2/5)sqrt(3))/(3/5)>1.6delta.
Thus the free right ray of R in (L_4,R) is untouched. New intersections on L_4
are close to Y and cannot touch its free right ray either.

Finally, R cannot cut any of the new free left rays. All intersections
involving new core lines have x<=n^6<=q^6/64 during a doubling stage, whereas
their intersections with R have x>0.99delta>q^6. Consequently the left-wedge
enumeration in the core remains valid after R is restored.

Every new selected wedge involves a line of slope less than sigma and has both
free rays pointing left. The other old supporting line, when present, is Y or
the previous M_1; at n=6 it is L_1. Its ray is w-positive too. This verifies the
direction condition required by the additional-line lemma.

We have therefore preserved all previously selected wedges except one and
constructed n/2+1 replacements. At each stage their number increases by at
least n/2. Starting with four gives

\[
c_t\ge4+\frac12\sum_{s=0}^{t-1}6\,2^s
   =4+\frac{q-6}{2}=\frac q2+1.
\]

Applying the additional-line lemma to C_t and S proves

\[
K(q+3)\ge\left(\frac{q^2}{3}+\frac q2\right)
             +\left(\frac q2+1\right)
          =\frac{q^2}{3}+q+1.
\qquad\square
\]

## Exact finite certificates and limits of the claim

The independently checkable members supplied here are

| t | N | Triangles |
|---:|---:|---:|
| 3 | 51 | 817 |
| 4 | 99 | 3,169 |
| 5 | 195 | 12,481 |

The generator uses rational approximations to the trigonometric data and
solves the two seed concurrence conditions exactly. Both counting methods use
exact arithmetic. The mathematical argument above concerns the exact real
parameter construction and does not infer infinitude from these examples.

This family gives odd N, despite starting from an even construction. It does
not improve the known records for N=9,15,27, and no complete comparison with
all earlier constructions at larger N has been completed. It should therefore
be described as a derived construction with a proof argument, **not as a new
best-known infinite family or as a completed solution of the requested even
record problem**.

For publication, the next mathematical review should concentrate on the
reflected wedge enumeration and its preservation under R; the next historical
review should check whether this corollary is already implicit or explicit in
earlier constructions. Neither a missing search hit nor absence from the OEIS
table establishes priority.
