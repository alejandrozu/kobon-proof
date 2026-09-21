# An explicit eleven-line seed and a Kobon family within one triangle of the upper bound

Working research note prepared for Alejandro Zarzuelo Urdiales · 20 September 2026

**Status.** This note gives a computer-assisted seed proof and an infinite-family consequence of a published doubling theorem. Rational interval arithmetic proves parameter stability; two independently implemented exact counters verify finite witnesses. This is not an end-to-end Lean formalization. First-discovery priority and global best-known status remain unestablished.

## Abstract

We exhibit an eleven-line realization with 32 bounded triangular cells, whose intersections with a distinguished horizontal line lie on the Bartholdi–Blanc–Loisel tangent grid. All nine bounded segments of the distinguished line support triangles, and the arrangement type persists for arbitrarily small positive values of the exceptional-intercept parameter. The published doubling theorem yields simple straight-line arrangements with $N=10\cdot2^t+1$ lines and $N(N-2)/3-1$ triangles for every integer $t\ge0$. The boundary-defect extension developed in our preceding work gives an infinite even family within two triangles of the polynomial upper bound for simple arrangements. Explicit rational witnesses improve that even guarantee by one triangle at the checked orders through 162 lines. The eleven-line input count and doubling method retain their earlier attribution.

## Main theorem and numerical consequences

Let $K_s(n)$ be the maximum number of bounded triangular cells in a simple affine arrangement of $n$ straight lines. Simple means no parallel pairs and no triple intersections. Let $K(n)$ be the unrestricted classical Kobon number; thus $K(n)\ge K_s(n)$.

**Theorem 1.** For every integer $t\ge0$, put $q_t=10\cdot2^t$ and $N_t=q_t+1$. There is a simple straight-line arrangement with exactly

\[
T_t=\frac{100\cdot4^t-4}{3}=\frac{N_t(N_t-2)}3-1
\]

bounded triangular cells. Consequently

\[
\boxed{\frac{N_t(N_t-2)}3-1\le K_s(N_t)\le K(N_t)\le\frac{N_t(N_t-2)}3.}
\]

The classical upper bound is integral since $N_t\equiv3$ or $5\pmod6$. The theorem narrows the possible classical Kobon number to two consecutive integers. It does not decide between them. At eleven lines, a stronger published upper bound already gives $K(11)=32$.

| Lines $N$ | Füredi–Palásti benchmark $\lceil N(N-3)/3\rceil$ | This construction | Classical upper bound | Gain over that benchmark |
|---:|---:|---:|---:|---:|
| 81 | 2106 | **2132** | 2133 | +26 |
| 161 | 8480 | **8532** | 8533 | +52 |
| 321 | 34026 | **34132** | 34133 | +106 |
| 641 | 136320 | **136532** | 136533 | +212 |

The benchmark is a particular earlier construction, not an assertion that it exhausts all earlier lower bounds. The rows at 321 and 641 follow from the theorem; finite coordinate certificates are delivered through 161 and the even extension 162. Intermediate members $21:132$ and $41:532$ are weaker than the known maxima $133$ and $533$. They are construction checkpoints, not numerical improvements at those orders.

## The compatible eleven-line seed

For $0<\varepsilon\le10^{-5}$, set

\[
(a_1,\ldots,a_{10})=
\bigl(-\tan(4\pi/10),-\tan(3\pi/10),-\tan(2\pi/10),-\tan(\pi/10),
-\varepsilon,+\varepsilon,
\tan(\pi/10),\tan(2\pi/10),\tan(3\pi/10),\tan(4\pi/10)\bigr).
\]

Take $Y_0:y=0$ and $L_i:x-v_i y=a_i$, with the exact rational vector

\[
\boxed{(v_1,\ldots,v_{10})=\frac1{10}(15,-2,14,1,4,-4,5,-3,12,-5).}
\]

These equations completely specify the seed. In BBL's convention, $L_i$ is $y=m_i(x-a_i)$ with $m_i=1/v_i$. The exceptional lines have slopes $m_5=5/2$ and $m_6=-5/2$ and meet above $Y_0$.

**Lemma 2.** For every $0<\varepsilon\le10^{-5}$, these eleven lines form a simple affine arrangement with 32 triangles, exactly nine of which have a side on $Y_0$.

**Computer-assisted proof.** The $v_i$ are distinct and nonzero, so the directions are fixed and pairwise distinct. The intercepts are strictly increasing for positive $\varepsilon$ in the stated interval. For three lines not including $Y_0$, concurrency is determined by

\[
D_{ijk}(\varepsilon)=(a_j-a_k)v_i+(a_k-a_i)v_j+(a_i-a_j)v_k.
\]

Each determinant is affine in $\varepsilon$. The verifier encloses the tangent constants using rational intervals: Machin's identity bounds $\pi$, alternating arctangent series bound its inputs, and Taylor polynomials with rigorous remainders enclose sine and cosine. All arithmetic is rounded outward to a rational mesh of size $10^{-60}$.

For all $\binom{10}{3}=120$ triples, the enclosures at $\varepsilon=0$ and $\varepsilon=10^{-5}$ have the same strict sign, with every endpoint enclosure more than $0.034$ from zero. Affine dependence proves sign stability throughout the interval. Triples involving $Y_0$ are controlled by the strictly ordered intercepts for $\varepsilon>0$. The endpoint $\varepsilon=0$ is used only to check limits; that endpoint arrangement is not asserted to be simple.

At $\varepsilon=10^{-5}$, replace tangent constants by rational midpoints of their certified intervals. The same interval bounds certify that the reference arrangement has the determinant signs of the trigonometric arrangement. Its 32 triangles are counted independently by:

1. Consecutive intersection vertices along supporting lines, followed by adjacency-cycle enumeration.
2. Triples of supporting lines, with an exact sign test excluding any other line from the triangle's open interior.

The reference is simple and exactly nine triangles touch $Y_0$. No direction degenerates and no determinant changes sign, so crossing orders and triangular-cell incidences remain unchanged throughout $0<\varepsilon\le10^{-5}$. This proves the lemma. The coordinate witness, crossing orders, triangle list, and interval-check report are included in the package.

## Infinite iteration

Bartholdi–Blanc–Loisel, Proposition 3.1, applies to a simple $q+1$-line seed on this tangent grid, with the two exceptional intercepts in $(-1/q,0)$ and $(0,1/q)$ and all $q-1$ bounded segments of $Y_0$ supporting triangles. It produces $2q+1$ straight lines, adds exactly $q^2$ triangles, and preserves the distinguished-line condition. Remark 3.2 explains iteration when the exceptional intercepts can be arbitrarily small.

For any desired finite number $t$ of iterations, choose

\[
\varepsilon_t=\min\left\{10^{-5},\frac1{40\cdot2^t}\right\}.
\]

Lemma 2 permits this choice, which satisfies the BBL smallness condition at every required stage. Thus

\[
T_t=32+\sum_{j=0}^{t-1}(10\cdot2^j)^2
=32+\frac{100(4^t-1)}3
=\frac{100\cdot4^t-4}3.
\]

This proves Theorem 1 for every $t$. The parameter may depend on the final order; one fixed positive parameter is not claimed to work for infinitely many consecutive insertions. The proof uses the published theorem and the full parameter-interval certificate, not extrapolation from finite counts.

The doubling formula and preservation of the triangle deficit belong to BBL. The explicit coefficient vector and its verified small-parameter compatibility supply the additional input.

## Combining the family with the exterior extension

For a simple $n$-line arrangement with $T$ triangles, let $d=n(n-2)-3T$ count the unused bounded segments. Our preceding boundary-defect theorem gives an exterior line preserving all old triangles and creating at least

\[
g(n,T)=\left\lceil\frac{n-1}{2n}\max\{3,3T-n(n-3)\}\right\rceil
\]

new triangles.

For completeness, let $b$ count unbounded two-sided wedge cells. Their $2b$ free boundary rays leave $2n-2b$ unpaired rays. At an unpaired ray's endpoint on a crossing line, one of that line's two incident bounded segments is unused: if both supported triangles, those triangles would share the unique bounded segment on the first line, which is impossible. Each unused segment receives at most two endpoint charges, so $b\ge n-d$. The convex hull of the finite vertices supplies at least three wedges. Among the $2n$ normal-direction sectors, each wedge is visible in exactly $n-1$ sectors. Averaging gives an exterior gain of at least $\lceil(n-1)b/(2n)\rceil$. A line beyond every old vertex closes precisely the visible wedges and misses every old bounded cell.

For Theorem 1, $n=q+1$, $T=(q^2-4)/3$, and $d=3$. Since $q=10\cdot2^t$ is even,

\[
g(n,T)=\left\lceil\frac{q(q-2)}{2(q+1)}\right\rceil
=\frac q2-1.
\]

**Corollary 3.** For every $q=10\cdot2^t$, $t\ge0$,

\[
\boxed{K_s(q+2)\ge\frac{q^2-4}{3}+\frac q2-1.}
\]

Writing $M=q+2$, this is $K_s(M)\ge M(M-5/2)/3-2$. These $M$ are $0$ or $4$ modulo $6$, so the polynomial before subtracting two is Blanc's upper bound for **simple** arrangements. It is not used here as an upper bound for unrestricted classical $K(M)$.

The exact finite exterior-direction search gains $q/2$ at every delivered order, improving the corollary by one triangle there:

| Even lines | Guaranteed by Corollary 3 | Exact finite witness | Polynomial upper bound for simple arrangements |
|---:|---:|---:|---:|
| 12 | 36 | 37 | 38 |
| 22 | 141 | 142 | 143 |
| 42 | 551 | 552 | 553 |
| 82 | **2171** | **2172** | 2173 |
| 162 | **8611** | **8612** | 8613 |
| 322 | **34291** | not generated | 34293 |

The polynomial upper bound has small-order exceptions where it can be strengthened: the simple maximum at 12 lines is 37. The first three rows are checkpoints, not claimed new records. Our earlier bounds at 22 and 42 already reach 143 and 553 and remain stronger there.

The program inspects every open normal-direction sector, selects one closing the most wedges, and takes $w(x,y)=H$ with $H=1+\max_p w(p)$ over old vertices. All calculations are rational; both triangle counters check the enlarged arrangement. The stronger gain $q/2$ observed in these examples is **not asserted for all $t$**. Corollary 3 is the proved infinite even statement.

## Attribution and the claim supported here

The final search started from the Honma-based eleven-line arrangement in Savchuk's Appendix A.4. We selected a different distinguished line, fitted a realization to the required grid with a small exceptional parameter, simplified reciprocal slopes to tenths, and proved stability for arbitrarily small positive parameters. The eleven-line count of 32 is an existing result.

The related work has distinct roles:

- **Honma and Savchuk:** the eleven-line starting construction; Savchuk also supplies the published computational exclusion of 33 triangles at eleven lines.
- **Bartholdi, Blanc and Loisel:** the straight-line doubling theorem and its iteration mechanism.
- **Parpalak and Utkin:** the 2026 optimal $18\cdot2^t+1$ straight-line family and careful treatment of geometric compatibility, motivating a full parameter-stability check.
- **Zarzuelo's extension work:** the exterior-addition program, applied here through the quantitative boundary-defect theorem to obtain the even corollary.

A precise statement suitable for this draft is:

> We exhibit an explicit realization of a known eleven-line Kobon arrangement satisfying the BBL hypotheses for arbitrarily small exceptional intercepts. A rational interval certificate establishes this compatibility and yields $K(10\cdot2^t+1)\ge(100\cdot4^t-4)/3$. Combining it with the boundary-defect extension gives a corresponding infinite family at adjacent even orders.

The candidate contribution is the certified compatible realization and these family consequences. First discovery and global record status require further priority comparison. The audit checked BBL, Blanc, Savchuk, Parpalak–Utkin, public galleries and the even-family draft, OEIS, and targeted searches for the family and counts. No explicit earlier matching straight-line family was identified in those sources. This limited search does not settle priority. Pseudoline lower bounds cannot serve as straight-line comparisons without a realizability argument.

The result is a sparse infinite family, not a formula closing the gap for every integer. At 81 and 161 the classical gap is now at most one within our working catalogue. Eliminating the last triangle, or proving the stronger observed even extension at every stage, remains open in this work.

## Reproducibility and references

All delivered scripts use only the Python standard library. Run **python verify_seed.py** for the parameter proof and **python generate_family.py 4** for the ten finite certificates at orders 11 through 162 in the two families. The files **seed-verification.json**, **seed-combinatorics.json**, and **finite-verification.json** record the interval proof, reference crossing orders and triangles, and exact finite checks. SHA-256 hashes are in **manifest.json**.

1. [Bartholdi, Blanc and Loisel (2007), Proposition 3.1 and Remark 3.2](https://arxiv.org/html/0706.0723v1).
2. [Blanc (2008), Theorem 1 and the distinction between pseudolines and lines](https://arxiv.org/html/0801.2845v2).
3. [Savchuk (2025), Appendix A.4 and the eleven-line computation](https://arxiv.org/html/2507.07951v1).
4. [Parpalak and Utkin (2026), Sections 2 and 7](https://arxiv.org/html/2604.22035v1).
5. [Füredi and Palásti (1984), Arrangements of Lines with a Large Number of Triangles](https://paperzz.com/doc/9476977/arrangements-of-lines-with-a-large-number-of-triangles).
6. [Parpalak–Utkin even-family draft](https://github.com/parpalak/kobon-even-draft/blob/master/8-14-26-even-series.md).
7. [OEIS A006066](https://oeis.org/A006066).
8. [Zarzuelo Urdiales, New Lower Bounds for Even Kobon Numbers, Archivara](https://archivara.org/paper/48b411c9-0e03-4592-931e-179b9a1c2312).
9. [Earlier boundary-defect manuscript](../kobon-extension/manuscript.md), including the scope of its Lean-checked counting core.

