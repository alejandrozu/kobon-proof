# An explicit 21-line seed and a Kobon family within two triangles of the upper bound

Working research note for Alejandro Zarzuelo Urdiales · 20 September 2026

**Status.** This note gives a computer-assisted proof of an explicit seed and an infinite-family consequence of a published doubling theorem. The seed verification uses rational interval arithmetic and two exact triangle counters. It is not an end-to-end Lean formalization. First-discovery priority and best-known status have not been established by this work.

## Main result

Let $K_s(n)$ denote the maximum number of bounded triangular cells in a simple affine arrangement of $n$ straight lines, where simple means no parallel pairs and no triple intersections. Let $K(n)$ be the unrestricted classical Kobon number. Then $K(n)\ge K_s(n)$.

**Theorem.** For every integer $t\ge0$, put $q_t=20\cdot2^t$ and $N_t=q_t+1$. There is a simple straight-line arrangement with exactly

\[
T_t=\frac{400\cdot4^t-7}{3}=\frac{N_t(N_t-2)}3-2
\]

bounded triangular cells. Consequently

\[
\boxed{\frac{N_t(N_t-2)}3-2\ \le K_s(N_t)\le K(N_t)\le\frac{N_t(N_t-2)}3.}
\]

Here $N_t\equiv3$ or $5\pmod6$, so the upper bound is integral. The construction leaves a gap of two triangles at every order in this family. It does not determine which of the three integers in the displayed interval is the actual Kobon number.

The construction at $21$ or $41$ lines does not improve the known maxima $133$ and $533$. Its first larger order is $81$.

| Lines $N$ | Classical Füredi–Palásti benchmark $\lceil N(N-3)/3\rceil$ | This construction | Segment upper bound | Improvement over that benchmark |
|---:|---:|---:|---:|---:|
| 81 | 2106 | 2131 | 2133 | 25 |
| 161 | 8480 | 8531 | 8533 | 51 |
| 321 | 34026 | 34131 | 34133 | 105 |
| 641 | 136320 | 136531 | 136533 | 211 |

The benchmark is a particular earlier construction, not an assertion that every earlier construction is weaker. The rows at $321$ and $641$ are theorem consequences; the delivered finite rational certificates run through $161$ and its even extension $162$.

## The compatible seed

Take $0<\varepsilon\le10^{-5}$. Define twenty ordered intercepts

\[
(a_1,\ldots,a_{20})=
\bigl(-\tan(9\pi/20),\ldots,-\tan(\pi/20),-\varepsilon,+\varepsilon,
\tan(\pi/20),\ldots,\tan(9\pi/20)\bigr).
\]

Define $Y_0:y=0$ and $L_i:x-v_i y=a_i$, with the following **exact rational** coefficients; each displayed decimal has denominator dividing $10000$.

| $i$ | $v_i$ | $i$ | $v_i$ |
|---:|---:|---:|---:|
| 1 | 1.0000 | 11 | 0.1977 |
| 2 | 0.2284 | 12 | 0.1236 |
| 3 | 0.4371 | 13 | 0.3641 |
| 4 | 0.2890 | 14 | 0.1211 |
| 5 | 0.3553 | 15 | 0.3230 |
| 6 | 0.1605 | 16 | 0.0932 |
| 7 | 0.3883 | 17 | 0.1359 |
| 8 | 0.1152 | 18 | -0.4334 |
| 9 | 0.2344 | 19 | -0.1840 |
| 10 | -0.0112 | 20 | -1.0000 |

**Seed lemma.** For every $0<\varepsilon\le10^{-5}$, these 21 lines form a simple affine arrangement with 131 triangular cells, exactly 19 of which have a side on $Y_0$.

**Computer-assisted proof.** The coefficients $v_i$ are distinct and nonzero. Thus no two $L_i$ are parallel, every $L_i$ is nonparallel to $Y_0$, and all slopes $m_i=1/v_i$ are finite and nonzero. The intercepts are strictly ordered when $\varepsilon>0$.

For three lines not including $Y_0$, concurrency is determined by

\[
D_{ijk}(\varepsilon)=(a_j-a_k)v_i+(a_k-a_i)v_j+(a_i-a_j)v_k.
\]

Every $D_{ijk}$ is affine in $\varepsilon$. The verifier encloses all tangent values with rational intervals, using Machin's identity for $\pi$, alternating arctangent-series bounds, and Taylor polynomials with rigorous remainder bounds for sine and cosine. Arithmetic is rounded outward to a rational mesh of size $10^{-60}$.

For all $\binom{20}{3}=1140$ triples, the interval enclosures at $\varepsilon=0$ and $\varepsilon=10^{-5}$ have the same strict sign. All endpoint enclosures stay more than $0.0034$ from zero. Affine dependence therefore proves sign stability for the entire interval. Triples involving $Y_0$ are governed by the strictly ordered intercepts for $\varepsilon>0$. We make no simplicity claim at $\varepsilon=0$ itself.

At $\varepsilon=10^{-5}$, replace the tangent constants by rational midpoints of their certified intervals. The resulting arrangement has the same determinant signs as the exact trigonometric arrangement. Its 131 triangles are counted independently by (i) adjacency of consecutive intersection vertices along each line and (ii) an exact open-interior sign test over triples of supporting lines. It is simple, and exactly 19 triangles touch $Y_0$. The arrangement type, its triangle count, and the distinguished-line property are unchanged throughout $0<\varepsilon\le10^{-5}$. This proves the lemma. The complete verifier and its output are included in the package.

## Infinite iteration

Apply Bartholdi–Blanc–Loisel, Proposition 3.1 and Remark 3.2. Their theorem starts with $q+1$ lines, the specified tangent intercepts, two sufficiently small exceptional intercepts, and a distinguished line touching all $q-1$ of its bounded segments. It produces $2q+1$ simple straight lines, adds exactly $q^2$ triangles, and retains the distinguished-line condition.

For a desired finite number $t$ of iterations, choose

\[
\varepsilon_t=\min\left\{10^{-5},\frac{1}{80\cdot2^t}\right\}.
\]

The seed lemma permits this choice. At every required iteration, the two exceptional intercepts satisfy the smallness condition in BBL. Therefore

\[
N_t=20\cdot2^t+1,\qquad
T_t=131+\sum_{j=0}^{t-1}(20\cdot2^j)^2
=131+\frac{400(4^t-1)}3
=\frac{400\cdot4^t-7}{3}.
\]

This proves the theorem for every $t$, rather than extrapolating from the finite certificates. The doubling mechanism and preservation of the triangle deficit are due to BBL; the explicit compatible seed is the output of the present search.

## Consequence of the boundary-defect extension

Our earlier boundary-defect extension gives an exterior-line gain of at least

\[
g(n,T)=\left\lceil\frac{n-1}{2n}\max\{3,3T-n(n-3)\}\right\rceil.
\]

For the new family, $n=q+1$, $T=(q^2-7)/3$, and the number of unused bounded segments is $d=n(n-2)-3T=6$. Since $q\ge20$ is even,

\[
g(n,T)=\left\lceil\frac{q(q-5)}{2(q+1)}\right\rceil=\frac q2-2.
\]

Thus, for every $q=20\cdot2^t$,

\[
\boxed{K_s(q+2)\ge\frac{q^2-7}{3}+\frac q2-2.}
\]

Writing $M=q+2$, this is $M(M-5/2)/3-4$, four triangles below Blanc's upper bound for **simple** arrangements in these residue classes. That simple upper bound is not being asserted as an unrestricted upper bound for classical $K(M)$.

The finite certificates actually obtain one more triangle with the explicit line $x=H$, where $H=1+\max_p x(p)$ over the old vertices:

| Even lines | Guaranteed by the infinite corollary | Exact finite certificate | Simple-arrangement upper bound |
|---:|---:|---:|---:|
| 22 | 139 | 140 | 143 |
| 42 | 549 | 550 | 553 |
| 82 | 2169 | 2170 | 2173 |
| 162 | 8609 | 8610 | 8613 |

The gain of $q/2-1$ seen in these explicit even certificates is not used here as a proved all-$t$ assertion. The infinite even corollary uses the established guaranteed gain $q/2-2$.

## Attribution and scope of novelty

The search was initialized from the public 21-line, 133-triangle gallery certificate, then fitted to the required tangent grid with selected constraints relaxed. Coordinate optimization and realizable triangle flips produced a different, compatible 131-triangle seed. Its listed rational coefficients and parameter verification are the mathematical content needed to reproduce the construction; no black-box search is needed to verify the result.

The inputs and methods must retain their attribution:

- BBL supply the doubling theorem, formulas, and invariant triangle deficit.
- The public gallery supplies the initial 21-line configuration used by the search.
- Parpalak–Utkin's work motivates checking geometric compatibility and arbitrary-small-parameter stability, rather than assuming every optimal seed can be doubled indefinitely.
- The boundary-defect extension developed in the preceding work supplies the guaranteed even-family corollary.

The $131$-triangle seed is not a record at 21 lines. The candidate contribution is its explicit compatibility for arbitrarily small $\varepsilon$, the resulting constant-gap straight-line family, and the associated extension bounds. No publication, OEIS edit, or first-discovery claim has been made.

The source audit checked BBL, Blanc, the 2026 Parpalak–Utkin paper and public gallery, the OEIS entry, and targeted searches for the family and numerical counts. It did not identify an earlier matching straight-line family. This is not an exhaustive priority proof. In particular, pseudoline constructions that attain the upper bound cannot be imported as straight-line results without a stretchability argument.

## References and verification files

1. [Bartholdi, Blanc and Loisel (2007), Proposition 3.1 and Remark 3.2](https://arxiv.org/html/0706.0723v1).
2. [Blanc (2008), Theorem 1 and the distinction between pseudolines and lines](https://arxiv.org/html/0801.2845v2).
3. [Parpalak and Utkin (2026), Sections 2 and 7](https://arxiv.org/html/2604.22035v1).
4. [Füredi and Palásti (1984), Arrangements of Lines with a Large Number of Triangles](https://paperzz.com/doc/9476977/arrangements-of-lines-with-a-large-number-of-triangles).
5. [Public 21-line input certificate](https://raw.githubusercontent.com/ud1/kobon-solutions/master/gallery/certificates/21/P21-2wdhca8g2cjbp.json), downloaded SHA-256 `501df61cc019577e1291e49fbcfa393e6e775e126cb46fe5010c8f2c85ca88b0`.
6. [OEIS A006066](https://oeis.org/A006066).
7. [Earlier boundary-defect manuscript](../kobon-extension/manuscript.md).

Local verification entry points: `verify_seed.py`, `generate_family.py`, `verify_direct.py`, `seed-verification.json`, and `finite-verification.json`. All delivered verification and generation scripts use only the Python standard library.
